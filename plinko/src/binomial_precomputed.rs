//! Precomputed CDF tables for constant-time binomial sampling.
//!
//! Optimization #85: For small n (< PRECOMPUTE_MAX_N) with p=0.5,
//! use precomputed CDF tables. The inverse CDF becomes a CT linear search
//! over the table instead of computing log/exp per iteration.
//!
//! This has lower constant factor than the log-space method.

use once_cell::sync::Lazy;

use crate::constant_time::{
    ct_f64_le, ct_le_u64, ct_min_u64, ct_saturating_sub_u64, ct_select_f64, ct_select_u64,
};

/// Maximum n for which we precompute CDF tables
pub const PRECOMPUTE_MAX_N: usize = 256;

/// Precomputed CDF values for Binomial(n, 0.5) for n = 0..PRECOMPUTE_MAX_N
/// Table[n][k] = P(X <= k) for X ~ Binomial(n, 0.5)
/// We only store up to k = n, rest is 1.0
/// Heap-allocated to avoid stack overflow (257x257 f64s = ~4.3MB)
static CDF_TABLES: Lazy<Box<[[f64; PRECOMPUTE_MAX_N + 1]; PRECOMPUTE_MAX_N + 1]>> =
    Lazy::new(|| {
        let mut tables = vec![[0.0f64; PRECOMPUTE_MAX_N + 1]; PRECOMPUTE_MAX_N + 1];

        for n in 0..=PRECOMPUTE_MAX_N {
            if n == 0 {
                tables[0][0] = 1.0;
            } else {
                let scale = 0.5f64.powi(n as i32);
                let mut cdf = 0.0f64;
                let mut binom_coeff = 1.0f64;

                for k in 0..=n {
                    let pmf = binom_coeff * scale;
                    cdf += pmf;
                    tables[n][k] = cdf;

                    if k < n {
                        binom_coeff *= (n - k) as f64 / (k + 1) as f64;
                    }
                }

                for k in (n + 1)..=PRECOMPUTE_MAX_N {
                    tables[n][k] = 1.0;
                }
            }
        }

        tables.try_into().unwrap()
    });

/// Precomputed binomial sampler for p=0.5 and small n.
pub struct PrecomputedBinomialSamplerTee {
    fallback_max_count: u64,
}

impl PrecomputedBinomialSamplerTee {
    pub fn new(fallback_max_count: u64) -> Self {
        Self { fallback_max_count }
    }

    /// Sample from Binomial(n, 0.5) using precomputed tables when possible.
    ///
    /// For n <= PRECOMPUTE_MAX_N: O(PRECOMPUTE_MAX_N) but with fast table lookups
    /// For n > PRECOMPUTE_MAX_N: O(fallback_max_count) with log/exp computation
    #[inline]
    pub fn sample_half(&self, count: u64, prf_output: u64) -> u64 {
        let u = (prf_output as f64 + 0.5) / (u64::MAX as f64 + 1.0);

        if count as usize <= PRECOMPUTE_MAX_N {
            self.inverse_cdf_precomputed_ct(count, u)
        } else {
            self.inverse_cdf_fallback_ct(count, 0.5, u)
        }
    }

    /// Sample from Binomial(n, num/denom) - uses precomputed table only for p=0.5.
    #[inline]
    pub fn sample(&self, count: u64, num: u64, denom: u64, prf_output: u64) -> u64 {
        if denom == 0 || num == 0 {
            return 0;
        }
        if num >= denom {
            return count;
        }

        if num * 2 == denom && count as usize <= PRECOMPUTE_MAX_N {
            return self.sample_half(count, prf_output);
        }

        let p = num as f64 / denom as f64;
        let u = (prf_output as f64 + 0.5) / (u64::MAX as f64 + 1.0);

        self.inverse_cdf_fallback_ct(count, p, u)
    }

    /// Constant-time inverse CDF using precomputed table.
    ///
    /// Always iterates PRECOMPUTE_MAX_N+1 times regardless of actual n.
    #[inline]
    fn inverse_cdf_precomputed_ct(&self, n: u64, u: f64) -> u64 {
        let n_idx = (n as usize).min(PRECOMPUTE_MAX_N);
        let table = &CDF_TABLES[n_idx];

        let mut result = 0u64;
        let mut found = 0u64;

        for k in 0..=PRECOMPUTE_MAX_N {
            let k_in_range = ct_le_u64(k as u64, n);
            let cdf_k = table[k];

            let u_le_cdf = ct_f64_le(u, cdf_k);
            let is_new_result = u_le_cdf & (1 - found) & k_in_range;
            result = ct_select_u64(is_new_result, k as u64, result);
            found |= is_new_result;
        }

        ct_select_u64(found, result, n)
    }

    /// Fallback log-space inverse CDF for large n or non-0.5 probability.
    #[inline]
    fn inverse_cdf_fallback_ct(&self, n: u64, p: f64, u: f64) -> u64 {
        let n = ct_min_u64(n, self.fallback_max_count);

        let mut p_adj = p;
        let use_complement = p > 0.5;
        if use_complement {
            p_adj = 1.0 - p;
        }

        let q = 1.0 - p_adj;
        let log_q = q.ln();
        let log_p = p_adj.ln();
        let log_p_over_q = log_p - log_q;

        let mut log_pmf = (n as f64) * log_q;
        let mut cdf = 0.0f64;
        let mut result = 0u64;
        let mut found = 0u64;

        for k in 0..=self.fallback_max_count {
            let k_in_range = ct_le_u64(k, n);

            let log_factor = if k == 0 {
                0.0
            } else {
                let n_minus_k_plus_1 = ct_saturating_sub_u64(n, k - 1) as f64;
                let k_f64 = k as f64;
                (n_minus_k_plus_1 / k_f64).ln() + log_p_over_q
            };

            let new_log_pmf = if k == 0 { log_pmf } else { log_pmf + log_factor };
            log_pmf = ct_select_f64(k_in_range, new_log_pmf, log_pmf);

            let pmf = log_pmf.exp();
            let valid_pmf = ct_select_f64(k_in_range, pmf, 0.0);
            cdf += valid_pmf;

            let u_le_cdf = ct_f64_le(u, cdf);
            let is_new_result = u_le_cdf & (1 - found) & k_in_range;
            result = ct_select_u64(is_new_result, k, result);
            found |= is_new_result;
        }

        let k = ct_select_u64(found, result, n);

        if use_complement {
            n - k
        } else {
            k
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::binomial::binomial_sample;

    #[test]
    fn test_precomputed_table_valid() {
        for n in 1..=PRECOMPUTE_MAX_N {
            let table = &CDF_TABLES[n];
            assert!(table[0] > 0.0, "CDF[{}][0] should be positive", n);

            for k in 1..=n {
                assert!(
                    table[k] >= table[k - 1],
                    "CDF[{}] not monotonic at k={}",
                    n,
                    k
                );
            }

            assert!(
                (table[n] - 1.0).abs() < 1e-10,
                "CDF[{}][{}] should be 1.0",
                n,
                n
            );
        }
    }

    #[test]
    fn test_matches_exact_for_small_n() {
        let sampler = PrecomputedBinomialSamplerTee::new(1024);

        for n in [10, 50, 100, 200] {
            for i in 0..100u64 {
                let prf = i.wrapping_mul(0x9E3779B97F4A7C15);
                let precomputed = sampler.sample_half(n, prf);
                let exact = binomial_sample(n, 1, 2, prf);
                assert_eq!(precomputed, exact, "mismatch at n={}, prf={}", n, prf);
            }
        }
    }

    #[test]
    fn test_distribution_mean() {
        let sampler = PrecomputedBinomialSamplerTee::new(1024);
        let n = 100u64;
        let samples = 10000u64;
        let mut sum = 0u64;

        for i in 0..samples {
            let prf = i.wrapping_mul(0x9E3779B97F4A7C15);
            sum += sampler.sample_half(n, prf);
        }

        let mean = sum as f64 / samples as f64;
        let expected = n as f64 * 0.5;
        assert!(
            (mean - expected).abs() < 2.0,
            "mean {} too far from {}",
            mean,
            expected
        );
    }

    #[test]
    fn test_result_in_bounds() {
        let sampler = PrecomputedBinomialSamplerTee::new(1024);

        for n in [1, 10, 50, 100, 200, 256] {
            for i in 0..100u64 {
                let prf = i.wrapping_mul(0x9E3779B97F4A7C15);
                let result = sampler.sample_half(n, prf);
                assert!(result <= n, "result {} > n {}", result, n);
            }
        }
    }
}
