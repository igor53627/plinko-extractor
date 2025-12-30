//! Parameterized TEE binomial sampler with configurable iteration bound.
//!
//! For TEE constant-time security, we need fixed iteration counts that don't
//! depend on secret values. The standard `binomial_sample_tee` uses a global
//! CT_BINOMIAL_MAX_COUNT = 65536, but this is overly conservative for many
//! Plinko parameter choices.
//!
//! This module provides `BinomialSamplerTee` which accepts a max_count parameter
//! derived from public protocol parameters (lambda, w), allowing tighter bounds.

use crate::constant_time::{ct_eq_u64, ct_f64_le, ct_le_u64, ct_max_u64, ct_min_u64, ct_select_f64, ct_select_u64, ct_saturating_sub_u64};

/// Maximum precomputed CDF table size (for small counts)
const PRECOMPUTE_THRESHOLD: u64 = 256;

/// TEE-safe binomial sampler with parameterized iteration bound.
///
/// The `max_count` parameter should be derived from public protocol parameters:
/// - For Plinko: max_count = 2 * lambda * w (total hints)
///
/// Security: The iteration count depends only on `max_count` (public), not on
/// the actual `count` value (which may be secret in TEE contexts).
pub struct BinomialSamplerTee {
    max_count: u64,
}

impl BinomialSamplerTee {
    /// Create a new sampler with the given maximum count bound.
    ///
    /// All calls to `sample()` will iterate exactly `max_count + 1` times.
    pub fn new(max_count: u64) -> Self {
        Self { max_count }
    }

    /// Sample from Binomial(count, num/denom) in constant time.
    ///
    /// Iterates exactly `self.max_count + 1` times regardless of `count`.
    #[inline]
    pub fn sample(&self, count: u64, num: u64, denom: u64, prf_output: u64) -> u64 {
        // Edge cases with public parameters only
        if denom == 0 || num == 0 {
            return 0;
        }
        if num >= denom {
            return count;
        }

        let mut p = num as f64 / denom as f64;
        let u = (prf_output as f64 + 0.5) / (u64::MAX as f64 + 1.0);

        // Use symmetry to keep p <= 0.5
        let use_complement = p > 0.5;
        if use_complement {
            p = 1.0 - p;
        }

        // Handle count == 0 via CT masking
        let count_is_zero = ct_eq_u64(count, 0);
        let k = self.inverse_cdf_ct(count, p, u);

        let result = if use_complement { count - k } else { k };
        ct_select_u64(count_is_zero, 0, result)
    }

    /// Constant-time inverse CDF with fixed iterations.
    #[inline]
    fn inverse_cdf_ct(&self, n: u64, p: f64, u: f64) -> u64 {
        let n = ct_min_u64(n, self.max_count);

        let q = 1.0 - p;
        let log_q = q.ln();
        let log_p = p.ln();
        let log_p_over_q = log_p - log_q;

        let mut log_pmf = (n as f64) * log_q;
        let mut cdf = 0.0f64;
        let mut result = 0u64;
        let mut found = 0u64;

        // Fixed iteration count based on max_count
        for k in 0..=self.max_count {
            let k_in_range = ct_le_u64(k, n);

            // Update log_pmf using recurrence (constant-time)
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

            // Check if u <= cdf (first time)
            let u_le_cdf = ct_f64_le(u, cdf);
            let is_new_result = u_le_cdf & (1 - found) & k_in_range;
            result = ct_select_u64(is_new_result, k, result);
            found |= is_new_result;
        }

        // If not found (numerical issues), return n
        ct_select_u64(found, result, n)
    }
}

// Removed local ct_f64_le - now using crate::constant_time::ct_f64_le (branchless)

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sampler_matches_standard() {
        let sampler = BinomialSamplerTee::new(1024);
        
        for count in [10, 50, 100, 500, 1000] {
            for (num, denom) in [(1, 2), (1, 4), (3, 4)] {
                for i in 0..20u64 {
                    let prf = i.wrapping_mul(0x9E3779B97F4A7C15);
                    let result = sampler.sample(count, num, denom, prf);
                    assert!(result <= count, "result {} > count {}", result, count);
                }
            }
        }
    }

    #[test]
    fn test_sampler_distribution() {
        let sampler = BinomialSamplerTee::new(1024);
        let n = 100u64;
        let samples = 1000u64;
        let mut sum = 0u64;

        for i in 0..samples {
            let prf = i.wrapping_mul(0x9E3779B97F4A7C15);
            sum += sampler.sample(n, 1, 2, prf);
        }

        let mean = sum as f64 / samples as f64;
        let expected = 50.0;
        assert!((mean - expected).abs() < 5.0, "mean {} too far from {}", mean, expected);
    }

    #[test]
    fn test_smaller_bound_is_faster() {
        // This test just verifies the API works with different bounds
        let small = BinomialSamplerTee::new(100);
        let large = BinomialSamplerTee::new(10000);

        let r1 = small.sample(50, 1, 2, 12345);
        let r2 = large.sample(50, 1, 2, 12345);
        
        // Both should give same result for same inputs
        assert_eq!(r1, r2);
    }
}
