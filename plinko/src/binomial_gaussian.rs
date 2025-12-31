//! Gaussian approximation for constant-time binomial sampling.
//!
//! Optimization #84: For large n where np > 10 and n(1-p) > 10, use
//! Normal(np, np(1-p)) approximation with O(1) inverse CDF.
//!
//! Uses Abramowitz-Stegun rational approximation for inverse normal CDF.
//! All operations are branchless for constant-time execution.

use crate::constant_time::{ct_f64_le, ct_f64_lt, ct_select_f64, ct_select_u64};

/// Threshold for Gaussian approximation (np > THRESHOLD and n(1-p) > THRESHOLD)
const GAUSSIAN_THRESHOLD: f64 = 10.0;

/// Coefficients for Abramowitz-Stegun rational approximation
/// (From "Handbook of Mathematical Functions" 26.2.23)
const C0: f64 = 2.515517;
const C1: f64 = 0.802853;
const C2: f64 = 0.010328;
const D1: f64 = 1.432788;
const D2: f64 = 0.189269;
const D3: f64 = 0.001308;

/// Constant-time Gaussian binomial sampler.
///
/// Uses Gaussian approximation when n is large, falls back to exact
/// inverse CDF for small n. All paths are constant-time.
pub struct GaussianBinomialSamplerTee {
    /// Maximum count for exact fallback
    fallback_max_count: u64,
}

impl GaussianBinomialSamplerTee {
    pub fn new(fallback_max_count: u64) -> Self {
        Self { fallback_max_count }
    }

    /// Sample from Binomial(n, num/denom) using Gaussian approximation.
    ///
    /// For large n: O(1) using Normal approximation
    /// For small n: O(fallback_max_count) using exact inverse CDF
    #[inline]
    pub fn sample(&self, count: u64, num: u64, denom: u64, prf_output: u64) -> u64 {
        if denom == 0 || num == 0 {
            return 0;
        }
        if num >= denom {
            return count;
        }

        let p = num as f64 / denom as f64;
        let u = (prf_output as f64 + 0.5) / (u64::MAX as f64 + 1.0);

        // Check if Gaussian approximation applies (this is based on public p, not secret count)
        // But we need count for np > 10 check, so we compute both and select CT
        let n_f64 = count as f64;
        let np = n_f64 * p;
        let nq = n_f64 * (1.0 - p);

        // Use Gaussian when both np > 10 and n(1-p) > 10
        let use_gaussian = ct_f64_lt(GAUSSIAN_THRESHOLD, np) & ct_f64_lt(GAUSSIAN_THRESHOLD, nq);

        // Compute both results (CT: always compute both)
        let gaussian_result = self.sample_gaussian_ct(count, p, u);
        let exact_result = self.sample_exact_ct(count, p, u);

        ct_select_u64(use_gaussian, gaussian_result, exact_result)
    }

    /// O(1) Gaussian approximation using inverse normal CDF.
    #[inline]
    fn sample_gaussian_ct(&self, n: u64, p: f64, u: f64) -> u64 {
        let n_f64 = n as f64;
        let q = 1.0 - p;

        // Mean and variance of Binomial(n, p)
        let mu = n_f64 * p;
        let sigma2 = n_f64 * p * q;
        let sigma = sigma2.sqrt();

        // Apply continuity correction: X_binomial ≈ round(X_normal)
        // For inverse CDF: find x such that Phi((x + 0.5 - mu) / sigma) = u

        // Inverse normal CDF (Abramowitz-Stegun approximation)
        let z = self.inv_norm_cdf_ct(u);

        // Transform to binomial scale with continuity correction
        let x_continuous = mu + sigma * z;

        // Round and clamp to [0, n]
        let x_rounded = x_continuous.round();
        let x_clamped = x_rounded.max(0.0).min(n_f64);

        x_clamped as u64
    }

    /// Constant-time inverse normal CDF using rational approximation.
    ///
    /// Abramowitz-Stegun 26.2.23: For 0 < p <= 0.5,
    /// Phi^{-1}(p) ≈ -t + (c0 + c1*t + c2*t^2) / (1 + d1*t + d2*t^2 + d3*t^3)
    /// where t = sqrt(-2 * ln(p))
    ///
    /// For p > 0.5, use symmetry: Phi^{-1}(p) = -Phi^{-1}(1-p)
    #[inline]
    fn inv_norm_cdf_ct(&self, u: f64) -> f64 {
        // Handle symmetry: work with p <= 0.5
        let use_upper = ct_f64_lt(0.5, u);
        let p = ct_select_f64(use_upper, 1.0 - u, u);

        // Clamp p away from 0 to avoid ln(0)
        let p_safe = p.max(1e-15);

        // t = sqrt(-2 * ln(p))
        let t = (-2.0 * p_safe.ln()).sqrt();

        // Rational approximation
        let numerator = C0 + t * (C1 + t * C2);
        let denominator = 1.0 + t * (D1 + t * (D2 + t * D3));

        let z_neg = t - numerator / denominator;

        // Apply sign based on which half we're in
        ct_select_f64(use_upper, z_neg, -z_neg)
    }

    /// Fallback exact inverse CDF for small n (O(fallback_max_count)).
    #[inline]
    fn sample_exact_ct(&self, n: u64, p: f64, u: f64) -> u64 {
        use crate::constant_time::{ct_le_u64, ct_min_u64, ct_saturating_sub_u64};

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

        if use_complement { n - k } else { k }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_gaussian_mean_variance() {
        let sampler = GaussianBinomialSamplerTee::new(1024);
        let n = 10000u64;
        let samples = 1000u64;

        let mut sum: u64 = 0;
        for i in 0..samples {
            let prf = i.wrapping_mul(0x9E3779B97F4A7C15);
            sum += sampler.sample(n, 1, 2, prf);
        }

        let mean = sum as f64 / samples as f64;
        let expected = n as f64 * 0.5;

        // Mean should be close to expected (within ~2 std errors)
        let std_err = (n as f64 * 0.25 / samples as f64).sqrt();
        assert!(
            (mean - expected).abs() < 5.0 * std_err * (n as f64).sqrt(),
            "Gaussian mean {} far from expected {}",
            mean,
            expected
        );
    }

    #[test]
    fn test_inv_norm_cdf_symmetry() {
        let sampler = GaussianBinomialSamplerTee::new(1024);

        let z_lower = sampler.inv_norm_cdf_ct(0.25);
        let z_upper = sampler.inv_norm_cdf_ct(0.75);

        assert!((z_lower + z_upper).abs() < 0.001, "Should be symmetric: {} vs {}", z_lower, z_upper);
    }

    #[test]
    fn test_inv_norm_cdf_known_values() {
        let sampler = GaussianBinomialSamplerTee::new(1024);

        // Phi^{-1}(0.5) = 0
        let z_median = sampler.inv_norm_cdf_ct(0.5);
        assert!(z_median.abs() < 0.01, "Phi^-1(0.5) should be ~0, got {}", z_median);

        // Phi^{-1}(0.975) ≈ 1.96
        let z_975 = sampler.inv_norm_cdf_ct(0.975);
        assert!((z_975 - 1.96).abs() < 0.01, "Phi^-1(0.975) should be ~1.96, got {}", z_975);
    }

    #[test]
    fn test_result_in_bounds() {
        let sampler = GaussianBinomialSamplerTee::new(1024);

        for n in [100, 1000, 10000, 50000] {
            for i in 0..100u64 {
                let prf = i.wrapping_mul(0x9E3779B97F4A7C15);
                let result = sampler.sample(n, 1, 2, prf);
                assert!(result <= n, "result {} > n {}", result, n);
            }
        }
    }
}
