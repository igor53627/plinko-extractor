//! True derandomized binomial sampling for PMNS.
//!
//! This module implements a proper Binomial(n, p) sampler using inverse-CDF
//! transform. When `prf_output` is uniform, the output is distributed according
//! to the binomial distribution, as required by the Plinko paper specification.
//!
//! Algorithm:
//! - Small count (<=1024): Exact inverse-CDF with PMF recurrence, O(n)
//! - Large count (>1024): Binary search over CDF using regularized incomplete beta, O(log n)
//!
//! For TEE environments, use `binomial_sample_tee` which is constant-time and
//! matches the simplified arithmetic formula in BinomialSpec.v exactly.

/// Threshold for switching between exact and approximate algorithms.
/// Below this, we use exact PMF summation. Above, we use binary search with beta function.
const EXACT_THRESHOLD: u64 = 1024;

/// Maximum value of u64 as f64 for normalization
const U64_MAX_F64: f64 = u64::MAX as f64;

/// True derandomized binomial sampler.
///
/// Given `count` trials with success probability `p = num/denom`, returns a value
/// distributed as Binomial(count, p) when `prf_output` is uniform over u64.
///
/// This implements the paper's specification:
/// "Binomial(n, p; r) will always return the same value, but over the random
/// choice of r with sufficient entropy, the output will be distributed according
/// to a binomial."
///
/// # Arguments
/// * `count` - Number of trials (n)
/// * `num` - Numerator of probability (must be <= denom)
/// * `denom` - Denominator of probability (must be > 0)
/// * `prf_output` - PRF output used as randomness source
///
/// # Returns
/// A value in [0, count] distributed as Binomial(count, num/denom)
pub fn binomial_sample(count: u64, num: u64, denom: u64, prf_output: u64) -> u64 {
    if denom == 0 {
        return 0;
    }
    if count == 0 {
        return 0;
    }
    if num == 0 {
        return 0;
    }
    if num >= denom {
        return count;
    }

    let mut p = num as f64 / denom as f64;
    let u = (prf_output as f64 + 0.5) / (U64_MAX_F64 + 1.0);

    // Use symmetry to keep p <= 0.5, avoiding underflow in q^n for exact branch
    // Binomial(n, p) = n - Binomial(n, 1-p)
    let use_complement = p > 0.5;
    if use_complement {
        p = 1.0 - p;
    }

    let k = if count <= EXACT_THRESHOLD {
        binomial_inverse_exact(count, p, u)
    } else {
        binomial_inverse_binary_search(count, p, u)
    };

    if use_complement {
        count - k
    } else {
        k
    }
}

/// Exact inverse-CDF for small count using PMF recurrence.
///
/// Complexity: O(count)
fn binomial_inverse_exact(n: u64, p: f64, u: f64) -> u64 {
    let q = 1.0 - p;

    let mut pmf = q.powi(n as i32);
    let mut cdf = pmf;

    if u <= cdf {
        return 0;
    }

    let p_over_q = p / q;

    for k in 1..=n {
        pmf *= ((n - k + 1) as f64 / k as f64) * p_over_q;
        cdf += pmf;
        if u <= cdf {
            return k;
        }
    }

    n
}

/// Inverse-CDF using binary search with regularized incomplete beta function.
///
/// Uses the identity: P(X <= k) = I_{1-p}(n-k, k+1)
/// where I_x(a,b) is the regularized incomplete beta function.
///
/// Complexity: O(log count)
fn binomial_inverse_binary_search(n: u64, p: f64, u: f64) -> u64 {
    let mut lo: u64 = 0;
    let mut hi: u64 = n;

    while lo < hi {
        let mid = lo + (hi - lo) / 2;
        let cdf = binomial_cdf(n, p, mid);

        if u <= cdf {
            hi = mid;
        } else {
            lo = mid + 1;
        }
    }

    lo
}

/// Compute binomial CDF: P(X <= k) for X ~ Binomial(n, p)
///
/// Uses the identity: P(X <= k) = I_{1-p}(n-k, k+1)
/// where I_x(a,b) is the regularized incomplete beta function.
fn binomial_cdf(n: u64, p: f64, k: u64) -> f64 {
    if k >= n {
        return 1.0;
    }

    let a = (n - k) as f64;
    let b = (k + 1) as f64;
    let x = 1.0 - p;

    puruspe::betai(a, b, x)
}

/// Maximum count for constant-time exact binomial sampling.
/// For counts above this, the O(n) iteration is too expensive.
/// In PMNS/Plinko contexts, `count` is always <= CT_BINOMIAL_MAX_COUNT,
/// which is chosen to exceed the maximum possible ball_count at any recursion
/// level (e.g., ~40k for Ethereum addresses at first recursion level).
pub const CT_BINOMIAL_MAX_COUNT: u64 = 65536;

/// TEE-safe constant-time exact binomial sampler.
///
/// Samples from Binomial(count, num/denom) distribution using inverse-CDF
/// with fixed iteration count to prevent timing side-channels.
///
/// Security properties:
/// - Always iterates exactly `CT_BINOMIAL_MAX_COUNT + 1` times (no early exit)
/// - Uses constant-time float comparison and selection
/// - No branches depend on `count` or `prf_output` (both are secret)
/// - Loop bounds depend only on public constants
///
/// Complexity: O(CT_BINOMIAL_MAX_COUNT) - fixed cost regardless of count
///
/// # TEE Usage
/// In TEE/constant-time contexts, callers MUST ensure `count <= CT_BINOMIAL_MAX_COUNT`.
/// This is a protocol-level invariant; exceeding it is a programmer error.
///
/// # Panics
/// Panics in debug mode if count > CT_BINOMIAL_MAX_COUNT.
#[inline]
pub fn binomial_sample_tee(count: u64, num: u64, denom: u64, prf_output: u64) -> u64 {
    use crate::constant_time::{ct_eq_u64, ct_select_u64};

    // Edge cases with public parameters only - these branches are on public values
    // (num, denom are fixed protocol parameters like 1/2)
    if denom == 0 {
        return 0;
    }
    if num == 0 {
        return 0;
    }
    if num >= denom {
        return count;
    }

    debug_assert!(
        count <= CT_BINOMIAL_MAX_COUNT,
        "binomial_sample_tee: count {} exceeds CT_BINOMIAL_MAX_COUNT {}",
        count,
        CT_BINOMIAL_MAX_COUNT
    );

    let mut p = num as f64 / denom as f64;
    let u = (prf_output as f64 + 0.5) / (U64_MAX_F64 + 1.0);

    // Use symmetry to keep p <= 0.5, avoiding underflow in q^n
    // This branch is on public parameter p
    let use_complement = p > 0.5;
    if use_complement {
        p = 1.0 - p;
    }

    // Handle count == 0 via CT masking instead of branching (count may be secret)
    let count_is_zero = ct_eq_u64(count, 0);
    let k = binomial_inverse_ct(count, p, u);

    // Apply complement if needed, but return 0 if count was 0
    let result = if use_complement { count - k } else { k };
    ct_select_u64(count_is_zero, 0, result)
}

/// Constant-time inverse-CDF binomial sampler with fixed iterations.
///
/// Always iterates exactly CT_BINOMIAL_MAX_COUNT+1 times regardless of n or
/// when the answer is found. Uses constant-time selection to track the result.
/// Loop bounds depend only on CT_BINOMIAL_MAX_COUNT (public constant), not on n.
///
/// Uses log-space PMF recurrence to avoid underflow. For n=40k and p=0.5,
/// the initial PMF(0) = q^n underflows to 0.0, but this is harmless since
/// those probabilities are below f64 precision anyway. The recurrence
/// log_pmf_{k+1} = log_pmf_k + ln((n-k)/(k+1)) + ln(p/q) stays in log-space
/// and produces valid PMF values near the mode where they matter.
///
/// Single-loop design: O(CT_BINOMIAL_MAX_COUNT) iterations instead of 3x that.
fn binomial_inverse_ct(n: u64, p: f64, u: f64) -> u64 {
    use crate::constant_time::{
        ct_f64_le, ct_le_u64, ct_max_u64, ct_min_u64, ct_saturating_sub_u64, ct_select_f64,
        ct_select_u64,
    };

    debug_assert!(
        n <= CT_BINOMIAL_MAX_COUNT,
        "binomial_inverse_ct: n={} exceeds CT_BINOMIAL_MAX_COUNT={}",
        n,
        CT_BINOMIAL_MAX_COUNT
    );

    // CT-safe clamping: if n > CT_BINOMIAL_MAX_COUNT, clamp to max (best effort).
    // This maintains constant-time behavior even for out-of-range inputs.
    // In release builds, this provides graceful degradation instead of UB.
    let n = ct_min_u64(n, CT_BINOMIAL_MAX_COUNT);

    let q = 1.0 - p;
    let log_q = q.ln();
    let log_p = p.ln();
    let log_p_over_q = log_p - log_q;

    // Start from k = 0: log(P(X=0)) = n * log(q)
    // For large n this may be very negative (e.g., -27726 for n=40k, p=0.5),
    // causing exp() to underflow to 0.0, which is fine.
    let mut log_pmf = (n as f64) * log_q;
    let mut cdf = 0.0f64;
    let mut result = 0u64;
    let mut found = 0u64;

    for k in 0..=CT_BINOMIAL_MAX_COUNT {
        let in_support = ct_le_u64(k, n);

        // PMF in linear space; underflow to 0.0 is fine for tiny probabilities.
        // exp() input range: log_pmf varies from n*log(q) (very negative for large n)
        // to ~-5 near the mode. We never hit NaN/INF cases:
        // - exp(-inf) = 0.0 (graceful underflow)
        // - exp(small negative) = valid PMF
        // CT note: libm exp() may have data-dependent latency, but this is
        // acceptable per our threat model (we already use f64 arithmetic throughout).
        let pmf = ct_select_f64(in_support, log_pmf.exp(), 0.0);
        cdf += pmf;

        // Check if u <= cdf and this is the first time we cross it
        let cond = ct_f64_le(u, cdf) & in_support;
        let is_first = (1 ^ found) & cond;
        result = ct_select_u64(is_first, k, result);
        found |= cond;

        // Update log PMF to k+1:
        // log P(X=k+1) = log P(X=k) + ln((n-k)/(k+1)) + ln(p/q)
        let n_minus_k = ct_saturating_sub_u64(n, k); // 0 when k >= n
        let k_plus_1 = ct_max_u64(k + 1, 1); // avoid div by 0

        // For k >= n, ratio = 0 => ln(0) = -inf, so log_pmf -> -inf; exp(-inf) = 0 as desired
        let ratio = (n_minus_k as f64) / (k_plus_1 as f64);
        let log_ratio = ratio.ln() + log_p_over_q;
        log_pmf += log_ratio;
    }

    ct_select_u64(found, result, n)
}

/// Lanczos approximation for log-gamma function.
///
/// # Note
/// This function is currently unused after the single-loop optimization in
/// `binomial_inverse_ct`, but is kept for reference and potential future use
/// (e.g., mode-based numerical stability approaches).
///
/// # Precondition
/// x >= 1.0 (enforced by debug_assert in TEE contexts).
///
/// # CT Safety
/// This function has no branches or data-dependent indexing on x.
/// The loop iterates a fixed 8 times regardless of input.
#[allow(dead_code)]
#[inline]
fn lgamma_approx(x: f64) -> f64 {
    use std::f64::consts::PI;

    debug_assert!(
        x >= 1.0,
        "lgamma_approx: x={} must be >= 1.0 for CT-safe execution",
        x
    );

    let g = 7.0;
    let coeffs = [
        0.999_999_999_999_809_9,
        676.5203681218851,
        -1259.1392167224028,
        771.323_428_777_653_1,
        -176.615_029_162_140_6,
        12.507343278686905,
        -0.13857109526572012,
        9.984_369_578_019_572e-6,
        1.5056327351493116e-7,
    ];

    let x = x - 1.0;
    let mut sum = coeffs[0];
    for (i, &c) in coeffs.iter().enumerate().skip(1) {
        sum += c / (x + i as f64);
    }

    let t = x + g + 0.5;
    0.5 * (2.0 * PI).ln() + (x + 0.5) * t.ln() - t + sum.ln()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_edge_cases() {
        assert_eq!(binomial_sample(0, 1, 2, 12345), 0);
        assert_eq!(binomial_sample(10, 0, 2, 12345), 0);
        assert_eq!(binomial_sample(10, 2, 2, 12345), 10);
        assert_eq!(binomial_sample(10, 3, 2, 12345), 10);
        assert_eq!(binomial_sample(10, 1, 0, 12345), 0);
    }

    #[test]
    fn test_range_bounds() {
        for count in [1, 10, 100, 1000, 2000] {
            for prf in [0u64, u64::MAX / 2, u64::MAX] {
                let result = binomial_sample(count, 1, 2, prf);
                assert!(result <= count, "result {} > count {}", result, count);
            }
        }
    }

    #[test]
    fn test_deterministic() {
        let r1 = binomial_sample(100, 1, 2, 42);
        let r2 = binomial_sample(100, 1, 2, 42);
        assert_eq!(r1, r2);
    }

    #[test]
    fn test_distribution_mean() {
        let n = 100u64;
        let num = 1u64;
        let denom = 2u64;
        let expected_mean = n as f64 * (num as f64 / denom as f64);

        let samples: u64 = 10000;
        let mut sum: u64 = 0;
        for i in 0..samples {
            let prf = (i as u64).wrapping_mul(0x9E3779B97F4A7C15);
            sum += binomial_sample(n, num, denom, prf);
        }

        let actual_mean = sum as f64 / samples as f64;
        let tolerance = 2.0;
        assert!(
            (actual_mean - expected_mean).abs() < tolerance,
            "mean {} too far from expected {}",
            actual_mean,
            expected_mean
        );
    }

    #[test]
    fn test_full_support() {
        let n = 20u64;
        let mut seen = vec![false; (n + 1) as usize];

        for i in 0..100000u64 {
            let prf = i.wrapping_mul(0x9E3779B97F4A7C15);
            let k = binomial_sample(n, 1, 2, prf);
            seen[k as usize] = true;
        }

        let count_seen = seen.iter().filter(|&&x| x).count();
        assert!(
            count_seen >= 15,
            "should see most values in [0,20], only saw {}",
            count_seen
        );
    }

    #[test]
    fn test_exact_vs_binary_search_consistency() {
        let n = 1024u64;
        let p = 0.3;

        for i in 0..1000u64 {
            let prf = i.wrapping_mul(0x9E3779B97F4A7C15);
            let u = (prf as f64 + 0.5) / (U64_MAX_F64 + 1.0);

            let exact = binomial_inverse_exact(n, p, u);
            let binary = binomial_inverse_binary_search(n, p, u);

            assert!(
                exact == binary || exact.abs_diff(binary) <= 1,
                "mismatch at prf={}: exact={}, binary={}",
                prf,
                exact,
                binary
            );
        }
    }

    #[test]
    fn test_large_count() {
        let n = 1_000_000u64;
        let result = binomial_sample(n, 1, 2, 0x123456789ABCDEF0);
        assert!(result <= n, "result should be <= n");
    }

    #[test]
    fn test_high_probability() {
        let n = 1024u64;
        let mut sum: u64 = 0;
        let samples = 1000;

        for i in 0..samples {
            let prf = (i as u64).wrapping_mul(0x9E3779B97F4A7C15);
            let k = binomial_sample(n, 9, 10, prf);
            assert!(k <= n, "result {} > count {}", k, n);
            sum += k;
        }

        let actual_mean = sum as f64 / samples as f64;
        let expected_mean = n as f64 * 0.9;
        let tolerance = 20.0;
        assert!(
            (actual_mean - expected_mean).abs() < tolerance,
            "mean {} too far from expected {} for p=0.9",
            actual_mean,
            expected_mean
        );
    }

    #[test]
    fn test_symmetry_correctness() {
        let n = 100u64;
        let samples = 1000u64;
        let mut sum_low: u64 = 0;
        let mut sum_high: u64 = 0;

        for i in 0..samples {
            let prf = i.wrapping_mul(0x9E3779B97F4A7C15);

            let k_low = binomial_sample(n, 1, 4, prf);
            let k_high = binomial_sample(n, 3, 4, prf);

            assert!(k_low <= n);
            assert!(k_high <= n);

            sum_low += k_low;
            sum_high += k_high;
        }

        let mean_low = sum_low as f64 / samples as f64;
        let mean_high = sum_high as f64 / samples as f64;

        assert!(
            mean_high > mean_low,
            "mean for p=0.75 ({}) should exceed mean for p=0.25 ({})",
            mean_high,
            mean_low
        );
    }

    // ============================================================================
    // TEE Binomial Sampler Tests (binomial_sample_tee) - True Binomial CT Version
    // ============================================================================

    #[test]
    fn test_tee_matches_standard_binomial() {
        // Verify binomial_sample_tee produces same results as binomial_sample
        // (both use true binomial distribution, but TEE version is constant-time)
        for count in [1, 10, 50, 100, 500] {
            for (num, denom) in [(1, 2), (1, 4), (3, 4), (1, 10), (9, 10)] {
                for i in 0..50u64 {
                    let prf = i.wrapping_mul(0x9E3779B97F4A7C15);
                    let standard = binomial_sample(count, num, denom, prf);
                    let tee = binomial_sample_tee(count, num, denom, prf);
                    assert_eq!(
                        standard, tee,
                        "Mismatch: count={}, num={}, denom={}, prf={}: standard={}, tee={}",
                        count, num, denom, prf, standard, tee
                    );
                }
            }
        }
    }

    #[test]
    fn test_tee_edge_cases() {
        // denom = 0 always returns 0
        assert_eq!(binomial_sample_tee(100, 50, 0, 12345), 0);
        assert_eq!(binomial_sample_tee(0, 0, 0, 0), 0);

        // count = 0 always returns 0
        assert_eq!(binomial_sample_tee(0, 1, 2, 0), 0);
        assert_eq!(binomial_sample_tee(0, 1, 2, u64::MAX), 0);

        // num = 0 always returns 0
        assert_eq!(binomial_sample_tee(100, 0, 10, 5), 0);

        // num >= denom returns count
        assert_eq!(binomial_sample_tee(10, 20, 10, 0), 10);
        assert_eq!(binomial_sample_tee(10, 10, 10, 12345), 10);
    }

    #[test]
    fn test_tee_range_bounds() {
        // Result should always be in [0, count]
        for count in [1, 10, 100, 500, 1000] {
            for (num, denom) in [(1, 2), (1, 4), (3, 4), (1, 10)] {
                for i in 0..100u64 {
                    let prf = i.wrapping_mul(0x9E3779B97F4A7C15);
                    let result = binomial_sample_tee(count, num, denom, prf);
                    assert!(
                        result <= count,
                        "Range violation: count={}, num={}, denom={}, result={}",
                        count,
                        num,
                        denom,
                        result
                    );
                }
            }
        }
    }

    #[test]
    fn test_tee_deterministic() {
        let r1 = binomial_sample_tee(100, 1, 2, 42);
        let r2 = binomial_sample_tee(100, 1, 2, 42);
        assert_eq!(r1, r2);
    }

    #[test]
    fn test_tee_distribution_mean() {
        // The CT version should have the same distribution as true binomial
        let n = 100u64;
        let num = 1u64;
        let denom = 2u64;
        let expected_mean = n as f64 * (num as f64 / denom as f64);

        let samples: u64 = 10000;
        let mut sum: u64 = 0;
        for i in 0..samples {
            let prf = (i as u64).wrapping_mul(0x9E3779B97F4A7C15);
            sum += binomial_sample_tee(n, num, denom, prf);
        }

        let actual_mean = sum as f64 / samples as f64;
        let tolerance = 2.0;
        assert!(
            (actual_mean - expected_mean).abs() < tolerance,
            "TEE mean {} too far from expected {}",
            actual_mean,
            expected_mean
        );
    }

    #[test]
    fn test_tee_full_support() {
        // Should see values across the full support [0, n]
        let n = 20u64;
        let mut seen = vec![false; (n + 1) as usize];

        for i in 0..100000u64 {
            let prf = i.wrapping_mul(0x9E3779B97F4A7C15);
            let k = binomial_sample_tee(n, 1, 2, prf);
            seen[k as usize] = true;
        }

        let count_seen = seen.iter().filter(|&&x| x).count();
        assert!(
            count_seen >= 15,
            "TEE should see most values in [0,20], only saw {}",
            count_seen
        );
    }

    #[test]
    fn test_tee_symmetry() {
        // Binomial(n, p) should be symmetric with Binomial(n, 1-p)
        let n = 100u64;
        let samples = 1000u64;
        let mut sum_low: u64 = 0;
        let mut sum_high: u64 = 0;

        for i in 0..samples {
            let prf = i.wrapping_mul(0x9E3779B97F4A7C15);
            sum_low += binomial_sample_tee(n, 1, 4, prf);
            sum_high += binomial_sample_tee(n, 3, 4, prf);
        }

        let mean_low = sum_low as f64 / samples as f64;
        let mean_high = sum_high as f64 / samples as f64;

        assert!(
            mean_high > mean_low,
            "TEE mean for p=0.75 ({}) should exceed mean for p=0.25 ({})",
            mean_high,
            mean_low
        );
    }

    #[test]
    fn test_tee_at_threshold() {
        // Test at exactly the threshold (should work without fallback)
        let count = super::CT_BINOMIAL_MAX_COUNT;
        let result = binomial_sample_tee(count, 1, 2, 12345);
        assert!(result <= count);
    }

    #[test]
    fn test_tee_large_count_ethereum() {
        // Test with ~40k count (Ethereum address use case)
        // This verifies numerical stability - old implementation would underflow
        let n = 40000u64;
        let num = 1u64;
        let denom = 2u64;
        let expected_mean = n as f64 * (num as f64 / denom as f64);

        let samples = 100u64;
        let mut sum: u64 = 0;
        for i in 0..samples {
            let prf = (i as u64).wrapping_mul(0x9E3779B97F4A7C15);
            let result = binomial_sample_tee(n, num, denom, prf);
            assert!(result <= n, "result {} > n {}", result, n);
            sum += result;
        }

        let actual_mean = sum as f64 / samples as f64;
        // Allow larger tolerance for fewer samples
        let tolerance = 500.0;
        assert!(
            (actual_mean - expected_mean).abs() < tolerance,
            "TEE large-n mean {} too far from expected {} (tolerance {})",
            actual_mean,
            expected_mean,
            tolerance
        );
    }
}
