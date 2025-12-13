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
/// In PMNS context, ball_count at each level is typically much smaller.
pub const CT_BINOMIAL_MAX_COUNT: u64 = 4096;

/// TEE-safe constant-time exact binomial sampler.
///
/// Samples from Binomial(count, num/denom) distribution using inverse-CDF
/// with fixed iteration count to prevent timing side-channels.
///
/// Security properties:
/// - Always iterates exactly `count + 1` times (no early exit)
/// - Uses constant-time float comparison and selection
/// - No branches depend on `prf_output` (secret-derived)
///
/// Complexity: O(count) - suitable for count <= 4096
///
/// # TEE Usage
/// In TEE/constant-time contexts, callers MUST ensure `count <= CT_BINOMIAL_MAX_COUNT`
/// (e.g., via a constructor assertion as in `IprfTee::new`). The fallback for larger
/// counts is NOT constant-time and uses an arithmetic approximation instead of true
/// binomial distribution.
///
/// # Panics
/// Panics in debug mode if count > CT_BINOMIAL_MAX_COUNT (4096).
/// In release mode, falls back to arithmetic approximation for large counts.
#[inline]
pub fn binomial_sample_tee(count: u64, num: u64, denom: u64, prf_output: u64) -> u64 {
    // Edge cases with public parameters only - these branches are on public values
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

    // For very large counts, fall back to arithmetic approximation
    // This is a public-parameter branch (count is public in PMNS context)
    if count > CT_BINOMIAL_MAX_COUNT {
        debug_assert!(
            false,
            "binomial_sample_tee: count {} exceeds CT_BINOMIAL_MAX_COUNT {}",
            count, CT_BINOMIAL_MAX_COUNT
        );
        return binomial_sample_tee_approx(count, num, denom, prf_output);
    }

    let mut p = num as f64 / denom as f64;
    let u = (prf_output as f64 + 0.5) / (U64_MAX_F64 + 1.0);

    // Use symmetry to keep p <= 0.5, avoiding underflow in q^n
    // This branch is on public parameter p
    let use_complement = p > 0.5;
    if use_complement {
        p = 1.0 - p;
    }

    let k = binomial_inverse_ct(count, p, u);

    if use_complement {
        count - k
    } else {
        k
    }
}

/// Constant-time inverse-CDF binomial sampler with fixed iterations.
///
/// Always iterates exactly n+1 times regardless of when the answer is found.
/// Uses constant-time selection to track the result.
fn binomial_inverse_ct(n: u64, p: f64, u: f64) -> u64 {
    use crate::constant_time::{ct_f64_le, ct_select_u64};

    let q = 1.0 - p;

    // Initial PMF: P(X = 0) = q^n
    let mut pmf = q.powi(n as i32);
    let mut cdf = pmf;

    // Track result and whether we've found it (using CT operations)
    let mut result = 0u64;
    let mut found = 0u64; // 0 = not found yet, 1 = found

    // Check k = 0
    {
        let cond = ct_f64_le(u, cdf);
        // is_first = 1 iff (not found yet) AND (u <= cdf)
        let is_first = (1 ^ found) & cond;
        result = ct_select_u64(is_first, 0, result);
        found |= cond;
    }

    let p_over_q = p / q;

    // Iterate k = 1 to n (always all iterations, no early exit)
    for k in 1..=n {
        // PMF recurrence: P(X=k) = P(X=k-1) * (n-k+1)/k * p/q
        pmf *= ((n - k + 1) as f64 / k as f64) * p_over_q;
        cdf += pmf;

        let cond = ct_f64_le(u, cdf);
        // is_first = 1 iff this is the first k where u <= cdf
        let is_first = (1 ^ found) & cond;
        result = ct_select_u64(is_first, k, result);
        found |= cond;
    }

    // If not found (shouldn't happen for valid input), return n
    ct_select_u64(found, result, n)
}

/// Fallback arithmetic approximation for very large counts.
/// Uses the simplified formula from BinomialSpec.v.
/// NOT a true binomial distribution (produces a narrow deterministic range
/// around n*p), but O(1). Unreachable when IprfTee enforces count <= 4096.
#[inline]
fn binomial_sample_tee_approx(count: u64, num: u64, denom: u64, prf_output: u64) -> u64 {
    let denom128 = denom as u128;
    let r = (prf_output as u128) % (denom128 + 1);
    let numerator = (count as u128) * (num as u128) + r;
    (numerator / denom128) as u64
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
    #[cfg_attr(debug_assertions, ignore)] // Fallback panics in debug mode
    fn test_tee_large_count_fallback() {
        // Large counts should still work (via fallback approximation)
        // This test is ignored in debug mode because we assert on large counts
        let count = 10000u64;
        let result = binomial_sample_tee(count, 1, 2, 12345);
        assert!(result <= count);
    }

    #[test]
    fn test_tee_at_threshold() {
        // Test at exactly the threshold (should work without fallback)
        let count = super::CT_BINOMIAL_MAX_COUNT;
        let result = binomial_sample_tee(count, 1, 2, 12345);
        assert!(result <= count);
    }
}
