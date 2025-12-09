//! True derandomized binomial sampling for PMNS.
//!
//! This module implements a proper Binomial(n, p) sampler using inverse-CDF
//! transform. When `prf_output` is uniform, the output is distributed according
//! to the binomial distribution, as required by the Plinko paper specification.
//!
//! Algorithm:
//! - Small count (<=1024): Exact inverse-CDF with PMF recurrence, O(n)
//! - Large count (>1024): Binary search over CDF using regularized incomplete beta, O(log n)

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
        for i in 0..100u64 {
            let prf = i.wrapping_mul(0x9E3779B97F4A7C15);

            let k_low = binomial_sample(n, 1, 4, prf);
            let k_high = binomial_sample(n, 3, 4, prf);

            assert!(k_low <= n);
            assert!(k_high <= n);
            assert!(
                k_high >= k_low,
                "p=0.75 should give higher values than p=0.25 on average"
            );
        }
    }
}
