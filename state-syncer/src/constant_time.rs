//! Constant-time primitives for TEE execution
//!
//! These functions are branchless and data-oblivious to prevent timing side-channels.

/// Branchless select: returns a if choice is 1, b if choice is 0
/// choice must be 0 or 1
pub fn ct_select_u64(choice: u64, a: u64, b: u64) -> u64 {
    // choice = 0 -> mask = 0, choice = 1 -> mask = u64::MAX
    let mask = choice.wrapping_neg();
    b ^ (mask & (a ^ b))
}

/// Returns 1 if a == b, 0 otherwise (constant-time)
pub fn ct_eq_u64(a: u64, b: u64) -> u64 {
    let diff = a ^ b;
    // If diff == 0, is_zero has high bit clear after this
    let is_zero = diff | diff.wrapping_neg();
    // High bit is 0 iff diff was 0; shift and invert
    1 ^ (is_zero >> 63)
}

/// Returns 1 if a < b, 0 otherwise (constant-time)
pub fn ct_lt_u64(a: u64, b: u64) -> u64 {
    // Compute borrow bit of a - b
    let borrow = ((!a) & b) | (((!a) ^ b) & a.wrapping_sub(b));
    borrow >> 63
}

/// Returns 1 if a <= b, 0 otherwise (constant-time)
pub fn ct_le_u64(a: u64, b: u64) -> u64 {
    1 ^ ct_lt_u64(b, a)
}

/// Returns 1 if a > b, 0 otherwise (constant-time)
pub fn ct_gt_u64(a: u64, b: u64) -> u64 {
    ct_lt_u64(b, a)
}

/// Returns 1 if a >= b, 0 otherwise (constant-time)
pub fn ct_ge_u64(a: u64, b: u64) -> u64 {
    1 ^ ct_lt_u64(a, b)
}

/// Constant-time f64 comparison: returns 1 if a <= b, 0 otherwise.
///
/// Works correctly for positive normalized floats (including 0.0).
/// For IEEE 754 positive floats, bit representation preserves ordering.
///
/// # Safety
/// - Both a and b must be non-negative (>= 0.0)
/// - Neither should be NaN
/// - Works correctly for +0.0, positive normals, and +inf
#[inline]
pub fn ct_f64_le(a: f64, b: f64) -> u64 {
    // For positive IEEE 754 floats, the bit representation as u64
    // has the same ordering as the float values
    let a_bits = a.to_bits();
    let b_bits = b.to_bits();
    ct_le_u64(a_bits, b_bits)
}

/// Constant-time f64 comparison: returns 1 if a < b, 0 otherwise.
#[inline]
pub fn ct_f64_lt(a: f64, b: f64) -> u64 {
    let a_bits = a.to_bits();
    let b_bits = b.to_bits();
    ct_lt_u64(a_bits, b_bits)
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    #[test]
    fn test_ct_select_basic() {
        assert_eq!(ct_select_u64(0, 100, 200), 200);
        assert_eq!(ct_select_u64(1, 100, 200), 100);
        assert_eq!(ct_select_u64(0, 0, u64::MAX), u64::MAX);
        assert_eq!(ct_select_u64(1, 0, u64::MAX), 0);
        assert_eq!(ct_select_u64(0, u64::MAX, 0), 0);
        assert_eq!(ct_select_u64(1, u64::MAX, 0), u64::MAX);
    }

    #[test]
    fn test_ct_eq_basic() {
        assert_eq!(ct_eq_u64(0, 0), 1);
        assert_eq!(ct_eq_u64(1, 1), 1);
        assert_eq!(ct_eq_u64(0, 1), 0);
        assert_eq!(ct_eq_u64(1, 0), 0);
        assert_eq!(ct_eq_u64(u64::MAX, u64::MAX), 1);
        assert_eq!(ct_eq_u64(u64::MAX, 0), 0);
    }

    #[test]
    fn test_ct_lt_basic() {
        assert_eq!(ct_lt_u64(0, 1), 1);
        assert_eq!(ct_lt_u64(1, 0), 0);
        assert_eq!(ct_lt_u64(0, 0), 0);
        assert_eq!(ct_lt_u64(1, 1), 0);
        assert_eq!(ct_lt_u64(0, u64::MAX), 1);
        assert_eq!(ct_lt_u64(u64::MAX, 0), 0);
        assert_eq!(ct_lt_u64(u64::MAX - 1, u64::MAX), 1);
    }

    #[test]
    fn test_ct_le_basic() {
        assert_eq!(ct_le_u64(0, 0), 1);
        assert_eq!(ct_le_u64(0, 1), 1);
        assert_eq!(ct_le_u64(1, 0), 0);
        assert_eq!(ct_le_u64(1, 1), 1);
        assert_eq!(ct_le_u64(u64::MAX, u64::MAX), 1);
    }

    #[test]
    fn test_ct_gt_basic() {
        assert_eq!(ct_gt_u64(1, 0), 1);
        assert_eq!(ct_gt_u64(0, 1), 0);
        assert_eq!(ct_gt_u64(0, 0), 0);
        assert_eq!(ct_gt_u64(u64::MAX, 0), 1);
        assert_eq!(ct_gt_u64(0, u64::MAX), 0);
    }

    #[test]
    fn test_ct_ge_basic() {
        assert_eq!(ct_ge_u64(0, 0), 1);
        assert_eq!(ct_ge_u64(1, 0), 1);
        assert_eq!(ct_ge_u64(0, 1), 0);
        assert_eq!(ct_ge_u64(1, 1), 1);
        assert_eq!(ct_ge_u64(u64::MAX, u64::MAX), 1);
        assert_eq!(ct_ge_u64(u64::MAX, 0), 1);
        assert_eq!(ct_ge_u64(0, u64::MAX), 0);
    }

    proptest! {
        #[test]
        fn prop_ct_select(choice in 0u64..=1, a: u64, b: u64) {
            let result = ct_select_u64(choice, a, b);
            let expected = if choice == 1 { a } else { b };
            prop_assert_eq!(result, expected);
        }

        #[test]
        fn prop_ct_eq_matches_equality(a: u64, b: u64) {
            let result = ct_eq_u64(a, b);
            let expected = if a == b { 1 } else { 0 };
            prop_assert_eq!(result, expected);
        }

        #[test]
        fn prop_ct_lt_matches_less_than(a: u64, b: u64) {
            let result = ct_lt_u64(a, b);
            let expected = if a < b { 1 } else { 0 };
            prop_assert_eq!(result, expected);
        }

        #[test]
        fn prop_ct_le_matches_less_equal(a: u64, b: u64) {
            let result = ct_le_u64(a, b);
            let expected = if a <= b { 1 } else { 0 };
            prop_assert_eq!(result, expected);
        }

        #[test]
        fn prop_ct_gt_matches_greater_than(a: u64, b: u64) {
            let result = ct_gt_u64(a, b);
            let expected = if a > b { 1 } else { 0 };
            prop_assert_eq!(result, expected);
        }

        #[test]
        fn prop_ct_ge_matches_greater_equal(a: u64, b: u64) {
            let result = ct_ge_u64(a, b);
            let expected = if a >= b { 1 } else { 0 };
            prop_assert_eq!(result, expected);
        }

        #[test]
        fn prop_ct_f64_le_matches(a in 0.0f64..1.0, b in 0.0f64..1.0) {
            let result = ct_f64_le(a, b);
            let expected = if a <= b { 1 } else { 0 };
            prop_assert_eq!(result, expected);
        }

        #[test]
        fn prop_ct_f64_lt_matches(a in 0.0f64..1.0, b in 0.0f64..1.0) {
            let result = ct_f64_lt(a, b);
            let expected = if a < b { 1 } else { 0 };
            prop_assert_eq!(result, expected);
        }
    }

    #[test]
    fn test_ct_f64_le_basic() {
        assert_eq!(ct_f64_le(0.0, 0.0), 1);
        assert_eq!(ct_f64_le(0.0, 1.0), 1);
        assert_eq!(ct_f64_le(1.0, 0.0), 0);
        assert_eq!(ct_f64_le(0.5, 0.5), 1);
        assert_eq!(ct_f64_le(0.3, 0.7), 1);
        assert_eq!(ct_f64_le(0.7, 0.3), 0);
        assert_eq!(ct_f64_le(0.0, 0.001), 1);
        assert_eq!(ct_f64_le(0.999, 1.0), 1);
    }

    #[test]
    fn test_ct_f64_lt_basic() {
        assert_eq!(ct_f64_lt(0.0, 0.0), 0);
        assert_eq!(ct_f64_lt(0.0, 1.0), 1);
        assert_eq!(ct_f64_lt(1.0, 0.0), 0);
        assert_eq!(ct_f64_lt(0.5, 0.5), 0);
        assert_eq!(ct_f64_lt(0.3, 0.7), 1);
        assert_eq!(ct_f64_lt(0.7, 0.3), 0);
    }
}
