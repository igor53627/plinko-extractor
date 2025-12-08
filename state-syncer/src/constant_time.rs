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
    }
}
