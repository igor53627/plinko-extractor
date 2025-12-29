//! Constant-time primitives for TEE execution
//!
//! These functions are branchless and data-oblivious to prevent timing side-channels.
//!
//! # Design Principles
//!
//! 1. **No conditional branches on secret data**: All functions use bitwise operations
//!    and arithmetic instead of `if` statements when the condition depends on secrets.
//!
//! 2. **Fixed execution time**: Each function performs the same operations regardless
//!    of input values. For example, `ct_select_u64` always computes the mask and XOR,
//!    even when selecting between equal values.
//!
//! 3. **Composable building blocks**: Complex constant-time operations are built from
//!    simple primitives (comparison, selection, masked operations).
//!
//! # Security Model
//!
//! These primitives protect against timing side-channels but NOT cache side-channels.
//! Memory access patterns (which cache lines are touched) may still depend on secret
//! values. For full memory-access obliviousness, ORAM techniques would be required.
//!
//! # Usage in Plinko
//!
//! The Plinko hint generator uses these primitives in constant-time mode (--constant-time)
//! to prevent leaking iPRF mappings during TEE execution. Key uses:
//!
//! - `ct_lt_u64`: Compare loop index against preimage count
//! - `ct_select_usize`: Clamp array indices without branching
//! - `ct_xor_32_masked`: Conditionally XOR parity values
//! - `ct_f64_le`, `ct_select_f64`: Constant-time binomial sampling in IprfTee

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

/// Constant-time minimum: returns min(a, b) without branching
#[inline]
pub fn ct_min_u64(a: u64, b: u64) -> u64 {
    let a_lt_b = ct_lt_u64(a, b);
    ct_select_u64(a_lt_b, a, b)
}

/// Constant-time maximum: returns max(a, b) without branching
#[inline]
pub fn ct_max_u64(a: u64, b: u64) -> u64 {
    let a_lt_b = ct_lt_u64(a, b);
    ct_select_u64(a_lt_b, b, a)
}

/// Constant-time saturating subtraction: returns a - b, or 0 if a < b
#[inline]
pub fn ct_saturating_sub_u64(a: u64, b: u64) -> u64 {
    let a_lt_b = ct_lt_u64(a, b);
    let diff = a.wrapping_sub(b);
    ct_select_u64(a_lt_b, 0, diff)
}

/// Constant-time XOR with mask: dst ^= src if mask == 1, else no-op.
///
/// # Implementation
///
/// Uses the identity: `mask.wrapping_neg()` produces:
/// - `0x00` when mask = 0 (no XOR effect)
/// - `0xFF` when mask = 1 (full XOR)
///
/// This avoids branching on the mask value while achieving conditional XOR.
///
/// # Invariant
///
/// Caller must ensure `mask` is either 0 or 1. Other values produce incorrect results.
/// In Plinko's CT HintInit, masks are derived from `ct_lt_u64` which guarantees this.
#[inline]
pub fn ct_xor_32_masked(dst: &mut [u8; 32], src: &[u8; 32], mask: u64) {
    let m = (mask.wrapping_neg()) as u8;
    for i in 0..32 {
        dst[i] ^= src[i] & m;
    }
}

/// Constant-time select for u8: returns a if choice == 1, b if choice == 0
#[inline]
pub fn ct_select_u8(choice: u64, a: u8, b: u8) -> u8 {
    let mask = (choice.wrapping_neg()) as u8;
    b ^ (mask & (a ^ b))
}

/// Constant-time select for usize: returns a if choice == 1, b if choice == 0
#[inline]
pub fn ct_select_usize(choice: u64, a: usize, b: usize) -> usize {
    ct_select_u64(choice, a as u64, b as u64) as usize
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

/// Branchless select for f64: returns a if choice is 1, b if choice is 0
/// choice must be 0 or 1
#[inline]
pub fn ct_select_f64(choice: u64, a: f64, b: f64) -> f64 {
    let a_bits = a.to_bits();
    let b_bits = b.to_bits();
    f64::from_bits(ct_select_u64(choice, a_bits, b_bits))
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

    #[test]
    fn test_ct_min_max_basic() {
        assert_eq!(ct_min_u64(0, 1), 0);
        assert_eq!(ct_min_u64(1, 0), 0);
        assert_eq!(ct_min_u64(5, 5), 5);
        assert_eq!(ct_min_u64(u64::MAX, 0), 0);
        assert_eq!(ct_min_u64(0, u64::MAX), 0);

        assert_eq!(ct_max_u64(0, 1), 1);
        assert_eq!(ct_max_u64(1, 0), 1);
        assert_eq!(ct_max_u64(5, 5), 5);
        assert_eq!(ct_max_u64(u64::MAX, 0), u64::MAX);
        assert_eq!(ct_max_u64(0, u64::MAX), u64::MAX);
    }

    #[test]
    fn test_ct_saturating_sub_basic() {
        assert_eq!(ct_saturating_sub_u64(5, 3), 2);
        assert_eq!(ct_saturating_sub_u64(3, 5), 0);
        assert_eq!(ct_saturating_sub_u64(0, 0), 0);
        assert_eq!(ct_saturating_sub_u64(0, 1), 0);
        assert_eq!(ct_saturating_sub_u64(u64::MAX, 1), u64::MAX - 1);
        assert_eq!(ct_saturating_sub_u64(1, u64::MAX), 0);
    }

    proptest! {
        #[test]
        fn prop_ct_min_matches_std(a: u64, b: u64) {
            prop_assert_eq!(ct_min_u64(a, b), a.min(b));
        }

        #[test]
        fn prop_ct_max_matches_std(a: u64, b: u64) {
            prop_assert_eq!(ct_max_u64(a, b), a.max(b));
        }

        #[test]
        fn prop_ct_saturating_sub_matches_std(a: u64, b: u64) {
            prop_assert_eq!(ct_saturating_sub_u64(a, b), a.saturating_sub(b));
        }
    }
}
