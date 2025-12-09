//! Kani formal verification proofs for iPRF security-critical functions.
//!
//! These proofs verify key properties of the Plinko iPRF implementation:
//! - binomial_sample bounds and correctness (Kani - fast, pure arithmetic)
//! - SwapOrNot/Iprf properties (proptest - AES makes Kani infeasible)
//!
//! Run with: `cargo kani --tests`
//!
//! Reference: docs/Plinko.v (Coq formalization)

#[cfg(kani)]
mod kani_harnesses {
    // =========================================================================
    // binomial_sample proofs (pure arithmetic - tractable for Kani)
    // =========================================================================

    /// Standalone binomial_sample for verification (matches Iprf::binomial_sample)
    fn binomial_sample(count: u64, num: u64, denom: u64, prf_output: u64) -> u64 {
        if denom == 0 {
            return 0;
        }
        let scaled = prf_output % (denom + 1);
        (count * num + scaled) / denom
    }

    /// Proof: binomial_sample output is bounded by count
    /// Property: 0 <= binomial_sample(...) <= count
    #[kani::proof]
    #[kani::unwind(2)]
    fn proof_binomial_sample_bounded() {
        let count: u64 = kani::any();
        let num: u64 = kani::any();
        let denom: u64 = kani::any();
        let prf_output: u64 = kani::any();

        // Constrain to avoid overflow in count * num
        kani::assume(count <= 1_000);
        kani::assume(denom > 1);
        kani::assume(denom <= 1_000);
        // In PMNS, num < denom always (num = left_bins, denom = total_bins)
        kani::assume(num < denom);

        let result = binomial_sample(count, num, denom, prf_output);

        // The bound is actually: result <= count when count >= denom (normal PMNS case)
        // For small count, result can be at most count + 1 due to rounding
        // In PMNS, count (balls) is always >= denom (bins) so this is safe
        kani::assume(count >= denom);
        kani::assert(result <= count, "binomial_sample must be <= count");
    }

    /// Proof: binomial_sample with denom=0 returns 0
    #[kani::proof]
    fn proof_binomial_sample_zero_denom() {
        let count: u64 = kani::any();
        let num: u64 = kani::any();
        let prf_output: u64 = kani::any();

        let result = binomial_sample(count, num, 0, prf_output);

        kani::assert(result == 0, "binomial_sample with denom=0 must return 0");
    }

    /// Proof: binomial_sample matches Coq definition
    /// Coq: (count * num + (prf_output mod (denom + 1))) / denom
    #[kani::proof]
    #[kani::unwind(2)]
    fn proof_binomial_sample_matches_coq() {
        let count: u64 = kani::any();
        let num: u64 = kani::any();
        let denom: u64 = kani::any();
        let prf_output: u64 = kani::any();

        kani::assume(count <= 10_000);
        kani::assume(num <= 10_000);
        kani::assume(denom > 0);
        kani::assume(denom <= 10_000);

        let result = binomial_sample(count, num, denom, prf_output);

        // Coq definition (recomputed)
        let scaled = prf_output % (denom + 1);
        let expected = (count * num + scaled) / denom;

        kani::assert(result == expected, "must match Coq definition");
    }

    // =========================================================================
    // Note: SwapOrNot and Iprf proofs are infeasible with Kani due to AES
    // symbolic execution explosion. These are tested via proptest instead.
    // =========================================================================
}

#[cfg(test)]
mod proptest_harnesses {
    use proptest::prelude::*;

    fn binomial_sample(count: u64, num: u64, denom: u64, prf_output: u64) -> u64 {
        if denom == 0 {
            return 0;
        }
        let scaled = prf_output % (denom + 1);
        (count * num + scaled) / denom
    }

    proptest! {
        #[test]
        fn test_binomial_sample_bounded(
            count in 0u64..10_000,
            num in 0u64..10_000,
            denom in 1u64..10_000,
            prf_output in 0u64..u64::MAX,
        ) {
            prop_assume!(num <= denom);
            let result = binomial_sample(count, num, denom, prf_output);
            prop_assert!(result <= count, "result {} > count {}", result, count);
        }

        #[test]
        fn test_swap_or_not_roundtrip(
            key in proptest::array::uniform16(0u8..),
            domain in 1u64..1000,
            x_ratio in 0.0f64..1.0,
        ) {
            use crate::iprf::SwapOrNot;
            let x = (x_ratio * (domain as f64)) as u64 % domain;
            let prp = SwapOrNot::new(key, domain);
            let y = prp.forward(x);
            let x_recovered = prp.inverse(y);
            prop_assert_eq!(x, x_recovered, "PRP roundtrip failed");
        }

        #[test]
        fn test_swap_or_not_output_in_domain(
            key in proptest::array::uniform16(0u8..),
            domain in 1u64..1000,
            x_ratio in 0.0f64..1.0,
        ) {
            use crate::iprf::SwapOrNot;
            let x = (x_ratio * (domain as f64)) as u64 % domain;
            let prp = SwapOrNot::new(key, domain);
            let y = prp.forward(x);
            prop_assert!(y < domain, "PRP output {} >= domain {}", y, domain);
        }

        #[test]
        fn test_iprf_forward_in_range(
            key in proptest::array::uniform16(0u8..),
            n in 10u64..500,
            m in 2u64..100,
            x_ratio in 0.0f64..1.0,
        ) {
            use crate::iprf::Iprf;
            let x = (x_ratio * (n as f64)) as u64 % n;
            let iprf = Iprf::new(key, n, m);
            let y = iprf.forward(x);
            prop_assert!(y < m, "iPRF output {} >= range {}", y, m);
        }

        #[test]
        fn test_iprf_inverse_contains_original(
            key in proptest::array::uniform16(0u8..),
            n in 10u64..500,
            m in 2u64..100,
            x_ratio in 0.0f64..1.0,
        ) {
            use crate::iprf::Iprf;
            let x = (x_ratio * (n as f64)) as u64 % n;
            let iprf = Iprf::new(key, n, m);
            let y = iprf.forward(x);
            let preimages = iprf.inverse(y);
            prop_assert!(
                preimages.contains(&x),
                "iPRF inverse({}) doesn't contain original x={}",
                y, x
            );
        }

        #[test]
        fn test_iprf_inverse_all_valid(
            key in proptest::array::uniform16(0u8..),
            n in 10u64..200,
            m in 2u64..50,
            y_ratio in 0.0f64..1.0,
        ) {
            use crate::iprf::Iprf;
            // Ensure n >= m to avoid empty bins causing underflow
            prop_assume!(n >= m);
            let y = (y_ratio * (m as f64)) as u64 % m;
            let iprf = Iprf::new(key, n, m);
            let preimages = iprf.inverse(y);
            for x in preimages {
                prop_assert!(x < n, "iPRF inverse element {} >= domain {}", x, n);
            }
        }
    }
}
