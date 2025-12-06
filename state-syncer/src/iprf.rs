//! Invertible Pseudorandom Function (iPRF) for Plinko PIR
//!
//! Implementation based on the Plinko paper (2024-318):
//! - iPRF is built from Swap-or-Not PRP + PMNS (Pseudorandom Multinomial Sampler)
//! - Forward: iF.F(k, x) = S(k_pmns, P(k_prp, x))
//! - Inverse: iF.F^{-1}(k, y) = {P^{-1}(k_prp, z) : z ∈ S^{-1}(k_pmns, y)}
//!
//! The Swap-or-Not PRP is based on Morris-Rogaway (eprint 2013/560).

use aes::cipher::{generic_array::GenericArray, BlockEncrypt, KeyInit};
use aes::Aes128;
use sha2::{Digest, Sha256};

pub type PrfKey128 = [u8; 16];

/// Swap-or-Not small-domain PRP (Morris-Rogaway 2013)
///
/// Achieves full security (withstands all N queries) in O(n log n) time.
/// Each round is an involution, so inversion just runs rounds in reverse.
pub struct SwapOrNot {
    cipher: Aes128,
    domain: u64,
    num_rounds: usize,
}

impl SwapOrNot {
    /// Creates a new SwapOrNot PRP instance for a finite domain.
    ///
    /// The `key` is a 16-byte AES-128 key used to initialize the internal cipher.
    /// `domain` is the size of the finite domain (must be greater than zero); the
    /// PRP operates over the integer set [0, domain).
    ///
    /// # Panics
    ///
    /// Panics if `domain` is zero.
    ///
    /// # Examples
    ///
    /// ```
    /// let key: PrfKey128 = [0u8; 16];
    /// let prp = SwapOrNot::new(key, 100);
    /// let y = prp.forward(42);
    /// assert!(y < 100);
    /// ```
    pub fn new(key: PrfKey128, domain: u64) -> Self {
        assert!(domain > 0, "SwapOrNot domain must be positive");
        let cipher = Aes128::new(&GenericArray::from(key));
        // ~6 * log2(N) rounds for full security
        let num_rounds = ((domain as f64).log2().ceil() as usize) * 6 + 6;

        Self {
            cipher,
            domain,
            num_rounds,
        }
    }

    /// Derives the round-specific key K_i from the PRP key and domain using AES.
    ///
    /// The function encrypts a 16-byte block formed from `round` (big-endian u64) and `domain`
    /// (big-endian u64), interprets the upper 64 bits of the ciphertext as a u64, and reduces
    /// it modulo `self.domain` to produce a value in the domain range.
    ///
    /// # Parameters
    ///
    /// - `round`: Round index (0-based) for which to derive the round key.
    ///
    /// # Returns
    ///
    /// `K_i` — a `u64` in the range `0..self.domain` representing the derived round key.
    fn derive_round_key(&self, round: usize) -> u64 {
        let mut input = [0u8; 16];
        input[0..8].copy_from_slice(&(round as u64).to_be_bytes());
        input[8..16].copy_from_slice(&self.domain.to_be_bytes());

        let mut block = GenericArray::from(input);
        self.cipher.encrypt_block(&mut block);

        u64::from_be_bytes(block[0..8].try_into().unwrap()) % self.domain
    }

    /// Derives the single-bit pseudorandom decision used to choose whether to swap in a Swap-or-Not round.
    ///
    /// # Examples
    ///
    /// ```
    /// let key: PrfKey128 = [0u8; 16];
    /// let prp = SwapOrNot::new(key, 100);
    /// let decision = prp.prf_bit(0, 42);
    /// // decision is a boolean indicating the swap choice for round 0 and canonical value 42
    /// assert!(decision == true || decision == false);
    /// ```
    fn prf_bit(&self, round: usize, canonical: u64) -> bool {
        let mut input = [0u8; 16];
        input[0..8].copy_from_slice(&(round as u64 | 0x8000000000000000).to_be_bytes());
        input[8..16].copy_from_slice(&canonical.to_be_bytes());

        let mut block = GenericArray::from(input);
        self.cipher.encrypt_block(&mut block);

        (block[0] & 1) == 1
    }

    /// Applies one round of the Swap-or-Not permutation to a value within the domain.
    ///
    /// The round computes a partner value K_i - x (mod N) using a round-specific key,
    /// chooses the canonical representative between the input and its partner, and
    /// uses a round-dependent PRF bit to decide whether to swap to the partner or
    /// keep the input. The operation is involutory: applying the same round again
    /// undoes the effect.
    ///
    /// # Examples
    ///
    /// ```
    /// let key: [u8; 16] = [0u8; 16];
    /// let prp = SwapOrNot::new(key, 10).unwrap();
    /// let x = 3u64;
    /// let y = prp.round(0, x);
    /// assert!(y < 10);
    /// // round is self-inverse
    /// assert_eq!(prp.round(0, y), x);
    /// ```
    fn round(&self, round_num: usize, x: u64) -> u64 {
        let k_i = self.derive_round_key(round_num);
        // Partner: K_i - X mod N
        let partner = (k_i + self.domain - (x % self.domain)) % self.domain;
        // Canonical representative: max(X, X')
        let canonical = x.max(partner);

        if self.prf_bit(round_num, canonical) {
            partner
        } else {
            x
        }
    }

    /// Forward PRP: encrypt by running rounds 0, 1, ..., r-1
    pub fn forward(&self, x: u64) -> u64 {
        let mut val = x;
        for round in 0..self.num_rounds {
            val = self.round(round, val);
        }
        val
    }

    /// Inverse PRP: decrypt by running rounds r-1, r-2, ..., 0
    pub fn inverse(&self, y: u64) -> u64 {
        let mut val = y;
        for round in (0..self.num_rounds).rev() {
            val = self.round(round, val);
        }
        val
    }
}

/// Invertible PRF built from Swap-or-Not PRP + PMNS
pub struct Iprf {
    key: PrfKey128,
    cipher: Aes128,
    prp: SwapOrNot,
    domain: u64,
    range: u64,
    _tree_depth: usize,
}

impl Iprf {
    /// Creates a new iPRF instance for input domain `n` and output range `m`.
    ///
    /// The constructor derives an internal AES-128 cipher from `key`, computes the PMNS
    /// tree depth as ceil(log2(m)), and derives a separate 128-bit key (SHA-256(key || "prp"))
    /// to initialize the internal Swap-or-Not PRP over the input domain `n`.
    ///
    /// # Examples
    ///
    /// ```
    /// let key: PrfKey128 = [0u8; 16];
    /// let iprf = Iprf::new(key, 100, 10);
    /// let y = iprf.forward(0);
    /// assert!(y < 10);
    /// ```
    pub fn new(key: PrfKey128, n: u64, m: u64) -> Self {
        let tree_depth = (m as f64).log2().ceil() as usize;
        let cipher = Aes128::new(&GenericArray::from(key));

        // Derive a separate key for PRP from main key
        let mut prp_key = [0u8; 16];
        let mut hasher = Sha256::new();
        hasher.update(&key);
        hasher.update(b"prp");
        let hash = hasher.finalize();
        prp_key.copy_from_slice(&hash[0..16]);

        let prp = SwapOrNot::new(prp_key, n);

        Self {
            key,
            cipher,
            prp,
            domain: n,
            range: m,
            _tree_depth: tree_depth,
        }
    }

    /// Forward evaluation: P(x) then S(P(x))
    pub fn forward(&self, x: u64) -> u64 {
        if x >= self.domain {
            return 0;
        }
        // Apply PRP first, then PMNS
        let permuted = self.prp.forward(x);
        self.trace_ball(permuted, self.domain, self.range)
    }

    /// Compute all input values `x` in the domain that map to the given output `y`.
    ///
    /// If `y` is outside the iPRF's output range, an empty vector is returned. The returned
    /// vector contains every `x` in `[0, self.domain)` such that `self.forward(x) == y` (order not specified).
    ///
    /// # Examples
    ///
    /// ```
    /// let key: [u8; 16] = [0u8; 16];
    /// let n = 100u64;
    /// let m = 10u64;
    /// let iprf = Iprf::new(key, n, m);
    /// let x = 42u64;
    /// let y = iprf.forward(x);
    /// let preimages = iprf.inverse(y);
    /// assert!(preimages.contains(&x));
    /// ```
    pub fn inverse(&self, y: u64) -> Vec<u64> {
        if y >= self.range {
            return vec![];
        }
        // First find all PMNS preimages, then apply inverse PRP to each
        let pmns_preimages = self.trace_ball_inverse(y, self.domain, self.range);
        pmns_preimages
            .into_iter()
            .map(|z| self.prp.inverse(z))
            .collect()
    }

    /// Deterministic binomial sampling matching Coq formalization.
    ///
    /// Given count balls and probability p = num/denom, determine how many go left.
    /// Uses PRF output as dither for deterministic sampling.
    ///
    /// This matches the Coq definition:
    ///   binomial_sample(count, num, denom, prf_output) =
    ///     (count * num + (prf_output mod (denom + 1))) / denom
    fn binomial_sample(count: u64, num: u64, denom: u64, prf_output: u64) -> u64 {
        if denom == 0 {
            return 0;
        }
        let scaled = prf_output % (denom + 1);
        (count * num + scaled) / denom
    }

    /// Determines which PMNS bin a ball falls into for a given ball index.
    ///
    /// Given a total of `n` balls partitioned into `m` bins, performs the PMNS forward
    /// trace for ball with index `x_prime` (0-based) and returns the 0-based bin index
    /// that the ball is assigned to. If `m == 1`, returns `0`.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// // `iprf` is an initialized instance that provides `trace_ball`.
    /// let bin = iprf.trace_ball(3, 10, 4);
    /// assert!(bin < 4);
    /// ```
    fn trace_ball(&self, x_prime: u64, n: u64, m: u64) -> u64 {
        if m == 1 {
            return 0;
        }

        let mut low = 0u64;
        let mut high = m - 1;
        let mut ball_count = n;
        let mut ball_index = x_prime;

        while low < high {
            let mid = (low + high) / 2;
            let left_bins = mid - low + 1;
            let total_bins = high - low + 1;

            let node_id = encode_node(low, high, n);
            let prf_output = self.prf_eval(node_id);

            let left_count = Self::binomial_sample(ball_count, left_bins, total_bins, prf_output);

            if ball_index < left_count {
                high = mid;
                ball_count = left_count;
            } else {
                low = mid + 1;
                ball_index -= left_count;
                ball_count -= left_count;
            }
        }
        low
    }

    /// Returns the contiguous range of ball indices that fall into PMNS bin `y`.
    ///
    /// For `m == 1` this is all balls `[0..n)`. Otherwise the method walks the PMNS
    /// binary partitioning tree deterministically (using `binomial_sample`) to
    /// compute the starting index and count of balls assigned to bin `y`, and
    /// returns the range `[start, start + count)` as a `Vec<u64>`.
    ///
    /// # Parameters
    ///
    /// - `y`: target bin index in `[0, m)`.
    /// - `n`: total number of balls (domain size).
    /// - `m`: total number of bins (range size).
    ///
    /// # Returns
    ///
    /// A `Vec<u64>` containing the ball indices that map to bin `y` (the closed-open
    /// range `start..start+count`).
    ///
    /// # Examples
    ///
    /// ```no_run
    /// // Assuming `iprf` is an initialized Iprf instance:
    /// // let indices = iprf.trace_ball_inverse(3, 100, 10);
    /// // `indices` now contains the contiguous ball indices assigned to bin 3.
    /// ```
    fn trace_ball_inverse(&self, y: u64, n: u64, m: u64) -> Vec<u64> {
        if m == 1 {
            return (0..n).collect();
        }

        let mut low = 0u64;
        let mut high = m - 1;
        let mut ball_count = n;
        let mut ball_start = 0u64;

        while low < high {
            let mid = (low + high) / 2;
            let left_bins = mid - low + 1;
            let total_bins = high - low + 1;

            let node_id = encode_node(low, high, n);
            let prf_output = self.prf_eval(node_id);

            let left_count = Self::binomial_sample(ball_count, left_bins, total_bins, prf_output);

            if y <= mid {
                high = mid;
                ball_count = left_count;
            } else {
                low = mid + 1;
                ball_start += left_count;
                ball_count -= left_count;
            }
        }

        (ball_start..ball_start + ball_count).collect()
    }

    /// Produces a 64-bit pseudorandom value by AES-encrypting a 16-byte block containing `x`.
    ///
    /// The input block places `x` in the last 8 bytes (big-endian), encrypts the block with the
    /// instance's AES-128 cipher, and returns the first 8 bytes of the ciphertext interpreted as a
    /// big-endian `u64`.
    ///
    /// # Examples
    ///
    /// ```rust,no_run
    /// // `iprf` is an instance providing `prf_eval`.
    /// let iprf = /* Iprf instance */ unimplemented!();
    /// let out: u64 = iprf.prf_eval(42);
    /// ```
    fn prf_eval(&self, x: u64) -> u64 {
        let mut input = [0u8; 16];
        input[8..16].copy_from_slice(&x.to_be_bytes());

        let mut block = GenericArray::from(input);
        self.cipher.encrypt_block(&mut block);

        u64::from_be_bytes(block[0..8].try_into().unwrap())
    }
}

fn encode_node(low: u64, high: u64, n: u64) -> u64 {
    let mut hasher = Sha256::new();
    hasher.update(&low.to_be_bytes());
    hasher.update(&high.to_be_bytes());
    hasher.update(&n.to_be_bytes());
    let result = hasher.finalize();
    u64::from_be_bytes(result[0..8].try_into().unwrap())
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    #[test]
    fn test_swap_or_not_inverse() {
        let key = [0u8; 16];
        let domain = 1000u64;
        let prp = SwapOrNot::new(key, domain);

        for x in 0..100 {
            let y = prp.forward(x);
            let x_recovered = prp.inverse(y);
            assert_eq!(x, x_recovered, "PRP inverse failed for x={}", x);
        }
    }

    #[test]
    fn test_swap_or_not_is_permutation() {
        let key = [1u8; 16];
        let domain = 100u64;
        let prp = SwapOrNot::new(key, domain);

        let mut outputs: Vec<u64> = (0..domain).map(|x| prp.forward(x)).collect();
        outputs.sort();
        outputs.dedup();
        assert_eq!(outputs.len(), domain as usize, "PRP is not a permutation");
    }

    #[test]
    fn test_iprf_inverse_contains_preimage() {
        let key = [2u8; 16];
        let domain = 1000u64;
        let range = 100u64;
        let iprf = Iprf::new(key, domain, range);

        for x in 0..50 {
            let y = iprf.forward(x);
            let preimages = iprf.inverse(y);
            assert!(
                preimages.contains(&x),
                "iPRF inverse for y={} does not contain original x={}",
                y,
                x
            );
        }
    }

    proptest! {
        #![proptest_config(ProptestConfig {
            cases: 64,
            .. ProptestConfig::default()
        })]

        #[test]
        fn swap_or_not_inverse_roundtrip(
            key in any::<[u8; 16]>(),
            domain in 1u64..10_000,
            x in any::<u64>(),
        ) {
            let x = x % domain;
            let prp = SwapOrNot::new(key, domain);

            let y = prp.forward(x);
            prop_assert!(y < domain);

            let x2 = prp.inverse(y);
            prop_assert_eq!(x, x2);
        }
    }

    proptest! {
        #![proptest_config(ProptestConfig {
            cases: 32,
            .. ProptestConfig::default()
        })]

        #[test]
        fn swap_or_not_is_permutation_for_small_domains(
            key in any::<[u8; 16]>(),
            domain in 1u64..65,
        ) {
            let prp = SwapOrNot::new(key, domain);

            let mut outputs: Vec<u64> = (0..domain).map(|x| prp.forward(x)).collect();
            outputs.sort_unstable();
            outputs.dedup();

            prop_assert_eq!(outputs.len() as u64, domain);
        }
    }

    proptest! {
        #![proptest_config(ProptestConfig {
            cases: 64,
            .. ProptestConfig::default()
        })]

        #[test]
        fn iprf_inverse_contains_preimage_and_is_consistent(
            key in any::<[u8; 16]>(),
            n in 1u64..1_000,
            m_raw in 1u64..1_000,
            x_raw in any::<u64>(),
        ) {
            let mut m = m_raw;
            if m > n {
                m = n;
            }

            let x = x_raw % n;

            let iprf = Iprf::new(key, n, m);

            let y = iprf.forward(x);
            prop_assert!(y < m);

            let preimages = iprf.inverse(y);
            prop_assert!(preimages.contains(&x));

            for &x2 in &preimages {
                prop_assert!(x2 < n);
                prop_assert_eq!(y, iprf.forward(x2));
            }
        }
    }

    proptest! {
        #![proptest_config(ProptestConfig {
            cases: 32,
            .. ProptestConfig::default()
        })]

        #[test]
        fn iprf_inverse_partitions_domain(
            key in any::<[u8; 16]>(),
            n_raw in 1u64..64,
            m_raw in 1u64..64,
        ) {
            let n = n_raw;
            let mut m = m_raw;
            if m > n {
                m = n;
            }

            let iprf = Iprf::new(key, n, m);
            let mut seen = vec![false; n as usize];

            for y in 0..m {
                for x in iprf.inverse(y) {
                    prop_assert!(x < n);
                    prop_assert!(
                        !seen[x as usize],
                        "element {} appears in multiple inverse bins", x
                    );
                    seen[x as usize] = true;
                }
            }

            prop_assert!(seen.iter().all(|&b| b));
        }
    }
}