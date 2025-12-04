//! Invertible Pseudorandom Function (iPRF) for Plinko PIR
//!
//! Implementation based on the Plinko paper (2024-318):
//! - iPRF is built from Swap-or-Not PRP + PMNS (Pseudorandom Multinomial Sampler)
//! - Forward: iF.F(k, x) = S(k_pmns, P(k_prp, x))
//! - Inverse: iF.F^{-1}(k, y) = {P^{-1}(k_prp, z) : z ∈ S^{-1}(k_pmns, y)}
//!
//! The Swap-or-Not PRP is based on Morris-Rogaway (eprint 2013/560).

use aes::cipher::{BlockEncrypt, KeyInit, generic_array::GenericArray};
use aes::Aes128;
use sha2::{Sha256, Digest};

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
    pub fn new(key: PrfKey128, domain: u64) -> Self {
        let cipher = Aes128::new(&GenericArray::from(key));
        // ~6 * log2(N) rounds for full security
        let num_rounds = ((domain as f64).log2().ceil() as usize) * 6 + 6;
        
        Self {
            cipher,
            domain,
            num_rounds,
        }
    }

    /// Derive round key K_i using AES
    fn derive_round_key(&self, round: usize) -> u64 {
        let mut input = [0u8; 16];
        input[0..8].copy_from_slice(&(round as u64).to_be_bytes());
        input[8..16].copy_from_slice(&self.domain.to_be_bytes());
        
        let mut block = GenericArray::from(input);
        self.cipher.encrypt_block(&mut block);
        
        u64::from_be_bytes(block[0..8].try_into().unwrap()) % self.domain
    }

    /// PRF for swap decision - returns a single bit
    fn prf_bit(&self, round: usize, canonical: u64) -> bool {
        let mut input = [0u8; 16];
        input[0..8].copy_from_slice(&(round as u64 | 0x8000000000000000).to_be_bytes());
        input[8..16].copy_from_slice(&canonical.to_be_bytes());
        
        let mut block = GenericArray::from(input);
        self.cipher.encrypt_block(&mut block);
        
        (block[0] & 1) == 1
    }

    /// Single round of Swap-or-Not (involutory - self-inverse)
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

const INV_TWO_TO_53: f64 = 1.0 / (1u64 << 53) as f64;

impl Iprf {
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

    /// Inverse evaluation: returns all x such that forward(x) = y
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

    /// PMNS forward: trace which bin ball x lands in
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

            let p = left_bins as f64 / total_bins as f64;
            
            let node_id = encode_node(low, high, n);
            let prf_output = self.prf_eval(node_id);
            
            // Map to (0, 1)
            let uniform = ((prf_output >> 11) as f64 + 0.5) * INV_TWO_TO_53;
            
            let left_count = self.binomial_inverse_cdf(ball_count, p, uniform);

            if ball_index < left_count {
                // Ball goes left
                high = mid;
                ball_count = left_count;
            } else {
                // Ball goes right
                low = mid + 1;
                ball_index -= left_count;
                ball_count -= left_count;
            }
        }
        low
    }

    /// PMNS inverse: find all balls in bin y
    /// Returns range [start, start + count) as a Vec
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

            let p = left_bins as f64 / total_bins as f64;
            
            let node_id = encode_node(low, high, n);
            let prf_output = self.prf_eval(node_id);
            
            let uniform = ((prf_output >> 11) as f64 + 0.5) * INV_TWO_TO_53;
            let left_count = self.binomial_inverse_cdf(ball_count, p, uniform);

            if y <= mid {
                // Target bin is in left subtree
                high = mid;
                ball_count = left_count;
            } else {
                // Target bin is in right subtree
                low = mid + 1;
                ball_start += left_count;
                ball_count -= left_count;
            }
        }
        
        (ball_start..ball_start + ball_count).collect()
    }

    fn binomial_inverse_cdf(&self, n: u64, p: f64, u: f64) -> u64 {
        if u <= 0.0 { return 0; }
        if u >= 1.0 { return n; }
        if p == 0.0 { return 0; }
        if p == 1.0 { return n; }
        if n == 0 { return 0; }

        if n > 100 {
            return self.normal_approx_binomial(n, p, u);
        }

        let mut cum_prob = 0.0;
        let q = 1.0 - p;
        let mut prob = q.powf(n as f64);
        cum_prob += prob;

        if u <= cum_prob {
            return 0;
        }

        for k in 0..n {
            prob = prob * (n - k) as f64 / (k + 1) as f64 * p / q;
            cum_prob += prob;
            if u <= cum_prob {
                return k + 1;
            }
        }
        n
    }

    fn normal_approx_binomial(&self, n: u64, p: f64, u: f64) -> u64 {
        let mean = n as f64 * p;
        let variance = n as f64 * p * (1.0 - p);
        let stddev = variance.sqrt();

        let u_clamped = u.clamp(0.001, 0.999);
        let z = inv_normal_cdf(u_clamped);
        let result = mean + z * stddev;

        if result < 0.0 { return 0; }
        if result > n as f64 { return n; }
        
        result.round() as u64
    }

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

fn inv_normal_cdf(p: f64) -> f64 {
    if p <= 0.0 || p >= 1.0 {
        if p <= 0.0 { return -10.0; }
        if p >= 1.0 { return 10.0; }
    }

    const A0: f64 = 2.50662823884;
    const A1: f64 = -18.61500062529;
    const A2: f64 = 41.39119773534;
    const A3: f64 = -25.44106049637;
    const B0: f64 = -8.47351093090;
    const B1: f64 = 23.08336743743;
    const B2: f64 = -21.06224101826;
    const B3: f64 = 3.13082909833;

    let y = p - 0.5;
    if y.abs() < 0.42 {
        let r = y * y;
        return y * (((A3 * r + A2) * r + A1) * r + A0) / ((((B3 * r + B2) * r + B1) * r + B0) * r + 1.0);
    }

    if y > 0.0 { 2.0 } else { -2.0 }
}

#[cfg(test)]
mod tests {
    use super::*;

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
                y, x
            );
        }
    }
}
