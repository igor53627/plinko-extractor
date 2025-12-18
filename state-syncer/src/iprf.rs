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
/// Inner shuffle used by SwapOrNotSr. Provides security for q < (1-epsilon)*N queries.
/// For full-domain security (all N queries), use SwapOrNotSr which wraps this with
/// the Sometimes-Recurse transformation.
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

/// Default security parameter (bits) for SR PRP
pub const DEFAULT_SECURITY_BITS: u32 = 128;

/// Per-stage SN round count from Morris-Rogaway Eq. (2) with Strategy 1 (split error equally).
///
/// For SR shuffle with canonical split, we need each SN stage to achieve error ε/p
/// where p = number of nontrivial stages ≈ lg(N₀).
///
/// Per Eq. (2): t_N ≥ 7.23 lg N - 4.82 lg(ε/p)
///            = 7.23 lg N - 4.82 lg ε + 4.82 lg p
///            = 7.23 lg N + 4.82 λ + 4.82 lg p   (for ε = 2^(-λ))
///
/// Parameters:
/// - `n`: Current domain size at this SR level
/// - `num_stages`: Total number of nontrivial stages p = |G'(N₀)|
/// - `lambda`: Security parameter in bits (ε = 2^(-λ))
fn sr_t_rounds_with_params(n: u64, num_stages: usize, lambda: u32) -> usize {
    if n <= 2 {
        return if n == 2 { 1 } else { 0 };
    }

    let log_n = (n as f64).log2();
    let log_p = if num_stages > 0 {
        (num_stages as f64).log2()
    } else {
        0.0
    };

    let rounds = 7.23 * log_n + 4.82 * (lambda as f64) + 4.82 * log_p;
    rounds.ceil() as usize
}

/// Compute the number of nontrivial SR stages for domain N₀.
///
/// Nontrivial stages are those with N ≥ 3 (we exclude N=1 and N=2).
/// For canonical split p_N = floor(N/2), we have:
/// - G(N₀) = {N₀, floor(N₀/2), floor(N₀/4), ...}
/// - G'(N₀) = G(N₀) \ {1, 2}
fn sr_num_stages(n0: u64) -> usize {
    if n0 <= 2 {
        return 0;
    }
    let mut count = 0;
    let mut n = n0;
    while n >= 3 {
        count += 1;
        n /= 2;
    }
    count
}

/// Conservative round count per Morris-Rogaway Section 5, Strategy 1.
///
/// Uses DEFAULT_SECURITY_BITS (128-bit security) and computes per-stage
/// round count based on equal error budget distribution.
#[allow(dead_code)]
fn sr_t_rounds(n: u64, n0: u64) -> usize {
    sr_t_rounds_with_security(n, n0, DEFAULT_SECURITY_BITS)
}

/// Round count with explicit security parameter.
///
/// For λ-bit security (distinguishing advantage ε = 2^(-λ)):
/// - Total error budget ε is split equally among p = |G'(N₀)| stages
/// - Each stage gets ε/p error budget
/// - Per Eq. (2), t_N = ceil(7.23 lg N + 4.82 lg(p/ε))
///                   = ceil(7.23 lg N + 4.82 lg p + 4.82 λ)
fn sr_t_rounds_with_security(n: u64, n0: u64, lambda: u32) -> usize {
    let num_stages = sr_num_stages(n0);
    sr_t_rounds_with_params(n, num_stages, lambda)
}

/// Precomputed round keys for one SR level
struct SrLevelKeys {
    n: u64,
    round_keys: Vec<u64>,
}

/// Sometimes-Recurse PRP wrapper (Morris-Rogaway Fig. 1)
///
/// Provides full-domain security: secure even when adversary queries all N elements.
/// Uses SwapOrNot as inner shuffle with recursive halving.
///
/// Round counts are computed per Morris-Rogaway Section 5 "Strategy 1" (equal error split)
/// with 128-bit security by default.
///
/// Optimization: All round keys are precomputed at construction time to eliminate
/// half of the AES operations during forward/inverse evaluation.
pub struct SwapOrNotSr {
    cipher: Aes128,
    domain: u64,
    max_levels: usize,
    #[allow(dead_code)]
    security_bits: u32,
    /// Precomputed round keys for each SR level: level_keys[level] contains
    /// all K_i values for that level's domain size
    level_keys: Vec<SrLevelKeys>,
}

impl SwapOrNotSr {
    pub fn new(key: PrfKey128, domain: u64) -> Self {
        Self::with_security(key, domain, DEFAULT_SECURITY_BITS)
    }

    pub fn with_security(key: PrfKey128, domain: u64, security_bits: u32) -> Self {
        assert!(domain > 0, "SwapOrNotSr domain must be positive");
        let cipher = Aes128::new(&GenericArray::from(key));
        let max_levels = if domain <= 1 {
            0
        } else {
            (domain as f64).log2().ceil() as usize
        };

        // Precompute all round keys for all levels
        let level_keys = Self::precompute_all_keys(&cipher, domain, max_levels, security_bits);

        Self {
            cipher,
            domain,
            max_levels,
            security_bits,
            level_keys,
        }
    }

    /// Precompute round keys for all SR levels at construction time
    fn precompute_all_keys(
        cipher: &Aes128,
        domain: u64,
        max_levels: usize,
        security_bits: u32,
    ) -> Vec<SrLevelKeys> {
        let mut keys = Vec::with_capacity(max_levels);
        let mut n = domain;

        for level in 0..max_levels {
            if n <= 1 {
                break;
            }
            let t = sr_t_rounds_with_security(n, domain, security_bits);
            let round_keys: Vec<u64> = (0..t)
                .map(|round| Self::compute_round_key(cipher, level, round, n))
                .collect();

            keys.push(SrLevelKeys { n, round_keys });
            n /= 2;
        }
        keys
    }

    /// Compute a single round key (used during precomputation)
    fn compute_round_key(cipher: &Aes128, level: usize, round: usize, n: u64) -> u64 {
        let mut input = [0u8; 16];
        let combined = ((level as u64) << 32) | (round as u64);
        input[0..8].copy_from_slice(&combined.to_be_bytes());
        input[8..16].copy_from_slice(&n.to_be_bytes());

        let mut block = GenericArray::from(input);
        cipher.encrypt_block(&mut block);

        u64::from_be_bytes(block[0..8].try_into().unwrap()) % n
    }

    fn prf_bit(&self, level: usize, round: usize, canonical: u64, _n: u64) -> bool {
        let mut input = [0u8; 16];
        let combined = ((level as u64) << 32) | (round as u64) | 0x80000000;
        input[0..8].copy_from_slice(&combined.to_be_bytes());
        input[8..16].copy_from_slice(&canonical.to_be_bytes());

        let mut block = GenericArray::from(input);
        self.cipher.encrypt_block(&mut block);

        (block[0] & 1) == 1
    }

    /// Apply one round using precomputed round key
    fn round_with_key(&self, level: usize, round_num: usize, n: u64, x: u64) -> u64 {
        let k_i = self.level_keys[level].round_keys[round_num];
        let partner = (k_i + n - (x % n)) % n;
        let canonical = x.max(partner);

        if self.prf_bit(level, round_num, canonical, n) {
            partner
        } else {
            x
        }
    }

    fn apply_rounds_forward(&self, level: usize, n: u64, x: u64) -> u64 {
        let num_rounds = self.level_keys[level].round_keys.len();
        let mut val = x;
        for r in 0..num_rounds {
            val = self.round_with_key(level, r, n, val);
        }
        val
    }

    fn apply_rounds_inverse(&self, level: usize, n: u64, y: u64) -> u64 {
        let num_rounds = self.level_keys[level].round_keys.len();
        let mut val = y;
        for r in (0..num_rounds).rev() {
            val = self.round_with_key(level, r, n, val);
        }
        val
    }

    pub fn forward(&self, x: u64) -> u64 {
        assert!(x < self.domain, "x must be < domain");
        let mut val = x;

        for level in 0..self.level_keys.len() {
            let n = self.level_keys[level].n;
            val = self.apply_rounds_forward(level, n, val);
            let half = n / 2;
            if val >= half {
                return val;
            }
        }
        val
    }

    pub fn inverse(&self, y: u64) -> u64 {
        assert!(y < self.domain, "y must be < domain");

        // Find the deepest level we need to reach
        let mut depth = 0;
        let mut n = self.domain;
        for level in 0..self.level_keys.len() {
            if n <= 1 {
                break;
            }
            depth = level + 1;
            let half = n / 2;
            if y >= half {
                break;
            }
            n = half;
        }

        let mut val = y;
        for level in (0..depth).rev() {
            let n = self.level_keys[level].n;
            val = self.apply_rounds_inverse(level, n, val);
        }
        val
    }
}

/// Constant-time Sometimes-Recurse PRP for TEE execution
///
/// Full-domain security variant using constant-time operations to prevent
/// timing side-channels. Uses branchless logic throughout.
///
/// Round counts are computed per Morris-Rogaway Section 5 "Strategy 1" (equal error split)
/// with 128-bit security by default.
///
/// Optimization: All round keys are precomputed at construction time to eliminate
/// half of the AES operations during forward/inverse evaluation.
pub struct SwapOrNotSrTee {
    cipher: Aes128,
    domain: u64,
    max_levels: usize,
    #[allow(dead_code)]
    security_bits: u32,
    /// Precomputed round keys for each SR level
    level_keys: Vec<SrLevelKeys>,
}

impl SwapOrNotSrTee {
    pub fn new(key: PrfKey128, domain: u64) -> Self {
        Self::with_security(key, domain, DEFAULT_SECURITY_BITS)
    }

    pub fn with_security(key: PrfKey128, domain: u64, security_bits: u32) -> Self {
        assert!(domain > 0, "SwapOrNotSrTee domain must be positive");
        let cipher = Aes128::new(&GenericArray::from(key));
        let max_levels = if domain <= 1 {
            0
        } else {
            (domain as f64).log2().ceil() as usize
        };

        // Precompute all round keys for all levels (reuse SwapOrNotSr helper)
        let level_keys =
            SwapOrNotSr::precompute_all_keys(&cipher, domain, max_levels, security_bits);

        Self {
            cipher,
            domain,
            max_levels,
            security_bits,
            level_keys,
        }
    }

    fn prf_bit_ct(&self, level: usize, round: usize, canonical: u64) -> u64 {
        let mut input = [0u8; 16];
        let combined = ((level as u64) << 32) | (round as u64) | 0x80000000;
        input[0..8].copy_from_slice(&combined.to_be_bytes());
        input[8..16].copy_from_slice(&canonical.to_be_bytes());

        let mut block = GenericArray::from(input);
        self.cipher.encrypt_block(&mut block);

        (block[0] & 1) as u64
    }

    /// Apply one round using precomputed round key (constant-time)
    fn round_ct_with_key(&self, level: usize, round_num: usize, n: u64, x: u64) -> u64 {
        use crate::constant_time::{ct_lt_u64, ct_select_u64};

        let k_i = self.level_keys[level].round_keys[round_num];
        let partner = (k_i + n - (x % n)) % n;

        let x_lt_partner = ct_lt_u64(x, partner);
        let canonical = ct_select_u64(x_lt_partner, partner, x);

        let swap = self.prf_bit_ct(level, round_num, canonical);
        ct_select_u64(swap, partner, x)
    }

    fn apply_rounds_forward(&self, level: usize, n: u64, x: u64) -> u64 {
        let num_rounds = self.level_keys[level].round_keys.len();
        let mut val = x;
        for r in 0..num_rounds {
            val = self.round_ct_with_key(level, r, n, val);
        }
        val
    }

    fn apply_rounds_inverse(&self, level: usize, n: u64, y: u64) -> u64 {
        let num_rounds = self.level_keys[level].round_keys.len();
        let mut val = y;
        for r in (0..num_rounds).rev() {
            val = self.round_ct_with_key(level, r, n, val);
        }
        val
    }

    pub fn forward(&self, x: u64) -> u64 {
        use crate::constant_time::{ct_ge_u64, ct_select_u64};

        debug_assert!(x < self.domain, "x must be < domain");
        let mut val = x % self.domain;
        let mut result = 0u64;
        let mut done = 0u64;

        for level in 0..self.level_keys.len() {
            let n = self.level_keys[level].n;
            let should_skip = done;

            val = ct_select_u64(should_skip, val, self.apply_rounds_forward(level, n, val));

            let half = n / 2;
            let exited = ct_ge_u64(val, half);
            result = ct_select_u64(exited & (1 - done), val, result);
            done |= exited;
        }

        ct_select_u64(done, result, val)
    }

    pub fn inverse(&self, y: u64) -> u64 {
        use crate::constant_time::{ct_eq_u64, ct_ge_u64, ct_lt_u64, ct_select_u64};

        debug_assert!(y < self.domain, "y must be < domain");
        let y = y % self.domain;

        let mut sizes = [0u64; 64];
        let mut stopped: u64 = 0;

        for level in 0..self.level_keys.len() {
            let n = self.level_keys[level].n;
            let should_record = ct_eq_u64(stopped, 0);
            sizes[level] = ct_select_u64(should_record, n, 0);

            let half = n / 2;
            let y_in_right = ct_ge_u64(y, half);
            let stopping_now = should_record & y_in_right;
            stopped = ct_select_u64(stopping_now, 1, stopped);
        }

        let mut val = y;
        for level in (0..self.level_keys.len()).rev() {
            let n_lvl = sizes[level];
            let skip = ct_lt_u64(n_lvl, 2);
            // Use level's actual n to avoid division by zero; skip flag handles correctness
            let safe_n = self.level_keys[level].n;
            val = ct_select_u64(skip, val, self.apply_rounds_inverse(level, safe_n, val));
        }
        val
    }
}

/// Constant-time SwapOrNot PRP for TEE execution
///
/// Functionally equivalent to SwapOrNot but uses branchless operations
/// to prevent timing side-channels.
pub struct SwapOrNotTee {
    cipher: Aes128,
    domain: u64,
    num_rounds: usize,
}

impl SwapOrNotTee {
    pub fn new(key: PrfKey128, domain: u64) -> Self {
        assert!(domain > 0, "SwapOrNot domain must be positive");
        let cipher = Aes128::new(&GenericArray::from(key));
        let num_rounds = ((domain as f64).log2().ceil() as usize) * 6 + 6;
        Self {
            cipher,
            domain,
            num_rounds,
        }
    }

    fn derive_round_key(&self, round: usize) -> u64 {
        let mut input = [0u8; 16];
        input[0..8].copy_from_slice(&(round as u64).to_be_bytes());
        input[8..16].copy_from_slice(&self.domain.to_be_bytes());
        let mut block = GenericArray::from(input);
        self.cipher.encrypt_block(&mut block);
        u64::from_be_bytes(block[0..8].try_into().unwrap()) % self.domain
    }

    /// Returns 1 if should swap, 0 otherwise (constant-time)
    fn prf_bit_ct(&self, round: usize, canonical: u64) -> u64 {
        let mut input = [0u8; 16];
        input[0..8].copy_from_slice(&(round as u64 | 0x8000000000000000).to_be_bytes());
        input[8..16].copy_from_slice(&canonical.to_be_bytes());
        let mut block = GenericArray::from(input);
        self.cipher.encrypt_block(&mut block);
        (block[0] & 1) as u64
    }

    /// Constant-time round - no secret-dependent branches
    fn round_ct(&self, round_num: usize, x: u64) -> u64 {
        use crate::constant_time::{ct_lt_u64, ct_select_u64};

        let k_i = self.derive_round_key(round_num);
        let partner = (k_i + self.domain - (x % self.domain)) % self.domain;

        // Constant-time max: canonical = max(x, partner)
        let x_lt_partner = ct_lt_u64(x, partner);
        let canonical = ct_select_u64(x_lt_partner, partner, x);

        // Constant-time swap decision
        let swap = self.prf_bit_ct(round_num, canonical);
        ct_select_u64(swap, partner, x)
    }

    pub fn forward(&self, x: u64) -> u64 {
        let mut val = x;
        for round in 0..self.num_rounds {
            val = self.round_ct(round, val);
        }
        val
    }

    pub fn inverse(&self, y: u64) -> u64 {
        let mut val = y;
        for round in (0..self.num_rounds).rev() {
            val = self.round_ct(round, val);
        }
        val
    }
}

/// Maximum preimages for fixed-size array return
pub const MAX_PREIMAGES: usize = 512;

/// Constant-time iPRF for TEE execution
///
/// Functionally equivalent to Iprf but uses branchless operations and
/// fixed iteration counts to prevent timing side-channels.
/// Uses SwapOrNotSrTee for full-domain PRP security.
pub struct IprfTee {
    #[allow(dead_code)]
    key: PrfKey128,
    cipher: Aes128,
    prp: SwapOrNotSrTee,
    domain: u64,
    range: u64,
    tree_depth: usize,
}

impl IprfTee {
    /// Creates a new TEE-safe iPRF instance.
    ///
    /// # Panics
    /// Panics if `n > CT_BINOMIAL_MAX_COUNT` (65536). TEE constant-time binomial
    /// sampling requires O(n) iterations; larger domains would either leak timing
    /// or fall back to a non-Binomial approximation.
    pub fn new(key: PrfKey128, n: u64, m: u64) -> Self {
        assert!(
            n <= crate::binomial::CT_BINOMIAL_MAX_COUNT,
            "IprfTee requires n <= {} for constant-time binomial sampling, got n={}",
            crate::binomial::CT_BINOMIAL_MAX_COUNT,
            n
        );

        let tree_depth = (m as f64).log2().ceil() as usize;
        let cipher = Aes128::new(&GenericArray::from(key));

        let mut prp_key = [0u8; 16];
        let mut hasher = Sha256::new();
        hasher.update(&key);
        hasher.update(b"prp");
        let hash = hasher.finalize();
        prp_key.copy_from_slice(&hash[0..16]);

        let prp = SwapOrNotSrTee::new(prp_key, n);

        Self {
            key,
            cipher,
            prp,
            domain: n,
            range: m,
            tree_depth,
        }
    }

    /// Forward evaluation.
    ///
    /// # Security Note
    /// This method is NOT constant-time: the internal `trace_ball` loop branches
    /// on `ball_index < left_count`. For PIR query privacy, only `inverse_ct` needs
    /// to be constant-time (the server computes inverse, not forward).
    ///
    /// # Precondition
    /// `x` must be in range `[0, domain)`. This is a precondition, not runtime-checked
    /// in release builds, to avoid timing side-channels.
    pub fn forward(&self, x: u64) -> u64 {
        debug_assert!(x < self.domain, "IprfTee::forward: x must be < domain");
        let permuted = self.prp.forward(x);
        self.trace_ball(permuted, self.domain, self.range)
    }

    /// Constant-time inverse returning fixed-size array with validity mask.
    ///
    /// # Precondition
    /// `y` must be in range `[0, range)`. This is a precondition, not runtime-checked
    /// in release builds, to avoid timing side-channels.
    pub fn inverse_ct(&self, y: u64) -> ([u64; MAX_PREIMAGES], usize) {
        use crate::constant_time::{ct_lt_u64, ct_select_u64};

        debug_assert!(y < self.range, "IprfTee::inverse_ct: y must be < range");

        let (ball_start, ball_count) = self.trace_ball_inverse_ct(y);

        // Constant-time min(ball_count, MAX_PREIMAGES) to avoid data-dependent branch
        let max_preimages = MAX_PREIMAGES as u64;
        let exceeds_max = ct_lt_u64(max_preimages, ball_count);
        let count_u64 = ct_select_u64(exceeds_max, max_preimages, ball_count);
        let count = count_u64 as usize;
        let mut result = [0u64; MAX_PREIMAGES];

        for i in 0..MAX_PREIMAGES {
            let in_range = ct_lt_u64(i as u64, count as u64);
            let z = ball_start + i as u64;
            // Only call inverse for valid z values; use 0 for out-of-range
            let z_valid = ct_lt_u64(z, self.domain);
            let z_safe = ct_select_u64(z_valid, z, 0);
            let x = self.prp.inverse(z_safe);
            result[i] = ct_select_u64(in_range & z_valid, x, 0);
        }

        (result, count)
    }

    /// Constant-time trace_ball_inverse with fixed iteration count
    fn trace_ball_inverse_ct(&self, y: u64) -> (u64, u64) {
        use crate::constant_time::{ct_le_u64, ct_lt_u64, ct_select_u64};

        if self.range == 1 {
            return (0, self.domain);
        }

        let mut low = 0u64;
        let mut high = self.range - 1;
        let mut ball_count = self.domain;
        let mut ball_start = 0u64;

        for _level in 0..self.tree_depth {
            let should_continue = ct_lt_u64(low, high);

            let mid = (low + high) / 2;
            let left_bins = mid - low + 1;
            let total_bins = high - low + 1;

            let node_id = encode_node(low, high, self.domain);
            let prf_output = self.prf_eval(node_id);
            // Use TEE-safe constant-time binomial sampler (matches BinomialSpec.v)
            let left_count =
                crate::binomial::binomial_sample_tee(ball_count, left_bins, total_bins, prf_output);

            let go_left = ct_le_u64(y, mid);

            let new_low_left = low;
            let new_high_left = mid;
            let new_count_left = left_count;
            let new_start_left = ball_start;

            let new_low_right = mid + 1;
            let new_high_right = high;
            let new_count_right = ball_count.wrapping_sub(left_count);
            let new_start_right = ball_start + left_count;

            let new_low = ct_select_u64(go_left, new_low_left, new_low_right);
            let new_high = ct_select_u64(go_left, new_high_left, new_high_right);
            let new_count = ct_select_u64(go_left, new_count_left, new_count_right);
            let new_start = ct_select_u64(go_left, new_start_left, new_start_right);

            low = ct_select_u64(should_continue, new_low, low);
            high = ct_select_u64(should_continue, new_high, high);
            ball_count = ct_select_u64(should_continue, new_count, ball_count);
            ball_start = ct_select_u64(should_continue, new_start, ball_start);
        }

        (ball_start, ball_count)
    }

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
            // Use TEE-safe constant-time binomial sampler (matches BinomialSpec.v)
            let left_count =
                crate::binomial::binomial_sample_tee(ball_count, left_bins, total_bins, prf_output);

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

    fn prf_eval(&self, x: u64) -> u64 {
        let mut input = [0u8; 16];
        input[8..16].copy_from_slice(&x.to_be_bytes());
        let mut block = GenericArray::from(input);
        self.cipher.encrypt_block(&mut block);
        u64::from_be_bytes(block[0..8].try_into().unwrap())
    }

    /// Helper to get Vec<u64> like standard inverse (for testing)
    pub fn inverse(&self, y: u64) -> Vec<u64> {
        let (arr, count) = self.inverse_ct(y);
        arr[..count].to_vec()
    }
}

/// Invertible PRF built from Sometimes-Recurse PRP + PMNS
///
/// Uses SwapOrNotSr for full-domain PRP security (secure even when all N elements queried).
pub struct Iprf {
    #[allow(dead_code)]
    key: PrfKey128,
    cipher: Aes128,
    prp: SwapOrNotSr,
    domain: u64,
    range: u64,
    _tree_depth: usize,
}

impl Iprf {
    /// Creates a new iPRF instance for input domain `n` and output range `m`.
    ///
    /// The constructor derives an internal AES-128 cipher from `key`, computes the PMNS
    /// tree depth as ceil(log2(m)), and derives a separate 128-bit key (SHA-256(key || "prp"))
    /// to initialize the internal Sometimes-Recurse PRP over the input domain `n`.
    pub fn new(key: PrfKey128, n: u64, m: u64) -> Self {
        Self::with_security(key, n, m, DEFAULT_SECURITY_BITS)
    }

    /// Creates a new iPRF with explicit SR PRP security parameter.
    ///
    /// The `security_bits` parameter controls the round count in the Sometimes-Recurse PRP.
    /// Lower values (e.g., 64) significantly speed up computation but provide weaker PRP security.
    pub fn with_security(key: PrfKey128, n: u64, m: u64, security_bits: u32) -> Self {
        let tree_depth = (m as f64).log2().ceil() as usize;
        let cipher = Aes128::new(&GenericArray::from(key));

        // Derive a separate key for PRP from main key
        let mut prp_key = [0u8; 16];
        let mut hasher = Sha256::new();
        hasher.update(&key);
        hasher.update(b"prp");
        let hash = hasher.finalize();
        prp_key.copy_from_slice(&hash[0..16]);

        let prp = SwapOrNotSr::with_security(prp_key, n, security_bits);

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
    /// Note: Multiple preimages per output are possible since this is an iPRF, not a bijection.
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

    /// Determines which PMNS bin a ball falls into for a given ball index.
    ///
    /// Given a total of `n` balls partitioned into `m` bins, performs the PMNS forward
    /// trace for ball with index `x_prime` (0-based) and returns the 0-based bin index
    /// that the ball is assigned to. If `m == 1`, returns `0`.
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

            let left_count =
                crate::binomial::binomial_sample(ball_count, left_bins, total_bins, prf_output);

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

            let left_count =
                crate::binomial::binomial_sample(ball_count, left_bins, total_bins, prf_output);

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
    fn prf_eval(&self, x: u64) -> u64 {
        let mut input = [0u8; 16];
        input[8..16].copy_from_slice(&x.to_be_bytes());

        let mut block = GenericArray::from(input);
        self.cipher.encrypt_block(&mut block);

        u64::from_be_bytes(block[0..8].try_into().unwrap())
    }
}

/// Encodes a PMNS tree node as a unique 64-bit identifier for PRF evaluation.
///
/// Note: The third argument is the global domain `n`, not the dynamic `ball_count`.
/// This differs from the Rocq spec (IprfSpec.v) which uses `ball_count`, but both are
/// valid as long as forward and inverse use the same encoding. The Rocq spec's
/// `encode_node` is a parameter that can be instantiated to match this behavior.
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

    #[test]
    fn test_swap_or_not_tee_matches_standard() {
        let key = [3u8; 16];
        let domain = 1000u64;
        let prp = SwapOrNot::new(key, domain);
        let prp_tee = SwapOrNotTee::new(key, domain);

        for x in 0..100 {
            assert_eq!(
                prp.forward(x),
                prp_tee.forward(x),
                "forward mismatch at x={}",
                x
            );
            assert_eq!(
                prp.inverse(x),
                prp_tee.inverse(x),
                "inverse mismatch at x={}",
                x
            );
        }
    }

    #[test]
    #[ignore = "slow with 128-bit security; run with --ignored"]
    fn test_iprf_tee_matches_standard() {
        let key = [4u8; 16];
        let domain = 500u64;
        let range = 50u64;
        let iprf = Iprf::new(key, domain, range);
        let iprf_tee = IprfTee::new(key, domain, range);

        for x in 0..100 {
            let y = iprf.forward(x);
            let y_tee = iprf_tee.forward(x);
            assert_eq!(y, y_tee, "forward mismatch at x={}", x);
        }

        for y in 0..range {
            let preimages = iprf.inverse(y);
            let preimages_tee = iprf_tee.inverse(y);
            assert_eq!(preimages, preimages_tee, "inverse mismatch at y={}", y);
        }
    }

    #[test]
    #[ignore = "slow with 128-bit security; run with --ignored"]
    fn test_swap_or_not_sr_inverse() {
        let key = [5u8; 16];
        let domain = 100u64;
        let prp = SwapOrNotSr::new(key, domain);

        for x in 0..domain {
            let y = prp.forward(x);
            let x_recovered = prp.inverse(y);
            assert_eq!(x, x_recovered, "SR inverse failed for x={}", x);
        }
    }

    #[test]
    #[ignore = "slow with 128-bit security; run with --ignored"]
    fn test_swap_or_not_sr_is_permutation() {
        let key = [6u8; 16];
        let domain = 64u64;
        let prp = SwapOrNotSr::new(key, domain);

        let mut outputs: Vec<u64> = (0..domain).map(|x| prp.forward(x)).collect();
        outputs.sort();
        outputs.dedup();
        assert_eq!(
            outputs.len(),
            domain as usize,
            "SR PRP is not a permutation"
        );
    }

    #[test]
    #[ignore = "slow with 128-bit security; run with --ignored"]
    fn test_swap_or_not_sr_tee_matches_standard() {
        let key = [7u8; 16];
        let domain = 64u64;
        let prp = SwapOrNotSr::new(key, domain);
        let prp_tee = SwapOrNotSrTee::new(key, domain);

        for x in 0..domain {
            assert_eq!(
                prp.forward(x),
                prp_tee.forward(x),
                "SR TEE forward mismatch at x={}",
                x
            );
        }

        for y in 0..domain {
            assert_eq!(
                prp.inverse(y),
                prp_tee.inverse(y),
                "SR TEE inverse mismatch at y={}",
                y
            );
        }
    }

    #[test]
    #[ignore = "slow with 128-bit security; run with --ignored"]
    fn test_swap_or_not_sr_tee_inverse_roundtrip() {
        let key = [8u8; 16];
        let domain = 100u64;
        let prp_tee = SwapOrNotSrTee::new(key, domain);

        for x in 0..domain {
            let y = prp_tee.forward(x);
            let x_recovered = prp_tee.inverse(y);
            assert_eq!(
                x, x_recovered,
                "SR TEE inverse roundtrip failed for x={}",
                x
            );
        }
    }

    #[test]
    fn test_sr_num_stages() {
        assert_eq!(sr_num_stages(1), 0);
        assert_eq!(sr_num_stages(2), 0);
        assert_eq!(sr_num_stages(3), 1);
        assert_eq!(sr_num_stages(4), 1);
        assert_eq!(sr_num_stages(5), 1);
        assert_eq!(sr_num_stages(6), 2);
        assert_eq!(sr_num_stages(8), 2);
        assert_eq!(sr_num_stages(16), 3);
        assert_eq!(sr_num_stages(64), 5);
        assert_eq!(sr_num_stages(1000), 9);
        assert_eq!(sr_num_stages(1_000_000), 19);
    }

    #[test]
    fn test_sr_t_rounds_with_params_paper_example() {
        let n = 10u64.pow(16);
        let epsilon = 10.0_f64.powi(-10);
        let lambda = (-epsilon.log2()).ceil() as u32;

        let num_stages = sr_num_stages(n);
        let rounds_at_top = sr_t_rounds_with_params(n, num_stages, lambda);

        assert!(
            rounds_at_top >= 500,
            "Expected 500+ per-stage rounds for N=10^16, eps=10^-10 (got {})",
            rounds_at_top
        );
        assert!(
            rounds_at_top <= 700,
            "Per-stage rounds too high for N=10^16, eps=10^-10 (got {})",
            rounds_at_top
        );
    }

    #[test]
    fn test_sr_t_rounds_128bit_security() {
        let n0 = 1000u64;
        let lambda = 128u32;

        let rounds_at_n0 = sr_t_rounds_with_security(n0, n0, lambda);
        let rounds_at_half = sr_t_rounds_with_security(n0 / 2, n0, lambda);

        assert!(
            rounds_at_n0 > 600,
            "128-bit security needs significant rounds (got {} for N=1000)",
            rounds_at_n0
        );

        assert!(
            rounds_at_half < rounds_at_n0,
            "Smaller levels should have fewer rounds"
        );
    }

    #[test]
    fn test_sr_t_rounds_lower_security() {
        let n0 = 1000u64;
        let lambda_high = 128u32;
        let lambda_low = 64u32;

        let rounds_high = sr_t_rounds_with_security(n0, n0, lambda_high);
        let rounds_low = sr_t_rounds_with_security(n0, n0, lambda_low);

        assert!(
            rounds_high > rounds_low,
            "Higher security should need more rounds"
        );

        let expected_diff = 4.82 * ((lambda_high - lambda_low) as f64);
        let actual_diff = (rounds_high - rounds_low) as f64;
        assert!(
            (actual_diff - expected_diff).abs() < 2.0,
            "Round difference should be ~4.82 * delta_lambda"
        );
    }

    #[test]
    fn test_sr_with_custom_security() {
        let key = [9u8; 16];
        let domain = 64u64;

        let prp_32 = SwapOrNotSr::with_security(key, domain, 32);

        for x in 0..domain {
            let y = prp_32.forward(x);
            let x_recovered = prp_32.inverse(y);
            assert_eq!(x, x_recovered, "32-bit SR inverse failed at x={}", x);
        }
    }

    #[test]
    fn test_sr_tee_with_low_security() {
        let key = [10u8; 16];
        let domain = 32u64;

        let prp = SwapOrNotSr::with_security(key, domain, 32);
        let prp_tee = SwapOrNotSrTee::with_security(key, domain, 32);

        for x in 0..domain {
            assert_eq!(
                prp.forward(x),
                prp_tee.forward(x),
                "SR/TEE forward mismatch at x={}",
                x
            );
            let y = prp.forward(x);
            assert_eq!(
                prp.inverse(y),
                prp_tee.inverse(y),
                "SR/TEE inverse mismatch at y={}",
                y
            );
        }
    }

    #[test]
    fn test_sr_is_permutation_low_security() {
        let key = [11u8; 16];
        let domain = 64u64;
        let prp = SwapOrNotSr::with_security(key, domain, 32);

        let mut outputs: Vec<u64> = (0..domain).map(|x| prp.forward(x)).collect();
        outputs.sort();
        outputs.dedup();
        assert_eq!(
            outputs.len(),
            domain as usize,
            "SR PRP is not a permutation"
        );
    }
}
