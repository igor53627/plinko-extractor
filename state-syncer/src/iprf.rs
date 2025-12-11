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

/// Conservative round count per Morris-Rogaway bounds for full-domain security
fn sr_t_rounds(n: u64) -> usize {
    if n <= 1 {
        return 0;
    }
    let logn = (n as f64).log2().ceil();
    // Per MR: ~14.5 * log2(N) + constant for security against N queries
    (14.5 * logn).ceil() as usize + 16
}

/// Sometimes-Recurse PRP wrapper (Morris-Rogaway Fig. 1)
///
/// Provides full-domain security: secure even when adversary queries all N elements.
/// Uses SwapOrNot as inner shuffle with recursive halving.
pub struct SwapOrNotSr {
    cipher: Aes128,
    domain: u64,
    max_levels: usize,
}

impl SwapOrNotSr {
    pub fn new(key: PrfKey128, domain: u64) -> Self {
        assert!(domain > 0, "SwapOrNotSr domain must be positive");
        let cipher = Aes128::new(&GenericArray::from(key));
        let max_levels = if domain <= 1 {
            0
        } else {
            (domain as f64).log2().ceil() as usize
        };

        Self {
            cipher,
            domain,
            max_levels,
        }
    }

    fn derive_round_key(&self, level: usize, round: usize, n: u64) -> u64 {
        let mut input = [0u8; 16];
        let combined = ((level as u64) << 32) | (round as u64);
        input[0..8].copy_from_slice(&combined.to_be_bytes());
        input[8..16].copy_from_slice(&n.to_be_bytes());

        let mut block = GenericArray::from(input);
        self.cipher.encrypt_block(&mut block);

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

    fn round(&self, level: usize, round_num: usize, n: u64, x: u64) -> u64 {
        let k_i = self.derive_round_key(level, round_num, n);
        let partner = (k_i + n - (x % n)) % n;
        let canonical = x.max(partner);

        if self.prf_bit(level, round_num, canonical, n) {
            partner
        } else {
            x
        }
    }

    fn apply_rounds_forward(&self, level: usize, n: u64, x: u64) -> u64 {
        let t = sr_t_rounds(n);
        let mut val = x;
        for r in 0..t {
            val = self.round(level, r, n, val);
        }
        val
    }

    fn apply_rounds_inverse(&self, level: usize, n: u64, y: u64) -> u64 {
        let t = sr_t_rounds(n);
        let mut val = y;
        for r in (0..t).rev() {
            val = self.round(level, r, n, val);
        }
        val
    }

    pub fn forward(&self, x: u64) -> u64 {
        assert!(x < self.domain, "x must be < domain");
        let mut val = x;
        let mut n = self.domain;

        for level in 0..self.max_levels {
            if n <= 1 {
                break;
            }
            val = self.apply_rounds_forward(level, n, val);
            let half = n / 2;
            if val >= half {
                return val;
            }
            n = half;
        }
        val
    }

    pub fn inverse(&self, y: u64) -> u64 {
        assert!(y < self.domain, "y must be < domain");

        let mut sizes = Vec::with_capacity(self.max_levels);
        let mut n = self.domain;
        for _ in 0..self.max_levels {
            if n <= 1 {
                break;
            }
            sizes.push(n);
            let half = n / 2;
            if y >= half {
                break;
            }
            n = half;
        }

        let mut val = y;
        for (level, &n) in sizes.iter().enumerate().rev() {
            val = self.apply_rounds_inverse(level, n, val);
        }
        val
    }
}

/// Constant-time Sometimes-Recurse PRP for TEE execution
///
/// Full-domain security variant using constant-time operations to prevent
/// timing side-channels. Uses branchless logic throughout.
pub struct SwapOrNotSrTee {
    cipher: Aes128,
    domain: u64,
    max_levels: usize,
}

impl SwapOrNotSrTee {
    pub fn new(key: PrfKey128, domain: u64) -> Self {
        assert!(domain > 0, "SwapOrNotSrTee domain must be positive");
        let cipher = Aes128::new(&GenericArray::from(key));
        let max_levels = if domain <= 1 {
            0
        } else {
            (domain as f64).log2().ceil() as usize
        };

        Self {
            cipher,
            domain,
            max_levels,
        }
    }

    fn derive_round_key(&self, level: usize, round: usize, n: u64) -> u64 {
        let mut input = [0u8; 16];
        let combined = ((level as u64) << 32) | (round as u64);
        input[0..8].copy_from_slice(&combined.to_be_bytes());
        input[8..16].copy_from_slice(&n.to_be_bytes());

        let mut block = GenericArray::from(input);
        self.cipher.encrypt_block(&mut block);

        u64::from_be_bytes(block[0..8].try_into().unwrap()) % n
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

    fn round_ct(&self, level: usize, round_num: usize, n: u64, x: u64) -> u64 {
        use crate::constant_time::{ct_lt_u64, ct_select_u64};

        let k_i = self.derive_round_key(level, round_num, n);
        let partner = (k_i + n - (x % n)) % n;

        let x_lt_partner = ct_lt_u64(x, partner);
        let canonical = ct_select_u64(x_lt_partner, partner, x);

        let swap = self.prf_bit_ct(level, round_num, canonical);
        ct_select_u64(swap, partner, x)
    }

    fn apply_rounds_forward(&self, level: usize, n: u64, x: u64) -> u64 {
        let t = sr_t_rounds(n);
        let mut val = x;
        for r in 0..t {
            val = self.round_ct(level, r, n, val);
        }
        val
    }

    fn apply_rounds_inverse(&self, level: usize, n: u64, y: u64) -> u64 {
        let t = sr_t_rounds(n);
        let mut val = y;
        for r in (0..t).rev() {
            val = self.round_ct(level, r, n, val);
        }
        val
    }

    pub fn forward(&self, x: u64) -> u64 {
        use crate::constant_time::{ct_ge_u64, ct_select_u64};

        debug_assert!(x < self.domain, "x must be < domain");
        let mut val = x % self.domain;
        let mut n = self.domain;
        let mut result = 0u64;
        let mut done = 0u64;

        for level in 0..self.max_levels {
            let should_skip = ct_ge_u64(1, n) | done;

            val = ct_select_u64(
                should_skip,
                val,
                self.apply_rounds_forward(level, n, val),
            );

            let half = n / 2;
            let exited = ct_ge_u64(val, half);
            result = ct_select_u64(exited & (1 - done), val, result);
            done |= exited;

            n = ct_select_u64(should_skip, n, half);
        }

        ct_select_u64(done, result, val)
    }

    pub fn inverse(&self, y: u64) -> u64 {
        use crate::constant_time::{ct_eq_u64, ct_ge_u64, ct_gt_u64, ct_lt_u64, ct_select_u64};

        debug_assert!(y < self.domain, "y must be < domain");
        let y = y % self.domain;

        let mut sizes = [0u64; 64];
        let mut n = self.domain;
        let mut stopped: u64 = 0;

        for i in 0..self.max_levels {
            let should_record = ct_gt_u64(n, 1) & ct_eq_u64(stopped, 0);
            sizes[i] = ct_select_u64(should_record, n, 0);

            let half = n / 2;
            let y_in_right = ct_ge_u64(y, half);
            let stopping_now = should_record & y_in_right;
            stopped = ct_select_u64(stopping_now, 1, stopped);

            n = ct_select_u64(should_record & ct_eq_u64(stopped, 0), half, n);
        }

        let mut val = y;
        for level in (0..self.max_levels).rev() {
            let n_lvl = sizes[level];
            let skip = ct_lt_u64(n_lvl, 2);
            val = ct_select_u64(skip, val, self.apply_rounds_inverse(level, n_lvl, val));
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
    pub fn new(key: PrfKey128, n: u64, m: u64) -> Self {
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

    /// Forward evaluation - constant-time for valid inputs.
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

        let count = (ball_count as usize).min(MAX_PREIMAGES);
        let mut result = [0u64; MAX_PREIMAGES];

        for i in 0..MAX_PREIMAGES {
            let in_range = ct_lt_u64(i as u64, count as u64);
            let z = ball_start + i as u64;
            let x = self.prp.inverse(z);
            result[i] = ct_select_u64(in_range, x, 0);
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
            let left_count =
                crate::binomial::binomial_sample(ball_count, left_bins, total_bins, prf_output);

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
        let tree_depth = (m as f64).log2().ceil() as usize;
        let cipher = Aes128::new(&GenericArray::from(key));

        // Derive a separate key for PRP from main key
        let mut prp_key = [0u8; 16];
        let mut hasher = Sha256::new();
        hasher.update(&key);
        hasher.update(b"prp");
        let hash = hasher.finalize();
        prp_key.copy_from_slice(&hash[0..16]);

        let prp = SwapOrNotSr::new(prp_key, n);

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
    fn test_swap_or_not_sr_tee_inverse_roundtrip() {
        let key = [8u8; 16];
        let domain = 100u64;
        let prp_tee = SwapOrNotSrTee::new(key, domain);

        for x in 0..domain {
            let y = prp_tee.forward(x);
            let x_recovered = prp_tee.inverse(y);
            assert_eq!(x, x_recovered, "SR TEE inverse roundtrip failed for x={}", x);
        }
    }
}
