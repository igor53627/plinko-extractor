> [!CAUTION]
> **OBSOLETE** - This spec was implemented in PR #67. See [docs/constant_time_mode.md](../constant_time_mode.md) for current documentation.

# Implement Data-Oblivious iPRF for TEE Server-Side Hint Generation

## Summary

Implement constant-time (data-oblivious) iPRF algorithms to enable secure server-side hint preprocessing inside a Trusted Execution Environment (TEE).

## Motivation

Current iPRF implementation in [`iprf.rs`](../../state-syncer/src/iprf.rs) uses variable-length loops and conditional branches that leak information through timing side channels:

```rust
// LEAKY: Branch on secret PRF bit
if self.prf_bit(round_num, canonical) {
    partner
} else {
    x
}

// LEAKY: Early return based on secret condition
if ball_index < left_count {
    high = mid;
    ball_count = left_count;
} else {
    // ...
}
```

For TEE execution, all operations must be data-oblivious (constant-time) to prevent the server from inferring private keys or query patterns through timing analysis.

**Reference:** https://gist.github.com/igor53627/1fbfa268da16b614fb7994ecabcd53bb

## Background

### Current Architecture

1. **SwapOrNot PRP** ([Morris-Rogaway 2013](https://eprint.iacr.org/2013/560.pdf)): Small-domain permutation using swap-or-not rounds
2. **PMNS** (Pseudorandom Multinomial Sampler): Binary tree traversal for ball-into-bins mapping
3. **iPRF**: Composition of PRP + PMNS for invertible PRF
4. **HintInit** (`plinko_hints.rs`): Generates PIR hints by XOR-accumulating database entries

### Timing Leakage Points

| Component | Leakage | Fix |
|-----------|---------|-----|
| `SwapOrNot::round()` | Branch on `prf_bit` | `ct_select` |
| `SwapOrNot::round()` | `x.max(partner)` | Arithmetic mask |
| `Iprf::trace_ball_inverse()` | `if y <= mid` branch | Masked arithmetic |
| `Iprf::trace_ball_inverse()` | Variable-size `Vec` return | Fixed-size array + mask |
| `process_block_*()` | `if !include { continue }` | Masked XOR |

## Implementation Plan

### Phase 1: Constant-Time Primitives

**New file:** `state-syncer/src/constant_time.rs`

```rust
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq, ConstantTimeLess};

/// Branchless select: returns a if mask is all-1s, b otherwise
pub fn ct_select_u64(mask: u64, a: u64, b: u64) -> u64 {
    b ^ (mask & (a ^ b))
}

/// Returns u64::MAX if a == b, 0 otherwise
pub fn ct_eq_u64(a: u64, b: u64) -> u64 {
    let diff = a ^ b;
    let is_zero = diff | diff.wrapping_neg();
    (is_zero >> 63).wrapping_sub(1)
}

/// Returns u64::MAX if a < b, 0 otherwise
pub fn ct_lt_u64(a: u64, b: u64) -> u64 {
    let borrow = ((!a) & b) | (((!a) ^ b) & (a.wrapping_sub(b)));
    (borrow >> 63).wrapping_neg()
}

/// Linear-scan ORAM read - touches all elements
pub fn ct_load<T: Copy + Default>(arr: &[T], secret_idx: usize) -> T {
    let mut result = T::default();
    for (i, item) in arr.iter().enumerate() {
        let mask = ct_eq_u64(i as u64, secret_idx as u64);
        // Apply mask to select item when i == secret_idx
        result = ct_select(mask, *item, result);
    }
    result
}

/// Linear-scan ORAM write - touches all elements
pub fn ct_store<T: Copy>(arr: &mut [T], secret_idx: usize, val: T) {
    for (i, item) in arr.iter_mut().enumerate() {
        let mask = ct_eq_u64(i as u64, secret_idx as u64);
        *item = ct_select(mask, val, *item);
    }
}
```

### Phase 2: SwapOrNot_TEE (Branchless PRP)

```rust
impl SwapOrNotTee {
    /// Branchless round - no secret-dependent branches
    fn round_ct(&self, round_num: usize, x: u64) -> u64 {
        let k_i = self.derive_round_key(round_num);
        let partner = (k_i + self.domain - (x % self.domain)) % self.domain;
        
        // Branchless max for canonical representative
        let x_lt_partner = ct_lt_u64(x, partner);
        let canonical = ct_select_u64(x_lt_partner, partner, x);
        
        // Branchless swap decision
        let swap_mask = self.prf_bit_ct(round_num, canonical); // returns 0 or u64::MAX
        ct_select_u64(swap_mask, partner, x)
    }
    
    fn prf_bit_ct(&self, round: usize, canonical: u64) -> u64 {
        // ... encrypt and return mask instead of bool
        let bit = block[0] & 1;
        (bit as u64).wrapping_neg() // 0 -> 0, 1 -> u64::MAX
    }
}
```

### Phase 3: PMNS_TEE (Constant-Time Multinomial Sampler)

```rust
/// Maximum preimages for fixed-size array (n for domain n, but typically small)
const MAX_PREIMAGES: usize = 64;

impl IprfTee {
    /// Constant-time inverse with fixed iteration count
    fn trace_ball_inverse_ct(&self, y: u64, n: u64, m: u64) -> ([u64; MAX_PREIMAGES], usize) {
        let depth = (m as f64).log2().ceil() as usize;
        
        let mut low = 0u64;
        let mut high = m - 1;
        let mut ball_count = n;
        let mut ball_start = 0u64;
        
        // Fixed D iterations regardless of early termination condition
        for _level in 0..depth {
            let should_continue = ct_lt_u64(low, high); // mask: continue if low < high
            
            let mid = (low + high) / 2;
            let left_bins = mid - low + 1;
            let total_bins = high - low + 1;
            
            let node_id = encode_node(low, high, n);
            let prf_output = self.prf_eval(node_id);
            let left_count = Self::binomial_sample(ball_count, left_bins, total_bins, prf_output);
            
            let go_left = ct_le_u64(y, mid); // mask for y <= mid
            
            // Branchless updates (only apply if should_continue)
            let new_high_left = mid;
            let new_high_right = high;
            let new_low_left = low;
            let new_low_right = mid + 1;
            
            high = ct_select_u64(should_continue & go_left, new_high_left,
                   ct_select_u64(should_continue & !go_left, new_high_right, high));
            low = ct_select_u64(should_continue & go_left, new_low_left,
                  ct_select_u64(should_continue & !go_left, new_low_right, low));
            
            // ... similar for ball_count, ball_start
        }
        
        // Build fixed-size output array
        let mut result = [0u64; MAX_PREIMAGES];
        let count = ball_count.min(MAX_PREIMAGES as u64) as usize;
        for i in 0..MAX_PREIMAGES {
            let in_range = ct_lt_u64(i as u64, count as u64);
            result[i] = ct_select_u64(in_range, ball_start + i as u64, 0);
        }
        
        (result, count)
    }
}
```

### Phase 4: Iprf_TEE.inverse

```rust
impl IprfTee {
    /// Returns fixed-size array with validity mask
    pub fn inverse_ct(&self, y: u64) -> ([u64; MAX_PREIMAGES], [bool; MAX_PREIMAGES]) {
        let (pmns_preimages, count) = self.trace_ball_inverse_ct(y, self.domain, self.range);
        
        let mut results = [0u64; MAX_PREIMAGES];
        let mut valid = [false; MAX_PREIMAGES];
        
        // Always compute MAX_PREIMAGES inverse PRPs (constant time)
        for i in 0..MAX_PREIMAGES {
            let is_valid = i < count;
            let z = pmns_preimages[i];
            
            // Always compute PRP inverse (even for invalid entries)
            results[i] = self.prp.inverse_ct(z);
            valid[i] = is_valid;
        }
        
        (results, valid)
    }
}
```

### Phase 5: HintInit Constant-Time

Modify `plinko_hints.rs` to add `--tee` mode:

```rust
/// Masked XOR - always executes XOR, but result is conditional
fn xor_32_masked(dst: &mut [u8; 32], src: &[u8; 32], include_mask: u64) {
    let mask_byte = (include_mask & 0xFF) as u8;
    for i in 0..32 {
        dst[i] ^= src[i] & mask_byte;
    }
}

fn process_block_tee(
    alpha: usize,
    db_bytes: &[u8],
    block_size_bytes: usize,
    w: usize,
    num_hints: usize,
    master_seed: &[u8; 32],
) -> (Vec<[u8; 32]>, u64) {
    // ... similar to process_block_aes but:
    // 1. No `if !include { continue }` - use masked XOR instead
    // 2. All iterations run regardless of include bit
    
    for j in 0..num_hints {
        let r = aes_hint_prf(&block_key, j as u64);
        
        // Convert include bit to mask (0x00 or 0xFF)
        let include_mask = ((r[0] & 1) as u64).wrapping_neg();
        
        let rand64 = u64::from_le_bytes(r[1..9].try_into().unwrap());
        let beta = (rand64 as usize) % w;
        
        let entry_offset = beta * WORD_SIZE;
        let entry: [u8; 32] = block_bytes[entry_offset..entry_offset + WORD_SIZE]
            .try_into()
            .unwrap();
        
        // Always XOR, but masked - no branch on include
        xor_32_masked(&mut partial_hints[j], &entry, include_mask);
        xor_count += include_mask & 1; // Count only if included
    }
}
```

## Files to Create/Modify

| File | Action | Description |
|------|--------|-------------|
| `state-syncer/src/constant_time.rs` | Create | CT primitives using `subtle` crate |
| `state-syncer/src/iprf.rs` | Modify | Add `SwapOrNotTee`, `IprfTee` structs |
| `state-syncer/src/bin/plinko_hints.rs` | Modify | Add `--tee` flag and `process_block_tee()` |
| `state-syncer/src/lib.rs` | Modify | Export `constant_time` module |
| `state-syncer/Cargo.toml` | Modify | Add `subtle = "2.5"` dependency |

## Testing Strategy

### Functional Equivalence Tests

```rust
#[test]
fn tee_iprf_matches_standard_iprf() {
    let key = [0u8; 16];
    let iprf = Iprf::new(key, 1000, 100);
    let iprf_tee = IprfTee::new(key, 1000, 100);
    
    for y in 0..100 {
        let standard = iprf.inverse(y);
        let (tee_results, tee_valid) = iprf_tee.inverse_ct(y);
        
        let tee_filtered: Vec<_> = tee_results.iter()
            .zip(tee_valid.iter())
            .filter(|(_, &v)| v)
            .map(|(&r, _)| r)
            .collect();
        
        assert_eq!(standard, tee_filtered);
    }
}
```

### Static Analysis

```bash
# Grep for secret-dependent branches in TEE code
grep -n "if.*secret\|while.*secret\|for.*secret" state-syncer/src/*.rs
```

### Timing Analysis (Optional)

Measure execution time variance across different keys/inputs - should be constant.

## Performance Considerations

- **Runtime increase**: O(k) -> O(n) for inverse operations (acceptable for offline preprocessing)
- **Memory**: Linear-scan ORAM acceptable if hint DB fits in TEE enclave (~10^5-10^6 hints)
- **AES-NI**: Ensure TEE has AES-NI for PRF throughput matching current benchmarks

## References

- [Plinko Paper (2024-318)](https://eprint.iacr.org/2024/318.pdf)
- [Morris-Rogaway Swap-or-Not (2013-560)](https://eprint.iacr.org/2013/560.pdf)
- [Keyword PIR with Cuckoo Hashing](https://eprint.iacr.org/2019/1483.pdf)
- [subtle crate](https://docs.rs/subtle) - Rust constant-time primitives

## Checklist

- [ ] Phase 1: Constant-time primitives
- [ ] Phase 2: SwapOrNot_TEE
- [ ] Phase 3: PMNS_TEE
- [ ] Phase 4: Iprf_TEE.inverse
- [ ] Phase 5: HintInit constant-time
- [ ] Unit tests for functional equivalence
- [ ] Static review for secret-dependent branches
- [ ] Benchmarks comparing TEE vs standard mode
