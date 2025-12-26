# BLAKE3 XOF Optimization for Plinko Hints

This document describes an alternative PRF mode using BLAKE3's extendable output function (XOF) for hint generation.

## Overview

The standard Plinko hint generation computes one BLAKE3 hash per (block, hint) pair. The XOF optimization replaces this with one BLAKE3-XOF stream per block, reducing hash initialization overhead.

## Standard Mode (Default)

For each block α and each hint j, compute a separate BLAKE3 hash:

```rust
for α in 0..c {
    k_α = BLAKE3(master_seed || "plinko_block" || α)
    for j in 0..num_hints {
        r = BLAKE3(k_α || "plinko_hint" || j)  // One hash per (block, hint)
        if r[0] & 1 {  // Bernoulli(1/2) inclusion
            β = u64(r[1..9]) % w
            hints[j] ^= DB[α * w + β]
        }
    }
}
```

**Cost**: `c × num_hints` BLAKE3 calls

For mainnet (c = 49k, num_hints = 6.3M, λ = 128):
- **310 billion** BLAKE3 hash calls

## XOF Mode

Use BLAKE3's extendable output function to generate one long pseudorandom stream per block:

```rust
for α in 0..c {
    xof = BLAKE3_XOF(master_seed || "plinko_block_xof" || α)
    buf = xof.read(num_hints × 9)  // 9 bytes per hint: 1 control + 8 for offset
    
    for j in 0..num_hints {
        control = buf[j * 9]
        if control & 1 {  // Bernoulli(1/2) inclusion
            β = u64(buf[j*9+1 .. j*9+9]) % w
            hints[j] ^= DB[α * w + β]
        }
    }
}
```

**Cost**: `c` BLAKE3-XOF streams (each producing `num_hints × 9` bytes)

For mainnet:
- **49,176** XOF streams
- Each stream outputs ~57 MB

## Benchmark Comparison (λ=128, Mainnet)

| Mode | Time | Throughput |
|------|------|------------|
| Standard | 19.5 min | 265M PRF/s |
| XOF | 19.0 min | 2.44 GB/s XOF |

At high λ, both modes achieve similar performance because the bottleneck shifts to:
- XOR operations (~132M/s)
- Memory bandwidth during parallel reduce phase

The XOF speedup is more pronounced at lower λ values where PRF overhead dominates.

## Why XOF Can Be Faster

1. **Amortized hash overhead**: One XOF initialization per block vs millions of hash calls
2. **BLAKE3 XOF efficiency**: Streams output using the same compression function
3. **Cache-friendly access**: Sequential XOF buffer reads

## Security Considerations

Both modes produce cryptographically secure pseudorandom bits:

- **BLAKE3** is a secure PRF when keyed
- **BLAKE3-XOF** is a secure extendable output function

The key difference:
- **Standard**: Each (block, hint) pair has independent randomness
- **XOF**: All hints for a given block derive from the same XOF stream

For Plinko's privacy guarantees, both approaches provide pseudorandom inclusion/offset decisions that are computationally indistinguishable from random. However, the XOF approach changes the PRF structure.

**Recommendation**: For production use, a formal security review should verify that the XOF construction maintains Plinko's privacy proofs.

## Usage

```bash
# Standard mode (default)
./target/release/plinko_hints \
  --db-path ./database.bin \
  --lambda 128

# XOF mode
./target/release/plinko_hints \
  --db-path ./database.bin \
  --lambda 128 \
  --xof
```

## Implementation

See [state-syncer/src/bin/plinko_hints.rs](../state-syncer/src/bin/plinko_hints.rs):
- `process_block_standard()` - Standard per-hint BLAKE3
- `process_block_xof()` - XOF stream per block
