# Constant-Time Mode for TEE Execution

## Security Goal

Eliminate timing side-channels that could leak the iPRF mapping (i.e., which hints contain which database entries).

This is critical because in Plinko, the hint structure encodes which database entries a client can privately retrieve. Leaking this structure would compromise PIR privacy.

## Implementation

Key techniques used:

- **Fixed-bound loops**: Always iterates `MAX_PREIMAGES` (512) times per entry, using masks to skip invalid indices. This prevents leaking preimage counts.

- **Branchless membership**: Uses `BlockBitset::contains_ct()` for O(1) bit lookup instead of binary search, preventing timing variation based on subset contents.

- **Masked XOR**: Uses `ct_xor_32_masked()` to conditionally XOR without branches, ensuring constant-time parity updates.

- **Branchless index clamping**: Uses `ct_select_usize` for safe array indexing.

## Security Model and Limitations

The CT mode protects against timing side-channels but does NOT provide full memory-access obliviousness. Array indexing patterns (e.g., `regular_bitsets[j]`) may leak information to cache side-channel attackers (Prime+Probe, etc.).

This is acceptable for the paper's security model, which reasons in an idealized RAM model without microarchitectural side-channels. For stronger protection, an ORAM-based approach would be needed (O(n) overhead).

## MAX_PREIMAGES Bound

With default parameters (λ=128, q=λw), expected preimages per offset is approximately 2λ = 256.

The bound MAX_PREIMAGES=512 (approximately 2μ) ensures truncation probability < 2^{-140} via Chernoff bounds.

A parameter guard enforces this at runtime:

```text
expected_preimages * 2 <= MAX_PREIMAGES
```

If exceeded, the program exits with an error instructing the user to reduce `total_hints` or increase `w`.

## Runtime Guards

The constant-time path requires:

1. `num_regular > 0` (lambda >= 1)
2. `num_backup > 0` (use `--backup-hints` to set q > 0)
3. Expected preimages * 2 <= MAX_PREIMAGES

## Performance

This mode is ~2-3x slower than the standard path due to the fixed-iteration loops and branchless operations.
