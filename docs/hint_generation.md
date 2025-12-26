# Plinko PIR Hint Generator

Implements Plinko's HintInit matching Fig. 7 of the paper and Plinko.v Coq spec.

## Key Design (per paper and Coq formalization)

- Generates c iPRF keys (one per block), not one global key
- Regular hints: block subset of size c/2+1, single parity
- Backup hints: block subset of size c/2, dual parities (in/out)
- iPRF domain = total hints (λw + q), range = w (block size)

## Module Structure

| File | Purpose |
|------|---------|
| types.rs | Data structures (RegularHint, BackupHint, Args) |
| bitset.rs | BlockBitset for CT membership testing |
| keys.rs | iPRF key and seed derivation |
| subsets.rs | Block subset computation |
| fast_path.rs | Standard streaming (non-CT) |
| ct_path.rs | Constant-time streaming for TEE |

## Usage

```bash
# Build
cd state-syncer && cargo build --release --bin plinko_hints

# Generate hints (standard mode)
./target/release/plinko_hints \
  --db-path ./database.bin \
  --lambda 128

# Generate hints (XOF mode - faster at low λ)
./target/release/plinko_hints \
  --db-path ./database.bin \
  --lambda 128 --xof

# Generate hints (constant-time mode for TEE)
./target/release/plinko_hints \
  --db-path ./database.bin \
  --lambda 128 --constant-time
```

See [xof-optimization.md](xof-optimization.md) for details on the XOF optimization.

See [constant_time_mode.md](constant_time_mode.md) for TEE security details.
