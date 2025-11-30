# Plinko Extractor - Agent Rules

## Host: root@aya

- **Reth DB location**: `/mnt/mainnet/data`
- **Working directory**: `/mnt/mainnet/plinko`
- **DO NOT** create artifacts outside `/mnt/mainnet/plinko` without explicit user permission

## Build Commands

```bash
# Build extractor
cargo build --release

# Build hints generator
cd state-syncer && cargo build --release --bin plinko_hints
```

## Run Commands

```bash
# Extract from Reth DB (on aya)
./target/release/plinko-extractor \
  --db-path /mnt/mainnet/data \
  --output-dir /mnt/mainnet/plinko

# Generate hints (standard mode)
./state-syncer/target/release/plinko_hints \
  --db-path /mnt/mainnet/plinko/database.bin \
  --lambda 128

# Generate hints (XOF mode - faster)
./state-syncer/target/release/plinko_hints \
  --db-path /mnt/mainnet/plinko/database.bin \
  --lambda 128 --xof
```

## Data Format

- Accounts: 3 words (96 bytes) - nonce, balance, bytecode_hash
- Storage: 1 word (32 bytes) - value
