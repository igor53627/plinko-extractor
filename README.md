# Plinko Extractor

A high-performance Rust tool to extract the complete Ethereum state (Accounts and Storage) directly from a Reth database and convert it into the artifacts required by the Plinko PIR server.

## Why this exists?
- **Speed**: Directly reads the MDBX database using `reth-db`, bypassing RPC overhead.
- **Efficiency**: Streams data to the output files with minimal memory footprint.
- **State Tree Support**: Extracts both Accounts and Storage Slots into a unified flat database format suitable for PIR.

## Usage

```bash
# Build release binary
cargo build --release

# Run extractor
./target/release/plinko-extractor \
  --db-path /path/to/reth/db \
  --output-dir ./data \
  --limit 1000000 # Optional: Extract subset for testing
```

### Options
- `--db-path`: Path to the Reth database (default: `/var/lib/reth/mainnet/db`).
- `--output-dir`: Output directory (default: `data`).
- `--limit`: (Optional) Limit the number of accounts/slots extracted (for testing).

## Output Artifacts

The extractor produces three files:

### 1. `database.bin`
A flat binary file containing 32-byte words.
- **Accounts**: occupy 4 consecutive entries (128 bytes).
  - Word 0: Nonce
  - Word 1: Balance
  - Word 2: Bytecode Hash
  - Word 3: Padding (Reserved)
- **Storage Slots**: occupy 1 entry (32 bytes).
  - Word 0: Storage Value

### 2. `account-mapping.bin`
Mapping of addresses to their index in `database.bin`.
- Format: `Address (20 bytes) || Index (4 bytes, LE)`
- Note: `Index` points to the start of the 4-word block.

### 3. `storage-mapping.bin`
Mapping of storage slots to their index in `database.bin`.
- Format: `Address (20 bytes) || SlotKey (32 bytes) || Index (4 bytes, LE)`
- Note: `Index` points to the 1-word entry.

These artifacts allow a PIR client to look up any account state or storage slot privately.
