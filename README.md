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
- **Storage Slots**: Each individual storage slot occupies 1 entry (32 bytes).
  - Word 0: Storage Value
  - *Note*: If an account has multiple storage slots (e.g., a smart contract), each slot is stored as a separate, independent entry in this flat file. The `storage-mapping.bin` allows looking up the index for any specific `(Address, SlotKey)` pair.

### 2. `account-mapping.bin`
Mapping of addresses to their index in `database.bin`.
- Format: `Address (20 bytes) || Index (4 bytes, LE)`
- Note: `Index` points to the start of the 4-word block.

### 3. `storage-mapping.bin`
Mapping of storage slots to their index in `database.bin`.
- Format: `Address (20 bytes) || SlotKey (32 bytes) || Index (4 bytes, LE)`
- Note: `Index` points to the 1-word entry.

## Client vs. Server Usage

| File | Size (Mainnet) | Server Usage | Client Usage |
| :--- | :--- | :--- | :--- |
| **`database.bin`** | ~82 GB | **Store** (Source of Truth). Used to answer PIR queries and compute deltas. | **Stream & Discard**. Client downloads this once to generate ~200MB of local Hints (parities), then deletes the raw data. |
| **`account-mapping.bin`** | ~7.4 GB | **Store**. Used to locate accounts when processing block updates. | **Store**. Client needs this to resolve `Address -> Index` to know which Hint allows recovering the account data. |
| **`storage-mapping.bin`** | ~74 GB | **Store**. Used to locate storage slots when processing block updates. | **None / Optional**. Most light clients (wallets) only need Account states. If storage access is needed, a client might query this mapping remotely or store a partial index. |

These artifacts allow a PIR client to look up any account state or storage slot privately.

## Statistics (Mainnet Snapshot)

*As of Block #23,237,684 (Nov 23, 2025)*

- **Total Unique Accounts**: 328,168,813
- **Total Storage Slots**: 1,415,847,352
- **Total Database Size**: ~87 GB
- **Total Mapping Size**: ~87 GB

## Update Strategy

To keep the PIR database fresh without re-downloading the entire ~175GB dataset:

1.  **Initial Sync**: Client downloads the full `database.bin` snapshot (once).
2.  **Incremental Updates**:
    *   A separate service monitors the chain for state changes.
    *   It publishes a compact list of `(DatabaseIndex, NewValue)` for each block.
    *   **Client Update**: The Plinko client updates its local hints using the XOR property:
        `NewHint = OldHint XOR (OldVal at Index) XOR (NewVal at Index)`
    *   This operation is $O(1)$ per changed state entry.

