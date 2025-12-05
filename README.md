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
- **Accounts**: occupy 3 consecutive entries (96 bytes).
  - Word 0: Nonce (u64 in first 8 bytes, zero-padded)
  - Word 1: Balance (u256, little-endian)
  - Word 2: Bytecode Hash
- **Storage Slots**: Each individual storage slot occupies 1 entry (32 bytes).
  - Word 0: Storage Value
  - *Note*: If an account has multiple storage slots (e.g., a smart contract), each slot is stored as a separate, independent entry in this flat file. The `storage-mapping.bin` allows looking up the index for any specific `(Address, SlotKey)` pair.

> **Note**: Earlier versions used 4 words per account (with a padding word). This was removed to reduce total entries N by ~12%, improving hint generation performance.

### 2. `account-mapping.bin`
Mapping of addresses to their index in `database.bin`.
- Format: `Address (20 bytes) || Index (4 bytes, LE)`
- Note: `Index` points to the start of the 3-word block.

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

- **Total Unique Accounts**: 330,142,988
- **Total Storage Slots**: 1,427,085,312
- **Total Entries (N)**: 2,417,514,276 (accounts × 3 + storage)
- **Total Database Size**: 73 GB
- **Total Mapping Size**: ~82 GB

## Hint Generation

The `state-syncer` crate includes a Plinko hint generator for benchmarking:

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
```

See [docs/xof-optimization.md](docs/xof-optimization.md) for details on the XOF optimization.

### Benchmark Results (Mainnet, λ=128, w=49177)

*AMD EPYC 9375F, 1.1TB RAM*

| Environment | vCPUs | Time | Throughput | XOR ops/s | Hint Storage |
|-------------|-------|------|------------|-----------|--------------|
| Bare metal | 64 | 22 min | 55.8 MB/s | 117M/s | 192 MB |
| SEV-SNP TEE | 32 | 57 min | 21.5 MB/s | 45M/s | 192 MB |

**SEV-SNP overhead: ~2.6x** (with half vCPUs). Normalized for vCPUs: ~1.3x.

The bottleneck is memory bandwidth (~117M XOR/s), not PRF computation. Both BLAKE3 and AES-CTR modes achieve similar performance with optimal Plinko parameters (w=√N).

Full benchmark results: 
- [Hint generation benchmark](https://gist.github.com/igor53627/44f237c4f89fb6dcf20a58d71af0d048)
- [SEV-SNP TEE benchmark](https://gist.github.com/igor53627/4c21ea3ea9d8963d4d20c9277cc45754)

## Update Strategy

To keep the PIR database fresh without re-downloading the entire ~175GB dataset:

1.  **Initial Sync**: Client downloads the full `database.bin` snapshot (once).
2.  **Incremental Updates**:
    *   A separate service monitors the chain for state changes.
    *   It publishes a compact list of `(DatabaseIndex, NewValue)` for each block.
    *   **Client Update**: The Plinko client updates its local hints using the XOR property:
        `NewHint = OldHint XOR (OldVal at Index) XOR (NewVal at Index)`
    *   This operation is $O(1)$ per changed state entry.

## iPRF Implementation

The Plinko PIR scheme relies on an Invertible PRF (iPRF) built from:
- **Swap-or-Not PRP**: Small-domain pseudorandom permutation (Morris-Rogaway 2013)
- **PMNS**: Pseudorandom Multinomial Sampler (binary tree ball-into-bins simulation)

### Implementation Parity

We maintain consistency between three sources:

| Component | Paper (2024-318) | Coq Formalization | Rust Implementation |
|-----------|------------------|-------------------|---------------------|
| iPRF structure | §4.2: `iF.F(k,x) = S(P(x))` | [Plinko.v](docs/Plinko.v) `iPRF.forward` | [iprf.rs](state-syncer/src/iprf.rs) `Iprf::forward` |
| iPRF inverse | §4.2: `iF.F⁻¹(k,y) = {P⁻¹(z) : z ∈ S⁻¹(y)}` | `iPRF.inverse` | `Iprf::inverse` |
| PMNS forward | Algorithm 1 | `PMNS.forward` | `Iprf::trace_ball` |
| PMNS inverse | Algorithm 2 | `PMNS.inverse` | `Iprf::trace_ball_inverse` |
| Binomial sampling | §4.3: "derandomized using r as randomness" | `binomial_sample` | `Iprf::binomial_sample` |
| Swap-or-Not PRP | Referenced: Morris-Rogaway 2013 | `SwapOrNot.prp_forward/inverse` | `SwapOrNot::forward/inverse` |

**Key design decision**: The paper doesn't specify the exact binomial sampling algorithm. We use a simple integer-arithmetic sampler matching the Coq formalization:

```text
binomial_sample(count, num, denom, prf_output) = (count * num + (prf_output mod (denom + 1))) / denom
```

This trades a slightly looser security bound for provable correctness and exact Rust-Coq parity.

### Documentation

- **Paper**: [docs/2024-318.pdf](docs/2024-318.pdf) - Original academic paper
- **Parsed Paper** (machine-readable JSON):
  - [plinko_paper_index.json](docs/plinko_paper_index.json) - Document structure
  - [plinko_paper_part2_technical.json](docs/plinko_paper_part2_technical.json) - Technical foundations
  - [plinko_paper_part3_scheme.json](docs/plinko_paper_part3_scheme.json) - Plinko scheme details
  - [plinko_paper_part6_algorithms.json](docs/plinko_paper_part6_algorithms.json) - Pseudocode
- **Coq Formalization**: [docs/Plinko.v](docs/Plinko.v) - Mechanized proofs and reference implementation

## References

- [Plinko: Single-Server PIR with Efficient Updates](https://vitalik.eth.limo/general/2025/11/25/plinko.html) - Vitalik Buterin's overview
- [Plinko Paper (ePrint 2024/318)](https://eprint.iacr.org/2024/318.pdf) - Academic paper by Mughees, Shi, and Chen
- [Morris-Rogaway 2013](https://eprint.iacr.org/2013/560.pdf) - Swap-or-Not small-domain PRP construction

