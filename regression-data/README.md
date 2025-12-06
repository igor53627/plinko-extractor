# Plinko Regression Test Database

A smaller Ethereum state snapshot for fast regression testing and development.

## Dataset Summary

| Metric | Value |
|--------|-------|
| Source Block | #23,889,314 (Dec 5, 2025) |
| Accounts | 30,000,000 |
| Storage Slots | 30,000,000 |
| Total Entries (N) | 120,000,000 |
| Database Size | 3.6 GB |

## Files

| File | Size | Description |
|------|------|-------------|
| `database.bin.partaa` | 1.9 GB | Flat array of 32-byte words (part 1) |
| `database.bin.partab` | 1.7 GB | Flat array of 32-byte words (part 2) |
| `account-mapping.bin` | 687 MB | Address → index lookup |
| `storage-mapping.bin` | 1.6 GB | (Address, Slot) → index lookup |
| `metadata.json` | 147 B | Extraction metadata |

### Reassembling database.bin

```bash
cat database.bin.part* > database.bin
```

## Extraction Command

```bash
/mnt/mainnet/plinko/target/release/plinko-extractor \
  --db-path /mnt/mainnet/data/db \
  --output-dir /mnt/mainnet/plinko/regression \
  --limit 30000000
```

## Benchmark Results

### Test Parameters

- **Lambda (λ)**: 128
- **Entries per block (w)**: 49,177
- **Number of blocks (c)**: 2,440
- **Number of hints**: 6,294,656
- **Hint storage**: 192 MB

### Performance (AES-CTR Mode)

| Environment | vCPUs | Time | Throughput | XOR ops/s |
|-------------|-------|------|------------|-----------|
| Bare metal | 64 | 57s | 63.8 MB/s | 134M/s |
| SEV-SNP TEE | 32 | 214s | 17.2 MB/s | 36M/s |

**SEV-SNP overhead**: ~3.7x (with half vCPUs)

### Test Commands

```bash
# Bare metal
./target/release/plinko_hints \
  --db-path regression-data/database.bin \
  --lambda 128 --aes \
  --entries-per-block 49177 --allow-truncation

# SEV-SNP (inside VM)
/mnt/plinko/plinko_hints \
  --db-path /mnt/plinko/regression.bin \
  --lambda 128 --aes \
  --entries-per-block 49177 --allow-truncation
```

## Test Environment

- **Host**: AMD EPYC 9375F (64 cores, 1.1TB RAM)
- **SEV-SNP VM**: Ubuntu 24.04, 32 vCPUs, 128GB RAM
- **QEMU**: 10.0.0 (AMDESE/qemu snp-latest)
- **OVMF**: edk2-stable202502 (AMDESE/ovmf snp-latest)

## Notes

- This dataset uses the first 30M accounts/storage slots in key order (not recent blocks)
- The c/w ratio is 0.05, which is suboptimal but sufficient for regression testing
- For production benchmarks, use the full 73GB mainnet database with w=√N
