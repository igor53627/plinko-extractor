# Plinko FPGA Accelerator

Hardware acceleration for Swap-or-Not PRP inverse operations used in Plinko PIR hint generation.

## Architecture

```
+------------------+      +-----------------------+
| TEE (SEV-SNP)    |<---->| FPGA Accelerator      |
|                  | PCIe |                       |
| - Hint storage   | TDISP| - 512-lane systolic   |
| - Query handler  |      |   PRP array           |
| - XOR accum      |      | - Shared AES pipeline |
+------------------+      +-----------------------+
```

## Components

### RTL Modules

| Module | Description | Status |
|--------|-------------|--------|
| `aes_sbox.v` | AES S-Box lookup (combinational) | [PASS] Verified |
| `aes_round.v` | Single AES round (SubBytes, ShiftRows, MixColumns, AddRoundKey) | [WIP] Byte order fix needed |
| `aes128_encrypt.v` | Pipelined AES-128 (12 stages, 1 block/cycle throughput) | [WIP] Depends on round fix |
| `swap_or_not_round.v` | Single Swap-or-Not PRP round | [WIP] |
| `prp_systolic_array.v` | 512-lane parallel PRP inverse | [WIP] |

### Resource Estimates (Xilinx Virtex UltraScale+ VU9P)

| Resource | Single AES Core | 512-Lane Array | Available | Utilization |
|----------|-----------------|----------------|-----------|-------------|
| LUTs | ~2,000 | ~150,000 | 1,182,240 | ~13% |
| FFs | ~1,500 | ~100,000 | 2,364,480 | ~4% |
| BRAM | 0 | ~50 | 2,160 | ~2% |
| DSP | 0 | 0 | 6,840 | 0% |

### Performance Projections

**Target**: 512 candidates × 700 rounds per iPRF inverse

| Metric | Software (Rust+AES-NI) | FPGA @ 250MHz |
|--------|------------------------|---------------|
| AES ops/inverse | 4.6M (sequential) | 700 (shared) |
| Latency/inverse | ~5-10 ms | ~35 μs |
| Speedup | 1x | ~150-300x |

**Note**: FPGA shares round keys across all 512 lanes, reducing AES calls from 4.6M to ~700.

## Building

### Prerequisites

- Icarus Verilog for simulation: `brew install icarus-verilog`
- GTKWave for waveform viewing: `brew install gtkwave`
- Xilinx Vivado for synthesis (target: VU9P or Alveo U250)

### Simulation

```bash
cd fpga

# Run AES testbench
iverilog -o sim/aes_test rtl/*.v sim/tb_aes128.v
vvp sim/aes_test

# View waveforms
gtkwave aes128.vcd
```

## TEE Integration

For AMD SEV-SNP + FPGA integration, the FPGA must support TDISP (TEE Device Interface Security Protocol):

1. **Device attestation**: FPGA provides identity/config to SEV-SNP guest
2. **IDE streams**: PCIe traffic encrypted between TEE and FPGA
3. **Memory isolation**: FPGA accesses guest private memory directly

### Compatible Hardware

- Intel PAC with Stratix 10 (TDISP support TBD)
- Xilinx Alveo U250/U280 (TDISP support TBD)
- Custom ASIC with TDISP interface

## TODO

- [ ] Fix AES byte ordering (FIPS 197 column-major)
- [ ] Complete Swap-or-Not round integration
- [ ] Add PMNS ball tracing logic
- [ ] Synthesize to get accurate resource/timing
- [ ] PCIe DMA interface design
- [ ] TDISP attestation flow
