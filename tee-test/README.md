# SEV-SNP TEE Test for Plinko Hint Generation

This directory contains scripts to test Plinko PIR hint generation inside an AMD SEV-SNP Trusted Execution Environment (TEE).

## Overview

AMD SEV-SNP (Secure Encrypted Virtualization - Secure Nested Paging) provides hardware-based memory encryption for virtual machines, protecting guest memory from the host/hypervisor. This allows running the Plinko hint generation in a confidential computing environment.

## Requirements

- AMD EPYC processor with SEV-SNP support (e.g., EPYC 9375F)
- SEV-SNP enabled in BIOS/UEFI
- Ubuntu 24.04 or similar Linux distribution
- QEMU 6.x+ with SEV support

## Setup Steps

### Step 1: Enable SEV-SNP in BIOS

Reboot and enter BIOS/UEFI. Enable these settings (location varies by motherboard):

**Common paths:**
- `Advanced` → `AMD CBS` → `CPU Common Options` → `SEV-SNP Memory Coverage` → **Enabled**
- `Advanced` → `AMD CBS` → `NBIO Common Options` → `SEV-SNP` → **Enabled**

**Required settings:**
- [x] SME (Secure Memory Encryption) - Enabled
- [x] SEV (Secure Encrypted Virtualization) - Enabled
- [x] SEV-ES (Encrypted State) - Enabled
- [x] SEV-SNP (Secure Nested Paging) - Enabled
- [x] IOMMU - Enabled (required for SEV)

Save and reboot.

### Step 2: Verify SEV-SNP after reboot

```bash
cd tee-test
./01-verify-sev-snp.sh
```

### Step 3: Install QEMU and dependencies

```bash
./02-install-packages.sh
```

### Step 4: Download Ubuntu cloud image

```bash
./03-download-image.sh
```

### Step 5: Create and start SEV-SNP VM

```bash
./04-create-vm.sh
```

### Step 6: Copy data and run benchmark

```bash
# In another terminal
./05-copy-data-to-vm.sh

# SSH into VM
ssh -p 2222 ubuntu@localhost

# Inside VM:
cd /mnt/plinko
./run-benchmark.sh
```

## Expected Results

Based on Oracle analysis, expected overhead for SEV-SNP vs bare metal:
- **5-20% slowdown** due to memory encryption
- VM should be provisioned with 128-192GB RAM for the 73GB database
- 32-64 vCPUs for parallel processing

## Scripts

| Script | Description |
|--------|-------------|
| `01-verify-sev-snp.sh` | Verify SEV-SNP is enabled after reboot |
| `02-install-packages.sh` | Install QEMU, OVMF, and dependencies |
| `03-download-image.sh` | Download Ubuntu 24.04 cloud image |
| `04-create-vm.sh` | Create and boot SEV-SNP VM |
| `05-copy-data-to-vm.sh` | Copy database and binary to VM |
| `run-benchmark.sh` | Benchmark script to run inside VM |

## Attestation (Future Work)

For remote attestation, the [AMD SEV-SNP Attestation SDK](https://github.com/automata-network/amd-sev-snp-attestation-sdk) can be integrated to:
- Generate attestation reports proving computation ran in SEV-SNP
- Verify guest measurements and boot chain
- Enable secure key provisioning based on attestation

## References

- [AMD SEV-SNP Documentation](https://www.amd.com/en/developer/sev.html)
- [QEMU SEV Documentation](https://www.qemu.org/docs/master/system/i386/amd-memory-encryption.html)
- [AMD SEV-SNP Attestation SDK](https://github.com/automata-network/amd-sev-snp-attestation-sdk)
