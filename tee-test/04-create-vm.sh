#!/bin/bash
# Create and boot SEV-SNP VM for Plinko testing

set -e
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

# VM Configuration
VCPUS=32          # Start with 32 vCPUs for testing (can scale to 64)
MEMORY=131072     # 128 GB RAM (in MB)
DISK="vm-disk.qcow2"
CLOUDINIT="cloud-init.iso"
SSH_PORT=2222

# Find OVMF firmware
if [[ -f /usr/share/OVMF/OVMF_CODE_4M.ms.fd ]]; then
    OVMF_CODE="/usr/share/OVMF/OVMF_CODE_4M.ms.fd"
    OVMF_VARS="/usr/share/OVMF/OVMF_VARS_4M.ms.fd"
elif [[ -f /usr/share/OVMF/OVMF_CODE.fd ]]; then
    OVMF_CODE="/usr/share/OVMF/OVMF_CODE.fd"
    OVMF_VARS="/usr/share/OVMF/OVMF_VARS.fd"
else
    echo "Error: OVMF firmware not found"
    exit 1
fi

# Copy OVMF vars (needs to be writable)
cp "$OVMF_VARS" ./ovmf-vars.fd

echo "=== Starting SEV-SNP VM ==="
echo "  vCPUs: $VCPUS"
echo "  RAM: $((MEMORY/1024)) GB"
echo "  SSH: localhost:$SSH_PORT"
echo "  OVMF: $OVMF_CODE"
echo

# Check if SEV-SNP is available
if [[ ! -f /sys/module/kvm_amd/parameters/sev_snp ]] || [[ $(cat /sys/module/kvm_amd/parameters/sev_snp) != "Y" ]]; then
    echo "Warning: SEV-SNP not detected, running in regular mode for testing"
    SEV_OPTS=""
    MACHINE_OPTS="q35"
else
    echo "SEV-SNP detected, enabling confidential computing"
    # SEV-SNP guest configuration:
    # - cbitpos=51: C-bit position for memory encryption (EPYC standard)
    # - reduced-phys-bits=1: Reduce physical address bits due to C-bit encryption
    SEV_OPTS="-object sev-snp-guest,id=sev0,cbitpos=51,reduced-phys-bits=1"
    MACHINE_OPTS="q35,memory-encryption=sev0"
fi

# Validate prerequisites before launching
if [[ ! -f "$DISK" ]]; then
    echo "Error: VM disk not found: $DISK"
    echo "Run ./03-download-image.sh first"
    exit 1
fi

if [[ ! -f "$CLOUDINIT" ]]; then
    echo "Error: cloud-init ISO not found: $CLOUDINIT"
    echo "Run ./03-download-image.sh first"
    exit 1
fi

echo "Starting QEMU..."
echo "(Use Ctrl+A, X to exit console, or SSH to port $SSH_PORT)"
echo

qemu-system-x86_64 \
    -enable-kvm \
    -cpu EPYC-v4 \
    -smp "$VCPUS" \
    -m "$MEMORY" \
    -machine "$MACHINE_OPTS" \
    -drive if=pflash,format=raw,unit=0,file="$OVMF_CODE",readonly=on \
    -drive if=pflash,format=raw,unit=1,file=./ovmf-vars.fd \
    -drive file="$DISK",format=qcow2,if=virtio \
    -drive file="$CLOUDINIT",format=raw,if=virtio \
    -netdev user,id=net0,hostfwd=tcp::${SSH_PORT}-:22 \
    -device virtio-net-pci,netdev=net0 \
    -nographic \
    $SEV_OPTS
