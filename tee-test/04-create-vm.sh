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

# Use AMD's QEMU with SNP support if available
if [[ -x /mnt/mainnet/plinko/qemu-build/qemu/build/qemu-system-x86_64 ]]; then
    QEMU_BIN="/mnt/mainnet/plinko/qemu-build/qemu/build/qemu-system-x86_64"
    echo "Using AMD QEMU with SEV-SNP support"
else
    QEMU_BIN="qemu-system-x86_64"
    echo "Using system QEMU (may not support SEV-SNP)"
fi

# Find OVMF firmware
# For SNP, use AMD's patched OVMF
if [[ -f /mnt/mainnet/plinko/qemu-build/OVMF_CODE.fd ]]; then
    OVMF_CODE="/mnt/mainnet/plinko/qemu-build/OVMF_CODE.fd"
    OVMF_VARS="/mnt/mainnet/plinko/qemu-build/OVMF_VARS.fd"
elif [[ -f /usr/share/OVMF/OVMF_CODE_4M.fd ]]; then
    OVMF_CODE="/usr/share/OVMF/OVMF_CODE_4M.fd"
    OVMF_VARS="/usr/share/OVMF/OVMF_VARS_4M.fd"
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
# SEV mode selection: set SEV_MODE=sev, sev-es, or none (default: none for testing)
SEV_MODE="${SEV_MODE:-none}"

if [[ "$SEV_MODE" == "none" ]]; then
    echo "Running in regular KVM mode (no SEV) for baseline testing"
    echo "To enable SEV: SEV_MODE=sev ./04-create-vm.sh"
    SEV_OPTS=""
    MACHINE_OPTS="q35"
elif [[ ! -f /sys/module/kvm_amd/parameters/sev ]] || [[ $(cat /sys/module/kvm_amd/parameters/sev) != "Y" ]]; then
    echo "Warning: SEV not available, running in regular mode"
    SEV_OPTS=""
    MACHINE_OPTS="q35"
else
    echo "SEV mode: $SEV_MODE"
    # Check if we have the AMD QEMU with sev-snp-guest support
    if $QEMU_BIN -object help 2>&1 | grep -q sev-snp-guest; then
        echo "Using SEV-SNP (full memory encryption + integrity)"
        # sev-snp-guest requires: id, cbitpos, reduced-phys-bits
        # EPYC 9375F uses cbitpos=51
        # policy=0x30000 = default SNP policy (no migration, no debugging)
        SEV_OPTS="-object memory-backend-memfd,id=ram1,size=${MEMORY}M,share=true,prealloc=false -object sev-snp-guest,id=sev0,policy=0x30000,cbitpos=51,reduced-phys-bits=1"
        MACHINE_OPTS="q35,confidential-guest-support=sev0,memory-backend=ram1"
    else
        echo "Using SEV (basic memory encryption)"
        SEV_OPTS="-object sev-guest,id=sev0,sev-device=/dev/sev,cbitpos=51,reduced-phys-bits=1"
        MACHINE_OPTS="q35,confidential-guest-support=sev0"
    fi
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

# For SNP, use combined OVMF.fd with -bios
if [[ "$SEV_MODE" == "sev" ]] && $QEMU_BIN -object help 2>&1 | grep -q sev-snp-guest; then
    # Use the combined OVMF.fd for SNP
    SNP_OVMF="/mnt/mainnet/plinko/qemu-build/OVMF.fd"
    $QEMU_BIN \
        -enable-kvm \
        -cpu EPYC-v4 \
        -smp "$VCPUS" \
        -m "$MEMORY" \
        -machine $MACHINE_OPTS \
        -bios "$SNP_OVMF" \
        -drive file="$DISK",format=qcow2,if=virtio \
        -drive file="$CLOUDINIT",format=raw,if=virtio \
        -netdev user,id=net0,hostfwd=tcp::${SSH_PORT}-:22 \
        -device virtio-net-pci,netdev=net0 \
        -nographic \
        $SEV_OPTS
else
    $QEMU_BIN \
        -enable-kvm \
        -cpu EPYC-v4 \
        -smp "$VCPUS" \
        -m "$MEMORY" \
        -machine $MACHINE_OPTS \
        -drive if=pflash,format=raw,unit=0,file="$OVMF_CODE",readonly=on \
        -drive if=pflash,format=raw,unit=1,file=./ovmf-vars.fd \
        -drive file="$DISK",format=qcow2,if=virtio \
        -drive file="$CLOUDINIT",format=raw,if=virtio \
        -netdev user,id=net0,hostfwd=tcp::${SSH_PORT}-:22 \
        -device virtio-net-pci,netdev=net0 \
        -nographic \
        $SEV_OPTS
fi
