#!/bin/bash
# Install QEMU and dependencies for SEV-SNP

set -e
echo "=== Installing SEV-SNP packages ==="
echo

apt-get update

echo "1. Installing QEMU with SEV support..."
apt-get install -y \
    qemu-system-x86 \
    qemu-utils \
    ovmf \
    cloud-image-utils \
    libvirt-daemon-system \
    libvirt-clients \
    virtinst \
    swtpm \
    swtpm-tools

echo
echo "2. Checking QEMU version..."
qemu-system-x86_64 --version

echo
echo "3. Checking OVMF paths..."
ls -la /usr/share/OVMF/ 2>/dev/null || ls -la /usr/share/edk2/ovmf/ 2>/dev/null || echo "OVMF location may vary"

echo
echo "4. Enabling libvirtd..."
systemctl enable --now libvirtd || true

echo
echo "=== Installation Complete ==="
echo "Proceed with: ./03-download-image.sh"
