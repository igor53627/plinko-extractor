#!/bin/bash
# Download Ubuntu 24.04 cloud image for SEV-SNP VM

set -e
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

IMAGE_URL="https://cloud-images.ubuntu.com/noble/current/noble-server-cloudimg-amd64.img"
IMAGE_FILE="ubuntu-24.04-cloudimg.qcow2"
IMAGE_ORIG="noble-server-cloudimg-amd64.img"
CHECKSUMS_URL="https://cloud-images.ubuntu.com/noble/current/SHA256SUMS"
DISK_FILE="vm-disk.qcow2"

echo "=== Downloading Ubuntu Cloud Image ==="
echo

if [[ -f "$IMAGE_FILE" ]]; then
    echo "Image already exists: $IMAGE_FILE"
else
    echo "Downloading from $IMAGE_URL..."
    wget -O "$IMAGE_FILE" "$IMAGE_URL"
    
    echo "Downloading checksums for verification..."
    wget -q -O SHA256SUMS "$CHECKSUMS_URL"
    
    # Extract expected checksum for the image
    EXPECTED_SUM=$(grep "$IMAGE_ORIG" SHA256SUMS | awk '{print $1}')
    ACTUAL_SUM=$(sha256sum "$IMAGE_FILE" | awk '{print $1}')
    
    if [[ "$EXPECTED_SUM" != "$ACTUAL_SUM" ]]; then
        echo "Error: Image checksum verification failed!"
        echo "  Expected: $EXPECTED_SUM"
        echo "  Actual:   $ACTUAL_SUM"
        rm -f "$IMAGE_FILE"
        exit 1
    fi
    echo "✓ Image checksum verified"
    rm -f SHA256SUMS
fi

echo
echo "Creating VM disk (200GB, copy-on-write)..."
qemu-img create -f qcow2 -F qcow2 -b "$IMAGE_FILE" "$DISK_FILE" 200G

echo
echo "Creating cloud-init config..."
cat > cloud-init-user-data << 'CLOUDINIT'
#cloud-config
hostname: plinko-sev
users:
  - name: ubuntu
    sudo: ALL=(ALL) NOPASSWD:ALL
    shell: /bin/bash
    ssh_authorized_keys:
      - SSH_KEY_PLACEHOLDER
packages:
  - htop
  - rsync
runcmd:
  - mkdir -p /mnt/plinko
  - echo "SEV-SNP VM ready for Plinko testing" > /mnt/plinko/ready.txt
CLOUDINIT

# Get the host SSH key
if [[ -f ~/.ssh/id_rsa.pub ]]; then
    SSH_KEY=$(cat ~/.ssh/id_rsa.pub)
elif [[ -f ~/.ssh/id_ed25519.pub ]]; then
    SSH_KEY=$(cat ~/.ssh/id_ed25519.pub)
else
    echo "Warning: No SSH key found, generating one..."
    ssh-keygen -t ed25519 -f ~/.ssh/id_ed25519 -N ""
    SSH_KEY=$(cat ~/.ssh/id_ed25519.pub)
fi

# Update cloud-init with actual SSH key
sed -i "s|SSH_KEY_PLACEHOLDER|$SSH_KEY|" cloud-init-user-data

cat > cloud-init-meta-data << 'META'
instance-id: plinko-sev-1
local-hostname: plinko-sev
META

echo
echo "Creating cloud-init ISO..."
cloud-localds cloud-init.iso cloud-init-user-data cloud-init-meta-data

echo
echo "=== Image Setup Complete ==="
ls -lh "$IMAGE_FILE" "$DISK_FILE" cloud-init.iso
echo
echo "Proceed with: ./04-create-vm.sh"
