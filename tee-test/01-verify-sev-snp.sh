#!/bin/bash
# Verify SEV-SNP is enabled after BIOS changes

set -e
echo "=== SEV-SNP Verification ==="
echo

echo "1. Checking dmesg for SEV/SNP..."
if dmesg | grep -i "SEV-SNP enabled" > /dev/null 2>&1; then
    echo "   ✓ SEV-SNP enabled in kernel"
    dmesg | grep -i sev | head -10
else
    echo "   ✗ SEV-SNP NOT enabled"
    echo "   dmesg output:"
    dmesg | grep -i sev
    echo
    echo "   If you see 'memory encryption not enabled by BIOS', check BIOS settings"
    exit 1
fi
echo

echo "2. Checking KVM AMD module parameters..."
SEV=$(cat /sys/module/kvm_amd/parameters/sev 2>/dev/null || echo "N")
SEV_SNP=$(cat /sys/module/kvm_amd/parameters/sev_snp 2>/dev/null || echo "N")

echo "   sev = $SEV"
echo "   sev_snp = $SEV_SNP"

if [[ "$SEV" == "Y" ]] && [[ "$SEV_SNP" == "Y" ]]; then
    echo "   ✓ KVM AMD SEV-SNP support enabled"
else
    echo "   ✗ KVM AMD parameters not set"
    echo "   Try: modprobe kvm_amd sev=1 sev_snp=1"
    exit 1
fi
echo

echo "3. Checking /dev/sev device..."
if [[ -c /dev/sev ]]; then
    echo "   ✓ /dev/sev exists"
    ls -la /dev/sev*
else
    echo "   ✗ /dev/sev not found"
    echo "   The sev-guest driver may need to be loaded"
fi
echo

echo "4. Checking CPU flags..."
if grep -q sev /proc/cpuinfo; then
    echo "   ✓ SEV CPU flag present"
    grep -m1 "flags" /proc/cpuinfo | tr " " "\n" | grep -E "sev|sme"
else
    echo "   ✗ SEV CPU flag not found"
fi
echo

echo "=== Verification Complete ==="
echo "If all checks passed, proceed with: ./02-install-packages.sh"
