#!/bin/bash
# Run Plinko hint generation benchmark inside the SEV-SNP VM
# This script should be run INSIDE the VM after SSH-ing in

set -e

PLINKO_DIR="/mnt/plinko"
DB_PATH="$PLINKO_DIR/database.bin"
HINTS_BIN="$PLINKO_DIR/plinko_hints"

echo "=== Plinko PIR Hint Generation Benchmark (SEV-SNP) ==="
echo

# Check if we are in an SEV-SNP guest
echo "1. Checking SEV-SNP guest status..."
if [[ -d /sys/kernel/security/sev ]]; then
    echo "   SEV info available"
    cat /sys/kernel/security/sev/* 2>/dev/null || true
elif dmesg 2>/dev/null | grep -qi "SEV-SNP"; then
    echo "   Running in SEV-SNP guest"
    dmesg 2>/dev/null | grep -i sev | head -5 || true
else
    echo "   Warning: SEV-SNP status unclear (may need root to check dmesg)"
fi
echo

# Check attestation capability
echo "2. Checking attestation device..."
if [[ -c /dev/sev-guest ]]; then
    echo "   ✓ /dev/sev-guest available for attestation"
else
    echo "   ! /dev/sev-guest not found (attestation not available)"
fi
echo

# Check resources
echo "3. System resources:"
echo "   CPUs: $(nproc)"
echo "   RAM: $(free -h | awk '/Mem:/ {print $2}')"
echo "   Database: $(ls -lh $DB_PATH 2>/dev/null | awk '{print $5}' || echo 'NOT FOUND')"
echo

if [[ ! -f "$DB_PATH" ]]; then
    echo "Error: Database not found at $DB_PATH"
    echo "Copy it from host with:"
    echo "  scp -P 2222 /path/to/database.bin ubuntu@localhost:/mnt/plinko/"
    exit 1
fi

if [[ ! -f "$HINTS_BIN" ]]; then
    echo "Error: plinko_hints binary not found at $HINTS_BIN"
    echo "Copy it from host with:"
    echo "  scp -P 2222 /path/to/plinko_hints ubuntu@localhost:/mnt/plinko/"
    exit 1
fi

chmod +x "$HINTS_BIN"

# Run benchmark
THREADS=$(nproc)
LAMBDA=128

echo "4. Running benchmark..."
echo "   Lambda: $LAMBDA"
echo "   Threads: $THREADS"
echo "   Mode: Standard (per-hint BLAKE3)"
echo

time "$HINTS_BIN" \
    --db-path "$DB_PATH" \
    --lambda "$LAMBDA" \
    --threads "$THREADS"

echo
echo "=== Benchmark Complete ==="
echo
echo "Compare results with bare metal run to measure SEV-SNP overhead."
