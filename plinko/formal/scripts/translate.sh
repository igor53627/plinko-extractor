#!/bin/bash
set -e

# Plinko Rust to Rocq Translation Script
# Uses rocq-of-rust (coq-of-rust) to translate Rust source files to Rocq/Coq

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PLINKO_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
OUTPUT_DIR="$SCRIPT_DIR/../translated"

# Files to translate
IPRF_SRC="$PLINKO_ROOT/src/iprf.rs"
HINTS_SRC="$PLINKO_ROOT/src/bin/plinko_hints.rs"

usage() {
    cat <<EOF
Usage: $(basename "$0") [OPTIONS]

Translate Plinko Rust sources to Rocq using rocq-of-rust (coq-of-rust).

OPTIONS:
    -h, --help      Show this help message
    -o, --output    Output directory (default: plinko/formal/translated/)
    -c, --clean     Clean output directory before translation

FILES TRANSLATED:
    - src/iprf.rs           SwapOrNot and Iprf implementations
    - src/bin/plinko_hints.rs   HintInit implementation

INSTALLATION:
    rocq-of-rust requires a specific nightly Rust toolchain.
    
    1. Install the required nightly toolchain:
        rustup toolchain install nightly-2024-12-07
    
    2. Install rocq-of-rust using that toolchain:
        cargo +nightly-2024-12-07 install coq-of-rust
    
    3. Run translation with the nightly toolchain:
        cargo +nightly-2024-12-07 rocq-of-rust

    For more information, see:
        https://github.com/formal-land/coq-of-rust

EOF
}

NIGHTLY_TOOLCHAIN="nightly-2024-12-07"

check_rocq_of_rust() {
    if ! cargo +$NIGHTLY_TOOLCHAIN rocq-of-rust --help >/dev/null 2>&1; then
        echo "[FAIL] rocq-of-rust is not installed or toolchain mismatch."
        echo ""
        echo "Installation instructions:"
        echo "  1. rustup toolchain install $NIGHTLY_TOOLCHAIN"
        echo "  2. cargo +$NIGHTLY_TOOLCHAIN install coq-of-rust"
        echo ""
        echo "For more information, see:"
        echo "  https://github.com/formal-land/coq-of-rust"
        exit 1
    fi
    echo "[OK] rocq-of-rust is installed with $NIGHTLY_TOOLCHAIN."
}

translate_file() {
    local src_file="$1"
    local output_name="$2"
    
    if [ ! -f "$src_file" ]; then
        echo "[FAIL] Source file not found: $src_file"
        return 1
    fi
    
    echo "[-->] Translating: $src_file"
    
    # Run rocq-of-rust translation
    # Note: rocq-of-rust operates on the crate level, we specify files via rustc
    cargo +$NIGHTLY_TOOLCHAIN rocq-of-rust "$src_file" > "$OUTPUT_DIR/${output_name}.v" 2>&1 || {
        echo "[WARN] Direct file translation failed, trying crate-level translation..."
        return 1
    }
    
    echo "[OK] Output: $OUTPUT_DIR/${output_name}.v"
}

translate_crate() {
    echo "[-->] Translating plinko crate to Rocq..."
    
    cd "$PLINKO_ROOT"
    
    # rocq-of-rust works at the crate level
    # It will generate .v files for the entire crate
    cargo +$NIGHTLY_TOOLCHAIN rocq-of-rust --output-path "$OUTPUT_DIR" || {
        echo "[WARN] Crate translation completed with warnings."
    }
    
    echo "[OK] Translation output in: $OUTPUT_DIR/"
}

# Parse arguments
CLEAN=0
while [[ $# -gt 0 ]]; do
    case $1 in
        -h|--help)
            usage
            exit 0
            ;;
        -o|--output)
            OUTPUT_DIR="$2"
            shift 2
            ;;
        -c|--clean)
            CLEAN=1
            shift
            ;;
        *)
            echo "[FAIL] Unknown option: $1"
            usage
            exit 1
            ;;
    esac
done

echo "=========================================="
echo "Plinko Rust to Rocq Translation"
echo "=========================================="
echo ""

# Check prerequisites
check_rocq_of_rust

# Clean if requested
if [ "$CLEAN" -eq 1 ] && [ -d "$OUTPUT_DIR" ]; then
    echo "[-->] Cleaning output directory: $OUTPUT_DIR"
    rm -rf "$OUTPUT_DIR"
fi

# Create output directory
mkdir -p "$OUTPUT_DIR"
echo "[OK] Output directory: $OUTPUT_DIR"
echo ""

# Translate the crate
translate_crate

echo ""
echo "=========================================="
echo "[OK] Translation complete!"
echo "=========================================="
echo ""
echo "Translated files should be in: $OUTPUT_DIR/"
echo ""
echo "Key files to review:"
echo "  - iprf.v        (SwapOrNot, Iprf implementations)"
echo "  - plinko_hints.v (HintInit implementation)"
echo ""
echo "Next steps:"
echo "  1. Review generated Rocq files for correctness"
echo "  2. Add to plinko/formal/specs/ or plinko/formal/proofs/"
echo "  3. Integrate with existing Coq specifications"
