//! Plinko PIR Hint Generator - iPRF Implementation (Paper-compliant)
//!
//! Implements Plinko's HintInit matching Fig. 7 of the paper and Plinko.v Coq spec.
//!
//! # Key Design (per paper and Coq formalization)
//!
//! - Generates c iPRF keys (one per block), not one global key
//! - Regular hints: block subset of size c/2+1, single parity
//! - Backup hints: block subset of size c/2, dual parities (in/out)
//! - iPRF domain = total hints (λw + q), range = w (block size)
//!
//! # Constant-Time Mode (--constant-time)
//!
//! For TEE execution, this generator supports a constant-time path that eliminates
//! timing side-channels which could leak iPRF mappings. Security properties:
//!
//! - **Fixed-bound loops**: Always iterates `MAX_PREIMAGES` (512) times per entry,
//!   using masks to skip invalid indices. This prevents leaking preimage counts.
//!
//! - **Branchless membership**: Uses `BlockBitset::contains_ct()` for O(1) bit lookup
//!   instead of binary search, preventing timing variation based on subset contents.
//!
//! - **Masked XOR**: Uses `ct_xor_32_masked()` to conditionally XOR without branches,
//!   ensuring constant-time parity updates.
//!
//! ## Security Model and Limitations
//!
//! The CT mode protects against timing side-channels but does NOT provide full
//! memory-access obliviousness. Array indexing patterns (e.g., `regular_bitsets[j]`)
//! may leak information to cache side-channel attackers (Prime+Probe, etc.).
//!
//! This is acceptable for the paper's security model, which reasons in an idealized
//! RAM model without microarchitectural side-channels. For stronger protection,
//! an ORAM-based approach would be needed (O(n) overhead).
//!
//! ## MAX_PREIMAGES Bound
//!
//! With default parameters (λ=128, q=λw), expected preimages per offset ≈ 2λ = 256.
//! The bound MAX_PREIMAGES=512 (≈2μ) ensures truncation probability < 2^{-140}
//! via Chernoff bounds. A parameter guard enforces this at runtime.

use clap::Parser;
use indicatif::{ProgressBar, ProgressStyle};
use memmap2::MmapOptions;
use rand::{RngCore, SeedableRng};
use rand_chacha::ChaCha20Rng;
use sha2::{Digest, Sha256};
use state_syncer::constant_time::{ct_lt_u64, ct_select_usize, ct_xor_32_masked};
use state_syncer::iprf::{Iprf, IprfTee, PrfKey128, MAX_PREIMAGES};
use std::fs::File;
use std::path::PathBuf;
use std::time::Instant;

const WORD_SIZE: usize = 32;
const SEED_SIZE: usize = 32;

const SEED_LABEL_REGULAR: &[u8] = b"plinko_regular_subset";
const SEED_LABEL_BACKUP: &[u8] = b"plinko_backup_subset";

#[derive(Parser, Debug)]
#[command(author, version, about = "Plinko PIR Hint Generator (Paper-compliant)", long_about = None)]
struct Args {
    /// Path to the database file
    #[arg(short, long, default_value = "/mnt/plinko/data/database.bin")]
    db_path: PathBuf,

    /// Security parameter lambda (regular hints = lambda * w)
    #[arg(short, long, default_value = "128")]
    lambda: usize,

    /// Number of backup hints (q). Default: lambda * w
    #[arg(short, long)]
    backup_hints: Option<usize>,

    /// Override entries per block (w). Default: round(sqrt(N)); DB is padded as needed.
    #[arg(short, long)]
    entries_per_block: Option<usize>,

    /// [DEBUG ONLY] Allow truncation instead of padding (violates security assumptions)
    #[arg(long, default_value = "false", hide = true)]
    allow_truncation: bool,

    /// Master seed for reproducible hint generation (hex, 32 bytes).
    /// If not provided, a random seed is generated from OS entropy.
    #[arg(long)]
    seed: Option<String>,

    /// Print the master seed (for reproducibility). Use with caution in production.
    #[arg(long)]
    print_seed: bool,

    /// Use constant-time implementation for TEE execution.
    /// Slower but prevents timing side-channels that could leak iPRF mappings.
    #[arg(long)]
    constant_time: bool,
}

/// Regular hint: P_j subset of c/2+1 blocks, single parity
/// Stores seed instead of explicit block list for compact representation
struct RegularHint {
    subset_seed: [u8; 32],
    parity: [u8; 32],
}

/// Backup hint: B_j subset of c/2 blocks, dual parities
/// Stores seed instead of explicit block list for compact representation
struct BackupHint {
    subset_seed: [u8; 32],
    parity_in: [u8; 32],
    parity_out: [u8; 32],
}

fn xor_32(dst: &mut [u8; 32], src: &[u8; 32]) {
    for i in 0..32 {
        dst[i] ^= src[i];
    }
}

/// Bitset for constant-time block membership testing.
///
/// Converts sorted block lists to a compact bit array for O(1) membership queries.
/// This is functionally equivalent to binary search on sorted `Vec<usize>`, but:
///
/// 1. **Constant-time**: `contains_ct()` performs fixed bit arithmetic regardless
///    of subset contents, preventing timing leaks in TEE execution.
///
/// 2. **Cache-efficient**: Single u64 load + shift vs. multiple comparisons.
///
/// # Security Note
///
/// The array index `block / 64` depends on the public block index (known from
/// the streaming loop), so `contains_ct` does not leak secret information via
/// its memory access pattern. The secret is "which hints map to this offset",
/// not "which block we're processing".
struct BlockBitset {
    bits: Vec<u64>,
    num_blocks: usize,
}

impl BlockBitset {
    fn new(num_blocks: usize) -> Self {
        let num_words = (num_blocks + 63) / 64;
        Self {
            bits: vec![0u64; num_words],
            num_blocks,
        }
    }

    fn from_sorted_blocks(blocks: &[usize], num_blocks: usize) -> Self {
        let mut bitset = Self::new(num_blocks);
        for &block in blocks {
            if block < num_blocks {
                bitset.bits[block / 64] |= 1u64 << (block % 64);
            }
        }
        bitset
    }

    /// Constant-time membership test: returns 1 if block is in set, 0 otherwise.
    ///
    /// The early return for out-of-bounds `block` is NOT a timing leak because
    /// `block` is derived from the public streaming index `i` (block = i / w).
    /// The secret values are the iPRF preimage indices, not the block index.
    #[inline]
    fn contains_ct(&self, block: usize) -> u64 {
        if block >= self.num_blocks {
            return 0;
        }
        let word_idx = block / 64;
        let bit_idx = block % 64;
        (self.bits[word_idx] >> bit_idx) & 1
    }
}

/// Derive a per-hint subset seed from master seed and hint index
fn derive_subset_seed(master_seed: &[u8; 32], label: &[u8], idx: u64) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(master_seed);
    hasher.update(label);
    hasher.update(&idx.to_le_bytes());
    let hash = hasher.finalize();
    let mut seed = [0u8; 32];
    seed.copy_from_slice(&hash[0..32]);
    seed
}

/// Compute regular hint block subset from seed
fn compute_regular_blocks(seed: &[u8; 32], c: usize) -> Vec<usize> {
    let regular_subset_size = c / 2 + 1;
    let mut rng = ChaCha20Rng::from_seed(*seed);
    let mut blocks = random_subset(&mut rng, regular_subset_size, c);
    blocks.sort_unstable();
    blocks
}

/// Compute backup hint block subset from seed
fn compute_backup_blocks(seed: &[u8; 32], c: usize) -> Vec<usize> {
    let backup_subset_size = c / 2;
    let mut rng = ChaCha20Rng::from_seed(*seed);
    let mut blocks = random_subset(&mut rng, backup_subset_size, c);
    blocks.sort_unstable();
    blocks
}

/// Derive c iPRF keys from master seed (one per block)
fn derive_block_keys(master_seed: &[u8; 32], c: usize) -> Vec<PrfKey128> {
    let mut keys = Vec::with_capacity(c);
    for block_idx in 0..c {
        let mut hasher = Sha256::new();
        hasher.update(master_seed);
        hasher.update(b"block_key");
        hasher.update(&(block_idx as u64).to_le_bytes());
        let hash = hasher.finalize();
        let mut key = [0u8; 16];
        key.copy_from_slice(&hash[0..16]);
        keys.push(key);
    }
    keys
}

/// Generate a random subset of `size` distinct elements from [0, total)
fn random_subset(rng: &mut ChaCha20Rng, size: usize, total: usize) -> Vec<usize> {
    use rand::seq::index::sample;
    sample(rng, total, size).into_vec()
}

/// Check if block is in the subset (sorted for binary search)
fn block_in_subset(blocks: &[usize], block: usize) -> bool {
    blocks.binary_search(&block).is_ok()
}

fn main() -> eyre::Result<()> {
    let args = Args::parse();

    if args.lambda == 0 {
        eprintln!("Error: lambda must be >= 1");
        std::process::exit(1);
    }

    println!("Plinko PIR Hint Generator (Paper-compliant)");
    println!("============================================");
    println!("Database: {:?}", args.db_path);

    let file = File::open(&args.db_path)?;
    let file_len = file.metadata()?.len() as usize;
    println!(
        "DB Size: {:.2} GB",
        file_len as f64 / 1024.0 / 1024.0 / 1024.0
    );

    let mmap = unsafe { MmapOptions::new().map(&file)? };
    let db_bytes: &[u8] = &mmap;

    assert_eq!(
        db_bytes.len() % WORD_SIZE,
        0,
        "DB size must be multiple of 32 bytes"
    );
    let n_entries = db_bytes.len() / WORD_SIZE;
    if n_entries == 0 {
        eprintln!("Error: Database must contain at least one entry");
        std::process::exit(1);
    }
    println!("Total Entries (N): {}", n_entries);

    // Default w = round(sqrt(N)), no divisor search - pad instead
    let default_w = (n_entries as f64).sqrt().round() as usize;
    let w = args.entries_per_block.unwrap_or(default_w);
    if w == 0 {
        eprintln!("Error: entries_per_block (w) must be > 0");
        std::process::exit(1);
    }

    // Compute padding to make n_entries a multiple of w (pad with dummy zero entries)
    let remainder = n_entries % w;
    let (logical_n_entries, pad_entries) = if remainder == 0 {
        (n_entries, 0usize)
    } else {
        let pad = w - remainder;
        (n_entries + pad, pad)
    };

    if pad_entries > 0 {
        if args.allow_truncation {
            // Legacy behavior: truncate instead of padding
            println!(
                "Warning: N ({}) not divisible by w ({}), {} tail entries will be ignored (truncation mode)",
                n_entries, w, remainder
            );
        } else {
            println!(
                "Info: N ({}) not divisible by w ({}); padding with {} dummy entries.",
                n_entries, w, pad_entries
            );
        }
    }

    // Use logical_n_entries (after padding) unless truncation mode (debug only)
    let (mut n_effective, mut pad_entries) = if args.allow_truncation && remainder != 0 {
        eprintln!(
            "Warning: --allow-truncation is a debug flag that violates security assumptions."
        );
        (n_entries - remainder, 0usize)
    } else {
        (logical_n_entries, pad_entries)
    };
    let mut c = n_effective / w;

    // Enforce c >= 2
    if c < 2 {
        eprintln!(
            "Error: Number of blocks (c = {}) must be at least 2 for Plinko security.",
            c
        );
        eprintln!("       Decrease --entries-per-block or increase DB size.");
        std::process::exit(1);
    }

    // Auto-bump c to even if odd (required for security proof)
    // Skip in truncation mode (debug only, explicitly violates security)
    if !args.allow_truncation && c % 2 != 0 {
        c += 1;
        n_effective = c * w;
        pad_entries = n_effective - n_entries;
        println!(
            "Info: Bumped c from {} to {} (must be even for security). Padding with {} entries.",
            c - 1,
            c,
            pad_entries
        );
    } else if args.allow_truncation && c % 2 != 0 {
        eprintln!(
            "Warning: --allow-truncation mode with odd c = {} further violates security assumptions.",
            c
        );
    }

    println!("\nPlinko Parameters:");
    println!("  Physical entries (from DB): {}", n_entries);
    println!(
        "  Logical entries (after {}): {}",
        if args.allow_truncation && n_effective < n_entries {
            "truncation"
        } else {
            "padding"
        },
        n_effective
    );
    if pad_entries > 0 {
        println!("  Padded entries: {}", pad_entries);
    }
    println!("  Entries per block (w): {}", w);
    println!("  Number of blocks (c): {}", c);
    println!(
        "  Block size: {:.2} MB",
        (w * WORD_SIZE) as f64 / 1024.0 / 1024.0
    );
    println!("  Lambda: {}", args.lambda);

    let num_regular = args.lambda * w;
    let num_backup = args.backup_hints.unwrap_or(num_regular);
    let total_hints = num_regular + num_backup;

    if total_hints == 0 {
        eprintln!("Error: total hints must be > 0");
        std::process::exit(1);
    }

    // Final assertion: c must be even (should always pass after auto-bump in production mode)
    if !args.allow_truncation {
        assert!(
            c % 2 == 0,
            "Invariant violation: number of blocks (c = {}) must be even for security.",
            c
        );
    }

    let regular_subset_size = c / 2 + 1;
    let backup_subset_size = c / 2;

    if regular_subset_size > c || backup_subset_size > c {
        eprintln!("Error: subset sizes exceed number of blocks");
        std::process::exit(1);
    }

    println!("\nHint Structure (per paper Fig. 7):");
    println!("  Regular hints (lambda*w): {}", num_regular);
    println!("  Backup hints (q): {}", num_backup);
    println!("  Total hints: {}", total_hints);
    println!("  Regular subset size (c/2+1): {}", regular_subset_size);
    println!("  Backup subset size (c/2): {}", backup_subset_size);

    // Storage: each hint stores only a 32-byte seed + parities (not full block list)
    let regular_storage = num_regular * (SEED_SIZE + WORD_SIZE);
    let backup_storage = num_backup * (SEED_SIZE + 2 * WORD_SIZE);
    println!(
        "  Estimated hint storage: {:.2} MB (seed-based, compact)",
        (regular_storage + backup_storage) as f64 / 1024.0 / 1024.0
    );

    // Generate or parse master seed
    let master_seed: [u8; 32] = if let Some(ref hex_seed) = args.seed {
        // Parse hex seed from CLI
        let hex_clean = hex_seed.strip_prefix("0x").unwrap_or(hex_seed);
        if hex_clean.len() != 64 {
            eprintln!("Error: --seed must be exactly 32 bytes (64 hex chars)");
            std::process::exit(1);
        }
        let mut seed = [0u8; 32];
        for (i, chunk) in hex_clean.as_bytes().chunks(2).enumerate() {
            let hex_str = std::str::from_utf8(chunk).unwrap();
            seed[i] = u8::from_str_radix(hex_str, 16).unwrap_or_else(|_| {
                eprintln!("Error: invalid hex in --seed at position {}", i * 2);
                std::process::exit(1);
            });
        }
        if args.print_seed {
            println!("Using provided seed: 0x{}", hex_clean);
        }
        seed
    } else {
        // Generate random seed from OS entropy (CSPRNG)
        let mut seed = [0u8; 32];
        rand::thread_rng().fill_bytes(&mut seed);
        if args.print_seed {
            println!(
                "Generated random seed: 0x{}",
                seed.iter()
                    .map(|b| format!("{:02x}", b))
                    .collect::<String>()
            );
            println!("  (use --seed to reproduce this run)");
        }
        seed
    };

    let start = Instant::now();

    // Step 1: Generate c iPRF keys (one per block)
    println!("\n[1/4] Generating {} iPRF keys (one per block)...", c);
    let block_keys = derive_block_keys(&master_seed, c);

    // Step 2: Initialize regular hints with seed-based block subsets
    println!(
        "[2/4] Initializing {} regular hints (subset size {})...",
        num_regular, regular_subset_size
    );
    let mut regular_hints: Vec<RegularHint> = Vec::with_capacity(num_regular);
    let mut regular_hint_blocks: Vec<Vec<usize>> = Vec::with_capacity(num_regular);

    for j in 0..num_regular {
        let subset_seed = derive_subset_seed(&master_seed, SEED_LABEL_REGULAR, j as u64);
        let blocks = compute_regular_blocks(&subset_seed, c);

        regular_hints.push(RegularHint {
            subset_seed,
            parity: [0u8; 32],
        });
        regular_hint_blocks.push(blocks);
    }

    // Step 3: Initialize backup hints with seed-based block subsets
    println!(
        "[3/4] Initializing {} backup hints (subset size {})...",
        num_backup, backup_subset_size
    );
    let mut backup_hints: Vec<BackupHint> = Vec::with_capacity(num_backup);
    let mut backup_hint_blocks: Vec<Vec<usize>> = Vec::with_capacity(num_backup);

    for j in 0..num_backup {
        let subset_seed = derive_subset_seed(&master_seed, SEED_LABEL_BACKUP, j as u64);
        let blocks = compute_backup_blocks(&subset_seed, c);

        backup_hints.push(BackupHint {
            subset_seed,
            parity_in: [0u8; 32],
            parity_out: [0u8; 32],
        });
        backup_hint_blocks.push(blocks);
    }

    // Step 4: Stream database and update parities
    println!("[4/4] Streaming database ({} entries)...", n_effective);
    if args.constant_time {
        println!("  [CT MODE] Using constant-time implementation for TEE");
    }
    let pb = ProgressBar::new(n_effective as u64);
    pb.set_style(
        ProgressStyle::default_bar()
            .template("{spinner:.green} [{elapsed_precise}] [{bar:40.cyan/blue}] {pos}/{len} entries ({eta})")
            .unwrap()
            .progress_chars("#>-"),
    );

    if args.constant_time {
        // =========================================================================
        // CONSTANT-TIME PATH FOR TEE EXECUTION
        // =========================================================================
        //
        // Security goal: Eliminate timing side-channels that could leak the iPRF
        // mapping (i.e., which hints contain which database entries).
        //
        // This is critical because in Plinko, the hint structure encodes which
        // database entries a client can privately retrieve. Leaking this structure
        // would compromise PIR privacy.
        //
        // Key techniques used:
        // 1. Fixed-bound loops (MAX_PREIMAGES iterations, not data-dependent count)
        // 2. BlockBitset for O(1) branchless membership testing
        // 3. ct_select_usize for branchless index clamping
        // 4. ct_xor_32_masked for conditional XOR without branches
        //
        // What we do NOT protect against (and why it's acceptable):
        // - Cache side-channels from secret-dependent array indices
        //   (would require ORAM, O(n) overhead; out of scope for paper's model)
        // =========================================================================

        // Guard: CT path requires non-empty hint arrays for safe array indexing.
        // ct_select_usize(0, _, default) returns default, but we still index into
        // the bitset/hint arrays, so they must have at least one element.
        if num_regular == 0 {
            eprintln!("Error: --constant-time mode requires num_regular > 0 (lambda >= 1)");
            std::process::exit(1);
        }
        if num_backup == 0 {
            eprintln!("Error: --constant-time mode requires num_backup > 0");
            eprintln!("       Use --backup-hints to set q > 0");
            std::process::exit(1);
        }

        // Guard: Ensure MAX_PREIMAGES is sufficient for the parameter configuration.
        //
        // For Plinko with (λ, w, q), expected preimages per offset ≈ (λw + q) / w.
        // With default q = λw: expected ≈ 2λ = 256 for λ=128.
        //
        // We require expected * 2 <= MAX_PREIMAGES to ensure truncation probability
        // is negligible (< 2^{-100}) via Chernoff bounds.
        let expected_preimages = (total_hints + w - 1) / w;
        if expected_preimages * 2 > MAX_PREIMAGES {
            eprintln!("Error: Parameter configuration too dense for constant-time mode.");
            eprintln!(
                "       Expected preimages per offset ({}) exceeds MAX_PREIMAGES/2 ({}).",
                expected_preimages,
                MAX_PREIMAGES / 2
            );
            eprintln!("       Reduce total_hints or increase w.");
            std::process::exit(1);
        }

        // Pre-create CT iPRF instances
        let block_iprfs_ct: Vec<IprfTee> = block_keys
            .iter()
            .map(|key| IprfTee::new(*key, total_hints as u64, w as u64))
            .collect();

        // Convert block lists to bitsets for CT membership testing
        let regular_bitsets: Vec<BlockBitset> = regular_hint_blocks
            .iter()
            .map(|blocks| BlockBitset::from_sorted_blocks(blocks, c))
            .collect();
        let backup_bitsets: Vec<BlockBitset> = backup_hint_blocks
            .iter()
            .map(|blocks| BlockBitset::from_sorted_blocks(blocks, c))
            .collect();

        // Drop the Vec<Vec<usize>> now that we have bitsets
        drop(regular_hint_blocks);
        drop(backup_hint_blocks);

        for i in 0..n_effective {
            let block = i / w;
            let offset = i % w;

            let entry: [u8; 32] = if i < n_entries {
                let entry_offset = i * WORD_SIZE;
                db_bytes[entry_offset..entry_offset + WORD_SIZE]
                    .try_into()
                    .unwrap()
            } else {
                [0u8; 32]
            };

            // CT inverse returns fixed-size array + count
            let (indices, count) = block_iprfs_ct[block].inverse_ct(offset as u64);

            // Fixed-bound loop: always iterates MAX_PREIMAGES times regardless of
            // actual preimage count. This prevents timing leaks from variable iteration.
            //
            // The in_range mask filters out invalid indices (t >= count), ensuring
            // the XOR operation has no effect for padding iterations.
            for t in 0..MAX_PREIMAGES {
                // in_range = 1 if this is a valid preimage (t < count), 0 otherwise.
                // All operations below are masked by this value.
                let in_range = ct_lt_u64(t as u64, count as u64);

                let j = indices[t] as usize;

                // Branchless classification: is j a regular hint index or backup?
                // Paper Fig. 7: regular hints are j < λw, backup hints are j >= λw.
                let is_regular = ct_lt_u64(j as u64, num_regular as u64);
                let backup_idx = j.wrapping_sub(num_regular);
                let is_valid_backup = ct_lt_u64(backup_idx as u64, num_backup as u64);
                let is_backup = (1 - is_regular) & is_valid_backup;

                // Branchless index clamping for array access:
                //
                // Problem: We need to access regular_bitsets[j] or backup_bitsets[backup_idx],
                // but if j is invalid for that array, we'd get out-of-bounds.
                //
                // Solution: ct_select_usize returns j if valid, 0 (dummy) otherwise.
                // The dummy access still happens (cache side-channel), but:
                // - The XOR mask will be 0, so no actual parity update occurs
                // - The timing is constant (same instructions execute either way)
                let regular_idx = ct_select_usize(is_regular, j, 0);
                let in_regular_subset = regular_bitsets[regular_idx].contains_ct(block);

                let backup_idx_clamped = ct_select_usize(is_valid_backup, backup_idx, 0);
                let in_backup_subset = backup_bitsets[backup_idx_clamped].contains_ct(block);

                // Final update masks: all conditions must be true (in_range AND correct type AND in subset)
                // These correspond exactly to the paper's HintInit update rules:
                // - Regular: j < λw AND α ∈ P_j  =>  H[j].parity ^= d
                // - Backup in: j >= λw AND α ∈ B_j  =>  T[j].p1 ^= d
                // - Backup out: j >= λw AND α ∉ B_j  =>  T[j].p2 ^= d
                let update_regular = in_range & is_regular & in_regular_subset;
                let update_backup_in = in_range & is_backup & in_backup_subset;
                let update_backup_out = in_range & is_backup & (1 - in_backup_subset);

                // Masked XOR: if mask == 1, dst ^= src; if mask == 0, no-op.
                // Both paths execute the same instructions (constant time).
                ct_xor_32_masked(
                    &mut regular_hints[regular_idx].parity,
                    &entry,
                    update_regular,
                );
                ct_xor_32_masked(
                    &mut backup_hints[backup_idx_clamped].parity_in,
                    &entry,
                    update_backup_in,
                );
                ct_xor_32_masked(
                    &mut backup_hints[backup_idx_clamped].parity_out,
                    &entry,
                    update_backup_out,
                );
            }

            if i % 10000 == 0 {
                pb.set_position(i as u64);
            }
        }
    } else {
        // Fast path (non-constant-time) for client-side execution
        let block_iprfs: Vec<Iprf> = block_keys
            .iter()
            .map(|key| Iprf::new(*key, total_hints as u64, w as u64))
            .collect();

        for i in 0..n_effective {
            let block = i / w;
            let offset = i % w;

            let entry: [u8; 32] = if i < n_entries {
                let entry_offset = i * WORD_SIZE;
                db_bytes[entry_offset..entry_offset + WORD_SIZE]
                    .try_into()
                    .unwrap()
            } else {
                [0u8; 32]
            };

            // Find all hints j where iPRF.forward(j) == offset
            let hint_indices = block_iprfs[block].inverse(offset as u64);

            for j in hint_indices {
                let j = j as usize;
                if j < num_regular {
                    // Regular hint: XOR if block in P
                    if block_in_subset(&regular_hint_blocks[j], block) {
                        xor_32(&mut regular_hints[j].parity, &entry);
                    }
                } else {
                    // Backup hint: XOR to parity_in if in P, else parity_out
                    let backup_idx = j - num_regular;
                    if backup_idx < num_backup {
                        if block_in_subset(&backup_hint_blocks[backup_idx], block) {
                            xor_32(&mut backup_hints[backup_idx].parity_in, &entry);
                        } else {
                            xor_32(&mut backup_hints[backup_idx].parity_out, &entry);
                        }
                    }
                }
            }

            if i % 10000 == 0 {
                pb.set_position(i as u64);
            }
        }

        // Drop in-memory block lists now that streaming is complete
        drop(regular_hint_blocks);
        drop(backup_hint_blocks);
    }

    pb.finish_with_message("Done");

    let duration = start.elapsed();
    let throughput_mb = (file_len as f64 / 1024.0 / 1024.0) / duration.as_secs_f64();

    println!("\n=== Results ===");
    println!("Time Taken: {:.2?}", duration);
    println!("Throughput: {:.2} MB/s", throughput_mb);

    let non_zero_regular = regular_hints
        .iter()
        .filter(|h| h.parity.iter().any(|&b| b != 0))
        .count();
    let non_zero_backup_in = backup_hints
        .iter()
        .filter(|h| h.parity_in.iter().any(|&b| b != 0))
        .count();
    let non_zero_backup_out = backup_hints
        .iter()
        .filter(|h| h.parity_out.iter().any(|&b| b != 0))
        .count();

    println!(
        "\nRegular hints with non-zero parity: {} / {} ({:.1}%)",
        non_zero_regular,
        num_regular,
        100.0 * non_zero_regular as f64 / num_regular as f64
    );
    if num_backup > 0 {
        println!(
            "Backup hints with non-zero parity_in: {} / {} ({:.1}%)",
            non_zero_backup_in,
            num_backup,
            100.0 * non_zero_backup_in as f64 / num_backup as f64
        );
        println!(
            "Backup hints with non-zero parity_out: {} / {} ({:.1}%)",
            non_zero_backup_out,
            num_backup,
            100.0 * non_zero_backup_out as f64 / num_backup as f64
        );
    }

    // Verify iPRF coverage: sum of |inverse(offset)| over all offsets should equal domain (total_hints)
    let blocks_to_check = c.min(10);
    println!(
        "\nSampling iPRF coverage (first {} blocks)...",
        blocks_to_check
    );
    let mut total_preimages = 0usize;
    for block in 0..blocks_to_check {
        let verify_iprf = Iprf::new(block_keys[block], total_hints as u64, w as u64);
        for offset in 0..w {
            total_preimages += verify_iprf.inverse(offset as u64).len();
        }
    }
    let blocks_checked = blocks_to_check;
    let expected_per_block = total_hints;
    println!(
        "  First {} blocks: {} total preimages across {} offsets (expected {} per block = {})",
        blocks_checked,
        total_preimages,
        w,
        expected_per_block,
        blocks_checked * expected_per_block
    );

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_derive_block_keys_deterministic() {
        let seed = [0u8; 32];
        let keys1 = derive_block_keys(&seed, 10);
        let keys2 = derive_block_keys(&seed, 10);
        assert_eq!(keys1, keys2);
    }

    #[test]
    fn test_derive_block_keys_unique() {
        let seed = [1u8; 32];
        let keys = derive_block_keys(&seed, 100);
        for i in 0..keys.len() {
            for j in (i + 1)..keys.len() {
                assert_ne!(keys[i], keys[j], "Keys {} and {} should differ", i, j);
            }
        }
    }

    #[test]
    fn test_random_subset_size() {
        let mut rng = ChaCha20Rng::from_seed([2u8; 32]);
        let subset = random_subset(&mut rng, 5, 10);
        assert_eq!(subset.len(), 5);
    }

    #[test]
    fn test_random_subset_bounds() {
        let mut rng = ChaCha20Rng::from_seed([3u8; 32]);
        let subset = random_subset(&mut rng, 10, 100);
        for &x in &subset {
            assert!(x < 100);
        }
    }

    #[test]
    fn test_random_subset_unique() {
        let mut rng = ChaCha20Rng::from_seed([4u8; 32]);
        let subset = random_subset(&mut rng, 20, 100);
        let mut sorted = subset.clone();
        sorted.sort_unstable();
        sorted.dedup();
        assert_eq!(
            sorted.len(),
            subset.len(),
            "subset should have no duplicates"
        );
    }

    #[test]
    fn test_block_in_subset() {
        let blocks = vec![1, 3, 5, 7, 9];
        assert!(block_in_subset(&blocks, 5));
        assert!(!block_in_subset(&blocks, 6));
        assert!(block_in_subset(&blocks, 1));
        assert!(!block_in_subset(&blocks, 0));
    }

    #[test]
    fn test_xor_32_identity() {
        let mut a = [0xABu8; 32];
        let b = [0u8; 32];
        let original = a;
        xor_32(&mut a, &b);
        assert_eq!(a, original);
    }

    #[test]
    fn test_xor_32_inverse() {
        let mut a = [0x12u8; 32];
        let b = [0x34u8; 32];
        let original = a;
        xor_32(&mut a, &b);
        xor_32(&mut a, &b);
        assert_eq!(a, original);
    }

    #[test]
    fn test_derive_subset_seed_deterministic() {
        let master = [5u8; 32];
        let seed1 = derive_subset_seed(&master, SEED_LABEL_REGULAR, 42);
        let seed2 = derive_subset_seed(&master, SEED_LABEL_REGULAR, 42);
        assert_eq!(seed1, seed2);
    }

    #[test]
    fn test_derive_subset_seed_unique_per_index() {
        let master = [6u8; 32];
        let seed1 = derive_subset_seed(&master, SEED_LABEL_REGULAR, 0);
        let seed2 = derive_subset_seed(&master, SEED_LABEL_REGULAR, 1);
        assert_ne!(seed1, seed2);
    }

    #[test]
    fn test_derive_subset_seed_unique_per_label() {
        let master = [7u8; 32];
        let seed1 = derive_subset_seed(&master, SEED_LABEL_REGULAR, 0);
        let seed2 = derive_subset_seed(&master, SEED_LABEL_BACKUP, 0);
        assert_ne!(seed1, seed2);
    }

    #[test]
    fn test_compute_regular_blocks_size() {
        let seed = [8u8; 32];
        let c = 100;
        let blocks = compute_regular_blocks(&seed, c);
        assert_eq!(blocks.len(), c / 2 + 1);
    }

    #[test]
    fn test_compute_backup_blocks_size() {
        let seed = [9u8; 32];
        let c = 100;
        let blocks = compute_backup_blocks(&seed, c);
        assert_eq!(blocks.len(), c / 2);
    }

    #[test]
    fn test_compute_blocks_deterministic() {
        let seed = [10u8; 32];
        let c = 50;
        let blocks1 = compute_regular_blocks(&seed, c);
        let blocks2 = compute_regular_blocks(&seed, c);
        assert_eq!(blocks1, blocks2);
    }

    #[test]
    fn test_bitset_membership() {
        let blocks = vec![1, 3, 5, 7, 9];
        let bitset = BlockBitset::from_sorted_blocks(&blocks, 10);
        assert_eq!(bitset.contains_ct(0), 0);
        assert_eq!(bitset.contains_ct(1), 1);
        assert_eq!(bitset.contains_ct(2), 0);
        assert_eq!(bitset.contains_ct(3), 1);
        assert_eq!(bitset.contains_ct(5), 1);
        assert_eq!(bitset.contains_ct(9), 1);
        assert_eq!(bitset.contains_ct(10), 0);
    }

    #[test]
    fn test_ct_and_fast_produce_same_results() {
        use state_syncer::iprf::{IprfTee, MAX_PREIMAGES};

        let master_seed = [42u8; 32];
        let c = 4;
        let w = 8;
        let lambda = 2;
        let num_regular = lambda * w;
        let num_backup = num_regular;
        let total_hints = num_regular + num_backup;

        let block_keys = derive_block_keys(&master_seed, c);

        let mut regular_blocks_list: Vec<Vec<usize>> = Vec::new();
        let mut backup_blocks_list: Vec<Vec<usize>> = Vec::new();

        for j in 0..num_regular {
            let subset_seed = derive_subset_seed(&master_seed, SEED_LABEL_REGULAR, j as u64);
            regular_blocks_list.push(compute_regular_blocks(&subset_seed, c));
        }
        for j in 0..num_backup {
            let subset_seed = derive_subset_seed(&master_seed, SEED_LABEL_BACKUP, j as u64);
            backup_blocks_list.push(compute_backup_blocks(&subset_seed, c));
        }

        let regular_bitsets: Vec<BlockBitset> = regular_blocks_list
            .iter()
            .map(|b| BlockBitset::from_sorted_blocks(b, c))
            .collect();
        let backup_bitsets: Vec<BlockBitset> = backup_blocks_list
            .iter()
            .map(|b| BlockBitset::from_sorted_blocks(b, c))
            .collect();

        let db: Vec<[u8; 32]> = (0..(c * w))
            .map(|i| {
                let mut entry = [0u8; 32];
                entry[0..8].copy_from_slice(&(i as u64).to_le_bytes());
                entry
            })
            .collect();

        let mut fast_regular: Vec<[u8; 32]> = vec![[0u8; 32]; num_regular];
        let mut fast_backup_in: Vec<[u8; 32]> = vec![[0u8; 32]; num_backup];
        let mut fast_backup_out: Vec<[u8; 32]> = vec![[0u8; 32]; num_backup];

        let block_iprfs: Vec<Iprf> = block_keys
            .iter()
            .map(|key| Iprf::new(*key, total_hints as u64, w as u64))
            .collect();

        for i in 0..(c * w) {
            let block = i / w;
            let offset = i % w;
            let entry = &db[i];

            let hint_indices = block_iprfs[block].inverse(offset as u64);

            for j in hint_indices {
                let j = j as usize;
                if j < num_regular {
                    if block_in_subset(&regular_blocks_list[j], block) {
                        xor_32(&mut fast_regular[j], entry);
                    }
                } else {
                    let backup_idx = j - num_regular;
                    if backup_idx < num_backup {
                        if block_in_subset(&backup_blocks_list[backup_idx], block) {
                            xor_32(&mut fast_backup_in[backup_idx], entry);
                        } else {
                            xor_32(&mut fast_backup_out[backup_idx], entry);
                        }
                    }
                }
            }
        }

        let mut ct_regular: Vec<[u8; 32]> = vec![[0u8; 32]; num_regular];
        let mut ct_backup_in: Vec<[u8; 32]> = vec![[0u8; 32]; num_backup];
        let mut ct_backup_out: Vec<[u8; 32]> = vec![[0u8; 32]; num_backup];

        let block_iprfs_ct: Vec<IprfTee> = block_keys
            .iter()
            .map(|key| IprfTee::new(*key, total_hints as u64, w as u64))
            .collect();

        for i in 0..(c * w) {
            let block = i / w;
            let offset = i % w;
            let entry = &db[i];

            let (indices, count) = block_iprfs_ct[block].inverse_ct(offset as u64);

            for t in 0..MAX_PREIMAGES {
                let in_range = ct_lt_u64(t as u64, count as u64);

                let j = indices[t] as usize;

                let is_regular = ct_lt_u64(j as u64, num_regular as u64);
                let backup_idx = j.wrapping_sub(num_regular);
                let is_valid_backup = ct_lt_u64(backup_idx as u64, num_backup as u64);
                let is_backup = (1 - is_regular) & is_valid_backup;

                // Branchless index selection (matches main CT path)
                let regular_idx = ct_select_usize(is_regular, j, 0);
                let in_regular_subset = regular_bitsets[regular_idx].contains_ct(block);

                let backup_idx_clamped = ct_select_usize(is_valid_backup, backup_idx, 0);
                let in_backup_subset = backup_bitsets[backup_idx_clamped].contains_ct(block);

                let update_regular = in_range & is_regular & in_regular_subset;
                let update_backup_in = in_range & is_backup & in_backup_subset;
                let update_backup_out = in_range & is_backup & (1 - in_backup_subset);

                ct_xor_32_masked(&mut ct_regular[regular_idx], entry, update_regular);
                ct_xor_32_masked(
                    &mut ct_backup_in[backup_idx_clamped],
                    entry,
                    update_backup_in,
                );
                ct_xor_32_masked(
                    &mut ct_backup_out[backup_idx_clamped],
                    entry,
                    update_backup_out,
                );
            }
        }

        assert_eq!(fast_regular, ct_regular, "Regular parities mismatch");
        assert_eq!(fast_backup_in, ct_backup_in, "Backup in-parities mismatch");
        assert_eq!(
            fast_backup_out, ct_backup_out,
            "Backup out-parities mismatch"
        );
    }
}
