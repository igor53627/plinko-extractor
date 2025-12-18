//! Plinko PIR Hint Generator - iPRF Implementation (Paper-compliant)
//!
//! Implements Plinko's HintInit matching Fig. 7 of the paper and Plinko.v Coq spec.
//!
//! Key differences from previous implementation:
//! - Generates c iPRF keys (one per block), not one global key
//! - Regular hints: block subset of size c/2+1, single parity
//! - Backup hints: block subset of size c/2, dual parities (in/out)
//! - iPRF domain = total hints (λw + q), range = w (block size)

use clap::Parser;
use indicatif::{ProgressBar, ProgressStyle};
use memmap2::MmapOptions;
use rand::{RngCore, SeedableRng};
use rand_chacha::ChaCha20Rng;
use sha2::{Digest, Sha256};
use state_syncer::iprf::{Iprf, PrfKey128};
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

    // Pre-create iPRF instances for each block (avoids recreating per entry)
    let block_iprfs: Vec<Iprf> = block_keys
        .iter()
        .map(|key| Iprf::new(*key, total_hints as u64, w as u64))
        .collect();

    // Precompute all iPRF inverse mappings: block -> offset -> Vec<hint_indices>
    // This moves the expensive SR PRP computation out of the streaming loop
    println!("[4/5] Precomputing iPRF inverse mappings ({} blocks x {} offsets)...", c, w);
    let precompute_start = Instant::now();
    let block_inverse_maps: Vec<Vec<Vec<u64>>> = block_iprfs
        .iter()
        .map(|iprf| {
            (0..w).map(|offset| iprf.inverse(offset as u64)).collect()
        })
        .collect();
    println!("  Precompute time: {:.2?}", precompute_start.elapsed());

    // Step 5: Stream database and update parities (now just lookups + XOR)
    println!("[5/5] Streaming database ({} entries)...", n_effective);
    let pb = ProgressBar::new(n_effective as u64);
    pb.set_style(
        ProgressStyle::default_bar()
            .template("{spinner:.green} [{elapsed_precise}] [{bar:40.cyan/blue}] {pos}/{len} entries ({eta})")
            .unwrap()
            .progress_chars("#>-"),
    );

    for i in 0..n_effective {
        let block = i / w;
        let offset = i % w;

        // For padded entries beyond actual DB, use zero (XOR with zero is no-op)
        let entry: [u8; 32] = if i < n_entries {
            let entry_offset = i * WORD_SIZE;
            db_bytes[entry_offset..entry_offset + WORD_SIZE]
                .try_into()
                .unwrap()
        } else {
            [0u8; 32]
        };

        // Look up precomputed hint indices for this (block, offset)
        let hint_indices = &block_inverse_maps[block][offset];

        for &j in hint_indices {
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

    pb.finish_with_message("Done");

    // Drop in-memory block lists now that streaming is complete
    // Only seeds + parities are retained in hint structs
    drop(regular_hint_blocks);
    drop(backup_hint_blocks);

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
        for offset in 0..w {
            total_preimages += block_iprfs[block].inverse(offset as u64).len();
        }
    }
    let blocks_checked = blocks_to_check;
    let expected_per_block = total_hints; // iPRF partitions domain [0, total_hints) into range [0, w)
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
}
