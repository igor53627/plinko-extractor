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
use rand::SeedableRng;
use rand_chacha::ChaCha20Rng;
use sha2::{Digest, Sha256};
use state_syncer::iprf::{Iprf, PrfKey128};
use std::fs::File;
use std::path::PathBuf;
use std::time::Instant;

const WORD_SIZE: usize = 32;

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

    /// Override entries per block (w). Default: sqrt(N) adjusted to divide N
    #[arg(short, long)]
    entries_per_block: Option<usize>,

    /// Allow truncation if N is not divisible by w (drops tail entries)
    #[arg(long, default_value = "false")]
    allow_truncation: bool,

}

/// Regular hint: P_j subset of c/2+1 blocks, single parity
struct RegularHint {
    blocks: Vec<usize>,
    parity: [u8; 32],
}

/// Backup hint: B_j subset of c/2 blocks, dual parities
struct BackupHint {
    blocks: Vec<usize>,
    parity_in: [u8; 32],
    parity_out: [u8; 32],
}

fn xor_32(dst: &mut [u8; 32], src: &[u8; 32]) {
    for i in 0..32 {
        dst[i] ^= src[i];
    }
}

fn find_nearest_divisor(n: usize, target: usize) -> usize {
    if n % target == 0 {
        return target;
    }
    for delta in 1..target {
        if target >= delta && n % (target - delta) == 0 {
            return target - delta;
        }
        if n % (target + delta) == 0 {
            return target + delta;
        }
    }
    1
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

    let w = args.entries_per_block.unwrap_or_else(|| {
        let sqrt_n = (n_entries as f64).sqrt().round() as usize;
        find_nearest_divisor(n_entries, sqrt_n)
    });

    let remainder = n_entries % w;
    if remainder != 0 {
        if args.allow_truncation {
            println!(
                "Warning: N ({}) not divisible by w ({}), {} tail entries will be ignored",
                n_entries, w, remainder
            );
        } else {
            eprintln!(
                "Error: N ({}) must be divisible by w ({}) for correct Plinko hints.",
                n_entries, w
            );
            eprintln!(
                "       {} entries would be dropped. Use --allow-truncation to proceed anyway.",
                remainder
            );
            std::process::exit(1);
        }
    }

    let c = n_entries / w;
    let n_effective = c * w;

    println!("\nPlinko Parameters:");
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

    if c < 2 {
        eprintln!("Warning: c={} is very small; backup hints will have empty subsets", c);
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

    let regular_storage = num_regular * (regular_subset_size * 8 + WORD_SIZE);
    let backup_storage = num_backup * (backup_subset_size * 8 + 2 * WORD_SIZE);
    println!(
        "  Estimated hint storage: {:.2} MB",
        (regular_storage + backup_storage) as f64 / 1024.0 / 1024.0
    );

    let master_seed: [u8; 32] = [
        0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f,
        0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19, 0x1a, 0x1b, 0x1c, 0x1d, 0x1e,
        0x1f, 0x20,
    ];

    let start = Instant::now();

    // Step 1: Generate c iPRF keys (one per block)
    println!("\n[1/4] Generating {} iPRF keys (one per block)...", c);
    let block_keys = derive_block_keys(&master_seed, c);

    // Step 2: Initialize regular hints with random block subsets
    println!(
        "[2/4] Initializing {} regular hints (subset size {})...",
        num_regular, regular_subset_size
    );
    let mut hint_rng = ChaCha20Rng::from_seed(master_seed);
    let mut regular_hints: Vec<RegularHint> = (0..num_regular)
        .map(|_| {
            let mut blocks = random_subset(&mut hint_rng, regular_subset_size, c);
            blocks.sort_unstable();
            RegularHint {
                blocks,
                parity: [0u8; 32],
            }
        })
        .collect();

    // Step 3: Initialize backup hints with random block subsets
    println!(
        "[3/4] Initializing {} backup hints (subset size {})...",
        num_backup, backup_subset_size
    );
    let mut backup_hints: Vec<BackupHint> = (0..num_backup)
        .map(|_| {
            let mut blocks = random_subset(&mut hint_rng, backup_subset_size, c);
            blocks.sort_unstable();
            BackupHint {
                blocks,
                parity_in: [0u8; 32],
                parity_out: [0u8; 32],
            }
        })
        .collect();

    // Pre-create iPRF instances for each block (avoids recreating per entry)
    let block_iprfs: Vec<Iprf> = block_keys
        .iter()
        .map(|key| Iprf::new(*key, total_hints as u64, w as u64))
        .collect();

    // Step 4: Stream database and update parities
    println!("[4/4] Streaming database ({} entries)...", n_effective);
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

        let entry_offset = i * WORD_SIZE;
        let entry: [u8; 32] = db_bytes[entry_offset..entry_offset + WORD_SIZE]
            .try_into()
            .unwrap();

        // Find all hints j where iPRF.forward(j) == offset
        let hint_indices = block_iprfs[block].inverse(offset as u64);

        for j in hint_indices {
            let j = j as usize;
            if j < num_regular {
                // Regular hint: XOR if block in P
                let hint = &mut regular_hints[j];
                if block_in_subset(&hint.blocks, block) {
                    xor_32(&mut hint.parity, &entry);
                }
            } else {
                // Backup hint: XOR to parity_in if in P, else parity_out
                let backup_idx = j - num_regular;
                if backup_idx < num_backup {
                    let hint = &mut backup_hints[backup_idx];
                    if block_in_subset(&hint.blocks, block) {
                        xor_32(&mut hint.parity_in, &entry);
                    } else {
                        xor_32(&mut hint.parity_out, &entry);
                    }
                }
            }
        }

        if i % 10000 == 0 {
            pb.set_position(i as u64);
        }
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
    println!("\nVerifying iPRF coverage...");
    let mut total_preimages = 0usize;
    for block in 0..c.min(10) {
        for offset in 0..w {
            total_preimages += block_iprfs[block].inverse(offset as u64).len();
        }
    }
    let blocks_checked = c.min(10);
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
}
