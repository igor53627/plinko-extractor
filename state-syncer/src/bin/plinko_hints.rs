//! Plinko PIR Hint Generator - iPRF Implementation
//!
//! This implements Plinko's HintInit using the invertible PRF (iPRF) construction.
//!
//! ## Modes:
//! - **iPRF** (default): Uses iPRF.inverse() to find all database indices for each hint
//! - **iPRF-TEE** (`--tee`): Constant-time iPRF for trusted execution environments

use clap::Parser;
use indicatif::{ProgressBar, ProgressStyle};
use memmap2::MmapOptions;
use rayon::prelude::*;
use state_syncer::constant_time::{ct_lt_u64, ct_select_u64};
use state_syncer::iprf::{Iprf, IprfTee, PrfKey128, MAX_PREIMAGES};
use std::fs::File;
use std::path::PathBuf;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::Instant;

const WORD_SIZE: usize = 32;

#[derive(Parser, Debug)]
#[command(author, version, about = "Plinko PIR Hint Generator (iPRF)", long_about = None)]
struct Args {
    /// Path to the database file
    #[arg(short, long, default_value = "/mnt/plinko/data/database.bin")]
    db_path: PathBuf,

    /// Security parameter lambda (number of hints = lambda * w)
    #[arg(short, long, default_value = "128")]
    lambda: usize,

    /// Override entries per block (w). Default: sqrt(N) adjusted to divide N
    #[arg(short, long)]
    entries_per_block: Option<usize>,

    /// Allow truncation if N is not divisible by w (drops tail entries)
    #[arg(long, default_value = "false")]
    allow_truncation: bool,

    /// Number of threads (default: all cores)
    #[arg(short = 't', long)]
    threads: Option<usize>,

    /// Use TEE mode: constant-time operations for trusted execution environments.
    /// Prevents timing side-channels but slightly slower.
    #[arg(long, default_value = "false")]
    tee: bool,
}

fn xor_32(dst: &mut [u8; 32], src: &[u8; 32]) {
    for i in 0..32 {
        dst[i] ^= src[i];
    }
}

/// Masked XOR - always executes XOR, but result is conditional on mask
/// mask should be 0x00 (skip) or 0xFF (include)
fn xor_32_masked(dst: &mut [u8; 32], src: &[u8; 32], mask_byte: u8) {
    for i in 0..32 {
        dst[i] ^= src[i] & mask_byte;
    }
}

/// Selects a divisor of `n` that is closest to `target`.
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

/// Process hints using the cryptographically correct iPRF.
///
/// Unlike block-parallel approaches, this iterates over hints and uses iPRF.inverse()
/// to find all database indices that contribute to each hint, then XORs those entries.
fn process_hints_iprf(
    db_bytes: &[u8],
    n_entries: usize,
    num_hints: usize,
    iprf_key: &PrfKey128,
    pb: &ProgressBar,
) -> (Vec<[u8; 32]>, u64) {
    let iprf = Iprf::new(*iprf_key, n_entries as u64, num_hints as u64);
    let progress_counter = AtomicU64::new(0);

    let results: Vec<([u8; 32], u64)> = (0..num_hints)
        .into_par_iter()
        .map(|hint_id| {
            let preimages = iprf.inverse(hint_id as u64);
            let mut hint_value = [0u8; 32];
            let mut xor_count = 0u64;

            for db_index in preimages {
                let offset = (db_index as usize) * WORD_SIZE;
                if offset + WORD_SIZE <= db_bytes.len() {
                    let entry: [u8; 32] = db_bytes[offset..offset + WORD_SIZE].try_into().unwrap();
                    xor_32(&mut hint_value, &entry);
                    xor_count += 1;
                }
            }

            let count = progress_counter.fetch_add(1, Ordering::Relaxed);
            if count % 1000 == 0 {
                pb.set_position(count);
            }

            (hint_value, xor_count)
        })
        .collect();

    let mut hints = Vec::with_capacity(num_hints);
    let mut total_xors = 0u64;
    for (hint_value, xor_count) in results {
        hints.push(hint_value);
        total_xors += xor_count;
    }

    (hints, total_xors)
}

/// Process hints using the constant-time iPRF for TEE execution.
fn process_hints_iprf_tee(
    db_bytes: &[u8],
    n_entries: usize,
    num_hints: usize,
    iprf_key: &PrfKey128,
    pb: &ProgressBar,
) -> (Vec<[u8; 32]>, u64) {
    let iprf = IprfTee::new(*iprf_key, n_entries as u64, num_hints as u64);
    let progress_counter = AtomicU64::new(0);

    let results: Vec<([u8; 32], u64)> = (0..num_hints)
        .into_par_iter()
        .map(|hint_id| {
            let (preimages, count) = iprf.inverse_ct(hint_id as u64);
            let mut hint_value = [0u8; 32];
            let mut xor_count = 0u64;

            for i in 0..MAX_PREIMAGES {
                let db_index = preimages[i];
                let in_range = ct_lt_u64(i as u64, count as u64);
                let mask_byte = (in_range as u8).wrapping_neg();

                let offset = (db_index as usize) * WORD_SIZE;
                let max_valid_offset = db_bytes.len().saturating_sub(WORD_SIZE);
                let is_valid = ct_lt_u64(offset as u64, (max_valid_offset + 1) as u64);
                let safe_offset =
                    ct_select_u64(is_valid, offset as u64, max_valid_offset as u64) as usize;
                let entry: [u8; 32] = db_bytes[safe_offset..safe_offset + WORD_SIZE]
                    .try_into()
                    .unwrap();
                xor_32_masked(&mut hint_value, &entry, mask_byte);
            }
            xor_count += count as u64;

            let count = progress_counter.fetch_add(1, Ordering::Relaxed);
            if count % 1000 == 0 {
                pb.set_position(count);
            }

            (hint_value, xor_count)
        })
        .collect();

    let mut hints = Vec::with_capacity(num_hints);
    let mut total_xors = 0u64;
    for (hint_value, xor_count) in results {
        hints.push(hint_value);
        total_xors += xor_count;
    }

    (hints, total_xors)
}

fn main() -> eyre::Result<()> {
    let args = Args::parse();

    if let Some(threads) = args.threads {
        rayon::ThreadPoolBuilder::new()
            .num_threads(threads)
            .build_global()
            .unwrap();
    }
    let num_threads = rayon::current_num_threads();

    if args.lambda == 0 {
        eprintln!("Error: lambda must be >= 1");
        std::process::exit(1);
    }

    let mode_str = if args.tee { "iPRF-TEE" } else { "iPRF" };
    println!("Plinko PIR Hint Generator (Parallel, {} mode)", mode_str);
    println!("================================================");
    println!("Database: {:?}", args.db_path);
    println!("Threads: {}", num_threads);
    println!("PRF Mode: {}", mode_str);

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
            eprintln!("       Or use --entries-per-block to set w to a divisor of N.");
            std::process::exit(1);
        }
    }

    let c = n_entries / w;
    let block_size_bytes = w * WORD_SIZE;

    println!("\nPlinko Parameters:");
    println!("  Entries per block (w): {}", w);
    println!("  Number of blocks (c): {}", c);
    println!(
        "  Block size: {:.2} MB",
        block_size_bytes as f64 / 1024.0 / 1024.0
    );
    println!("  Lambda: {}", args.lambda);

    let num_hints = args.lambda * w;

    if num_hints == 0 {
        eprintln!("Error: num_hints must be > 0 (lambda * w = 0)");
        std::process::exit(1);
    }

    // Validate TEE mode won't truncate preimages
    if args.tee {
        let expected_preimages = n_entries as f64 / num_hints as f64;
        if expected_preimages > 48.0 {
            eprintln!(
                "Error: Expected {:.1} preimages/hint exceeds safe threshold for TEE mode.",
                expected_preimages
            );
            eprintln!(
                "       TEE mode will truncate at MAX_PREIMAGES=64, causing incorrect hints."
            );
            eprintln!("       Increase num_hints (lambda) or use non-TEE iPRF mode.");
            std::process::exit(1);
        }
    }

    let hint_storage_bytes = num_hints * WORD_SIZE;
    println!("  Number of hints: {}", num_hints);
    println!(
        "  Hint storage: {:.2} MB",
        hint_storage_bytes as f64 / 1024.0 / 1024.0
    );

    if c < w / 2 || c > w * 2 {
        println!(
            "\nWarning: c/w ratio is {:.2}, ideally should be ~1.0 for optimal Plinko",
            c as f64 / w as f64
        );
    }

    println!("\nEstimated work:");
    println!("  iPRF inverse calls: {} (one per hint)", num_hints);
    println!(
        "  Expected XORs: ~{} (n_entries total, distributed across hints)",
        n_entries
    );

    let master_seed: [u8; 32] = [
        0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f,
        0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19, 0x1a, 0x1b, 0x1c, 0x1d, 0x1e,
        0x1f, 0x20,
    ];

    let start = Instant::now();

    println!(
        "\nGenerating hints (parallel over {} hints, {} mode)...",
        num_hints, mode_str
    );
    let pb = ProgressBar::new(num_hints as u64);
    pb.set_style(
        ProgressStyle::default_bar()
            .template("{spinner:.green} [{elapsed_precise}] [{bar:40.cyan/blue}] {pos}/{len} hints ({eta}) {msg}")
            .unwrap()
            .progress_chars("#>-"),
    );

    let iprf_key: PrfKey128 = master_seed[0..16].try_into().unwrap();

    let (hints, total_xors) = if args.tee {
        process_hints_iprf_tee(db_bytes, n_entries, num_hints, &iprf_key, &pb)
    } else {
        process_hints_iprf(db_bytes, n_entries, num_hints, &iprf_key, &pb)
    };

    pb.finish_with_message("Done");

    let duration = start.elapsed();

    let throughput_mb = (file_len as f64 / 1024.0 / 1024.0) / duration.as_secs_f64();
    let xors_per_sec = total_xors as f64 / duration.as_secs_f64();

    println!("\n=== Results ===");
    println!("Time Taken: {:.2?}", duration);
    println!("Throughput: {:.2} MB/s (raw DB)", throughput_mb);

    let hints_per_sec = num_hints as f64 / duration.as_secs_f64();
    let avg_preimages = total_xors as f64 / num_hints as f64;
    println!(
        "iPRF inverse calls: {:.2}/s ({:.2}K hints/s)",
        hints_per_sec,
        hints_per_sec / 1000.0
    );
    println!(
        "Average preimages per hint: {:.2} (expected ~{:.2})",
        avg_preimages,
        n_entries as f64 / num_hints as f64
    );

    println!(
        "XOR operations: {} ({:.2}M/s)",
        total_xors,
        xors_per_sec / 1_000_000.0
    );
    println!(
        "\nHint storage: {:.2} MB",
        hint_storage_bytes as f64 / 1024.0 / 1024.0
    );

    let non_zero_hints = hints.iter().filter(|h| h.iter().any(|&b| b != 0)).count();
    println!(
        "\nNon-zero hints: {} / {} ({:.1}%)",
        non_zero_hints,
        num_hints,
        100.0 * non_zero_hints as f64 / num_hints as f64
    );

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    proptest! {
        #![proptest_config(ProptestConfig {
            cases: 256,
            .. ProptestConfig::default()
        })]

        #[test]
        fn xor_32_with_zero_is_noop(mut a in any::<[u8; 32]>()) {
            let original = a;
            let zeros = [0u8; 32];
            xor_32(&mut a, &zeros);
            prop_assert_eq!(a, original);
        }

        #[test]
        fn xor_32_twice_with_same_operand_restores_original(
            mut a in any::<[u8; 32]>(),
            b in any::<[u8; 32]>(),
        ) {
            let original = a;
            xor_32(&mut a, &b);
            xor_32(&mut a, &b);
            prop_assert_eq!(a, original);
        }

        #[test]
        fn xor_32_matches_bytewise_xor(
            mut a in any::<[u8; 32]>(),
            b in any::<[u8; 32]>(),
        ) {
            let mut expected = [0u8; 32];
            for i in 0..32 {
                expected[i] = a[i] ^ b[i];
            }

            xor_32(&mut a, &b);
            prop_assert_eq!(a, expected);
        }

        #[test]
        fn xor_32_masked_with_ff_matches_xor_32(
            mut a in any::<[u8; 32]>(),
            b in any::<[u8; 32]>(),
        ) {
            let mut expected = a;
            xor_32(&mut expected, &b);
            xor_32_masked(&mut a, &b, 0xFF);
            prop_assert_eq!(a, expected);
        }

        #[test]
        fn xor_32_masked_with_00_is_noop(
            mut a in any::<[u8; 32]>(),
            b in any::<[u8; 32]>(),
        ) {
            let original = a;
            xor_32_masked(&mut a, &b, 0x00);
            prop_assert_eq!(a, original);
        }
    }

    proptest! {
        #![proptest_config(ProptestConfig {
            cases: 128,
            .. ProptestConfig::default()
        })]

        #[test]
        fn find_nearest_divisor_returns_valid_divisor(
            n in 1usize..100_000,
            target in 1usize..1000,
        ) {
            let divisor = find_nearest_divisor(n, target);
            prop_assert!(divisor >= 1);
            prop_assert_eq!(n % divisor, 0);
        }

        #[test]
        fn find_nearest_divisor_exact_match(n in 1usize..10_000) {
            let divisor = find_nearest_divisor(n, n);
            prop_assert_eq!(divisor, n);
        }
    }
}
