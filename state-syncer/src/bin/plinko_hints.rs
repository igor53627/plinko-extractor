//! Plinko PIR Hint Generator - Baseline Implementation
//!
//! This implements a simplified version of Plinko's HintInit for benchmarking purposes.
//!
//! ## Deviations from the paper (https://eprint.iacr.org/2024/318.pdf):
//! - **Subset sampling**: Uses Bernoulli(1/2) per block instead of exact c/2+1 subset
//! - **Backup hints**: Not implemented (only regular hints)
//! - **Subset storage**: Only parities are stored, not subset descriptors P_j
//!
//! This is suitable for measuring hint generation throughput but is NOT a
//! cryptographically faithful implementation of full Plinko HintInit.
//!
//! ## PRF Modes:
//! - **Default**: One BLAKE3 hash per (block, hint) pair - standard, well-understood
//! - **XOF mode** (`--xof`): One BLAKE3-XOF stream per block, sliced for all hints
//!   - Significantly faster but changes the PRF structure
//!   - Should be reviewed before production use

use std::time::Instant;
use std::path::PathBuf;
use std::fs::File;
use std::sync::atomic::{AtomicU64, Ordering};
use memmap2::MmapOptions;
use clap::Parser;
use indicatif::{ProgressBar, ProgressStyle};
use rayon::prelude::*;
use blake3::OutputReader;

const WORD_SIZE: usize = 32;
const BYTES_PER_HINT: usize = 9; // 1 byte control + 8 bytes for beta

#[derive(Parser, Debug)]
#[command(author, version, about = "Plinko PIR Hint Generator (baseline benchmark)", long_about = None)]
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

    /// Use XOF mode: one BLAKE3-XOF stream per block instead of per-hint hashes.
    /// Faster but changes PRF structure - review before production use.
    #[arg(long, default_value = "false")]
    xof: bool,
}

fn block_key(master_seed: &[u8; 32], alpha: u64) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_keyed(master_seed);
    hasher.update(b"plinko_block");
    hasher.update(&alpha.to_le_bytes());
    *hasher.finalize().as_bytes()
}

fn hint_block_prf(k_alpha: &[u8; 32], hint_j: u64) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_keyed(k_alpha);
    hasher.update(b"plinko_hint");
    hasher.update(&hint_j.to_le_bytes());
    *hasher.finalize().as_bytes()
}

/// Create XOF reader for a block - produces pseudorandom stream for all hints
fn block_xof(master_seed: &[u8; 32], alpha: u64) -> OutputReader {
    let mut hasher = blake3::Hasher::new_keyed(master_seed);
    hasher.update(b"plinko_block_xof");
    hasher.update(&alpha.to_le_bytes());
    hasher.finalize_xof()
}

fn xor_32(dst: &mut [u8; 32], src: &[u8; 32]) {
    for i in 0..32 {
        dst[i] ^= src[i];
    }
}

/// Find a divisor of n that is closest to target
fn find_nearest_divisor(n: usize, target: usize) -> usize {
    if n % target == 0 {
        return target;
    }
    
    // Search outward from target
    for delta in 1..target {
        if target >= delta && n % (target - delta) == 0 {
            return target - delta;
        }
        if n % (target + delta) == 0 {
            return target + delta;
        }
    }
    
    // Fallback: use 1 (every entry is its own block)
    1
}

/// Process a single block using standard per-hint PRF
fn process_block_standard(
    alpha: usize,
    db_bytes: &[u8],
    block_size_bytes: usize,
    w: usize,
    num_hints: usize,
    master_seed: &[u8; 32],
) -> (Vec<[u8; 32]>, u64) {
    let k_alpha = block_key(master_seed, alpha as u64);
    
    let block_start = alpha * block_size_bytes;
    let block_bytes = &db_bytes[block_start..block_start + block_size_bytes];

    let mut partial_hints = vec![[0u8; 32]; num_hints];
    let mut xor_count = 0u64;

    for j in 0..num_hints {
        let r = hint_block_prf(&k_alpha, j as u64);
        
        // Bit 0 of first byte determines inclusion (Bernoulli 1/2)
        let include = (r[0] & 1) == 1;
        if !include {
            continue;
        }

        // Derive offset beta within block from PRF output
        let rand64 = u64::from_le_bytes(r[1..9].try_into().unwrap());
        let beta = (rand64 as usize) % w;

        // Fetch the 32-byte entry at DB[alpha * w + beta]
        let entry_offset = beta * WORD_SIZE;
        let entry: [u8; 32] = block_bytes[entry_offset..entry_offset + WORD_SIZE]
            .try_into()
            .unwrap();

        // XOR into partial hint[j]
        xor_32(&mut partial_hints[j], &entry);
        xor_count += 1;
    }

    (partial_hints, xor_count)
}

/// Process a single block using XOF mode - one stream per block
fn process_block_xof(
    alpha: usize,
    db_bytes: &[u8],
    block_size_bytes: usize,
    w: usize,
    num_hints: usize,
    master_seed: &[u8; 32],
) -> (Vec<[u8; 32]>, u64) {
    let block_start = alpha * block_size_bytes;
    let block_bytes = &db_bytes[block_start..block_start + block_size_bytes];

    let mut partial_hints = vec![[0u8; 32]; num_hints];
    let mut xor_count = 0u64;

    // Generate XOF stream for this block
    let mut xof = block_xof(master_seed, alpha as u64);
    
    // Read all random bytes needed for all hints at once
    let total_bytes = num_hints * BYTES_PER_HINT;
    let mut xof_buf = vec![0u8; total_bytes];
    xof.fill(&mut xof_buf);

    for j in 0..num_hints {
        let offset = j * BYTES_PER_HINT;
        let control = xof_buf[offset];
        
        // Bit 0 determines inclusion (Bernoulli 1/2)
        let include = (control & 1) == 1;
        if !include {
            continue;
        }

        // Derive offset beta from next 8 bytes
        let rand64 = u64::from_le_bytes(
            xof_buf[offset + 1..offset + 9].try_into().unwrap()
        );
        let beta = (rand64 as usize) % w;

        // Fetch the 32-byte entry at DB[alpha * w + beta]
        let entry_offset = beta * WORD_SIZE;
        let entry: [u8; 32] = block_bytes[entry_offset..entry_offset + WORD_SIZE]
            .try_into()
            .unwrap();

        // XOR into partial hint[j]
        xor_32(&mut partial_hints[j], &entry);
        xor_count += 1;
    }

    (partial_hints, xor_count)
}

fn main() -> eyre::Result<()> {
    let args = Args::parse();

    // Configure thread pool
    if let Some(threads) = args.threads {
        rayon::ThreadPoolBuilder::new()
            .num_threads(threads)
            .build_global()
            .unwrap();
    }
    let num_threads = rayon::current_num_threads();
    
    let mode_str = if args.xof { "XOF" } else { "Standard" };
    println!("Plinko PIR Hint Generator (Parallel, {} mode)", mode_str);
    println!("================================================");
    println!("Database: {:?}", args.db_path);
    println!("Threads: {}", num_threads);
    println!("PRF Mode: {}", mode_str);

    let file = File::open(&args.db_path)?;
    let file_len = file.metadata()?.len() as usize;
    println!("DB Size: {:.2} GB", file_len as f64 / 1024.0 / 1024.0 / 1024.0);

    let mmap = unsafe { MmapOptions::new().map(&file)? };
    let db_bytes: &[u8] = &mmap;

    assert_eq!(db_bytes.len() % WORD_SIZE, 0, "DB size must be multiple of 32 bytes");
    let n_entries = db_bytes.len() / WORD_SIZE;
    println!("Total Entries (N): {}", n_entries);

    // Derive w (entries per block) - default to sqrt(N), adjusted to divide N
    let w = args.entries_per_block.unwrap_or_else(|| {
        let sqrt_n = (n_entries as f64).sqrt().round() as usize;
        find_nearest_divisor(n_entries, sqrt_n)
    });
    
    // Validate divisibility
    let remainder = n_entries % w;
    if remainder != 0 {
        if args.allow_truncation {
            println!("⚠️  Warning: N ({}) not divisible by w ({}), {} tail entries will be ignored", 
                     n_entries, w, remainder);
        } else {
            eprintln!("Error: N ({}) must be divisible by w ({}) for correct Plinko hints.", n_entries, w);
            eprintln!("       {} entries would be dropped. Use --allow-truncation to proceed anyway.", remainder);
            eprintln!("       Or use --entries-per-block to set w to a divisor of N.");
            std::process::exit(1);
        }
    }
    
    let c = n_entries / w; // number of blocks
    let block_size_bytes = w * WORD_SIZE;
    
    println!("\nPlinko Parameters:");
    println!("  Entries per block (w): {}", w);
    println!("  Number of blocks (c): {}", c);
    println!("  Block size: {:.2} MB", block_size_bytes as f64 / 1024.0 / 1024.0);
    println!("  Lambda: {}", args.lambda);
    
    let num_hints = args.lambda * w;
    let hint_storage_bytes = num_hints * WORD_SIZE;
    println!("  Number of hints: {}", num_hints);
    println!("  Hint storage: {:.2} MB", hint_storage_bytes as f64 / 1024.0 / 1024.0);

    // Warn if parameters are off
    if c < w / 2 || c > w * 2 {
        println!("\n⚠️  Warning: c/w ratio is {:.2}, ideally should be ~1.0 for optimal Plinko", c as f64 / w as f64);
    }

    // Estimate work
    let total_prf_calls = if args.xof {
        c as u64 // One XOF call per block
    } else {
        (c as u64) * (num_hints as u64) // One hash per (block, hint)
    };
    let expected_xors = ((c as u64) * (num_hints as u64)) / 2; // Bernoulli(1/2)
    
    println!("\nEstimated work:");
    if args.xof {
        println!("  XOF streams: {} (one per block)", c);
        println!("  XOF bytes: {:.2e}", (c * num_hints * BYTES_PER_HINT) as f64);
    } else {
        println!("  PRF calls: {:.2e}", total_prf_calls as f64);
    }
    println!("  XOR operations: {:.2e}", expected_xors as f64);

    // Master seed (fixed for benchmark reproducibility)
    let master_seed: [u8; 32] = [
        0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,
        0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f, 0x10,
        0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18,
        0x19, 0x1a, 0x1b, 0x1c, 0x1d, 0x1e, 0x1f, 0x20,
    ];

    println!("\nGenerating hints (parallel over {} blocks)...", c);
    let start = Instant::now();
    
    let pb = ProgressBar::new(c as u64);
    pb.set_style(ProgressStyle::default_bar()
        .template("{spinner:.green} [{elapsed_precise}] [{bar:40.cyan/blue}] {pos}/{len} blocks ({eta}) {msg}")
        .unwrap()
        .progress_chars("#>-"));

    let progress_counter = AtomicU64::new(0);
    let use_xof = args.xof;

    // Parallel map-reduce over blocks
    let (hints, total_xors) = (0..c)
        .into_par_iter()
        .map(|alpha| {
            let result = if use_xof {
                process_block_xof(
                    alpha,
                    db_bytes,
                    block_size_bytes,
                    w,
                    num_hints,
                    &master_seed,
                )
            } else {
                process_block_standard(
                    alpha,
                    db_bytes,
                    block_size_bytes,
                    w,
                    num_hints,
                    &master_seed,
                )
            };
            
            // Update progress
            let count = progress_counter.fetch_add(1, Ordering::Relaxed);
            if count % 100 == 0 {
                pb.set_position(count);
            }
            
            result
        })
        .reduce(
            || (vec![[0u8; 32]; num_hints], 0u64),
            |(mut acc_hints, acc_xors), (partial_hints, partial_xors)| {
                for (acc, partial) in acc_hints.iter_mut().zip(partial_hints.iter()) {
                    xor_32(acc, partial);
                }
                (acc_hints, acc_xors + partial_xors)
            },
        );

    pb.finish_with_message("Done");
    let duration = start.elapsed();
    
    // Statistics
    let expected_xors_per_block = num_hints as f64 / 2.0;
    let actual_avg = total_xors as f64 / c as f64;
    
    let throughput_mb = (file_len as f64 / 1024.0 / 1024.0) / duration.as_secs_f64();
    let xors_per_sec = total_xors as f64 / duration.as_secs_f64();

    println!("\n=== Results ===");
    println!("Time Taken: {:.2?}", duration);
    println!("Throughput: {:.2} MB/s (raw DB)", throughput_mb);
    if args.xof {
        let xof_streams_per_sec = c as f64 / duration.as_secs_f64();
        let xof_bytes_per_sec = (c * num_hints * BYTES_PER_HINT) as f64 / duration.as_secs_f64();
        println!("XOF streams: {:.2}/s ({:.2} GB/s output)", xof_streams_per_sec, xof_bytes_per_sec / 1e9);
    } else {
        let prf_per_sec = ((c as u64) * (num_hints as u64)) as f64 / duration.as_secs_f64();
        println!("PRF calls: {:.2}M/s", prf_per_sec / 1_000_000.0);
    }
    println!("XOR operations: {} ({:.2}M/s)", total_xors, xors_per_sec / 1_000_000.0);
    println!("\nCoverage per block:");
    println!("  Expected: {:.0} hints/block", expected_xors_per_block);
    println!("  Actual avg: {:.1} hints/block", actual_avg);
    println!("\nHint storage: {:.2} MB", hint_storage_bytes as f64 / 1024.0 / 1024.0);

    // Sanity check: count non-zero hints
    let non_zero_hints = hints.iter().filter(|h| h.iter().any(|&b| b != 0)).count();
    println!("\nNon-zero hints: {} / {} ({:.1}%)", 
             non_zero_hints, num_hints, 
             100.0 * non_zero_hints as f64 / num_hints as f64);

    Ok(())
}
