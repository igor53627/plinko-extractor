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
//! - **AES mode** (`--aes`): AES-CTR stream cipher using AES-NI hardware acceleration
//!   - Fastest on CPUs with AES-NI support
//!   - Uses AES-128-CTR for PRF stream generation

use aes::cipher::{KeyIvInit, StreamCipher};
use blake3::OutputReader;
use clap::Parser;
use indicatif::{ProgressBar, ProgressStyle};
use memmap2::MmapOptions;
use rayon::prelude::*;
use std::fs::File;
use std::path::PathBuf;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::Instant;

type Aes128Ctr = ctr::Ctr128BE<aes::Aes128>;

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

    /// Use AES-CTR mode: AES-NI accelerated stream cipher instead of BLAKE3.
    /// Fastest on CPUs with AES-NI support.
    #[arg(long, default_value = "false")]
    aes: bool,

    /// Use AES standard mode: one AES-CTR PRF per (block, hint) pair.
    /// Comparable to standard BLAKE3 mode but with AES-NI acceleration.
    #[arg(long, default_value = "false")]
    aes_standard: bool,
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

/// Derive AES-128 key and IV from master seed and block index
fn aes_block_key_iv(master_seed: &[u8; 32], alpha: u64) -> ([u8; 16], [u8; 16]) {
    let mut hasher = blake3::Hasher::new_keyed(master_seed);
    hasher.update(b"plinko_aes_block");
    hasher.update(&alpha.to_le_bytes());
    let hash = hasher.finalize();
    let bytes = hash.as_bytes();
    let key: [u8; 16] = bytes[0..16].try_into().unwrap();
    let iv: [u8; 16] = bytes[16..32].try_into().unwrap();
    (key, iv)
}

/// Derives a 32-byte pseudorandom value for a hint using AES-128-CTR with a per-block key.
///
/// The IV is formed from the little-endian bytes of `hint_j` in its first 8 bytes; remaining IV bytes are zero.
///
/// # Examples
///
/// ```
/// let key = [0u8; 16];
/// let out = aes_hint_prf(&key, 1);
/// assert_eq!(out.len(), 32);
/// ```
fn aes_hint_prf(block_key: &[u8; 16], hint_j: u64) -> [u8; 32] {
    let mut iv = [0u8; 16];
    iv[0..8].copy_from_slice(&hint_j.to_le_bytes());

    let mut cipher = Aes128Ctr::new(block_key.into(), &iv.into());
    let mut output = [0u8; 32];
    cipher.apply_keystream(&mut output);
    output
}

/// Selects a divisor of `n` that is closest to `target`.
///
/// If `target` divides `n`, that value is chosen. Otherwise the function
/// searches outward from `target` to find the nearest value that divides `n`.
/// If no divisor is found in the search range, `1` is returned as a fallback.
///
/// # Examples
///
/// ```
/// // exact match
/// assert_eq!(find_nearest_divisor(100, 10), 10);
///
/// // nearest divisor above target
/// assert_eq!(find_nearest_divisor(100, 9), 10);
///
/// // prime n falls back to 1
/// assert_eq!(find_nearest_divisor(13, 5), 1);
/// ```
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

/// Computes per-hint partial hints for a single block by selecting pseudorandom entries
/// from the block and XOR-accumulating them into per-hint 32-byte values.
///
/// For each of the `num_hints` hint indices this function deterministically decides
/// whether to include a single 32-byte database entry from the specified block and,
/// when included, XORs that entry into the corresponding partial hint. Selection is
/// driven by a block-specific PRF derived from `master_seed` and `alpha`.
///
/// # Examples
///
/// ```
/// # use std::convert::TryInto;
/// // Minimal example: one block with w = 1 entry, a single hint.
/// let master_seed = [0u8; 32];
/// let w = 1usize;
/// let num_hints = 1usize;
/// let block_size_bytes = w * 32;
/// // Database: one block containing one 32-byte entry filled with 0x01
/// let mut db_bytes = vec![0u8; block_size_bytes];
/// for b in db_bytes.iter_mut() { *b = 1u8; }
///
/// let (partial_hints, xor_count) = process_block_standard(0, &db_bytes, block_size_bytes, w, num_hints, &master_seed);
/// assert_eq!(partial_hints.len(), num_hints);
/// // xor_count is the number of entries XORed into hints (0 or more)
/// assert!(xor_count <= num_hints as u64);
/// ```
///
/// # Returns
///
/// A tuple `(partial_hints, xor_count)` where `partial_hints` is a vector of `num_hints`
/// 32-byte arrays containing the XOR-accumulated values for each hint, and `xor_count`
/// is the total number of database entries XORed across all hints.
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

/// Process a single database block and produce per-hint 32-byte partial hints using a block-level XOF.
///
/// For each hint index from 0..num_hints this reads BYTES_PER_HINT bytes from a BLAKE3 XOF seeded by
/// the master seed and the block index, uses the first byte's least-significant bit to decide
/// whether to include the hint, derives a beta index from the next 8 bytes modulo `w`, fetches the
/// corresponding 32-byte entry from the block, and XORs that entry into the hint's accumulator.
///
/// # Returns
///
/// A tuple `(partial_hints, xor_count)` where `partial_hints` is a `Vec<[u8; 32]>` of length
/// `num_hints` containing the XOR-accumulated partial hints for this block, and `xor_count` is the
/// number of entry XORs performed for this block.
///
/// # Examples
///
/// ```
/// // Create a dummy block with w = 4 entries of 32 bytes (all zeros) and a single block in db_bytes.
/// let w = 4usize;
/// let num_hints = 8usize;
/// let block_size_bytes = w * 32;
/// let db_bytes = vec![0u8; block_size_bytes]; // one block
/// let master_seed = [0u8; 32];
///
/// let (partial_hints, xor_count) = process_block_xof(0, &db_bytes, block_size_bytes, w, num_hints, &master_seed);
/// assert_eq!(partial_hints.len(), num_hints);
/// // partial_hints contains 32-byte arrays; xor_count is a non-negative integer
/// ```
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
        let rand64 = u64::from_le_bytes(xof_buf[offset + 1..offset + 9].try_into().unwrap());
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

/// Processes a single database block using AES-CTR as the per-block PRF and produces partial hints.
///
/// The returned vector contains `num_hints` 32-byte partial hints where each hint is the XOR
/// accumulation of database entries selected by the AES-CTR-generated per-hint values. The
/// accompanying count is the number of database entries XORed across all hints for this block.
///
/// # Returns
///
/// A tuple `(partial_hints, xor_count)` where `partial_hints` is a `Vec<[u8; 32]>` of length
/// `num_hints` containing the accumulated XORed entries for each hint, and `xor_count` is the
/// total number of entries XORed into those hints for this block.
///
/// # Examples
///
/// ```
/// let w = 2;
/// let num_hints = 4;
/// let block_size_bytes = w * 32;
/// // Construct a single block with two 32-byte entries (all zeros and all ones)
/// let mut block = Vec::new();
/// block.extend_from_slice(&[0u8; 32]);
/// block.extend_from_slice(&[1u8; 32]);
/// // db_bytes contains one block only
/// let db_bytes = block;
/// let master_seed = [0u8; 32];
/// let (partial_hints, xor_count) = process_block_aes(0, &db_bytes, block_size_bytes, w, num_hints, &master_seed);
/// assert_eq!(partial_hints.len(), num_hints);
/// assert!(xor_count <= num_hints as u64);
/// ```
fn process_block_aes(
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

    // Derive AES key and IV for this block
    let (key, iv) = aes_block_key_iv(master_seed, alpha as u64);
    let mut cipher = Aes128Ctr::new(&key.into(), &iv.into());

    // Generate AES-CTR stream for all hints
    let total_bytes = num_hints * BYTES_PER_HINT;
    let mut aes_buf = vec![0u8; total_bytes];
    cipher.apply_keystream(&mut aes_buf);

    for j in 0..num_hints {
        let offset = j * BYTES_PER_HINT;
        let control = aes_buf[offset];

        // Bit 0 determines inclusion (Bernoulli 1/2)
        let include = (control & 1) == 1;
        if !include {
            continue;
        }

        // Derive offset beta from next 8 bytes
        let rand64 = u64::from_le_bytes(aes_buf[offset + 1..offset + 9].try_into().unwrap());
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

/// Process one block using an AES-based per-hint PRF to produce partial hints.
///
/// For the block identified by `alpha`, derives an AES block key from `master_seed` and
/// uses AES-CTR as a per-hint PRF to decide which entries from the block to include
/// in each hint. For each hint index `j`, the PRF output's lowest bit selects inclusion;
/// when included, the next 8 bytes (little-endian) determine an entry index `beta` in
/// [0, w) whose 32-byte value is XORed into that hint's accumulator.
///
/// # Parameters
///
/// - `alpha`: block index to process.
/// - `db_bytes`: raw database bytes (contiguous 32-byte entries); the function reads the
///   slice corresponding to the block `alpha`.
/// - `block_size_bytes`: number of bytes in one block (equals `w * 32`).
/// - `w`: number of 32-byte entries per block.
/// - `num_hints`: total number of hints (typically `lambda * w`).
/// - `master_seed`: 32-byte master seed used to derive the per-block AES key.
///
/// # Returns
///
/// A tuple `(partial_hints, xor_count)` where `partial_hints` is a vector of length
/// `num_hints` containing 32-byte accumulators (each the XOR of selected entries for
/// that hint), and `xor_count` is the total number of XOR operations performed.
///
/// # Examples
///
/// ```
/// // Single-block DB with w = 2 entries, each 32 bytes.
/// let w = 2usize;
/// let num_hints = 4usize;
/// let block_size_bytes = w * 32;
/// let mut db = vec![0u8; block_size_bytes]; // one block
/// // populate two distinct entries for test
/// db[0..32].copy_from_slice(&[1u8; 32]);
/// db[32..64].copy_from_slice(&[2u8; 32]);
/// let master_seed = &[0u8; 32];
/// let (hints, xor_count) = process_block_aes_standard(0, &db, block_size_bytes, w, num_hints, master_seed);
/// assert_eq!(hints.len(), num_hints);
/// // xor_count is between 0 and num_hints
/// assert!(xor_count <= num_hints as u64);
/// ```
fn process_block_aes_standard(
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

    // Derive block key once (one BLAKE3 per block, then pure AES per hint)
    let (block_key, _) = aes_block_key_iv(master_seed, alpha as u64);

    for j in 0..num_hints {
        let r = aes_hint_prf(&block_key, j as u64);

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

/// CLI entrypoint that generates Plinko PIR hints from a memory‑mapped database, runs the chosen PRF mode in parallel across blocks, and prints benchmarking and coverage statistics.
///
/// This function parses command‑line arguments, configures threading and PRF mode, memory‑maps the database file, partitions it into blocks, generates per‑hint XOR aggregates in parallel (using BLAKE3 XOF, per‑hint BLAKE3, AES‑CTR stream, or AES per‑hint modes), and prints throughput, XOR counts, and hint coverage. It uses a fixed master seed for reproducible benchmarking and supports optional truncation when N is not divisible by w.
///
/// # Examples
///
/// ```no_run
/// // Run the compiled binary with a database path and parameters:
/// // cargo run --release --bin plinko_hints -- --db-path ./db.bin --lambda 8 --threads 8
/// ```
///
/// # Returns
///
/// `Ok(())` on success, or an `eyre::Report` describing the failure.
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

    let mode_str = if args.aes {
        "AES-CTR"
    } else if args.aes_standard {
        "AES-Standard"
    } else if args.xof {
        "XOF"
    } else {
        "Standard"
    };
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
            println!(
                "⚠️  Warning: N ({}) not divisible by w ({}), {} tail entries will be ignored",
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

    let c = n_entries / w; // number of blocks
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
    let hint_storage_bytes = num_hints * WORD_SIZE;
    println!("  Number of hints: {}", num_hints);
    println!(
        "  Hint storage: {:.2} MB",
        hint_storage_bytes as f64 / 1024.0 / 1024.0
    );

    // Warn if parameters are off
    if c < w / 2 || c > w * 2 {
        println!(
            "\n⚠️  Warning: c/w ratio is {:.2}, ideally should be ~1.0 for optimal Plinko",
            c as f64 / w as f64
        );
    }

    // Estimate work
    let total_prf_calls = if args.xof || args.aes {
        c as u64 // One stream per block
    } else {
        (c as u64) * (num_hints as u64) // One hash per (block, hint)
    };
    let expected_xors = ((c as u64) * (num_hints as u64)) / 2; // Bernoulli(1/2)

    println!("\nEstimated work:");
    if args.aes {
        println!("  AES-CTR streams: {} (one per block)", c);
        println!(
            "  AES-CTR bytes: {:.2e}",
            (c * num_hints * BYTES_PER_HINT) as f64
        );
    } else if args.aes_standard {
        println!(
            "  AES PRF calls: {:.2e} (one per block*hint)",
            (c as u64 * num_hints as u64) as f64
        );
    } else if args.xof {
        println!("  XOF streams: {} (one per block)", c);
        println!(
            "  XOF bytes: {:.2e}",
            (c * num_hints * BYTES_PER_HINT) as f64
        );
    } else {
        println!("  PRF calls: {:.2e}", total_prf_calls as f64);
    }
    println!("  XOR operations: {:.2e}", expected_xors as f64);

    // Master seed (fixed for benchmark reproducibility)
    let master_seed: [u8; 32] = [
        0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f,
        0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19, 0x1a, 0x1b, 0x1c, 0x1d, 0x1e,
        0x1f, 0x20,
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
    let use_aes = args.aes;
    let use_aes_standard = args.aes_standard;

    // Parallel map-reduce over blocks
    let (hints, total_xors) = (0..c)
        .into_par_iter()
        .map(|alpha| {
            let result = if use_aes {
                process_block_aes(
                    alpha,
                    db_bytes,
                    block_size_bytes,
                    w,
                    num_hints,
                    &master_seed,
                )
            } else if use_aes_standard {
                process_block_aes_standard(
                    alpha,
                    db_bytes,
                    block_size_bytes,
                    w,
                    num_hints,
                    &master_seed,
                )
            } else if use_xof {
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
    if args.aes {
        let aes_streams_per_sec = c as f64 / duration.as_secs_f64();
        let aes_bytes_per_sec = (c * num_hints * BYTES_PER_HINT) as f64 / duration.as_secs_f64();
        println!(
            "AES-CTR streams: {:.2}/s ({:.2} GB/s output)",
            aes_streams_per_sec,
            aes_bytes_per_sec / 1e9
        );
    } else if args.aes_standard {
        let prf_per_sec = ((c as u64) * (num_hints as u64)) as f64 / duration.as_secs_f64();
        println!("AES PRF calls: {:.2}M/s", prf_per_sec / 1_000_000.0);
    } else if args.xof {
        let xof_streams_per_sec = c as f64 / duration.as_secs_f64();
        let xof_bytes_per_sec = (c * num_hints * BYTES_PER_HINT) as f64 / duration.as_secs_f64();
        println!(
            "XOF streams: {:.2}/s ({:.2} GB/s output)",
            xof_streams_per_sec,
            xof_bytes_per_sec / 1e9
        );
    } else {
        let prf_per_sec = ((c as u64) * (num_hints as u64)) as f64 / duration.as_secs_f64();
        println!("PRF calls: {:.2}M/s", prf_per_sec / 1_000_000.0);
    }
    println!(
        "XOR operations: {} ({:.2}M/s)",
        total_xors,
        xors_per_sec / 1_000_000.0
    );
    println!("\nCoverage per block:");
    println!("  Expected: {:.0} hints/block", expected_xors_per_block);
    println!("  Actual avg: {:.1} hints/block", actual_avg);
    println!(
        "\nHint storage: {:.2} MB",
        hint_storage_bytes as f64 / 1024.0 / 1024.0
    );

    // Sanity check: count non-zero hints
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
    }

    proptest! {
        #![proptest_config(ProptestConfig {
            cases: 128,
            .. ProptestConfig::default()
        })]

        #[test]
        fn block_key_is_deterministic(
            seed in any::<[u8; 32]>(),
            alpha in any::<u64>(),
        ) {
            let k1 = block_key(&seed, alpha);
            let k2 = block_key(&seed, alpha);
            prop_assert_eq!(k1, k2);
        }

        #[test]
        fn block_key_changes_with_alpha(
            seed in any::<[u8; 32]>(),
            alpha1 in any::<u64>(),
            alpha2 in any::<u64>(),
        ) {
            prop_assume!(alpha1 != alpha2);
            let k1 = block_key(&seed, alpha1);
            let k2 = block_key(&seed, alpha2);
            prop_assert_ne!(k1, k2);
        }

        #[test]
        fn hint_block_prf_is_deterministic(
            k_alpha in any::<[u8; 32]>(),
            hint_j in any::<u64>(),
        ) {
            let r1 = hint_block_prf(&k_alpha, hint_j);
            let r2 = hint_block_prf(&k_alpha, hint_j);
            prop_assert_eq!(r1, r2);
        }

        #[test]
        fn hint_block_prf_changes_with_hint_index(
            k_alpha in any::<[u8; 32]>(),
            j1 in any::<u64>(),
            j2 in any::<u64>(),
        ) {
            prop_assume!(j1 != j2);
            let r1 = hint_block_prf(&k_alpha, j1);
            let r2 = hint_block_prf(&k_alpha, j2);
            prop_assert_ne!(r1, r2);
        }
    }

    proptest! {
        #![proptest_config(ProptestConfig {
            cases: 64,
            .. ProptestConfig::default()
        })]

        #[test]
        fn block_xof_is_deterministic(
            seed in any::<[u8; 32]>(),
            alpha in any::<u64>(),
            len in 0usize..512,
        ) {
            let mut buf1 = vec![0u8; len];
            let mut buf2 = vec![0u8; len];

            block_xof(&seed, alpha).fill(&mut buf1);
            block_xof(&seed, alpha).fill(&mut buf2);

            prop_assert_eq!(buf1, buf2);
        }
    }

    proptest! {
        #![proptest_config(ProptestConfig {
            cases: 128,
            .. ProptestConfig::default()
        })]

        #[test]
        fn aes_block_key_iv_is_deterministic(
            seed in any::<[u8; 32]>(),
            alpha in any::<u64>(),
        ) {
            let (k1, iv1) = aes_block_key_iv(&seed, alpha);
            let (k2, iv2) = aes_block_key_iv(&seed, alpha);
            prop_assert_eq!(k1, k2);
            prop_assert_eq!(iv1, iv2);
        }

        #[test]
        fn aes_hint_prf_is_deterministic(
            block_key in any::<[u8; 16]>(),
            hint_j in any::<u64>(),
        ) {
            let r1 = aes_hint_prf(&block_key, hint_j);
            let r2 = aes_hint_prf(&block_key, hint_j);
            prop_assert_eq!(r1, r2);
        }

        #[test]
        fn aes_hint_prf_changes_with_hint_index(
            block_key in any::<[u8; 16]>(),
            j1 in any::<u64>(),
            j2 in any::<u64>(),
        ) {
            prop_assume!(j1 != j2);
            let r1 = aes_hint_prf(&block_key, j1);
            let r2 = aes_hint_prf(&block_key, j2);
            prop_assert_ne!(r1, r2);
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