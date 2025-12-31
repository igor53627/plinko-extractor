//! Benchmark IprfTee vs IprfTeeGaussian for hint generation
//!
//! This benchmark simulates the full hint generation workload in TEE/CT mode,
//! comparing the original O(n) binomial sampler vs the O(1) Gaussian approximation.
//!
//! Run: cargo build --release -p plinko --bin bench_iprf_gaussian
//!      ./target/release/bench_iprf_gaussian [--entries N] [--lambda L]

use clap::Parser;
use plinko::iprf::{IprfTee, IprfTeeGaussian, PrfKey128, MAX_PREIMAGES};
use std::time::Instant;

#[derive(Parser, Debug)]
#[command(author, version, about = "Benchmark IprfTee vs IprfTeeGaussian")]
struct Args {
    /// Number of database entries to simulate
    #[arg(long, default_value_t = 10000)]
    entries: usize,

    /// Security parameter (lambda)
    #[arg(long, default_value_t = 128)]
    lambda: usize,

    /// Entries per block (w). Defaults to sqrt(entries)
    #[arg(long)]
    w: Option<usize>,

    /// PRP security bits (lower = faster for benchmarking)
    #[arg(long, default_value_t = 32)]
    security_bits: u32,
}

fn main() {
    let args = Args::parse();

    let w = args.w.unwrap_or_else(|| (args.entries as f64).sqrt().round() as usize);
    let c = (args.entries + w - 1) / w;
    let total_hints = args.lambda * w * 2;

    println!("=== IprfTee vs IprfTeeGaussian Benchmark ===");
    println!("Entries: {}", args.entries);
    println!("Lambda: {}", args.lambda);
    println!("w (entries/block): {}", w);
    println!("c (blocks): {}", c);
    println!("total_hints (domain): {}", total_hints);
    println!("Security bits: {}", args.security_bits);
    println!();

    let key: PrfKey128 = [0x42u8; 16];
    let domain = total_hints as u64;
    let range = w as u64;

    // Create fake DB
    let db: Vec<[u8; 32]> = (0..args.entries)
        .map(|i| {
            let mut entry = [0u8; 32];
            entry[0..8].copy_from_slice(&(i as u64).to_le_bytes());
            entry
        })
        .collect();

    let num_regular = total_hints / 2;
    let num_backup = total_hints / 2;

    // Benchmark IprfTee (original)
    println!("--- IprfTee (O(n) binomial) ---");
    let (time_orig, checksum_orig) =
        bench_hint_gen(&args, &db, w, c, domain, range, num_regular, num_backup, key, false);

    // Benchmark IprfTeeGaussian (optimized)
    println!("\n--- IprfTeeGaussian (O(1) Gaussian) ---");
    let (time_gauss, checksum_gauss) =
        bench_hint_gen(&args, &db, w, c, domain, range, num_regular, num_backup, key, true);

    // Summary
    println!("\n=== Summary ===");
    println!("IprfTee:         {:.2} s ({:.2} us/entry)", time_orig, time_orig * 1_000_000.0 / args.entries as f64);
    println!("IprfTeeGaussian: {:.2} s ({:.2} us/entry)", time_gauss, time_gauss * 1_000_000.0 / args.entries as f64);
    println!("Speedup: {:.1}x", time_orig / time_gauss);
    println!("Checksum orig:  {}", checksum_orig);
    println!("Checksum gauss: {}", checksum_gauss);

    // Estimate for Ethereum mainnet
    println!("\n=== Ethereum Mainnet Estimate (2.4B entries, 128 cores) ===");
    let n_entries = 2_400_000_000u64;
    let cores = 128u64;

    let orig_per_entry_us = time_orig * 1_000_000.0 / args.entries as f64;
    let gauss_per_entry_us = time_gauss * 1_000_000.0 / args.entries as f64;

    let orig_total_sec = (n_entries as f64 * orig_per_entry_us) / 1_000_000.0;
    let gauss_total_sec = (n_entries as f64 * gauss_per_entry_us) / 1_000_000.0;

    let orig_days = orig_total_sec / cores as f64 / 86400.0;
    let gauss_days = gauss_total_sec / cores as f64 / 86400.0;

    println!("IprfTee:         {:.1} days", orig_days);
    println!("IprfTeeGaussian: {:.2} days ({:.1} hours)", gauss_days, gauss_days * 24.0);
    println!("Speedup: {:.1}x", orig_days / gauss_days);
}

fn bench_hint_gen(
    args: &Args,
    db: &[[u8; 32]],
    w: usize,
    c: usize,
    domain: u64,
    range: u64,
    num_regular: usize,
    num_backup: usize,
    key: PrfKey128,
    use_gaussian: bool,
) -> (f64, u8) {
    let mut regular_parities: Vec<[u8; 32]> = vec![[0u8; 32]; num_regular];
    let mut backup_parities: Vec<[u8; 32]> = vec![[0u8; 32]; num_backup];

    let entries_to_process = args.entries.min(db.len());

    let start = Instant::now();

    if use_gaussian {
        let iprf = IprfTeeGaussian::with_security(key, domain, range, args.security_bits);

        for i in 0..entries_to_process {
            let _block = i / w;
            let offset = i % w;
            let entry = &db[i];

            let (indices, count) = iprf.inverse_ct(offset as u64);

            for t in 0..MAX_PREIMAGES {
                if t < count {
                    let j = indices[t] as usize;
                    if j < num_regular {
                        for k in 0..32 {
                            regular_parities[j % num_regular][k] ^= entry[k];
                        }
                    } else if j - num_regular < num_backup {
                        let idx = (j - num_regular) % num_backup;
                        for k in 0..32 {
                            backup_parities[idx][k] ^= entry[k];
                        }
                    }
                }
            }
        }
    } else {
        let iprf = IprfTee::with_security(key, domain, range, args.security_bits);

        for i in 0..entries_to_process {
            let _block = i / w;
            let offset = i % w;
            let entry = &db[i];

            let (indices, count) = iprf.inverse_ct(offset as u64);

            for t in 0..MAX_PREIMAGES {
                if t < count {
                    let j = indices[t] as usize;
                    if j < num_regular {
                        for k in 0..32 {
                            regular_parities[j % num_regular][k] ^= entry[k];
                        }
                    } else if j - num_regular < num_backup {
                        let idx = (j - num_regular) % num_backup;
                        for k in 0..32 {
                            backup_parities[idx][k] ^= entry[k];
                        }
                    }
                }
            }
        }
    }

    let elapsed = start.elapsed().as_secs_f64();

    let checksum: u8 = regular_parities
        .iter()
        .chain(backup_parities.iter())
        .flat_map(|p| p.iter())
        .fold(0u8, |acc, &b| acc ^ b);

    println!("  Processed {} entries in {:.2} s", entries_to_process, elapsed);
    println!(
        "  Throughput: {:.2} entries/s, {:.2} us/entry",
        entries_to_process as f64 / elapsed,
        elapsed * 1_000_000.0 / entries_to_process as f64
    );

    (elapsed, checksum)
}
