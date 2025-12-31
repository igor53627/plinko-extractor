//! Benchmark all TEE binomial sampler optimizations
//!
//! Compares:
//! 1. Current: BinomialSamplerTee (global max_count bound)
//! 2. Opt #83: LeveledBinomialSamplerTee (per-level bounds)
//! 3. Opt #84: GaussianBinomialSamplerTee (O(1) for large n)
//! 4. Opt #85: PrecomputedBinomialSamplerTee (table lookup for small n, p=0.5)
//! 5. Combined: Hybrid using best approach for each case
//!
//! Run: cargo build --release -p plinko --bin bench_binomial_opts
//!      ./target/release/bench_binomial_opts [--iterations N]

use clap::Parser;
use std::time::Instant;

use plinko::binomial::{binomial_sample, binomial_sample_tee};
use plinko::binomial_gaussian::GaussianBinomialSamplerTee;
use plinko::binomial_leveled::LeveledBinomialSamplerTee;
use plinko::binomial_precomputed::PrecomputedBinomialSamplerTee;
use plinko::binomial_tee::BinomialSamplerTee;

#[derive(Parser, Debug)]
#[command(author, version, about = "Benchmark TEE binomial sampler optimizations")]
struct Args {
    /// Number of samples per benchmark
    #[arg(long, default_value_t = 10000)]
    iterations: usize,

    /// Security parameter lambda
    #[arg(long, default_value_t = 128)]
    lambda: usize,

    /// Entries per block (w) - uses Ethereum mainnet default
    #[arg(long, default_value_t = 256)]
    w: usize,

    /// Domain size (n) - balls in PMNS tree
    #[arg(long, default_value_t = 49152)]
    n: u64,
}

fn main() {
    let args = Args::parse();

    println!("=== TEE Binomial Sampler Optimization Benchmark ===");
    println!("Iterations: {}", args.iterations);
    println!("Lambda: {}", args.lambda);
    println!("w (range): {}", args.w);
    println!("n (domain/balls): {}", args.n);
    println!();

    let total_hints = 2 * args.lambda * args.w;
    println!("Derived parameters:");
    println!("  total_hints = 2 * lambda * w = {}", total_hints);
    println!();

    // Test cases: (count, num, denom)
    let test_cases = [
        (args.n, 1, 2),                    // Level 0: all balls, p=0.5
        (args.n / 2, 1, 2),                // Level 1: half balls
        (args.n / 4, 1, 2),                // Level 2: quarter balls
        (100u64, 1, 2),                    // Small n, p=0.5
        (args.n, 1, 4),                    // Large n, p=0.25
    ];

    println!("=== Benchmark Results ===\n");

    for &(count, num, denom) in &test_cases {
        println!(
            "--- count={}, p={}/{} ---",
            count, num, denom
        );

        // 1. Standard (non-CT) for reference
        bench_standard(&args, count, num, denom);

        // 2. Current TEE (global 65536 bound)
        bench_global_tee(&args, count, num, denom);

        // 3. Parameterized TEE (domain bound)
        bench_parameterized_tee(&args, count, num, denom);

        // 4. Opt #83: Leveled TEE
        bench_leveled_tee(&args, count, num, denom, args.w as u64);

        // 5. Opt #84: Gaussian TEE
        bench_gaussian_tee(&args, count, num, denom);

        // 6. Opt #85: Precomputed TEE
        if num * 2 == denom {
            bench_precomputed_tee(&args, count);
        }

        println!();
    }

    // Summary: estimate hint generation time for Ethereum mainnet
    println!("=== Ethereum Mainnet Estimate ===");
    estimate_mainnet(&args, total_hints);
}

fn bench_standard(args: &Args, count: u64, num: u64, denom: u64) {
    let start = Instant::now();
    let mut dummy = 0u64;
    for i in 0..args.iterations {
        let prf = (i as u64).wrapping_mul(0x9E3779B97F4A7C15);
        dummy = dummy.wrapping_add(binomial_sample(count, num, denom, prf));
    }
    let elapsed = start.elapsed();
    println!(
        "  Standard (non-CT):      {:>8.2} us/op  (dummy={})",
        elapsed.as_micros() as f64 / args.iterations as f64,
        dummy % 1000
    );
}

fn bench_global_tee(args: &Args, count: u64, num: u64, denom: u64) {
    let start = Instant::now();
    let mut dummy = 0u64;
    for i in 0..args.iterations {
        let prf = (i as u64).wrapping_mul(0x9E3779B97F4A7C15);
        dummy = dummy.wrapping_add(binomial_sample_tee(count, num, denom, prf));
    }
    let elapsed = start.elapsed();
    println!(
        "  Global TEE (65536):     {:>8.2} us/op  (dummy={})",
        elapsed.as_micros() as f64 / args.iterations as f64,
        dummy % 1000
    );
}

fn bench_parameterized_tee(args: &Args, count: u64, num: u64, denom: u64) {
    let sampler = BinomialSamplerTee::new(count);
    let start = Instant::now();
    let mut dummy = 0u64;
    for i in 0..args.iterations {
        let prf = (i as u64).wrapping_mul(0x9E3779B97F4A7C15);
        dummy = dummy.wrapping_add(sampler.sample(count, num, denom, prf));
    }
    let elapsed = start.elapsed();
    println!(
        "  Parameterized (n={}): {:>8.2} us/op  (dummy={})",
        count,
        elapsed.as_micros() as f64 / args.iterations as f64,
        dummy % 1000
    );
}

fn bench_leveled_tee(args: &Args, count: u64, num: u64, denom: u64, m: u64) {
    let sampler = LeveledBinomialSamplerTee::new(count, m);
    let start = Instant::now();
    let mut dummy = 0u64;
    for i in 0..args.iterations {
        let prf = (i as u64).wrapping_mul(0x9E3779B97F4A7C15);
        // Use level 0 (root) - actual level would vary
        dummy = dummy.wrapping_add(sampler.sample(0, count, num, denom, prf));
    }
    let elapsed = start.elapsed();
    println!(
        "  Leveled (#83, L0):      {:>8.2} us/op  (dummy={})",
        elapsed.as_micros() as f64 / args.iterations as f64,
        dummy % 1000
    );
}

fn bench_gaussian_tee(args: &Args, count: u64, num: u64, denom: u64) {
    let sampler = GaussianBinomialSamplerTee::new(1024);
    let start = Instant::now();
    let mut dummy = 0u64;
    for i in 0..args.iterations {
        let prf = (i as u64).wrapping_mul(0x9E3779B97F4A7C15);
        dummy = dummy.wrapping_add(sampler.sample(count, num, denom, prf));
    }
    let elapsed = start.elapsed();
    println!(
        "  Gaussian (#84):         {:>8.2} us/op  (dummy={})",
        elapsed.as_micros() as f64 / args.iterations as f64,
        dummy % 1000
    );
}

fn bench_precomputed_tee(args: &Args, count: u64) {
    let sampler = PrecomputedBinomialSamplerTee::new(1024);
    let start = Instant::now();
    let mut dummy = 0u64;
    for i in 0..args.iterations {
        let prf = (i as u64).wrapping_mul(0x9E3779B97F4A7C15);
        dummy = dummy.wrapping_add(sampler.sample_half(count, prf));
    }
    let elapsed = start.elapsed();
    println!(
        "  Precomputed (#85):      {:>8.2} us/op  (dummy={})",
        elapsed.as_micros() as f64 / args.iterations as f64,
        dummy % 1000
    );
}

fn estimate_mainnet(args: &Args, total_hints: usize) {
    // Ethereum mainnet: ~2.4B entries, 128 cores
    let n_entries = 2_400_000_000u64;
    let cores = 128u64;

    // Measure baseline (current TEE) for level 0
    let sampler_old = BinomialSamplerTee::new(total_hints as u64);
    let samples = 1000;
    
    // Warmup
    for i in 0..100 {
        let prf = (i as u64).wrapping_mul(0x9E3779B97F4A7C15);
        std::hint::black_box(sampler_old.sample(args.n, 1, 2, prf));
    }
    
    let start = Instant::now();
    for i in 0..samples {
        let prf = (i as u64).wrapping_mul(0x9E3779B97F4A7C15);
        std::hint::black_box(sampler_old.sample(args.n, 1, 2, prf));
    }
    let baseline_us = start.elapsed().as_secs_f64() * 1_000_000.0 / samples as f64;

    // Measure Gaussian (best for large n)
    let sampler_gauss = GaussianBinomialSamplerTee::new(1024);
    
    // Warmup
    for i in 0..100 {
        let prf = (i as u64).wrapping_mul(0x9E3779B97F4A7C15);
        std::hint::black_box(sampler_gauss.sample(args.n, 1, 2, prf));
    }
    
    let start = Instant::now();
    for i in 0..samples {
        let prf = (i as u64).wrapping_mul(0x9E3779B97F4A7C15);
        std::hint::black_box(sampler_gauss.sample(args.n, 1, 2, prf));
    }
    let gaussian_us = start.elapsed().as_secs_f64() * 1_000_000.0 / samples as f64;

    // Number of binomial samples per entry (tree depth for each hint)
    let tree_depth = (args.w as f64).log2().ceil() as u64;
    let samples_per_entry = tree_depth * 2; // regular + backup

    // Total time estimates (single core)
    let baseline_total_sec = (n_entries as f64 * samples_per_entry as f64 * baseline_us) / 1_000_000.0;
    let gaussian_total_sec = (n_entries as f64 * samples_per_entry as f64 * gaussian_us) / 1_000_000.0;

    // Parallel time (128 cores)
    let baseline_days = baseline_total_sec / cores as f64 / 86400.0;
    let gaussian_days = gaussian_total_sec / cores as f64 / 86400.0;

    println!("Parameters: {} entries, {} cores", n_entries, cores);
    println!("Tree depth: {}, samples/entry: {}", tree_depth, samples_per_entry);
    println!();
    println!("Per-sample timing:");
    println!("  Current TEE (total_hints={}): {:.2} us", total_hints, baseline_us);
    println!("  Gaussian (#84): {:.2} us", gaussian_us);
    println!();
    println!("Estimated total time (128 cores):");
    println!("  Current: {:.1} days", baseline_days);
    println!("  Gaussian: {:.1} days", gaussian_days);
    if gaussian_days > 0.0 {
        println!("  Speedup: {:.1}x", baseline_days / gaussian_days);
    }
}
