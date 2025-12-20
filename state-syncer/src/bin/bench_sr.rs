//! Benchmark for SwapOrNotSr PRP performance
//!
//! This binary measures the performance of the SR PRP with various configurations.
//! Used by the LLM-guided optimization harness.

use clap::Parser;
use state_syncer::iprf::{security_bits_from_env, PrfKey128, SwapOrNotSr};
use std::time::Instant;

#[derive(Parser, Debug)]
#[command(author, version, about = "Benchmark SwapOrNotSr PRP performance")]
struct Args {
    /// Domain size (number of elements)
    #[arg(short, long, default_value = "1000000")]
    domain: u64,

    /// Number of operations to perform
    #[arg(short, long, default_value = "100000")]
    operations: u64,

    /// Security bits (overrides SR_SECURITY_BITS env var)
    #[arg(short, long)]
    security_bits: Option<u32>,

    /// Run inverse operations instead of forward
    #[arg(long)]
    inverse: bool,

    /// Batch size for batch operations (0 = sequential)
    #[arg(short, long, default_value = "0")]
    batch: u64,

    /// Use parallel rayon processing
    #[arg(short, long)]
    parallel: bool,

    /// Verbose output
    #[arg(short, long)]
    verbose: bool,
}

fn main() -> eyre::Result<()> {
    let args = Args::parse();

    let security_bits = args.security_bits.unwrap_or_else(security_bits_from_env);
    let domain = args.domain;
    let operations = args.operations;
    let batch_size = args.batch;

    println!("SR PRP Benchmark");
    println!("----------------");
    println!("Domain: {}", domain);
    println!("Operations: {}", operations);
    println!("Security bits: {}", security_bits);
    println!("Mode: {}", if args.inverse { "inverse" } else { "forward" });
    println!("Batch size: {}", if batch_size == 0 { "sequential".to_string() } else { batch_size.to_string() });
    println!("Parallel: {}", args.parallel);

    // Initialize PRP
    let key: PrfKey128 = [0u8; 16];
    
    if args.verbose {
        println!("\nInitializing PRP...");
    }
    let init_start = Instant::now();
    let prp = SwapOrNotSr::with_security(key, domain, security_bits);
    let init_time = init_start.elapsed();
    println!("Initialization time: {:.3}s", init_time.as_secs_f64());

    // Warm-up
    if args.verbose {
        println!("Warming up...");
    }
    for i in 0..1000.min(domain) {
        if args.inverse {
            let _ = prp.inverse(i);
        } else {
            let _ = prp.forward(i);
        }
    }

    // Benchmark
    if args.verbose {
        println!("Running benchmark...");
    }
    let start = Instant::now();
    
    if args.parallel && args.inverse {
        // Parallel batch mode (inverse only)
        let ys: Vec<u64> = (0..operations).map(|i| i % domain).collect();
        let chunk_size = batch_size.max(1024) as usize;
        let _ = prp.inverse_batch_parallel(&ys, chunk_size);
    } else if batch_size > 0 {
        // Batch mode
        let batch_size = batch_size as usize;
        let num_batches = (operations as usize + batch_size - 1) / batch_size;
        
        for batch_idx in 0..num_batches {
            let batch_start = (batch_idx * batch_size) as u64;
            let batch_end = ((batch_idx + 1) * batch_size).min(operations as usize) as u64;
            
            let ys: Vec<u64> = (batch_start..batch_end)
                .map(|i| i % domain)
                .collect();
            
            if args.inverse {
                let _ = prp.inverse_batch(&ys);
            } else {
                // Forward batch not implemented yet, fall back to sequential
                for &y in &ys {
                    let _ = prp.forward(y);
                }
            }
        }
    } else {
        // Sequential mode
        if args.inverse {
            for i in 0..operations {
                let x = i % domain;
                let _ = prp.inverse(x);
            }
        } else {
            for i in 0..operations {
                let x = i % domain;
                let _ = prp.forward(x);
            }
        }
    }

    let duration = start.elapsed();
    let ops_per_sec = operations as f64 / duration.as_secs_f64();
    let us_per_op = duration.as_micros() as f64 / operations as f64;

    println!("\nResults:");
    println!("Time: {:.3}s", duration.as_secs_f64());
    println!("Throughput: {:.0} ops/sec", ops_per_sec);
    println!("Latency: {:.2} us/op", us_per_op);

    // Memory estimate (rough)
    let level_count = (domain as f64).log2().ceil() as usize;
    let avg_rounds_per_level = (7.23 * (domain as f64).log2() 
        + 4.82 * security_bits as f64 
        + 4.82 * (level_count as f64).log2()).ceil() as usize;
    let total_keys = level_count * avg_rounds_per_level;
    let memory_bytes = total_keys * 8; // u64 keys
    println!("Estimated key memory: {:.2} KB", memory_bytes as f64 / 1024.0);

    Ok(())
}
