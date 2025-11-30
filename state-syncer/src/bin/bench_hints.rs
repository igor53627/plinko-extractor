use std::time::Instant;
use std::path::PathBuf;
use std::fs::File;
use memmap2::MmapOptions;
use clap::Parser;
use indicatif::{ProgressBar, ProgressStyle};

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    /// Path to the database file
    #[arg(short, long, default_value = "/mnt/plinko/data/database.bin")]
    db_path: PathBuf,

    /// Block size in bytes
    #[arg(short, long)]
    block_size: usize,
}

fn main() -> eyre::Result<()> {
    let args = Args::parse();
    
    println!("Plinko Hint Generation Benchmark");
    println!("--------------------------------");
    println!("Database: {:?}", args.db_path);
    println!("Block Size: {} bytes", args.block_size);

    let file = File::open(&args.db_path)?;
    let file_len = file.metadata()?.len();
    println!("DB Size: {:.2} GB", file_len as f64 / 1024.0 / 1024.0 / 1024.0);

    // Memory Map
    let mmap = unsafe { MmapOptions::new().map(&file)? };

    // Calculate Dimensions
    let num_rows = file_len / args.block_size as u64;
    let num_hints = (num_rows as f64).sqrt().ceil() as usize;
    
    let hint_storage_bytes = num_hints * args.block_size;
    println!("Total Rows (N): {}", num_rows);
    println!("Sqrt(N) / Hint Count: {}", num_hints);
    println!("Client Hint Storage: {:.2} MB", hint_storage_bytes as f64 / 1024.0 / 1024.0);

    // Allocate Hints (Simulating Client Memory)
    // Using u8 for raw byte storage, but operations would be u64 aligned usually.
    // We'll iterate as u64 words for performance realism.
    let u64s_per_block = args.block_size / 8;
    let mut hints = vec![0u64; num_hints * u64s_per_block];

    println!("\nStarting processing...");
    let start = Instant::now();
    
    let pb = ProgressBar::new(num_rows);
    pb.set_style(ProgressStyle::default_bar()
        .template("{spinner:.green} [{elapsed_precise}] [{bar:40.cyan/blue}] {pos}/{len} ({eta}) {msg}")
        .unwrap()
        .progress_chars("#>-"));

    // Simulation Loop
    // We iterate over the memory mapped file
    // We treat it as &[u64] to be faster
    let (_, db_u64, _) = unsafe { mmap.align_to::<u64>() };
    
    // Simple LCG for deterministic "random" scalars
    let mut rng_state: u64 = 123456789;
    
    // Optimization: Process in chunks to be cache friendly if possible, 
    // but the naive algorithm visits hints randomly if we do row-by-row.
    // Actually, Plinko usually does linear scan of DB and linear scan of Hints?
    // No, simple PIR is A * D. D is (sqrt(N) x sqrt(N)).
    // If we stream D (the database) linearly, we hit the Hint matrix in a column-major way?
    // Let's stick to the simple logic: 
    // For each row `i` in DB:
    //    TargetHintIndex = i % num_hints;
    //    Scalar = Random(i);
    //    Hints[TargetHintIndex] += Row[i] * Scalar;
    
    // This simulates the "scatter" write pattern which might be the bottleneck.
    
    for (row_idx, row_chunk) in db_u64.chunks(u64s_per_block).enumerate() {
        if row_idx % 10000 == 0 {
            pb.set_position(row_idx as u64);
        }

        // Mock Scalar Gen
        rng_state = rng_state.wrapping_mul(6364136223846793005).wrapping_add(1);
        let scalar = rng_state;

        let target_hint_idx = row_idx % num_hints;
        let hint_offset = target_hint_idx * u64s_per_block;
        
        // Vector update
        for (k, &val) in row_chunk.iter().enumerate() {
            // Simulated Math: Hint += DB_Val * Scalar
            // Using wrapping_add/mul to avoid overflow checks overhead
            let contribution = val.wrapping_mul(scalar);
            hints[hint_offset + k] = hints[hint_offset + k].wrapping_add(contribution);
        }
    }

    pb.finish_with_message("Done");
    let duration = start.elapsed();
    
    let throughput_mb = (file_len as f64 / 1024.0 / 1024.0) / duration.as_secs_f64();
    
    println!("\nResults:");
    println!("Time Taken: {:.2?}", duration);
    println!("Throughput: {:.2} MB/s", throughput_mb);
    println!("Final Hint Storage: {:.2} MB", hint_storage_bytes as f64 / 1024.0 / 1024.0);

    Ok(())
}
