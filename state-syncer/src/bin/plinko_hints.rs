//! Plinko PIR Hint Generator - see docs/hint_generation.md for details.

mod hint_gen;

use clap::Parser;
use indicatif::{ProgressBar, ProgressStyle};
use memmap2::MmapOptions;
use state_syncer::iprf::{Iprf, IprfTee};
use std::fs::File;
use std::time::Instant;

use hint_gen::*;

fn main() -> eyre::Result<()> {
    let args = Args::parse();
    validate_args(&args)?;

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

    let geom = compute_geometry(db_bytes.len(), &args)?;
    println!("Total Entries (N): {}", geom.n_entries);

    println!("\nPlinko Parameters:");
    println!("  Entries per block (w): {}", geom.w);
    println!("  Number of blocks (c): {}", geom.c);
    println!("  Lambda: {}", args.lambda);

    let params = HintParams::from_args(&args, geom.w);
    if args.constant_time {
        validate_hint_params(&params, geom.w)?;
    }
    println!("\nHint Structure:");
    println!("  Regular hints: {}", params.num_regular);
    println!("  Backup hints: {}", params.num_backup);

    let master_seed = parse_or_generate_seed(&args)?;
    let start = Instant::now();

    println!("\n[1/4] Generating {} iPRF keys...", geom.c);
    let block_keys = derive_block_keys(&master_seed, geom.c);

    println!("[2/4] Initializing {} regular hints...", params.num_regular);
    println!("[3/4] Initializing {} backup hints...", params.num_backup);
    let (mut regular_hints, regular_hint_blocks, mut backup_hints, backup_hint_blocks) =
        init_hints(&master_seed, geom.c, &params);

    println!("[4/4] Streaming database ({} entries)...", geom.n_effective);
    if args.constant_time {
        println!("  [CT MODE] Using constant-time implementation for TEE");
    }

    let pb = ProgressBar::new(geom.n_effective as u64);
    pb.set_style(
        ProgressStyle::default_bar()
            .template(
                "{spinner:.green} [{elapsed_precise}] [{bar:40.cyan/blue}] {pos}/{len} ({eta})",
            )
            .unwrap()
            .progress_chars("#>-"),
    );

    if args.constant_time {
        let block_iprfs_ct: Vec<IprfTee> = block_keys
            .iter()
            .map(|key| IprfTee::new(*key, params.total_hints as u64, geom.w as u64))
            .collect();

        let regular_bitsets: Vec<BlockBitset> = regular_hint_blocks
            .iter()
            .map(|blocks| BlockBitset::from_sorted_blocks(blocks, geom.c))
            .collect();
        let backup_bitsets: Vec<BlockBitset> = backup_hint_blocks
            .iter()
            .map(|blocks| BlockBitset::from_sorted_blocks(blocks, geom.c))
            .collect();

        hint_gen::ct_path::process_entries_ct(
            db_bytes,
            geom.n_entries,
            geom.n_effective,
            geom.w,
            params.num_regular,
            params.num_backup,
            &block_iprfs_ct,
            &regular_bitsets,
            &backup_bitsets,
            &mut regular_hints,
            &mut backup_hints,
            |i| pb.set_position(i as u64),
        );
    } else {
        let block_iprfs: Vec<Iprf> = block_keys
            .iter()
            .map(|key| Iprf::new(*key, params.total_hints as u64, geom.w as u64))
            .collect();

        hint_gen::fast_path::process_entries_fast(
            db_bytes,
            geom.n_entries,
            geom.n_effective,
            geom.w,
            geom.c,
            params.num_regular,
            params.num_backup,
            &block_iprfs,
            &regular_hint_blocks,
            &backup_hint_blocks,
            &mut regular_hints,
            &mut backup_hints,
            |i| pb.set_position(i as u64),
        );
    }

    pb.finish_with_message("Done");

    let duration = start.elapsed();
    print_results(
        duration,
        file_len,
        &regular_hints,
        &backup_hints,
        &params,
        &block_keys,
        geom.w,
        geom.c,
    );

    Ok(())
}
