use alloy_primitives::U256;
use clap::Parser;
use eyre::Result;
use indicatif::{ProgressBar, ProgressStyle};
use reth_db::{
    cursor::{DbCursorRO, DbDupCursorRO},
    database::Database,
    open_db_read_only,
    tables,
    transaction::DbTx,
};
use std::{
    fs::File,
    io::{BufWriter, Write},
    path::PathBuf,
    time::{Duration, Instant},
};

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    /// Path to the Reth database folder (e.g. /home/user/.local/share/reth/mainnet/db)
    #[arg(long, default_value = "/var/lib/reth/mainnet/db")]
    db_path: PathBuf,

    /// Output directory for artifacts
    #[arg(long, default_value = "data")]
    output_dir: PathBuf,

    /// Limit the number of accounts/slots to extract (useful for testing)
    #[arg(long)]
    limit: Option<usize>,

    /// Count items only, do not write artifacts
    #[arg(long, default_value_t = false)]
    count_only: bool,

    /// Batch size for transactions (items per transaction)
    #[arg(long, default_value_t = 100_000)]
    batch_size: usize,
}

fn main() -> Result<()> {
    tracing_subscriber::fmt::init();
    let args = Args::parse();

    let now = || chrono::Local::now().format("%Y-%m-%d %H:%M:%S");

    println!("[{}] Opening database at {:?}", now(), args.db_path);
    
    // We keep the DB open, but we will open/close TXs
    let db = open_db_read_only(&args.db_path, Default::default())?;

    let (mut db_writer, mut acc_map_writer, mut sto_map_writer) = if !args.count_only {
        // Create output directory
        std::fs::create_dir_all(&args.output_dir)?;
        let db_file_path = args.output_dir.join("database.bin");
        let acc_map_path = args.output_dir.join("account-mapping.bin");
        let sto_map_path = args.output_dir.join("storage-mapping.bin");

        println!("[{}] Writing outputs to:", now());
        println!("  Database: {:?}", db_file_path);
        println!("  Acc Map:  {:?}", acc_map_path);
        println!("  Sto Map:  {:?}", sto_map_path);

        (
            Some(BufWriter::new(File::create(&db_file_path)?)),
            Some(BufWriter::new(File::create(&acc_map_path)?)),
            Some(BufWriter::new(File::create(&sto_map_path)?))
        )
    } else {
        println!("[{}] Running in COUNT-ONLY mode. No files will be written.", now());
        (None, None, None)
    };

    // Setup progress bar
    let pb = ProgressBar::new_spinner();
    pb.set_style(ProgressStyle::default_spinner()
        .template("{spinner:.green} [{elapsed_precise}] {msg}")
        .unwrap());

    let limit = args.limit.unwrap_or(usize::MAX);
    let batch_size = args.batch_size;

    // --- PROCESS ACCOUNTS ---
    println!("[{}] Processing Accounts...", now());
    let mut count_acc = 0;
    let mut total_indices = 0;
    let mut last_acc_key = None;

    loop {
        if count_acc >= limit {
            break;
        }

        let tx = db.tx()?;
        let mut cursor = tx.cursor_read::<tables::PlainAccountState>()?;
        
        // Resume from last key
        let walker = if let Some(key) = last_acc_key.clone() {
            let mut w = cursor.walk(Some(key))?;
            // Skip the first element if it matches the last key we processed
            if let Some(Ok((addr, _))) = w.next() {
                if addr != key {
                    // If it's different, we shouldn't have skipped it.
                    drop(w);
                    let mut w2 = cursor.walk(Some(key))?;
                    w2
                } else {
                    w
                }
            } else {
                w
            }
        } else {
            cursor.walk(None)?
        };

        let mut batch_count = 0;
        let mut current_acc_key = None;

        for entry in walker {
            let (address, account) = entry?;
            
            // Double check skipping
            if let Some(last) = &last_acc_key {
                if &address == last {
                    continue;
                }
            }

            if count_acc >= limit {
                break;
            }

            // --- WRITE DATABASE ENTRY ---
            if let Some(writer) = db_writer.as_mut() {
                // 1. Nonce (u64 -> 32 bytes)
                let mut nonce_bytes = [0u8; 32];
                nonce_bytes[0..8].copy_from_slice(&account.nonce.to_le_bytes());
                writer.write_all(&nonce_bytes)?;

                // 2. Balance (u256 -> 32 bytes)
                writer.write_all(&account.balance.to_le_bytes::<32>())?;

                // 3. Bytecode Hash (Option<B256> -> 32 bytes)
                let code_hash = account.bytecode_hash.unwrap_or_default();
                writer.write_all(code_hash.as_slice())?;
                
                // 4. Padding (Reserved / StorageRoot placeholder)
                writer.write_all(&[0u8; 32])?;
            }

            // --- WRITE MAPPING ---
            if let Some(writer) = acc_map_writer.as_mut() {
                // Address (20) + Index (4)
                writer.write_all(address.as_slice())?;
                writer.write_all(&(total_indices as u32).to_le_bytes())?;
            }

            total_indices += 4;
            count_acc += 1;
            batch_count += 1;
            current_acc_key = Some(address);

            if count_acc % 10000 == 0 {
                pb.set_message(format!("Acc: {}, Sto: 0", count_acc));
                pb.inc(1);
            }

            if batch_count >= batch_size {
                break;
            }
        }

        // End of batch
        if batch_count == 0 {
            break;
        }
        
        last_acc_key = current_acc_key;
        drop(tx); // Close transaction
    }
    
    println!("[{}] Processed {} accounts. Current Index: {}", now(), count_acc, total_indices);

    // --- PROCESS STORAGE ---
    println!("[{}] Processing Storage...", now());
    let mut count_sto = 0;
    let mut last_sto_addr = None;

    loop {
        if count_sto >= limit {
            break;
        }

        let tx = db.tx()?;
        let mut cursor = tx.cursor_dup_read::<tables::PlainStorageState>()?;
        
        // Resume Logic for Storage
        let walker = if let Some(addr) = last_sto_addr.clone() {
            // Try to seek to the address
            if let Some((_k, _)) = cursor.seek_exact(addr)? {
                // If found, jump to next unique key
                if let Some((next_k, _)) = cursor.next_no_dup()? {
                    cursor.walk(Some(next_k))?
                } else {
                    // End of database
                    break;
                }
            } else {
                // If `addr` not found, just walk from `addr` and filtering will handle it
                cursor.walk(Some(addr))?
            }
        } else {
            cursor.walk(None)?
        };

        let mut batch_count = 0;
        let mut current_addr = None;

        for entry in walker {
            let (address, storage_entry) = entry?;

            // Robust skipping: if we are still seeing the old address, skip it
            if let Some(last) = &last_sto_addr {
                if &address == last {
                    continue;
                }
            }

            // Check if we crossed a boundary and should stop for this batch
            if let Some(curr) = current_addr {
                if address != curr && batch_count >= batch_size {
                    break;
                }
            }
            
            current_addr = Some(address);

            if count_sto >= limit {
                break;
            }

            // --- WRITE DATABASE ENTRY ---
            if let Some(writer) = db_writer.as_mut() {
                writer.write_all(&storage_entry.value.to_le_bytes::<32>())?;
            }

            // --- WRITE MAPPING ---
            if let Some(writer) = sto_map_writer.as_mut() {
                writer.write_all(address.as_slice())?;
                writer.write_all(storage_entry.key.as_slice())?;
                writer.write_all(&(total_indices as u32).to_le_bytes())?;
            }

            total_indices += 1;
            count_sto += 1;
            batch_count += 1;

            if count_sto % 10000 == 0 {
                pb.set_message(format!("Acc: {}, Sto: {}", count_acc, count_sto));
                pb.inc(1);
            }
        }

        if batch_count == 0 {
            break;
        }

        last_sto_addr = current_addr;
        drop(tx);
    }

    pb.finish_with_message(format!("Done! Acc: {}, Sto: {}, Total Indices: {}", count_acc, count_sto, total_indices));
    
    if let Some(mut writer) = db_writer { writer.flush()?; }
    if let Some(mut writer) = acc_map_writer { writer.flush()?; }
    if let Some(mut writer) = sto_map_writer { writer.flush()?; }

    println!("[{}] Extraction complete.", now());

    Ok(())
}
