mod config;
mod db;
mod iprf;
mod update_manager;

use clap::Parser;
use config::Config;
use db::{Database, DB_ENTRY_U64_COUNT};
use update_manager::{UpdateManager, DBUpdate, HintDelta};
use eyre::Result;
use std::time::Duration;
use tracing::info;
use std::path::Path;
use std::fs::File;
use std::io::Write;
use serde::Deserialize;

#[derive(Debug, Deserialize)]
struct Metadata {
    block: u64,
}

#[tokio::main]
async fn main() -> Result<()> {
    tracing_subscriber::fmt::init();
    let cfg = Config::parse();

    info!("State Syncer starting (rpc={}, simulated={})", cfg.rpc_url, cfg.simulated);

    // 1. Start Metrics/Health Server
    let metrics_port = cfg.http_port;
    tokio::spawn(async move {
        start_metrics_server(metrics_port).await;
    });

    // 2. Load Address Mapping (Mock for now as we don't use it in simulation)
    // info!("Loading address mapping from {:?}", cfg.address_mapping_path);
    
    // 3. Load Database
    info!("Loading database from {:?}", cfg.database_path);
    let mut db = Database::load(&cfg.database_path)?;
    info!("Loaded database: {} entries, chunk_size={}, set_size={}", 
        db.num_entries, db.chunk_size, db.set_size);
    
    // 4. Setup Update Manager
    let mut manager = UpdateManager::new(&mut db);
    // manager.enable_cache_mode(); // Optional: takes time but speeds up updates

    // 5. Determine Start Block
    let mut last_block = if let Some(b) = cfg.start_block {
        b
    } else {
        // Try to find metadata.json in the same dir as database
        let meta_path = cfg.database_path.parent().unwrap().join("metadata.json");
        if meta_path.exists() {
            let content = std::fs::read_to_string(&meta_path)?;
            let meta: Metadata = serde_json::from_str(&content)?;
            info!("Found metadata.json: starting from block {}", meta.block);
            meta.block
        } else {
            info!("No start block or metadata found. Defaulting to 0.");
            0
        }
    };

    // 6. Main Loop
    loop {
        let next_block = last_block + 1;
        
        // Check head block from RPC
        if !cfg.simulated {
             // TODO: Implement RPC head check
        }

        // Fetch updates
        let updates: Vec<DBUpdate> = if cfg.simulated {
            let raw = simulate_updates(manager.db_size(), next_block);
            raw.into_iter().map(|(idx, new_val)| {
                let old_val = manager.get_value(idx).unwrap_or([0; 4]);
                DBUpdate {
                    index: idx,
                    old_value: old_val,
                    new_value: new_val,
                }
            }).collect()
        } else {
            // TODO: Implement RPC fetch
            vec![]
        };

        if updates.is_empty() {
            if cfg.simulated {
                tokio::time::sleep(cfg.poll_interval()).await;
                last_block = next_block;
                continue;
            } else {
                tokio::time::sleep(cfg.poll_interval()).await;
                continue;
            }
        }

        // Apply updates
        let (deltas, duration) = manager.apply_updates(&updates);
        info!("Block {}: {} updates, {} deltas ({:?})", next_block, updates.len(), deltas.len(), duration);

        // Flush DB & Save Delta
        manager.flush()?;
        
        let delta_filename = format!("delta-{:06}.bin", next_block);
        let delta_path = cfg.delta_dir.join(delta_filename);
        // Ensure dir exists
        std::fs::create_dir_all(&cfg.delta_dir)?;
        save_delta(&delta_path, &deltas)?;

        // Placeholder increment
        last_block = next_block;
        
        if cfg.simulated {
            tokio::time::sleep(Duration::from_millis(100)).await; // Fast simulation
        }
    }
}

fn simulate_updates(db_size: u64, block: u64) -> Vec<(u64, [u64; 4])> {
    if db_size == 0 {
        return vec![];
    }
    let count = 2000;
    let mut updates = Vec::with_capacity(count);
    
    for i in 0..count {
        let index = (block * count as u64 + i as u64) % db_size;
        updates.push((index, [block * 1000 + i as u64, 0, 0, 0]));
    }
    updates
}

fn save_delta(path: &Path, deltas: &[HintDelta]) -> Result<()> {
    let mut file = File::create(path)?;
    
    // Header: Count (u64) + EntryLength (u64)
    file.write_all(&(deltas.len() as u64).to_le_bytes())?;
    file.write_all(&(DB_ENTRY_U64_COUNT as u64).to_le_bytes())?;
    
    for delta in deltas {
        file.write_all(&delta.hint_set_id.to_le_bytes())?;
        file.write_all(&(if delta.is_backup_set { 1u64 } else { 0u64 }).to_le_bytes())?;
        for val in delta.delta {
            file.write_all(&val.to_le_bytes())?;
        }
    }
    
    file.flush()?;
    Ok(())
}

async fn start_metrics_server(port: u16) {
    use axum::{routing::get, Router};
    
    let app = Router::new()
        .route("/health", get(|| async { "OK" }))
        .route("/metrics", get(|| async { "{}" }));

    let addr = format!("0.0.0.0:{}", port);
    info!("Metrics server listening on {}", addr);
    let listener = tokio::net::TcpListener::bind(addr).await.unwrap();
    axum::serve(listener, app).await.unwrap();
}
