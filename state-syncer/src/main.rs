mod address_mapping;
mod config;
mod constant_time;
mod db;
mod iprf;
mod rpc;
mod update_manager;

use address_mapping::AddressMapping;
use clap::Parser;
use config::Config;
use db::{Database, DB_ENTRY_U64_COUNT};
use eyre::Result;
use futures::StreamExt;
use rpc::EthClient;
use serde::Deserialize;
use std::collections::HashMap;
use std::fs::File;
use std::io::Read;
use std::io::Write;
use std::path::Path;
use std::sync::Arc;
use std::time::Duration;
use tracing::{info, warn};
use update_manager::{AccountDelta, DBUpdate, UpdateManager};

#[derive(Debug, Deserialize)]
struct Metadata {
    block: u64,
}

/// Program entry point that initializes logging, metrics, optional RPC client and address
/// mapping, loads the local database, and then continuously processes blocks to produce
/// and persist state deltas either in simulated mode or by fetching touched states from
/// an Ethereum RPC provider.
///
/// In simulated mode, the process generates deterministic synthetic updates per block,
/// applies them to the local database, and writes a delta file for each block. In real
/// RPC mode, the process concurrently fetches touched states for upcoming blocks (preserving
/// in-order application), computes and applies updates that change state, and writes per-block
/// delta files. The function blocks until the program exits.
///
/// # Examples
///
/// ```text
/// # To run the process as a binary:
/// cargo run --release
/// ```
#[tokio::main]
async fn main() -> Result<()> {
    tracing_subscriber::fmt::init();
    let cfg = Config::parse();

    info!(
        "State Syncer starting (rpc={}, simulated={})",
        cfg.rpc_url, cfg.simulated
    );

    let rpc_client = if !cfg.simulated {
        Some(EthClient::new(cfg.rpc_url.clone()))
    } else {
        None
    };

    // 1. Start Metrics/Health Server
    let metrics_port = cfg.http_port;
    tokio::spawn(async move {
        start_metrics_server(metrics_port).await;
    });

    // 2. Load Address Mapping
    let mut address_mapping = None;
    if !cfg.simulated {
        info!(
            "Loading address mapping from {:?}",
            cfg.address_mapping_path
        );
        let mapping = AddressMapping::load(&cfg.address_mapping_path)?;
        info!("Loaded {} addresses (mmap)", mapping.len());
        address_mapping = Some(Arc::new(mapping));
    }

    // 3. Load Database
    info!("Loading database from {:?}", cfg.database_path);
    let mut db = Database::load(&cfg.database_path)?;
    info!(
        "Loaded database: {} entries, chunk_size={}, set_size={}",
        db.num_entries, db.chunk_size, db.set_size
    );

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
    if cfg.simulated {
        // Simulation loop (kept simple)
        loop {
            let next_block = last_block + 1;
            let raw = simulate_updates(manager.db_size(), next_block);
            let updates: Vec<DBUpdate> = raw
                .into_iter()
                .map(|(idx, new_val)| {
                    let old_val = manager.get_value(idx).unwrap_or([0; 4]);
                    DBUpdate {
                        index: idx,
                        old_value: old_val,
                        new_value: new_val,
                    }
                })
                .collect();

            let (deltas, duration) = manager.apply_updates(&updates);
            info!(
                "Block {}: {} updates, {} deltas ({:?})",
                next_block,
                updates.len(),
                deltas.len(),
                duration
            );
            manager.flush()?;
            let delta_filename = format!("delta-{:06}.bin", next_block);
            let delta_path = cfg.delta_dir.join(delta_filename);
            std::fs::create_dir_all(&cfg.delta_dir)?;
            save_delta(&delta_path, &deltas)?;
            last_block = next_block;
            tokio::time::sleep(Duration::from_millis(100)).await;
        }
    } else {
        // Real RPC Parallel Loop
        let mapping = address_mapping.unwrap(); // Arc<AddressMapping>
        let client = rpc_client.unwrap();

        // Create a stream of futures
        // Note: buffer_unordered allows fetching out of order, but we iterate results in order?
        // No, buffer_unordered returns items as they complete.
        // We need `buffered` (ordered) to ensure we process block N before N+1?
        // Yes! We cannot apply block N+1 updates before Block N updates.
        // So we use `buffered(concurrency)`. This starts N tasks, but returns them in order 1, 2, 3...

        let mut stream = futures::stream::iter((last_block + 1)..)
            .map(|block| {
                let c = client.clone();
                let m = mapping.clone();
                async move {
                    loop {
                        // Fetch block header first to check if ready?
                        // Or just fetch updates. If block doesn't exist, RPC error/null.
                        match c.block_number() {
                            Ok(head) => {
                                if head < block {
                                    tokio::time::sleep(Duration::from_secs(1)).await;
                                    continue;
                                }
                            }
                            Err(_) => {
                                tokio::time::sleep(Duration::from_secs(1)).await;
                                continue;
                            }
                        }

                        // Fetch
                        // Note: rpc::fetch_touched_states is synchronous (blocking reqwest).
                        // We need to wrap it in spawn_blocking?
                        // Or rewrite rpc to async reqwest.
                        // Since we are in async context, blocking calls block the executor thread.
                        // With `concurrency=10`, if we block, we block all 10?
                        // No, we map to futures.
                        // But `fetch_touched_states` uses `blocking::Client`.

                        let res = {
                            let c_inner = c.clone();
                            let m_inner = m.clone();
                            tokio::task::spawn_blocking(move || {
                                rpc::fetch_touched_states(&c_inner, block, &m_inner)
                            })
                            .await
                            .unwrap()
                        };

                        match res {
                            Ok(data) => return (block, data),
                            Err(e) => {
                                warn!("Fetch failed for block {}: {}. Retrying...", block, e);
                                tokio::time::sleep(Duration::from_secs(1)).await;
                            }
                        }
                    }
                }
            })
            .buffered(cfg.concurrency);

        while let Some((block, states)) = stream.next().await {
            // Sequential Processing
            if states.is_empty() {
                info!("Block {}: No updates found", block);
                // Still need to save empty delta? Or skip?
                // Plinko spec: client likely expects delta for every block to sync forward?
                // Or just skip.
                // Let's skip saving if empty, but logging is good.
            } else {
                let mut updates = Vec::with_capacity(states.len());
                for (idx, new_balance_u128) in states {
                    let balance_idx = idx + 1;
                    let old_val = manager.get_value(balance_idx).unwrap_or([0; 4]);
                    let mut new_val = [0u64; 4];
                    new_val[0] = new_balance_u128 as u64;
                    new_val[1] = (new_balance_u128 >> 64) as u64;

                    if old_val != new_val {
                        updates.push(DBUpdate {
                            index: balance_idx,
                            old_value: old_val,
                            new_value: new_val,
                        });
                    }
                }

                if !updates.is_empty() {
                    let (deltas, duration) = manager.apply_updates(&updates);
                    info!(
                        "Block {}: {} updates, {} deltas ({:?})",
                        block,
                        updates.len(),
                        deltas.len(),
                        duration
                    );
                    manager.flush()?;
                    let delta_filename = format!("delta-{:06}.bin", block);
                    let delta_path = cfg.delta_dir.join(delta_filename);
                    std::fs::create_dir_all(&cfg.delta_dir)?;
                    save_delta(&delta_path, &deltas)?;
                } else {
                    info!("Block {}: No state changes", block);
                }
            }
        }
    }

    Ok(())
}

/// Generates a deterministic set of simulated account updates for a given block.
///
/// Each update is a tuple of (index, [u64; 4]) where `index` is an account index within
/// the range [0, db_size) and the array encodes the new 4-word account value.
/// If `db_size` is 0, an empty vector is returned.
///
/// # Returns
///
/// A vector of up to 2000 simulated updates for the block. Each update's index is computed
/// as `(block * 2000 + i) % db_size` and the value is `[block * 1000 + i, 0, 0, 0]`.
///
/// # Examples
///
/// ```
/// // small database and block for demonstration
/// let updates = simulate_updates(10, 2);
/// assert!(!updates.is_empty());
/// // first update index and value
/// let (idx0, val0) = updates[0];
/// assert_eq!(idx0, (2 * 2000 + 0) % 10);
/// assert_eq!(val0, [2 * 1000 + 0, 0, 0, 0]);
/// // empty when db_size == 0
/// let empty = simulate_updates(0, 1);
/// assert!(empty.is_empty());
/// ```
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

/// Writes `deltas` to `path` as a binary delta file.
///
/// The file format is:
/// - u64: number of delta entries (little-endian)
/// - u64: entry length in u64 words (little-endian, equal to `DB_ENTRY_U64_COUNT`)
/// - repeated per entry:
///   - u64: account index (little-endian)
///   - `DB_ENTRY_U64_COUNT` × u64: four 64-bit words from `AccountDelta::delta` (little-endian)
///
/// # Examples
///
/// ```
/// # use std::path::Path;
/// # // `AccountDelta` and `save_delta` are assumed to be in scope for this example.
/// let deltas: Vec<AccountDelta> = Vec::new();
/// let tmp = std::env::temp_dir().join("delta-example.bin");
/// save_delta(tmp.as_path(), &deltas).unwrap();
/// ```
///
/// # Errors
///
/// Returns an `Err` if creating, writing, or flushing the file fails.
fn save_delta(path: &Path, deltas: &[AccountDelta]) -> Result<()> {
    let mut file = File::create(path)?;

    // Header: Count (u64) + EntryLength (u64)
    file.write_all(&(deltas.len() as u64).to_le_bytes())?;
    file.write_all(&(DB_ENTRY_U64_COUNT as u64).to_le_bytes())?;

    for delta in deltas {
        file.write_all(&delta.account_index.to_le_bytes())?;
        for val in delta.delta {
            file.write_all(&val.to_le_bytes())?;
        }
    }

    file.flush()?;
    Ok(())
}

/// Starts an HTTP metrics and health server bound to 0.0.0.0 on the given port.
///
/// The server exposes two routes:
/// - `GET /health` which responds with `OK`
/// - `GET /metrics` which responds with an empty JSON object (`{}`)
///
/// # Examples
///
/// ```
/// # use tokio::runtime::Runtime;
/// # let rt = Runtime::new().unwrap();
/// rt.spawn(async {
///     // Runs the metrics server on port 9100 in the background.
///     start_metrics_server(9100).await;
/// });
/// ```
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
