use crate::db::DB_ENTRY_U64_COUNT;
use crate::update_manager::DBUpdate;
use eyre::Result;
use reqwest::blocking::Client;
use serde::Deserialize;
use serde_json::json;
use std::collections::HashSet;
use tracing::warn;

#[derive(Clone)]
pub struct EthClient {
    url: String,
    client: Client,
}

#[derive(Deserialize)]
struct RpcResponse<T> {
    result: Option<T>,
    error: Option<serde_json::Value>,
    id: serde_json::Value,
}

#[derive(Deserialize)]
struct Block {
    transactions: Vec<Transaction>,
}

#[derive(Deserialize)]
struct Transaction {
    from: String,
    to: Option<String>,
}

impl EthClient {
    /// Creates a new EthClient configured to call the given Ethereum JSON-RPC endpoint.
    ///
    /// `url` is the HTTP(S) endpoint for JSON-RPC requests (e.g. "http://localhost:8545").
    /// The returned client uses a blocking HTTP client with a 120-second timeout.
    ///
    /// # Examples
    ///
    /// ```
    /// let client = EthClient::new("http://localhost:8545".to_string());
    /// // use client to call RPC methods...
    /// ```
    pub fn new(url: String) -> Self {
        Self {
            url,
            client: Client::builder()
                .timeout(std::time::Duration::from_secs(120))
                .build()
                .unwrap(),
        }
    }

    /// Send a single JSON-RPC request and return the parsed result.
    ///
    /// On success returns the deserialized RPC `result`. Returns an `Err` if the HTTP request or
    /// JSON parsing fails, if the RPC response contains an `error` field, or if the `result` field is `null`.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use serde_json::json;
    ///
    /// let client = EthClient::new("http://localhost:8545".to_string());
    /// let net_version: String = client.call("net_version", json!([])).unwrap();
    /// assert!(!net_version.is_empty());
    /// ```
    fn call<T: for<'de> Deserialize<'de>>(
        &self,
        method: &str,
        params: serde_json::Value,
    ) -> Result<T> {
        let body = json!({
            "jsonrpc": "2.0",
            "method": method,
            "params": params,
            "id": 1
        });

        let resp: RpcResponse<T> = self.client.post(&self.url).json(&body).send()?.json()?;

        if let Some(err) = resp.error {
            return Err(eyre::eyre!("RPC error for {}: {:?}", method, err));
        }

        resp.result
            .ok_or_else(|| eyre::eyre!("RPC method {} returned null result", method))
    }

    /// Sends the given JSON-RPC method calls in batched requests (chunked to 100 per batch) and
    /// returns a vector of per-call results aligned with the provided `params_list` order.
    ///
    /// Each entry in the returned vector corresponds to the same-position entry in `params_list`:
    /// an `Ok(T)` when the RPC returned a valid result for that call, or an `Err` when that call
    /// produced an RPC error. If the entire batch fails to parse or returns a single error object,
    /// this function returns an `Err`.
    ///
    /// # Examples
    ///
    /// ```ignore
    /// let params_list = vec![
    ///     serde_json::json!(["0xdeadbeef", "latest"]),
    ///     serde_json::json!(["0xcafebabe", "latest"]),
    /// ];
    /// let results: Vec<Result<serde_json::Value>> = client.call_batch("eth_getBalance", params_list)?;
    /// for res in results {
    ///     match res {
    ///         Ok(val) => println!("balance: {:?}", val),
    ///         Err(e) => eprintln!("rpc error: {}", e),
    ///     }
    /// }
    /// ```
    pub fn call_batch<T: for<'de> Deserialize<'de>>(
        &self,
        method: &str,
        params_list: Vec<serde_json::Value>,
    ) -> Result<Vec<Result<T>>> {
        let mut all_results = Vec::with_capacity(params_list.len());

        // Chunk size 100 (Erigon default limit)
        for chunk in params_list.chunks(100) {
            let batch: Vec<_> = chunk
                .iter()
                .enumerate()
                .map(|(i, params)| {
                    json!({
                        "jsonrpc": "2.0",
                        "method": method,
                        "params": params,
                        "id": i
                    })
                })
                .collect();

            let response_text = self.client.post(&self.url).json(&batch).send()?.text()?;

            // Try to parse as array
            if let Ok(resps) = serde_json::from_str::<Vec<RpcResponse<T>>>(&response_text) {
                let mut map = std::collections::HashMap::new();
                for r in resps {
                    let id =
                        r.id.as_u64()
                            .ok_or_else(|| eyre::eyre!("RPC response missing or invalid id"))?
                            as usize;
                    let val = if let Some(err) = r.error {
                        Err(eyre::eyre!("RPC Error: {:?}", err))
                    } else {
                        r.result
                            .ok_or_else(|| eyre::eyre!("RPC returned null result for id {}", id))
                    };
                    map.insert(id, val);
                }

                for i in 0..batch.len() {
                    all_results.push(
                        map.remove(&i)
                            .ok_or_else(|| eyre::eyre!("Missing response for id {}", i))?,
                    );
                }
            } else if let Ok(err_obj) = serde_json::from_str::<serde_json::Value>(&response_text) {
                return Err(eyre::eyre!("Batch RPC Failed: {:?}", err_obj));
            } else {
                return Err(eyre::eyre!("Invalid JSON response: {}", response_text));
            }
        }

        Ok(all_results)
    }

    pub fn block_number(&self) -> Result<u64> {
        let hex: String = self.call("eth_blockNumber", json!([]))?;
        u64::from_str_radix(hex.trim_start_matches("0x"), 16).map_err(|e| e.into())
    }

    pub fn get_block_transactions(&self, block_number: u64) -> Result<Vec<Transaction>> {
        let hex_num = format!("0x{:x}", block_number);
        let block: Block = self.call("eth_getBlockByNumber", json!([hex_num, true]))?;
        Ok(block.transactions)
    }

    pub fn get_balance(&self, address: &str, block_number: u64) -> Result<u128> {
        let hex_num = format!("0x{:x}", block_number);
        let hex: String = self.call("eth_getBalance", json!([address, hex_num]))?;
        u128::from_str_radix(hex.trim_start_matches("0x"), 16).map_err(|e| e.into())
    }
}

use crate::address_mapping::AddressMapping;

/// Returns balance change updates for tracked addresses touched by a block.
///
/// This queries the given `EthClient` for transactions in `block_number`, identifies the
/// touched addresses present in `address_mapping`, fetches their balances at that block,
/// and returns a `Vec<DBUpdate>` for each tracked address whose stored balance (via
/// `manager`) differs from the fetched balance.
///
/// # Examples
///
/// ```no_run
/// # use std::collections::HashMap;
/// # use crate::{EthClient, AddressMapping, DBUpdate};
/// // Assume `client`, `manager`, and `address_mapping` are initialized.
/// // let updates = fetch_updates_rpc(&client, 12345, &manager, &address_mapping).unwrap();
/// ```
pub fn fetch_updates_rpc(
    client: &EthClient,
    block_number: u64,
    manager: &crate::update_manager::UpdateManager,
    address_mapping: &AddressMapping,
) -> Result<Vec<DBUpdate>> {
    // 1. Get block transactions to find touched addresses
    let txs = client.get_block_transactions(block_number)?;

    let mut addresses = HashSet::new();
    for tx in txs {
        addresses.insert(tx.from.to_lowercase());
        if let Some(to) = tx.to {
            addresses.insert(to.to_lowercase());
        }
    }

    if addresses.is_empty() {
        return Ok(vec![]);
    }

    let mut updates = Vec::new();
    let addrs: Vec<String> = addresses.into_iter().collect();

    // Filter for tracked addresses
    let tracked_addrs: Vec<&String> = addrs
        .iter()
        .filter(|a| address_mapping.get(*a).is_some())
        .collect();

    if tracked_addrs.is_empty() {
        return Ok(vec![]);
    }

    // Batch fetch balances
    let hex_num = format!("0x{:x}", block_number);
    let params: Vec<serde_json::Value> =
        tracked_addrs.iter().map(|a| json!([a, hex_num])).collect();

    let balances: Vec<Result<String>> = client.call_batch("eth_getBalance", params)?;

    for (i, addr) in tracked_addrs.iter().enumerate() {
        match &balances[i] {
            Ok(hex_balance) => {
                let balance = u128::from_str_radix(hex_balance.trim_start_matches("0x"), 16)?;
                let index = address_mapping.get(*addr).unwrap(); // Safe because we filtered

                let balance_idx = index + 1;
                let old_balance_entry = manager
                    .get_value(balance_idx)
                    .unwrap_or([0; DB_ENTRY_U64_COUNT]);

                let mut new_balance_entry = [0u64; DB_ENTRY_U64_COUNT];
                new_balance_entry[0] = balance as u64;
                new_balance_entry[1] = (balance >> 64) as u64;

                if old_balance_entry != new_balance_entry {
                    updates.push(DBUpdate {
                        index: balance_idx,
                        old_value: old_balance_entry,
                        new_value: new_balance_entry,
                    });
                }
            }
            Err(e) => {
                warn!("Failed to fetch balance for {}: {}", addr, e);
            }
        }
    }

    Ok(updates)
}

/// Fetches balances for addresses touched by transactions in a block and returns their mapped indices with balances.
///
/// This queries the block's transactions, collects unique addresses touched (from/to), filters them by `address_mapping`, batch-requests each address balance at `block_number`, and returns a vector of (index, balance) for each tracked address whose balance was successfully parsed.
///
/// # Parameters
/// - `client`: Ethereum RPC client used to fetch block data and balances.
/// - `block_number`: Block number to inspect and use when querying balances.
/// - `address_mapping`: Mapping from lowercase hex address strings to stored indices; only addresses present in this mapping are returned.
///
/// # Returns
/// A `Vec<(u64, u128)>` where each tuple is `(index, balance)` — `index` is the mapped index from `address_mapping` and `balance` is the account balance at `block_number` parsed as a `u128`.
///
/// # Examples
///
/// ```
/// // Assume `client` and `address_mapping` are previously constructed:
/// // let client = EthClient::new("https://mainnet.infura.io".into());
/// // let address_mapping = AddressMapping::from_iter(vec![("0xabc...".to_string(), 42u64)]);
/// let states = fetch_touched_states(&client, 12_345_678u64, &address_mapping).unwrap();
/// for (idx, balance) in states {
///     println!("index={} balance={}", idx, balance);
/// }
/// ```
pub fn fetch_touched_states(
    client: &EthClient,
    block_number: u64,
    address_mapping: &AddressMapping,
) -> Result<Vec<(u64, u128)>> {
    // 1. Get block transactions
    let txs = client.get_block_transactions(block_number)?;

    let mut addresses = HashSet::new();
    for tx in txs {
        addresses.insert(tx.from.to_lowercase());
        if let Some(to) = tx.to {
            addresses.insert(to.to_lowercase());
        }
    }

    let addrs: Vec<String> = addresses.into_iter().collect();

    // Filter and Map to Indices
    // We store (StringAddr, Index) pairs to query RPC then return Index
    let mut tracked = Vec::with_capacity(addrs.len());
    for a in &addrs {
        if let Some(idx) = address_mapping.get(a) {
            tracked.push((a.clone(), idx));
        }
    }

    if tracked.is_empty() {
        return Ok(vec![]);
    }

    // Batch fetch balances
    let hex_num = format!("0x{:x}", block_number);
    let params: Vec<serde_json::Value> = tracked.iter().map(|(a, _)| json!([a, hex_num])).collect();

    let balances: Vec<Result<String>> = client.call_batch("eth_getBalance", params)?;

    let mut results = Vec::with_capacity(tracked.len());
    for (i, (addr, idx)) in tracked.iter().enumerate() {
        match &balances[i] {
            Ok(hex_balance) => {
                if let Ok(balance) = u128::from_str_radix(hex_balance.trim_start_matches("0x"), 16)
                {
                    results.push((*idx, balance));
                }
            }
            Err(e) => {
                warn!("Failed to fetch balance for {}: {}", addr, e);
            }
        }
    }

    Ok(results)
}
