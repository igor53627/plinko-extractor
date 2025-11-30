use eyre::Result;
use reqwest::blocking::Client;
use serde_json::json;
use serde::Deserialize;
use crate::update_manager::DBUpdate;
use crate::db::DB_ENTRY_U64_COUNT;
use std::collections::HashSet;

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
    pub fn new(url: String) -> Self {
        Self {
            url,
            client: Client::builder()
                .timeout(std::time::Duration::from_secs(120))
                .build()
                .unwrap(),
        }
    }

    fn call<T: for<'de> Deserialize<'de>>(&self, method: &str, params: serde_json::Value) -> Result<T> {
        let body = json!({
            "jsonrpc": "2.0",
            "method": method,
            "params": params,
            "id": 1
        });

        let resp: RpcResponse<T> = self.client.post(&self.url)
            .json(&body)
            .send()?
            .json()?;

        if let Some(err) = resp.error {
            return Err(eyre::eyre!("RPC Error: {:?}", err));
        }
        
        resp.result.ok_or_else(|| eyre::eyre!("RPC returned null result"))
    }

    pub fn call_batch<T: for<'de> Deserialize<'de>>(&self, method: &str, params_list: Vec<serde_json::Value>) -> Result<Vec<Result<T>>> {
        let mut all_results = Vec::with_capacity(params_list.len());
        
        // Chunk size 100 (Erigon default limit)
        for chunk in params_list.chunks(100) {
            let batch: Vec<_> = chunk.iter().enumerate().map(|(i, params)| {
                json!({
                    "jsonrpc": "2.0",
                    "method": method,
                    "params": params,
                    "id": i
                })
            }).collect();

            let response_text = self.client.post(&self.url)
                .json(&batch)
                .send()?
                .text()?;

            // Try to parse as array
            if let Ok(resps) = serde_json::from_str::<Vec<RpcResponse<T>>>(&response_text) {
                let mut map = std::collections::HashMap::new();
                for r in resps {
                    let id = r.id.as_u64().unwrap() as usize;
                    let val = if let Some(err) = r.error {
                        Err(eyre::eyre!("RPC Error: {:?}", err))
                    } else {
                        Ok(r.result.unwrap())
                    };
                    map.insert(id, val);
                }
                
                for i in 0..batch.len() {
                    all_results.push(map.remove(&i).ok_or_else(|| eyre::eyre!("Missing response for id {}", i))?);
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

pub fn fetch_updates_rpc(client: &EthClient, block_number: u64, manager: &crate::update_manager::UpdateManager, address_mapping: &AddressMapping) -> Result<Vec<DBUpdate>> {
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
    let tracked_addrs: Vec<&String> = addrs.iter()
        .filter(|a| address_mapping.get(*a).is_some())
        .collect();

    if tracked_addrs.is_empty() {
        return Ok(vec![]);
    }

    // Batch fetch balances
    let hex_num = format!("0x{:x}", block_number);
    let params: Vec<serde_json::Value> = tracked_addrs.iter()
        .map(|a| json!([a, hex_num]))
        .collect();

    let balances: Vec<Result<String>> = client.call_batch("eth_getBalance", params)?;

    for (i, addr) in tracked_addrs.iter().enumerate() {
        if let Ok(hex_balance) = &balances[i] {
            let balance = u128::from_str_radix(hex_balance.trim_start_matches("0x"), 16)?;
            let index = address_mapping.get(*addr).unwrap(); // Safe because we filtered
            
            let balance_idx = index + 1;
            let old_balance_entry = manager.get_value(balance_idx).unwrap_or([0; 4]);
            
            let mut new_balance_entry = [0u64; 4];
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
    }
    
    Ok(updates)
}

pub fn fetch_touched_states(client: &EthClient, block_number: u64, address_mapping: &AddressMapping) -> Result<Vec<(u64, u128)>> {
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
    let params: Vec<serde_json::Value> = tracked.iter()
        .map(|(a, _)| json!([a, hex_num]))
        .collect();

    let balances: Vec<Result<String>> = client.call_batch("eth_getBalance", params)?;

    let mut results = Vec::with_capacity(tracked.len());
    for (i, (_, idx)) in tracked.iter().enumerate() {
        if let Ok(hex_balance) = &balances[i] {
            if let Ok(balance) = u128::from_str_radix(hex_balance.trim_start_matches("0x"), 16) {
                results.push((*idx, balance));
            }
        }
    }
    
    Ok(results)
}
