use crate::db::{Database, DB_ENTRY_U64_COUNT};
use std::time::Instant;

pub struct UpdateManager<'a> {
    db: &'a mut Database,
}

#[derive(Debug, Clone)]
pub struct DBUpdate {
    pub index: u64,
    pub old_value: [u64; DB_ENTRY_U64_COUNT],
    pub new_value: [u64; DB_ENTRY_U64_COUNT],
}

#[derive(Debug)]
pub struct AccountDelta {
    pub account_index: u64,
    pub delta: [u64; DB_ENTRY_U64_COUNT],
}

impl<'a> UpdateManager<'a> {
    pub fn new(db: &'a mut Database) -> Self {
        Self { db }
    }

    pub fn apply_updates(&mut self, updates: &[DBUpdate]) -> (Vec<AccountDelta>, std::time::Duration) {
        let start = Instant::now();
        let mut deltas = Vec::with_capacity(updates.len());

        for update in updates {
            // XOR Difference
            let mut diff = [0u64; DB_ENTRY_U64_COUNT];
            for i in 0..DB_ENTRY_U64_COUNT {
                diff[i] = update.old_value[i] ^ update.new_value[i];
            }

            // Apply update to DB
            self.db.update(update.index, update.new_value);

            // Output Raw Delta (Client handles IPRF/Hint mapping)
            deltas.push(AccountDelta {
                account_index: update.index,
                delta: diff,
            });
        }

        (deltas, start.elapsed())
    }

    pub fn db_size(&self) -> u64 {
        self.db.num_entries
    }

    pub fn get_value(&self, index: u64) -> Option<[u64; DB_ENTRY_U64_COUNT]> {
        let bytes = self.db.get(index)?;
        let mut result = [0u64; DB_ENTRY_U64_COUNT];
        for i in 0..DB_ENTRY_U64_COUNT {
            result[i] = u64::from_le_bytes(bytes[i*8..(i+1)*8].try_into().unwrap());
        }
        Some(result)
    }

    pub fn flush(&self) -> eyre::Result<()> {
        self.db.flush()
    }
}
