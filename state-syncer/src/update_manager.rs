use crate::db::{Database, DB_ENTRY_U64_COUNT};
use crate::iprf::Iprf;
use std::time::Instant;
use rand::RngCore;

pub struct UpdateManager<'a> {
    db: &'a mut Database,
    iprf: Iprf,
    use_cache_mode: bool,
    index_to_hint: Vec<u64>,
}

#[derive(Debug, Clone)]
pub struct DBUpdate {
    pub index: u64,
    pub old_value: [u64; DB_ENTRY_U64_COUNT],
    pub new_value: [u64; DB_ENTRY_U64_COUNT],
}

#[derive(Debug)]
pub struct HintDelta {
    pub hint_set_id: u64,
    pub is_backup_set: bool,
    pub delta: [u64; DB_ENTRY_U64_COUNT],
}

impl<'a> UpdateManager<'a> {
    pub fn new(db: &'a mut Database) -> Self {
        // Generate random key for now (per Go implementation)
        let mut key = [0u8; 16];
        rand::thread_rng().fill_bytes(&mut key);
        
        let iprf = Iprf::new(key, db.num_entries, db.set_size);

        Self { 
            db, 
            iprf,
            use_cache_mode: false,
            index_to_hint: Vec::new(),
        }
    }

    pub fn enable_cache_mode(&mut self) {
        let start = Instant::now();
        let db_size = self.db.num_entries;
        self.index_to_hint = vec![0; db_size as usize];
        
        for i in 0..db_size {
            self.index_to_hint[i as usize] = self.iprf.forward(i);
        }
        self.use_cache_mode = true;
        tracing::info!("Cache mode enabled in {:?}", start.elapsed());
    }

    pub fn apply_updates(&mut self, updates: &[DBUpdate]) -> (Vec<HintDelta>, std::time::Duration) {
        let start = Instant::now();
        let mut deltas = Vec::new();

        for update in updates {
            // XOR Difference
            let mut diff = [0u64; DB_ENTRY_U64_COUNT];
            for i in 0..DB_ENTRY_U64_COUNT {
                diff[i] = update.old_value[i] ^ update.new_value[i];
            }

            // Apply update to DB
            self.db.update(update.index, update.new_value);

            // Find affected hint set
            let hint_set_id = if self.use_cache_mode && (update.index as usize) < self.index_to_hint.len() {
                self.index_to_hint[update.index as usize]
            } else {
                self.iprf.forward(update.index)
            };
            
            deltas.push(HintDelta {
                hint_set_id,
                is_backup_set: false,
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
