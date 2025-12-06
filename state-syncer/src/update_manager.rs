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
    /// Creates a new UpdateManager that holds a mutable reference to the provided database.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use crate::db::Database;
    /// use crate::update::UpdateManager;
    ///
    /// // Given a mutable `Database` instance `db`, create an UpdateManager:
    /// let mut db: Database = /* obtain or construct a Database */ unimplemented!();
    /// let manager = UpdateManager::new(&mut db);
    /// ```
    pub fn new(db: &'a mut Database) -> Self {
        Self { db }
    }

    /// Applies a sequence of updates to the database and returns per-account raw deltas along with the elapsed time.
    ///
    /// For each `DBUpdate`, computes the element-wise XOR of `old_value` and `new_value`, writes `new_value` into the underlying `Database` at `update.index`, and collects an `AccountDelta` containing the account index and the computed difference.
    ///
    /// # Returns
    ///
    /// A tuple `(Vec<AccountDelta>, std::time::Duration)` where the vector contains one `AccountDelta` per applied update in the same order, and the `Duration` is the elapsed time spent applying all updates.
    ///
    /// # Examples
    ///
    /// ```
    /// // Given an existing `UpdateManager` instance `mgr` and a list of updates:
    /// let updates: Vec<DBUpdate> = Vec::new();
    /// let (deltas, elapsed) = mgr.apply_updates(&updates);
    /// assert!(elapsed.as_nanos() >= 0);
    /// assert!(deltas.is_empty());
    /// ```
    pub fn apply_updates(
        &mut self,
        updates: &[DBUpdate],
    ) -> (Vec<AccountDelta>, std::time::Duration) {
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

    /// Retrieves the database entry at `index` and decodes it as an array of little-endian `u64` values.
    ///
    /// The stored entry is expected to contain exactly `DB_ENTRY_U64_COUNT * 8` bytes; those bytes are
    /// interpreted as `DB_ENTRY_U64_COUNT` consecutive `u64` values in little-endian byte order.
    /// Returns `None` if there is no entry for the given `index`.
    ///
    /// # Returns
    ///
    /// `Some([u64; DB_ENTRY_U64_COUNT])` with the decoded values, or `None` if the entry is missing.
    ///
    /// # Examples
    ///
    /// ```
    /// // `mgr` is an instance of `UpdateManager`.
    /// if let Some(values) = mgr.get_value(0) {
    ///     assert_eq!(values.len(), DB_ENTRY_U64_COUNT);
    /// }
    /// ```
    pub fn get_value(&self, index: u64) -> Option<[u64; DB_ENTRY_U64_COUNT]> {
        let bytes = self.db.get(index)?;
        let mut result = [0u64; DB_ENTRY_U64_COUNT];
        for i in 0..DB_ENTRY_U64_COUNT {
            result[i] = u64::from_le_bytes(bytes[i * 8..(i + 1) * 8].try_into().unwrap());
        }
        Some(result)
    }

    pub fn flush(&self) -> eyre::Result<()> {
        self.db.flush()
    }
}