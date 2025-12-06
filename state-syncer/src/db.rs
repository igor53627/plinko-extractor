use eyre::{ensure, Result};
use memmap2::MmapMut;
use std::fs::OpenOptions;
use std::path::Path;

pub const DB_ENTRY_SIZE: usize = 32; // 32 bytes (256 bits)
pub const DB_ENTRY_U64_COUNT: usize = 4; // 32 bytes = 4 * u64

pub struct Database {
    pub mmap: MmapMut,
    pub num_entries: u64,
    pub chunk_size: u64,
    pub set_size: u64,
}

impl Database {
    /// Loads a database file into memory and returns a Database backed by a writable memory map.
    ///
    /// The file at `path` is opened for read/write, validated to have a length that is a multiple
    /// of the database entry size, and then memory-mapped for in-place access. The number of
    /// entries and the derived `chunk_size` and `set_size` are computed and stored in the returned
    /// Database.
    ///
    /// # Arguments
    ///
    /// * `path` - Path to the database file to open and memory-map.
    ///
    /// # Returns
    ///
    /// `Ok(Database)` containing a writable memory-mapped view of the file and derived parameters
    /// on success; `Err` if the file cannot be opened, its metadata read, its size is not a multiple
    /// of the entry size, or the memory map cannot be created.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::fs::OpenOptions;
    /// # use std::io::Write;
    /// # use tempfile::NamedTempFile;
    /// # // Prepare a temporary file with one 32-byte entry
    /// # let mut tmp = NamedTempFile::new().unwrap();
    /// # tmp.as_file_mut().set_len(32).unwrap();
    /// let db = state_syncer::db::Database::load(tmp.path()).unwrap();
    /// assert!(db.num_entries >= 1);
    /// ```
    pub fn load(path: impl AsRef<Path>) -> Result<Self> {
        let path = path.as_ref();
        let file = OpenOptions::new().read(true).write(true).open(path)?;
        let len = file.metadata()?.len();

        ensure!(
            len % DB_ENTRY_SIZE as u64 == 0,
            "Database size {} is not a multiple of {}",
            len,
            DB_ENTRY_SIZE
        );

        let num_entries = len / DB_ENTRY_SIZE as u64;
        let (chunk_size, set_size) = derive_plinko_params(num_entries);

        // Memory map the file
        let mmap = unsafe { MmapMut::map_mut(&file)? };

        Ok(Self {
            mmap,
            num_entries,
            chunk_size,
            set_size,
        })
    }

    /// Returns a 32-byte slice for the database entry at the given index, or `None` if the index is out of bounds.
    ///
    /// # Parameters
    ///
    /// - `index`: The zero-based entry index within the database.
    ///
    /// # Returns
    ///
    /// `Some(&[u8])` containing exactly 32 bytes for the entry at `index`, or `None` if `index` refers to an entry beyond the mapped file.
    pub fn get(&self, index: u64) -> Option<&[u8]> {
        let idx = index as usize * DB_ENTRY_SIZE;
        if idx + DB_ENTRY_SIZE > self.mmap.len() {
            return None;
        }
        Some(&self.mmap[idx..idx + DB_ENTRY_SIZE])
    }

    /// Overwrites the database entry at the given index with the four provided `u64` values in little-endian order.
    ///
    /// If `index` addresses an entry outside the mapped file, this method does nothing; otherwise it writes the four
    /// `u64` values into the 32-byte entry (8 bytes each) in little-endian byte order.
    ///
    /// # Parameters
    ///
    /// - `index`: Entry index within the database to update.
    /// - `new_val`: Array of four `u64` values to store into the entry (written in little-endian).
    ///
    /// # Examples
    ///
    /// ```
    /// // Assume `db` is a mutable Database previously loaded with enough entries:
    /// // db.update(0, [1, 2, 3, 4]);
    /// ```
    pub fn update(&mut self, index: u64, new_val: [u64; DB_ENTRY_U64_COUNT]) {
        let idx = index as usize * DB_ENTRY_SIZE;
        if idx + DB_ENTRY_SIZE <= self.mmap.len() {
            // Convert [u64; 4] to bytes and write to mmap
            for (i, val) in new_val.iter().enumerate() {
                let bytes = val.to_le_bytes();
                self.mmap[idx + i * 8..idx + (i + 1) * 8].copy_from_slice(&bytes);
            }
        }
    }

    /// Flushes in-memory changes to the database file backing the memory map.
    ///
    /// # Examples
    ///
    /// ```
    /// # use state_syncer::db::Database;
    /// # fn example() -> std::io::Result<()> {
    /// let db = Database::load("path/to/db")?; // load existing database file
    /// db.flush()?; // persist any pending changes to disk
    /// # Ok(())
    /// # }
    /// ```
    ///
    /// Returns `Ok(())` on success, or propagates the underlying I/O error otherwise.
    pub fn flush(&self) -> Result<()> {
        self.mmap.flush()?;
        Ok(())
    }
}

/// Compute chunk and set sizes for partitioning a database of entries.
///
/// The function derives two parameters used to split `db_entries` into
/// chunked groups:
/// - `chunk_size`: a power-of-two chunk width chosen as the smallest power of two
///   greater than or equal to `2 * sqrt(db_entries)` (at least 1).
/// - `set_size`: the number of chunks per set computed as `ceil(db_entries / chunk_size)`
///   then rounded up to the nearest multiple of 4.
///
/// # Returns
///
/// A tuple `(chunk_size, set_size)` describing the derived partition sizes.
///
/// # Examples
///
/// ```
/// let (chunk, set) = derive_plinko_params(1_000);
/// assert!(chunk.is_power_of_two());
/// assert!(set % 4 == 0);
/// assert!(chunk * set >= 1_000);
/// ```
fn derive_plinko_params(db_entries: u64) -> (u64, u64) {
    if db_entries == 0 {
        return (1, 1);
    }
    let target_chunk = (2.0 * (db_entries as f64).sqrt()) as u64;
    let mut chunk_size = 1;
    while chunk_size < target_chunk {
        chunk_size *= 2;
    }
    let mut set_size = (db_entries as f64 / chunk_size as f64).ceil() as u64;
    // Round up to nearest multiple of 4 (SIMD friendly alignment maybe? inherited from Go)
    set_size = (set_size + 3) / 4 * 4;
    (chunk_size, set_size)
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    #[test]
    fn derive_plinko_params_zero_entries() {
        let (chunk, set) = derive_plinko_params(0);
        assert_eq!((chunk, set), (1, 1));
    }

    proptest! {
        #![proptest_config(ProptestConfig {
            cases: 256,
            .. ProptestConfig::default()
        })]

        #[test]
        fn derive_plinko_params_invariants(db_entries in 1u64..1_000_000) {
            let (chunk_size, set_size) = derive_plinko_params(db_entries);

            prop_assert!(chunk_size.is_power_of_two());
            prop_assert!(chunk_size >= 1);

            let target_chunk = (2.0 * (db_entries as f64).sqrt()) as u64;
            prop_assert!(chunk_size >= target_chunk);
            prop_assert!(chunk_size <= target_chunk.saturating_mul(2).max(1));

            prop_assert!(set_size > 0);
            prop_assert_eq!(set_size % 4, 0);

            let base_sets = (db_entries + chunk_size - 1) / chunk_size;
            prop_assert!(set_size >= base_sets);
            prop_assert!(set_size <= base_sets + 4);

            let capacity = chunk_size.checked_mul(set_size).expect("overflow in capacity");
            prop_assert!(capacity >= db_entries);
        }
    }
}