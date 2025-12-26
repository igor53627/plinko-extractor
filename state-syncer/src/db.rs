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
    ///
    /// Note: Silently does nothing if index is out of range.
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
/// This implementation uses pure integer arithmetic to match the Coq spec in
/// `plinko/formal/specs/DbSpec.v` exactly, avoiding floating-point rounding issues.
///
/// # Returns
///
/// A tuple `(chunk_size, set_size)` describing the derived partition sizes.
fn derive_plinko_params(db_entries: u64) -> (u64, u64) {
    if db_entries == 0 {
        return (1, 1);
    }
    // Compute target_chunk = floor(sqrt(4 * db_entries)) = floor(2 * sqrt(db_entries))
    // This matches Coq: target_chunk = Z.sqrt(4 * db_entries)
    let target_chunk = isqrt(4u64.saturating_mul(db_entries));

    // Find smallest power of 2 >= target_chunk
    // This matches Coq: chunk_size = smallest_power_of_two_geq(target_chunk)
    let mut chunk_size = 1u64;
    while chunk_size < target_chunk {
        chunk_size = chunk_size.saturating_mul(2);
    }

    // Integer ceiling division: ceil(db_entries / chunk_size)
    // Matches Coq: ceil_div db_entries chunk_size
    let mut set_size = db_entries.div_ceil(chunk_size);
    // Round up to nearest multiple of 4 (SIMD friendly alignment)
    // Matches Coq: round_up_multiple set_size_raw 4
    set_size = set_size.div_ceil(4) * 4;
    (chunk_size, set_size)
}

/// Integer square root: returns floor(sqrt(n))
/// Uses Newton's method for fast convergence.
fn isqrt(n: u64) -> u64 {
    if n <= 1 {
        return n;
    }
    // Newton iteration: x_{k+1} = (x_k + n/x_k) / 2
    // Initial guess must be >= sqrt(n) for Newton to converge from above
    // Use 2^ceil((log2(n)+1)/2) which is always >= sqrt(n)
    let bits = 64 - n.leading_zeros(); // bits = floor(log2(n)) + 1
    let shift = bits.div_ceil(2); // ceil((bits)/2)
    let mut x = 1u64 << shift;

    loop {
        // y = (x + n/x) / 2
        // Since x >= sqrt(n), we have n/x <= sqrt(n) <= x
        // So x + n/x <= 2x, and since x <= 2^33 for any n, no overflow
        let y = (x + n / x) / 2;
        if y >= x {
            return x;
        }
        x = y;
    }
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
            cases: 512,
            .. ProptestConfig::default()
        })]

        #[test]
        fn derive_plinko_params_invariants(db_entries in 1u64..10_000_000_000u64) {
            let (chunk_size, set_size) = derive_plinko_params(db_entries);

            // Matches Coq: chunk_is_power_of_two
            prop_assert!(chunk_size.is_power_of_two());
            prop_assert!(chunk_size >= 1);

            // Matches Coq: chunk_ge_target (chunk >= floor(sqrt(4 * db_entries)))
            let target = isqrt(4u64.saturating_mul(db_entries));
            prop_assert!(chunk_size >= target);

            // Matches Coq: chunk_le_double_target (chunk <= 2 * target)
            // Since chunk is smallest power of 2 >= target, chunk/2 < target
            let half_chunk = chunk_size / 2;
            if half_chunk > 0 && target > 0 {
                prop_assert!(half_chunk < target);
            }

            // Matches Coq: set_size_positive, set_size_multiple_of_4
            prop_assert!(set_size > 0);
            prop_assert_eq!(set_size % 4, 0);

            // set_size >= ceil(db_entries / chunk_size)
            let base_sets = (db_entries + chunk_size - 1) / chunk_size;
            prop_assert!(set_size >= base_sets);
            prop_assert!(set_size <= base_sets + 3); // round_up_multiple adds at most 3

            // Matches Coq: capacity_sufficient
            let capacity = chunk_size.checked_mul(set_size).expect("overflow in capacity");
            prop_assert!(capacity >= db_entries);
        }
    }

    #[test]
    fn derive_plinko_params_edge_cases() {
        // Powers of 2
        for exp in [0, 1, 2, 10, 20, 30] {
            let n = 1u64 << exp;
            let (chunk, set) = derive_plinko_params(n);
            assert!(chunk.is_power_of_two());
            assert!(set % 4 == 0);
            assert!(chunk * set >= n);
        }

        // Near powers of 2
        for base in [15u64, 16, 17, 1023, 1024, 1025, 65535, 65536, 65537] {
            let (chunk, set) = derive_plinko_params(base);
            let target = isqrt(4 * base);
            assert!(chunk.is_power_of_two());
            assert!(chunk >= target);
            assert!(chunk * set >= base);
        }

        // Perfect squares
        for root in [1u64, 2, 10, 100, 1000, 10000] {
            let n = root * root;
            let (chunk, set) = derive_plinko_params(n);
            assert!(chunk.is_power_of_two());
            assert!(chunk * set >= n);
        }
    }

    #[test]
    fn test_isqrt() {
        assert_eq!(isqrt(0), 0);
        assert_eq!(isqrt(1), 1);
        assert_eq!(isqrt(2), 1); // floor(sqrt(2)) = 1
        assert_eq!(isqrt(3), 1); // floor(sqrt(3)) = 1
        assert_eq!(isqrt(4), 2);
        assert_eq!(isqrt(9), 3);
        assert_eq!(isqrt(16), 4);
        assert_eq!(isqrt(17), 4); // floor(sqrt(17)) = 4
        assert_eq!(isqrt(24), 4); // floor(sqrt(24)) = 4
        assert_eq!(isqrt(25), 5);
        assert_eq!(isqrt(100), 10);
        assert_eq!(isqrt(u64::MAX), 4294967295); // floor(sqrt(2^64-1)) = 2^32-1
    }

    proptest! {
        #![proptest_config(ProptestConfig { cases: 1000, .. ProptestConfig::default() })]

        #[test]
        fn isqrt_property(n in 0u64..1_000_000_000_000u64) {
            let s = isqrt(n);
            // floor(sqrt(n))^2 <= n
            prop_assert!(s.saturating_mul(s) <= n);
            // n < (floor(sqrt(n)) + 1)^2
            let s_plus_1_sq = (s + 1).saturating_mul(s + 1);
            prop_assert!(n < s_plus_1_sq || s_plus_1_sq == u64::MAX);
        }
    }

    #[test]
    fn derive_plinko_params_matches_f64_reference() {
        // Reference implementation using f64 (original code)
        fn derive_f64(db_entries: u64) -> (u64, u64) {
            if db_entries == 0 {
                return (1, 1);
            }
            let target_chunk = (2.0 * (db_entries as f64).sqrt()) as u64;
            let mut chunk_size = 1u64;
            while chunk_size < target_chunk {
                chunk_size *= 2;
            }
            let mut set_size = (db_entries as f64 / chunk_size as f64).ceil() as u64;
            set_size = (set_size + 3) / 4 * 4;
            (chunk_size, set_size)
        }

        // Test that integer version matches f64 version for reasonable inputs
        for n in 1..10000u64 {
            let (chunk_int, set_int) = derive_plinko_params(n);
            let (chunk_f64, set_f64) = derive_f64(n);
            assert_eq!(
                (chunk_int, set_int),
                (chunk_f64, set_f64),
                "Mismatch at n={}: int=({}, {}), f64=({}, {})",
                n,
                chunk_int,
                set_int,
                chunk_f64,
                set_f64
            );
        }
    }
}
