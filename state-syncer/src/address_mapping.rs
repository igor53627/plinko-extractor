use eyre::{ensure, Result};
use hex;
use memmap2::Mmap;
use std::fs::File;
use std::path::Path;

pub struct AddressMapping {
    mmap: Mmap,
    count: usize,
}

const ENTRY_SIZE: usize = 24; // 20 bytes address + 4 bytes index

impl AddressMapping {
    /// Loads an AddressMapping from the file at `path`, memory-mapping its contents and validating that the file length is a multiple of `ENTRY_SIZE`.
    ///
    /// The file is opened, safely memory-mapped, and the number of 24-byte entries is computed and stored. The call fails if the file size is not a multiple of `ENTRY_SIZE` or if any I/O/mmap operation errors.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::fs::File;
    /// use std::io::Write;
    /// use tempfile::tempdir;
    ///
    /// let dir = tempdir().unwrap();
    /// let path = dir.path().join("map.bin");
    /// let mut f = File::create(&path).unwrap();
    /// // write a single 24-byte entry
    /// f.write_all(&[0u8; 24]).unwrap();
    ///
    /// let mapping = AddressMapping::load(&path).unwrap();
    /// assert_eq!(mapping.len(), 1);
    /// ```
    pub fn load(path: impl AsRef<Path>) -> Result<Self> {
        let file = File::open(path)?;
        let len = file.metadata()?.len();

        ensure!(
            len % ENTRY_SIZE as u64 == 0,
            "Mapping size {} is not multiple of {}",
            len,
            ENTRY_SIZE
        );

        let mmap = unsafe { Mmap::map(&file)? };
        let count = len as usize / ENTRY_SIZE;

        Ok(Self { mmap, count })
    }

    /// Looks up a 20-byte address (given as hex) in the memory-mapped mapping and returns its stored index.
    ///
    /// The `address_hex` string may optionally start with the prefix `"0x"`. If the hex decoding fails
    /// or the decoded byte sequence is not exactly 20 bytes long, the function returns `None`.
    /// If a matching 20-byte key is found, the following 4 bytes are interpreted as a little-endian
    /// `u32` and returned as `u64`.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// // Assume `mapping` is a previously loaded AddressMapping.
    /// // let mapping = AddressMapping::load("path/to/file").unwrap();
    /// let idx = mapping.get("0x0123456789abcdef0123456789abcdef01234567");
    /// // `idx` is `Some(value)` when the address is present, otherwise `None`.
    /// ```
    pub fn get(&self, address_hex: &str) -> Option<u64> {
        // Convert hex string to [u8; 20]
        let address_bytes = match hex::decode(address_hex.trim_start_matches("0x")) {
            Ok(b) if b.len() == 20 => b,
            _ => return None,
        };

        // Binary search
        // We are searching for `address_bytes` in a sorted array of 24-byte chunks
        // where the first 20 bytes are the key.

        let mut low = 0;
        let mut high = self.count;

        while low < high {
            let mid = low + (high - low) / 2;
            let offset = mid * ENTRY_SIZE;
            let entry_addr = &self.mmap[offset..offset + 20];

            match entry_addr.cmp(&address_bytes) {
                std::cmp::Ordering::Equal => {
                    let idx_bytes = &self.mmap[offset + 20..offset + 24];
                    return Some(u32::from_le_bytes(idx_bytes.try_into().unwrap()) as u64);
                }
                std::cmp::Ordering::Less => low = mid + 1,
                std::cmp::Ordering::Greater => high = mid,
            }
        }
        None
    }

    pub fn len(&self) -> usize {
        self.count
    }
}