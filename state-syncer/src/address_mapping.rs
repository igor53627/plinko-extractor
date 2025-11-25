use eyre::{Result, ensure};
use memmap2::Mmap;
use std::fs::File;
use std::path::Path;
use hex;

pub struct AddressMapping {
    mmap: Mmap,
    count: usize,
}

const ENTRY_SIZE: usize = 24; // 20 bytes address + 4 bytes index

impl AddressMapping {
    pub fn load(path: impl AsRef<Path>) -> Result<Self> {
        let file = File::open(path)?;
        let len = file.metadata()?.len();
        
        ensure!(len % ENTRY_SIZE as u64 == 0, "Mapping size {} is not multiple of {}", len, ENTRY_SIZE);
        
        let mmap = unsafe { Mmap::map(&file)? };
        let count = len as usize / ENTRY_SIZE;

        Ok(Self {
            mmap,
            count,
        })
    }

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
