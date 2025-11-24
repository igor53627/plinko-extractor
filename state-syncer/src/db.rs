use eyre::{Result, ensure};
use std::path::Path;
use std::fs::OpenOptions;
use memmap2::MmapMut;

pub const DB_ENTRY_SIZE: usize = 32; // 32 bytes (256 bits)
pub const DB_ENTRY_U64_COUNT: usize = 4; // 32 bytes = 4 * u64

pub struct Database {
    pub mmap: MmapMut,
    pub num_entries: u64,
    pub chunk_size: u64,
    pub set_size: u64,
}

impl Database {
    pub fn load(path: impl AsRef<Path>) -> Result<Self> {
        let path = path.as_ref();
        let file = OpenOptions::new().read(true).write(true).open(path)?;
        let len = file.metadata()?.len();

        ensure!(len % DB_ENTRY_SIZE as u64 == 0, "Database size {} is not a multiple of {}", len, DB_ENTRY_SIZE);

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

    pub fn get(&self, index: u64) -> Option<&[u8]> {
        let idx = index as usize * DB_ENTRY_SIZE;
        if idx + DB_ENTRY_SIZE > self.mmap.len() {
            return None;
        }
        Some(&self.mmap[idx..idx+DB_ENTRY_SIZE])
    }

    pub fn update(&mut self, index: u64, new_val: [u64; DB_ENTRY_U64_COUNT]) {
         let idx = index as usize * DB_ENTRY_SIZE;
         if idx + DB_ENTRY_SIZE <= self.mmap.len() {
             // Convert [u64; 4] to bytes and write to mmap
             for (i, val) in new_val.iter().enumerate() {
                 let bytes = val.to_le_bytes();
                 self.mmap[idx + i*8 .. idx + (i+1)*8].copy_from_slice(&bytes);
             }
         }
    }

    pub fn flush(&self) -> Result<()> {
        self.mmap.flush()?;
        Ok(())
    }
}

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
