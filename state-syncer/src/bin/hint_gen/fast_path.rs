use state_syncer::iprf::Iprf;

use crate::hint_gen::subsets::{block_in_subset, xor_32};
use crate::hint_gen::types::{BackupHint, RegularHint, WORD_SIZE};

pub fn process_entries_fast(
    db_bytes: &[u8],
    n_entries: usize,
    n_effective: usize,
    w: usize,
    _c: usize,
    num_regular: usize,
    num_backup: usize,
    block_iprfs: &[Iprf],
    regular_hint_blocks: &[Vec<usize>],
    backup_hint_blocks: &[Vec<usize>],
    regular_hints: &mut [RegularHint],
    backup_hints: &mut [BackupHint],
    progress_callback: impl Fn(usize),
) {
    for i in 0..n_effective {
        let block = i / w;
        let offset = i % w;

        let entry: [u8; 32] = if i < n_entries {
            let entry_offset = i * WORD_SIZE;
            db_bytes[entry_offset..entry_offset + WORD_SIZE]
                .try_into()
                .unwrap()
        } else {
            [0u8; 32]
        };

        let hint_indices = block_iprfs[block].inverse(offset as u64);

        for j in hint_indices {
            let j = j as usize;
            if j < num_regular {
                if block_in_subset(&regular_hint_blocks[j], block) {
                    xor_32(&mut regular_hints[j].parity, &entry);
                }
            } else {
                let backup_idx = j - num_regular;
                if backup_idx < num_backup {
                    if block_in_subset(&backup_hint_blocks[backup_idx], block) {
                        xor_32(&mut backup_hints[backup_idx].parity_in, &entry);
                    } else {
                        xor_32(&mut backup_hints[backup_idx].parity_out, &entry);
                    }
                }
            }
        }

        if i % 10000 == 0 {
            progress_callback(i);
        }
    }
}
