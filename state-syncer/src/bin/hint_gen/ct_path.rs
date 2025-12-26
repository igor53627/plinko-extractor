use state_syncer::constant_time::{ct_lt_u64, ct_select_usize, ct_xor_32_masked};
use state_syncer::iprf::{IprfTee, MAX_PREIMAGES};

use crate::hint_gen::bitset::BlockBitset;
use crate::hint_gen::types::{BackupHint, RegularHint, WORD_SIZE};

/// Process database entries in constant-time for TEE execution.
///
/// # Safety Requirements
/// - `num_backup` must be >= 1 (CT indexing clamps to index 0 for dummy access)
/// - `backup_bitsets` and `backup_hints` must have at least 1 element
pub fn process_entries_ct(
    db_bytes: &[u8],
    n_entries: usize,
    n_effective: usize,
    w: usize,
    num_regular: usize,
    num_backup: usize,
    block_iprfs_ct: &[IprfTee],
    regular_bitsets: &[BlockBitset],
    backup_bitsets: &[BlockBitset],
    regular_hints: &mut [RegularHint],
    backup_hints: &mut [BackupHint],
    progress_callback: impl Fn(usize),
) {
    assert!(
        num_backup >= 1 && !backup_bitsets.is_empty() && !backup_hints.is_empty(),
        "CT path requires at least 1 backup hint for safe dummy indexing"
    );
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

        let (indices, count) = block_iprfs_ct[block].inverse_ct(offset as u64);

        for t in 0..MAX_PREIMAGES {
            let in_range = ct_lt_u64(t as u64, count as u64);

            let j = indices[t] as usize;

            let is_regular = ct_lt_u64(j as u64, num_regular as u64);
            let backup_idx = j.wrapping_sub(num_regular);
            let is_valid_backup = ct_lt_u64(backup_idx as u64, num_backup as u64);
            let is_backup = (1 - is_regular) & is_valid_backup;

            let regular_idx = ct_select_usize(is_regular, j, 0);
            let in_regular_subset = regular_bitsets[regular_idx].contains_ct(block);

            let backup_idx_clamped = ct_select_usize(is_valid_backup, backup_idx, 0);
            let in_backup_subset = backup_bitsets[backup_idx_clamped].contains_ct(block);

            let update_regular = in_range & is_regular & in_regular_subset;
            let update_backup_in = in_range & is_backup & in_backup_subset;
            let update_backup_out = in_range & is_backup & (1 - in_backup_subset);

            ct_xor_32_masked(
                &mut regular_hints[regular_idx].parity,
                &entry,
                update_regular,
            );
            ct_xor_32_masked(
                &mut backup_hints[backup_idx_clamped].parity_in,
                &entry,
                update_backup_in,
            );
            ct_xor_32_masked(
                &mut backup_hints[backup_idx_clamped].parity_out,
                &entry,
                update_backup_out,
            );
        }

        if i % 10000 == 0 {
            progress_callback(i);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hint_gen::keys::{derive_block_keys, derive_subset_seed};
    use crate::hint_gen::subsets::{
        block_in_subset, compute_backup_blocks, compute_regular_blocks, xor_32,
    };
    use crate::hint_gen::types::{SEED_LABEL_BACKUP, SEED_LABEL_REGULAR};
    use state_syncer::iprf::Iprf;

    #[test]
    fn test_ct_and_fast_produce_same_results() {
        let master_seed = [42u8; 32];
        let c = 4;
        let w = 8;
        let lambda = 2;
        let num_regular = lambda * w;
        let num_backup = num_regular;
        let total_hints = num_regular + num_backup;

        let block_keys = derive_block_keys(&master_seed, c);

        let mut regular_blocks_list: Vec<Vec<usize>> = Vec::new();
        let mut backup_blocks_list: Vec<Vec<usize>> = Vec::new();

        for j in 0..num_regular {
            let subset_seed = derive_subset_seed(&master_seed, SEED_LABEL_REGULAR, j as u64);
            regular_blocks_list.push(compute_regular_blocks(&subset_seed, c));
        }
        for j in 0..num_backup {
            let subset_seed = derive_subset_seed(&master_seed, SEED_LABEL_BACKUP, j as u64);
            backup_blocks_list.push(compute_backup_blocks(&subset_seed, c));
        }

        let regular_bitsets: Vec<BlockBitset> = regular_blocks_list
            .iter()
            .map(|b| BlockBitset::from_sorted_blocks(b, c))
            .collect();
        let backup_bitsets: Vec<BlockBitset> = backup_blocks_list
            .iter()
            .map(|b| BlockBitset::from_sorted_blocks(b, c))
            .collect();

        let db: Vec<[u8; 32]> = (0..(c * w))
            .map(|i| {
                let mut entry = [0u8; 32];
                entry[0..8].copy_from_slice(&(i as u64).to_le_bytes());
                entry
            })
            .collect();

        let mut fast_regular: Vec<[u8; 32]> = vec![[0u8; 32]; num_regular];
        let mut fast_backup_in: Vec<[u8; 32]> = vec![[0u8; 32]; num_backup];
        let mut fast_backup_out: Vec<[u8; 32]> = vec![[0u8; 32]; num_backup];

        let block_iprfs: Vec<Iprf> = block_keys
            .iter()
            .map(|key| Iprf::new(*key, total_hints as u64, w as u64))
            .collect();

        for i in 0..(c * w) {
            let block = i / w;
            let offset = i % w;
            let entry = &db[i];

            let hint_indices = block_iprfs[block].inverse(offset as u64);

            for j in hint_indices {
                let j = j as usize;
                if j < num_regular {
                    if block_in_subset(&regular_blocks_list[j], block) {
                        xor_32(&mut fast_regular[j], entry);
                    }
                } else {
                    let backup_idx = j - num_regular;
                    if backup_idx < num_backup {
                        if block_in_subset(&backup_blocks_list[backup_idx], block) {
                            xor_32(&mut fast_backup_in[backup_idx], entry);
                        } else {
                            xor_32(&mut fast_backup_out[backup_idx], entry);
                        }
                    }
                }
            }
        }

        let mut ct_regular: Vec<[u8; 32]> = vec![[0u8; 32]; num_regular];
        let mut ct_backup_in: Vec<[u8; 32]> = vec![[0u8; 32]; num_backup];
        let mut ct_backup_out: Vec<[u8; 32]> = vec![[0u8; 32]; num_backup];

        let block_iprfs_ct: Vec<IprfTee> = block_keys
            .iter()
            .map(|key| IprfTee::new(*key, total_hints as u64, w as u64))
            .collect();

        for i in 0..(c * w) {
            let block = i / w;
            let offset = i % w;
            let entry = &db[i];

            let (indices, count) = block_iprfs_ct[block].inverse_ct(offset as u64);

            for t in 0..MAX_PREIMAGES {
                let in_range = ct_lt_u64(t as u64, count as u64);

                let j = indices[t] as usize;

                let is_regular = ct_lt_u64(j as u64, num_regular as u64);
                let backup_idx = j.wrapping_sub(num_regular);
                let is_valid_backup = ct_lt_u64(backup_idx as u64, num_backup as u64);
                let is_backup = (1 - is_regular) & is_valid_backup;

                let regular_idx = ct_select_usize(is_regular, j, 0);
                let in_regular_subset = regular_bitsets[regular_idx].contains_ct(block);

                let backup_idx_clamped = ct_select_usize(is_valid_backup, backup_idx, 0);
                let in_backup_subset = backup_bitsets[backup_idx_clamped].contains_ct(block);

                let update_regular = in_range & is_regular & in_regular_subset;
                let update_backup_in = in_range & is_backup & in_backup_subset;
                let update_backup_out = in_range & is_backup & (1 - in_backup_subset);

                ct_xor_32_masked(&mut ct_regular[regular_idx], entry, update_regular);
                ct_xor_32_masked(
                    &mut ct_backup_in[backup_idx_clamped],
                    entry,
                    update_backup_in,
                );
                ct_xor_32_masked(
                    &mut ct_backup_out[backup_idx_clamped],
                    entry,
                    update_backup_out,
                );
            }
        }

        assert_eq!(fast_regular, ct_regular, "Regular parities mismatch");
        assert_eq!(fast_backup_in, ct_backup_in, "Backup in-parities mismatch");
        assert_eq!(
            fast_backup_out, ct_backup_out,
            "Backup out-parities mismatch"
        );
    }
}
