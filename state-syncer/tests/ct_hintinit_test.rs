//! Integration tests for constant-time HintInit
//!
//! Verifies that the constant-time (TEE) path produces identical results
//! to the non-constant-time path, ensuring correctness while providing
//! timing side-channel protection.

use rand::{RngCore, SeedableRng};
use rand_chacha::ChaCha20Rng;
use sha2::{Digest, Sha256};
use state_syncer::constant_time::{ct_lt_u64, ct_select_usize, ct_xor_32_masked};
use state_syncer::iprf::{Iprf, IprfTee, PrfKey128, MAX_PREIMAGES};

const SEED_LABEL_REGULAR: &[u8] = b"plinko_regular_subset";
const SEED_LABEL_BACKUP: &[u8] = b"plinko_backup_subset";

struct RegularHint {
    parity: [u8; 32],
}

struct BackupHint {
    parity_in: [u8; 32],
    parity_out: [u8; 32],
}

struct BlockBitset {
    bits: Vec<u64>,
    num_blocks: usize,
}

impl BlockBitset {
    fn new(num_blocks: usize) -> Self {
        let num_words = num_blocks.div_ceil(64);
        Self {
            bits: vec![0u64; num_words],
            num_blocks,
        }
    }

    fn from_sorted_blocks(blocks: &[usize], num_blocks: usize) -> Self {
        let mut bitset = Self::new(num_blocks);
        for &block in blocks {
            if block < num_blocks {
                bitset.bits[block / 64] |= 1u64 << (block % 64);
            }
        }
        bitset
    }

    #[inline]
    fn contains_ct(&self, block: usize) -> u64 {
        if block >= self.num_blocks {
            return 0;
        }
        let word_idx = block / 64;
        let bit_idx = block % 64;
        (self.bits[word_idx] >> bit_idx) & 1
    }
}

fn xor_32(dst: &mut [u8; 32], src: &[u8; 32]) {
    for i in 0..32 {
        dst[i] ^= src[i];
    }
}

fn derive_subset_seed(master_seed: &[u8; 32], label: &[u8], idx: u64) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(master_seed);
    hasher.update(label);
    hasher.update(idx.to_le_bytes());
    let hash = hasher.finalize();
    let mut seed = [0u8; 32];
    seed.copy_from_slice(&hash[0..32]);
    seed
}

fn derive_block_keys(master_seed: &[u8; 32], c: usize) -> Vec<PrfKey128> {
    let mut keys = Vec::with_capacity(c);
    for block_idx in 0..c {
        let mut hasher = Sha256::new();
        hasher.update(master_seed);
        hasher.update(b"block_key");
        hasher.update((block_idx as u64).to_le_bytes());
        let hash = hasher.finalize();
        let mut key = [0u8; 16];
        key.copy_from_slice(&hash[0..16]);
        keys.push(key);
    }
    keys
}

fn random_subset(rng: &mut ChaCha20Rng, size: usize, total: usize) -> Vec<usize> {
    use rand::seq::index::sample;
    sample(rng, total, size).into_vec()
}

fn compute_regular_blocks(seed: &[u8; 32], c: usize) -> Vec<usize> {
    let regular_subset_size = c / 2 + 1;
    let mut rng = ChaCha20Rng::from_seed(*seed);
    let mut blocks = random_subset(&mut rng, regular_subset_size, c);
    blocks.sort_unstable();
    blocks
}

fn compute_backup_blocks(seed: &[u8; 32], c: usize) -> Vec<usize> {
    let backup_subset_size = c / 2;
    let mut rng = ChaCha20Rng::from_seed(*seed);
    let mut blocks = random_subset(&mut rng, backup_subset_size, c);
    blocks.sort_unstable();
    blocks
}

fn block_in_subset(blocks: &[usize], block: usize) -> bool {
    blocks.binary_search(&block).is_ok()
}

/// Run HintInit using the fast (non-CT) path
fn hintinit_fast(
    db: &[[u8; 32]],
    master_seed: &[u8; 32],
    lambda: usize,
    w: usize,
) -> (Vec<RegularHint>, Vec<BackupHint>) {
    let n = db.len();
    let c = n.div_ceil(w);
    let n_effective = c * w;

    let num_regular = lambda * w;
    let num_backup = lambda * w;
    let total_hints = num_regular + num_backup;

    let block_keys = derive_block_keys(master_seed, c);

    let mut regular_hints: Vec<RegularHint> = (0..num_regular)
        .map(|_| RegularHint { parity: [0u8; 32] })
        .collect();
    let mut backup_hints: Vec<BackupHint> = (0..num_backup)
        .map(|_| BackupHint {
            parity_in: [0u8; 32],
            parity_out: [0u8; 32],
        })
        .collect();

    let regular_hint_blocks: Vec<Vec<usize>> = (0..num_regular)
        .map(|j| {
            let subset_seed = derive_subset_seed(master_seed, SEED_LABEL_REGULAR, j as u64);
            compute_regular_blocks(&subset_seed, c)
        })
        .collect();

    let backup_hint_blocks: Vec<Vec<usize>> = (0..num_backup)
        .map(|j| {
            let subset_seed = derive_subset_seed(master_seed, SEED_LABEL_BACKUP, j as u64);
            compute_backup_blocks(&subset_seed, c)
        })
        .collect();

    let block_iprfs: Vec<Iprf> = block_keys
        .iter()
        .map(|key| Iprf::new(*key, total_hints as u64, w as u64))
        .collect();

    for i in 0..n_effective {
        let block = i / w;
        let offset = i % w;

        let entry: [u8; 32] = if i < n { db[i] } else { [0u8; 32] };

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
    }

    (regular_hints, backup_hints)
}

/// Run HintInit using the constant-time (TEE) path
fn hintinit_ct(
    db: &[[u8; 32]],
    master_seed: &[u8; 32],
    lambda: usize,
    w: usize,
) -> (Vec<RegularHint>, Vec<BackupHint>) {
    let n = db.len();
    let c = n.div_ceil(w);
    let n_effective = c * w;

    let num_regular = lambda * w;
    let num_backup = lambda * w;
    let total_hints = num_regular + num_backup;

    let block_keys = derive_block_keys(master_seed, c);

    let mut regular_hints: Vec<RegularHint> = (0..num_regular)
        .map(|_| RegularHint { parity: [0u8; 32] })
        .collect();
    let mut backup_hints: Vec<BackupHint> = (0..num_backup)
        .map(|_| BackupHint {
            parity_in: [0u8; 32],
            parity_out: [0u8; 32],
        })
        .collect();

    let regular_bitsets: Vec<BlockBitset> = (0..num_regular)
        .map(|j| {
            let subset_seed = derive_subset_seed(master_seed, SEED_LABEL_REGULAR, j as u64);
            let blocks = compute_regular_blocks(&subset_seed, c);
            BlockBitset::from_sorted_blocks(&blocks, c)
        })
        .collect();

    let backup_bitsets: Vec<BlockBitset> = (0..num_backup)
        .map(|j| {
            let subset_seed = derive_subset_seed(master_seed, SEED_LABEL_BACKUP, j as u64);
            let blocks = compute_backup_blocks(&subset_seed, c);
            BlockBitset::from_sorted_blocks(&blocks, c)
        })
        .collect();

    let block_iprfs_ct: Vec<IprfTee> = block_keys
        .iter()
        .map(|key| IprfTee::new(*key, total_hints as u64, w as u64))
        .collect();

    for i in 0..n_effective {
        let block = i / w;
        let offset = i % w;

        let entry: [u8; 32] = if i < n { db[i] } else { [0u8; 32] };

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
    }

    (regular_hints, backup_hints)
}

#[test]
fn test_ct_hintinit_matches_fast_path_tiny() {
    let master_seed = [42u8; 32];
    let lambda = 2;
    let w = 4;
    let n = 16;

    let mut rng = ChaCha20Rng::from_seed([1u8; 32]);
    let db: Vec<[u8; 32]> = (0..n)
        .map(|_| {
            let mut entry = [0u8; 32];
            rng.fill_bytes(&mut entry);
            entry
        })
        .collect();

    let (regular_fast, backup_fast) = hintinit_fast(&db, &master_seed, lambda, w);
    let (regular_ct, backup_ct) = hintinit_ct(&db, &master_seed, lambda, w);

    assert_eq!(
        regular_fast.len(),
        regular_ct.len(),
        "Regular hint count mismatch"
    );
    assert_eq!(
        backup_fast.len(),
        backup_ct.len(),
        "Backup hint count mismatch"
    );

    for (i, (fast, ct)) in regular_fast.iter().zip(regular_ct.iter()).enumerate() {
        assert_eq!(fast.parity, ct.parity, "Regular hint {} parity mismatch", i);
    }

    for (i, (fast, ct)) in backup_fast.iter().zip(backup_ct.iter()).enumerate() {
        assert_eq!(
            fast.parity_in, ct.parity_in,
            "Backup hint {} parity_in mismatch",
            i
        );
        assert_eq!(
            fast.parity_out, ct.parity_out,
            "Backup hint {} parity_out mismatch",
            i
        );
    }
}

#[test]
fn test_ct_hintinit_matches_fast_path_small() {
    let master_seed = [0xABu8; 32];
    let lambda = 2;
    let w = 4;
    let n = 32;

    let mut rng = ChaCha20Rng::from_seed([2u8; 32]);
    let db: Vec<[u8; 32]> = (0..n)
        .map(|_| {
            let mut entry = [0u8; 32];
            rng.fill_bytes(&mut entry);
            entry
        })
        .collect();

    let (regular_fast, backup_fast) = hintinit_fast(&db, &master_seed, lambda, w);
    let (regular_ct, backup_ct) = hintinit_ct(&db, &master_seed, lambda, w);

    for (i, (fast, ct)) in regular_fast.iter().zip(regular_ct.iter()).enumerate() {
        assert_eq!(fast.parity, ct.parity, "Regular hint {} parity mismatch", i);
    }

    for (i, (fast, ct)) in backup_fast.iter().zip(backup_ct.iter()).enumerate() {
        assert_eq!(
            fast.parity_in, ct.parity_in,
            "Backup hint {} parity_in mismatch",
            i
        );
        assert_eq!(
            fast.parity_out, ct.parity_out,
            "Backup hint {} parity_out mismatch",
            i
        );
    }
}

#[test]
#[ignore] // Slow due to MAX_PREIMAGES=512 iterations per entry in CT path
fn test_ct_hintinit_matches_fast_path_medium() {
    let master_seed = [0xCDu8; 32];
    let lambda = 4;
    let w = 8;
    let n = 64;

    let mut rng = ChaCha20Rng::from_seed([3u8; 32]);
    let db: Vec<[u8; 32]> = (0..n)
        .map(|_| {
            let mut entry = [0u8; 32];
            rng.fill_bytes(&mut entry);
            entry
        })
        .collect();

    let (regular_fast, backup_fast) = hintinit_fast(&db, &master_seed, lambda, w);
    let (regular_ct, backup_ct) = hintinit_ct(&db, &master_seed, lambda, w);

    for (i, (fast, ct)) in regular_fast.iter().zip(regular_ct.iter()).enumerate() {
        assert_eq!(fast.parity, ct.parity, "Regular hint {} parity mismatch", i);
    }

    for (i, (fast, ct)) in backup_fast.iter().zip(backup_ct.iter()).enumerate() {
        assert_eq!(
            fast.parity_in, ct.parity_in,
            "Backup hint {} parity_in mismatch",
            i
        );
        assert_eq!(
            fast.parity_out, ct.parity_out,
            "Backup hint {} parity_out mismatch",
            i
        );
    }
}

#[test]
fn test_ct_hintinit_zero_db() {
    let master_seed = [0u8; 32];
    let lambda = 2;
    let w = 4;
    let n = 16;

    let db: Vec<[u8; 32]> = vec![[0u8; 32]; n];

    let (regular_fast, backup_fast) = hintinit_fast(&db, &master_seed, lambda, w);
    let (regular_ct, backup_ct) = hintinit_ct(&db, &master_seed, lambda, w);

    for (fast, ct) in regular_fast.iter().zip(regular_ct.iter()) {
        assert_eq!(fast.parity, ct.parity);
        assert_eq!(fast.parity, [0u8; 32], "Zero DB should yield zero parity");
    }

    for (fast, ct) in backup_fast.iter().zip(backup_ct.iter()) {
        assert_eq!(fast.parity_in, ct.parity_in);
        assert_eq!(fast.parity_out, ct.parity_out);
    }
}

#[test]
fn test_ct_hintinit_single_nonzero_entry() {
    let master_seed = [99u8; 32];
    let lambda = 2;
    let w = 4;
    let n = 16;

    let mut db: Vec<[u8; 32]> = vec![[0u8; 32]; n];
    db[7] = [0xFFu8; 32];

    let (regular_fast, backup_fast) = hintinit_fast(&db, &master_seed, lambda, w);
    let (regular_ct, backup_ct) = hintinit_ct(&db, &master_seed, lambda, w);

    for (i, (fast, ct)) in regular_fast.iter().zip(regular_ct.iter()).enumerate() {
        assert_eq!(fast.parity, ct.parity, "Regular hint {} parity mismatch", i);
    }

    for (i, (fast, ct)) in backup_fast.iter().zip(backup_ct.iter()).enumerate() {
        assert_eq!(
            fast.parity_in, ct.parity_in,
            "Backup hint {} parity_in mismatch",
            i
        );
        assert_eq!(
            fast.parity_out, ct.parity_out,
            "Backup hint {} parity_out mismatch",
            i
        );
    }

    let has_nonzero_regular = regular_ct.iter().any(|h| h.parity != [0u8; 32]);
    assert!(
        has_nonzero_regular,
        "Should have at least one non-zero regular parity"
    );
}

#[test]
fn test_block_bitset_ct_membership() {
    let blocks = vec![1, 5, 10, 15, 20];
    let bitset = BlockBitset::from_sorted_blocks(&blocks, 32);

    assert_eq!(bitset.contains_ct(0), 0);
    assert_eq!(bitset.contains_ct(1), 1);
    assert_eq!(bitset.contains_ct(5), 1);
    assert_eq!(bitset.contains_ct(6), 0);
    assert_eq!(bitset.contains_ct(10), 1);
    assert_eq!(bitset.contains_ct(15), 1);
    assert_eq!(bitset.contains_ct(20), 1);
    assert_eq!(bitset.contains_ct(31), 0);
    assert_eq!(bitset.contains_ct(100), 0);
}

#[test]
fn test_iprf_tee_inverse_ct_coverage() {
    let key = [42u8; 16];
    let domain = 256u64;
    let range = 16u64;

    let iprf = Iprf::new(key, domain, range);
    let iprf_tee = IprfTee::new(key, domain, range);

    for offset in 0..range {
        let fast_result = iprf.inverse(offset);
        let (ct_array, ct_count) = iprf_tee.inverse_ct(offset);
        let ct_result: Vec<u64> = ct_array[..ct_count].to_vec();

        let mut fast_sorted = fast_result.clone();
        let mut ct_sorted = ct_result.clone();
        fast_sorted.sort();
        ct_sorted.sort();

        assert_eq!(
            fast_sorted, ct_sorted,
            "iPRF inverse mismatch for offset {}",
            offset
        );
    }
}

#[test]
fn test_ct_xor_masked_correctness() {
    let mut dst = [0xAAu8; 32];
    let src = [0x55u8; 32];

    let mut test_dst = dst;
    ct_xor_32_masked(&mut test_dst, &src, 0);
    assert_eq!(test_dst, dst, "mask=0 should not modify dst");

    ct_xor_32_masked(&mut dst, &src, 1);
    assert_eq!(dst, [0xFFu8; 32], "mask=1 should XOR");
}
