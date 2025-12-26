use rand::SeedableRng;
use rand_chacha::ChaCha20Rng;

use crate::hint_gen::keys::random_subset;

pub fn compute_regular_blocks(seed: &[u8; 32], c: usize) -> Vec<usize> {
    let regular_subset_size = c / 2 + 1;
    let mut rng = ChaCha20Rng::from_seed(*seed);
    let mut blocks = random_subset(&mut rng, regular_subset_size, c);
    blocks.sort_unstable();
    blocks
}

pub fn compute_backup_blocks(seed: &[u8; 32], c: usize) -> Vec<usize> {
    let backup_subset_size = c / 2;
    let mut rng = ChaCha20Rng::from_seed(*seed);
    let mut blocks = random_subset(&mut rng, backup_subset_size, c);
    blocks.sort_unstable();
    blocks
}

/// Returns true if `block` is in the sorted `blocks` slice.
///
/// Precondition: `blocks` must be sorted in ascending order.
pub fn block_in_subset(blocks: &[usize], block: usize) -> bool {
    blocks.binary_search(&block).is_ok()
}

pub fn xor_32(dst: &mut [u8; 32], src: &[u8; 32]) {
    for i in 0..32 {
        dst[i] ^= src[i];
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_block_in_subset() {
        let blocks = vec![1, 3, 5, 7, 9];
        assert!(block_in_subset(&blocks, 5));
        assert!(!block_in_subset(&blocks, 6));
        assert!(block_in_subset(&blocks, 1));
        assert!(!block_in_subset(&blocks, 0));
    }

    #[test]
    fn test_xor_32_identity() {
        let mut a = [0xABu8; 32];
        let b = [0u8; 32];
        let original = a;
        xor_32(&mut a, &b);
        assert_eq!(a, original);
    }

    #[test]
    fn test_xor_32_inverse() {
        let mut a = [0x12u8; 32];
        let b = [0x34u8; 32];
        let original = a;
        xor_32(&mut a, &b);
        xor_32(&mut a, &b);
        assert_eq!(a, original);
    }

    #[test]
    fn test_compute_regular_blocks_size() {
        let seed = [8u8; 32];
        let c = 100;
        let blocks = compute_regular_blocks(&seed, c);
        assert_eq!(blocks.len(), c / 2 + 1);
    }

    #[test]
    fn test_compute_backup_blocks_size() {
        let seed = [9u8; 32];
        let c = 100;
        let blocks = compute_backup_blocks(&seed, c);
        assert_eq!(blocks.len(), c / 2);
    }

    #[test]
    fn test_compute_blocks_deterministic() {
        let seed = [10u8; 32];
        let c = 50;
        let blocks1 = compute_regular_blocks(&seed, c);
        let blocks2 = compute_regular_blocks(&seed, c);
        assert_eq!(blocks1, blocks2);
    }
}
