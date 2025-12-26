use rand_chacha::ChaCha20Rng;
use sha2::{Digest, Sha256};
use state_syncer::iprf::PrfKey128;

pub fn derive_block_keys(master_seed: &[u8; 32], c: usize) -> Vec<PrfKey128> {
    let mut keys = Vec::with_capacity(c);
    for block_idx in 0..c {
        let mut hasher = Sha256::new();
        hasher.update(master_seed);
        hasher.update(b"block_key");
        hasher.update(&(block_idx as u64).to_le_bytes());
        let hash = hasher.finalize();
        let mut key = [0u8; 16];
        key.copy_from_slice(&hash[0..16]);
        keys.push(key);
    }
    keys
}

pub fn derive_subset_seed(master_seed: &[u8; 32], label: &[u8], idx: u64) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(master_seed);
    hasher.update(label);
    hasher.update(&idx.to_le_bytes());
    let hash = hasher.finalize();
    let mut seed = [0u8; 32];
    seed.copy_from_slice(&hash[0..32]);
    seed
}

pub fn random_subset(rng: &mut ChaCha20Rng, size: usize, total: usize) -> Vec<usize> {
    use rand::seq::index::sample;
    sample(rng, total, size).into_vec()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hint_gen::types::{SEED_LABEL_BACKUP, SEED_LABEL_REGULAR};
    use rand::SeedableRng;

    #[test]
    fn test_derive_block_keys_deterministic() {
        let seed = [0u8; 32];
        let keys1 = derive_block_keys(&seed, 10);
        let keys2 = derive_block_keys(&seed, 10);
        assert_eq!(keys1, keys2);
    }

    #[test]
    fn test_derive_block_keys_unique() {
        let seed = [1u8; 32];
        let keys = derive_block_keys(&seed, 100);
        for i in 0..keys.len() {
            for j in (i + 1)..keys.len() {
                assert_ne!(keys[i], keys[j], "Keys {} and {} should differ", i, j);
            }
        }
    }

    #[test]
    fn test_random_subset_size() {
        let mut rng = ChaCha20Rng::from_seed([2u8; 32]);
        let subset = random_subset(&mut rng, 5, 10);
        assert_eq!(subset.len(), 5);
    }

    #[test]
    fn test_random_subset_bounds() {
        let mut rng = ChaCha20Rng::from_seed([3u8; 32]);
        let subset = random_subset(&mut rng, 10, 100);
        for &x in &subset {
            assert!(x < 100);
        }
    }

    #[test]
    fn test_random_subset_unique() {
        let mut rng = ChaCha20Rng::from_seed([4u8; 32]);
        let subset = random_subset(&mut rng, 20, 100);
        let mut sorted = subset.clone();
        sorted.sort_unstable();
        sorted.dedup();
        assert_eq!(
            sorted.len(),
            subset.len(),
            "subset should have no duplicates"
        );
    }

    #[test]
    fn test_derive_subset_seed_deterministic() {
        let master = [5u8; 32];
        let seed1 = derive_subset_seed(&master, SEED_LABEL_REGULAR, 42);
        let seed2 = derive_subset_seed(&master, SEED_LABEL_REGULAR, 42);
        assert_eq!(seed1, seed2);
    }

    #[test]
    fn test_derive_subset_seed_unique_per_index() {
        let master = [6u8; 32];
        let seed1 = derive_subset_seed(&master, SEED_LABEL_REGULAR, 0);
        let seed2 = derive_subset_seed(&master, SEED_LABEL_REGULAR, 1);
        assert_ne!(seed1, seed2);
    }

    #[test]
    fn test_derive_subset_seed_unique_per_label() {
        let master = [7u8; 32];
        let seed1 = derive_subset_seed(&master, SEED_LABEL_REGULAR, 0);
        let seed2 = derive_subset_seed(&master, SEED_LABEL_BACKUP, 0);
        assert_ne!(seed1, seed2);
    }
}
