pub struct BlockBitset {
    bits: Vec<u64>,
    num_blocks: usize,
}

impl BlockBitset {
    pub fn new(num_blocks: usize) -> Self {
        let num_words = num_blocks.div_ceil(64);
        Self {
            bits: vec![0u64; num_words],
            num_blocks,
        }
    }

    pub fn from_sorted_blocks(blocks: &[usize], num_blocks: usize) -> Self {
        let mut bitset = Self::new(num_blocks);
        for &block in blocks {
            if block < num_blocks {
                bitset.bits[block / 64] |= 1u64 << (block % 64);
            }
        }
        bitset
    }

    #[inline]
    pub fn contains_ct(&self, block: usize) -> u64 {
        if block >= self.num_blocks {
            return 0;
        }
        let word_idx = block / 64;
        let bit_idx = block % 64;
        (self.bits[word_idx] >> bit_idx) & 1
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_bitset_membership() {
        let blocks = vec![1, 3, 5, 7, 9];
        let bitset = BlockBitset::from_sorted_blocks(&blocks, 10);
        assert_eq!(bitset.contains_ct(0), 0);
        assert_eq!(bitset.contains_ct(1), 1);
        assert_eq!(bitset.contains_ct(2), 0);
        assert_eq!(bitset.contains_ct(3), 1);
        assert_eq!(bitset.contains_ct(5), 1);
        assert_eq!(bitset.contains_ct(9), 1);
        assert_eq!(bitset.contains_ct(10), 0);
    }
}
