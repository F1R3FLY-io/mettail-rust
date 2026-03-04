//! Bloom filter for fast negative lookup rejection.
//!
//! Copied from libdictenstein's `bloom_filter.rs` (143 lines).
//! Used for O(1) negative rejection before PathMap descent in the pattern index.
//!
//! # Characteristics
//!
//! - **False positives**: Possible (requires full trie traversal to confirm)
//! - **False negatives**: Never (guaranteed correct rejection)
//! - **Target false positive rate**: ~1% with 3 hash functions
//! - **Memory usage**: ~1.2 bytes per expected element (10 bits per element)

use rustc_hash::FxHasher;
use std::hash::{Hash, Hasher};

/// Simple Bloom filter for fast negative lookup rejection.
///
/// Uses 3 hash functions and a bit vector to probabilistically test membership.
/// - False positives: Possible (requires full PathMap traversal)
/// - False negatives: Never (guaranteed correct rejection)
#[derive(Debug, Clone)]
pub struct BloomFilter {
    bits: Vec<u64>,
    bit_count: usize,
    hash_count: usize,
}

impl BloomFilter {
    /// Create a new Bloom filter with specified capacity.
    ///
    /// Uses ~1.2 bytes per expected element with 3 hash functions.
    /// Target false positive rate: ~1%
    pub fn new(expected_elements: usize) -> Self {
        let bit_count = expected_elements.saturating_mul(10).max(64);
        let chunk_count = (bit_count + 63) / 64;

        BloomFilter {
            bits: vec![0u64; chunk_count],
            bit_count: chunk_count * 64,
            hash_count: 3,
        }
    }

    /// Add raw bytes to the Bloom filter.
    #[inline]
    pub fn insert_bytes(&mut self, bytes: &[u8]) {
        for i in 0..self.hash_count {
            let hash = self.hash_with_seed(bytes, i as u64);
            let bit_index = (hash % self.bit_count as u64) as usize;
            let chunk_index = bit_index / 64;
            let bit_offset = bit_index % 64;
            self.bits[chunk_index] |= 1u64 << bit_offset;
        }
    }

    /// Check if raw bytes might be in the set.
    ///
    /// Returns `false` if definitely NOT in set (fast rejection).
    /// Returns `true` if might be in set (requires full check).
    #[inline]
    pub fn might_contain_bytes(&self, bytes: &[u8]) -> bool {
        for i in 0..self.hash_count {
            let hash = self.hash_with_seed(bytes, i as u64);
            let bit_index = (hash % self.bit_count as u64) as usize;
            let chunk_index = bit_index / 64;
            let bit_offset = bit_index % 64;
            if (self.bits[chunk_index] & (1u64 << bit_offset)) == 0 {
                return false;
            }
        }
        true
    }

    /// Hash bytes with a seed using FxHash.
    #[inline]
    fn hash_with_seed(&self, bytes: &[u8], seed: u64) -> u64 {
        let mut hasher = FxHasher::default();
        seed.hash(&mut hasher);
        bytes.hash(&mut hasher);
        hasher.finish()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_bloom_filter_basic() {
        let mut bloom = BloomFilter::new(100);
        bloom.insert_bytes(b"hello");
        bloom.insert_bytes(b"world");
        assert!(bloom.might_contain_bytes(b"hello"));
        assert!(bloom.might_contain_bytes(b"world"));
    }

    #[test]
    fn test_bloom_filter_no_false_negatives() {
        let mut bloom = BloomFilter::new(1000);
        let terms: Vec<Vec<u8>> = (0..100).map(|i| format!("term{}", i).into_bytes()).collect();
        for term in &terms {
            bloom.insert_bytes(term);
        }
        for term in &terms {
            assert!(
                bloom.might_contain_bytes(term),
                "False negative for: {:?}",
                term
            );
        }
    }

    #[test]
    fn test_bloom_filter_bytes() {
        let mut bloom = BloomFilter::new(100);
        bloom.insert_bytes(&[0x10, 0x20, 0x30]);
        assert!(bloom.might_contain_bytes(&[0x10, 0x20, 0x30]));
    }
}
