//! Bloom filter for fast negative lookup rejection.
//!
//! Copied from libdictenstein's `bloom_filter.rs` (143 lines).
//! Used for O(1) negative rejection before PathMap descent in the pattern index.
//!
//! # A-RT04: Bloom Filter Pre-check for Congruence Rules
//!
//! Additionally used at codegen time by the congruence rule generators
//! (`equations.rs`, `congruence.rs`) to:
//!
//! 1. Track which constructor labels participate in equality/rewrite congruence groups
//! 2. Verify no false negatives at codegen time (`debug_assert!`)
//! 3. Report per-category bloom filter occupancy in lint diagnostics (G37, G38)
//!
//! The bloom filter is consulted during macro expansion to build exact `matches!()`
//! guards on constructor discriminants. These guards skip non-participating
//! constructors before entering the TLS pool match, eliminating:
//! - O(|cat|^2) cross-constructor pairs in equality congruence (via discriminant equality)
//! - O(|cat|) non-participating terms in rewrite congruence (via matches! guard)
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

    /// Insert a string into the Bloom filter (convenience wrapper).
    #[inline]
    pub fn insert_str(&mut self, s: &str) {
        self.insert_bytes(s.as_bytes());
    }

    /// Check if a string might be in the set (convenience wrapper).
    ///
    /// Returns `false` if definitely NOT in set (fast rejection).
    /// Returns `true` if might be in set (requires full check).
    #[inline]
    pub fn might_contain_str(&self, s: &str) -> bool {
        self.might_contain_bytes(s.as_bytes())
    }

    /// Return the number of elements that have been inserted.
    ///
    /// Note: This is an estimate based on the number of `insert_*` calls,
    /// not the actual cardinality (which cannot be determined from the bit vector).
    /// This method counts set bits as a rough occupancy measure.
    #[inline]
    pub fn occupancy(&self) -> usize {
        self.bits.iter().map(|chunk| chunk.count_ones() as usize).sum()
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

    #[test]
    fn test_bloom_filter_str_convenience() {
        let mut bloom = BloomFilter::new(100);
        bloom.insert_str("POutput");
        bloom.insert_str("PPar");
        bloom.insert_str("PNew");
        assert!(bloom.might_contain_str("POutput"));
        assert!(bloom.might_contain_str("PPar"));
        assert!(bloom.might_contain_str("PNew"));
    }

    #[test]
    fn test_bloom_filter_str_no_false_negatives() {
        let constructors = vec![
            "Add", "Sub", "Mul", "Div", "Eq", "Ne", "Gt", "Lt", "GtEq", "LtEq",
            "And", "Or", "Not", "Len", "ConcatStr", "ToInt", "ToFloat", "ToBool",
            "ToStr", "POutput", "PDrop", "PIf", "PNew", "PPar", "NQuote",
        ];
        let mut bloom = BloomFilter::new(constructors.len());
        for ctor in &constructors {
            bloom.insert_str(ctor);
        }
        for ctor in &constructors {
            assert!(
                bloom.might_contain_str(ctor),
                "False negative for constructor: {}",
                ctor
            );
        }
    }

    #[test]
    fn test_bloom_filter_occupancy() {
        let mut bloom = BloomFilter::new(10);
        assert_eq!(bloom.occupancy(), 0);
        bloom.insert_str("hello");
        assert!(bloom.occupancy() > 0);
    }

    // ── Property-based tests ────────────────────────────────────────────────

    use proptest::prelude::*;

    proptest! {
        /// Inserting N arbitrary u64 items and querying each one must always
        /// return `true` — bloom filters guarantee zero false negatives.
        #[test]
        fn prop_no_false_negatives(items in proptest::collection::vec(any::<u64>(), 1..100)) {
            let mut bloom = BloomFilter::new(items.len());
            for item in &items {
                bloom.insert_bytes(&item.to_le_bytes());
            }
            for item in &items {
                prop_assert!(
                    bloom.might_contain_bytes(&item.to_le_bytes()),
                    "False negative for item: {}",
                    item
                );
            }
        }

        /// Insert 100 string-keyed items, then probe 1000 items with keys
        /// guaranteed disjoint from the insert set. The observed false
        /// positive rate must stay below 10% (generous bound; theoretical
        /// rate for 3 hashes at 10 bits/element is ~1%).
        ///
        /// We use string representations rather than raw u64 bytes to avoid
        /// hash-distribution quirks with small-integer LE encodings.
        #[test]
        fn prop_false_positive_rate_bound(
            inserts in proptest::collection::hash_set(0u64..100_000, 100),
        ) {
            let mut bloom = BloomFilter::new(inserts.len());
            for item in &inserts {
                bloom.insert_str(&format!("key_{}", item));
            }

            // Probe 1000 items whose string keys cannot collide with inserted ones
            let mut false_positives = 0usize;
            let probe_count = 1000usize;
            for i in 0..probe_count {
                let probe_key = format!("probe_{}", i);
                if bloom.might_contain_str(&probe_key) {
                    false_positives += 1;
                }
            }

            let fp_rate = false_positives as f64 / probe_count as f64;
            prop_assert!(
                fp_rate < 0.10,
                "False positive rate {} exceeds 10% bound ({} / {})",
                fp_rate,
                false_positives,
                probe_count,
            );
        }
    }
}
