//! Fast, deterministic hashing for the e-graph's internal integer keys.
//!
//! The e-graph, extractor, WTA, SCC pass, and set-automaton index all key their
//! maps/sets on [`EClassId`](crate::egraph::EClassId) (a `usize` newtype) and on
//! `ENode<L>` (an op plus a `SmallVec` of `EClassId` children). Profiling the
//! Dovetail saturation baseline (`docs/benchmarks/rho-native-baselines.md`) showed
//! **~16 % of saturation wall-time in SipHash-1-3** (the default `RandomState`),
//! which exists for HrDoS resistance on *untrusted* keys — irrelevant for these
//! internal, integer-shaped keys.
//!
//! This module provides the FxHash algorithm (the multiply-rotate-xor hash rustc
//! and Firefox use) as an inline `Hasher`, so dovetail keeps `rigail` as its only
//! external dependency (see `Cargo.toml`) instead of pulling in `rustc-hash`. The
//! specialized `write_u*` paths make hashing an `EClassId`/`usize` a single
//! multiply — the hot path.
//!
//! FxHash is fully deterministic (unlike `RandomState`, which is process-seeded),
//! so results are stable across runs; e-graph algorithms never depend on hash
//! iteration order (they were already correct under process-varying `RandomState`),
//! so swapping the hasher changes only speed, not results.

use core::hash::{BuildHasherDefault, Hasher};

/// The 64-bit FxHash multiplier (odd, well-distributed high bits).
const SEED64: u64 = 0x51_7c_c1_b7_27_22_0a_95;
/// FxHash rotates the running hash by 5 bits before mixing each word.
const ROTATE: u32 = 5;

/// A fast, deterministic non-cryptographic hasher (FxHash).
#[derive(Default)]
pub struct FxHasher {
    hash: u64,
}

impl FxHasher {
    #[inline]
    fn add_to_hash(&mut self, word: u64) {
        self.hash = (self.hash.rotate_left(ROTATE) ^ word).wrapping_mul(SEED64);
    }
}

impl Hasher for FxHasher {
    #[inline]
    fn finish(&self) -> u64 {
        self.hash
    }

    #[inline]
    fn write(&mut self, mut bytes: &[u8]) {
        // Word-at-a-time over the aligned prefix, then the ragged tail.
        while bytes.len() >= 8 {
            let mut buf = [0u8; 8];
            buf.copy_from_slice(&bytes[..8]);
            self.add_to_hash(u64::from_le_bytes(buf));
            bytes = &bytes[8..];
        }
        if bytes.len() >= 4 {
            let mut buf = [0u8; 4];
            buf.copy_from_slice(&bytes[..4]);
            self.add_to_hash(u32::from_le_bytes(buf) as u64);
            bytes = &bytes[4..];
        }
        if bytes.len() >= 2 {
            let mut buf = [0u8; 2];
            buf.copy_from_slice(&bytes[..2]);
            self.add_to_hash(u16::from_le_bytes(buf) as u64);
            bytes = &bytes[2..];
        }
        if let Some(&b) = bytes.first() {
            self.add_to_hash(b as u64);
        }
    }

    // Integer specializations — the hot path: an `EClassId`/`usize` key mixes in a
    // single multiply rather than routing through the byte-slice path.
    #[inline]
    fn write_u8(&mut self, i: u8) {
        self.add_to_hash(i as u64);
    }
    #[inline]
    fn write_u16(&mut self, i: u16) {
        self.add_to_hash(i as u64);
    }
    #[inline]
    fn write_u32(&mut self, i: u32) {
        self.add_to_hash(i as u64);
    }
    #[inline]
    fn write_u64(&mut self, i: u64) {
        self.add_to_hash(i);
    }
    #[inline]
    fn write_usize(&mut self, i: usize) {
        self.add_to_hash(i as u64);
    }
}

/// `BuildHasher` for [`FxHasher`], usable as the `S` parameter of `HashMap`/`HashSet`.
pub type FxBuildHasher = BuildHasherDefault<FxHasher>;

/// Drop-in `HashMap` keyed with [`FxHasher`]. Construct with `HashMap::default()`
/// (there is no `new()` for a non-`RandomState` hasher).
pub type HashMap<K, V> = std::collections::HashMap<K, V, FxBuildHasher>;

/// Drop-in `HashSet` keyed with [`FxHasher`]. Construct with `HashSet::default()`.
pub type HashSet<K> = std::collections::HashSet<K, FxBuildHasher>;

#[cfg(test)]
mod tests {
    use super::*;
    use std::hash::Hash;

    fn hash_of<T: Hash>(value: &T) -> u64 {
        let mut hasher = FxHasher::default();
        value.hash(&mut hasher);
        hasher.finish()
    }

    #[test]
    fn deterministic_across_instances() {
        assert_eq!(hash_of(&42usize), hash_of(&42usize));
        assert_eq!(hash_of(&"swap"), hash_of(&"swap"));
    }

    #[test]
    fn distinguishes_distinct_small_ints() {
        // The keys the e-graph actually uses: small, dense integers must not collide.
        let hashes: std::collections::HashSet<u64> = (0u64..1000).map(|i| hash_of(&i)).collect();
        assert_eq!(hashes.len(), 1000, "small-int keys must be collision-free");
    }

    #[test]
    fn map_roundtrips() {
        let mut map: HashMap<usize, &str> = HashMap::default();
        map.insert(7, "seven");
        assert_eq!(map.get(&7), Some(&"seven"));
    }
}
