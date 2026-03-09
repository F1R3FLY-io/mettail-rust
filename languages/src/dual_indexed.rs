//! BYODS provider for dual-indexed binary relations (A-RT03).
//!
//! This module provides a data structure provider for Ascent relations that
//! maintains hash-based indices on **both** columns of a binary relation.
//! This ensures O(1) amortized lookups regardless of which column is used
//! as a key in body clauses.
//!
//! # Usage
//!
//! In generated Ascent code, annotate binary relations with:
//! ```text
//! #[ds(crate::dual_indexed)]
//! relation rw_proc(Proc, Proc);
//! ```
//!
//! # Why
//!
//! Ascent's default `::ascent::rel` data structure creates indices based on
//! body clause usage patterns determined at compile time. If no generated
//! rule queries a relation by a particular column, no index is created for
//! that column, forcing a linear scan when custom logic or future rules
//! query it. This provider eagerly maintains both forward and reverse
//! indices, trading a small amount of memory for guaranteed O(1) lookups
//! on either column.
//!
//! # Implementation
//!
//! Uses `hashbrown::HashMap` with FxHasher for both directions:
//! - Forward map (col0 -> col1): `HashMap<T, HashSet<T>>`
//! - Reverse map (col1 -> col0): `HashMap<T, Vec<T>>`
//!
//! Implements `ByodsBinRel` from `ascent-byods-rels` and delegates index
//! type generation to the standard `bin_rel_provider` adaptor types.

use std::hash::{BuildHasherDefault, Hash};

use ascent::internal::{Freezable, RelIndexMerge};
use ascent_byods_rels::adaptor::bin_rel::ByodsBinRel;
use hashbrown::HashMap;
use rustc_hash::FxHasher;

// ---------------------------------------------------------------------------
// Type aliases (matching ascent-byods-rels conventions)
// ---------------------------------------------------------------------------

type FxBuildHasher = BuildHasherDefault<FxHasher>;
type FxHashMap<K, V> = HashMap<K, V, FxBuildHasher>;
type FxHashSet<T> = hashbrown::HashSet<T, FxBuildHasher>;

/// Iterator over elements of an `FxHashSet`.
pub type HashSetIter<'a, T> = hashbrown::hash_set::Iter<'a, T>;

// ---------------------------------------------------------------------------
// DualIndexedRel: the `rel_ind_common` type
// ---------------------------------------------------------------------------

/// A binary relation with hash-based indices on both columns.
///
/// Column 0 (forward): `HashMap<T, HashSet<T>>` -- O(1) lookup by first element.
/// Column 1 (reverse): `HashMap<T, Vec<T>>` -- O(1) lookup by second element.
///
/// Both maps are kept in sync by `insert`. The reverse map uses `Vec<T>` rather
/// than `HashSet<T>` to avoid the overhead of hashing during merge operations,
/// matching the convention used by `ascent-byods-rels::binary_rel::BinaryRel`.
#[derive(Clone)]
pub struct DualIndexedRel<T: Clone + Hash + Eq> {
    /// Forward index: col0 -> set of col1 values.
    forward: FxHashMap<T, FxHashSet<T>>,
    /// Reverse index: col1 -> vec of col0 values.
    reverse: FxHashMap<T, Vec<T>>,
}

impl<T: Clone + Hash + Eq> Default for DualIndexedRel<T> {
    fn default() -> Self {
        Self {
            forward: FxHashMap::default(),
            reverse: FxHashMap::default(),
        }
    }
}

impl<T: Clone + Hash + Eq> DualIndexedRel<T> {
    /// Insert a (col0, col1) pair. Returns `true` if the pair was new.
    #[inline]
    pub fn insert(&mut self, x: T, y: T) -> bool {
        if self.forward.entry(x.clone()).or_default().insert(y.clone()) {
            self.reverse.entry(y).or_default().push(x);
            true
        } else {
            false
        }
    }

    /// Iterate over all (col0, col1) pairs.
    pub fn iter_all(&self) -> impl Iterator<Item = (&T, &T)> + '_ {
        self.forward
            .iter()
            .flat_map(|(x, x_set)| x_set.iter().map(move |y| (x, y)))
    }

    /// Membership test.
    #[inline]
    pub fn contains(&self, x: &T, y: &T) -> bool {
        self.forward.get(x).is_some_and(|s| s.contains(y))
    }

    /// Estimated tuple count (sampled).
    pub fn count_estimate(&self) -> usize {
        let sample_size = 3;
        let sampled = self.forward.values().take(sample_size);
        let sum: usize = sampled.map(|s| s.len()).sum();
        let n = sample_size.min(self.forward.len()).max(1);
        sum * self.forward.len() / n
    }
}

impl<T: Clone + Hash + Eq> RelIndexMerge for DualIndexedRel<T> {
    fn move_index_contents(from: &mut Self, to: &mut Self) {
        // Move all entries from `from` into `to`.
        // This is called during semi-naive evaluation to merge delta into total.
        for (x, y) in from.iter_all() {
            to.insert(x.clone(), y.clone());
        }
        *from = Self::default();
    }
}

impl<T: Clone + Hash + Eq> Freezable for DualIndexedRel<T> {}

// ---------------------------------------------------------------------------
// ByodsBinRel implementation
// ---------------------------------------------------------------------------

impl<T: Clone + Hash + Eq + 'static> ByodsBinRel for DualIndexedRel<T> {
    type T0 = T;
    type T1 = T;

    fn contains(&self, x0: &Self::T0, x1: &Self::T1) -> bool {
        DualIndexedRel::contains(self, x0, x1)
    }

    type AllIter<'a>
        = Box<dyn Iterator<Item = (&'a T, &'a T)> + 'a>
    where
        Self: 'a;

    fn iter_all(&self) -> Self::AllIter<'_> {
        Box::new(DualIndexedRel::iter_all(self))
    }

    fn len_estimate(&self) -> usize {
        self.count_estimate()
    }

    // -- Column 0 (forward index) --

    type Ind0AllIterValsIter<'a>
        = HashSetIter<'a, T>
    where
        Self: 'a;

    type Ind0AllIter<'a>
        = Box<dyn Iterator<Item = (&'a T, Self::Ind0AllIterValsIter<'a>)> + 'a>
    where
        Self: 'a;

    fn ind0_iter_all(&self) -> Self::Ind0AllIter<'_> {
        Box::new(self.forward.iter().map(|(k, v)| (k, v.iter())))
    }

    fn ind0_len_estimate(&self) -> usize {
        self.forward.len()
    }

    type Ind0ValsIter<'a>
        = HashSetIter<'a, T>
    where
        Self: 'a;

    fn ind0_index_get<'a>(&'a self, key: &Self::T0) -> Option<Self::Ind0ValsIter<'a>> {
        self.forward.get(key).map(|set| set.iter())
    }

    // -- Column 1 (reverse index) --

    type Ind1AllIterValsIter<'a>
        = std::slice::Iter<'a, T>
    where
        Self: 'a;

    type Ind1AllIter<'a>
        = Box<dyn Iterator<Item = (&'a T, Self::Ind1AllIterValsIter<'a>)> + 'a>
    where
        Self: 'a;

    fn ind1_iter_all(&self) -> Self::Ind1AllIter<'_> {
        Box::new(self.reverse.iter().map(|(k, v)| (k, v.iter())))
    }

    fn ind1_len_estimate(&self) -> usize {
        self.reverse.len()
    }

    type Ind1ValsIter<'a>
        = std::slice::Iter<'a, T>
    where
        Self: 'a;

    fn ind1_index_get<'a>(&'a self, key: &Self::T1) -> Option<Self::Ind1ValsIter<'a>> {
        self.reverse.get(key).map(|v| v.iter())
    }

    fn insert(&mut self, x0: Self::T0, x1: Self::T1) -> bool {
        DualIndexedRel::insert(self, x0, x1)
    }

    fn is_empty(&self) -> bool {
        self.forward.is_empty()
    }
}

// ---------------------------------------------------------------------------
// BYODS provider macros
// ---------------------------------------------------------------------------
// These macros are invoked by Ascent's codegen when a relation is annotated
// with `#[ds(crate::dual_indexed)]`.

/// Relation storage type: `Vec` -- stores tuples for `.push()` seeding and
/// `.iter()` extraction. The `rel_ind_common` (`DualIndexedRel`) provides
/// the actual indexed lookups during fixpoint evaluation.
///
/// Note: We use `Vec` rather than `FakeVec` because the generated runtime
/// code seeds relations via `.push()` and extracts via `.iter()`. Using
/// `FakeVec` would silently drop seeded data and return zero results.
#[doc(hidden)]
#[macro_export]
macro_rules! dual_indexed_rel {
    ($name:ident, ($col0:ty, $col1:ty), $indices:expr, ser, ()) => {
        ::std::vec::Vec<($col0, $col1)>
    };
}
pub use dual_indexed_rel as rel;

/// Central data structure: `DualIndexedRel<T>`.
#[doc(hidden)]
#[macro_export]
macro_rules! dual_indexed_rel_ind_common {
    ($name:ident, ($col0:ty, $col1:ty), $indices:expr, ser, ()) => {
        $crate::dual_indexed::DualIndexedRel<$col0>
    };
}
pub use dual_indexed_rel_ind_common as rel_ind_common;

/// Full index (both columns bound): delegates to `bin_rel_provider` adaptor.
#[doc(hidden)]
#[macro_export]
macro_rules! dual_indexed_rel_full_ind {
    ($name:ident, ($col0:ty, $col1:ty), $indices:expr, ser, (), $key:ty, $val:ty) => {
        ascent_byods_rels::adaptor::bin_rel::ToByodsBinRelInd0_1<$col0, $col1>
    };
}
pub use dual_indexed_rel_full_ind as rel_full_ind;

/// Per-column index: delegates to `bin_rel_provider` adaptor types.
#[doc(hidden)]
#[macro_export]
macro_rules! dual_indexed_rel_ind {
    ($name:ident, ($col0:ty, $col1:ty), $indices:expr, ser, (), [0], $key:ty, $val:ty) => {
        ascent_byods_rels::adaptor::bin_rel::ToByodsBinRelInd0<$col0, $col1>
    };
    ($name:ident, ($col0:ty, $col1:ty), $indices:expr, ser, (), [1], $key:ty, $val:ty) => {
        ascent_byods_rels::adaptor::bin_rel::ToByodsBinRelInd1<$col0, $col1>
    };
    ($name:ident, ($col0:ty, $col1:ty), $indices:expr, ser, (), [], $key:ty, $val:ty) => {
        ascent_byods_rels::adaptor::bin_rel::ToByodsBinRelIndNone<$col0, $col1>
    };
}
pub use dual_indexed_rel_ind as rel_ind;

/// Codegen hook (no-op for this provider).
#[doc(hidden)]
#[macro_export]
macro_rules! dual_indexed_rel_codegen {
    ($($tt:tt)*) => {};
}
pub use dual_indexed_rel_codegen as rel_codegen;

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use ascent::internal::RelIndexMerge;
    use proptest::prelude::*;
    use std::collections::HashSet;

    // -- Unit tests ----------------------------------------------------------

    #[test]
    fn test_insert_and_contains() {
        let mut rel = DualIndexedRel::default();
        assert!(rel.insert(1, 2));
        assert!(rel.contains(&1, &2));
        assert!(!rel.contains(&2, &1));
    }

    #[test]
    fn test_insert_dedup() {
        let mut rel = DualIndexedRel::default();
        assert!(rel.insert(1, 2), "first insert should return true");
        assert!(!rel.insert(1, 2), "duplicate insert should return false");
    }

    #[test]
    fn test_iter_all_complete() {
        let mut rel = DualIndexedRel::default();
        let pairs = vec![(1, 2), (3, 4), (1, 5), (6, 2)];
        for &(x, y) in &pairs {
            rel.insert(x, y);
        }
        let collected: HashSet<(i32, i32)> =
            rel.iter_all().map(|(&x, &y)| (x, y)).collect();
        let expected: HashSet<(i32, i32)> = pairs.into_iter().collect();
        assert_eq!(collected, expected);
    }

    #[test]
    fn test_forward_lookup() {
        let mut rel = DualIndexedRel::default();
        rel.insert(1, 2);
        rel.insert(1, 3);
        rel.insert(2, 4);

        let vals: HashSet<i32> = rel
            .ind0_index_get(&1)
            .expect("forward lookup for key 1 should exist")
            .cloned()
            .collect();
        assert_eq!(vals, HashSet::from([2, 3]));

        // Key 2 should map to {4}
        let vals2: HashSet<i32> = rel
            .ind0_index_get(&2)
            .expect("forward lookup for key 2 should exist")
            .cloned()
            .collect();
        assert_eq!(vals2, HashSet::from([4]));

        // Key 99 should be absent
        assert!(rel.ind0_index_get(&99).is_none());
    }

    #[test]
    fn test_reverse_lookup() {
        let mut rel = DualIndexedRel::default();
        rel.insert(1, 2);
        rel.insert(3, 2);

        let vals: HashSet<i32> = rel
            .ind1_index_get(&2)
            .expect("reverse lookup for key 2 should exist")
            .cloned()
            .collect();
        assert_eq!(vals, HashSet::from([1, 3]));

        // Key 99 should be absent
        assert!(rel.ind1_index_get(&99).is_none());
    }

    #[test]
    fn test_count_estimate() {
        let mut rel = DualIndexedRel::default();
        let n = 20;
        for i in 0..n {
            rel.insert(i, i + 100);
        }
        // count_estimate is sampled, but for uniform 1-per-key it should be exact
        assert!(
            rel.count_estimate() >= n,
            "count_estimate() = {} should be >= {}",
            rel.count_estimate(),
            n,
        );
    }

    #[test]
    fn test_is_empty() {
        let mut rel: DualIndexedRel<i32> = DualIndexedRel::default();
        assert!(rel.is_empty());
        rel.insert(1, 2);
        assert!(!rel.is_empty());
    }

    #[test]
    fn test_move_index_contents() {
        let mut from = DualIndexedRel::default();
        let mut to = DualIndexedRel::default();

        from.insert(1, 2);
        from.insert(3, 4);
        from.insert(5, 6);

        // Seed `to` with a pre-existing pair to verify merge rather than replace
        to.insert(10, 20);

        DualIndexedRel::move_index_contents(&mut from, &mut to);

        // `from` should be empty after move
        assert!(from.is_empty());
        assert_eq!(from.iter_all().count(), 0);

        // `to` should contain all pairs (original + moved)
        assert!(to.contains(&1, &2));
        assert!(to.contains(&3, &4));
        assert!(to.contains(&5, &6));
        assert!(to.contains(&10, &20));
        assert_eq!(to.iter_all().count(), 4);
    }

    // -- Property-based tests ------------------------------------------------

    proptest! {
        #[test]
        fn prop_bidirectional_consistency(
            pairs in proptest::collection::vec((0..100i32, 0..100i32), 0..50)
        ) {
            let mut rel = DualIndexedRel::default();
            for &(x, y) in &pairs {
                rel.insert(x, y);
            }
            let unique: HashSet<(i32, i32)> = pairs.into_iter().collect();
            for &(x, y) in &unique {
                prop_assert!(rel.contains(&x, &y),
                    "contains({}, {}) should be true", x, y);
                let fwd: HashSet<i32> = rel.ind0_index_get(&x)
                    .expect("forward index should exist")
                    .cloned()
                    .collect();
                prop_assert!(fwd.contains(&y),
                    "ind0_index_get({}) should contain {}", x, y);
                let rev: HashSet<i32> = rel.ind1_index_get(&y)
                    .expect("reverse index should exist")
                    .cloned()
                    .collect();
                prop_assert!(rev.contains(&x),
                    "ind1_index_get({}) should contain {}", y, x);
            }
        }

        #[test]
        fn prop_insert_roundtrip(x in any::<i32>(), y in any::<i32>()) {
            let mut rel = DualIndexedRel::default();
            rel.insert(x, y);
            prop_assert!(rel.contains(&x, &y),
                "after insert({}, {}), contains should be true", x, y);
        }

        #[test]
        fn prop_iter_all_count(
            pairs in proptest::collection::vec((0..50i32, 0..50i32), 0..30)
        ) {
            let mut rel = DualIndexedRel::default();
            let mut unique = HashSet::new();
            for &(x, y) in &pairs {
                rel.insert(x, y);
                unique.insert((x, y));
            }
            prop_assert_eq!(
                rel.iter_all().count(),
                unique.len(),
                "iter_all count should equal unique pair count"
            );
        }
    }
}
