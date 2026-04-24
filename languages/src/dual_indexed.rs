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
use std::marker::PhantomData;
use std::sync::Mutex;

use std::rc::Rc;

use ascent::internal::{
    CRelFullIndexWrite, CRelIndexWrite, Freezable, RelFullIndexRead, RelFullIndexWrite,
    RelIndexMerge, RelIndexRead, RelIndexReadAll, RelIndexWrite,
    ToRelIndex, ToRelIndex0,
};
use ascent::internal::{CRelIndexRead, CRelIndexReadAll};
use ascent::rayon;
use ascent::rayon::iter::{IntoParallelRefIterator, ParallelIterator};
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
// IteratorFromDyn: clonable dynamic iterator (matches ascent-byods-rels pattern)
// ---------------------------------------------------------------------------

/// A clonable iterator backed by a boxed `dyn Iterator` and an `Rc`-wrapped
/// producer closure that can recreate the iterator on clone.
///
/// This mirrors the private `IteratorFromDyn` in `ascent-byods-rels`.
pub struct IteratorFromDyn<'a, T> {
    iter: Box<dyn Iterator<Item = T> + 'a>,
    producer: Rc<dyn Fn() -> Box<dyn Iterator<Item = T> + 'a> + 'a>,
}

impl<'a, T> IteratorFromDyn<'a, T> {
    pub fn new<F: Fn() -> Iter + 'a, Iter: Iterator<Item = T> + 'a>(producer: F) -> Self {
        Self::from_box_clo(move || Box::new(producer()))
    }

    pub fn from_box_clo<F: Fn() -> Box<dyn Iterator<Item = T> + 'a> + 'a>(producer: F) -> Self {
        let iter = producer();
        Self {
            iter,
            producer: Rc::new(producer) as _,
        }
    }
}

impl<T> Iterator for IteratorFromDyn<'_, T> {
    type Item = T;

    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next()
    }
}

impl<T> Clone for IteratorFromDyn<'_, T> {
    fn clone(&self) -> Self {
        Self {
            iter: (self.producer)(),
            producer: self.producer.clone(),
        }
    }
}

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
// Concurrent dual-indexed relation for ascent_par!
// ---------------------------------------------------------------------------

/// Convert `&T` to `&(T,)`. Sound because `(T,)` has the same repr as `T`.
/// Same pattern as `ceqrel_ind.rs` in ascent-byods-rels.
pub(crate) fn ref_to_singleton_tuple_ref<T>(x: &T) -> &(T,) {
    unsafe { std::mem::transmute(x) }
}

/// Concurrent dual-indexed binary relation for `ascent_par!`.
///
/// Uses an enum state machine following the `CEqRelIndCommon` pattern:
/// - `Unfrozen`: Writable via `Mutex<DualIndexedRel<T>>` for concurrent access
/// - `Frozen`: Immutable snapshot for parallel reads via Rayon iterators
pub enum CDualIndexedRel<T: Clone + Hash + Eq> {
    Unfrozen(Mutex<DualIndexedRel<T>>),
    Frozen(DualIndexedRel<T>),
}

impl<T: Clone + Hash + Eq> CDualIndexedRel<T> {
    fn unwrap_frozen(&self) -> &DualIndexedRel<T> {
        match self {
            CDualIndexedRel::Frozen(rel) => rel,
            CDualIndexedRel::Unfrozen(_) => {
                panic!("CDualIndexedRel: unexpected state (unwrap_frozen called on Unfrozen)")
            }
        }
    }

    fn unwrap_mut_frozen(&mut self) -> &mut DualIndexedRel<T> {
        match self {
            CDualIndexedRel::Frozen(rel) => rel,
            CDualIndexedRel::Unfrozen(_) => {
                panic!("CDualIndexedRel: unexpected state (unwrap_mut_frozen called on Unfrozen)")
            }
        }
    }

    fn unwrap_unfrozen(&self) -> &Mutex<DualIndexedRel<T>> {
        match self {
            CDualIndexedRel::Unfrozen(m) => m,
            CDualIndexedRel::Frozen(_) => {
                panic!("CDualIndexedRel: unexpected state (unwrap_unfrozen called on Frozen)")
            }
        }
    }

    fn unwrap_mut_unfrozen(&mut self) -> &mut DualIndexedRel<T> {
        match self {
            CDualIndexedRel::Unfrozen(m) => m.get_mut().expect(
                "CDualIndexedRel: unexpected state (unwrap_mut_unfrozen: mutex poisoned)",
            ),
            CDualIndexedRel::Frozen(_) => {
                panic!(
                    "CDualIndexedRel: unexpected state (unwrap_mut_unfrozen called on Frozen)"
                )
            }
        }
    }
}

impl<T: Clone + Hash + Eq> Default for CDualIndexedRel<T> {
    fn default() -> Self {
        CDualIndexedRel::Frozen(DualIndexedRel::default())
    }
}

impl<T: Clone + Hash + Eq> Clone for CDualIndexedRel<T> {
    fn clone(&self) -> Self {
        match self {
            CDualIndexedRel::Unfrozen(m) => CDualIndexedRel::Unfrozen(Mutex::new(
                m.lock()
                    .expect("CDualIndexedRel: unexpected state (clone: mutex poisoned)")
                    .clone(),
            )),
            CDualIndexedRel::Frozen(rel) => CDualIndexedRel::Frozen(rel.clone()),
        }
    }
}

impl<T: Clone + Hash + Eq> Freezable for CDualIndexedRel<T> {
    // No-op: state transitions are managed by RelIndexMerge.
}

impl<T: Clone + Hash + Eq> RelIndexMerge for CDualIndexedRel<T> {
    fn move_index_contents(_from: &mut Self, _to: &mut Self) {
        unimplemented!("merge_delta_to_total_new_to_delta must be used instead")
    }

    fn init(new: &mut Self, _delta: &mut Self, _total: &mut Self) {
        *new = CDualIndexedRel::Unfrozen(Mutex::new(DualIndexedRel::default()));
    }

    fn merge_delta_to_total_new_to_delta(new: &mut Self, delta: &mut Self, total: &mut Self) {
        // Merge delta (Frozen) into total (Frozen).
        let total_inner = total.unwrap_mut_frozen();
        let delta_inner = delta.unwrap_mut_frozen();
        for (x, y) in delta_inner.iter_all() {
            total_inner.insert(x.clone(), y.clone());
        }

        // Take new's unfrozen content as the new delta (Frozen).
        let new_content = std::mem::take(new.unwrap_mut_unfrozen());
        *delta = CDualIndexedRel::Frozen(new_content);

        // Reset new to empty Unfrozen.
        *new = CDualIndexedRel::Unfrozen(Mutex::new(DualIndexedRel::default()));
    }
}

impl<T: Clone + Hash + Eq> RelIndexWrite for CDualIndexedRel<T> {
    type Key = (T, T);
    type Value = ();

    fn index_insert(&mut self, key: Self::Key, _value: Self::Value) {
        self.unwrap_mut_unfrozen().insert(key.0, key.1);
    }
}

impl<T: Clone + Hash + Eq> CRelIndexWrite for CDualIndexedRel<T> {
    type Key = (T, T);
    type Value = ();

    fn index_insert(&self, key: Self::Key, _value: Self::Value) {
        self.unwrap_unfrozen()
            .lock()
            .expect("CDualIndexedRel: unexpected state (CRelIndexWrite: mutex poisoned)")
            .insert(key.0, key.1);
    }
}

impl<T: Clone + Hash + Eq> RelFullIndexWrite for CDualIndexedRel<T> {
    type Key = (T, T);
    type Value = ();

    fn insert_if_not_present(&mut self, key: &Self::Key, _v: Self::Value) -> bool {
        self.unwrap_mut_unfrozen()
            .insert(key.0.clone(), key.1.clone())
    }
}

impl<T: Clone + Hash + Eq> CRelFullIndexWrite for CDualIndexedRel<T> {
    type Key = (T, T);
    type Value = ();

    fn insert_if_not_present(&self, key: &Self::Key, _v: Self::Value) -> bool {
        self.unwrap_unfrozen()
            .lock()
            .expect("CDualIndexedRel: unexpected state (CRelFullIndexWrite: mutex poisoned)")
            .insert(key.0.clone(), key.1.clone())
    }
}

impl<'a, T: Clone + Hash + Eq + 'a> RelIndexRead<'a> for CDualIndexedRel<T> {
    type Key = (T, T);
    type Value = ();
    type IteratorType = std::iter::Once<()>;

    fn index_get(&'a self, key: &Self::Key) -> Option<Self::IteratorType> {
        let rel = self.unwrap_frozen();
        if rel.contains(&key.0, &key.1) {
            Some(std::iter::once(()))
        } else {
            None
        }
    }

    fn len_estimate(&self) -> usize {
        self.unwrap_frozen().count_estimate()
    }
}

impl<'a, T: Clone + Hash + Eq + Sync + 'a> CRelIndexRead<'a> for CDualIndexedRel<T> {
    type Key = (T, T);
    type Value = ();
    type IteratorType = rayon::iter::Once<()>;

    fn c_index_get(&'a self, key: &Self::Key) -> Option<Self::IteratorType> {
        let rel = self.unwrap_frozen();
        if rel.contains(&key.0, &key.1) {
            Some(rayon::iter::once(()))
        } else {
            None
        }
    }
}

impl<'a, T: Clone + Hash + Eq + 'a> RelIndexReadAll<'a> for CDualIndexedRel<T> {
    type Key = (&'a T, &'a T);
    type Value = ();
    type ValueIteratorType = std::iter::Once<()>;
    type AllIteratorType = Box<dyn Iterator<Item = (Self::Key, Self::ValueIteratorType)> + 'a>;

    fn iter_all(&'a self) -> Self::AllIteratorType {
        Box::new(
            self.unwrap_frozen()
                .iter_all()
                .map(|pair| (pair, std::iter::once(()))),
        )
    }
}

impl<'a, T: Clone + Hash + Eq + Sync + Send + 'a> CRelIndexReadAll<'a> for CDualIndexedRel<T> {
    type Key = (&'a T, &'a T);
    type Value = ();
    type ValueIteratorType = rayon::iter::Once<()>;
    type AllIteratorType = rayon::iter::Map<
        DualAllPairsParIter<'a, T>,
        fn((&'a T, &'a T)) -> ((&'a T, &'a T), rayon::iter::Once<()>),
    >;

    fn c_iter_all(&'a self) -> Self::AllIteratorType {
        DualAllPairsParIter(self.unwrap_frozen()).map(|pair| (pair, rayon::iter::once(())))
    }
}

impl<'a, T: Clone + Hash + Eq> RelFullIndexRead<'a> for CDualIndexedRel<T> {
    type Key = (T, T);

    fn contains_key(&'a self, key: &Self::Key) -> bool {
        self.unwrap_frozen().contains(&key.0, &key.1)
    }
}

// ---------------------------------------------------------------------------
// DualInd0: forward index (col0 -> col1)
// ---------------------------------------------------------------------------

pub struct DualInd0<'a, T: Clone + Hash + Eq>(pub(crate) &'a CDualIndexedRel<T>);

impl<'a, T: Clone + Hash + Eq> RelIndexRead<'a> for DualInd0<'a, T> {
    type Key = (T,);
    type Value = (&'a T,);
    type IteratorType = std::iter::Map<HashSetIter<'a, T>, fn(&T) -> (&T,)>;

    fn index_get(&'a self, key: &Self::Key) -> Option<Self::IteratorType> {
        self.0
            .unwrap_frozen()
            .forward
            .get(&key.0)
            .map(|set| set.iter().map((|x| (x,)) as fn(&T) -> (&T,)))
    }

    fn len_estimate(&self) -> usize {
        self.0.unwrap_frozen().forward.len()
    }
}

/// Clonable parallel iterator over values in a forward-index `FxHashSet`.
/// Stores a reference to the set rather than the non-Clone `ParIter` itself.
#[derive(Clone)]
pub struct DualInd0CRelReadIter<'a, T: Clone + Hash + Eq + Sync> {
    set: &'a FxHashSet<T>,
}

impl<'a, T: Clone + Hash + Eq + Sync + Send> ParallelIterator for DualInd0CRelReadIter<'a, T> {
    type Item = (&'a T,);

    fn drive_unindexed<C>(self, consumer: C) -> C::Result
    where
        C: rayon::iter::plumbing::UnindexedConsumer<Self::Item>,
    {
        self.set
            .par_iter()
            .map(|x| (x,))
            .drive_unindexed(consumer)
    }
}

impl<'a, T: Clone + Hash + Eq + Sync + Send> CRelIndexRead<'a> for DualInd0<'a, T> {
    type Key = (T,);
    type Value = (&'a T,);
    type IteratorType = DualInd0CRelReadIter<'a, T>;

    fn c_index_get(&'a self, key: &Self::Key) -> Option<Self::IteratorType> {
        self.0
            .unwrap_frozen()
            .forward
            .get(&key.0)
            .map(|set| DualInd0CRelReadIter { set })
    }
}

impl<'a, T: Clone + Hash + Eq> RelIndexReadAll<'a> for DualInd0<'a, T> {
    type Key = &'a (T,);
    type Value = (&'a T,);
    type ValueIteratorType = std::iter::Map<HashSetIter<'a, T>, for<'aa> fn(&'aa T) -> (&'aa T,)>;
    type AllIteratorType = Box<dyn Iterator<Item = (Self::Key, Self::ValueIteratorType)> + 'a>;

    fn iter_all(&'a self) -> Self::AllIteratorType {
        Box::new(
            self.0
                .unwrap_frozen()
                .forward
                .iter()
                .map(|(k, v)| {
                    (
                        ref_to_singleton_tuple_ref(k),
                        v.iter().map((|x| (x,)) as for<'aa> fn(&'aa T) -> (&'aa T,)),
                    )
                }),
        )
    }
}

/// Parallel iterator over `DualInd0`'s forward index entries.
/// Yields `(key_ref, par_iter_over_values)` for each forward-map entry.
#[derive(Clone)]
pub struct DualInd0ParIter<'a, T: Clone + Hash + Eq + Sync>(&'a DualIndexedRel<T>);

impl<'a, T: Clone + Hash + Eq + Sync + Send> ParallelIterator for DualInd0ParIter<'a, T> {
    type Item = (
        &'a (T,),
        rayon::iter::Map<hashbrown::hash_set::rayon::ParIter<'a, T>, fn(&T) -> (&T,)>,
    );

    fn drive_unindexed<C>(self, consumer: C) -> C::Result
    where
        C: rayon::iter::plumbing::UnindexedConsumer<Self::Item>,
    {
        self.0
            .forward
            .par_iter()
            .map(|(k, v)| {
                let vals: rayon::iter::Map<
                    hashbrown::hash_set::rayon::ParIter<'a, T>,
                    fn(&T) -> (&T,),
                > = v.par_iter().map(|x| (x,));
                (ref_to_singleton_tuple_ref(k), vals)
            })
            .drive_unindexed(consumer)
    }
}

impl<'a, T: Clone + Hash + Eq + Sync + Send> CRelIndexReadAll<'a> for DualInd0<'a, T> {
    type Key = &'a (T,);
    type Value = (&'a T,);
    type ValueIteratorType =
        rayon::iter::Map<hashbrown::hash_set::rayon::ParIter<'a, T>, fn(&T) -> (&T,)>;
    type AllIteratorType = DualInd0ParIter<'a, T>;

    fn c_iter_all(&'a self) -> Self::AllIteratorType {
        DualInd0ParIter(self.0.unwrap_frozen())
    }
}

impl<T: Clone + Hash + Eq> RelIndexWrite for DualInd0<'_, T> {
    type Key = (T,);
    type Value = (T,);
    fn index_insert(&mut self, _key: Self::Key, _value: Self::Value) { /* noop */ }
}

impl<T: Clone + Hash + Eq> CRelIndexWrite for DualInd0<'_, T> {
    type Key = (T,);
    type Value = (T,);
    fn index_insert(&self, _key: Self::Key, _value: Self::Value) { /* noop */ }
}

impl<T: Clone + Hash + Eq> RelIndexMerge for DualInd0<'_, T> {
    fn move_index_contents(_from: &mut Self, _to: &mut Self) { /* noop */ }
}

// ---------------------------------------------------------------------------
// DualInd1: reverse index (col1 -> col0)
// ---------------------------------------------------------------------------

pub struct DualInd1<'a, T: Clone + Hash + Eq>(pub(crate) &'a CDualIndexedRel<T>);

impl<'a, T: Clone + Hash + Eq> RelIndexRead<'a> for DualInd1<'a, T> {
    type Key = (T,);
    type Value = (&'a T,);
    type IteratorType = std::iter::Map<std::slice::Iter<'a, T>, fn(&T) -> (&T,)>;

    fn index_get(&'a self, key: &Self::Key) -> Option<Self::IteratorType> {
        self.0
            .unwrap_frozen()
            .reverse
            .get(&key.0)
            .map(|v| v.iter().map((|x| (x,)) as fn(&T) -> (&T,)))
    }

    fn len_estimate(&self) -> usize {
        self.0.unwrap_frozen().reverse.len()
    }
}

impl<'a, T: Clone + Hash + Eq + Sync + Send> CRelIndexRead<'a> for DualInd1<'a, T> {
    type Key = (T,);
    type Value = (&'a T,);
    type IteratorType =
        rayon::iter::Map<rayon::slice::Iter<'a, T>, fn(&T) -> (&T,)>;

    fn c_index_get(&'a self, key: &Self::Key) -> Option<Self::IteratorType> {
        self.0
            .unwrap_frozen()
            .reverse
            .get(&key.0)
            .map(|v| v.par_iter().map((|x| (x,)) as fn(&T) -> (&T,)))
    }
}

impl<'a, T: Clone + Hash + Eq> RelIndexReadAll<'a> for DualInd1<'a, T> {
    type Key = &'a (T,);
    type Value = (&'a T,);
    type ValueIteratorType =
        std::iter::Map<std::slice::Iter<'a, T>, for<'aa> fn(&'aa T) -> (&'aa T,)>;
    type AllIteratorType = Box<dyn Iterator<Item = (Self::Key, Self::ValueIteratorType)> + 'a>;

    fn iter_all(&'a self) -> Self::AllIteratorType {
        Box::new(
            self.0
                .unwrap_frozen()
                .reverse
                .iter()
                .map(|(k, v)| {
                    (
                        ref_to_singleton_tuple_ref(k),
                        v.iter().map((|x| (x,)) as for<'aa> fn(&'aa T) -> (&'aa T,)),
                    )
                }),
        )
    }
}

/// Parallel iterator over `DualInd1`'s reverse index entries.
#[derive(Clone)]
pub struct DualInd1ParIter<'a, T: Clone + Hash + Eq + Sync>(&'a DualIndexedRel<T>);

impl<'a, T: Clone + Hash + Eq + Sync + Send> ParallelIterator for DualInd1ParIter<'a, T> {
    type Item = (
        &'a (T,),
        rayon::iter::Map<rayon::slice::Iter<'a, T>, fn(&T) -> (&T,)>,
    );

    fn drive_unindexed<C>(self, consumer: C) -> C::Result
    where
        C: rayon::iter::plumbing::UnindexedConsumer<Self::Item>,
    {
        self.0
            .reverse
            .par_iter()
            .map(|(k, v)| {
                let vals: rayon::iter::Map<rayon::slice::Iter<'a, T>, fn(&T) -> (&T,)> =
                    v.par_iter().map(|x| (x,));
                (ref_to_singleton_tuple_ref(k), vals)
            })
            .drive_unindexed(consumer)
    }
}

impl<'a, T: Clone + Hash + Eq + Sync + Send> CRelIndexReadAll<'a> for DualInd1<'a, T> {
    type Key = &'a (T,);
    type Value = (&'a T,);
    type ValueIteratorType =
        rayon::iter::Map<rayon::slice::Iter<'a, T>, fn(&T) -> (&T,)>;
    type AllIteratorType = DualInd1ParIter<'a, T>;

    fn c_iter_all(&'a self) -> Self::AllIteratorType {
        DualInd1ParIter(self.0.unwrap_frozen())
    }
}

impl<T: Clone + Hash + Eq> RelIndexWrite for DualInd1<'_, T> {
    type Key = (T,);
    type Value = (T,);
    fn index_insert(&mut self, _key: Self::Key, _value: Self::Value) { /* noop */ }
}

impl<T: Clone + Hash + Eq> CRelIndexWrite for DualInd1<'_, T> {
    type Key = (T,);
    type Value = (T,);
    fn index_insert(&self, _key: Self::Key, _value: Self::Value) { /* noop */ }
}

impl<T: Clone + Hash + Eq> RelIndexMerge for DualInd1<'_, T> {
    fn move_index_contents(_from: &mut Self, _to: &mut Self) { /* noop */ }
}

// ---------------------------------------------------------------------------
// DualInd0_1: full index (both columns bound)
// ---------------------------------------------------------------------------

pub struct DualInd0_1<'a, T: Clone + Hash + Eq>(&'a CDualIndexedRel<T>);

impl<'a, T: Clone + Hash + Eq + 'a> RelIndexRead<'a> for DualInd0_1<'a, T> {
    type Key = <CDualIndexedRel<T> as RelIndexRead<'a>>::Key;
    type Value = <CDualIndexedRel<T> as RelIndexRead<'a>>::Value;
    type IteratorType = <CDualIndexedRel<T> as RelIndexRead<'a>>::IteratorType;

    fn index_get(&'a self, key: &Self::Key) -> Option<Self::IteratorType> {
        self.0.index_get(key)
    }

    fn len_estimate(&self) -> usize {
        self.0.len_estimate()
    }
}

impl<'a, T: Clone + Hash + Eq + Sync + 'a> CRelIndexRead<'a> for DualInd0_1<'a, T> {
    type Key = <CDualIndexedRel<T> as CRelIndexRead<'a>>::Key;
    type Value = <CDualIndexedRel<T> as CRelIndexRead<'a>>::Value;
    type IteratorType = <CDualIndexedRel<T> as CRelIndexRead<'a>>::IteratorType;

    fn c_index_get(&'a self, key: &Self::Key) -> Option<Self::IteratorType> {
        self.0.c_index_get(key)
    }
}

impl<'a, T: Clone + Hash + Eq + 'a> RelIndexReadAll<'a> for DualInd0_1<'a, T> {
    type Key = <CDualIndexedRel<T> as RelIndexReadAll<'a>>::Key;
    type Value = <CDualIndexedRel<T> as RelIndexReadAll<'a>>::Value;
    type ValueIteratorType = <CDualIndexedRel<T> as RelIndexReadAll<'a>>::ValueIteratorType;
    type AllIteratorType = <CDualIndexedRel<T> as RelIndexReadAll<'a>>::AllIteratorType;

    fn iter_all(&'a self) -> Self::AllIteratorType {
        RelIndexReadAll::iter_all(self.0)
    }
}

impl<'a, T: Clone + Hash + Eq + Sync + Send + 'a> CRelIndexReadAll<'a> for DualInd0_1<'a, T> {
    type Key = <CDualIndexedRel<T> as CRelIndexReadAll<'a>>::Key;
    type Value = <CDualIndexedRel<T> as CRelIndexReadAll<'a>>::Value;
    type ValueIteratorType = <CDualIndexedRel<T> as CRelIndexReadAll<'a>>::ValueIteratorType;
    type AllIteratorType = <CDualIndexedRel<T> as CRelIndexReadAll<'a>>::AllIteratorType;

    fn c_iter_all(&'a self) -> Self::AllIteratorType {
        self.0.c_iter_all()
    }
}

impl<'a, T: Clone + Hash + Eq> RelFullIndexRead<'a> for DualInd0_1<'a, T> {
    type Key = <CDualIndexedRel<T> as RelFullIndexRead<'a>>::Key;

    fn contains_key(&'a self, key: &Self::Key) -> bool {
        self.0.contains_key(key)
    }
}

// ---------------------------------------------------------------------------
// DualInd0_1Write: serial write wrapper for full index
// ---------------------------------------------------------------------------

pub struct DualInd0_1Write<'a, T: Clone + Hash + Eq>(&'a mut CDualIndexedRel<T>);

impl<T: Clone + Hash + Eq> RelIndexWrite for DualInd0_1Write<'_, T> {
    type Key = (T, T);
    type Value = ();

    fn index_insert(&mut self, key: Self::Key, value: Self::Value) {
        self.0.index_insert(key, value)
    }
}

impl<T: Clone + Hash + Eq> RelFullIndexWrite for DualInd0_1Write<'_, T> {
    type Key = <CDualIndexedRel<T> as RelFullIndexWrite>::Key;
    type Value = <CDualIndexedRel<T> as RelFullIndexWrite>::Value;

    fn insert_if_not_present(&mut self, key: &Self::Key, v: Self::Value) -> bool {
        self.0.insert_if_not_present(key, v)
    }
}

impl<T: Clone + Hash + Eq> RelIndexMerge for DualInd0_1Write<'_, T> {
    fn move_index_contents(_from: &mut Self, _to: &mut Self) { /* noop */ }
}

// ---------------------------------------------------------------------------
// DualInd0_1CWrite: concurrent write wrapper for full index
// ---------------------------------------------------------------------------

pub struct DualInd0_1CWrite<'a, T: Clone + Hash + Eq>(&'a CDualIndexedRel<T>);

impl<T: Clone + Hash + Eq> CRelIndexWrite for DualInd0_1CWrite<'_, T> {
    type Key = (T, T);
    type Value = ();

    fn index_insert(&self, key: Self::Key, _value: Self::Value) {
        self.0
            .unwrap_unfrozen()
            .lock()
            .expect("CDualIndexedRel: unexpected state (DualInd0_1CWrite: mutex poisoned)")
            .insert(key.0, key.1);
    }
}

impl<T: Clone + Hash + Eq> CRelFullIndexWrite for DualInd0_1CWrite<'_, T> {
    type Key = <CDualIndexedRel<T> as CRelFullIndexWrite>::Key;
    type Value = <CDualIndexedRel<T> as CRelFullIndexWrite>::Value;

    fn insert_if_not_present(&self, key: &Self::Key, v: Self::Value) -> bool {
        CRelFullIndexWrite::insert_if_not_present(self.0, key, v)
    }
}

// ---------------------------------------------------------------------------
// DualIndNone: unindexed access (iterates all pairs)
// ---------------------------------------------------------------------------

pub struct DualIndNone<'a, T: Clone + Hash + Eq>(&'a CDualIndexedRel<T>);

impl<'a, T: Clone + Hash + Eq> RelIndexRead<'a> for DualIndNone<'a, T> {
    type Key = ();
    type Value = (&'a T, &'a T);
    type IteratorType = IteratorFromDyn<'a, (&'a T, &'a T)>;

    fn index_get(&'a self, _key: &Self::Key) -> Option<Self::IteratorType> {
        Some(IteratorFromDyn::new(|| self.0.unwrap_frozen().iter_all()))
    }

    fn len_estimate(&self) -> usize {
        1
    }
}

impl<'a, T: Clone + Hash + Eq + Sync + Send> CRelIndexRead<'a> for DualIndNone<'a, T> {
    type Key = ();
    type Value = (&'a T, &'a T);
    type IteratorType = DualAllPairsParIter<'a, T>;

    fn c_index_get(&'a self, _key: &Self::Key) -> Option<Self::IteratorType> {
        Some(DualAllPairsParIter(self.0.unwrap_frozen()))
    }
}

impl<'a, T: Clone + Hash + Eq> RelIndexReadAll<'a> for DualIndNone<'a, T> {
    type Key = ();
    type Value = (&'a T, &'a T);
    type ValueIteratorType = IteratorFromDyn<'a, (&'a T, &'a T)>;
    type AllIteratorType = std::option::IntoIter<(Self::Key, Self::ValueIteratorType)>;

    fn iter_all(&'a self) -> Self::AllIteratorType {
        self.index_get(&()).map(|iter| ((), iter)).into_iter()
    }
}

impl<'a, T: Clone + Hash + Eq + Sync + Send> CRelIndexReadAll<'a> for DualIndNone<'a, T> {
    type Key = ();
    type Value = (&'a T, &'a T);
    type ValueIteratorType = DualAllPairsParIter<'a, T>;
    type AllIteratorType = rayon::iter::Once<(Self::Key, Self::ValueIteratorType)>;

    fn c_iter_all(&'a self) -> Self::AllIteratorType {
        rayon::iter::once(((), DualAllPairsParIter(self.0.unwrap_frozen())))
    }
}

impl<T: Clone + Hash + Eq> RelIndexWrite for DualIndNone<'_, T> {
    type Key = ();
    type Value = (T, T);
    fn index_insert(&mut self, _key: Self::Key, _value: Self::Value) { /* noop */ }
}

impl<T: Clone + Hash + Eq> CRelIndexWrite for DualIndNone<'_, T> {
    type Key = ();
    type Value = (T, T);
    fn index_insert(&self, _key: Self::Key, _value: Self::Value) { /* noop */ }
}

impl<T: Clone + Hash + Eq> RelIndexMerge for DualIndNone<'_, T> {
    fn move_index_contents(_from: &mut Self, _to: &mut Self) { /* noop */ }
}

// ---------------------------------------------------------------------------
// Parallel iterator: all (col0, col1) pairs
// ---------------------------------------------------------------------------

/// Parallel iterator over all (col0, col1) pairs in a `DualIndexedRel`.
#[derive(Clone)]
pub struct DualAllPairsParIter<'a, T: Clone + Hash + Eq + Sync>(&'a DualIndexedRel<T>);

impl<'a, T: Clone + Hash + Eq + Sync + Send> ParallelIterator for DualAllPairsParIter<'a, T> {
    type Item = (&'a T, &'a T);

    fn drive_unindexed<C>(self, consumer: C) -> C::Result
    where
        C: rayon::iter::plumbing::UnindexedConsumer<Self::Item>,
    {
        self.0
            .forward
            .par_iter()
            .flat_map(|(x, x_set)| x_set.par_iter().map(move |y| (x, y)))
            .drive_unindexed(consumer)
    }
}

// ---------------------------------------------------------------------------
// Adaptor types: ToRelIndex / ToRelIndex0
// ---------------------------------------------------------------------------

// Option D (source consolidation): the three single-index markers
// `ToDualInd0` / `ToDualInd1` / `ToDualIndNone` have identical structural
// impls (`Default` / `Freezable` / `ToRelIndex`) that differ only in the
// wrapper type they yield (`DualInd0` / `DualInd1` / `DualIndNone`). Ascent
// requires DISTINCT marker types for trait-coherence dispatch in its BYODS
// protocol — merging into one generic `ToDualInd<K, T>` would risk
// breaking that dispatch via blanket-impl coherence conflicts. The safe
// consolidation is a local macro_rules! that emits the three structs and
// their trait impls from a single template, keeping the type surface
// distinct but reducing source duplication. Monomorphization count is
// unchanged (still N types × T = N*|cats| mono instances); what we save
// is ~90 lines of mechanical boilerplate that maintainers had to keep
// in lock-step.
macro_rules! single_column_marker {
    ($marker:ident, $wrapper:ident) => {
        pub struct $marker<T>(PhantomData<T>);
        impl<T> Default for $marker<T> {
            fn default() -> Self {
                Self(PhantomData)
            }
        }
        impl<T> Freezable for $marker<T> {}

        impl<T: Clone + Hash + Eq> ToRelIndex<CDualIndexedRel<T>> for $marker<T> {
            type RelIndex<'a>
                = $wrapper<'a, T>
            where
                T: 'a;

            fn to_rel_index<'a>(
                &'a self,
                rel: &'a CDualIndexedRel<T>,
            ) -> <Self as ToRelIndex<CDualIndexedRel<T>>>::RelIndex<'a> {
                $wrapper(rel)
            }

            type RelIndexWrite<'a>
                = $wrapper<'a, T>
            where
                T: 'a;

            fn to_rel_index_write<'a>(
                &'a mut self,
                rel: &'a mut CDualIndexedRel<T>,
            ) -> <Self as ToRelIndex<CDualIndexedRel<T>>>::RelIndexWrite<'a> {
                $wrapper(rel)
            }
        }
    };
}

single_column_marker!(ToDualInd0, DualInd0);
single_column_marker!(ToDualInd1, DualInd1);

pub struct ToDualInd0_1<T>(PhantomData<T>);
impl<T> Default for ToDualInd0_1<T> {
    fn default() -> Self {
        Self(PhantomData)
    }
}
impl<T> Freezable for ToDualInd0_1<T> {}

impl<T: Clone + Hash + Eq> ToRelIndex0<CDualIndexedRel<T>> for ToDualInd0_1<T> {
    type RelIndex<'a>
        = DualInd0_1<'a, T>
    where
        T: 'a;

    fn to_rel_index<'a>(
        &'a self,
        rel: &'a CDualIndexedRel<T>,
    ) -> <Self as ToRelIndex0<CDualIndexedRel<T>>>::RelIndex<'a> {
        DualInd0_1(rel)
    }

    type RelIndexWrite<'a>
        = DualInd0_1Write<'a, T>
    where
        T: 'a;

    fn to_rel_index_write<'a>(
        &'a mut self,
        rel: &'a mut CDualIndexedRel<T>,
    ) -> <Self as ToRelIndex0<CDualIndexedRel<T>>>::RelIndexWrite<'a> {
        DualInd0_1Write(rel)
    }

    type CRelIndexWrite<'a>
        = DualInd0_1CWrite<'a, T>
    where
        Self: 'a,
        CDualIndexedRel<T>: 'a;

    fn to_c_rel_index_write<'a>(
        &'a self,
        rel: &'a CDualIndexedRel<T>,
    ) -> <Self as ToRelIndex0<CDualIndexedRel<T>>>::CRelIndexWrite<'a> {
        DualInd0_1CWrite(rel)
    }
}

single_column_marker!(ToDualIndNone, DualIndNone);

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
    ($name:ident, ($col0:ty, $col1:ty), $indices:expr, par, ()) => {
        ::std::vec::Vec<($col0, $col1)>
    };
}
pub use dual_indexed_rel as rel;

/// Central data structure: `DualIndexedRel<T>` for serial, `CDualIndexedRel<T>` for parallel.
#[doc(hidden)]
#[macro_export]
macro_rules! dual_indexed_rel_ind_common {
    ($name:ident, ($col0:ty, $col1:ty), $indices:expr, ser, ()) => {
        $crate::dual_indexed::DualIndexedRel<$col0>
    };
    ($name:ident, ($col0:ty, $col1:ty), $indices:expr, par, ()) => {
        $crate::dual_indexed::CDualIndexedRel<$col0>
    };
}
pub use dual_indexed_rel_ind_common as rel_ind_common;

/// Full index (both columns bound): delegates to `bin_rel_provider` adaptor for serial,
/// `ToDualInd0_1` for parallel.
#[doc(hidden)]
#[macro_export]
macro_rules! dual_indexed_rel_full_ind {
    ($name:ident, ($col0:ty, $col1:ty), $indices:expr, ser, (), $key:ty, $val:ty) => {
        ascent_byods_rels::adaptor::bin_rel::ToByodsBinRelInd0_1<$col0, $col1>
    };
    ($name:ident, ($col0:ty, $col1:ty), $indices:expr, par, (), $key:ty, $val:ty) => {
        $crate::dual_indexed::ToDualInd0_1<$col0>
    };
}
pub use dual_indexed_rel_full_ind as rel_full_ind;

/// Per-column index: delegates to `bin_rel_provider` adaptor types for serial,
/// `ToDualInd*` types for parallel.
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
    ($name:ident, ($col0:ty, $col1:ty), $indices:expr, par, (), [0], $key:ty, $val:ty) => {
        $crate::dual_indexed::ToDualInd0<$col0>
    };
    ($name:ident, ($col0:ty, $col1:ty), $indices:expr, par, (), [1], $key:ty, $val:ty) => {
        $crate::dual_indexed::ToDualInd1<$col0>
    };
    ($name:ident, ($col0:ty, $col1:ty), $indices:expr, par, (), [], $key:ty, $val:ty) => {
        $crate::dual_indexed::ToDualIndNone<$col0>
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
