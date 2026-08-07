//! HashBag - Multiset (bag) implementation
//!
//! A `HashBag<T>` is an unordered collection that allows duplicates,
//! tracking the count of each unique element. Also known as a multiset.
//!
//! # Examples
//!
//! ```
//! use mettail_runtime::HashBag;
//!
//! let mut bag = HashBag::new();
//! bag.insert("a");
//! bag.insert("a");
//! bag.insert("b");
//!
//! assert_eq!(HashBag::count(&bag, &"a"), 2);
//! assert_eq!(HashBag::count(&bag, &"b"), 1);
//! assert_eq!(bag.len(), 3);
//! ```

use rustc_hash::FxHasher;
use std::cmp::Ordering;
use std::collections::HashMap;
use std::fmt;
use std::hash::{BuildHasherDefault, Hash, Hasher};

use crate::{BoundTerm, Var};
use moniker::{OnBoundFn, OnFreeFn, ScopeState};

/// A multiset (bag) - unordered collection with duplicates.
///
/// Uses a `HashMap` to track element counts efficiently.
/// Equality is based on element counts (order-independent).
///
/// # Type Parameters
///
/// * `T` - Element type, must be `Clone + Hash + Eq`
#[derive(Clone)]
pub struct HashBag<T: Clone + Hash + Eq> {
    /// Map from elements to their counts
    counts: HashMap<T, usize, BuildHasherDefault<FxHasher>>,
    /// Total number of elements (sum of all counts)
    total_count: usize,
    /// Order-independent element/count lanes maintained incrementally by every mutation.
    ///
    /// Keeping these lanes with the bag makes hashing the bag O(1). In particular, hashing a
    /// `Proc::PPar` no longer re-hashes every descendant of an already-built nested parallel
    /// term. The four lanes are exactly those historically computed by [`Hash::hash`], so this
    /// changes cost, not the emitted hash stream.
    hash_summary: HashBagHashSummary,
}

#[derive(Clone, Copy, Debug, Default)]
struct HashBagHashSummary {
    sum_a: u64,
    sum_b: u64,
    xor_a: u64,
    xor_b: u64,
}

impl HashBagHashSummary {
    fn add(&mut self, lanes: (u64, u64)) {
        let (a, b) = lanes;
        self.sum_a = self.sum_a.wrapping_add(a);
        self.sum_b = self.sum_b.wrapping_add(b);
        self.xor_a ^= a.rotate_left((b & 63) as u32);
        self.xor_b ^= b.rotate_left((a & 63) as u32);
    }

    fn remove(&mut self, lanes: (u64, u64)) {
        let (a, b) = lanes;
        self.sum_a = self.sum_a.wrapping_sub(a);
        self.sum_b = self.sum_b.wrapping_sub(b);
        self.xor_a ^= a.rotate_left((b & 63) as u32);
        self.xor_b ^= b.rotate_left((a & 63) as u32);
    }
}

fn hashbag_entry_lanes<T: Hash>(elem: &T, count: usize) -> (u64, u64) {
    let mut ha = FxHasher::with_seed(0);
    elem.hash(&mut ha);
    count.hash(&mut ha);
    let a = mix_hashbag_lane(ha.finish());

    let mut hb = FxHasher::with_seed(0x9e37_79b9_7f4a_7c15usize);
    count.hash(&mut hb);
    elem.hash(&mut hb);
    let b = mix_hashbag_lane(hb.finish());
    (a, b)
}

impl<T: Clone + Hash + Eq> HashBag<T> {
    fn from_elements(iter: impl IntoIterator<Item = T>) -> Self {
        let mut bag = Self::new();
        for item in iter {
            bag.insert(item);
        }
        bag
    }

    fn rebuild_hash_summary(&mut self) {
        let mut summary = HashBagHashSummary::default();
        for (element, count) in &self.counts {
            summary.add(hashbag_entry_lanes(element, *count));
        }
        self.hash_summary = summary;
    }

    /// Creates an empty `HashBag`.
    ///
    /// # Examples
    ///
    /// ```
    /// use mettail_runtime::HashBag;
    ///
    /// let bag: HashBag<i32> = HashBag::new();
    /// assert!(bag.is_empty());
    /// ```
    pub fn new() -> Self {
        Self {
            counts: HashMap::default(),
            total_count: 0,
            hash_summary: HashBagHashSummary::default(),
        }
    }

    /// Creates a `HashBag` from an iterator of elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use mettail_runtime::HashBag;
    ///
    /// let bag = HashBag::from_iter(vec!["a", "b", "a"]);
    /// assert_eq!(HashBag::count(&bag, &"a"), 2);
    /// assert_eq!(bag.len(), 3);
    /// ```
    #[allow(clippy::should_implement_trait)]
    pub fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        Self::from_elements(iter)
    }

    /// Inserts an element into the bag, incrementing its count.
    ///
    /// # Examples
    ///
    /// ```
    /// use mettail_runtime::HashBag;
    ///
    /// let mut bag = HashBag::new();
    /// bag.insert("a");
    /// bag.insert("a");
    /// assert_eq!(HashBag::count(&bag, &"a"), 2);
    /// ```
    pub fn insert(&mut self, item: T) {
        let (old_lanes, new_lanes) = match self.counts.entry(item) {
            std::collections::hash_map::Entry::Occupied(mut entry) => {
                let old_count = *entry.get();
                let old_lanes = hashbag_entry_lanes(entry.key(), old_count);
                *entry.get_mut() = old_count + 1;
                let new_lanes = hashbag_entry_lanes(entry.key(), old_count + 1);
                (Some(old_lanes), new_lanes)
            },
            std::collections::hash_map::Entry::Vacant(entry) => {
                let new_lanes = hashbag_entry_lanes(entry.key(), 1);
                entry.insert(1);
                (None, new_lanes)
            },
        };
        if let Some(old_lanes) = old_lanes {
            self.hash_summary.remove(old_lanes);
        }
        self.hash_summary.add(new_lanes);
        self.total_count += 1;
    }

    /// Removes one occurrence of an element from the bag.
    ///
    /// Returns `true` if an element was removed, `false` if the element was not in the bag.
    ///
    /// # Examples
    ///
    /// ```
    /// use mettail_runtime::HashBag;
    ///
    /// let mut bag = HashBag::new();
    /// bag.insert("a");
    /// bag.insert("a");
    ///
    /// assert!(bag.remove(&"a"));
    /// assert_eq!(HashBag::count(&bag, &"a"), 1);
    ///
    /// assert!(bag.remove(&"a"));
    /// assert_eq!(HashBag::count(&bag, &"a"), 0);
    ///
    /// assert!(!bag.remove(&"a"));
    /// ```
    pub fn remove(&mut self, item: &T) -> bool {
        if let Some(count) = self.counts.get_mut(item) {
            let old_count = *count;
            let old_lanes = hashbag_entry_lanes(item, old_count);
            let new_lanes = (old_count > 1).then(|| hashbag_entry_lanes(item, old_count - 1));
            *count -= 1;
            self.hash_summary.remove(old_lanes);
            if let Some(new_lanes) = new_lanes {
                self.hash_summary.add(new_lanes);
            }
            self.total_count -= 1;
            if old_count == 1 {
                self.counts.remove(item);
            }
            true
        } else {
            false
        }
    }

    /// Returns `true` if the bag contains at least one occurrence of the element.
    ///
    /// # Examples
    ///
    /// ```
    /// use mettail_runtime::HashBag;
    ///
    /// let mut bag = HashBag::new();
    /// bag.insert("a");
    ///
    /// assert!(bag.contains(&"a"));
    /// assert!(!bag.contains(&"b"));
    /// ```
    pub fn contains(&self, item: &T) -> bool {
        self.counts.contains_key(item)
    }

    /// Returns the count of an element in the bag.
    ///
    /// Returns 0 if the element is not in the bag.
    ///
    /// # Examples
    ///
    /// ```
    /// use mettail_runtime::HashBag;
    ///
    /// let mut bag = HashBag::new();
    /// bag.insert("a");
    /// bag.insert("a");
    ///
    /// assert_eq!(HashBag::count(&bag, &"a"), 2);
    /// assert_eq!(HashBag::count(&bag, &"b"), 0);
    /// ```
    pub fn count(&self, item: &T) -> usize {
        self.counts.get(item).copied().unwrap_or(0)
    }

    /// Returns the total number of elements in the bag (sum of all counts).
    ///
    /// # Examples
    ///
    /// ```
    /// use mettail_runtime::HashBag;
    ///
    /// let mut bag = HashBag::new();
    /// bag.insert("a");
    /// bag.insert("a");
    /// bag.insert("b");
    ///
    /// assert_eq!(bag.len(), 3);
    /// ```
    pub fn len(&self) -> usize {
        self.total_count
    }

    /// Returns `true` if the bag contains no elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use mettail_runtime::HashBag;
    ///
    /// let mut bag = HashBag::new();
    /// assert!(bag.is_empty());
    ///
    /// bag.insert("a");
    /// assert!(!bag.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.total_count == 0
    }

    /// Inserts an element into the bag `count` times.
    ///
    /// This is more efficient than calling `insert()` in a loop because
    /// it performs a single hash lookup and adds the count directly.
    ///
    /// # Examples
    ///
    /// ```
    /// use mettail_runtime::HashBag;
    ///
    /// let mut bag = HashBag::new();
    /// bag.insert_n("a", 3);
    /// assert_eq!(HashBag::count(&bag, &"a"), 3);
    /// assert_eq!(bag.len(), 3);
    /// ```
    pub fn insert_n(&mut self, item: T, count: usize) {
        if count > 0 {
            let (old_lanes, new_lanes) = match self.counts.entry(item) {
                std::collections::hash_map::Entry::Occupied(mut entry) => {
                    let old_count = *entry.get();
                    let old_lanes = hashbag_entry_lanes(entry.key(), old_count);
                    let new_count = old_count + count;
                    *entry.get_mut() = new_count;
                    let new_lanes = hashbag_entry_lanes(entry.key(), new_count);
                    (Some(old_lanes), new_lanes)
                },
                std::collections::hash_map::Entry::Vacant(entry) => {
                    let new_lanes = hashbag_entry_lanes(entry.key(), count);
                    entry.insert(count);
                    (None, new_lanes)
                },
            };
            if let Some(old_lanes) = old_lanes {
                self.hash_summary.remove(old_lanes);
            }
            self.hash_summary.add(new_lanes);
            self.total_count += count;
        }
    }

    /// Returns an iterator over `(element, count)` pairs.
    ///
    /// The order of iteration is arbitrary.
    ///
    /// # Examples
    ///
    /// ```
    /// use mettail_runtime::HashBag;
    ///
    /// let mut bag = HashBag::new();
    /// bag.insert("a");
    /// bag.insert("a");
    /// bag.insert("b");
    ///
    /// let mut items: Vec<_> = bag.iter().collect();
    /// items.sort();
    /// assert_eq!(items, vec![(&"a", 2), (&"b", 1)]);
    /// ```
    pub fn iter(&self) -> impl Iterator<Item = (&T, usize)> {
        self.counts.iter().map(|(k, &v)| (k, v))
    }

    /// Returns an iterator that yields each element `count` times.
    ///
    /// The order of iteration is arbitrary.
    ///
    /// # Examples
    ///
    /// ```
    /// use mettail_runtime::HashBag;
    ///
    /// let mut bag = HashBag::new();
    /// bag.insert("a");
    /// bag.insert("a");
    /// bag.insert("b");
    ///
    /// let mut elements: Vec<_> = bag.iter_elements().copied().collect();
    /// elements.sort();
    /// assert_eq!(elements, vec!["a", "a", "b"]);
    /// ```
    pub fn iter_elements(&self) -> impl Iterator<Item = &T> {
        self.counts
            .iter()
            .flat_map(|(k, &count)| std::iter::repeat_n(k, count))
    }

    /// Multiset union: for each element, count is sum of counts in self and other.
    pub fn union(&self, other: &Self) -> Self {
        let mut bag = self.clone();
        for (elem, count) in other.counts.iter() {
            bag.insert_n(elem.clone(), *count);
        }
        bag
    }

    /// Removes one occurrence of `elem`. Returns a new bag; if `elem` was not present, returns a clone of self.
    pub fn remove_one(&self, elem: &T) -> Self {
        let mut bag = self.clone();
        bag.remove(elem);
        bag
    }

    /// Multiset difference: for each element, count is max(0, self.count - other.count).
    pub fn diff(&self, other: &Self) -> Self {
        let mut bag = self.clone();
        for (elem, count) in other.counts.iter() {
            for _ in 0..*count {
                bag.remove(elem);
            }
        }
        bag
    }
}

// PartialEq: compare by element counts (order-independent)
impl<T: Clone + Hash + Eq> PartialEq for HashBag<T> {
    fn eq(&self, other: &Self) -> bool {
        self.total_count == other.total_count && self.counts == other.counts
    }
}

impl<T: Clone + Hash + Eq> Eq for HashBag<T> {}

impl<T: Clone + Hash + Eq + fmt::Debug> fmt::Debug for HashBag<T> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("HashBag")
            .field("counts", &self.counts)
            .field("total_count", &self.total_count)
            .finish()
    }
}

// Hash: order-independent over all (element, count) pairs.
//
// We cannot assume `T: Ord`, and sorting by a hash key is not enough: if two
// unequal elements collide on the sort key, equal bags built in different
// insertion orders may write their tied entries in different orders and violate
// Hash's `a == b => hash(a) == hash(b)` contract. Use commutative summaries
// instead. This keeps the BigInt/Rholang fast path O(distinct element hash
// cost), without going back to `Debug`/`Display` sorting.
impl<T: Clone + Hash + Eq> Hash for HashBag<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.total_count.hash(state);
        self.counts.len().hash(state);
        self.hash_summary.sum_a.hash(state);
        self.hash_summary.sum_b.hash(state);
        self.hash_summary.xor_a.hash(state);
        self.hash_summary.xor_b.hash(state);
    }
}

impl<T: Clone + Hash + Eq> HashBag<T> {
    /// Order-independent SEMANTIC hash: identical multiset-combine to
    /// [`Hash::hash`], but each element is hashed through the supplied `elem_sem`
    /// visitor instead of its `std::hash::Hash`.
    ///
    /// Generated `semantic_hash` uses this for collections whose elements are
    /// category types that may contain binders. The element's `semantic_hash` is
    /// alpha-canonical (de-Bruijn body + arity-only binder position), whereas its
    /// `std::hash::Hash` is structural and leaks the binder's run-varying,
    /// alpha-irrelevant `unique_id`. The combine (lanes, `mix_hashbag_lane`,
    /// sum/xor, `total_count`/`counts.len()` framing) is byte-for-byte the same as
    /// `Hash::hash`, so multiset order-independence and count-sensitivity are
    /// preserved — only the per-element hash source changes.
    pub fn semantic_hash_into<H, F>(&self, state: &mut H, elem_sem: F)
    where
        H: Hasher,
        F: Fn(&T, &mut FxHasher),
    {
        self.total_count.hash(state);
        self.counts.len().hash(state);

        let mut sum_a = 0u64;
        let mut sum_b = 0u64;
        let mut xor_a = 0u64;
        let mut xor_b = 0u64;

        for (elem, count) in self.counts.iter() {
            let mut ha = FxHasher::with_seed(0);
            elem_sem(elem, &mut ha);
            count.hash(&mut ha);
            let a = mix_hashbag_lane(ha.finish());

            let mut hb = FxHasher::with_seed(0x9e37_79b9_7f4a_7c15usize);
            count.hash(&mut hb);
            elem_sem(elem, &mut hb);
            let b = mix_hashbag_lane(hb.finish());

            sum_a = sum_a.wrapping_add(a);
            sum_b = sum_b.wrapping_add(b);
            xor_a ^= a.rotate_left((b & 63) as u32);
            xor_b ^= b.rotate_left((a & 63) as u32);
        }

        sum_a.hash(state);
        sum_b.hash(state);
        xor_a.hash(state);
        xor_b.hash(state);
    }
}

#[inline]
fn mix_hashbag_lane(mut x: u64) -> u64 {
    x ^= x >> 30;
    x = x.wrapping_mul(0xbf58_476d_1ce4_e5b9);
    x ^= x >> 27;
    x = x.wrapping_mul(0x94d0_49bb_1331_11eb);
    x ^ (x >> 31)
}

// Ord: lexicographic ordering by sorted elements
impl<T: Clone + Hash + Eq + Ord> PartialOrd for HashBag<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<T: Clone + Hash + Eq + Ord> Ord for HashBag<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        // First compare by total count
        match self.total_count.cmp(&other.total_count) {
            Ordering::Equal => {
                // Then compare sorted elements lexicographically
                let mut v1: Vec<_> = self.iter_elements().collect();
                let mut v2: Vec<_> = other.iter_elements().collect();
                v1.sort();
                v2.sort();
                v1.cmp(&v2)
            },
            ord => ord,
        }
    }
}

impl<T: Clone + Hash + Eq> Default for HashBag<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: Clone + Hash + Eq> FromIterator<T> for HashBag<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        Self::from_elements(iter)
    }
}

/// Consuming iterator over `(element, count)` pairs.
///
/// Yields each unique element along with its multiplicity, consuming the
/// `HashBag`. Used by the iterative drop implementation to take ownership
/// of elements for stack-safe deallocation.
impl<T: Clone + Hash + Eq> IntoIterator for HashBag<T> {
    type Item = (T, usize);
    type IntoIter = std::collections::hash_map::IntoIter<T, usize>;

    fn into_iter(self) -> Self::IntoIter {
        self.counts.into_iter()
    }
}

// BoundTerm: Integration with moniker for substitution and variable binding
impl<N, T> BoundTerm<N> for HashBag<T>
where
    N: Clone + PartialEq,
    T: Clone + Hash + Eq + BoundTerm<N>,
{
    fn term_eq(&self, other: &Self) -> bool {
        if self.total_count != other.total_count {
            return false;
        }
        // Check term equality for each element (alpha-equivalence aware)
        // For each unique element in self, find matching elements in other
        for (elem1, count1) in self.iter() {
            let count2 = other
                .iter()
                .filter(|(elem2, _)| elem1.term_eq(elem2))
                .map(|(_, c)| c)
                .sum::<usize>();
            if count1 != count2 {
                return false;
            }
        }
        true
    }

    fn close_term(&mut self, state: ScopeState, on_free: &impl OnFreeFn<N>) {
        // Close each unique element
        // We need to rebuild the map because closing might change element identity
        let old_counts = std::mem::take(&mut self.counts);
        self.counts = HashMap::default();

        for (mut elem, count) in old_counts {
            elem.close_term(state, on_free);
            self.counts.insert(elem, count);
        }
        self.rebuild_hash_summary();
    }

    fn open_term(&mut self, state: ScopeState, on_bound: &impl OnBoundFn<N>) {
        // Open each unique element
        let old_counts = std::mem::take(&mut self.counts);
        self.counts = HashMap::default();

        for (mut elem, count) in old_counts {
            elem.open_term(state, on_bound);
            self.counts.insert(elem, count);
        }
        self.rebuild_hash_summary();
    }

    fn visit_vars(&self, on_var: &mut impl FnMut(&Var<N>)) {
        for (elem, _) in self.iter() {
            elem.visit_vars(on_var);
        }
    }

    fn visit_mut_vars(&mut self, on_var: &mut impl FnMut(&mut Var<N>)) {
        // Need to rebuild the map since we need mutable access to keys
        let old_counts = std::mem::take(&mut self.counts);
        self.counts = HashMap::default();

        for (mut elem, count) in old_counts {
            elem.visit_mut_vars(on_var);
            self.counts.insert(elem, count);
        }
        self.rebuild_hash_summary();
    }
}

/// Display implementation for HashBag
///
/// Formats as `{elem1, elem1, elem2}` with elements repeated according to their count.
/// Elements are sorted for deterministic output.
impl<T: Clone + Hash + Eq + Ord + fmt::Display> fmt::Display for HashBag<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{{")?;

        // Collect and sort elements for deterministic output
        let mut items: Vec<(&T, &usize)> = self.counts.iter().collect();
        items.sort_by(|a, b| a.0.cmp(b.0));

        let mut first = true;
        for (elem, &count) in items {
            for _ in 0..count {
                if !first {
                    write!(f, ", ")?;
                }
                write!(f, "{}", elem)?;
                first = false;
            }
        }

        write!(f, "}}")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::hash_map::DefaultHasher;
    use std::sync::atomic::{AtomicUsize, Ordering as AtomicOrdering};

    fn hash_of<T: Hash>(value: &T) -> u64 {
        let mut h = DefaultHasher::new();
        value.hash(&mut h);
        h.finish()
    }

    fn legacy_hash_of<T: Clone + Hash + Eq>(bag: &HashBag<T>) -> u64 {
        let mut state = DefaultHasher::new();
        bag.total_count.hash(&mut state);
        bag.counts.len().hash(&mut state);

        let mut sum_a = 0u64;
        let mut sum_b = 0u64;
        let mut xor_a = 0u64;
        let mut xor_b = 0u64;
        for (element, count) in &bag.counts {
            let mut ha = FxHasher::with_seed(0);
            element.hash(&mut ha);
            count.hash(&mut ha);
            let a = mix_hashbag_lane(ha.finish());

            let mut hb = FxHasher::with_seed(0x9e37_79b9_7f4a_7c15usize);
            count.hash(&mut hb);
            element.hash(&mut hb);
            let b = mix_hashbag_lane(hb.finish());

            sum_a = sum_a.wrapping_add(a);
            sum_b = sum_b.wrapping_add(b);
            xor_a ^= a.rotate_left((b & 63) as u32);
            xor_b ^= b.rotate_left((a & 63) as u32);
        }
        sum_a.hash(&mut state);
        sum_b.hash(&mut state);
        xor_a.hash(&mut state);
        xor_b.hash(&mut state);
        state.finish()
    }

    fn assert_cached_hash_matches_legacy<T: Clone + Hash + Eq>(bag: &HashBag<T>) {
        assert_eq!(hash_of(bag), legacy_hash_of(bag));
    }

    #[test]
    fn equal_bags_hash_equal_across_insertion_order() {
        let mut left = HashBag::new();
        left.insert("alpha");
        left.insert("beta");
        left.insert("alpha");
        left.insert("gamma");

        let mut right = HashBag::new();
        right.insert("gamma");
        right.insert("alpha");
        right.insert("beta");
        right.insert("alpha");

        assert_eq!(left, right);
        assert_eq!(hash_of(&left), hash_of(&right));
    }

    #[derive(Clone, Debug, PartialEq, Eq)]
    struct CollidingKey(u8);

    impl Hash for CollidingKey {
        fn hash<H: Hasher>(&self, state: &mut H) {
            0u8.hash(state);
            self.0.hash(state);
        }
    }

    #[test]
    fn hash_depends_on_counts_not_iteration_order() {
        let mut left = HashBag::new();
        left.insert(CollidingKey(1));
        left.insert(CollidingKey(2));
        left.insert(CollidingKey(2));

        let mut right = HashBag::new();
        right.insert(CollidingKey(2));
        right.insert(CollidingKey(1));
        right.insert(CollidingKey(2));

        assert_eq!(left, right);
        assert_eq!(hash_of(&left), hash_of(&right));
    }

    #[test]
    fn cached_hash_is_byte_identical_to_legacy_recomputation_after_mutations() {
        let mut bag = HashBag::new();
        assert_cached_hash_matches_legacy(&bag);

        bag.insert_n(CollidingKey(1), 3);
        assert_cached_hash_matches_legacy(&bag);
        bag.insert(CollidingKey(2));
        assert_cached_hash_matches_legacy(&bag);
        bag.insert(CollidingKey(1));
        assert_cached_hash_matches_legacy(&bag);
        assert!(bag.remove(&CollidingKey(1)));
        assert_cached_hash_matches_legacy(&bag);
        assert!(bag.remove(&CollidingKey(2)));
        assert_cached_hash_matches_legacy(&bag);

        let cloned = bag.clone();
        assert_eq!(hash_of(&cloned), legacy_hash_of(&cloned));
    }

    static ELEMENT_HASH_CALLS: AtomicUsize = AtomicUsize::new(0);

    #[derive(Clone, Debug, PartialEq, Eq)]
    struct CountingKey(u8);

    impl Hash for CountingKey {
        fn hash<H: Hasher>(&self, state: &mut H) {
            ELEMENT_HASH_CALLS.fetch_add(1, AtomicOrdering::Relaxed);
            self.0.hash(state);
        }
    }

    #[test]
    fn hashing_a_built_bag_does_not_rehash_its_elements() {
        let mut bag = HashBag::new();
        bag.insert_n(CountingKey(7), 4);
        ELEMENT_HASH_CALLS.store(0, AtomicOrdering::Relaxed);

        let first = hash_of(&bag);
        let second = hash_of(&bag);
        assert_eq!(first, second);
        assert_eq!(ELEMENT_HASH_CALLS.load(AtomicOrdering::Relaxed), 0);
    }
}
