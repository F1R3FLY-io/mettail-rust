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
#[derive(Clone, Debug)]
pub struct HashBag<T: Clone + Hash + Eq> {
    /// Map from elements to their counts
    counts: HashMap<T, usize, BuildHasherDefault<FxHasher>>,
    /// Total number of elements (sum of all counts)
    total_count: usize,
}

impl<T: Clone + Hash + Eq> HashBag<T> {
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
        let mut bag = Self::new();
        for item in iter {
            bag.insert(item);
        }
        bag
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
        *self.counts.entry(item).or_insert(0) += 1;
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
            *count -= 1;
            self.total_count -= 1;
            if *count == 0 {
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
            for _ in 0..*count {
                bag.insert(elem.clone());
            }
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

// Hash: hash all (element, count) pairs in a deterministic order
impl<T: Clone + Hash + Eq + fmt::Debug> Hash for HashBag<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        // Hash total count first
        self.total_count.hash(state);

        // Collect and sort entries for deterministic hashing
        // We use Debug format for sorting since we can't assume T: Ord
        let mut entries: Vec<_> = self.counts.iter().collect();
        entries.sort_by_key(|(k, _)| format!("{:?}", k));

        for (elem, &count) in entries {
            elem.hash(state);
            count.hash(state);
        }
    }
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
        Self::from_iter(iter)
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
    }

    fn open_term(&mut self, state: ScopeState, on_bound: &impl OnBoundFn<N>) {
        // Open each unique element
        let old_counts = std::mem::take(&mut self.counts);
        self.counts = HashMap::default();

        for (mut elem, count) in old_counts {
            elem.open_term(state, on_bound);
            self.counts.insert(elem, count);
        }
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
