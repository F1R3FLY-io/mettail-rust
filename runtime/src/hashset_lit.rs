//! HashSetLit - deterministic HashSet wrapper
//!
//! `std::collections::HashSet` does not implement `Ord`, but MeTTaIL terms derive
//! these traits so they can be stored in Ascent relations and enumerated
//! deterministically.
//!
//! `HashSetLit<T>` is a small newtype wrapper with deterministic `Hash` and `Ord`
//! implementations based on sorting elements.

use rustc_hash::FxHasher;
use std::cmp::Ordering;
use std::collections::HashSet;
use std::fmt;
use std::hash::{BuildHasherDefault, Hash, Hasher};

use crate::{BoundTerm, Var};
use moniker::{OnBoundFn, OnFreeFn, ScopeState};

type FxBuildHasher = BuildHasherDefault<FxHasher>;

/// Deterministic, hashable, orderable set literal.
#[derive(Clone, Debug)]
pub struct HashSetLit<T>(HashSet<T, FxBuildHasher>);

// Manual `Default` impl — do NOT use `#[derive]`. `#[derive(Default)]` on a
// generic struct adds a spurious `T: Default` bound, which would force every
// macro-generated element type (e.g. `Proc`) to implement `Default`. By
// constructing the empty set directly, `Default` is available on any
// `HashSetLit<T>` regardless of `T`.
impl<T> Default for HashSetLit<T> {
    fn default() -> Self {
        Self(HashSet::default())
    }
}

impl<T> PartialEq for HashSetLit<T>
where
    T: Eq + Hash,
{
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl<T> Eq for HashSetLit<T> where T: Eq + Hash {}

impl<T> HashSetLit<T> {
    #[inline]
    pub fn new() -> Self {
        Self(HashSet::default())
    }

    #[inline]
    pub fn insert(&mut self, item: T) -> bool
    where
        T: Eq + Hash,
    {
        self.0.insert(item)
    }

    #[inline]
    pub fn remove(&mut self, item: &T) -> bool
    where
        T: Eq + Hash,
    {
        self.0.remove(item)
    }

    #[inline]
    pub fn contains(&self, item: &T) -> bool
    where
        T: Eq + Hash,
    {
        self.0.contains(item)
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.0.len()
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    #[inline]
    pub fn iter(&self) -> impl Iterator<Item = &T> {
        self.0.iter()
    }

    pub fn union(&self, other: &Self) -> Self
    where
        T: Clone + Eq + Hash,
    {
        let mut out = self.0.clone();
        for item in other.0.iter() {
            out.insert(item.clone());
        }
        Self(out)
    }

    pub fn difference(&self, other: &Self) -> Self
    where
        T: Clone + Eq + Hash,
    {
        let mut out = Self::new();
        for item in self.0.iter() {
            if !other.0.contains(item) {
                out.0.insert(item.clone());
            }
        }
        out
    }
}

impl<T: Ord + Eq + Hash> PartialOrd for HashSetLit<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<T: Ord + Eq + Hash> Ord for HashSetLit<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        let mut a: Vec<_> = self.0.iter().collect();
        let mut b: Vec<_> = other.0.iter().collect();
        a.sort();
        b.sort();
        a.cmp(&b)
    }
}

impl<T: Hash + Ord> Hash for HashSetLit<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.len().hash(state);
        let mut elems: Vec<_> = self.0.iter().collect();
        elems.sort();
        for elem in elems {
            elem.hash(state);
        }
    }
}

impl<T> HashSetLit<T> {
    /// Order-independent hash whose per-element source is the caller's
    /// ALPHA-CANONICAL `semantic_hash` rather than the structural [`Hash`] above
    /// (#154).
    ///
    /// The sibling of [`HashBag::semantic_hash_into`](crate::HashBag::semantic_hash_into)
    /// and [`HashMapLit::semantic_hash_into`](crate::HashMapLit::semantic_hash_into),
    /// added because `semantic_hash`'s collection emitter had no method to call for
    /// a `HashSet`-shaped collection and fell back to structural `Hash` — which
    /// writes a binder's run-varying moniker `unique_id` into a CONSENSUS-VISIBLE
    /// fingerprint.
    ///
    /// ## Why it sorts by the SEMANTIC DIGEST and not by `T: Ord`
    ///
    /// `Hash for HashSetLit` restores determinism by sorting with `T: Ord`, which
    /// is the structural order — and for a binder-bearing `T` the structural order
    /// itself depends on `unique_id`. Sorting by it would therefore leak the very
    /// thing this method exists to exclude, through the ORDER instead of through
    /// the bytes. Sorting by the alpha-canonical per-element digest keeps
    /// order-independence (equal sets emit identical streams) while being
    /// name-free. This is exactly what `HashMapLit::semantic_hash_into` does, and
    /// it is stated here too because the reason is easy to lose.
    ///
    /// ⚠ Two elements whose semantic digests COLLIDE could be written in either
    /// relative order, so the stream is deterministic only up to digest collision —
    /// the same bound `HashMapLit::semantic_hash_into` carries. `HashBag` avoids it
    /// entirely with commutative lanes; matching that here would change the
    /// (already consensus-visible) `Bag` and `Map` streams too, so the three are
    /// deliberately left consistent with each other rather than individually
    /// perfected.
    pub fn semantic_hash_into<H, F>(&self, state: &mut H, elem_sem: F)
    where
        H: Hasher,
        F: Fn(&T, &mut FxHasher),
    {
        self.0.len().hash(state);
        let mut digests: Vec<u64> = self
            .0
            .iter()
            .map(|elem| {
                let mut hasher = FxHasher::default();
                elem_sem(elem, &mut hasher);
                hasher.finish()
            })
            .collect();
        digests.sort_unstable();
        for digest in digests {
            state.write_u64(digest);
        }
    }
}

impl<T> FromIterator<T> for HashSetLit<T>
where
    T: Eq + Hash,
{
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut set = HashSetLit::new();
        for item in iter {
            set.insert(item);
        }
        set
    }
}

impl<N, T> BoundTerm<N> for HashSetLit<T>
where
    N: Clone + PartialEq,
    T: Clone + Eq + Hash + BoundTerm<N>,
{
    fn term_eq(&self, other: &Self) -> bool {
        if self.len() != other.len() {
            return false;
        }
        for elem in self.iter() {
            let mut found = false;
            for other_elem in other.iter() {
                if elem.term_eq(other_elem) {
                    found = true;
                    break;
                }
            }
            if !found {
                return false;
            }
        }
        true
    }

    fn close_term(&mut self, state: ScopeState, on_free: &impl OnFreeFn<N>) {
        let old = std::mem::take(&mut self.0);
        self.0 = HashSet::default();
        for mut elem in old {
            elem.close_term(state, on_free);
            self.0.insert(elem);
        }
    }

    fn open_term(&mut self, state: ScopeState, on_bound: &impl OnBoundFn<N>) {
        let old = std::mem::take(&mut self.0);
        self.0 = HashSet::default();
        for mut elem in old {
            elem.open_term(state, on_bound);
            self.0.insert(elem);
        }
    }

    fn visit_vars(&self, on_var: &mut impl FnMut(&Var<N>)) {
        for elem in self.iter() {
            elem.visit_vars(on_var);
        }
    }

    fn visit_mut_vars(&mut self, on_var: &mut impl FnMut(&mut Var<N>)) {
        let old = std::mem::take(&mut self.0);
        self.0 = HashSet::default();
        for mut elem in old {
            elem.visit_mut_vars(on_var);
            self.0.insert(elem);
        }
    }
}

impl<T: fmt::Display + Ord> fmt::Display for HashSetLit<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut elems: Vec<_> = self.0.iter().collect();
        elems.sort_by_key(|e| e.to_string());
        write!(f, "Set(")?;
        for (i, elem) in elems.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", elem)?;
        }
        write!(f, ")")
    }
}

#[cfg(test)]
mod tests {
    use super::HashSetLit;

    #[test]
    fn union_difference_and_ord_are_deterministic() {
        let a = HashSetLit::from_iter([1, 2, 3]);
        let b = HashSetLit::from_iter([3, 4]);
        let union = a.union(&b);
        assert_eq!(union.len(), 4);
        assert!(union.contains(&1));
        assert!(union.contains(&4));

        let diff = a.difference(&b);
        assert_eq!(diff.len(), 2);
        assert!(diff.contains(&1));
        assert!(diff.contains(&2));
        assert!(!diff.contains(&3));

        let c = HashSetLit::from_iter([3, 2, 1]);
        assert_eq!(a, c);
        assert_eq!(a.cmp(&c), std::cmp::Ordering::Equal);
    }
}
