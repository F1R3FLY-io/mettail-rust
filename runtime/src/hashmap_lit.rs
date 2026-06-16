//! HashMapLit - ordered/hashable map wrapper
//!
//! `std::collections::HashMap` does not implement `Hash` or `Ord`, but MeTTaIL
//! terms derive these traits so they can be stored in Ascent relations and
//! enumerated deterministically. Additionally, `HashMap` has non-deterministic
//! iteration order, so user-facing operations like `keys()`/`values()` on a
//! `Map` literal produce flaky output — unacceptable for a language runtime
//! where e.g. `keys(map(a=1, b=2))[0]` must always return `a`.
//!
//! `HashMapLit<K, V>` wraps `indexmap::IndexMap` (insertion-order iteration)
//! with deterministic `Hash` and `Ord` implementations based on sorting
//! entries by key (and value as a tie-breaker). User-facing iteration
//! (`keys()`/`values()`/`iter()`) preserves insertion order; `Hash`/`Ord`
//! remain order-independent so equal maps always hash/compare equal
//! regardless of their insertion history.

use rustc_hash::FxHasher;
use std::cmp::Ordering;
use std::fmt;
use std::hash::{BuildHasherDefault, Hash, Hasher};

use crate::{BoundTerm, Var};
use moniker::{OnBoundFn, OnFreeFn, ScopeState};

type FxBuildHasher = BuildHasherDefault<FxHasher>;

/// Deterministic, hashable, orderable map literal backed by `IndexMap`
/// (insertion-order iteration).
#[derive(Clone, Debug)]
pub struct HashMapLit<K, V>(indexmap::IndexMap<K, V, FxBuildHasher>);

// Manual `Default` impl — do NOT use `#[derive]`. `#[derive(Default)]` on a
// generic struct requires `K: Default + V: Default`, which would force every
// macro-generated payload type (Proc, Expr, …) to implement `Default`. By
// constructing the empty map directly, `Default` is available on any
// `HashMapLit<K, V>` regardless of `K`/`V` bounds.
impl<K, V> Default for HashMapLit<K, V> {
    fn default() -> Self {
        Self(indexmap::IndexMap::with_hasher(FxBuildHasher::default()))
    }
}

impl<K, V> PartialEq for HashMapLit<K, V>
where
    K: Eq + Hash,
    V: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl<K, V> Eq for HashMapLit<K, V>
where
    K: Eq + Hash,
    V: Eq,
{
}

impl<K, V> HashMapLit<K, V> {
    #[inline]
    pub fn new() -> Self {
        Self::default()
    }

    #[inline]
    pub fn insert(&mut self, k: K, v: V) -> Option<V>
    where
        K: Eq + Hash,
    {
        self.0.insert(k, v)
    }

    #[inline]
    pub fn get(&self, k: &K) -> Option<&V>
    where
        K: Eq + Hash,
    {
        self.0.get(k)
    }

    #[inline]
    pub fn remove(&mut self, k: &K) -> Option<V>
    where
        K: Eq + Hash,
    {
        // `IndexMap::shift_remove` preserves insertion order (analogous to
        // removing a Vec element). `swap_remove` would reorder by moving the
        // last element into the removed slot, which violates our
        // deterministic-iteration contract.
        self.0.shift_remove(k)
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.0.len()
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// Iterate entries in insertion order.
    #[inline]
    pub fn iter(&self) -> impl Iterator<Item = (&K, &V)> {
        self.0.iter()
    }

    /// Iterate keys in insertion order.
    #[inline]
    pub fn keys(&self) -> impl Iterator<Item = &K> {
        self.0.keys()
    }

    /// Iterate values in insertion order.
    #[inline]
    pub fn values(&self) -> impl Iterator<Item = &V> {
        self.0.values()
    }

    /// Phase 4 #5b (2026-05-12): consume the map and return the inner
    /// `IndexMap`. Used by codegen sites (iterative_drop, iterative_clone,
    /// etc.) that need to walk the entries by value — `IndexMap` implements
    /// `IntoIterator<Item = (K, V)>` but `HashMapLit` (the newtype) does
    /// not implement it directly (manual impl would conflict with future
    /// `&HashMapLit` impls and would add a public API surface that's
    /// hard to evolve). Exposing the inner map gives callers the iterator
    /// without committing the wrapper to `IntoIterator`.
    #[inline]
    pub fn into_inner(self) -> indexmap::IndexMap<K, V, FxBuildHasher> {
        self.0
    }
}

impl<K: Ord + Eq + Hash, V: Ord> PartialOrd for HashMapLit<K, V> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<K: Ord + Eq + Hash, V: Ord> Ord for HashMapLit<K, V> {
    fn cmp(&self, other: &Self) -> Ordering {
        // Compare by sorted (key, value) pairs.
        let mut a: Vec<_> = self.0.iter().collect();
        let mut b: Vec<_> = other.0.iter().collect();
        a.sort_by(|(ka, va), (kb, vb)| ka.cmp(kb).then_with(|| va.cmp(vb)));
        b.sort_by(|(ka, va), (kb, vb)| ka.cmp(kb).then_with(|| va.cmp(vb)));
        a.cmp(&b)
    }
}

impl<K: Hash + Ord, V: Hash + Ord> Hash for HashMapLit<K, V> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.len().hash(state);
        let mut entries: Vec<_> = self.0.iter().collect();
        entries.sort_by(|(ka, va), (kb, vb)| ka.cmp(kb).then_with(|| va.cmp(vb)));
        for (k, v) in entries {
            k.hash(state);
            v.hash(state);
        }
    }
}

impl<K, V> HashMapLit<K, V> {
    /// Order-independent SEMANTIC hash: like [`Hash::hash`] but each key/value is
    /// hashed through `key_sem`/`val_sem` (their alpha-canonical `semantic_hash`)
    /// instead of `std::hash::Hash`, and entries are ordered by their SEMANTIC
    /// digest rather than by structural `Ord`.
    ///
    /// Both the per-entry hash source AND the ordering must be semantic: the
    /// structural `Ord` used by `Hash::hash` sorts via the binder's run-varying
    /// `unique_id` (`Scope::cmp`), which would make the emitted byte stream
    /// non-deterministic for maps whose keys/values contain binders. Sorting by
    /// the alpha-canonical semantic digest restores determinism while keeping
    /// order-independence (equal maps emit identical streams).
    pub fn semantic_hash_into<H, FK, FV>(&self, state: &mut H, key_sem: FK, val_sem: FV)
    where
        H: Hasher,
        FK: Fn(&K, &mut FxHasher),
        FV: Fn(&V, &mut FxHasher),
    {
        self.0.len().hash(state);
        let mut entries: Vec<(u64, u64)> = self
            .0
            .iter()
            .map(|(k, v)| {
                let mut hk = FxHasher::default();
                key_sem(k, &mut hk);
                let mut hv = FxHasher::default();
                val_sem(v, &mut hv);
                (hk.finish(), hv.finish())
            })
            .collect();
        entries.sort_unstable();
        for (kd, vd) in entries {
            state.write_u64(kd);
            state.write_u64(vd);
        }
    }
}

impl<K, V> FromIterator<(K, V)> for HashMapLit<K, V>
where
    K: Eq + Hash,
{
    fn from_iter<T: IntoIterator<Item = (K, V)>>(iter: T) -> Self {
        let mut m = HashMapLit::new();
        for (k, v) in iter {
            m.insert(k, v);
        }
        m
    }
}

impl<N, K, V> BoundTerm<N> for HashMapLit<K, V>
where
    N: Clone + PartialEq,
    K: Clone + Eq + Hash + BoundTerm<N>,
    V: Clone + BoundTerm<N>,
{
    fn term_eq(&self, other: &Self) -> bool {
        if self.len() != other.len() {
            return false;
        }
        // Key/value alpha-equivalence aware: every entry in self must match some entry in other.
        for (k1, v1) in self.iter() {
            let mut found = false;
            for (k2, v2) in other.iter() {
                if k1.term_eq(k2) && v1.term_eq(v2) {
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
        // Need rebuild since keys can change identity.
        let old = std::mem::take(&mut self.0);
        self.0 = indexmap::IndexMap::with_hasher(FxBuildHasher::default());
        for (mut k, mut v) in old {
            k.close_term(state, on_free);
            v.close_term(state, on_free);
            self.0.insert(k, v);
        }
    }

    fn open_term(&mut self, state: ScopeState, on_bound: &impl OnBoundFn<N>) {
        let old = std::mem::take(&mut self.0);
        self.0 = indexmap::IndexMap::with_hasher(FxBuildHasher::default());
        for (mut k, mut v) in old {
            k.open_term(state, on_bound);
            v.open_term(state, on_bound);
            self.0.insert(k, v);
        }
    }

    fn visit_vars(&self, on_var: &mut impl FnMut(&Var<N>)) {
        for (k, v) in self.iter() {
            k.visit_vars(on_var);
            v.visit_vars(on_var);
        }
    }

    fn visit_mut_vars(&mut self, on_var: &mut impl FnMut(&mut Var<N>)) {
        let old = std::mem::take(&mut self.0);
        self.0 = indexmap::IndexMap::with_hasher(FxBuildHasher::default());
        for (mut k, mut v) in old {
            k.visit_mut_vars(on_var);
            v.visit_mut_vars(on_var);
            self.0.insert(k, v);
        }
    }
}

impl<K: fmt::Display + Ord, V: fmt::Display + Ord> fmt::Display for HashMapLit<K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // Generic debug-ish form; language-specific display (map(...)) is generated in macros.
        let mut entries: Vec<_> = self.0.iter().collect();
        entries.sort_by_key(|(k, _)| *k);
        write!(f, "{{")?;
        let mut first = true;
        for (k, v) in entries {
            if !first {
                write!(f, ", ")?;
            }
            first = false;
            write!(f, "{}:{}", k, v)?;
        }
        write!(f, "}}")
    }
}
