//! PathMapLit — path-keyed map wrapper for Rholang `Pathmap` literals.
//!
//! Stored as [`HashMapLit`] so Ascent relations keep deterministic `Hash` / `Ord` / `BoundTerm`.
//! Language-level path operations also use the `pathmap` crate trie via
//! [`crate::pathmap_bridge`] (encode keys to bytes, then `PathMap` lookup / update).

use std::cmp::Ordering;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::ops::{Deref, DerefMut};

use crate::{BoundTerm, HashMapLit, Var};
use moniker::{OnBoundFn, OnFreeFn, ScopeState};

/// Deterministic path-map literal (same representation as [`HashMapLit`]).
#[derive(Clone, Debug)]
pub struct PathMapLit<K, V>(pub HashMapLit<K, V>);

// Manual `Default` impl — do NOT use `#[derive]`. `#[derive(Default)]` on a
// generic struct adds spurious `K: Default, V: Default` bounds, which would
// force every macro-generated key/value type (e.g. `Proc`) to implement
// `Default`. Delegate to `HashMapLit`'s no-bound `Default`.
impl<K, V> Default for PathMapLit<K, V> {
    fn default() -> Self {
        Self(HashMapLit::default())
    }
}

impl<K, V> PathMapLit<K, V> {
    #[inline]
    pub fn new() -> Self {
        Self(HashMapLit::new())
    }
}

impl<K, V> Deref for PathMapLit<K, V> {
    type Target = HashMapLit<K, V>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<K, V> DerefMut for PathMapLit<K, V> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<K, V> PartialEq for PathMapLit<K, V>
where
    K: Eq + Hash,
    V: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl<K, V> Eq for PathMapLit<K, V>
where
    K: Eq + Hash,
    V: Eq,
{
}

impl<K: Ord + Eq + Hash, V: Ord> PartialOrd for PathMapLit<K, V> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<K: Ord + Eq + Hash, V: Ord> Ord for PathMapLit<K, V> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.0.cmp(&other.0)
    }
}

impl<K: Hash + Ord, V: Hash + Ord> Hash for PathMapLit<K, V> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.hash(state);
    }
}

/// By-value iteration over `(key, value)` pairs. ★ #162 — added for the generated
/// iterative `Drop`; see [`HashSetLit`](crate::HashSetLit)'s impl. `Deref` cannot
/// serve here because `Deref` only yields a borrow and `Drop` needs to MOVE.
impl<K, V> IntoIterator for PathMapLit<K, V> {
    type Item = (K, V);
    type IntoIter = <HashMapLit<K, V> as IntoIterator>::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<K, V> FromIterator<(K, V)> for PathMapLit<K, V>
where
    K: Eq + Hash,
{
    fn from_iter<T: IntoIterator<Item = (K, V)>>(iter: T) -> Self {
        Self(iter.into_iter().collect::<HashMapLit<K, V>>())
    }
}

impl<N, K, V> BoundTerm<N> for PathMapLit<K, V>
where
    N: Clone + PartialEq,
    K: Clone + Eq + Hash + BoundTerm<N>,
    V: Clone + BoundTerm<N>,
{
    fn term_eq(&self, other: &Self) -> bool {
        self.0.term_eq(&other.0)
    }

    fn close_term(&mut self, state: ScopeState, on_free: &impl OnFreeFn<N>) {
        self.0.close_term(state, on_free);
    }

    fn open_term(&mut self, state: ScopeState, on_bound: &impl OnBoundFn<N>) {
        self.0.open_term(state, on_bound);
    }

    fn visit_vars(&self, on_var: &mut impl FnMut(&Var<N>)) {
        self.0.visit_vars(on_var);
    }

    fn visit_mut_vars(&mut self, on_var: &mut impl FnMut(&mut Var<N>)) {
        self.0.visit_mut_vars(on_var);
    }
}

impl<K: fmt::Display + Ord, V: fmt::Display + Ord> fmt::Display for PathMapLit<K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}
