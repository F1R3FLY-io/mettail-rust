//! HashMapLit - ordered/hashable HashMap wrapper
//!
//! `std::collections::HashMap` does not implement `Hash` or `Ord`, but MeTTaIL
//! terms derive these traits so they can be stored in Ascent relations and
//! enumerated deterministically.
//!
//! `HashMapLit<K, V>` is a small newtype wrapper with deterministic `Hash` and
//! `Ord` implementations based on sorting entries by key (and value as a tie-breaker).

use rustc_hash::FxHasher;
use std::cmp::Ordering;
use std::collections::HashMap;
use std::fmt;
use std::hash::{BuildHasherDefault, Hash, Hasher};

use crate::{BoundTerm, Var};
use moniker::{OnBoundFn, OnFreeFn, ScopeState};

type FxBuildHasher = BuildHasherDefault<FxHasher>;

/// Deterministic, hashable, orderable map literal.
#[derive(Clone, Debug, Default)]
pub struct HashMapLit<K, V>(HashMap<K, V, FxBuildHasher>);

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
        Self(HashMap::default())
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
        self.0.remove(k)
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
    pub fn iter(&self) -> impl Iterator<Item = (&K, &V)> {
        self.0.iter()
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
        self.0 = HashMap::default();
        for (mut k, mut v) in old {
            k.close_term(state, on_free);
            v.close_term(state, on_free);
            self.0.insert(k, v);
        }
    }

    fn open_term(&mut self, state: ScopeState, on_bound: &impl OnBoundFn<N>) {
        let old = std::mem::take(&mut self.0);
        self.0 = HashMap::default();
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
        self.0 = HashMap::default();
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
