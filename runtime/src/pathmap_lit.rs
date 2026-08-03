//! Homogeneous path-map literal storage.
//!
//! A path-map is one of three states: neutral empty, a set of paths, or a map
//! from paths to values.  Set and map membership cannot coexist in one value.
//! This mirrors f1r3node's `EPathMapRepr::{Empty, Set(PathMap<()>),
//! Map(PathMap<Par>)}` at the syntax/runtime boundary without attaching an
//! `Option`-like tag to every entry.
//!
//! `PathMapLit` deliberately keeps the source-language key objects until the
//! f1r3node lowering boundary.  The lowering encodes those keys once into the
//! target's prefix-compressed `PathMap`; it never flattens an `EPathMap` back to
//! a list or ordinary hash map.

use std::cmp::Ordering;
use std::fmt;
use std::hash::{Hash, Hasher};

use crate::{BoundTerm, HashMapLit, Var};
use moniker::{OnBoundFn, OnFreeFn, ScopeState};
use rustc_hash::FxHasher;

/// Storage specialization selected by the first non-empty entry.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum PathMapMode {
    /// No entry has selected set or map storage yet.
    #[default]
    Empty,
    /// Every entry is a value-free path member.
    Set,
    /// Every entry has an associated value.
    Map,
}

/// A rejected operation that would mix set and map membership.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PathMapModeError {
    pub expected: PathMapMode,
    pub actual: PathMapMode,
}

impl fmt::Display for PathMapModeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "pathmap is in {:?} mode; {:?} operation would mix set and map membership",
            self.actual, self.expected
        )
    }
}

impl std::error::Error for PathMapModeError {}

/// One borrowed homogeneous entry.
#[derive(Debug, PartialEq, Eq)]
pub enum PathMapEntryRef<'a, K, V> {
    Set(&'a K),
    Map(&'a K, &'a V),
}

impl<K, V> Copy for PathMapEntryRef<'_, K, V> {}

impl<K, V> Clone for PathMapEntryRef<'_, K, V> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<'a, K, V> PathMapEntryRef<'a, K, V> {
    #[inline]
    pub fn key(&self) -> &'a K {
        match *self {
            Self::Set(key) | Self::Map(key, _) => key,
        }
    }

    #[inline]
    pub fn value(&self) -> Option<&'a V> {
        match *self {
            Self::Set(_) => None,
            Self::Map(_, value) => Some(value),
        }
    }

    #[inline]
    pub fn is_set(&self) -> bool {
        matches!(self, Self::Set(_))
    }

    #[inline]
    pub fn is_map(&self) -> bool {
        matches!(self, Self::Map(_, _))
    }
}

/// One owned homogeneous entry, used by generated destructive PDAs.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum PathMapEntry<K, V> {
    Set(K),
    Map(K, V),
}

/// A path-keyed literal with one mode for the whole container.
#[derive(Clone, Debug)]
pub enum PathMapLit<K, V> {
    Empty,
    Set(HashMapLit<K, ()>),
    Map(HashMapLit<K, V>),
}

impl<K, V> Default for PathMapLit<K, V> {
    fn default() -> Self {
        Self::Empty
    }
}

impl<K, V> PathMapLit<K, V> {
    #[inline]
    pub fn new() -> Self {
        Self::Empty
    }

    #[inline]
    pub fn mode(&self) -> PathMapMode {
        match self {
            Self::Empty => PathMapMode::Empty,
            Self::Set(_) => PathMapMode::Set,
            Self::Map(_) => PathMapMode::Map,
        }
    }

    #[inline]
    pub fn len(&self) -> usize {
        match self {
            Self::Empty => 0,
            Self::Set(entries) => entries.len(),
            Self::Map(entries) => entries.len(),
        }
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    #[inline]
    pub fn as_set(&self) -> Option<&HashMapLit<K, ()>> {
        match self {
            Self::Set(entries) => Some(entries),
            Self::Empty | Self::Map(_) => None,
        }
    }

    #[inline]
    pub fn as_map(&self) -> Option<&HashMapLit<K, V>> {
        match self {
            Self::Map(entries) => Some(entries),
            Self::Empty | Self::Set(_) => None,
        }
    }

    #[inline]
    pub fn iter(&self) -> PathMapIter<'_, K, V> {
        let inner = match self {
            Self::Empty => PathMapIterInner::Empty,
            Self::Set(entries) => PathMapIterInner::Set(entries.iter()),
            Self::Map(entries) => PathMapIterInner::Map(entries.iter()),
        };
        PathMapIter { inner }
    }

    #[inline]
    pub fn keys(&self) -> PathMapKeys<'_, K, V> {
        PathMapKeys { inner: self.iter() }
    }

    #[inline]
    pub fn entry(&self, key: &K) -> Option<PathMapEntryRef<'_, K, V>>
    where
        K: Eq + Hash,
    {
        match self {
            Self::Empty => None,
            Self::Set(entries) => entries
                .get_key_value(key)
                .map(|(stored_key, ())| PathMapEntryRef::Set(stored_key)),
            Self::Map(entries) => entries
                .get_key_value(key)
                .map(|(stored_key, value)| PathMapEntryRef::Map(stored_key, value)),
        }
    }

    #[inline]
    pub fn contains_key(&self, key: &K) -> bool
    where
        K: Eq + Hash,
    {
        self.entry(key).is_some()
    }

    /// Borrow a map value. Set mode is a type error, not a missing key.
    #[inline]
    pub fn get_map(&self, key: &K) -> Result<Option<&V>, PathMapModeError>
    where
        K: Eq + Hash,
    {
        match self {
            Self::Empty => Ok(None),
            Self::Set(_) => Err(PathMapModeError {
                expected: PathMapMode::Map,
                actual: PathMapMode::Set,
            }),
            Self::Map(entries) => Ok(entries.get(key)),
        }
    }

    /// Insert one value-free path. The first insertion specializes `Empty` to
    /// set mode; map mode is rejected.
    pub fn insert_set(&mut self, key: K) -> Result<bool, PathMapModeError>
    where
        K: Eq + Hash,
    {
        if matches!(self, Self::Map(_)) {
            return Err(PathMapModeError {
                expected: PathMapMode::Set,
                actual: PathMapMode::Map,
            });
        }
        if matches!(self, Self::Empty) {
            *self = Self::Set(HashMapLit::new());
        }
        let Self::Set(entries) = self else {
            unreachable!("map mode was rejected and empty mode was specialized")
        };
        Ok(entries.insert(key, ()).is_none())
    }

    /// Insert one key/value entry. The first insertion specializes `Empty` to
    /// map mode; set mode is rejected.
    pub fn insert_map(&mut self, key: K, value: V) -> Result<Option<V>, PathMapModeError>
    where
        K: Eq + Hash,
    {
        if matches!(self, Self::Set(_)) {
            return Err(PathMapModeError {
                expected: PathMapMode::Map,
                actual: PathMapMode::Set,
            });
        }
        if matches!(self, Self::Empty) {
            *self = Self::Map(HashMapLit::new());
        }
        let Self::Map(entries) = self else {
            unreachable!("set mode was rejected and empty mode was specialized")
        };
        Ok(entries.insert(key, value))
    }

    /// Remove a key and return the entry shape it had. Removing the final entry
    /// restores neutral empty mode.
    pub fn remove(&mut self, key: &K) -> Option<PathMapEntry<K, V>>
    where
        K: Clone + Eq + Hash,
    {
        let removed = match self {
            Self::Empty => None,
            Self::Set(entries) => entries.remove(key).map(|()| PathMapEntry::Set(key.clone())),
            Self::Map(entries) => entries
                .remove(key)
                .map(|value| PathMapEntry::Map(key.clone(), value)),
        };
        if self.is_empty() {
            *self = Self::Empty;
        }
        removed
    }

    pub fn from_set_iter(iter: impl IntoIterator<Item = K>) -> Self
    where
        K: Eq + Hash,
    {
        let mut out = Self::Empty;
        for key in iter {
            out.insert_set(key)
                .expect("a fresh set pathmap cannot be in map mode");
        }
        out
    }

    pub fn from_map_iter(iter: impl IntoIterator<Item = (K, V)>) -> Self
    where
        K: Eq + Hash,
    {
        let mut out = Self::Empty;
        for (key, value) in iter {
            out.insert_map(key, value)
                .expect("a fresh map pathmap cannot be in set mode");
        }
        out
    }

    /// Order-independent semantic hash with one container-mode tag. Set mode
    /// hashes keys only; map mode hashes keys and values.
    pub fn semantic_hash_into<H, FK, FV>(&self, state: &mut H, key_sem: FK, value_sem: FV)
    where
        H: Hasher,
        FK: Fn(&K, &mut FxHasher),
        FV: Fn(&V, &mut FxHasher),
    {
        self.mode().hash(state);
        match self {
            Self::Empty => state.write_usize(0),
            Self::Set(entries) => {
                entries.semantic_hash_into(state, key_sem, |_unit, _hasher| {});
            },
            Self::Map(entries) => entries.semantic_hash_into(state, key_sem, value_sem),
        }
    }
}

enum PathMapIterInner<'a, K, V> {
    Empty,
    Set(indexmap::map::Iter<'a, K, ()>),
    Map(indexmap::map::Iter<'a, K, V>),
}

pub struct PathMapIter<'a, K, V> {
    inner: PathMapIterInner<'a, K, V>,
}

impl<'a, K, V> Iterator for PathMapIter<'a, K, V> {
    type Item = PathMapEntryRef<'a, K, V>;

    fn next(&mut self) -> Option<Self::Item> {
        match &mut self.inner {
            PathMapIterInner::Empty => None,
            PathMapIterInner::Set(entries) => {
                entries.next().map(|(key, ())| PathMapEntryRef::Set(key))
            },
            PathMapIterInner::Map(entries) => entries
                .next()
                .map(|(key, value)| PathMapEntryRef::Map(key, value)),
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.len();
        (len, Some(len))
    }
}

impl<K, V> ExactSizeIterator for PathMapIter<'_, K, V> {
    fn len(&self) -> usize {
        match &self.inner {
            PathMapIterInner::Empty => 0,
            PathMapIterInner::Set(entries) => entries.len(),
            PathMapIterInner::Map(entries) => entries.len(),
        }
    }
}

pub struct PathMapKeys<'a, K, V> {
    inner: PathMapIter<'a, K, V>,
}

impl<'a, K, V> Iterator for PathMapKeys<'a, K, V> {
    type Item = &'a K;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|entry| entry.key())
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<K, V> ExactSizeIterator for PathMapKeys<'_, K, V> {
    fn len(&self) -> usize {
        self.inner.len()
    }
}

pub enum PathMapIntoIter<K, V> {
    Empty,
    Set(indexmap::map::IntoIter<K, ()>),
    Map(indexmap::map::IntoIter<K, V>),
}

impl<K, V> Iterator for PathMapIntoIter<K, V> {
    type Item = PathMapEntry<K, V>;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            Self::Empty => None,
            Self::Set(entries) => entries.next().map(|(key, ())| PathMapEntry::Set(key)),
            Self::Map(entries) => entries
                .next()
                .map(|(key, value)| PathMapEntry::Map(key, value)),
        }
    }
}

impl<K, V> IntoIterator for PathMapLit<K, V> {
    type Item = PathMapEntry<K, V>;
    type IntoIter = PathMapIntoIter<K, V>;

    fn into_iter(self) -> Self::IntoIter {
        match self {
            Self::Empty => PathMapIntoIter::Empty,
            Self::Set(entries) => PathMapIntoIter::Set(entries.into_iter()),
            Self::Map(entries) => PathMapIntoIter::Map(entries.into_iter()),
        }
    }
}

impl<K, V> PartialEq for PathMapLit<K, V>
where
    K: Eq + Hash,
    V: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Empty, Self::Empty) => true,
            (Self::Set(left), Self::Set(right)) => left == right,
            (Self::Map(left), Self::Map(right)) => left == right,
            _ => false,
        }
    }
}

impl<K, V> Eq for PathMapLit<K, V>
where
    K: Eq + Hash,
    V: Eq,
{
}

impl<K, V> PartialOrd for PathMapLit<K, V>
where
    K: Ord + Eq + Hash,
    V: Ord,
{
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<K, V> Ord for PathMapLit<K, V>
where
    K: Ord + Eq + Hash,
    V: Ord,
{
    fn cmp(&self, other: &Self) -> Ordering {
        self.mode()
            .cmp(&other.mode())
            .then_with(|| match (self, other) {
                (Self::Set(left), Self::Set(right)) => left.cmp(right),
                (Self::Map(left), Self::Map(right)) => left.cmp(right),
                _ => Ordering::Equal,
            })
    }
}

impl<K, V> Hash for PathMapLit<K, V>
where
    K: Hash + Ord,
    V: Hash + Ord,
{
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.mode().hash(state);
        match self {
            Self::Empty => {},
            Self::Set(entries) => entries.hash(state),
            Self::Map(entries) => entries.hash(state),
        }
    }
}

impl<N, K, V> BoundTerm<N> for PathMapLit<K, V>
where
    N: Clone + PartialEq,
    K: Clone + Eq + Hash + BoundTerm<N>,
    V: Clone + BoundTerm<N>,
{
    fn term_eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Empty, Self::Empty) => true,
            (Self::Set(left), Self::Set(right)) => left.term_eq(right),
            (Self::Map(left), Self::Map(right)) => left.term_eq(right),
            _ => false,
        }
    }

    fn close_term(&mut self, state: ScopeState, on_free: &impl OnFreeFn<N>) {
        match self {
            Self::Empty => {},
            Self::Set(entries) => {
                let old = std::mem::take(entries);
                let mut rebuilt = HashMapLit::new();
                for (mut key, ()) in old {
                    key.close_term(state, on_free);
                    rebuilt.insert(key, ());
                }
                *entries = rebuilt;
            },
            Self::Map(entries) => {
                let old = std::mem::take(entries);
                let mut rebuilt = HashMapLit::new();
                for (mut key, mut value) in old {
                    key.close_term(state, on_free);
                    value.close_term(state, on_free);
                    rebuilt.insert(key, value);
                }
                *entries = rebuilt;
            },
        }
    }

    fn open_term(&mut self, state: ScopeState, on_bound: &impl OnBoundFn<N>) {
        match self {
            Self::Empty => {},
            Self::Set(entries) => {
                let old = std::mem::take(entries);
                let mut rebuilt = HashMapLit::new();
                for (mut key, ()) in old {
                    key.open_term(state, on_bound);
                    rebuilt.insert(key, ());
                }
                *entries = rebuilt;
            },
            Self::Map(entries) => {
                let old = std::mem::take(entries);
                let mut rebuilt = HashMapLit::new();
                for (mut key, mut value) in old {
                    key.open_term(state, on_bound);
                    value.open_term(state, on_bound);
                    rebuilt.insert(key, value);
                }
                *entries = rebuilt;
            },
        }
    }

    fn visit_vars(&self, on_var: &mut impl FnMut(&Var<N>)) {
        for entry in self.iter() {
            entry.key().visit_vars(on_var);
            if let Some(value) = entry.value() {
                value.visit_vars(on_var);
            }
        }
    }

    fn visit_mut_vars(&mut self, on_var: &mut impl FnMut(&mut Var<N>)) {
        match self {
            Self::Empty => {},
            Self::Set(entries) => {
                let old = std::mem::take(entries);
                let mut rebuilt = HashMapLit::new();
                for (mut key, ()) in old {
                    key.visit_mut_vars(on_var);
                    rebuilt.insert(key, ());
                }
                *entries = rebuilt;
            },
            Self::Map(entries) => {
                let old = std::mem::take(entries);
                let mut rebuilt = HashMapLit::new();
                for (mut key, mut value) in old {
                    key.visit_mut_vars(on_var);
                    value.visit_mut_vars(on_var);
                    rebuilt.insert(key, value);
                }
                *entries = rebuilt;
            },
        }
    }
}

impl<K, V> fmt::Display for PathMapLit<K, V>
where
    K: fmt::Display,
    V: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut first = true;
        for entry in self.iter() {
            if !first {
                f.write_str(", ")?;
            }
            first = false;
            write!(f, "{}", entry.key())?;
            if let Some(value) = entry.value() {
                write!(f, ": {value}")?;
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_selects_a_mode_on_first_insert() {
        let mut set = PathMapLit::<i32, i32>::new();
        assert_eq!(set.mode(), PathMapMode::Empty);
        assert_eq!(set.insert_set(1), Ok(true));
        assert_eq!(set.mode(), PathMapMode::Set);

        let mut map = PathMapLit::<i32, i32>::new();
        assert_eq!(map.insert_map(1, 2), Ok(None));
        assert_eq!(map.mode(), PathMapMode::Map);
    }

    #[test]
    fn mixed_membership_is_unrepresentable_through_the_api() {
        let mut set = PathMapLit::<i32, i32>::new();
        set.insert_set(1).unwrap();
        assert!(set.insert_map(2, 3).is_err());

        let mut map = PathMapLit::<i32, i32>::new();
        map.insert_map(1, 2).unwrap();
        assert!(map.insert_set(3).is_err());
    }

    #[test]
    fn deleting_the_last_entry_restores_neutral_empty() {
        let mut map = PathMapLit::<i32, i32>::new();
        map.insert_map(1, 2).unwrap();
        assert_eq!(map.remove(&1), Some(PathMapEntry::Map(1, 2)));
        assert_eq!(map.mode(), PathMapMode::Empty);
    }
}
