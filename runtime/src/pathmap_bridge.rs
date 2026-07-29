//! Bridge between [`PathMapLit`] (deterministic `HashMapLit` storage for Ascent) and the
//! [`pathmap`](https://crates.io/crates/pathmap) trie (`PathMap<V>`).
//!
//! Encoders return `Result<Vec<u8>, E>` so callers can reject unsupported keys without silent
//! coercion.

use std::collections::HashMap;
use std::hash::Hash;

use pathmap::PathMap;

use crate::PathMapLit;

/// Crate trie type used for path-indexed values.
pub type PathTrie<V> = PathMap<V>;

/// Return type for [`trie_and_key_index_from_lit`].
pub type TrieAndKeyIndex<K, V> = (PathTrie<V>, HashMap<Vec<u8>, K>);

/// Build a trie from literal entries (no reverse key index).
pub fn trie_from_lit<K, V, F, E>(lit: &PathMapLit<K, V>, mut encode: F) -> Result<PathTrie<V>, E>
where
    K: Eq + Hash,
    V: Clone + Send + Sync + Unpin,
    F: FnMut(&K) -> Result<Vec<u8>, E>,
{
    let mut trie = PathTrie::new();
    for (k, v) in lit.iter() {
        trie.set_val_at(&encode(k)?, v.clone());
    }
    Ok(trie)
}

/// Build a trie plus reverse map from encoded path → canonical key handle.
pub fn trie_and_key_index_from_lit<K, V, F, E>(
    lit: &PathMapLit<K, V>,
    mut encode: F,
) -> Result<TrieAndKeyIndex<K, V>, E>
where
    K: Clone + Eq + Hash,
    V: Clone + Send + Sync + Unpin,
    F: FnMut(&K) -> Result<Vec<u8>, E>,
{
    let mut trie = PathTrie::new();
    let mut key_index = HashMap::new();
    for (k, v) in lit.iter() {
        let enc = encode(k)?;
        trie.set_val_at(&enc, v.clone());
        key_index.insert(enc, k.clone());
    }
    Ok((trie, key_index))
}

/// Rebuild a [`PathMapLit`] from a trie and the key index produced by [`trie_and_key_index_from_lit`].
///
/// # ★ The order is the TRIE's, and that is load-bearing (2026-07-29)
///
/// This used to iterate `key_index` directly:
///
/// ```ignore
/// for (enc, k) in key_index {                  // ⚠ std::HashMap iteration
///     if let Some(v) = trie.get_val_at(&enc) { out.insert(k, v.clone()); }
/// }
/// ```
///
/// `key_index` is a [`std::collections::HashMap`], whose iteration order is a
/// function of its `RandomState` seed — **randomised per process**. So the
/// rebuilt literal's insertion order was RUN-VARYING, and every operation that
/// round-trips through the trie (`pathmap_put`, `pathmap_merge`,
/// `pathmap_restrict`, `pathmap_subtract`, `pathmap_meet`, and the zipper
/// writers) produced a `PathMapLit` whose order changed from run to run.
///
/// That was invisible because it was MASKED in both places a pathmap's order can
/// be observed: generated `Display` sorted by formatted key, and `lower_pathmap`
/// sorted by `Ord` before building the `EMap`. Removing either sort (Ruling E —
/// "never sort pathmaps") exposes it immediately: `{| 1:10, 2:20 |}.set(3, 30)`
/// rendered as `{|2:20, 1:10, 3:30|}`.
///
/// ⚠ The masking was not equally benign in the two places. Display flakiness is
/// user-visible; the lowering's sort was the only thing keeping the `EMap` pair
/// order — and therefore the serialized bytes and the post-state hash —
/// deterministic. A run-varying wire order is a consensus break.
///
/// So the sorts were not merely redundant, they were LOAD-BEARING, and the honest
/// repair is at the root rather than at either observation point: walk the TRIE,
/// which iterates its keys in a deterministic order derived from the path bytes,
/// and use `key_index` only to recover each encoded key's original `K`.
///
/// This also PRE-STAGES #116 ("EPathMap must BE a trie map"), whose thesis is
/// exactly that a pathmap's canonical key order is derived from the trie rather
/// than from insertion or from a sort bolted onto one consumer.
///
/// An encoded key present in the trie but absent from `key_index` is skipped: it
/// has no original `K` to insert under, so inventing one is not available. That
/// cannot arise from this module's own operations (every `set_val_at` is paired
/// with a `key_index.insert`), and the skip is the same conservative behaviour
/// the previous `get_val_at`-guarded form had in the mirror direction.
pub fn pathmap_lit_from_trie_and_keys<K, V>(
    trie: &PathTrie<V>,
    key_index: HashMap<Vec<u8>, K>,
) -> PathMapLit<K, V>
where
    K: Eq + Hash + Clone,
    V: Clone + Send + Sync + Unpin,
{
    let mut out = PathMapLit::new();
    for (enc, v) in trie.iter() {
        if let Some(k) = key_index.get(enc.as_slice()) {
            out.insert(k.clone(), v.clone());
        }
    }
    out
}

/// Insert or overwrite one entry in trie + key index.
pub fn trie_put_encoded<K, V>(
    trie: &mut PathTrie<V>,
    key_index: &mut HashMap<Vec<u8>, K>,
    encoded_key: Vec<u8>,
    proc_key: K,
    value: V,
) where
    K: Clone + Eq + Hash,
    V: Clone + Send + Sync + Unpin,
{
    trie.set_val_at(&encoded_key, value);
    key_index.insert(encoded_key, proc_key);
}

/// Merge `other` into `trie` / `key_index` (right-hand keys overwrite on collision).
pub fn trie_merge_lit<K, V, F, E>(
    trie: &mut PathTrie<V>,
    key_index: &mut HashMap<Vec<u8>, K>,
    other: &PathMapLit<K, V>,
    mut encode: F,
) -> Result<(), E>
where
    K: Clone + Eq + Hash,
    V: Clone + Send + Sync + Unpin,
    F: FnMut(&K) -> Result<Vec<u8>, E>,
{
    for (k, v) in other.iter() {
        let enc = encode(k)?;
        trie.set_val_at(&enc, v.clone());
        key_index.insert(enc, k.clone());
    }
    Ok(())
}

/// Keep entries from `base` whose encoded paths also exist in `mask`.
pub fn trie_restrict_lit<K, V, F, E>(
    base: &PathMapLit<K, V>,
    mask: &PathMapLit<K, V>,
    encode: F,
) -> Result<PathMapLit<K, V>, E>
where
    K: Clone + Eq + Hash,
    V: Clone + Send + Sync + Unpin,
    F: FnMut(&K) -> Result<Vec<u8>, E> + Copy,
{
    let (base_trie, base_keys) = trie_and_key_index_from_lit(base, encode)?;
    let mask_trie = trie_from_lit(mask, encode)?;
    let kept_keys = base_keys
        .into_iter()
        .filter(|(enc, _)| mask_trie.get_val_at(enc).is_some())
        .collect::<HashMap<_, _>>();
    Ok(pathmap_lit_from_trie_and_keys(&base_trie, kept_keys))
}

/// Keep entries from `left` whose encoded paths do not exist in `right`.
pub fn trie_subtract_lit<K, V, F, E>(
    left: &PathMapLit<K, V>,
    right: &PathMapLit<K, V>,
    encode: F,
) -> Result<PathMapLit<K, V>, E>
where
    K: Clone + Eq + Hash,
    V: Clone + Send + Sync + Unpin,
    F: FnMut(&K) -> Result<Vec<u8>, E> + Copy,
{
    let (left_trie, left_keys) = trie_and_key_index_from_lit(left, encode)?;
    let right_trie = trie_from_lit(right, encode)?;
    let kept_keys = left_keys
        .into_iter()
        .filter(|(enc, _)| right_trie.get_val_at(enc).is_none())
        .collect::<HashMap<_, _>>();
    Ok(pathmap_lit_from_trie_and_keys(&left_trie, kept_keys))
}

/// Intersection by encoded path; values are taken from `right`.
pub fn trie_meet_lit<K, V, F, E>(
    left: &PathMapLit<K, V>,
    right: &PathMapLit<K, V>,
    encode: F,
) -> Result<PathMapLit<K, V>, E>
where
    K: Clone + Eq + Hash,
    V: Clone + Send + Sync + Unpin,
    F: FnMut(&K) -> Result<Vec<u8>, E> + Copy,
{
    let (_left_trie, left_keys) = trie_and_key_index_from_lit(left, encode)?;
    let right_trie = trie_from_lit(right, encode)?;
    let mut out = PathMapLit::new();
    for (enc, key) in left_keys {
        if let Some(v) = right_trie.get_val_at(&enc) {
            out.insert(key, v.clone());
        }
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn trie_roundtrip_through_lit() {
        let mut lit = PathMapLit::<String, i32>::new();
        lit.insert("a".into(), 1);
        lit.insert("b".into(), 2);
        let (trie, keys) =
            trie_and_key_index_from_lit(&lit, |k| Ok::<Vec<u8>, ()>(k.as_bytes().to_vec()))
                .unwrap();
        let lit2 = pathmap_lit_from_trie_and_keys(&trie, keys);
        assert_eq!(lit, lit2);
    }

    #[test]
    fn trie_from_lit_rejects_bad_key() {
        let mut lit = PathMapLit::<i32, ()>::new();
        lit.insert(0, ());
        lit.insert(1, ());
        let r: Result<_, ()> =
            trie_from_lit(&lit, |&k| if k == 1 { Err(()) } else { Ok(vec![k as u8]) });
        assert!(r.is_err());
    }

    #[test]
    fn trie_restrict_keeps_overlap() {
        let mut base = PathMapLit::<String, i32>::new();
        base.insert("a".into(), 1);
        base.insert("b".into(), 2);
        let mut mask = PathMapLit::<String, i32>::new();
        mask.insert("b".into(), 99);
        let out =
            trie_restrict_lit(&base, &mask, |k| Ok::<Vec<u8>, ()>(k.as_bytes().to_vec())).unwrap();
        assert_eq!(out.len(), 1);
        assert_eq!(out.get(&"b".to_string()), Some(&2));
    }

    #[test]
    fn trie_subtract_removes_overlap() {
        let mut left = PathMapLit::<String, i32>::new();
        left.insert("a".into(), 1);
        left.insert("b".into(), 2);
        let mut right = PathMapLit::<String, i32>::new();
        right.insert("b".into(), 9);
        let out =
            trie_subtract_lit(&left, &right, |k| Ok::<Vec<u8>, ()>(k.as_bytes().to_vec())).unwrap();
        assert_eq!(out.len(), 1);
        assert_eq!(out.get(&"a".to_string()), Some(&1));
    }

    #[test]
    fn trie_meet_intersects_with_right_values() {
        let mut left = PathMapLit::<String, i32>::new();
        left.insert("a".into(), 1);
        left.insert("b".into(), 2);
        let mut right = PathMapLit::<String, i32>::new();
        right.insert("b".into(), 20);
        let out =
            trie_meet_lit(&left, &right, |k| Ok::<Vec<u8>, ()>(k.as_bytes().to_vec())).unwrap();
        assert_eq!(out.len(), 1);
        assert_eq!(out.get(&"b".to_string()), Some(&20));
    }

    #[test]
    fn trie_set_ops_reject_bad_key() {
        let mut left = PathMapLit::<i32, i32>::new();
        left.insert(0, 0);
        left.insert(1, 1);
        let mut right = PathMapLit::<i32, i32>::new();
        right.insert(0, 9);
        let enc = |&k: &i32| if k == 1 { Err(()) } else { Ok(vec![k as u8]) };
        let r: Result<_, ()> = trie_restrict_lit(&left, &right, enc);
        assert!(r.is_err());
    }
}
