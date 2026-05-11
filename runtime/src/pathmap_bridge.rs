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
pub fn pathmap_lit_from_trie_and_keys<K, V>(
    trie: &PathTrie<V>,
    key_index: HashMap<Vec<u8>, K>,
) -> PathMapLit<K, V>
where
    K: Eq + Hash + Clone,
    V: Clone + Send + Sync + Unpin,
{
    let mut out = PathMapLit::new();
    for (enc, k) in key_index {
        if let Some(v) = trie.get_val_at(&enc) {
            out.insert(k, v.clone());
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
}
