use std::collections::HashMap;
use std::hash::Hash;

use crate::{pathmap_lit_from_trie_and_keys, trie_and_key_index_from_lit, PathMapLit, PathTrie};

/// Minimal zipper-like editor over a crate-backed path trie and encoded key index.
pub struct PathTrieZipper<K, V>
where
    V: Clone + Send + Sync + Unpin,
{
    trie: PathTrie<V>,
    key_index: HashMap<Vec<u8>, K>,
    focus: Vec<u8>,
}

impl<K, V> PathTrieZipper<K, V>
where
    K: Clone + Eq + Hash,
    V: Clone + Send + Sync + Unpin,
{
    pub fn from_lit_with_encoder<F, E>(lit: &PathMapLit<K, V>, encode: F) -> Result<Self, E>
    where
        F: FnMut(&K) -> Result<Vec<u8>, E>,
    {
        let (trie, key_index) = trie_and_key_index_from_lit(lit, encode)?;
        Ok(Self { trie, key_index, focus: Vec::new() })
    }

    pub fn focus_encoded(&mut self, encoded_path: Vec<u8>) {
        self.focus = encoded_path;
    }

    pub fn get_focused(&self) -> Option<&V> {
        if self.key_index.contains_key(&self.focus) {
            self.trie.get_val_at(&self.focus)
        } else {
            None
        }
    }

    pub fn set_focused(&mut self, key: K, value: V) {
        self.trie.set_val_at(&self.focus, value);
        self.key_index.insert(self.focus.clone(), key);
    }

    pub fn delete_focused(&mut self) -> bool {
        self.key_index.remove(&self.focus).is_some()
    }

    pub fn into_lit(self) -> PathMapLit<K, V> {
        pathmap_lit_from_trie_and_keys(&self.trie, self.key_index)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn zipper_focus_set_get_delete_roundtrip() {
        let lit = PathMapLit::<String, i32>::new();
        let mut z = PathTrieZipper::from_lit_with_encoder(&lit, |k| {
            Ok::<Vec<u8>, ()>(k.as_bytes().to_vec())
        })
        .unwrap();
        z.focus_encoded(b"a/b".to_vec());
        z.set_focused("a/b".to_string(), 7);
        assert_eq!(z.get_focused(), Some(&7));
        assert!(z.delete_focused());
        assert_eq!(z.get_focused(), None);
        let out = z.into_lit();
        assert!(out.is_empty());
    }

    #[test]
    fn zipper_rejects_bad_key_from_initial_lit() {
        let mut lit = PathMapLit::<i32, i32>::new();
        lit.insert(0, 10);
        lit.insert(1, 11);
        let r: Result<_, ()> = PathTrieZipper::from_lit_with_encoder(&lit, |&k| {
            if k == 1 {
                Err(())
            } else {
                Ok(vec![k as u8])
            }
        });
        assert!(r.is_err());
    }
}
