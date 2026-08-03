//! Rholang path encoding and homogeneous trie-backed pathmap operations.

use std::collections::HashMap;

use mettail_runtime::{
    homogeneous_lit_from_trie_and_keys, homogeneous_trie_and_key_index, HomogeneousPathTrie,
    PathMapLit,
};
use pathmap::PathMap;

use super::{List, Proc};

pub(crate) type ProcPathMap = PathMapLit<Proc, Proc>;

/// Result of an exact-key lookup. Set membership and map values are separate
/// outcomes; absence is separate from both.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum PathmapLookup {
    Absent,
    SetMember,
    MapValue(Proc),
}

/// Path segments for trie keys. `None` when the path is not encodable (for
/// example the empty list path).
fn proc_path_segments(key: &Proc) -> Option<Vec<Vec<u8>>> {
    match key {
        Proc::CastList(inner) => match inner.as_ref() {
            List::ListLit(items) if items.is_empty() => None,
            List::ListLit(items) => Some(
                items
                    .iter()
                    .map(|segment| segment.to_string().into_bytes())
                    .collect(),
            ),
            _ => Some(vec![key.to_string().into_bytes()]),
        },
        _ => Some(vec![key.to_string().into_bytes()]),
    }
}

fn proc_to_path_key_bytes(key: &Proc) -> Option<Vec<u8>> {
    Some(mettail_runtime::flatten_segments(&proc_path_segments(key)?))
}

pub(crate) fn encode_proc_path_entry(key: &Proc) -> Result<Vec<u8>, ()> {
    proc_to_path_key_bytes(key).ok_or(())
}

fn encoded(
    payload: &ProcPathMap,
) -> Result<(HomogeneousPathTrie<Proc>, HashMap<Vec<u8>, Proc>), ()> {
    homogeneous_trie_and_key_index(payload, encode_proc_path_entry)
}

pub(crate) fn pathmap_get(payload: &ProcPathMap, key: &Proc) -> Result<PathmapLookup, ()> {
    let key = encode_proc_path_entry(key)?;
    let (trie, _) = encoded(payload)?;
    Ok(match trie {
        HomogeneousPathTrie::Empty => PathmapLookup::Absent,
        HomogeneousPathTrie::Set(trie) => match trie.get(&key) {
            Some(()) => PathmapLookup::SetMember,
            None => PathmapLookup::Absent,
        },
        HomogeneousPathTrie::Map(trie) => match trie.get(&key) {
            Some(value) => PathmapLookup::MapValue(value.clone()),
            None => PathmapLookup::Absent,
        },
    })
}

pub(crate) fn pathmap_has(payload: &ProcPathMap, key: &Proc) -> Result<bool, ()> {
    Ok(!matches!(pathmap_get(payload, key)?, PathmapLookup::Absent))
}

/// Bind `key` to `value`. Empty selects map mode; set mode is rejected.
pub(crate) fn pathmap_put(
    payload: &ProcPathMap,
    key: &Proc,
    value: Proc,
) -> Result<ProcPathMap, ()> {
    let encoded_key = encode_proc_path_entry(key)?;
    let (trie, mut keys) = encoded(payload)?;
    let trie = match trie {
        HomogeneousPathTrie::Empty => {
            let mut map = PathMap::new();
            map.insert(&encoded_key, value);
            HomogeneousPathTrie::Map(map)
        },
        HomogeneousPathTrie::Set(_) => return Err(()),
        HomogeneousPathTrie::Map(mut map) => {
            map.insert(&encoded_key, value);
            HomogeneousPathTrie::Map(map)
        },
    };
    keys.insert(encoded_key, key.clone());
    Ok(homogeneous_lit_from_trie_and_keys(&trie, &keys))
}

fn merge_key_indexes(
    mut left: HashMap<Vec<u8>, Proc>,
    right: HashMap<Vec<u8>, Proc>,
) -> HashMap<Vec<u8>, Proc> {
    left.extend(right);
    left
}

pub(crate) fn pathmap_merge(left: &ProcPathMap, right: &ProcPathMap) -> Result<ProcPathMap, ()> {
    let (left_trie, left_keys) = encoded(left)?;
    let (right_trie, right_keys) = encoded(right)?;
    let trie = match (left_trie, right_trie) {
        (HomogeneousPathTrie::Empty, right) => right,
        (left, HomogeneousPathTrie::Empty) => left,
        (HomogeneousPathTrie::Set(mut left), HomogeneousPathTrie::Set(right)) => {
            for (key, ()) in right.iter() {
                left.insert(&key, ());
            }
            HomogeneousPathTrie::Set(left)
        },
        (HomogeneousPathTrie::Map(mut left), HomogeneousPathTrie::Map(right)) => {
            for (key, value) in right.iter() {
                left.insert(&key, value.clone());
            }
            HomogeneousPathTrie::Map(left)
        },
        _ => return Err(()),
    };
    let keys = merge_key_indexes(left_keys, right_keys);
    Ok(homogeneous_lit_from_trie_and_keys(&trie, &keys))
}

pub(crate) fn pathmap_restrict(base: &ProcPathMap, mask: &ProcPathMap) -> Result<ProcPathMap, ()> {
    let (base_trie, base_keys) = encoded(base)?;
    let (mask_trie, _) = encoded(mask)?;
    let (trie, keys) = match (base_trie, mask_trie) {
        (HomogeneousPathTrie::Empty, _) | (_, HomogeneousPathTrie::Empty) => {
            (HomogeneousPathTrie::Empty, HashMap::new())
        },
        (HomogeneousPathTrie::Set(base), HomogeneousPathTrie::Set(mask)) => {
            let mut out = PathMap::new();
            let mut keys = HashMap::new();
            for (key, ()) in base.iter() {
                if mask.get(&key).is_some() {
                    out.insert(&key, ());
                    if let Some(source) = base_keys.get(key.as_slice()) {
                        keys.insert(key, source.clone());
                    }
                }
            }
            (HomogeneousPathTrie::Set(out), keys)
        },
        (HomogeneousPathTrie::Map(base), HomogeneousPathTrie::Map(mask)) => {
            let mut out = PathMap::new();
            let mut keys = HashMap::new();
            for (key, value) in base.iter() {
                if mask.get(&key).is_some() {
                    out.insert(&key, value.clone());
                    if let Some(source) = base_keys.get(key.as_slice()) {
                        keys.insert(key, source.clone());
                    }
                }
            }
            (HomogeneousPathTrie::Map(out), keys)
        },
        _ => return Err(()),
    };
    Ok(homogeneous_lit_from_trie_and_keys(&trie, &keys))
}

pub(crate) fn pathmap_subtract(left: &ProcPathMap, right: &ProcPathMap) -> Result<ProcPathMap, ()> {
    let (left_trie, left_keys) = encoded(left)?;
    let (right_trie, _) = encoded(right)?;
    let (trie, keys) = match (left_trie, right_trie) {
        (HomogeneousPathTrie::Empty, _) => (HomogeneousPathTrie::Empty, HashMap::new()),
        (left, HomogeneousPathTrie::Empty) => (left, left_keys),
        (HomogeneousPathTrie::Set(left), HomogeneousPathTrie::Set(right)) => {
            let mut out = PathMap::new();
            let mut keys = HashMap::new();
            for (key, ()) in left.iter() {
                if right.get(&key).is_none() {
                    out.insert(&key, ());
                    if let Some(source) = left_keys.get(key.as_slice()) {
                        keys.insert(key, source.clone());
                    }
                }
            }
            (HomogeneousPathTrie::Set(out), keys)
        },
        (HomogeneousPathTrie::Map(left), HomogeneousPathTrie::Map(right)) => {
            let mut out = PathMap::new();
            let mut keys = HashMap::new();
            for (key, value) in left.iter() {
                if right.get(&key).is_none() {
                    out.insert(&key, value.clone());
                    if let Some(source) = left_keys.get(key.as_slice()) {
                        keys.insert(key, source.clone());
                    }
                }
            }
            (HomogeneousPathTrie::Map(out), keys)
        },
        _ => return Err(()),
    };
    Ok(homogeneous_lit_from_trie_and_keys(&trie, &keys))
}

pub(crate) fn pathmap_meet(left: &ProcPathMap, right: &ProcPathMap) -> Result<ProcPathMap, ()> {
    let (left_trie, left_keys) = encoded(left)?;
    let (right_trie, right_keys) = encoded(right)?;
    let (trie, keys) = match (left_trie, right_trie) {
        (HomogeneousPathTrie::Empty, _) | (_, HomogeneousPathTrie::Empty) => {
            (HomogeneousPathTrie::Empty, HashMap::new())
        },
        (HomogeneousPathTrie::Set(left), HomogeneousPathTrie::Set(right)) => {
            let mut out = PathMap::new();
            let mut keys = HashMap::new();
            for (key, ()) in left.iter() {
                if right.get(&key).is_some() {
                    out.insert(&key, ());
                    if let Some(source) = left_keys.get(key.as_slice()) {
                        keys.insert(key, source.clone());
                    }
                }
            }
            (HomogeneousPathTrie::Set(out), keys)
        },
        (HomogeneousPathTrie::Map(left), HomogeneousPathTrie::Map(right)) => {
            let mut out = PathMap::new();
            let mut keys = HashMap::new();
            for (key, value) in right.iter() {
                if left.get(&key).is_some() {
                    out.insert(&key, value.clone());
                    if let Some(source) = right_keys.get(key.as_slice()) {
                        keys.insert(key, source.clone());
                    }
                }
            }
            (HomogeneousPathTrie::Map(out), keys)
        },
        _ => return Err(()),
    };
    Ok(homogeneous_lit_from_trie_and_keys(&trie, &keys))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn encode_proc_path_entry_rejects_empty_list() {
        let empty = Proc::CastList(std::sync::Arc::new(List::ListLit(vec![])));
        assert!(encode_proc_path_entry(&empty).is_err());
    }
}
