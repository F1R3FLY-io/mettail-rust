//! Rholang `Proc` path encoding and trie-backed [`PathMapLit`] operations via
//! [`mettail_runtime::pathmap_bridge`].

use mettail_runtime::{PathMapLit, PathValue};

use super::{List, Proc};

/// The rholang pathmap payload.
///
/// #74 (2026-07-29): the VALUE is a [`PathValue<Proc>`], not a `Proc`, because a
/// pathmap's value slot is optional — `{| k |}` binds `k` to NOTHING, and that is
/// a different term from `{| k : Nil |}`. The parser has known the slot was
/// optional since 2026-06-27 (`kv_value_optional` is a compile-time property of
/// `CollectionType::PathMap`); this alias is the type agreeing with it.
///
/// The trie bridge (`mettail_runtime::pathmap_bridge`) is generic in the value
/// type, so every operation below carries `PathValue` through without inspecting
/// it: a path operation moves values, it does not read them.
pub(crate) type ProcPathMap = PathMapLit<Proc, PathValue<Proc>>;

/// Path segments for trie keys. `None` when the path is not encodable (e.g. empty list path `[]`).
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

/// Look up `key`.
///
/// The three outcomes are genuinely three, and the caller must keep them apart
/// (#74):
///
/// | result | meaning |
/// |---|---|
/// | `Ok(None)` | the key is ABSENT |
/// | `Ok(Some(PathValue::Unset))` | the key is PRESENT and bound to nothing (`{\| k \|}`) |
/// | `Ok(Some(PathValue::Set(v)))` | the key is present and bound to `v` |
///
/// ⚠ Collapsing the middle row into either neighbour is the defect this campaign
/// removed: reporting it as `Ok(None)` claims the key is absent, and reporting it
/// as `Set(Nil)` fabricates a value the source never wrote.
pub(crate) fn pathmap_get(
    payload: &ProcPathMap,
    key: &Proc,
) -> Result<Option<PathValue<Proc>>, ()> {
    let enc = encode_proc_path_entry(key)?;
    let trie = mettail_runtime::trie_from_lit(payload, encode_proc_path_entry)?;
    Ok(trie.get_val_at(&enc).cloned())
}

pub(crate) fn pathmap_has(payload: &ProcPathMap, key: &Proc) -> Result<bool, ()> {
    let enc = encode_proc_path_entry(key)?;
    let trie = mettail_runtime::trie_from_lit(payload, encode_proc_path_entry)?;
    Ok(trie.get_val_at(&enc).is_some())
}

/// Bind `key` to `value`.
///
/// `value` is a [`PathValue`] rather than a `Proc` so the caller states which
/// binding it means: `.set(k, v)` supplies `PathValue::Set(v)`, while a
/// hypothetical "declare the key with no value" operation would supply
/// `PathValue::Unset`. Taking a bare `Proc` here and wrapping it internally would
/// make `Unset` unreachable through this door — and an unreachable case is how
/// #74 stayed invisible for as long as it did.
pub(crate) fn pathmap_put(
    payload: &ProcPathMap,
    key: &Proc,
    value: PathValue<Proc>,
) -> Result<ProcPathMap, ()> {
    let enc = encode_proc_path_entry(key)?;
    let (mut trie, mut key_index) =
        mettail_runtime::trie_and_key_index_from_lit(payload, encode_proc_path_entry)?;
    mettail_runtime::trie_put_encoded(&mut trie, &mut key_index, enc, key.clone(), value);
    Ok(mettail_runtime::pathmap_lit_from_trie_and_keys(&trie, key_index))
}

pub(crate) fn pathmap_merge(
    left: &ProcPathMap,
    right: &ProcPathMap,
) -> Result<ProcPathMap, ()> {
    let (mut trie, mut key_index) =
        mettail_runtime::trie_and_key_index_from_lit(left, encode_proc_path_entry)?;
    mettail_runtime::trie_merge_lit(&mut trie, &mut key_index, right, encode_proc_path_entry)?;
    Ok(mettail_runtime::pathmap_lit_from_trie_and_keys(&trie, key_index))
}

pub(crate) fn pathmap_restrict(
    base: &ProcPathMap,
    mask: &ProcPathMap,
) -> Result<ProcPathMap, ()> {
    mettail_runtime::trie_restrict_lit(base, mask, encode_proc_path_entry)
}

pub(crate) fn pathmap_subtract(
    left: &ProcPathMap,
    right: &ProcPathMap,
) -> Result<ProcPathMap, ()> {
    mettail_runtime::trie_subtract_lit(left, right, encode_proc_path_entry)
}

pub(crate) fn pathmap_meet(
    left: &ProcPathMap,
    right: &ProcPathMap,
) -> Result<ProcPathMap, ()> {
    mettail_runtime::trie_meet_lit(left, right, encode_proc_path_entry)
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
