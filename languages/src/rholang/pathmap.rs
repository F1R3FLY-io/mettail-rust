//! Rholang `Proc` path encoding and trie-backed [`PathMapLit`] operations via
//! [`mettail_runtime::pathmap_bridge`].

use mettail_runtime::PathMapLit;

use super::{List, Proc};

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

pub(crate) fn pathmap_get(
    payload: &PathMapLit<Proc, Proc>,
    key: &Proc,
) -> Result<Option<Proc>, ()> {
    let enc = encode_proc_path_entry(key)?;
    let trie = mettail_runtime::trie_from_lit(payload, encode_proc_path_entry)?;
    Ok(trie.get_val_at(&enc).cloned())
}

pub(crate) fn pathmap_has(payload: &PathMapLit<Proc, Proc>, key: &Proc) -> Result<bool, ()> {
    let enc = encode_proc_path_entry(key)?;
    let trie = mettail_runtime::trie_from_lit(payload, encode_proc_path_entry)?;
    Ok(trie.get_val_at(&enc).is_some())
}

pub(crate) fn pathmap_put(
    payload: &PathMapLit<Proc, Proc>,
    key: &Proc,
    value: &Proc,
) -> Result<PathMapLit<Proc, Proc>, ()> {
    let enc = encode_proc_path_entry(key)?;
    let (mut trie, mut key_index) =
        mettail_runtime::trie_and_key_index_from_lit(payload, encode_proc_path_entry)?;
    mettail_runtime::trie_put_encoded(&mut trie, &mut key_index, enc, key.clone(), value.clone());
    Ok(mettail_runtime::pathmap_lit_from_trie_and_keys(&trie, key_index))
}

pub(crate) fn pathmap_merge(
    left: &PathMapLit<Proc, Proc>,
    right: &PathMapLit<Proc, Proc>,
) -> Result<PathMapLit<Proc, Proc>, ()> {
    let (mut trie, mut key_index) =
        mettail_runtime::trie_and_key_index_from_lit(left, encode_proc_path_entry)?;
    mettail_runtime::trie_merge_lit(&mut trie, &mut key_index, right, encode_proc_path_entry)?;
    Ok(mettail_runtime::pathmap_lit_from_trie_and_keys(&trie, key_index))
}

pub(crate) fn pathmap_restrict(
    base: &PathMapLit<Proc, Proc>,
    mask: &PathMapLit<Proc, Proc>,
) -> Result<PathMapLit<Proc, Proc>, ()> {
    mettail_runtime::trie_restrict_lit(base, mask, encode_proc_path_entry)
}

pub(crate) fn pathmap_subtract(
    left: &PathMapLit<Proc, Proc>,
    right: &PathMapLit<Proc, Proc>,
) -> Result<PathMapLit<Proc, Proc>, ()> {
    mettail_runtime::trie_subtract_lit(left, right, encode_proc_path_entry)
}

pub(crate) fn pathmap_meet(
    left: &PathMapLit<Proc, Proc>,
    right: &PathMapLit<Proc, Proc>,
) -> Result<PathMapLit<Proc, Proc>, ()> {
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
