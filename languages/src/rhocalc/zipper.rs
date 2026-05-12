//! PathMap zipper support backed by the `pathmap` crate (`PathMap::read_zipper` / `write_zipper`).
//! Rhocalc uses prefix functions; see plan: Rholang PathMap Zipper Parity.

use std::fmt;
use std::hash::{Hash, Hasher};

use mettail_runtime::{flatten_segments, unflatten_segments, BoundTerm, PathMapLit, Var};
use moniker::{OnBoundFn, OnFreeFn, ScopeState};
use pathmap::alloc::GlobalAlloc;
use pathmap::zipper::{
    Zipper, ZipperAbsolutePath, ZipperMoving, ZipperSubtries, ZipperValues, ZipperWriting,
};
use pathmap::PathMap;

use super::{encode_proc_path_entry, Int, List, Proc, Str};

/// Immutable read zipper: underlying literal plus absolute encoded focus path from trie root.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct ReadZipperLit(pub PathMapLit<Proc, Proc>, pub Vec<u8>);

/// Write zipper token: literal plus encoded prefix where `write_zipper_at_path` is rooted.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct WriteZipperLit(pub PathMapLit<Proc, Proc>, pub Vec<u8>);

impl<N> BoundTerm<N> for ReadZipperLit
where
    N: Clone + PartialEq,
    Proc: BoundTerm<N>,
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

impl<N> BoundTerm<N> for WriteZipperLit
where
    N: Clone + PartialEq,
    Proc: BoundTerm<N>,
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

impl fmt::Display for ReadZipperLit {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "readZipper@{}", self.1.len())
    }
}

impl fmt::Display for WriteZipperLit {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "writeZipper@{}", self.1.len())
    }
}

fn pathmap_from_lit(lit: &PathMapLit<Proc, Proc>) -> Result<PathMap<Proc, GlobalAlloc>, ()> {
    mettail_runtime::trie_from_lit(lit, encode_proc_path_entry)
}

fn proc_key_from_path_bytes(bytes: &[u8]) -> Result<Proc, ()> {
    let segs = unflatten_segments(bytes);
    if segs.is_empty() {
        return Err(());
    }
    if segs.len() == 1 {
        let st = String::from_utf8(segs[0].clone()).map_err(|_| ())?;
        return Proc::parse(&st).map_err(|_| ());
    }
    let mut items = Vec::with_capacity(segs.len());
    for s in segs {
        let st = String::from_utf8(s).map_err(|_| ())?;
        items.push(Proc::parse(&st).map_err(|_| ())?);
    }
    Ok(Proc::CastList(Box::new(List::ListLit(items))))
}

pub(crate) fn pathmap_lit_from_pathmap(pm: &PathMap<Proc, GlobalAlloc>) -> Result<PathMapLit<Proc, Proc>, ()> {
    let mut lit = PathMapLit::new();
    for (kb, v) in pm.iter() {
        let k = proc_key_from_path_bytes(&kb)?;
        lit.insert(k, v.clone());
    }
    Ok(lit)
}

fn concat_path_keys(prefix: &[u8], rel: &[u8]) -> Result<Vec<u8>, ()> {
    let mut a = unflatten_segments(prefix);
    let b = unflatten_segments(rel);
    a.extend(b);
    Ok(flatten_segments(&a))
}

pub(crate) fn read_zipper_root(lit: &PathMapLit<Proc, Proc>) -> Result<ReadZipperLit, ()> {
    let _ = pathmap_from_lit(lit)?;
    Ok(ReadZipperLit(lit.clone(), Vec::new()))
}

pub(crate) fn read_zipper_at(lit: &PathMapLit<Proc, Proc>, path: &Proc) -> Result<ReadZipperLit, ()> {
    let _ = pathmap_from_lit(lit)?;
    let enc = encode_proc_path_entry(path)?;
    Ok(ReadZipperLit(lit.clone(), enc))
}

pub(crate) fn write_zipper_root(lit: &PathMapLit<Proc, Proc>) -> Result<WriteZipperLit, ()> {
    let _ = pathmap_from_lit(lit)?;
    Ok(WriteZipperLit(lit.clone(), Vec::new()))
}

pub(crate) fn write_zipper_at(lit: &PathMapLit<Proc, Proc>, path: &Proc) -> Result<WriteZipperLit, ()> {
    let _ = pathmap_from_lit(lit)?;
    let enc = encode_proc_path_entry(path)?;
    Ok(WriteZipperLit(lit.clone(), enc))
}

pub(crate) fn path_get_subtrie(lit: &PathMapLit<Proc, Proc>) -> Result<PathMapLit<Proc, Proc>, ()> {
    path_get_subtrie_at_bytes(lit, &[])
}

fn path_get_subtrie_at_bytes(lit: &PathMapLit<Proc, Proc>, focus: &[u8]) -> Result<PathMapLit<Proc, Proc>, ()> {
    let pm = pathmap_from_lit(lit)?;
    let z = pm.read_zipper_at_path(focus);
    match z.make_map() {
        None => Ok(PathMapLit::new()),
        Some(sub) => pathmap_lit_from_pathmap(&sub),
    }
}

pub(crate) fn path_get_subtrie_at(lit: &PathMapLit<Proc, Proc>, path: &Proc) -> Result<PathMapLit<Proc, Proc>, ()> {
    let enc = encode_proc_path_entry(path)?;
    path_get_subtrie_at_bytes(lit, &enc)
}

pub(crate) fn zipper_get_subtrie(z: &ReadZipperLit) -> Result<PathMapLit<Proc, Proc>, ()> {
    path_get_subtrie_at_bytes(&z.0, &z.1)
}

pub(crate) fn zipper_get_leaf(z: &ReadZipperLit) -> Result<Proc, ()> {
    let pm = pathmap_from_lit(&z.0)?;
    pm.get_val_at(&z.1).cloned().ok_or(())
}

pub(crate) fn zipper_descend_to(z: &ReadZipperLit, rel: &Proc) -> Result<ReadZipperLit, ()> {
    let pm = pathmap_from_lit(&z.0)?;
    let rel_enc = encode_proc_path_entry(rel)?;
    let mut rz = pm.read_zipper();
    rz.move_to_path(&z.1);
    rz.descend_to(rel_enc);
    Ok(ReadZipperLit(z.0.clone(), rz.origin_path().to_vec()))
}

pub(crate) fn zipper_child_count(z: &ReadZipperLit) -> Result<i64, ()> {
    let pm = pathmap_from_lit(&z.0)?;
    let rz = pm.read_zipper_at_path(&z.1);
    Ok(rz.child_count() as i64)
}

pub(crate) fn zipper_descend_first(z: &ReadZipperLit) -> Result<ReadZipperLit, ()> {
    let pm = pathmap_from_lit(&z.0)?;
    let mut rz = pm.read_zipper_at_path(&z.1);
    if !rz.descend_first_byte() {
        return Err(());
    }
    Ok(ReadZipperLit(z.0.clone(), rz.origin_path().to_vec()))
}

pub(crate) fn zipper_to_next_sibling(z: &ReadZipperLit) -> Result<ReadZipperLit, ()> {
    let pm = pathmap_from_lit(&z.0)?;
    let mut rz = pm.read_zipper_at_path(&z.1);
    if !rz.to_next_sibling_byte() {
        return Err(());
    }
    Ok(ReadZipperLit(z.0.clone(), rz.origin_path().to_vec()))
}

pub(crate) fn zipper_to_prev_sibling(z: &ReadZipperLit) -> Result<ReadZipperLit, ()> {
    let pm = pathmap_from_lit(&z.0)?;
    let mut rz = pm.read_zipper_at_path(&z.1);
    if !rz.to_prev_sibling_byte() {
        return Err(());
    }
    Ok(ReadZipperLit(z.0.clone(), rz.origin_path().to_vec()))
}

pub(crate) fn zipper_descend_indexed_branch(z: &ReadZipperLit, idx: i64) -> Result<ReadZipperLit, ()> {
    if idx < 0 {
        return Err(());
    }
    let idx = idx as usize;
    let pm = pathmap_from_lit(&z.0)?;
    let mut rz = pm.read_zipper_at_path(&z.1);
    if !rz.descend_indexed_byte(idx) {
        return Err(());
    }
    Ok(ReadZipperLit(z.0.clone(), rz.origin_path().to_vec()))
}

pub(crate) fn zipper_ascend_one(z: &ReadZipperLit) -> Result<ReadZipperLit, ()> {
    zipper_ascend(z, 1)
}

pub(crate) fn zipper_ascend(z: &ReadZipperLit, steps: i64) -> Result<ReadZipperLit, ()> {
    if steps < 0 {
        return Err(());
    }
    let steps = steps as usize;
    let pm = pathmap_from_lit(&z.0)?;
    let mut rz = pm.read_zipper_at_path(&z.1);
    if !rz.ascend(steps) {
        return Err(());
    }
    Ok(ReadZipperLit(z.0.clone(), rz.origin_path().to_vec()))
}

pub(crate) fn write_zipper_set_leaf(
    w: &WriteZipperLit,
    full_path: &Proc,
    val: &Proc,
) -> Result<PathMapLit<Proc, Proc>, ()> {
    let mut pm = pathmap_from_lit(&w.0)?;
    let enc = encode_proc_path_entry(full_path)?;
    pm.set_val_at(enc, val.clone());
    pathmap_lit_from_pathmap(&pm)
}

pub(crate) fn write_zipper_set_subtrie(
    w: &WriteZipperLit,
    rel_lit: &PathMapLit<Proc, Proc>,
) -> Result<PathMapLit<Proc, Proc>, ()> {
    let mut pm = pathmap_from_lit(&w.0)?;
    let rel_pm = pathmap_from_lit(rel_lit)?;
    {
        let mut wz = pm.write_zipper_at_path(&w.1);
        wz.graft_map(rel_pm);
    }
    pathmap_lit_from_pathmap(&pm)
}

pub(crate) fn write_zipper_remove_leaf(w: &WriteZipperLit) -> Result<PathMapLit<Proc, Proc>, ()> {
    let mut pm = pathmap_from_lit(&w.0)?;
    {
        let mut wz = pm.write_zipper_at_path(&w.1);
        wz.remove_val(true);
    }
    pathmap_lit_from_pathmap(&pm)
}

pub(crate) fn write_zipper_remove_branches(w: &WriteZipperLit) -> Result<PathMapLit<Proc, Proc>, ()> {
    let mut pm = pathmap_from_lit(&w.0)?;
    {
        let mut wz = pm.write_zipper_at_path(&w.1);
        wz.remove_branches(true);
    }
    pathmap_lit_from_pathmap(&pm)
}

pub(crate) fn write_zipper_graft(w: &WriteZipperLit, src: &ReadZipperLit) -> Result<PathMapLit<Proc, Proc>, ()> {
    let mut dest = pathmap_from_lit(&w.0)?;
    let src_pm = pathmap_from_lit(&src.0)?;
    let src_rz = src_pm.read_zipper_at_path(&src.1);
    {
        let mut wz = dest.write_zipper_at_path(&w.1);
        wz.graft(&src_rz);
    }
    pathmap_lit_from_pathmap(&dest)
}

/// Right-biased union of the source subtrie into the destination subtrie at `w`'s focus.
pub(crate) fn write_zipper_join_into(w: &WriteZipperLit, src: &ReadZipperLit) -> Result<PathMapLit<Proc, Proc>, ()> {
    let mut dest = pathmap_from_lit(&w.0)?;
    let src_pm = pathmap_from_lit(&src.0)?;
    let rz = src_pm.read_zipper_at_path(&src.1);
    if let Some(sub) = rz.make_map() {
        for (rel_bytes, v) in sub.iter() {
            let abs = concat_path_keys(&w.1, &rel_bytes)?;
            dest.set_val_at(abs, v.clone());
        }
    }
    pathmap_lit_from_pathmap(&dest)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lit_one(k: Proc, v: Proc) -> PathMapLit<Proc, Proc> {
        let mut lit = PathMapLit::new();
        lit.insert(k, v);
        lit
    }

    #[test]
    fn pathmap_roundtrip_bytes_keys() {
        let k = Proc::CastList(Box::new(List::ListLit(vec![
            Proc::CastStr(Box::new(Str::StringLit("a".into()))),
            Proc::CastStr(Box::new(Str::StringLit("b".into()))),
        ])));
        let lit = lit_one(k.clone(), Proc::CastInt(Box::new(Int::NumLit(1))));
        let pm = pathmap_from_lit(&lit).unwrap();
        let lit2 = pathmap_lit_from_pathmap(&pm).unwrap();
        assert_eq!(lit, lit2);
    }

    #[test]
    fn zipper_get_subtrie_prefix() {
        let mut lit = PathMapLit::new();
        let k1 = Proc::CastList(Box::new(List::ListLit(vec![
            Proc::CastStr(Box::new(Str::StringLit("users".into()))),
            Proc::CastStr(Box::new(Str::StringLit("alice".into()))),
        ])));
        let k2 = Proc::CastList(Box::new(List::ListLit(vec![
            Proc::CastStr(Box::new(Str::StringLit("users".into()))),
            Proc::CastStr(Box::new(Str::StringLit("bob".into()))),
        ])));
        lit.insert(k1, Proc::CastInt(Box::new(Int::NumLit(1))));
        lit.insert(k2, Proc::CastInt(Box::new(Int::NumLit(2))));
        let users = Proc::CastList(Box::new(List::ListLit(vec![Proc::CastStr(Box::new(
            Str::StringLit("users".into()),
        ))])));
        let sub = path_get_subtrie_at(&lit, &users).unwrap();
        assert_eq!(sub.len(), 2);
    }
}
