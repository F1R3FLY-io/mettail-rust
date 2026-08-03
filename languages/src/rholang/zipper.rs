//! PathMap zipper support backed by the `pathmap` crate (`PathMap::read_zipper` / `write_zipper`).
//! Rholang uses prefix functions; see plan: Rholang PathMap Zipper Parity.

use std::fmt;
use std::hash::{Hash, Hasher};

use mettail_runtime::{
    flatten_segments, homogeneous_trie_and_key_index, unflatten_segments, BoundTerm,
    HomogeneousPathTrie, PathMapLit, Var,
};
use moniker::{OnBoundFn, OnFreeFn, ScopeState};
use pathmap::alloc::GlobalAlloc;
use pathmap::zipper::{
    Zipper, ZipperAbsolutePath, ZipperIteration, ZipperMoving, ZipperSubtries, ZipperValues,
    ZipperWriting,
};
use pathmap::PathMap;

use super::pathmap::{encode_proc_path_entry, ProcPathMap};
use super::{BigInt, Int, List, Proc, Str};

/// Extract a signed integer index/count from a rholang `Proc` that wraps an
/// integer literal.
///
/// Rholang bare integer literals lex to `BigInt` (the Rholang 1.4
/// arbitrary-precision default), arriving as `Proc::CastBigInt(NumLit)`. The
/// zipper index/step ops (`ascend`, `descendIndexedBranch`) were merge-added
/// from `main`, whose integer literals were the fixed-width `Proc::CastInt`.
/// Accepting BOTH forms here is what lets the merged grammar reduce those ops
/// instead of collapsing to `Proc::Err`. A `BigInt` outside the `i64` range
/// yields `None` (the caller then produces `Proc::Err`, which every zipper op
/// already treats as "operation not applicable"), so out-of-range indices fail
/// closed rather than wrapping.
pub(crate) fn proc_to_index(p: &Proc) -> Option<i64> {
    match p {
        Proc::CastInt(inner) => match inner.as_ref() {
            Int::NumLit(n) => Some(*n),
            _ => None,
        },
        Proc::CastBigInt(inner) => match inner.as_ref() {
            BigInt::NumLit(n) => num_traits::ToPrimitive::to_i64(n.get()),
            _ => None,
        },
        _ => None,
    }
}

/// Immutable read zipper: underlying literal plus absolute encoded focus path from trie root.
#[derive(Clone, Debug, Default, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct ReadZipperLit(pub ProcPathMap, pub Vec<u8>);

/// Write zipper token: literal plus encoded prefix where `write_zipper_at_path` is rooted.
#[derive(Clone, Debug, Default, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct WriteZipperLit(pub ProcPathMap, pub Vec<u8>);

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

fn pathmap_from_lit(lit: &ProcPathMap) -> Result<HomogeneousPathTrie<Proc>, ()> {
    homogeneous_trie_and_key_index(lit, encode_proc_path_entry).map(|(trie, _)| trie)
}

macro_rules! with_pathmap {
    ($lit:expr, |$pm:ident| $body:block) => {{
        match pathmap_from_lit($lit)? {
            HomogeneousPathTrie::Empty => {
                let $pm = PathMap::<(), GlobalAlloc>::new();
                $body
            },
            HomogeneousPathTrie::Set($pm) => $body,
            HomogeneousPathTrie::Map($pm) => $body,
        }
    }};
}

/// Build a read zipper rooted at the trie ROOT and move its focus to `path`.
///
/// Upward navigation (`ascend`, and any op that must reach the focus's PARENT)
/// requires the trie above the focus to remain reachable.
/// `PathMap::read_zipper_at_path(path)` builds the zipper directly on the node
/// at `path` with an EMPTY ancestor stack, so once `ascend` exhausts the key it
/// already holds it finds nothing to pop and returns `false` — the merge-added
/// `RZAscend` / `RZDescendIndexedBranch` folds collapsed to `Proc::Err` under
/// that rooting. Rooting at the trie root and moving the focus via
/// `move_to_path` keeps the full path above the focus climbable, and
/// `origin_path()` still reports the ABSOLUTE path, so the resulting
/// `ReadZipperLit` carries a correct absolute focus. Descent-only ops
/// (`descendFirst`, `descendIndexedBranch`, `descendTo`) are also correct under
/// this rooting because they never move above the focus, and they return
/// absolute origin paths for free.
///
/// ## ⚠ Correction (2026-07-26, measured): SIBLING moves are NOT affected
///
/// An earlier revision of this comment also claimed that under
/// `read_zipper_at_path` "sibling moves see no parent" and that
/// `RZToNext/PrevSibling` collapsed to `Proc::Err`. That is **wrong**, and
/// `zipper_to_next_sibling` / `zipper_to_prev_sibling` accordingly still use
/// `read_zipper_at_path` and are CORRECT as they stand.
///
/// The trait-default `to_next_sibling_byte` does read `path().last()`, which
/// would indeed be empty under a rerooting — but `ReadZipperCore` OVERRIDES it
/// (`pathmap/src/zipper.rs:2269`) with a native implementation that tests
/// `prefix_buf` instead, and `read_zipper_at_path` passes `root_key_start = 0`
/// so `path()` returns the FULL absolute path rather than an empty one. Only
/// the ancestor STACK is truncated by the rerooting, which is why ascent — and
/// nothing else — is impaired.
///
/// Measured, and pinned by `rerooting_bounds_ascent_but_not_sibling_moves`:
/// from a focus reached by `descendFirst` (byte `[49]`), `toNextSibling`
/// yields `[50]`; from the leaf `[1,2,3]` (`[49,255,50,255,51,255]`) it yields
/// `Err` — which is the CORRECT answer, because that leaf's parent has exactly
/// one child. The brief that reported "toNextSibling is broken" had observed
/// only the second case.
fn zipper_relative_read_zipper<'a, V: Clone + Send + Sync + Unpin>(
    pm: &'a PathMap<V, GlobalAlloc>,
    path: &[u8],
) -> impl Zipper
       + ZipperMoving
       + ZipperIteration
       + ZipperValues<V>
       + ZipperAbsolutePath
       + ZipperSubtries<V, GlobalAlloc>
       + 'a {
    let mut rz = pm.read_zipper();
    rz.move_to_path(path);
    rz
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
    Ok(Proc::CastList(std::sync::Arc::new(List::ListLit(items))))
}

// ═══════════════════════════════════════════════════════════════════════════
// Trie ENUMERATION: the cursor-key readout and the leaf walk
// ═══════════════════════════════════════════════════════════════════════════
//
// These three functions make enumeration of a `Pathmap` TOTAL — descend to a
// leaf, read its key and its value, advance to the next leaf, and know in
// advance how many leaves there are. They surface capability that the
// underlying `pathmap` crate ALREADY has; nothing here is new machinery:
//
//   `getPath()`   ▸ `ZipperMoving::path()`        (pathmap/src/zipper.rs:144)
//   `toNextLeaf()`▸ `ZipperIteration::to_next_val()`            (…:546)
//   `leafCount()` ▸ `ZipperMoving::val_count()`                 (…:150)
//
// ## Why a LEAF-granular walk, and not `descendFirst`/`toNextSibling`
//
// A rholang `Pathmap` key is a LIST of segments, and `flatten_segments`
// encodes it as `seg₀ 0xFF seg₁ 0xFF …` — so a key occupies MANY trie bytes.
// Every pre-existing move (`descendFirst`, `toNextSibling`, `toPrevSibling`,
// `descendIndexedBranch`, `ascend`) moves by ONE BYTE, which parks the focus
// mid-segment, where:
//
//   * `getLeaf()` is stuck — a mid-segment position holds no value; and
//   * `getSubtrie()` FAILS — the relative keys below a mid-segment focus begin
//     with a partial segment, which no `Proc` can name.
//
// and, decisively, Rholang surface syntax cannot ADDRESS a byte: `descendTo`
// takes a `Proc` and always encodes a whole segment. So the byte-granular
// moves cannot be composed into an enumeration from Rholang source at all, no
// matter what accessor is added beside them. `to_next_val()` sidesteps the
// granularity mismatch entirely by landing ONLY on positions that carry a
// value — every such position is a complete, segment-aligned, decodable key.
//
// (f1r3node's `EZipper` is segment-granular — `repeated bytes current_path`,
// `RhoTypes.proto:352` — so it does not have this mismatch. mettail's
// byte-granular `ReadZipperLit.1` is the divergent representation.)

/// Decode an encoded trie key back into the rholang `Proc` LIST of its path
/// segments — the cursor-key readout behind `getPath()`.
///
/// ## Why this is a LIST unconditionally, unlike [`proc_key_from_path_bytes`]
///
/// [`proc_key_from_path_bytes`] reconstructs a key in the shape a `Pathmap`
/// LITERAL displays it: a one-segment key comes back BARE (`1`, never `[1]`)
/// so that `{|1:…|}` round-trips to itself. `getPath()` carries the opposite
/// obligation — a cursor key is a *trace*, a SEQUENCE of choices, and its
/// consumer indexes it (`p.nth(i)`, `p.length()`). A bare one-segment result
/// would leave `p.length()` undefined on exactly the singleton traces, so the
/// list shape here is unconditional.
///
/// This costs nothing in key IDENTITY. `encode_proc_path_entry` sends a bare
/// `Proc` and the one-element `List` containing it to the SAME bytes (each is
/// one segment), so `m.get(z.getPath())` addresses the very entry `z` is
/// focused on at every arity; the two decoders differ in display shape only.
pub(crate) fn proc_path_list_from_path_bytes(bytes: &[u8]) -> Result<Proc, ()> {
    let segs = unflatten_segments(bytes);
    if segs.is_empty() {
        return Err(());
    }
    let mut items = Vec::with_capacity(segs.len());
    for seg in segs {
        let text = String::from_utf8(seg).map_err(|_| ())?;
        items.push(Proc::parse(&text).map_err(|_| ())?);
    }
    Ok(Proc::CastList(std::sync::Arc::new(List::ListLit(items))))
}

/// `z.getPath()` — THE CURSOR KEY: the zipper's focus path, as the list of its
/// segments. Surfaces [`pathmap::zipper::ZipperMoving::path`].
///
/// The literal is NOT re-validated here. Every `ReadZipperLit` is built by
/// [`read_zipper_root`] or [`read_zipper_at`], both of which already reject an
/// un-encodable literal, so "the literal is encodable" holds by construction
/// at every zipper; rebuilding the whole trie (an O(map) walk) to read back a
/// byte string already stored in the zipper would buy no information.
///
/// Errors only for the empty focus path (the trie root, which names no entry —
/// see [`read_zipper_root`]: `{|…|}.readZipper().getPath()` has no key to
/// report, because rholang cannot construct a root-valued `Pathmap` at all;
/// `encode_proc_path_entry` rejects the empty-list key).
pub(crate) fn zipper_get_path(z: &ReadZipperLit) -> Result<Proc, ()> {
    proc_path_list_from_path_bytes(&z.1)
}

/// `z.toNextLeaf()` — advance the focus, in depth-first order, to the next
/// path that CARRIES A VALUE. Surfaces
/// [`pathmap::zipper::ZipperIteration::to_next_val`].
///
/// This is the enumeration primitive: from `m.readZipper()` (focus at the trie
/// root) the first call lands on the FIRST leaf, and each subsequent call
/// advances by exactly one leaf, so
///
/// ```text
///     z ← m.readZipper() ;  n ← z.leafCount() ;  n × ( z ← z.toNextLeaf() )
/// ```
///
/// visits every entry of `m` exactly once. Because the focus after every
/// successful call is a value-bearing, segment-aligned position, the
/// accompanying `z.getPath()` and `z.getLeaf()` are BOTH guaranteed to reduce
/// — which is why no separate "is there a value here?" predicate is needed.
///
/// ## ⚠ EXHAUSTION MUST ERROR — returning a zipper here is an INFINITE LOOP
///
/// This is the single most important invariant of this function, and it is not
/// obvious from its signature.
///
/// `to_next_val()` does not merely return `false` when the walk is finished —
/// it also **RESETS THE ZIPPER TO THE ROOT** (`pathmap/src/zipper.rs:546`; the
/// ascending arm climbs until `at_root()` and only then reports `false`). So
/// the zipper handed back on exhaustion is a *perfectly valid root zipper*. If
/// this function returned it, the counted walk would not fail, would not error,
/// and would not stop — it would **silently restart from the first leaf and run
/// forever**, with nothing anywhere reporting a fault.
///
/// Exhaustion is therefore reported as `Err`, which the fold body renders as
/// the house "failed navigation stays STUCK" form (user decision 2026-06-30;
/// see `RZGetLeaf` / `RZDescendFirst`). A stuck term is not a decidable
/// end-test, so [`zipper_leaf_count`] is what bounds the loop.
///
/// ★ The reducer reports the same condition as **`Nil`**, not as a stuck term.
/// C1 must translate. See the CROSS-ENDPOINT CONTRACT block in this module's
/// tests and its f1r3node twin
/// (`rholang/tests/zipper_enumeration_spec.rs::to_next_leaf_returns_nil_when_exhausted`).
///
/// ## Scope: the walk is trie-GLOBAL, the count is subtrie-LOCAL
///
/// The walk is rooted at the trie root, so it does not stop at the end of the
/// subtrie the focus happens to sit in. That is deliberate: scoping an
/// enumeration is already served ALGEBRAICALLY and better — `m.getSubtrieAt(p)`
/// yields a `Pathmap` of just that branch, whose `readZipper()` then walks
/// exactly it. Confining the walk instead would require `ReadZipperLit` to
/// carry a second path (its walk root), changing a `Hash`/`Ord`/`BoundTerm`
/// representation for a capability the algebra already provides.
///
/// Composing them is still sound without `getSubtrieAt`, because keys sharing
/// a prefix occupy a CONTIGUOUS run of the depth-first order: starting from a
/// focus at a strict prefix `p`, the first `z.leafCount()` calls land exactly
/// on the subtrie of `p`. The one edge is a focus that is ITSELF a leaf — it
/// is counted by `leafCount()` but `toNextLeaf()` starts *after* it.
pub(crate) fn zipper_to_next_leaf(z: &ReadZipperLit) -> Result<ReadZipperLit, ()> {
    let path = with_pathmap!(&z.0, |pm| {
        // Rooted at the trie root so iteration can ascend out of the current
        // branch and `origin_path` remains absolute.
        let mut rz = zipper_relative_read_zipper(&pm, &z.1);
        if !rz.to_next_val() {
            return Err(());
        }
        rz.origin_path().to_vec()
    });
    Ok(ReadZipperLit(z.0.clone(), path))
}

/// `z.leafCount()` — how many values lie AT AND BELOW the focus. Surfaces
/// [`pathmap::zipper::ZipperMoving::val_count`].
///
/// On a root zipper this is the entry count of the whole `Pathmap` (the
/// cardinality answer), and it is the DECIDABLE BOUND that terminates a
/// [`zipper_to_next_leaf`] walk. On a zipper at a prefix it answers "how many
/// results are under this branch?" directly from the trie.
///
/// Cost: `val_count()` is documented O(subtrie) upstream, so this is meant to
/// be read ONCE, before a walk, not per step. (On this code path every zipper
/// op already pays an O(map) `pathmap_from_lit` rebuild, so it adds no
/// asymptotic cost here — but it does on a runtime that holds a live trie.)
///
/// Rerooted at the focus on purpose: `val_count()` must see the focus as its
/// root so that the count is the SUBTRIE's, not the whole trie's.
pub(crate) fn zipper_leaf_count(z: &ReadZipperLit) -> Result<i64, ()> {
    Ok(with_pathmap!(&z.0, |pm| { pm.read_zipper_at_path(&z.1).val_count() as i64 }))
}

fn set_lit_from_pathmap(pm: &PathMap<(), GlobalAlloc>) -> Result<ProcPathMap, ()> {
    let mut lit = PathMapLit::new();
    for (kb, ()) in pm.iter() {
        let k = proc_key_from_path_bytes(&kb)?;
        lit.insert_set(k).map_err(|_| ())?;
    }
    Ok(lit)
}

fn map_lit_from_pathmap(pm: &PathMap<Proc, GlobalAlloc>) -> Result<ProcPathMap, ()> {
    let mut lit = PathMapLit::new();
    for (kb, value) in pm.iter() {
        let k = proc_key_from_path_bytes(&kb)?;
        lit.insert_map(k, value.clone()).map_err(|_| ())?;
    }
    Ok(lit)
}

fn concat_path_keys(prefix: &[u8], rel: &[u8]) -> Result<Vec<u8>, ()> {
    let mut a = unflatten_segments(prefix);
    let b = unflatten_segments(rel);
    a.extend(b);
    Ok(flatten_segments(&a))
}

pub(crate) fn read_zipper_root(lit: &ProcPathMap) -> Result<ReadZipperLit, ()> {
    pathmap_from_lit(lit)?;
    Ok(ReadZipperLit(lit.clone(), Vec::new()))
}

pub(crate) fn read_zipper_at(lit: &ProcPathMap, path: &Proc) -> Result<ReadZipperLit, ()> {
    pathmap_from_lit(lit)?;
    let enc = encode_proc_path_entry(path)?;
    Ok(ReadZipperLit(lit.clone(), enc))
}

pub(crate) fn write_zipper_root(lit: &ProcPathMap) -> Result<WriteZipperLit, ()> {
    pathmap_from_lit(lit)?;
    Ok(WriteZipperLit(lit.clone(), Vec::new()))
}

pub(crate) fn write_zipper_at(lit: &ProcPathMap, path: &Proc) -> Result<WriteZipperLit, ()> {
    pathmap_from_lit(lit)?;
    let enc = encode_proc_path_entry(path)?;
    Ok(WriteZipperLit(lit.clone(), enc))
}

pub(crate) fn path_get_subtrie(lit: &ProcPathMap) -> Result<ProcPathMap, ()> {
    path_get_subtrie_at_bytes(lit, &[])
}

fn path_get_subtrie_at_bytes(lit: &ProcPathMap, focus: &[u8]) -> Result<ProcPathMap, ()> {
    match pathmap_from_lit(lit)? {
        HomogeneousPathTrie::Empty => Ok(PathMapLit::new()),
        HomogeneousPathTrie::Set(pm) => match pm.read_zipper_at_path(focus).make_map() {
            None => Ok(PathMapLit::new()),
            Some(sub) => set_lit_from_pathmap(&sub),
        },
        HomogeneousPathTrie::Map(pm) => match pm.read_zipper_at_path(focus).make_map() {
            None => Ok(PathMapLit::new()),
            Some(sub) => map_lit_from_pathmap(&sub),
        },
    }
}

pub(crate) fn path_get_subtrie_at(lit: &ProcPathMap, path: &Proc) -> Result<ProcPathMap, ()> {
    let enc = encode_proc_path_entry(path)?;
    path_get_subtrie_at_bytes(lit, &enc)
}

pub(crate) fn zipper_get_subtrie(z: &ReadZipperLit) -> Result<ProcPathMap, ()> {
    path_get_subtrie_at_bytes(&z.0, &z.1)
}

/// The homogeneous leaf state at the zipper's focus.
pub(crate) enum ZipperLeaf {
    SetMember,
    MapValue(Proc),
}

pub(crate) fn zipper_get_leaf(z: &ReadZipperLit) -> Result<ZipperLeaf, ()> {
    match pathmap_from_lit(&z.0)? {
        HomogeneousPathTrie::Empty => Err(()),
        HomogeneousPathTrie::Set(pm) => pm
            .get_val_at(&z.1)
            .map(|()| ZipperLeaf::SetMember)
            .ok_or(()),
        HomogeneousPathTrie::Map(pm) => pm
            .get_val_at(&z.1)
            .cloned()
            .map(ZipperLeaf::MapValue)
            .ok_or(()),
    }
}

pub(crate) fn zipper_descend_to(z: &ReadZipperLit, rel: &Proc) -> Result<ReadZipperLit, ()> {
    let rel_enc = encode_proc_path_entry(rel)?;
    let path = with_pathmap!(&z.0, |pm| {
        let mut rz = pm.read_zipper();
        rz.move_to_path(&z.1);
        rz.descend_to(&rel_enc);
        rz.origin_path().to_vec()
    });
    Ok(ReadZipperLit(z.0.clone(), path))
}

pub(crate) fn zipper_child_count(z: &ReadZipperLit) -> Result<i64, ()> {
    Ok(with_pathmap!(&z.0, |pm| { pm.read_zipper_at_path(&z.1).child_count() as i64 }))
}

pub(crate) fn zipper_descend_first(z: &ReadZipperLit) -> Result<ReadZipperLit, ()> {
    let path = with_pathmap!(&z.0, |pm| {
        let mut rz = pm.read_zipper_at_path(&z.1);
        if !rz.descend_first_byte() {
            return Err(());
        }
        rz.origin_path().to_vec()
    });
    Ok(ReadZipperLit(z.0.clone(), path))
}

pub(crate) fn zipper_to_next_sibling(z: &ReadZipperLit) -> Result<ReadZipperLit, ()> {
    let path = with_pathmap!(&z.0, |pm| {
        let mut rz = pm.read_zipper_at_path(&z.1);
        if !rz.to_next_sibling_byte() {
            return Err(());
        }
        rz.origin_path().to_vec()
    });
    Ok(ReadZipperLit(z.0.clone(), path))
}

pub(crate) fn zipper_to_prev_sibling(z: &ReadZipperLit) -> Result<ReadZipperLit, ()> {
    let path = with_pathmap!(&z.0, |pm| {
        let mut rz = pm.read_zipper_at_path(&z.1);
        if !rz.to_prev_sibling_byte() {
            return Err(());
        }
        rz.origin_path().to_vec()
    });
    Ok(ReadZipperLit(z.0.clone(), path))
}

pub(crate) fn zipper_descend_indexed_branch(
    z: &ReadZipperLit,
    idx: i64,
) -> Result<ReadZipperLit, ()> {
    if idx < 0 {
        return Err(());
    }
    let idx = idx as usize;
    let path = with_pathmap!(&z.0, |pm| {
        let mut rz = zipper_relative_read_zipper(&pm, &z.1);
        if !rz.descend_indexed_byte(idx) {
            return Err(());
        }
        rz.origin_path().to_vec()
    });
    Ok(ReadZipperLit(z.0.clone(), path))
}

pub(crate) fn zipper_ascend_one(z: &ReadZipperLit) -> Result<ReadZipperLit, ()> {
    zipper_ascend(z, 1)
}

pub(crate) fn zipper_ascend(z: &ReadZipperLit, steps: i64) -> Result<ReadZipperLit, ()> {
    if steps < 0 {
        return Err(());
    }
    let steps = steps as usize;
    let path = with_pathmap!(&z.0, |pm| {
        let mut rz = zipper_relative_read_zipper(&pm, &z.1);
        if !rz.ascend(steps) {
            return Err(());
        }
        rz.origin_path().to_vec()
    });
    Ok(ReadZipperLit(z.0.clone(), path))
}

/// Bind the leaf at `full_path` to `val`. Empty selects map mode; set mode is
/// rejected so a zipper cannot manufacture mixed membership.
pub(crate) fn write_zipper_set_leaf(
    w: &WriteZipperLit,
    full_path: &Proc,
    val: Proc,
) -> Result<ProcPathMap, ()> {
    let enc = encode_proc_path_entry(full_path)?;
    let mut pm = match pathmap_from_lit(&w.0)? {
        HomogeneousPathTrie::Empty => PathMap::new(),
        HomogeneousPathTrie::Set(_) => return Err(()),
        HomogeneousPathTrie::Map(pm) => pm,
    };
    pm.set_val_at(enc, val);
    map_lit_from_pathmap(&pm)
}

fn replace_subtrie<V: Clone + Send + Sync + Unpin>(
    mut dest: PathMap<V, GlobalAlloc>,
    focus: &[u8],
    replacement: PathMap<V, GlobalAlloc>,
) -> PathMap<V, GlobalAlloc> {
    dest.write_zipper_at_path(focus).graft_map(replacement);
    dest
}

fn remove_leaf<V: Clone + Send + Sync + Unpin>(
    mut trie: PathMap<V, GlobalAlloc>,
    focus: &[u8],
) -> PathMap<V, GlobalAlloc> {
    trie.write_zipper_at_path(focus).remove_val(true);
    trie
}

fn remove_branches<V: Clone + Send + Sync + Unpin>(
    mut trie: PathMap<V, GlobalAlloc>,
    focus: &[u8],
) -> PathMap<V, GlobalAlloc> {
    trie.write_zipper_at_path(focus).remove_branches(true);
    trie
}

fn graft_from<V: Clone + Send + Sync + Unpin>(
    mut dest: PathMap<V, GlobalAlloc>,
    dest_focus: &[u8],
    src: &PathMap<V, GlobalAlloc>,
    src_focus: &[u8],
) -> PathMap<V, GlobalAlloc> {
    let src_zipper = src.read_zipper_at_path(src_focus);
    dest.write_zipper_at_path(dest_focus).graft(&src_zipper);
    dest
}

fn join_from<V: Clone + Send + Sync + Unpin>(
    mut dest: PathMap<V, GlobalAlloc>,
    dest_focus: &[u8],
    src: &PathMap<V, GlobalAlloc>,
    src_focus: &[u8],
) -> Result<PathMap<V, GlobalAlloc>, ()> {
    if let Some(subtrie) = src.read_zipper_at_path(src_focus).make_map() {
        for (relative_key, value) in subtrie.iter() {
            let absolute_key = concat_path_keys(dest_focus, &relative_key)?;
            dest.set_val_at(absolute_key, value.clone());
        }
    }
    Ok(dest)
}

pub(crate) fn write_zipper_set_subtrie(
    w: &WriteZipperLit,
    rel_lit: &ProcPathMap,
) -> Result<ProcPathMap, ()> {
    match (pathmap_from_lit(&w.0)?, pathmap_from_lit(rel_lit)?) {
        (HomogeneousPathTrie::Empty, HomogeneousPathTrie::Empty) => Ok(PathMapLit::new()),
        (HomogeneousPathTrie::Empty, HomogeneousPathTrie::Set(replacement)) => {
            set_lit_from_pathmap(&replace_subtrie(PathMap::new(), &w.1, replacement))
        },
        (HomogeneousPathTrie::Empty, HomogeneousPathTrie::Map(replacement)) => {
            map_lit_from_pathmap(&replace_subtrie(PathMap::new(), &w.1, replacement))
        },
        (HomogeneousPathTrie::Set(dest), HomogeneousPathTrie::Empty) => {
            set_lit_from_pathmap(&replace_subtrie(dest, &w.1, PathMap::new()))
        },
        (HomogeneousPathTrie::Map(dest), HomogeneousPathTrie::Empty) => {
            map_lit_from_pathmap(&replace_subtrie(dest, &w.1, PathMap::new()))
        },
        (HomogeneousPathTrie::Set(dest), HomogeneousPathTrie::Set(replacement)) => {
            set_lit_from_pathmap(&replace_subtrie(dest, &w.1, replacement))
        },
        (HomogeneousPathTrie::Map(dest), HomogeneousPathTrie::Map(replacement)) => {
            map_lit_from_pathmap(&replace_subtrie(dest, &w.1, replacement))
        },
        _ => Err(()),
    }
}

pub(crate) fn write_zipper_remove_leaf(w: &WriteZipperLit) -> Result<ProcPathMap, ()> {
    match pathmap_from_lit(&w.0)? {
        HomogeneousPathTrie::Empty => Ok(PathMapLit::new()),
        HomogeneousPathTrie::Set(trie) => set_lit_from_pathmap(&remove_leaf(trie, &w.1)),
        HomogeneousPathTrie::Map(trie) => map_lit_from_pathmap(&remove_leaf(trie, &w.1)),
    }
}

pub(crate) fn write_zipper_remove_branches(w: &WriteZipperLit) -> Result<ProcPathMap, ()> {
    match pathmap_from_lit(&w.0)? {
        HomogeneousPathTrie::Empty => Ok(PathMapLit::new()),
        HomogeneousPathTrie::Set(trie) => set_lit_from_pathmap(&remove_branches(trie, &w.1)),
        HomogeneousPathTrie::Map(trie) => map_lit_from_pathmap(&remove_branches(trie, &w.1)),
    }
}

pub(crate) fn write_zipper_graft(
    w: &WriteZipperLit,
    src: &ReadZipperLit,
) -> Result<ProcPathMap, ()> {
    match (pathmap_from_lit(&w.0)?, pathmap_from_lit(&src.0)?) {
        (HomogeneousPathTrie::Empty, HomogeneousPathTrie::Empty) => Ok(PathMapLit::new()),
        (HomogeneousPathTrie::Empty, HomogeneousPathTrie::Set(src_trie)) => {
            set_lit_from_pathmap(&graft_from(PathMap::new(), &w.1, &src_trie, &src.1))
        },
        (HomogeneousPathTrie::Empty, HomogeneousPathTrie::Map(src_trie)) => {
            map_lit_from_pathmap(&graft_from(PathMap::new(), &w.1, &src_trie, &src.1))
        },
        (HomogeneousPathTrie::Set(dest), HomogeneousPathTrie::Empty) => {
            set_lit_from_pathmap(&graft_from(dest, &w.1, &PathMap::new(), &src.1))
        },
        (HomogeneousPathTrie::Map(dest), HomogeneousPathTrie::Empty) => {
            map_lit_from_pathmap(&graft_from(dest, &w.1, &PathMap::new(), &src.1))
        },
        (HomogeneousPathTrie::Set(dest), HomogeneousPathTrie::Set(src_trie)) => {
            set_lit_from_pathmap(&graft_from(dest, &w.1, &src_trie, &src.1))
        },
        (HomogeneousPathTrie::Map(dest), HomogeneousPathTrie::Map(src_trie)) => {
            map_lit_from_pathmap(&graft_from(dest, &w.1, &src_trie, &src.1))
        },
        _ => Err(()),
    }
}

/// Right-biased union of the source subtrie into the destination subtrie at `w`'s focus.
pub(crate) fn write_zipper_join_into(
    w: &WriteZipperLit,
    src: &ReadZipperLit,
) -> Result<ProcPathMap, ()> {
    match (pathmap_from_lit(&w.0)?, pathmap_from_lit(&src.0)?) {
        (HomogeneousPathTrie::Empty, HomogeneousPathTrie::Empty) => Ok(PathMapLit::new()),
        (dest, HomogeneousPathTrie::Empty) => match dest {
            HomogeneousPathTrie::Empty => Ok(PathMapLit::new()),
            HomogeneousPathTrie::Set(dest) => set_lit_from_pathmap(&dest),
            HomogeneousPathTrie::Map(dest) => map_lit_from_pathmap(&dest),
        },
        (HomogeneousPathTrie::Empty, HomogeneousPathTrie::Set(src_trie)) => {
            set_lit_from_pathmap(&join_from(PathMap::new(), &w.1, &src_trie, &src.1)?)
        },
        (HomogeneousPathTrie::Empty, HomogeneousPathTrie::Map(src_trie)) => {
            map_lit_from_pathmap(&join_from(PathMap::new(), &w.1, &src_trie, &src.1)?)
        },
        (HomogeneousPathTrie::Set(dest), HomogeneousPathTrie::Set(src_trie)) => {
            set_lit_from_pathmap(&join_from(dest, &w.1, &src_trie, &src.1)?)
        },
        (HomogeneousPathTrie::Map(dest), HomogeneousPathTrie::Map(src_trie)) => {
            map_lit_from_pathmap(&join_from(dest, &w.1, &src_trie, &src.1)?)
        },
        _ => Err(()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lit_one(k: Proc, v: Proc) -> ProcPathMap {
        let mut lit = PathMapLit::new();
        lit.insert_map(k, v).unwrap();
        lit
    }

    #[test]
    fn pathmap_roundtrip_bytes_keys() {
        let k = Proc::CastList(std::sync::Arc::new(List::ListLit(vec![
            Proc::CastStr(std::sync::Arc::new(Str::StringLit("a".into()))),
            Proc::CastStr(std::sync::Arc::new(Str::StringLit("b".into()))),
        ])));
        let lit = lit_one(k.clone(), Proc::CastInt(std::sync::Arc::new(Int::NumLit(1))));
        let lit2 = match pathmap_from_lit(&lit).unwrap() {
            HomogeneousPathTrie::Map(pm) => map_lit_from_pathmap(&pm).unwrap(),
            _ => panic!("map literal must select map trie storage"),
        };
        assert_eq!(lit, lit2);
    }

    #[test]
    fn zipper_get_subtrie_prefix() {
        let mut lit = PathMapLit::new();
        let k1 = Proc::CastList(std::sync::Arc::new(List::ListLit(vec![
            Proc::CastStr(std::sync::Arc::new(Str::StringLit("users".into()))),
            Proc::CastStr(std::sync::Arc::new(Str::StringLit("alice".into()))),
        ])));
        let k2 = Proc::CastList(std::sync::Arc::new(List::ListLit(vec![
            Proc::CastStr(std::sync::Arc::new(Str::StringLit("users".into()))),
            Proc::CastStr(std::sync::Arc::new(Str::StringLit("bob".into()))),
        ])));
        lit.insert_map(k1, Proc::CastInt(std::sync::Arc::new(Int::NumLit(1))))
            .unwrap();
        lit.insert_map(k2, Proc::CastInt(std::sync::Arc::new(Int::NumLit(2))))
            .unwrap();
        let users = Proc::CastList(std::sync::Arc::new(List::ListLit(vec![Proc::CastStr(
            std::sync::Arc::new(Str::StringLit("users".into())),
        )])));
        let sub = path_get_subtrie_at(&lit, &users).unwrap();
        assert_eq!(sub.len(), 2);
    }

    // ── Enumeration: `getPath` / `toNextLeaf` / `leafCount` ────────────────

    fn int(n: i64) -> Proc {
        Proc::CastInt(std::sync::Arc::new(Int::NumLit(n)))
    }

    fn key(segments: &[i64]) -> Proc {
        Proc::CastList(std::sync::Arc::new(List::ListLit(
            segments.iter().copied().map(int).collect(),
        )))
    }

    /// `[1,2,3]:100, [1,2,4]:200, [2,1]:300` — the shared-prefix fixture.
    fn walk_db() -> ProcPathMap {
        let mut lit = PathMapLit::new();
        lit.insert_map(key(&[1, 2, 3]), int(100)).unwrap();
        lit.insert_map(key(&[1, 2, 4]), int(200)).unwrap();
        lit.insert_map(key(&[2, 1]), int(300)).unwrap();
        lit
    }

    /// Drive the walk to exhaustion, collecting `(path, leaf)` per step.
    fn walk_all(lit: &ProcPathMap) -> Vec<(String, String)> {
        let root = read_zipper_root(lit).expect("root zipper over an encodable literal");
        let total = zipper_leaf_count(&root).expect("leafCount at the root");
        let mut out = Vec::with_capacity(total as usize);
        let mut z = root;
        for _ in 0..total {
            z = zipper_to_next_leaf(&z).expect("toNextLeaf within the counted bound");
            out.push((
                zipper_get_path(&z).expect("getPath at a leaf").to_string(),
                match zipper_get_leaf(&z).expect("getLeaf at a leaf") {
                    ZipperLeaf::MapValue(value) => value.to_string(),
                    ZipperLeaf::SetMember => "<set-member>".to_string(),
                },
            ));
        }
        out
    }

    /// The walk is TOTAL: `leafCount` steps of `toNextLeaf` visit every entry
    /// exactly once, and at each stop BOTH `getPath` and `getLeaf` succeed.
    #[test]
    fn leaf_walk_is_total_and_every_stop_is_addressable() {
        let lit = walk_db();
        let visited = walk_all(&lit);
        assert_eq!(
            visited,
            vec![
                ("[1, 2, 3]".to_string(), "100".to_string()),
                ("[1, 2, 4]".to_string(), "200".to_string()),
                ("[2, 1]".to_string(), "300".to_string()),
            ],
            "depth-first leaf order over {{|[1,2,3]:100,[1,2,4]:200,[2,1]:300|}}"
        );
        assert_eq!(visited.len(), lit.len(), "every entry visited exactly once");
    }

    /// `leafCount` is SUBTRIE-scoped: at the root it is the map cardinality;
    /// at a prefix it counts that branch; at a leaf it is 1.
    #[test]
    fn leaf_count_is_subtrie_scoped() {
        let lit = walk_db();
        let root = read_zipper_root(&lit).expect("root zipper");
        assert_eq!(zipper_leaf_count(&root).expect("root count"), 3);
        let at_prefix = read_zipper_at(&lit, &key(&[1])).expect("zipper at [1]");
        assert_eq!(zipper_leaf_count(&at_prefix).expect("prefix count"), 2);
        let at_leaf = read_zipper_at(&lit, &key(&[1, 2, 3])).expect("zipper at [1,2,3]");
        assert_eq!(zipper_leaf_count(&at_leaf).expect("leaf count"), 1);
    }

    /// Prefix-scoped walking composes WITHOUT a walk-root field, because keys
    /// sharing a prefix are contiguous in depth-first order: from a strict
    /// prefix, the first `leafCount()` steps stay inside that branch.
    #[test]
    fn leaf_walk_from_a_strict_prefix_stays_in_the_branch() {
        let lit = walk_db();
        let at_prefix = read_zipper_at(&lit, &key(&[1])).expect("zipper at [1]");
        let n = zipper_leaf_count(&at_prefix).expect("prefix count");
        let mut z = at_prefix;
        let mut seen = Vec::with_capacity(n as usize);
        for _ in 0..n {
            z = zipper_to_next_leaf(&z).expect("in-branch step");
            seen.push(zipper_get_path(&z).expect("getPath").to_string());
        }
        assert_eq!(seen, vec!["[1, 2, 3]".to_string(), "[1, 2, 4]".to_string()]);
    }

    /// `getPath` returns a LIST at every arity — including the singleton trace,
    /// where the literal-shaped decoder would hand back a bare `Proc` and make
    /// `p.length()` undefined.
    #[test]
    fn get_path_is_a_list_at_every_arity() {
        let mut lit = PathMapLit::new();
        lit.insert_map(key(&[7]), int(1)).unwrap();
        let z = read_zipper_at(&lit, &key(&[7])).expect("zipper at [7]");
        assert_eq!(zipper_get_path(&z).expect("getPath").to_string(), "[7]");
        // The literal-shaped decoder deliberately differs here.
        assert_eq!(
            proc_key_from_path_bytes(&z.1)
                .expect("literal-shaped decode")
                .to_string(),
            "7"
        );
    }

    /// `getPath` round-trips through the map: the reported key re-addresses the
    /// entry the cursor is focused on, at every arity.
    #[test]
    fn get_path_round_trips_through_the_map() {
        let lit = walk_db();
        let root = read_zipper_root(&lit).expect("root zipper");
        let mut z = root.clone();
        for _ in 0..zipper_leaf_count(&root).expect("leafCount") {
            z = zipper_to_next_leaf(&z).expect("step");
            let reported = zipper_get_path(&z).expect("getPath");
            let leaf = match zipper_get_leaf(&z).expect("getLeaf") {
                ZipperLeaf::MapValue(value) => value,
                ZipperLeaf::SetMember => panic!("fixture is map-mode"),
            };
            let via_key = match super::super::pathmap::pathmap_get(&lit, &reported)
                .expect("encodable reported key")
            {
                super::super::pathmap::PathmapLookup::MapValue(value) => value,
                _ => panic!("reported key must address a live map entry"),
            };
            assert_eq!(via_key, leaf, "m.get(z.getPath()) must be z.getLeaf()");
        }
    }

    /// The root focus names no entry, so `getPath` errors there. rholang cannot
    /// build a root-valued `Pathmap` (`encode_proc_path_entry` rejects `[]`), so
    /// this position never carries a leaf either.
    #[test]
    fn get_path_at_the_root_has_no_key() {
        let lit = walk_db();
        let root = read_zipper_root(&lit).expect("root zipper");
        assert!(zipper_get_path(&root).is_err());
    }

    /// Measurement behind the design note: BYTE-granular moves park the focus
    /// mid-segment, where the key does not decode and no value exists — which
    /// is why enumeration is leaf-granular instead.
    #[test]
    fn byte_granular_moves_park_mid_segment() {
        let lit = walk_db();
        let root = read_zipper_root(&lit).expect("root zipper");
        let first = zipper_descend_first(&root).expect("descendFirst from the root");
        assert_eq!(first.1.len(), 1, "descendFirst advances ONE byte");
        assert!(zipper_get_leaf(&first).is_err(), "a mid-segment focus carries no value");
        assert!(
            zipper_get_path(&first).is_err() || zipper_get_leaf(&first).is_err(),
            "a mid-segment focus is not an addressable entry"
        );
        assert!(
            zipper_get_subtrie(&first).is_err(),
            "relative keys below a mid-segment focus begin with a partial segment"
        );
    }

    /// Pins the ⚠ correction on [`zipper_relative_read_zipper`]: rerooting via
    /// `read_zipper_at_path` truncates the ancestor STACK (so ascent is
    /// impaired) but leaves SIBLING moves working, because `ReadZipperCore`
    /// overrides `to_next_sibling_byte` to test `prefix_buf` rather than the
    /// trait default's `path().last()`.
    ///
    /// An earlier rationale claimed sibling moves collapsed to `Proc::Err`
    /// under rerooting; they do not, and `zipper_to_next_sibling` is correct
    /// as written. What looked like breakage was the leaf case, where `Err` is
    /// the RIGHT answer — `[1,2,3]`'s parent has exactly one child.
    #[test]
    fn rerooting_bounds_ascent_but_not_sibling_moves() {
        let lit = walk_db();
        let root = read_zipper_root(&lit).expect("root zipper");

        // A focus one BYTE below the root: `[1,…]` and `[2,…]` are siblings.
        let first = zipper_descend_first(&root).expect("descendFirst from the root");
        assert_eq!(first.1, vec![b'1'], "descendFirst advances one byte");
        let sibling = zipper_to_next_sibling(&first)
            .expect("sibling moves DO work from a rerooted focus (the correction)");
        assert_eq!(sibling.1, vec![b'2'], "'1' -> '2' across the root's children");

        // At a leaf the parent has ONE child, so `Err` is the correct answer —
        // not evidence of rerooting damage.
        let at_leaf = read_zipper_at(&lit, &key(&[1, 2, 3])).expect("zipper at [1,2,3]");
        assert_eq!(at_leaf.1, vec![b'1', 0xFF, b'2', 0xFF, b'3', 0xFF]);
        assert!(
            zipper_to_next_sibling(&at_leaf).is_err(),
            "the leaf's parent has exactly one child, so there IS no next sibling"
        );

        // Ascent, by contrast, needs the full-trie rooting: two bytes up from
        // the leaf is the shared prefix `1<FF>2<FF>`, whose subtrie is {3,4}.
        let up = zipper_ascend(&at_leaf, 2).expect("ascend via the full-trie rooting");
        assert_eq!(up.1, vec![b'1', 0xFF, b'2', 0xFF]);
        assert_eq!(
            zipper_get_subtrie(&up)
                .expect("subtrie at the shared prefix")
                .len(),
            2
        );
    }

    // ── ★ CROSS-ENDPOINT CONTRACT: exhaustion is STUCK here, `Nil` there ────
    //
    // The two runtimes report a failed/exhausted navigation DIFFERENTLY, and
    // each is correct in its own house style:
    //
    //   mettail (this file)  ▸ `Err(())`, which the fold body renders as the
    //                          UNREDUCED term `z.toNextLeaf()` — "stuck"
    //                          (user decision 2026-06-30; see `RZGetLeaf`).
    //   f1r3node (reducer)   ▸ `Ok(Par::default())` — i.e. **`Nil`**
    //                          (`reduce.rs::to_next_sibling_method` and every
    //                          other navigation method return `Par::default()`
    //                          rather than erroring).
    //
    // ⚠ REQUIRED TRANSLATION FOR C1 — the seam that routes rholang collection
    // methods to the reducer's own method table MUST map the reducer's `Nil`
    // result for `toNextLeaf` back to mettail's STUCK form. It must NOT surface
    // `Nil` as a `ReadZipper`, and it must NOT let the walk continue.
    //
    // Why this is worth a test on each side rather than a paragraph: the
    // counted-walk idiom is
    //
    //     z ← m.readZipper(); n ← z.leafCount(); n × ( z ← z.toNextLeaf() )
    //
    // If exhaustion yields anything the walk can keep consuming, the loop does
    // not fail — it SILENTLY RESTARTS, because `to_next_val()` resets the
    // zipper to the root on `false` (pathmap/src/zipper.rs:546). A mistranslated
    // seam therefore produces an infinite loop with no error anywhere, which is
    // exactly the defect that gets found late and expensively.
    //
    // The sibling assertion lives at
    // `f1r3node-rust-mettail/rholang/tests/zipper_enumeration_spec.rs`
    // (`to_next_leaf_returns_nil_when_exhausted`), and cross-references back
    // here.

    /// ★ mettail endpoint of the `Nil`-vs-stuck contract. See the block comment
    /// above, and the f1r3node twin `to_next_leaf_returns_nil_when_exhausted`.
    #[test]
    fn exhausted_walk_is_stuck_here_and_nil_on_the_reducer() {
        let lit = walk_db();
        let root = read_zipper_root(&lit).expect("root zipper");
        let mut z = root.clone();
        for _ in 0..zipper_leaf_count(&root).expect("leafCount") {
            z = zipper_to_next_leaf(&z).expect("in-bound step");
        }
        // mettail's half of the contract: Err => the fold leaves the term
        // UNREDUCED (stuck). It must never be `Ok`, because an `Ok` here would
        // carry the root-reset focus and restart the walk forever.
        assert!(
            zipper_to_next_leaf(&z).is_err(),
            "exhaustion must be Err (=> stuck), never a returning zipper; \
             C1 must translate the reducer's `Nil` to this same stuck form"
        );
    }

    #[test]
    fn zipper_navigation_child_count_and_failure() {
        let mut lit = PathMapLit::new();
        lit.insert_map(
            Proc::CastList(std::sync::Arc::new(List::ListLit(vec![
                Proc::CastInt(std::sync::Arc::new(Int::NumLit(1))),
                Proc::CastInt(std::sync::Arc::new(Int::NumLit(1))),
                Proc::CastInt(std::sync::Arc::new(Int::NumLit(1))),
            ]))),
            Proc::CastInt(std::sync::Arc::new(Int::NumLit(30))),
        )
        .unwrap();
        lit.insert_map(
            Proc::CastList(std::sync::Arc::new(List::ListLit(vec![
                Proc::CastInt(std::sync::Arc::new(Int::NumLit(1))),
                Proc::CastInt(std::sync::Arc::new(Int::NumLit(2))),
                Proc::CastInt(std::sync::Arc::new(Int::NumLit(1))),
            ]))),
            Proc::CastInt(std::sync::Arc::new(Int::NumLit(35))),
        )
        .unwrap();
        let root_branch = Proc::CastList(std::sync::Arc::new(List::ListLit(vec![Proc::CastInt(
            std::sync::Arc::new(Int::NumLit(1)),
        )])));
        let rz = read_zipper_at(&lit, &root_branch).unwrap();
        assert_eq!(zipper_child_count(&rz).unwrap(), 2);
        let mut single = PathMapLit::new();
        single
            .insert_map(
                Proc::CastList(std::sync::Arc::new(List::ListLit(vec![Proc::CastInt(
                    std::sync::Arc::new(Int::NumLit(1)),
                )]))),
                Proc::CastInt(std::sync::Arc::new(Int::NumLit(10))),
            )
            .unwrap();
        let leaf = Proc::CastList(std::sync::Arc::new(List::ListLit(vec![Proc::CastInt(
            std::sync::Arc::new(Int::NumLit(1)),
        )])));
        let leaf_zipper = read_zipper_at(&single, &leaf).unwrap();
        assert!(zipper_descend_first(&leaf_zipper).is_err());
    }
}
