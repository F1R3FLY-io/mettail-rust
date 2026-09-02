//! E-3 T-E6B (H4v2) — the pathmap-0.2.2-backed CONSTRUCTION-SIDE fragment store
//! (pgmcp experiment 146; the frozen H4v2 registration + delta amendment EM-8,
//! which is BINDING; bench-only extension surface per user decision D3 — the
//! `bench-fragment-store` feature quarantines this module and its `pathmap`
//! dependency, exactly like the `bench-naive-baseline` precedent).
//!
//! # What the store holds
//!
//! Per compiled language family, one SERIALIZED, SYN-FREE fragment per
//! set-automaton rule entry plus ONE family manifest fragment, keyed
//! `family / root-op / rule-id` (the manifest occupies the reserved empty
//! `root-op`/`rule-id` segments, which no identifier can collide with):
//!
//! * **rule fragment** — the FINGERPRINT-INDEPENDENT construction facts of one
//!   automaton entry: family, rule label, root op, the canonical serialization
//!   of its converted LHS [`Pattern`], its accept channel
//!   (`lhs_pattern_trace_channel` — pattern-content-derived, fingerprint- and
//!   index-independent, EM-6), and its ROOT-OP GROUP's member labels in
//!   declaration order. The group list is honest content, not bookkeeping: the
//!   per-call receiver-network emitter groups entries by root op (the EM-11
//!   `groups` structure), so any emitted per-group artifact depends on the whole
//!   group's membership — a fragment therefore genuinely changes exactly when
//!   its group gains or loses a member.
//! * **manifest fragment** — the family-level facts: name, the WHOLE-DEFINITION
//!   fingerprint (user decision D1), rewrite/entry/state counts, and the
//!   deferred-rule labels. The T-INCR finding stands: any rule insert taints the
//!   fingerprint, so the manifest invalidates on EVERY append — the store
//!   QUARANTINES the fingerprint-dependent share into this ONE fragment (the
//!   registration's "+ 1") instead of letting it taint every per-rule fragment.
//!
//! # The H4v2 deterministic metrics this module computes
//!
//! * **(i) retained serialized-fragment bytes, deduped by `Arc` identity**
//!   ([`ladder_accounting`]): across ALL retained ladder snapshots, each
//!   distinct `Arc<Fragment>` allocation is counted ONCE (`Arc::as_ptr`
//!   identity — unchanged fragments are SHARED between snapshots by the
//!   snapshot clone, and content-recurrent fragments are shared by the intern
//!   table). Compared against the per-variant WHOLE-ARTIFACT baseline: the same
//!   fragment content retained wholesale per variant (Σ over snapshots of Σ of
//!   fragment lengths — framing and key bytes are EXCLUDED on both sides, which
//!   UNDERSTATES the baseline, i.e. is conservative for the `<` claim). Never
//!   RSS — pure byte arithmetic over the serialized payloads.
//! * **(ii) exact invalidation per append** ([`AppendReport`]): what ACTUALLY
//!   invalidates is COUNTED (a previously retained fragment counts only if its
//!   recomputed canonical bytes differ), never inferred from the touched-key
//!   set. The primary registered expectation for a single-rewrite append is
//!   `root-op-group size + 1`, where the group size is the appended rule's
//!   root-op group BEFORE the insert (its stale members) and the `+ 1` is the
//!   always-invalidating manifest; the freshly appended rule's own fragment is
//!   a NEW insert (`inserted_new`), reported separately so the alternative
//!   after-insert reading (`group_after + 1`, which folds the insert into the
//!   count) is derivable from the same record.
//! * **(iii) wall parity** is the HARNESS's job (`--mode e6b`): this module is
//!   container-generic ([`FragmentStoreBackend`]) so the pathmap-backed arm and
//!   the `HashMap`-backed twin run IDENTICAL reconciliation logic — the two
//!   arms differ only in the container operations, which is exactly what the
//!   two-sided ≤ 5 % guard compares.
//!
//! # EM-8 (BINDING): the store value
//!
//! The stored value is [`FragmentHandle`] — a newtype over `Arc<Fragment>` —
//! and `Fragment` is SYN-FREE (owned `String`s/bytes/integers only), because
//! pathmap's `TrieValue` supertrait requires `Clone + Send + Sync + Unpin +
//! 'static` and `syn`/`proc-macro2` data is deliberately `!Send + !Sync`
//! (non-atomic `Rc` refcounts — see `rho_net_cache`'s module docs). The
//! [`Lattice`] impl is CONTENT-HASH EQUALITY: content-equal fragments (hash
//! fast path + byte verification, so a hash collision can never alias) are
//! identities of each other — `pjoin`/`pmeet` return
//! `Identity(SELF_IDENT | COUNTER_IDENT)`, preserving `Arc` sharing with zero
//! allocation — and content-UNEQUAL fragments resolve by the total order
//! `(content_hash, bytes)`, making `pjoin` = max and `pmeet` = min: a lawful
//! (distributive) lattice, since min/max over any total order satisfies
//! idempotence, commutativity, associativity, and absorption. Every result is
//! an `Identity`, never an `Element` — joins allocate nothing.
//!
//! # Bench-only surface (D3)
//!
//! No production entry point, generated body, or macro references this module;
//! the E-3 `--mode e6b` harness and this module's tests are its only
//! consumers. It lives here (not in the harness) beside `rho_net_incremental`
//! — fragment derivation reads the SAME artifact surface
//! ([`CompiledInRhoArtifacts`], `convert_lhs_pattern`, the ruleset's derived
//! `accept_channels`) that the incremental append produces, and the
//! `bench-fragment-store` feature quarantines the module + its `pathmap`
//! dependency the same way `bench-naive-baseline` quarantines the naive
//! emitter.

use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use dovetail::rules::Pattern as DvPattern;
use dovetail::set_automaton::{AutomatonNode, PatternId};
use pathmap::ring::{AlgebraicResult, Lattice, COUNTER_IDENT, SELF_IDENT};
use pathmap::zipper::{ZipperMoving, ZipperReadOnlyIteration};
use pathmap::PathMap;

use crate::rho_net_cache::CompiledInRhoArtifacts;
use crate::rho_net_ruleset::convert_lhs_pattern;

// ─────────────────────────────────────────────────────────────────────────────
// Content hashing.
// ─────────────────────────────────────────────────────────────────────────────

fn content_digest(bytes: &[u8]) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new();
    hasher.update(b"MeTTaIL construction fragment\0");
    hasher.update(&(bytes.len() as u64).to_be_bytes());
    hasher.update(bytes);
    *hasher.finalize().as_bytes()
}

// ─────────────────────────────────────────────────────────────────────────────
// Key encoding: length-prefixed segments (prefix-injective by construction).
// ─────────────────────────────────────────────────────────────────────────────

/// Append one length-prefixed segment (`u16` big-endian length, then the raw
/// bytes). Length-prefixing makes the 3-segment key encoding INJECTIVE and the
/// 2-segment group prefix a true byte prefix of exactly its own group's keys:
/// `seg(a)·seg(b)` can prefix `seg(a)·seg(b')·seg(c)` only if `b = b'`
/// (a longer `b'` sharing `b` as a prefix necessarily differs in its length
/// prefix first — pinned by `key_encoding_is_prefix_injective`).
fn push_segment(out: &mut Vec<u8>, segment: &str) {
    let length = u16::try_from(segment.len())
        .expect("store key segments are identifiers/labels far below 64 KiB");
    out.extend_from_slice(&length.to_be_bytes());
    out.extend_from_slice(segment.as_bytes());
}

/// The encoded `family / root-op / rule-label` key of a rule fragment.
fn rule_key(family: &str, root_op: &str, rule_label: &str) -> Vec<u8> {
    debug_assert!(!root_op.is_empty(), "a rule fragment's root op is a named constructor");
    debug_assert!(!rule_label.is_empty(), "a rule fragment's label is a named rewrite");
    let mut key = Vec::with_capacity(6 + family.len() + root_op.len() + rule_label.len());
    push_segment(&mut key, family);
    push_segment(&mut key, root_op);
    push_segment(&mut key, rule_label);
    key
}

/// The encoded group prefix `family / root-op` — a byte prefix of exactly this
/// group's rule keys (see [`push_segment`]).
fn group_prefix(family: &str, root_op: &str) -> Vec<u8> {
    let mut key = Vec::with_capacity(4 + family.len() + root_op.len());
    push_segment(&mut key, family);
    push_segment(&mut key, root_op);
    key
}

/// The encoded manifest key `family / "" / ""` — the empty segments are
/// RESERVED (no constructor op or rewrite label is empty), so the manifest can
/// never collide with a rule key and never falls under any real group prefix.
fn manifest_key(family: &str) -> Vec<u8> {
    let mut key = Vec::with_capacity(6 + family.len());
    push_segment(&mut key, family);
    push_segment(&mut key, "");
    push_segment(&mut key, "");
    key
}

// ─────────────────────────────────────────────────────────────────────────────
// Canonical fragment payloads (deterministic, self-describing, syn-free).
// ─────────────────────────────────────────────────────────────────────────────

/// Payload tag of a rule fragment.
const TAG_RULE: u8 = 0x01;
/// Payload tag of a manifest fragment.
const TAG_MANIFEST: u8 = 0x02;

fn push_u32(out: &mut Vec<u8>, value: usize) {
    let value = u32::try_from(value).expect("store cardinalities fit u32");
    out.extend_from_slice(&value.to_be_bytes());
}

/// Canonical serialization of a converted LHS [`DvPattern`] (structural,
/// deterministic): `0x00 seg(var)` / `0x01 seg(op) u32(argc) args…` /
/// `0x02 seg(op) u32(fixedc) fixed… (0x00 | 0x01 seg(rest))`.
fn encode_pattern(out: &mut Vec<u8>, pattern: &DvPattern<String>) {
    enum Work<'a> {
        Pattern(&'a DvPattern<String>),
        AcRest(Option<&'a String>),
    }

    let mut work = vec![Work::Pattern(pattern)];
    while let Some(step) = work.pop() {
        match step {
            Work::Pattern(DvPattern::Var(name)) => {
                out.push(0x00);
                push_segment(out, name);
            },
            Work::Pattern(DvPattern::App { op, args }) => {
                out.push(0x01);
                push_segment(out, op);
                push_u32(out, args.len());
                work.extend(args.iter().rev().map(Work::Pattern));
            },
            Work::Pattern(DvPattern::AcApp { op, fixed, rest }) => {
                out.push(0x02);
                push_segment(out, op);
                push_u32(out, fixed.len());
                work.push(Work::AcRest(rest.as_ref()));
                work.extend(fixed.iter().rev().map(Work::Pattern));
            },
            Work::AcRest(rest) => match rest {
                None => out.push(0x00),
                Some(rest) => {
                    out.push(0x01);
                    push_segment(out, rest);
                },
            },
        }
    }
}

/// The canonical rule-fragment payload. Embeds the FULL key (family, root op,
/// label), so content equality implies key equality — the intern table's
/// cross-key reuse can never alias two keys' fragments.
fn encode_rule_fragment(
    family: &str,
    rule_label: &str,
    root_op: &str,
    pattern: &DvPattern<String>,
    accept_channel: &str,
    group_members: &[String],
) -> Vec<u8> {
    let mut out = Vec::with_capacity(
        64 + family.len()
            + rule_label.len()
            + root_op.len()
            + accept_channel.len()
            + group_members
                .iter()
                .map(|member| member.len() + 2)
                .sum::<usize>(),
    );
    out.push(TAG_RULE);
    push_segment(&mut out, family);
    push_segment(&mut out, rule_label);
    push_segment(&mut out, root_op);
    encode_pattern(&mut out, pattern);
    push_segment(&mut out, accept_channel);
    push_u32(&mut out, group_members.len());
    for member in group_members {
        push_segment(&mut out, member);
    }
    out
}

/// The canonical manifest payload (the ONE fingerprint-dependent fragment).
fn encode_manifest_fragment(
    family: &str,
    language_fingerprint: &str,
    rewrite_count: usize,
    entry_count: usize,
    state_count: usize,
    deferred_labels: &[String],
) -> Vec<u8> {
    let mut out = Vec::with_capacity(
        32 + family.len()
            + language_fingerprint.len()
            + deferred_labels
                .iter()
                .map(|label| label.len() + 2)
                .sum::<usize>(),
    );
    out.push(TAG_MANIFEST);
    push_segment(&mut out, family);
    push_segment(&mut out, language_fingerprint);
    push_u32(&mut out, rewrite_count);
    push_u32(&mut out, entry_count);
    push_u32(&mut out, state_count);
    push_u32(&mut out, deferred_labels.len());
    for label in deferred_labels {
        push_segment(&mut out, label);
    }
    out
}

// ─────────────────────────────────────────────────────────────────────────────
// The fragment value + the EM-8 content-hash-equality Lattice.
// ─────────────────────────────────────────────────────────────────────────────

/// One serialized construction fragment — SYN-FREE by construction (owned
/// strings/bytes/integers only), so `Arc<Fragment>` satisfies pathmap's
/// `TrieValue` supertrait (`Clone + Send + Sync + Unpin + 'static`).
#[derive(Debug)]
pub struct Fragment {
    /// The key parts (also embedded in `bytes` — content equality implies key
    /// equality).
    family: String,
    root_op: String,
    rule_label: String,
    /// The canonical serialized payload — THE retained bytes of metric (i).
    bytes: Vec<u8>,
    /// Domain-separated BLAKE3-256 of `bytes` (the Lattice fast path).
    content_hash: [u8; 32],
}

/// EM-8 (BINDING): the store value — a newtype over `Arc<Fragment>` carrying
/// the content-hash-equality [`Lattice`]. Cloning is an `Arc` clone (the
/// snapshot/dedup sharing mechanism).
#[derive(Clone, Debug)]
pub struct FragmentHandle(Arc<Fragment>);

impl FragmentHandle {
    fn new(family: String, root_op: String, rule_label: String, bytes: Vec<u8>) -> Self {
        let content_hash = content_digest(&bytes);
        Self(Arc::new(Fragment {
            family,
            root_op,
            rule_label,
            bytes,
            content_hash,
        }))
    }

    /// The serialized payload (metric (i)'s retained bytes).
    pub fn bytes(&self) -> &[u8] {
        &self.0.bytes
    }

    /// The BLAKE3-256 content hash of [`bytes`](Self::bytes).
    pub fn content_hash(&self) -> [u8; 32] {
        self.0.content_hash
    }

    /// The `(family, root_op, rule_label)` key parts (empty `root_op`/`rule_label`
    /// on the manifest fragment).
    pub fn key_parts(&self) -> (&str, &str, &str) {
        (&self.0.family, &self.0.root_op, &self.0.rule_label)
    }

    /// The `Arc` allocation identity (metric (i)'s dedup key).
    fn arc_identity(&self) -> usize {
        Arc::as_ptr(&self.0) as usize
    }

    /// Total order for the content lattice: `(content_hash, bytes)`
    /// lexicographic. Hash equality falls through to byte comparison, so a hash
    /// collision orders by content and NEVER aliases two distinct fragments as
    /// equal.
    fn content_cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.0
            .content_hash
            .cmp(&other.0.content_hash)
            .then_with(|| self.0.bytes.cmp(&other.0.bytes))
    }
}

impl PartialEq for FragmentHandle {
    /// CONTENT equality (hash fast path + byte verification) — the equality the
    /// EM-8 Lattice identity results assert.
    fn eq(&self, other: &Self) -> bool {
        self.0.content_hash == other.0.content_hash && self.0.bytes == other.0.bytes
    }
}

impl Eq for FragmentHandle {}

impl Lattice for FragmentHandle {
    /// Join = max under the `(content_hash, bytes)` total order; content-equal
    /// operands are identities of each other (both mask bits — lawful because
    /// [`PartialEq`] IS content equality). Always an `Identity` (the result is
    /// always one of the operands), never an allocation.
    fn pjoin(&self, other: &Self) -> AlgebraicResult<Self> {
        match self.content_cmp(other) {
            std::cmp::Ordering::Equal => AlgebraicResult::Identity(SELF_IDENT | COUNTER_IDENT),
            std::cmp::Ordering::Greater => AlgebraicResult::Identity(SELF_IDENT),
            std::cmp::Ordering::Less => AlgebraicResult::Identity(COUNTER_IDENT),
        }
    }

    /// Meet = min under the same total order (the dual of [`pjoin`](Self::pjoin)).
    fn pmeet(&self, other: &Self) -> AlgebraicResult<Self> {
        match self.content_cmp(other) {
            std::cmp::Ordering::Equal => AlgebraicResult::Identity(SELF_IDENT | COUNTER_IDENT),
            std::cmp::Ordering::Less => AlgebraicResult::Identity(SELF_IDENT),
            std::cmp::Ordering::Greater => AlgebraicResult::Identity(COUNTER_IDENT),
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// The container-generic backend (the (iii) arm seam).
// ─────────────────────────────────────────────────────────────────────────────

/// The store's container operations — implemented by the pathmap trie and by
/// the plain-`HashMap` twin with IDENTICAL semantics, so the two `--mode e6b`
/// arms differ ONLY in container cost (the H4v2 (iii) comparison).
pub trait FragmentStoreBackend: Sized {
    /// The arm's stable CLI/JSON name.
    const NAME: &'static str;

    /// An empty store.
    fn empty() -> Self;

    /// The fragment at `key`, if present (an `Arc` clone — cheap).
    fn get(&self, key: &[u8]) -> Option<FragmentHandle>;

    /// Insert/overwrite the fragment at `key`, returning the displaced one.
    fn set(&mut self, key: &[u8], value: FragmentHandle) -> Option<FragmentHandle>;

    /// Remove the fragment at `key`, returning it.
    fn remove(&mut self, key: &[u8]) -> Option<FragmentHandle>;

    /// Every `(key, fragment)` under `prefix`, key-ascending.
    fn group_entries(&self, prefix: &[u8]) -> Vec<(Vec<u8>, FragmentHandle)>;

    /// Every `(key, fragment)` in the store, key-ascending.
    fn entries(&self) -> Vec<(Vec<u8>, FragmentHandle)>;

    /// The number of stored fragments.
    fn len(&self) -> usize;

    /// Whether the store is empty.
    fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// A retained snapshot of the current state. Both containers clone
    /// `FragmentHandle`s (`Arc` clones), so unchanged fragments SHARE their
    /// allocation across snapshots — the sharing metric (i) measures.
    fn snapshot(&self) -> Self;
}

/// The pathmap-0.2.2-backed arm: keys are trie paths, group enumeration is a
/// prefix-rooted read zipper, group removal is a subtree branch removal.
pub struct PathMapFragmentStore {
    map: PathMap<FragmentHandle>,
}

impl FragmentStoreBackend for PathMapFragmentStore {
    const NAME: &'static str = "pathmap";

    fn empty() -> Self {
        Self { map: PathMap::new() }
    }

    fn get(&self, key: &[u8]) -> Option<FragmentHandle> {
        self.map.get_val_at(key).cloned()
    }

    fn set(&mut self, key: &[u8], value: FragmentHandle) -> Option<FragmentHandle> {
        self.map.set_val_at(key, value)
    }

    fn remove(&mut self, key: &[u8]) -> Option<FragmentHandle> {
        self.map.remove_val_at(key, true)
    }

    fn group_entries(&self, prefix: &[u8]) -> Vec<(Vec<u8>, FragmentHandle)> {
        let mut zipper = self.map.read_zipper_at_path(prefix);
        let mut entries: Vec<(Vec<u8>, FragmentHandle)> = Vec::new();
        while let Some(value) = zipper.to_next_get_val() {
            let mut key = Vec::with_capacity(prefix.len() + zipper.path().len());
            key.extend_from_slice(prefix);
            key.extend_from_slice(zipper.path());
            entries.push((key, value.clone()));
        }
        entries.sort_by(|left, right| left.0.cmp(&right.0));
        entries
    }

    fn entries(&self) -> Vec<(Vec<u8>, FragmentHandle)> {
        let mut entries: Vec<(Vec<u8>, FragmentHandle)> = self
            .map
            .iter()
            .map(|(key, value)| (key, value.clone()))
            .collect();
        entries.sort_by(|left, right| left.0.cmp(&right.0));
        entries
    }

    fn len(&self) -> usize {
        self.map.val_count()
    }

    fn snapshot(&self) -> Self {
        Self { map: self.map.clone() }
    }
}

/// The `HashMap`-backed twin arm (the (iii) comparand): the SAME encoded keys
/// in a flat `HashMap`; group enumeration is a full-scan prefix filter (the
/// straightforward `HashMap` realization — no secondary index).
pub struct HashMapFragmentStore {
    map: HashMap<Vec<u8>, FragmentHandle>,
}

impl FragmentStoreBackend for HashMapFragmentStore {
    const NAME: &'static str = "hashmap";

    fn empty() -> Self {
        Self { map: HashMap::new() }
    }

    fn get(&self, key: &[u8]) -> Option<FragmentHandle> {
        self.map.get(key).cloned()
    }

    fn set(&mut self, key: &[u8], value: FragmentHandle) -> Option<FragmentHandle> {
        self.map.insert(key.to_vec(), value)
    }

    fn remove(&mut self, key: &[u8]) -> Option<FragmentHandle> {
        self.map.remove(key)
    }

    fn group_entries(&self, prefix: &[u8]) -> Vec<(Vec<u8>, FragmentHandle)> {
        let mut entries: Vec<(Vec<u8>, FragmentHandle)> = self
            .map
            .iter()
            .filter(|(key, _)| key.starts_with(prefix))
            .map(|(key, value)| (key.clone(), value.clone()))
            .collect();
        entries.sort_by(|left, right| left.0.cmp(&right.0));
        entries
    }

    fn entries(&self) -> Vec<(Vec<u8>, FragmentHandle)> {
        let mut entries: Vec<(Vec<u8>, FragmentHandle)> = self
            .map
            .iter()
            .map(|(key, value)| (key.clone(), value.clone()))
            .collect();
        entries.sort_by(|left, right| left.0.cmp(&right.0));
        entries
    }

    fn len(&self) -> usize {
        self.map.len()
    }

    fn snapshot(&self) -> Self {
        Self { map: self.map.clone() }
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Family fact derivation (host-side, syn-consuming; outputs are syn-free).
// ─────────────────────────────────────────────────────────────────────────────

/// One automaton entry's light facts (no pattern conversion — the O(r) scan).
struct EntryFact {
    label: String,
    root_op: String,
    rewrite_index: usize,
}

/// The light per-entry facts of `artifacts` (label + root op per automaton
/// entry, in entry order) plus the family-level manifest inputs. `Err` when
/// the family is outside the store's admitted shape (native entries, an
/// auto-injected entry, or a variable-root entry) — the same fail-closed
/// discipline as `rho_net_incremental`'s admission matrix.
fn entry_facts(artifacts: &CompiledInRhoArtifacts) -> Result<Vec<EntryFact>, String> {
    let ruleset = artifacts.ruleset();
    let view = ruleset.automaton.view();
    let mut facts = Vec::with_capacity(view.entry_count());
    for entry in 0..view.entry_count() {
        let id = view.entry_id(entry);
        let rewrite = artifacts.def.rewrites.get(id.0).ok_or_else(|| {
            format!("automaton entry {entry} names no rewrite (a native entry?) — outside the store's family shape")
        })?;
        if rewrite.is_auto_injected {
            return Err(format!(
                "automaton entry {entry} names the auto-injected rewrite `{}` — outside the store's family shape",
                rewrite.name
            ));
        }
        let root_op = match view.node(view.entry_root_state(entry)) {
            AutomatonNode::App { op, .. } => op.clone(),
            AutomatonNode::Var => {
                return Err(format!(
                    "automaton entry {entry} has a variable root — no root-op group"
                ));
            },
        };
        facts.push(EntryFact {
            label: rewrite.name.to_string(),
            root_op,
            rewrite_index: id.0,
        });
    }
    Ok(facts)
}

/// The accept channel of entry `PatternId(index)` from the ruleset's derived
/// `accept_channels` (EM-6: pattern-content-hashed, fingerprint-independent).
fn accept_channel_for(
    artifacts: &CompiledInRhoArtifacts,
    rewrite_index: usize,
) -> Result<String, String> {
    artifacts
        .ruleset()
        .accept_channels
        .iter()
        .find(|(id, _)| *id == PatternId(rewrite_index))
        .map(|(_, channel)| channel.clone())
        .ok_or_else(|| format!("automaton entry PatternId({rewrite_index}) has no accept channel"))
}

/// The manifest payload of `artifacts` (family name, fingerprint, counts,
/// deferred labels — sorted for determinism).
fn manifest_bytes(artifacts: &CompiledInRhoArtifacts, family: &str) -> Vec<u8> {
    let ruleset = artifacts.ruleset();
    let view = ruleset.automaton.view();
    let mut deferred_labels: Vec<String> = ruleset
        .deferred
        .iter()
        .map(|deferred| deferred.rule_label.clone())
        .collect();
    deferred_labels.sort();
    encode_manifest_fragment(
        family,
        &ruleset.language_fingerprint,
        artifacts.def.rewrites.len(),
        view.entry_count(),
        view.state_count(),
        &deferred_labels,
    )
}

/// The root op of the LAST automaton entry of `artifacts` — the appended
/// rule's root op after a T-INCR extend (the extend appends its entry), i.e.
/// the DIRTY root-op group of [`ConstructionFragmentStore::reconcile_append`].
pub fn appended_rule_root_op(artifacts: &CompiledInRhoArtifacts) -> Result<String, String> {
    let facts = entry_facts(artifacts)?;
    facts
        .last()
        .map(|fact| fact.root_op.clone())
        .ok_or_else(|| "the artifacts have no automaton entries".to_string())
}

// ─────────────────────────────────────────────────────────────────────────────
// The construction-side store.
// ─────────────────────────────────────────────────────────────────────────────

/// What one base-family seeding did ([`ConstructionFragmentStore::seed_from_artifacts`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SeedReport {
    /// Fragments inserted (rule fragments + the manifest).
    pub inserted: usize,
    /// Total fragments in the store after seeding.
    pub store_entries: usize,
}

/// What one append reconciliation ACTUALLY did
/// ([`ConstructionFragmentStore::reconcile_append`]) — every count is observed
/// (content compared), never inferred.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AppendReport {
    /// Fragments retained under the dirty root-op group BEFORE the append.
    pub group_before: usize,
    /// Rules in the dirty root-op group AFTER the append (per the extended def).
    pub group_after: usize,
    /// Previously retained group fragments whose recomputed canonical bytes
    /// DIFFER (recomputed and re-stored) — actual invalidations.
    pub invalidated_existing: usize,
    /// Previously retained group fragments whose key left the group (removed) —
    /// zero on any append-only ladder, counted for completeness.
    pub invalidated_removed: usize,
    /// `1` iff the recomputed manifest differs from the retained one (it always
    /// does on a real append — the fingerprint taint), else `0`.
    pub manifest_invalidated: usize,
    /// Group keys not previously present (the appended rule's own fragment) —
    /// fresh inserts, NOT invalidations.
    pub inserted_new: usize,
    /// Group fragments whose recomputed bytes are UNCHANGED (old `Arc` kept —
    /// zero recompute waste is the precision claim's complement).
    pub unchanged_group: usize,
    /// Total fragments in the store after the reconcile.
    pub store_entries: usize,
}

impl AppendReport {
    /// The H4v2 (ii) registered expectation for a single-rewrite append:
    /// the appended rule's root-op-group size BEFORE the insert (its stale
    /// members) `+ 1` (the always-invalidating manifest). The after-insert
    /// reading (`group_after + 1`) additionally counts [`inserted_new`]
    /// (self.group_after = group_before + inserted_new on an append) and is
    /// derivable from the same record.
    ///
    /// [`inserted_new`]: Self::inserted_new
    pub fn expected_invalidated(&self) -> usize {
        self.group_before + 1
    }

    /// What ACTUALLY invalidated: stale group fragments (changed or removed)
    /// plus the manifest if it changed.
    pub fn actual_invalidated(&self) -> usize {
        self.invalidated_existing + self.invalidated_removed + self.manifest_invalidated
    }

    /// The H4v2 (ii) exactness predicate for this append.
    pub fn invalidation_exact(&self) -> bool {
        self.actual_invalidated() == self.expected_invalidated()
    }
}

/// The construction-side fragment store: a container backend plus the
/// content-hash intern table that realizes the `Arc`-identity dedup (a
/// recomputed fragment whose bytes equal ANY retained fragment reuses that
/// allocation instead of retaining a second copy).
pub struct ConstructionFragmentStore<B: FragmentStoreBackend> {
    backend: B,
    /// content hash → interned handles with that hash (byte-verified on reuse,
    /// so a hash collision stores both fragments rather than aliasing them).
    intern: HashMap<[u8; 32], Vec<FragmentHandle>>,
    /// Total content-level dedup hits (a recomputed payload byte-equal to an
    /// already-interned fragment) since construction.
    content_dedup_hits: u64,
}

impl<B: FragmentStoreBackend> Default for ConstructionFragmentStore<B> {
    fn default() -> Self {
        Self::new()
    }
}

impl<B: FragmentStoreBackend> ConstructionFragmentStore<B> {
    /// An empty store.
    pub fn new() -> Self {
        Self {
            backend: B::empty(),
            intern: HashMap::new(),
            content_dedup_hits: 0,
        }
    }

    /// The container (read access for tests/accounting).
    pub fn backend(&self) -> &B {
        &self.backend
    }

    /// A retained snapshot of the container ([`FragmentStoreBackend::snapshot`]).
    pub fn snapshot(&self) -> B {
        self.backend.snapshot()
    }

    /// Total content-level dedup hits since construction.
    pub fn content_dedup_hits(&self) -> u64 {
        self.content_dedup_hits
    }

    /// Intern `bytes` under its content hash: byte-equal retained content
    /// reuses the existing `Arc` (a content dedup hit); fresh content allocates
    /// and registers one.
    fn intern_fragment(
        &mut self,
        family: &str,
        root_op: &str,
        rule_label: &str,
        bytes: Vec<u8>,
    ) -> FragmentHandle {
        let content_hash = content_digest(&bytes);
        if let Some(candidates) = self.intern.get(&content_hash) {
            if let Some(existing) = candidates
                .iter()
                .find(|candidate| candidate.bytes() == bytes.as_slice())
            {
                // The payload embeds the key parts, so content equality implies
                // key equality — reuse can never alias two keys.
                debug_assert_eq!(existing.key_parts(), (family, root_op, rule_label));
                self.content_dedup_hits += 1;
                return existing.clone();
            }
        }
        let handle = FragmentHandle::new(
            family.to_string(),
            root_op.to_string(),
            rule_label.to_string(),
            bytes,
        );
        self.intern
            .entry(content_hash)
            .or_default()
            .push(handle.clone());
        handle
    }

    /// Derive + store one rule fragment (returns the displaced fragment).
    fn store_rule_fragment(
        &mut self,
        artifacts: &CompiledInRhoArtifacts,
        family: &str,
        fact: &EntryFact,
        group_members: &[String],
    ) -> Result<Option<FragmentHandle>, String> {
        let rewrite = &artifacts.def.rewrites[fact.rewrite_index];
        let pattern = convert_lhs_pattern(&rewrite.left).map_err(|reject| {
            format!("rule `{}` has no automaton image: {reject:?}", fact.label)
        })?;
        let accept_channel = accept_channel_for(artifacts, fact.rewrite_index)?;
        let bytes = encode_rule_fragment(
            family,
            &fact.label,
            &fact.root_op,
            &pattern,
            &accept_channel,
            group_members,
        );
        let handle = self.intern_fragment(family, &fact.root_op, &fact.label, bytes);
        let key = rule_key(family, &fact.root_op, &fact.label);
        Ok(self.backend.set(&key, handle))
    }

    /// Seed the store from a BASE family's artifacts: one fragment per
    /// automaton entry plus the manifest (the base bring-up — setup work in the
    /// harness, outside every timed region).
    pub fn seed_from_artifacts(
        &mut self,
        artifacts: &CompiledInRhoArtifacts,
    ) -> Result<SeedReport, String> {
        let facts = entry_facts(artifacts)?;
        let family = artifacts.def.name.to_string();
        let mut inserted = 0usize;
        for fact in &facts {
            let group_members: Vec<String> = facts
                .iter()
                .filter(|other| other.root_op == fact.root_op)
                .map(|other| other.label.clone())
                .collect();
            if self
                .store_rule_fragment(artifacts, &family, fact, &group_members)?
                .is_none()
            {
                inserted += 1;
            }
        }
        let manifest = manifest_bytes(artifacts, &family);
        let handle = self.intern_fragment(&family, "", "", manifest);
        if self.backend.set(&manifest_key(&family), handle).is_none() {
            inserted += 1;
        }
        Ok(SeedReport {
            inserted,
            store_entries: self.backend.len(),
        })
    }

    /// Reconcile the store with `artifacts` after ONE appended rewrite whose
    /// LHS root op is `dirty_root_op`: recompute EXACTLY the dirty root-op
    /// group's fragments and the manifest, count what actually changed (byte
    /// comparison against the retained content), keep every unchanged `Arc`,
    /// and leave every other group UNTOUCHED — the H4v2 precision claim.
    pub fn reconcile_append(
        &mut self,
        artifacts: &CompiledInRhoArtifacts,
        dirty_root_op: &str,
    ) -> Result<AppendReport, String> {
        let facts = entry_facts(artifacts)?;
        let family = artifacts.def.name.to_string();

        let prefix = group_prefix(&family, dirty_root_op);
        let previous = self.backend.group_entries(&prefix);
        let group_before = previous.len();

        let members: Vec<&EntryFact> = facts
            .iter()
            .filter(|fact| fact.root_op == dirty_root_op)
            .collect();
        let group_after = members.len();
        let member_labels: Vec<String> =
            members.iter().map(|member| member.label.clone()).collect();

        let mut invalidated_existing = 0usize;
        let mut inserted_new = 0usize;
        let mut unchanged_group = 0usize;
        let mut after_keys: HashSet<Vec<u8>> = HashSet::with_capacity(members.len());
        for member in &members {
            let key = rule_key(&family, &member.root_op, &member.label);
            after_keys.insert(key.clone());
            let rewrite = &artifacts.def.rewrites[member.rewrite_index];
            let pattern = convert_lhs_pattern(&rewrite.left).map_err(|reject| {
                format!("rule `{}` has no automaton image: {reject:?}", member.label)
            })?;
            let accept_channel = accept_channel_for(artifacts, member.rewrite_index)?;
            let bytes = encode_rule_fragment(
                &family,
                &member.label,
                &member.root_op,
                &pattern,
                &accept_channel,
                &member_labels,
            );
            match self.backend.get(&key) {
                Some(existing) if existing.bytes() == bytes.as_slice() => {
                    // Unchanged: the retained Arc stays — NOT an invalidation.
                    unchanged_group += 1;
                },
                Some(_) => {
                    let handle =
                        self.intern_fragment(&family, &member.root_op, &member.label, bytes);
                    self.backend.set(&key, handle);
                    invalidated_existing += 1;
                },
                None => {
                    let handle =
                        self.intern_fragment(&family, &member.root_op, &member.label, bytes);
                    self.backend.set(&key, handle);
                    inserted_new += 1;
                },
            }
        }

        // Group keys that left the extended def (none on an append-only ladder).
        let mut invalidated_removed = 0usize;
        for (key, _) in &previous {
            if !after_keys.contains(key) {
                self.backend.remove(key);
                invalidated_removed += 1;
            }
        }

        // The manifest — the ONE fingerprint-dependent fragment (the "+ 1").
        let manifest = manifest_bytes(artifacts, &family);
        let manifest_slot = manifest_key(&family);
        let manifest_invalidated = match self.backend.get(&manifest_slot) {
            Some(existing) if existing.bytes() == manifest.as_slice() => 0,
            _ => {
                let handle = self.intern_fragment(&family, "", "", manifest);
                self.backend.set(&manifest_slot, handle);
                1
            },
        };

        Ok(AppendReport {
            group_before,
            group_after,
            invalidated_existing,
            invalidated_removed,
            manifest_invalidated,
            inserted_new,
            unchanged_group,
            store_entries: self.backend.len(),
        })
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Metric (i): retained-byte accounting across the ladder's snapshots.
// ─────────────────────────────────────────────────────────────────────────────

/// The deterministic retention accounting of a ladder's snapshots
/// (metric (i) — pure byte arithmetic, NEVER RSS).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LadderAccounting {
    /// Snapshots walked.
    pub snapshots: usize,
    /// Fragment references across all snapshots (Σ per-snapshot entry counts).
    pub total_fragment_refs: u64,
    /// Distinct `Arc<Fragment>` allocations across all snapshots.
    pub distinct_fragments: u64,
    /// `total_fragment_refs − distinct_fragments` — references served by
    /// sharing instead of retention.
    pub dedup_hits: u64,
    /// Metric (i) treatment: Σ of `bytes().len()` over DISTINCT allocations.
    pub retained_fragment_bytes: u64,
    /// Metric (i) baseline: the per-variant whole-artifact retention — Σ over
    /// snapshots of Σ of every entry's `bytes().len()` (every variant retains
    /// full copies; framing/keys excluded on BOTH sides — conservative).
    pub whole_artifact_bytes: u64,
}

impl LadderAccounting {
    /// The H4v2 (i) predicate: deduped retained bytes strictly below the
    /// per-variant whole-artifact retention.
    pub fn retained_lt_whole_artifact(&self) -> bool {
        self.retained_fragment_bytes < self.whole_artifact_bytes
    }
}

/// Walk `snapshots` and compute [`LadderAccounting`]: dedup by `Arc` identity
/// (`Arc::as_ptr`), sum distinct payload lengths (treatment) and per-variant
/// payload lengths (baseline).
pub fn ladder_accounting<B: FragmentStoreBackend>(snapshots: &[B]) -> LadderAccounting {
    let mut seen: HashSet<usize> = HashSet::new();
    let mut total_fragment_refs = 0u64;
    let mut retained_fragment_bytes = 0u64;
    let mut whole_artifact_bytes = 0u64;
    for snapshot in snapshots {
        for (_, fragment) in snapshot.entries() {
            total_fragment_refs += 1;
            whole_artifact_bytes += fragment.bytes().len() as u64;
            if seen.insert(fragment.arc_identity()) {
                retained_fragment_bytes += fragment.bytes().len() as u64;
            }
        }
    }
    let distinct_fragments = seen.len() as u64;
    LadderAccounting {
        snapshots: snapshots.len(),
        total_fragment_refs,
        distinct_fragments,
        dedup_hits: total_fragment_refs - distinct_fragments,
        retained_fragment_bytes,
        whole_artifact_bytes,
    }
}

#[cfg(test)]
#[path = "../tests/support/rho_net_fragment_pattern_recursive_oracle.rs"]
mod pattern_recursive_oracle;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rho_net_cache::cached_in_rho_artifacts;
    use crate::rho_net_incremental::{extend_in_rho_artifacts, IncrementalExtendOutcome};
    use proptest::prelude::*;

    /// A handle from raw parts (tests only — production handles come from the
    /// intern path, which embeds the key in the payload).
    fn test_handle(bytes: &[u8]) -> FragmentHandle {
        FragmentHandle::new("Fam".to_string(), "Op".to_string(), "Rule".to_string(), bytes.to_vec())
    }

    /// Resolve an [`AlgebraicResult`] against its operands (the lattice ops
    /// here always produce `Identity` — asserted).
    fn resolve(
        result: AlgebraicResult<FragmentHandle>,
        a: &FragmentHandle,
        b: &FragmentHandle,
    ) -> FragmentHandle {
        match result {
            AlgebraicResult::Identity(mask) => {
                assert_ne!(mask, 0, "identity masks are non-zero");
                if mask & SELF_IDENT != 0 {
                    a.clone()
                } else {
                    b.clone()
                }
            },
            AlgebraicResult::Element(_) => {
                panic!("the content lattice's results are always one of the operands")
            },
            AlgebraicResult::None => panic!("a total lattice never annihilates"),
        }
    }

    // ── Key encoding ─────────────────────────────────────────────────────────

    #[test]
    fn key_encoding_is_prefix_injective() {
        // The group prefix is a byte prefix of exactly its own group's keys.
        let key = rule_key("Fam", "R0", "M0");
        assert!(key.starts_with(&group_prefix("Fam", "R0")));
        assert!(!key.starts_with(&group_prefix("Fam", "R00")));
        // A root op that EXTENDS another (`R0` vs `R00`) cannot alias groups:
        // the length prefixes differ first.
        let key00 = rule_key("Fam", "R00", "M0");
        assert!(!key00.starts_with(&group_prefix("Fam", "R0")));
        // Distinct key parts encode to distinct keys even when concatenations
        // collide ("ab"+"c" vs "a"+"bc").
        assert_ne!(rule_key("Fam", "ab", "c"), rule_key("Fam", "a", "bc"));
        // The manifest key falls under NO real group prefix and collides with
        // no rule key (empty segments are reserved).
        let manifest = manifest_key("Fam");
        assert!(!manifest.starts_with(&group_prefix("Fam", "R0")));
        assert_ne!(manifest, rule_key("Fam", "R0", "M0"));
        assert!(manifest.starts_with(&group_prefix("Fam", "")));
    }

    // ── The EM-8 content-hash-equality Lattice ───────────────────────────────

    #[test]
    fn content_equal_fragments_are_mutual_identities() {
        let a = test_handle(b"payload");
        let b = test_handle(b"payload");
        assert_eq!(a, b, "content equality is the handle equality");
        assert!(!std::ptr::eq(Arc::as_ptr(&a.0), Arc::as_ptr(&b.0)), "distinct allocations");
        assert_eq!(a.pjoin(&b), AlgebraicResult::Identity(SELF_IDENT | COUNTER_IDENT));
        assert_eq!(a.pmeet(&b), AlgebraicResult::Identity(SELF_IDENT | COUNTER_IDENT));
    }

    #[test]
    fn unequal_fragments_resolve_by_the_total_order() {
        let a = test_handle(b"alpha");
        let b = test_handle(b"beta");
        let join = resolve(a.pjoin(&b), &a, &b);
        let join_flipped = resolve(b.pjoin(&a), &b, &a);
        assert_eq!(join, join_flipped, "pjoin commutes");
        let meet = resolve(a.pmeet(&b), &a, &b);
        let meet_flipped = resolve(b.pmeet(&a), &b, &a);
        assert_eq!(meet, meet_flipped, "pmeet commutes");
        assert_ne!(join, meet, "distinct content splits max from min");
        // Join and meet partition the operand pair.
        assert!(join == a || join == b);
        assert!(meet == a || meet == b);
    }

    proptest! {
        /// Lattice laws over arbitrary content: idempotence, commutativity,
        /// associativity, absorption — and mask honesty (a both-bits identity
        /// asserts operand equality).
        #[test]
        fn lattice_laws_hold(
            a_bytes in proptest::collection::vec(any::<u8>(), 0..48),
            b_bytes in proptest::collection::vec(any::<u8>(), 0..48),
            c_bytes in proptest::collection::vec(any::<u8>(), 0..48),
        ) {
            let a = test_handle(&a_bytes);
            let b = test_handle(&b_bytes);
            let c = test_handle(&c_bytes);

            // Idempotence: x ⊔ x = x = x ⊓ x (mutual identity).
            prop_assert_eq!(a.pjoin(&a), AlgebraicResult::Identity(SELF_IDENT | COUNTER_IDENT));
            prop_assert_eq!(a.pmeet(&a), AlgebraicResult::Identity(SELF_IDENT | COUNTER_IDENT));

            // Mask honesty: both bits set ⇒ the operands are equal in fact.
            if let AlgebraicResult::Identity(mask) = a.pjoin(&b) {
                if mask & SELF_IDENT != 0 && mask & COUNTER_IDENT != 0 {
                    prop_assert_eq!(&a, &b);
                }
            }

            // Commutativity.
            prop_assert_eq!(
                resolve(a.pjoin(&b), &a, &b),
                resolve(b.pjoin(&a), &b, &a)
            );
            prop_assert_eq!(
                resolve(a.pmeet(&b), &a, &b),
                resolve(b.pmeet(&a), &b, &a)
            );

            // Associativity.
            let ab = resolve(a.pjoin(&b), &a, &b);
            let bc = resolve(b.pjoin(&c), &b, &c);
            prop_assert_eq!(
                resolve(ab.pjoin(&c), &ab, &c),
                resolve(a.pjoin(&bc), &a, &bc)
            );
            let ab_meet = resolve(a.pmeet(&b), &a, &b);
            let bc_meet = resolve(b.pmeet(&c), &b, &c);
            prop_assert_eq!(
                resolve(ab_meet.pmeet(&c), &ab_meet, &c),
                resolve(a.pmeet(&bc_meet), &a, &bc_meet)
            );

            // Absorption: x ⊔ (x ⊓ y) = x and x ⊓ (x ⊔ y) = x.
            let meet_ab = resolve(a.pmeet(&b), &a, &b);
            prop_assert_eq!(resolve(a.pjoin(&meet_ab), &a, &meet_ab), a.clone());
            let join_ab = resolve(a.pjoin(&b), &a, &b);
            prop_assert_eq!(resolve(a.pmeet(&join_ab), &a, &join_ab), a.clone());
        }
    }

    #[test]
    fn pathmap_join_dedupes_content_equal_values_through_the_lattice() {
        // The Lattice through the container: two maps holding content-equal
        // fragments at the same path join to ONE entry whose content equals
        // both (the Identity path — no new allocation for the value).
        let mut left: PathMap<FragmentHandle> = PathMap::new();
        let mut right: PathMap<FragmentHandle> = PathMap::new();
        let shared_left = test_handle(b"shared");
        let shared_right = test_handle(b"shared");
        left.set_val_at(b"k", shared_left.clone());
        right.set_val_at(b"k", shared_right);
        left.set_val_at(b"only-left", test_handle(b"L"));
        right.set_val_at(b"only-right", test_handle(b"R"));
        let joined = left.join(&right);
        assert_eq!(joined.val_count(), 3);
        let at_k = joined
            .get_val_at(b"k")
            .expect("the shared path survives the join");
        assert_eq!(at_k, &shared_left, "the joined value is the shared content");
    }

    // ── Backend parity + store/lookup/invalidate ─────────────────────────────

    /// The IncrSmoke-scale base (mirrors `rho_net_incremental::tests`): two
    /// rules over distinct roots.
    const STORE_BASE_SOURCE: &str = r#"
        name: E6bStoreSmoke,
        types { Proc }
        terms {
            Wrap . x:Proc |- "wrap" "(" x ")" : Proc ;
            S . x:Proc |- "s" "(" x ")" : Proc ;
            R0 . x:Proc |- "r0" "(" x ")" : Proc ;
            R1 . x:Proc |- "r1" "(" x ")" : Proc ;
        }
        equations {}
        rewrites {
            M0 . |- (R0 (S x)) ~> (Wrap x) ;
            M1 . |- (R1 (S x)) ~> (Wrap x) ;
        }
    "#;

    const STORE_APPEND_FRAGMENT: &str = "MX0 . |- (R0 (S (S x))) ~> (Wrap x) ;";

    /// Everything [`seeded_append_run`] hands back, in order: the seed report, the append
    /// report, the backend's `(key, fragment-bytes)` entries, the ladder accounting, and
    /// the content-dedup hit count. Every component is `Send`, which is what lets a caller
    /// compute the whole run on a fresh thread (fresh artifact cache) and carry the result
    /// across the `join`; the artifacts themselves are `!Send` and stay on that thread.
    type SeededAppendRun =
        (SeedReport, AppendReport, Vec<(Vec<u8>, Vec<u8>)>, LadderAccounting, u64);

    /// Seed + append one rewrite through BOTH the incremental pipeline and the
    /// store under backend `B`; return the `Send`-safe observables.
    fn seeded_append_run<B: FragmentStoreBackend>() -> SeededAppendRun {
        let base = cached_in_rho_artifacts(STORE_BASE_SOURCE).expect("the base derives");
        let mut store: ConstructionFragmentStore<B> = ConstructionFragmentStore::new();
        let seed = store.seed_from_artifacts(&base).expect("the base seeds");
        let mut snapshots = vec![store.snapshot()];
        let outcome =
            extend_in_rho_artifacts(&base, STORE_APPEND_FRAGMENT).expect("the append derives");
        let artifacts = match outcome {
            IncrementalExtendOutcome::Incremental(artifacts) => artifacts,
            IncrementalExtendOutcome::FellBack { reason, .. } => {
                panic!("the base-shape append must take the incremental path, fell back: {reason}")
            },
        };
        let dirty = appended_rule_root_op(&artifacts).expect("the appended entry has a root op");
        assert_eq!(dirty, "R0");
        let report = store
            .reconcile_append(&artifacts, &dirty)
            .expect("the append reconciles");
        snapshots.push(store.snapshot());
        let entries: Vec<(Vec<u8>, Vec<u8>)> = store
            .backend()
            .entries()
            .into_iter()
            .map(|(key, fragment)| (key, fragment.bytes().to_vec()))
            .collect();
        let accounting = ladder_accounting(&snapshots);
        (seed, report, entries, accounting, store.content_dedup_hits())
    }

    #[test]
    fn seed_and_append_reconcile_exactly() {
        // Fresh thread: fresh artifact cache (the store consumes the same
        // thread-local artifact surface as the harness).
        std::thread::spawn(|| {
            let (seed, report, _, accounting, content_hits) =
                seeded_append_run::<PathMapFragmentStore>();
            // Seed: 2 rule fragments + 1 manifest.
            assert_eq!(seed, SeedReport { inserted: 3, store_entries: 3 });
            // Append MX0 (root R0): group before = {M0}; after = {M0, MX0};
            // M0's fragment genuinely changes (its group list grew), MX0 is a
            // fresh insert, the manifest changes (fingerprint taint).
            assert_eq!(report.group_before, 1);
            assert_eq!(report.group_after, 2);
            assert_eq!(report.invalidated_existing, 1);
            assert_eq!(report.invalidated_removed, 0);
            assert_eq!(report.manifest_invalidated, 1);
            assert_eq!(report.inserted_new, 1);
            assert_eq!(report.unchanged_group, 0);
            assert_eq!(report.store_entries, 4);
            assert_eq!(report.expected_invalidated(), 2);
            assert_eq!(report.actual_invalidated(), 2);
            assert!(report.invalidation_exact());
            // Accounting: snapshots hold 3 + 4 = 7 refs; distinct = 3 seed +
            // 3 append versions (M0', MX0, manifest') = 6; the untouched M1
            // fragment is the ONE shared allocation.
            assert_eq!(accounting.snapshots, 2);
            assert_eq!(accounting.total_fragment_refs, 7);
            assert_eq!(accounting.distinct_fragments, 6);
            assert_eq!(accounting.dedup_hits, 1);
            assert!(accounting.retained_lt_whole_artifact());
            assert_eq!(content_hits, 0, "no payload recurs in this ladder");
        })
        .join()
        .expect("the fresh-thread probe completes");
    }

    #[test]
    fn backends_are_semantically_identical() {
        // The (iii) twin discipline: both backends run the SAME reconciliation
        // and end with byte-identical entry sets and identical reports.
        let pathmap_run = std::thread::spawn(seeded_append_run::<PathMapFragmentStore>)
            .join()
            .expect("the pathmap-arm thread completes");
        let hashmap_run = std::thread::spawn(seeded_append_run::<HashMapFragmentStore>)
            .join()
            .expect("the hashmap-arm thread completes");
        assert_eq!(pathmap_run.0, hashmap_run.0, "seed reports agree");
        assert_eq!(pathmap_run.1, hashmap_run.1, "append reports agree");
        assert_eq!(pathmap_run.2, hashmap_run.2, "entry sets are byte-identical");
        assert_eq!(pathmap_run.3, hashmap_run.3, "accounting agrees");
        assert_eq!(pathmap_run.4, hashmap_run.4, "content dedup hits agree");
    }

    #[test]
    fn reconcile_without_a_change_invalidates_nothing() {
        // "Count what actually invalidates": re-reconciling the SAME artifacts
        // observes zero invalidations (every recomputed payload byte-equals the
        // retained one; the old Arcs stay). The registered expectation formula
        // applies to a REAL append, not to a no-op reconcile.
        std::thread::spawn(|| {
            let base = cached_in_rho_artifacts(STORE_BASE_SOURCE).expect("the base derives");
            let mut store: ConstructionFragmentStore<PathMapFragmentStore> =
                ConstructionFragmentStore::new();
            store.seed_from_artifacts(&base).expect("the base seeds");
            let before = store.backend().entries();
            let report = store
                .reconcile_append(&base, "R0")
                .expect("the no-op reconciles");
            assert_eq!(report.group_before, 1);
            assert_eq!(report.group_after, 1);
            assert_eq!(report.actual_invalidated(), 0, "nothing actually invalidated");
            assert_eq!(report.unchanged_group, 1);
            assert_eq!(report.inserted_new, 0);
            let after = store.backend().entries();
            assert_eq!(before.len(), after.len());
            for ((key_before, frag_before), (key_after, frag_after)) in
                before.iter().zip(after.iter())
            {
                assert_eq!(key_before, key_after);
                assert_eq!(
                    frag_before.arc_identity(),
                    frag_after.arc_identity(),
                    "unchanged fragments keep their allocation"
                );
            }
        })
        .join()
        .expect("the fresh-thread probe completes");
    }

    #[test]
    fn group_entries_and_removal_are_prefix_scoped() {
        // store/lookup/invalidate on the raw backend surface: group enumeration
        // sees exactly its own group; group removal leaves every other key.
        let mut store: ConstructionFragmentStore<PathMapFragmentStore> =
            ConstructionFragmentStore::new();
        for (root, label, payload) in [("R0", "M0", "a"), ("R0", "MX0", "b"), ("R1", "M1", "c")] {
            let handle = store.intern_fragment("Fam", root, label, payload.as_bytes().to_vec());
            store.backend.set(&rule_key("Fam", root, label), handle);
        }
        let manifest = store.intern_fragment("Fam", "", "", b"manifest".to_vec());
        store.backend.set(&manifest_key("Fam"), manifest);
        assert_eq!(store.backend().len(), 4);

        let r0 = store.backend().group_entries(&group_prefix("Fam", "R0"));
        assert_eq!(r0.len(), 2);
        assert!(r0
            .iter()
            .all(|(key, _)| key.starts_with(&group_prefix("Fam", "R0"))));
        let r1 = store.backend().group_entries(&group_prefix("Fam", "R1"));
        assert_eq!(r1.len(), 1);

        // Point removal (the invalidation primitive the reconciler uses).
        let removed = store.backend.remove(&rule_key("Fam", "R0", "M0"));
        assert!(removed.is_some());
        assert_eq!(store.backend().len(), 3);
        assert_eq!(
            store
                .backend()
                .group_entries(&group_prefix("Fam", "R0"))
                .len(),
            1
        );
        assert!(store.backend().get(&rule_key("Fam", "R1", "M1")).is_some());
        assert!(store.backend().get(&manifest_key("Fam")).is_some());
    }

    #[test]
    fn intern_dedupes_recurring_content_by_arc_identity() {
        let mut store: ConstructionFragmentStore<HashMapFragmentStore> =
            ConstructionFragmentStore::new();
        let first = store.intern_fragment("Fam", "R0", "M0", b"same".to_vec());
        assert_eq!(store.content_dedup_hits(), 0);
        let second = store.intern_fragment("Fam", "R0", "M0", b"same".to_vec());
        assert_eq!(store.content_dedup_hits(), 1);
        assert_eq!(first.arc_identity(), second.arc_identity(), "one retained allocation");
        let different = store.intern_fragment("Fam", "R0", "M0", b"other".to_vec());
        assert_eq!(store.content_dedup_hits(), 1);
        assert_ne!(first.arc_identity(), different.arc_identity());
    }

    #[test]
    fn accounting_counts_shared_allocations_once() {
        // Hand-built snapshots with known sharing: A appears in both snapshots
        // (one allocation), B is replaced by C.
        let mut store: ConstructionFragmentStore<HashMapFragmentStore> =
            ConstructionFragmentStore::new();
        let a = store.intern_fragment("Fam", "R0", "A", vec![0u8; 10]);
        let b = store.intern_fragment("Fam", "R1", "B", vec![1u8; 20]);
        store.backend.set(&rule_key("Fam", "R0", "A"), a);
        store.backend.set(&rule_key("Fam", "R1", "B"), b);
        let first = store.snapshot();
        let c = store.intern_fragment("Fam", "R1", "C", vec![2u8; 40]);
        store.backend.remove(&rule_key("Fam", "R1", "B"));
        store.backend.set(&rule_key("Fam", "R1", "C"), c);
        let second = store.snapshot();

        let accounting = ladder_accounting(&[first, second]);
        assert_eq!(accounting.snapshots, 2);
        assert_eq!(accounting.total_fragment_refs, 4);
        assert_eq!(accounting.distinct_fragments, 3, "A is shared, B and C are distinct");
        assert_eq!(accounting.dedup_hits, 1);
        assert_eq!(accounting.retained_fragment_bytes, 10 + 20 + 40);
        assert_eq!(accounting.whole_artifact_bytes, (10 + 20) + (10 + 40));
        assert!(accounting.retained_lt_whole_artifact());
    }
}
