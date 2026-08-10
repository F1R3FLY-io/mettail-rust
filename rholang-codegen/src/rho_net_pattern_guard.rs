//! Pattern-guard matcher engines shared by the production persistent-root PDA
//! and the benchmark-only Knotted-Topoi Appendix-A oracle.
//!
//! # What this is
//!
//! The `knotted-topoi` Appendix-A paper scheme, emitted LITERALLY: for each rule
//! `f(p_1,…,p_n) ~> R` and each subject position `ℓ` whose head is `f`, ONE
//! per-rule, per-site receiver
//!
//! ```text
//! for( f̲ <= loc(ℓ) ){                      ← persistent head-tag consume at the site
//!   for( g̲ <- loc(ℓ·(f,0)) ){ …           ← pre-order one-shot tag receives, one per
//!     …                                       non-var pattern node (expected tag per
//!     for( x ⃗ <- cap(ℓ·π) ){ …               NaiveGuardEncoding)
//!       accept!(σ_0,…,σ_{k-1}, @out)       ← the SAME accept ABI as the optimized
//!     } … }                                   network (build_accept_send, shared fn)
//! }
//! ```
//!
//! installed at EVERY head-matching position (the Appendix-A `∥_{ℓ : hd(ℓ)=f}`
//! comprehension), UNSHARED: the interned pattern DAG of the optimized emitter
//! ([`multi_pattern_receiver_network_par`](crate::multi_pattern_receiver_network_par))
//! is deliberately ignored — each compiled entry's pattern tree is walked
//! independently, each site gets its own full receiver, and same-prefix work is
//! duplicated. That duplication is the QUANTITY the Track-B benchmarks measure.
//!
//! # Equivalence by construction at the interfaces
//!
//! The naive emitter consumes the SAME [`InRhoMatchingRuleset`] the optimized
//! drivers consume (same compiled entries, same accept channels, same
//! fingerprint), reads the SAME compact spread ABI (every production channel
//! derives through the shared fixed-width position encoder), and emits its
//! innermost accept through the SAME [`build_accept_send`] function with the
//! SAME arguments — so the accept send is byte-identical to the optimized
//! network's and the downstream σ-receivers / firing contracts are shared
//! unchanged. Only the MATCHING NETWORK between the spread and the accept
//! differs.
//!
//! # Fail-closed admission ([`NaiveKtUnsupported`])
//!
//! The scheme is emitted only when it is KNOWN sound for a single spread:
//!
//! * [`NaiveKtUnsupported::VariableRootPattern`] — a bare-variable root has no
//!   head tag to demand (mirrors the optimized emitter's reject).
//! * [`NaiveKtUnsupported::NonLinearEntry`] — a repeated LHS variable needs a
//!   consistency join the paper scheme does not carry; the v1 benchmark corpus
//!   is linear, so repeats fail closed rather than mis-fire.
//! * [`NaiveKtUnsupported::OverlappingTagDemand`] — the naive analogue of the
//!   optimized locate-all's
//!   [`NestedEntryMultiSite`](crate::AutomatonUnsupported::NestedEntryMultiSite)
//!   contention gate; see the variant's rustdoc for the exact static condition.
//!
//! # Guard encodings ([`NaiveGuardEncoding`]) and the partial-fire hazard
//!
//! * [`PatternGuard`](NaiveGuardEncoding::PatternGuard) (default): the expected
//!   head tag IS the receive pattern, so the RSpace spatial matcher evaluates
//!   the equality and a non-matching tag message is simply never consumed —
//!   reject-safe at every level.
//! * [`ConsumeTest`](NaiveGuardEncoding::ConsumeTest) (paper-literal): the tag
//!   is bound FREE and tested by an explicit `Match` whose else-arm republishes
//!   the consumed tag. This carries a PARTIAL-FIRE hazard: when a LATER tag
//!   test in the chain fails, the tags already consumed by EARLIER receives in
//!   the same chain are NOT republished (their continuations hold them), so any
//!   other candidate receiver demanding one of those tags starves. Under the
//!   [`OverlappingTagDemand`](NaiveKtUnsupported::OverlappingTagDemand) gate no
//!   OTHER receiver ever demands them (single-candidate demand), which is why
//!   the gate is REQUIRED for this encoding; B2+ additionally restricts
//!   `ConsumeTest` to single-candidate subjects. The persistent ROOT receive
//!   never sees a mismatching tag (the install walk pre-filters by head), so
//!   the persistent-consume/republish livelock cannot arise from this emitter's
//!   own installs.
//!
//! # Production boundary
//!
//! The unshared per-step baseline remains reachable only through the
//! `bench-naive-baseline` crate exports.  The persistent R3 PDA is shared with
//! generated production invocations, but only after
//! [`persistent_root_drive_certificate`] proves its complete root-only sound
//! envelope; all other subjects retain the general quiescence driver.

#![cfg_attr(not(feature = "bench-naive-baseline"), allow(dead_code))]

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use dovetail::set_automaton::{AutomatonNode, PatternId, SetAutomatonView, SlotId};
use mettail_ast::language::LanguageDef;
use models::rhoapi::var::{VarInstance, WildcardMsg};
use models::rhoapi::{MatchCase, Par, Receive, ReceiveBind, Var};
use models::rust::rholang::implicits::GPrivateBuilder;
use models::rust::utils::{
    new_boundvar_par, new_elist_par, new_freevar_par, new_gstring_par, new_match_par, new_send_par,
    new_wildcard_par,
};

use crate::rho_net_automaton::{
    bits, build_accept_send, collect_nested_schedule, wrap_capture_chain, AutomatonUnsupported,
    Descent,
};
use crate::rho_net_drive::{
    drive_err_channel, drive_fired_channel, drive_fuel_channel, RhoNetDriveInvocation,
    RhoNetDriveStrategy,
};
use crate::rho_net_location::{
    compact_position_channel, MatcherPosition, SubjectLocationIndex, SubjectPosition,
};
use crate::rho_net_lower::{
    contextual_hole_bridge_par, contextual_premise_hole_channel, reflect_ground_term_par,
    reflect_tag, spread_term_par, GroundTerm, BOUND_VAR_REFLECT_LABEL, LAMBDA_REFLECT_LABEL,
    PEANO_ZERO_REFLECT_LABEL,
};
use crate::rho_net_ruleset::InRhoMatchingRuleset;
use crate::rho_net_subst_trs as trs;

/// How a naive receiver DEMANDS an expected head tag at a `loc:` channel.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NaiveGuardEncoding {
    /// The DEFAULT: the expected head tag appears as the RECEIVE PATTERN itself
    /// (`for(⌜op⌝ <- loc(ℓ))`, `free_count = 0`). The RSpace spatial matcher
    /// evaluates the tag equality, so a non-matching tag message is never
    /// consumed — reject-safe: a failed candidate leaves the spread intact for
    /// every other reader.
    PatternGuard,
    /// The PAPER-LITERAL encoding: the tag is bound FREE
    /// (`for(h <- loc(ℓ))`), and the continuation is wrapped in a `Match` on
    /// tag equality whose else-arm REPUBLISHES the consumed tag
    /// (`match h { ⌜op⌝ => … ; _ => loc(ℓ)!(h) }`). PARTIAL-FIRE HAZARD: a
    /// mismatch republishes only the tag consumed by the FAILING receive; the
    /// tags consumed by EARLIER receives of the same chain stay held by their
    /// continuations, so any other candidate demanding one of them starves.
    /// The [`OverlappingTagDemand`](NaiveKtUnsupported::OverlappingTagDemand)
    /// gate guarantees no such other candidate exists in an admitted ruleset;
    /// B2+ additionally restricts this encoding to single-candidate subjects.
    ConsumeTest,
}

/// Why the naive Knotted-Topoi scheme is NOT emitted for a ruleset — each
/// variant fails closed BEFORE any `Par` is built, never emitting a network
/// that could drop or mis-route a match.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NaiveKtUnsupported {
    /// An entry's LHS is a bare variable: it has no head constructor, so there
    /// is no head tag for the per-site receiver to demand (the naive mirror of
    /// [`AutomatonUnsupported::VariableRootPattern`](crate::AutomatonUnsupported::VariableRootPattern)).
    VariableRootPattern,
    /// An entry repeats an LHS variable. The paper scheme binds each Var leaf
    /// from its own `cap:` channel with no consistency comparison, so a repeat
    /// would silently accept mismatched subtrees; the v1 benchmark corpus is
    /// linear, and a non-linear entry fails closed here rather than mis-firing
    /// (the optimized emitter instead hosts flat repeats via its `eq:` join).
    NonLinearEntry,
    /// STATIC TAG-DEMAND OVERLAP — the naive analogue of the optimized
    /// locate-all's
    /// [`NestedEntryMultiSite`](crate::AutomatonUnsupported::NestedEntryMultiSite)
    /// contention gate. The spread publishes every node's head tag EXACTLY ONCE
    /// on its `loc:` channel; the scheme is sound only if no location message
    /// can have two candidate consumers. Two static shapes violate that:
    ///
    /// 1. NESTED-vs-ROOT (`demanding_entry ≠ root_entry` or, for a
    ///    self-recursive pattern like `f(f(x))`, the same entry): some entry's
    ///    NON-ROOT pattern-node op equals some entry's ROOT op. At any subject
    ///    position with that head, the first entry's descent receive and the
    ///    second entry's installed root receive demand the SAME single `loc:`
    ///    message — one starves, dropping a match the optimized network would
    ///    have made.
    /// 2. DUPLICATE ROOTS (two DISTINCT entries share a root op): both entries'
    ///    per-site receivers are installed at every shared candidate site and
    ///    demand that site's single head-tag message (and its once-published
    ///    `cap:` values); only one can fire, whereas the optimized network
    ///    SHARES the match and fans the accept out to every rule (O3). The
    ///    naive scheme is unshared BY DESIGN, so it cannot host this shape and
    ///    fails closed.
    ///
    /// β passes this gate: the internal `^lambda` op of
    /// `App(^lambda(fun), arg)` is not any entry's root op.
    OverlappingTagDemand {
        /// The head-constructor op both readers demand.
        op: String,
        /// The entry whose NON-ROOT pattern node (case 1) or duplicate root
        /// (case 2) raises the second demand.
        demanding_entry: PatternId,
        /// The entry whose ROOT op owns the first demand at that head.
        root_entry: PatternId,
    },
    /// R3 (self-driving) only: a subject constructor label collides with one of
    /// the reserved `^respread` rendezvous labels (`^respread` /
    /// `^respread-root` / `^respread-err`) — a walker arm for it would alias the
    /// walker's own channels, so the emitter fails closed.
    SelfDrivingReservedLabel {
        /// The colliding constructor label.
        op: String,
    },
    /// R3 (self-driving) only: the subject contains an AC operand COLLECTION
    /// node (`GroundTerm::coll_type = Some(_)`). The `^respread` walker is a
    /// POSITIONAL tagged-`EList` decomposer (the Appendix-A positional scheme's
    /// re-spread); an AC carrier has no positional spread to re-emit, so the
    /// emitter fails closed.
    SelfDrivingCollectionSubject {
        /// The collection node's constructor label.
        op: String,
    },
}

impl fmt::Display for NaiveKtUnsupported {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::VariableRootPattern => write!(
                f,
                "naive Knotted-Topoi baseline: a bare-variable root pattern has no head tag to demand"
            ),
            Self::NonLinearEntry => write!(
                f,
                "naive Knotted-Topoi baseline: a repeated LHS variable needs a consistency join \
                 the paper scheme does not carry (v1 corpus is linear)"
            ),
            Self::OverlappingTagDemand { op, demanding_entry, root_entry } => write!(
                f,
                "naive Knotted-Topoi baseline: entry {demanding_entry:?} demands head tag `{op}` \
                 also demanded by root entry {root_entry:?} — two readers for one location \
                 message would drop a match"
            ),
            Self::SelfDrivingReservedLabel { op } => write!(
                f,
                "naive Knotted-Topoi R3 (self-driving): subject constructor `{op}` collides with \
                 a reserved ^respread rendezvous label"
            ),
            Self::SelfDrivingCollectionSubject { op } => write!(
                f,
                "naive Knotted-Topoi R3 (self-driving): subject node `{op}` is an AC operand \
                 collection — the positional ^respread walker has no carrier re-spread"
            ),
        }
    }
}

/// Why the naive CONTEXTUAL driver fails closed: either one of the VERBATIM
/// context-shape checks mirrored from
/// [`contextual_match_call_par`](crate::contextual_match_call_par) (carrying
/// the same typed reason it would), or a naive per-ruleset admission gate.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NaiveKtContextualUnsupported {
    /// A context-shape check failed — the SAME check, with the SAME typed
    /// reason, the optimized [`contextual_match_call_par`](crate::contextual_match_call_par)
    /// fails closed with (0 or ≥2 contextual families, a premise/hole drift, or
    /// the located-redex/hole-position bijection).
    Context(AutomatonUnsupported),
    /// A naive admission gate rejected the ruleset (see [`NaiveKtUnsupported`]).
    Naive(NaiveKtUnsupported),
}

impl fmt::Display for NaiveKtContextualUnsupported {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Context(reason) => {
                write!(
                    f,
                    "naive Knotted-Topoi contextual driver: context shape check failed: {reason:?}"
                )
            },
            Self::Naive(reason) => write!(f, "{reason}"),
        }
    }
}

/// One entry's naive matching schedule at one site: the root op, the pre-order
/// descent list (every non-root, non-var pattern node with its `loc:` channel),
/// and the DFS capture list (every Var leaf's `cap:` channel) — collected
/// through the SAME [`collect_nested_schedule`] the optimized emitter uses, so
/// the orders (and therefore the accept's De Bruijn frame) agree by
/// construction.
struct NaiveEntrySchedule {
    root_op: String,
    root_channel: String,
    descents: Vec<Descent>,
    captures: Vec<String>,
}

/// Collect one entry's schedule at `site`, running the per-entry admission
/// gates: a Var root fails closed ([`NaiveKtUnsupported::VariableRootPattern`]),
/// a repeated Var name fails closed ([`NaiveKtUnsupported::NonLinearEntry`]).
fn collect_entry_schedule(
    view: &SetAutomatonView<'_, String>,
    entry: usize,
    locations: &SubjectLocationIndex<'_>,
    root_position: SubjectPosition,
    language_fingerprint: &str,
    root_site: &str,
) -> Result<NaiveEntrySchedule, NaiveKtUnsupported> {
    let root = view.entry_root_state(entry);
    match view.node(root) {
        AutomatonNode::Var => Err(NaiveKtUnsupported::VariableRootPattern),
        AutomatonNode::App { op, args } => {
            let root_op = op.to_string();
            let root_channel =
                locations.channel("loc", language_fingerprint, root_site, root_position);
            let mut descents: Vec<Descent> = Vec::new();
            let mut captures: Vec<String> = Vec::new();
            let mut capture_slots: Vec<SlotId> = Vec::new();
            for (index, arg) in args.iter().enumerate() {
                collect_nested_schedule(
                    view,
                    arg.state(),
                    arg.parent_slots().collect(),
                    locations,
                    root_site,
                    language_fingerprint,
                    locations.matcher_child(MatcherPosition::Live(root_position), index),
                    &mut descents,
                    &mut captures,
                    &mut capture_slots,
                );
            }
            let is_linear = capture_slots
                .iter()
                .enumerate()
                .all(|(i, slot)| !capture_slots[..i].contains(slot));
            if !is_linear {
                return Err(NaiveKtUnsupported::NonLinearEntry);
            }
            Ok(NaiveEntrySchedule {
                root_op,
                root_channel,
                descents,
                captures,
            })
        },
    }
}

/// Validate one entry's root and linearity without materializing subject
/// channels.  The explicit worklist counts positional Var occurrences; a
/// linear entry has exactly one occurrence per canonical root slot.
fn validate_naive_entry(
    view: &SetAutomatonView<'_, String>,
    entry: usize,
) -> Result<String, NaiveKtUnsupported> {
    let root = view.entry_root_state(entry);
    let root_op = match view.node(root) {
        AutomatonNode::Var => return Err(NaiveKtUnsupported::VariableRootPattern),
        AutomatonNode::App { op, .. } => op.to_string(),
    };
    let mut work = vec![root];
    let mut occurrences = 0usize;
    while let Some(state) = work.pop() {
        match view.node(state) {
            AutomatonNode::Var => occurrences += 1,
            AutomatonNode::App { args, .. } => {
                work.extend(args.iter().rev().map(|arg| arg.state()));
            },
        }
    }
    if occurrences != view.state_slot_count(root) {
        return Err(NaiveKtUnsupported::NonLinearEntry);
    }
    Ok(root_op)
}

/// Collect every op of the non-root App nodes of `state`'s subtree (the tags an
/// entry's DESCENT receives demand) — pre-order, duplicates kept (only set
/// membership matters to the gate, but keeping the walk total and order-stable
/// keeps the reported witness deterministic).
fn collect_non_root_ops(
    view: &SetAutomatonView<'_, String>,
    state: dovetail::set_automaton::StateId,
    ops: &mut Vec<String>,
) {
    let mut work = vec![state];
    while let Some(state) = work.pop() {
        match view.node(state) {
            AutomatonNode::Var => {},
            AutomatonNode::App { op, args } => {
                ops.push(op.to_string());
                work.extend(args.iter().rev().map(|arg| arg.state()));
            },
        }
    }
}

/// The RULESET-level admission gates, run BEFORE any emission:
///
/// 1. per-entry: Var root / non-linear entry via a channel-free structural
///    worklist;
/// 2. [`NaiveKtUnsupported::OverlappingTagDemand`]: no entry's NON-ROOT op may
///    equal any entry's ROOT op (nested-vs-root demand), and no two DISTINCT
///    entries may share a ROOT op (duplicate-root demand). See the variant's
///    rustdoc for why each shape drops a match under the once-published spread.
fn validate_naive_ruleset(view: &SetAutomatonView<'_, String>) -> Result<(), NaiveKtUnsupported> {
    let entry_count = view.entry_count();
    // Per-entry root op (also runs the Var-root + linearity gates).
    let mut root_ops: Vec<(PatternId, String)> = Vec::with_capacity(entry_count);
    for entry in 0..entry_count {
        root_ops.push((view.entry_id(entry), validate_naive_entry(view, entry)?));
    }
    // Duplicate roots: two DISTINCT entries sharing a root op.
    for (i, (pid_i, op_i)) in root_ops.iter().enumerate() {
        for (pid_j, op_j) in &root_ops[i + 1..] {
            if op_i == op_j {
                return Err(NaiveKtUnsupported::OverlappingTagDemand {
                    op: op_i.clone(),
                    demanding_entry: *pid_j,
                    root_entry: *pid_i,
                });
            }
        }
    }
    // Nested-vs-root: some entry's non-root op equals some entry's root op
    // (including the SAME entry — a self-recursive pattern like f(f(x))).
    for entry in 0..entry_count {
        let root = view.entry_root_state(entry);
        let mut non_root_ops: Vec<String> = Vec::new();
        if let AutomatonNode::App { args, .. } = view.node(root) {
            for arg in args {
                collect_non_root_ops(view, arg.state(), &mut non_root_ops);
            }
        }
        for op in &non_root_ops {
            if let Some((root_pid, _)) = root_ops.iter().find(|(_, root_op)| root_op == op) {
                return Err(NaiveKtUnsupported::OverlappingTagDemand {
                    op: op.clone(),
                    demanding_entry: view.entry_id(entry),
                    root_entry: *root_pid,
                });
            }
        }
    }
    Ok(())
}

/// One naive TAG receive on `loc_channel` demanding `op_tag`, wrapping the
/// CLOSED `closed_body` (`locally_free = {}` — the capture chain closes its own
/// σ binders below), per [`NaiveGuardEncoding`]:
///
/// * `PatternGuard`: `for(⌜op⌝ <-/<= loc){ body }` — the tag is the receive
///   pattern (`free_count = 0`, `bind_count = 0`), so the body's De Bruijn
///   frame passes through unshifted and the receive is closed.
/// * `ConsumeTest`: `for(h <-/<= loc){ match h { ⌜op⌝ => body ; _ => loc!(h) } }`
///   — one free bind (`h = BoundVar(0)`), a ground-tag case (`free_count = 0`)
///   running the closed body, and a wildcard else-arm republishing `h`; the
///   receive binds `h`, closing to `{}`.
///
/// `persistent` is `true` only for the ROOT tag receive (the Appendix-A rule
/// receiver is a persistent contract at its site); every descent is one-shot.
fn naive_tag_receive(
    loc_channel: &str,
    op_tag: Par,
    closed_body: Par,
    persistent: bool,
    encoding: NaiveGuardEncoding,
) -> Par {
    match encoding {
        NaiveGuardEncoding::PatternGuard => {
            let receive = Receive {
                binds: vec![ReceiveBind {
                    patterns: vec![op_tag],
                    source: Some(new_gstring_par(loc_channel.to_string(), Vec::new(), false)),
                    remainder: None,
                    free_count: 0,
                }],
                body: Some(closed_body),
                persistent,
                peek: false,
                bind_count: 0,
                locally_free: Vec::new(),
                connective_used: false,
                condition: None,
            };
            Par::default().with_receives(vec![receive])
        },
        NaiveGuardEncoding::ConsumeTest => {
            // Else-arm: republish the consumed tag `h = BoundVar(0)` on the SAME
            // location channel, so a non-matching tag is re-offered to the reader
            // it belongs to (see the partial-fire hazard note on the encoding).
            let republish = new_send_par(
                new_gstring_par(loc_channel.to_string(), Vec::new(), false),
                vec![new_boundvar_par(0, bits(&[0]), false)],
                false,
                bits(&[0]),
                false,
                bits(&[0]),
                false,
            );
            let cases = vec![
                MatchCase {
                    pattern: Some(op_tag),
                    source: Some(closed_body),
                    free_count: 0,
                    guard: None,
                },
                MatchCase {
                    pattern: Some(new_wildcard_par(Vec::new(), true)),
                    source: Some(republish),
                    free_count: 0,
                    guard: None,
                },
            ];
            let match_free = bits(&[0]);
            let match_par = new_match_par(
                new_boundvar_par(0, bits(&[0]), false),
                cases,
                match_free.clone(),
                false,
                match_free,
                false,
            );
            let receive = Receive {
                binds: vec![ReceiveBind {
                    patterns: vec![new_freevar_par(0, Vec::new())],
                    source: Some(new_gstring_par(loc_channel.to_string(), Vec::new(), false)),
                    remainder: None,
                    free_count: 1,
                }],
                body: Some(match_par),
                persistent,
                peek: false,
                bind_count: 1,
                locally_free: Vec::new(),
                connective_used: false,
                condition: None,
            };
            Par::default().with_receives(vec![receive])
        },
    }
}

/// ONE rule's Appendix-A receiver at ONE site: the outer PERSISTENT tag receive
/// on the site's spread root-location channel demanding the entry's root op,
/// the pre-order one-shot tag receives for every non-root, non-var pattern node
/// at its child `loc:` channel (deepest innermost — DFS-reverse wrap, matching
/// [`build_nested_case_body`](crate::rho_net_automaton) ordering), the DFS Var-leaf
/// captures on the `cap:` collapse channels (via the SHARED
/// [`wrap_capture_chain`], so the capture ABI — channels, order, De Bruijn
/// frame — is the automaton's), and innermost the SHARED [`build_accept_send`]
/// tuple `accept_channel!(σ_0,…,σ_{k-1}, @out)` — byte-identical to the
/// optimized network's accept, so the downstream σ-receivers / firing contracts
/// are shared unchanged.
///
/// Because every tag receive wraps a CLOSED body (and, for `ConsumeTest`, its
/// own `h` binder sits OUTSIDE the whole capture chain), the tag binders never
/// shift the capture frame: the accept's `σ_d = BoundVar(k-1-d)` indices are
/// the same under both encodings. The emitted receiver is a CLOSED `Par`
/// (`locally_free = {}`, no connectives at process position).
///
/// Fails closed per entry: [`NaiveKtUnsupported::VariableRootPattern`] /
/// [`NaiveKtUnsupported::NonLinearEntry`]. The RULESET-level
/// [`NaiveKtUnsupported::OverlappingTagDemand`] gate lives in the drivers
/// ([`naive_kt_match_call_par`] / [`naive_kt_contextual_match_call_par`]),
/// which validate BEFORE emitting any receiver.
pub fn naive_kt_entry_receiver_par(
    view: &SetAutomatonView<'_, String>,
    entry: usize,
    subject: &GroundTerm,
    site: &str,
    accept_channel: &str,
    out_channel: &str,
    language_fingerprint: &str,
    encoding: NaiveGuardEncoding,
) -> Result<Par, NaiveKtUnsupported> {
    let locations = SubjectLocationIndex::new(subject);
    naive_kt_entry_receiver_indexed_par(
        view,
        entry,
        &locations,
        SubjectPosition::ROOT,
        site,
        accept_channel,
        out_channel,
        language_fingerprint,
        encoding,
    )
}

fn naive_kt_entry_receiver_indexed_par(
    view: &SetAutomatonView<'_, String>,
    entry: usize,
    locations: &SubjectLocationIndex<'_>,
    root_position: SubjectPosition,
    root_site: &str,
    accept_channel: &str,
    out_channel: &str,
    language_fingerprint: &str,
    encoding: NaiveGuardEncoding,
) -> Result<Par, NaiveKtUnsupported> {
    let schedule = collect_entry_schedule(
        view,
        entry,
        locations,
        root_position,
        language_fingerprint,
        root_site,
    )?;
    // Linear entry: k distinct vars in DFS (first-occurrence) order, so
    // `first_occ = [0,…,k-1]` — the SAME arguments the optimized emitter passes
    // for a linear entry, making the accept send byte-identical by construction.
    let k = schedule.captures.len();
    let first_occ: Vec<usize> = (0..k).collect();
    let accept = build_accept_send(accept_channel, out_channel, k, &first_occ);
    let mut body = wrap_capture_chain(&schedule.captures, accept);
    for descent in schedule.descents.iter().rev() {
        let tag =
            GPrivateBuilder::new_par_from_string(reflect_tag(language_fingerprint, &descent.op));
        body = naive_tag_receive(&descent.loc_channel, tag, body, false, encoding);
    }
    let root_tag =
        GPrivateBuilder::new_par_from_string(reflect_tag(language_fingerprint, &schedule.root_op));
    Ok(naive_tag_receive(&schedule.root_channel, root_tag, body, true, encoding))
}

/// Collect the exact subject positions whose head constructor is `root_op`.
fn collect_entry_sites(
    locations: &SubjectLocationIndex<'_>,
    root_op: &str,
    sites: &mut Vec<SubjectPosition>,
) {
    locations.walk(SubjectPosition::ROOT, |position, node| {
        if node.constructor == root_op {
            sites.push(position);
        }
        true
    });
}

/// The accept channel of the compiled entry `pid` — an [`InRhoMatchingRuleset`]
/// invariant (`accept_channels` is built in lockstep with the compiled entries
/// and retained together), so a miss is an internal-coherence bug, not an
/// input-dependent failure.
fn entry_accept_channel(ruleset: &InRhoMatchingRuleset, pid: PatternId) -> &str {
    ruleset
        .accept_channels
        .iter()
        .find(|(entry_pid, _)| *entry_pid == pid)
        .map(|(_, channel)| channel.as_str())
        .expect(
            "InRhoMatchingRuleset invariant: every compiled automaton entry has an accept channel",
        )
}

/// Track B — the naive Appendix-A MATCH CALL: for each compiled entry with root
/// op `f`, walk `subject` and install that entry's [`naive_kt_entry_receiver_par`]
/// at EVERY position whose head is `f` (the Appendix-A `∥_{ℓ : hd(ℓ)=f}`
/// comprehension — the same walk shape as the optimized driver's
/// `collect_redex_sites`, but PER RULE and UNSHARED), then append ONE
/// [`spread_term_par`] of the whole subject at `root_site`. Returns the call and
/// the INSTALLED-RECEIVER COUNT (a benchmark metric: the naive scheme's
/// installed-network volume, vs. the optimized driver's shared per-site count).
///
/// All admission gates ([`NaiveKtUnsupported`]) run BEFORE any emission. The
/// non-positional dispatch families of the ruleset (`ac_dispatch`,
/// `structural_ac_dispatch`, `nested_structural_ac_dispatch`,
/// `contextual_dispatch`, and the native value bridges) are OUTSIDE the
/// Appendix-A positional scheme and are not driven by this call — the Track-B
/// positional workload families (flat, comb, nested, λ-chain) exercise only
/// automaton entries, and the contextual family has its own driver
/// ([`naive_kt_contextual_match_call_par`]).
pub fn naive_kt_match_call_par(
    ruleset: &InRhoMatchingRuleset,
    subject: &GroundTerm,
    root_site: &str,
    out_channel: &str,
    encoding: NaiveGuardEncoding,
) -> Result<(Par, usize), NaiveKtUnsupported> {
    let view = ruleset.automaton.view();
    validate_naive_ruleset(&view)?;
    let locations = SubjectLocationIndex::new(subject);

    let mut call = Par::default();
    let mut installed = 0usize;
    for entry in 0..view.entry_count() {
        let root_op = match view.node(view.entry_root_state(entry)) {
            AutomatonNode::App { op, .. } => op.to_string(),
            // Unreachable past `validate_naive_ruleset`, kept total + typed.
            AutomatonNode::Var => return Err(NaiveKtUnsupported::VariableRootPattern),
        };
        let accept_channel = entry_accept_channel(ruleset, view.entry_id(entry));
        let mut sites: Vec<SubjectPosition> = Vec::new();
        collect_entry_sites(&locations, &root_op, &mut sites);
        for &site in &sites {
            let receiver = naive_kt_entry_receiver_indexed_par(
                &view,
                entry,
                &locations,
                site,
                root_site,
                accept_channel,
                out_channel,
                &ruleset.language_fingerprint,
                encoding,
            )?;
            call = call.append(receiver);
        }
        installed += sites.len();
    }

    let spread = spread_term_par(subject, &ruleset.language_fingerprint, root_site);
    Ok((call.append(spread), installed))
}

/// Track B — the naive CONTEXTUAL match call: the VERBATIM mirror of
/// [`contextual_match_call_par`](crate::contextual_match_call_par)'s
/// hole-position derivation, located-redex bijection check, per-hole
/// [`contextual_hole_bridge_par`] wiring, and single trailing spread — with ONLY
/// the per-hole premise LOCATOR networks swapped from the shared automaton
/// network to naive per-entry receivers (out-routed to the hole's intermediate
/// [`contextual_premise_hole_channel`], exactly as the optimized driver routes
/// its per-hole accept targets). The installed persistent
/// [`contextual_join_receiver_par`](crate::contextual_join_receiver_par) is
/// untouched and shared: the bridges re-deliver each reduced hole on the SAME
/// premise channels in the SAME bind ABI, so the join reassembles ⟦K'⟧
/// identically for both emitters.
///
/// At each hole site exactly the head-matching entry's receiver is installed
/// (the Appendix-A comprehension restricted to the hole position; after the
/// duplicate-root gate at most one entry matches any head). The optimized
/// driver's flat-only co-install check (`NestedEntryMultiSite` for `n > 1`) is
/// REPLACED by the naive [`NaiveKtUnsupported::OverlappingTagDemand`] gate:
/// hole sites are distinct indexed sibling positions, so two per-hole naive
/// receivers can contend for a channel only through a nested-vs-root or
/// duplicate-root demand — exactly what the gate excludes statically.
pub fn naive_kt_contextual_match_call_par(
    ruleset: &InRhoMatchingRuleset,
    subject: &GroundTerm,
    root_site: &str,
    out_channel: &str,
    encoding: NaiveGuardEncoding,
) -> Result<Par, NaiveKtContextualUnsupported> {
    // ── VERBATIM context-shape mirror of `contextual_match_call_par` ─────────
    // Exactly one contextual family (the single congruence context to close).
    let [entry] = ruleset.contextual_dispatch.as_slice() else {
        return Err(NaiveKtContextualUnsupported::Context(
            AutomatonUnsupported::ContextualHoleMismatch,
        ));
    };
    let n = entry.premise_channels.len();
    if n == 0 || n != entry.hole_positions.len() {
        return Err(NaiveKtContextualUnsupported::Context(
            AutomatonUnsupported::ContextualHoleMismatch,
        ));
    }

    let locations = SubjectLocationIndex::new(subject);

    // The `n` expected hole sites in the SAME compact index used by spread.
    let expected_sites: Vec<SubjectPosition> = entry
        .hole_positions
        .iter()
        .map(|path| locations.resolve_path(SubjectPosition::ROOT, path))
        .collect::<Option<Vec<_>>>()
        .ok_or(NaiveKtContextualUnsupported::Context(
            AutomatonUnsupported::ContextualHoleMismatch,
        ))?;

    // LOAD-BEARING bijection check: the subject's located rule-root redexes must
    // be EXACTLY the `n` expected hole positions (as a multiset).
    let roots = crate::rule_lhs_root_constructors(ruleset);
    let mut located: Vec<SubjectPosition> = Vec::new();
    collect_ruleset_sites(&locations, &roots, &mut located);
    let mut located_sorted = located;
    located_sorted.sort();
    let mut expected_sorted = expected_sites.clone();
    expected_sorted.sort();
    if located_sorted != expected_sorted {
        return Err(NaiveKtContextualUnsupported::Context(
            AutomatonUnsupported::ContextualHoleMismatch,
        ));
    }

    // ── Naive admission gates (replacing the flat-only co-install check) ─────
    let view = ruleset.automaton.view();
    validate_naive_ruleset(&view).map_err(NaiveKtContextualUnsupported::Naive)?;

    // ── Per-hole: naive locator network + verbatim hole bridge ───────────────
    let mut call = Par::default();
    for (index, &expected_site) in expected_sites.iter().enumerate() {
        let premise_channel = &entry.premise_channels[index];
        let hole_channel = contextual_premise_hole_channel(premise_channel);

        // The subject's head at the hole (defensive: a drift fails closed).
        let hole_subterm = locations.term(expected_site);
        // Install the head-matching entry's receiver AT the hole site, its
        // accept routed to the hole's intermediate `ph:` channel (the join's
        // premise ABI is completed by the bridge below). After the
        // duplicate-root gate at most one entry matches; the bijection check
        // guarantees at least one does (the hole head is a rule root).
        for automaton_entry in 0..view.entry_count() {
            let root_op = match view.node(view.entry_root_state(automaton_entry)) {
                AutomatonNode::App { op, .. } => op.to_string(),
                AutomatonNode::Var => {
                    return Err(NaiveKtContextualUnsupported::Naive(
                        NaiveKtUnsupported::VariableRootPattern,
                    ))
                },
            };
            if root_op != hole_subterm.constructor {
                continue;
            }
            let accept_channel = entry_accept_channel(ruleset, view.entry_id(automaton_entry));
            let receiver = naive_kt_entry_receiver_indexed_par(
                &view,
                automaton_entry,
                &locations,
                expected_site,
                root_site,
                accept_channel,
                &hole_channel,
                &ruleset.language_fingerprint,
                encoding,
            )
            .map_err(NaiveKtContextualUnsupported::Naive)?;
            call = call.append(receiver);
        }

        // VERBATIM: the shared hole bridge (the LAST hole carries `@out`).
        let is_last = index + 1 == n;
        let bridge = contextual_hole_bridge_par(
            &hole_channel,
            premise_channel,
            if is_last { Some(out_channel) } else { None },
        );
        call = call.append(bridge);
    }

    // ONE spread of the whole subject — every hole locator reads its site's
    // channels from it.
    let spread = spread_term_par(subject, &ruleset.language_fingerprint, root_site);
    Ok(call.append(spread))
}

/// The multi-root site walk (every position whose head is one of `roots`) —
/// the same derivation as the optimized driver's `collect_redex_sites`,
/// re-stated here for the contextual bijection check (that function is private
/// to `rho_net_ruleset`; both walks consume [`SubjectLocationIndex`]'s exact
/// compact topology).
fn collect_ruleset_sites(
    locations: &SubjectLocationIndex<'_>,
    roots: &std::collections::BTreeSet<String>,
    sites: &mut Vec<SubjectPosition>,
) {
    locations.walk(SubjectPosition::ROOT, |position, node| {
        if roots.contains(&node.constructor) {
            sites.push(position);
        }
        true
    });
}

// ─────────────────────────────────────────────────────────────────────────────
// R3 — the persistent self-driving pattern-guard engine
// ─────────────────────────────────────────────────────────────────────────────
//
// USER-approved, PRE-REGISTERED, clearly-labeled EXPLORATORY column
// (Track B R3, 2026-07-19). It DEVIATES from the same-firing-contract
// constraint every measured column above observes — BY DESIGN: instead of one
// matcher session per rewrite step (the per-invocation architecture of the
// per-step `lambda_chain` drives; see
// `docs/benchmarks/data/sa-vs-naive/README.md`), the fired rule's REDUCT is
// re-spread IN-SESSION at the fired site, so the PERSISTENT Appendix-A root
// receiver keeps matching and a β chain normalizes in ONE injection. This is
// the paper's actual runtime model — the first probe of the regime where
// matching work SURVIVES across steps.

/// The reserved rendezvous label of the R3 `^respread` WALKER receiver
/// (`GPrivate(reflect_tag(fp, "^respread"))`): a 3-ary persistent contract
/// `^respread(t, loc, cap)` that decomposes one reflected node and emits its
/// spread sends (see [`respread_walker_receiver_par`]). `^`-prefixed, so it can
/// never collide with a user constructor (a Rust `Ident`).
pub const RESPREAD_RESERVED_LABEL: &str = "^respread";

/// The reserved rendezvous label of the R3 ROOT dispatcher
/// (`GPrivate(reflect_tag(fp, "^respread-root"))`): the 1-ary persistent
/// contract every R3 firing's reduct is DELIVERED to (the accept's dynamic
/// `out` slot), which either seeds a walk (redex-rooted reduct) or lands the
/// session normal form on OUT (see [`respread_root_receiver_par`]).
pub const RESPREAD_ROOT_RESERVED_LABEL: &str = "^respread-root";

/// The reserved FAIL-CLOSED error channel of the R3 walker family
/// (`GPrivate(reflect_tag(fp, "^respread-err"))`): any reflected node whose
/// head tag is outside the emitter-derived admitted constructor set is SENT
/// here (typed, resting — no receiver consumes it), never silently spread or
/// silently dropped. A test / driver reads the channel to observe the breach;
/// the session's OUT then fails its observed-value expectation loudly.
pub const RESPREAD_ERR_RESERVED_LABEL: &str = "^respread-err";

/// The three reserved `^respread`-family rendezvous labels, for the B4
/// counter classification (`bench_support`'s `respread_tau` bucket) — the
/// analogue of `reserved_subst_trs_labels` for the R3 walker family.
pub fn respread_reserved_labels() -> [&'static str; 3] {
    [
        RESPREAD_RESERVED_LABEL,
        RESPREAD_ROOT_RESERVED_LABEL,
        RESPREAD_ERR_RESERVED_LABEL,
    ]
}

/// Fixed-width identity carried by the R3 walker for one pattern constructor
/// state.  It is control data, not a channel name; the selected route owns the
/// exact compact `loc:`/`cap:` channels to publish.
fn selfdriving_route_key(position: u64) -> String {
    format!("@r2:{position:016x}")
}

fn allocate_selfdriving_position(next: &mut u64) -> u64 {
    assert!(
        *next < u64::MAX,
        "the R3 pattern-position index exhausted its u64 identity space"
    );
    let position = *next;
    *next += 1;
    position
}

enum SelfDrivingChild {
    /// The child is another constructor demanded by the pattern PDA.
    Descend { route_key: String },
    /// The child is a pattern variable: publish its already-reflected value
    /// directly, without traversing the captured subtree.
    Capture { channel: String },
}

struct SelfDrivingRoute {
    route_key: String,
    op: String,
    loc_channel: String,
    children: Vec<SelfDrivingChild>,
}

struct SelfDrivingEntry {
    pattern_id: PatternId,
    schedule: NaiveEntrySchedule,
}

struct SelfDrivingPlan {
    entries: Vec<SelfDrivingEntry>,
    routes: Vec<SelfDrivingRoute>,
    root_routes: BTreeMap<String, String>,
}

/// Compile the admitted rule patterns to a finite route PDA.  Every pattern
/// node receives one exact fixed-width identity; constructor nodes become
/// walker states and variable nodes become direct capture actions on their
/// parent transition.  The worklist is stack-safe and the retained plan is
/// linear in the pattern forest, independent of subject depth.
fn build_selfdriving_plan(
    view: &SetAutomatonView<'_, String>,
    language_fingerprint: &str,
    root_site: &str,
) -> Result<SelfDrivingPlan, NaiveKtUnsupported> {
    let mut next_position = 0u64;
    let mut entries = Vec::with_capacity(view.entry_count());
    let mut routes = Vec::new();
    let mut root_routes = BTreeMap::new();

    for entry in 0..view.entry_count() {
        let root_state = view.entry_root_state(entry);
        if matches!(view.node(root_state), AutomatonNode::Var) {
            return Err(NaiveKtUnsupported::VariableRootPattern);
        }

        let root_position = allocate_selfdriving_position(&mut next_position);
        let root_route_key = selfdriving_route_key(root_position);
        let mut schedule = NaiveEntrySchedule {
            root_op: String::new(),
            root_channel: compact_position_channel(
                "loc",
                language_fingerprint,
                root_site,
                root_position,
            ),
            descents: Vec::new(),
            captures: Vec::new(),
        };
        let mut pending = vec![(root_state, root_position, true)];

        while let Some((state, position, is_root)) = pending.pop() {
            match view.node(state) {
                AutomatonNode::Var => {
                    schedule.captures.push(compact_position_channel(
                        "cap",
                        language_fingerprint,
                        root_site,
                        position,
                    ));
                },
                AutomatonNode::App { op, args } => {
                    if is_root {
                        schedule.root_op = op.to_string();
                    } else {
                        schedule.descents.push(Descent {
                            loc_channel: compact_position_channel(
                                "loc",
                                language_fingerprint,
                                root_site,
                                position,
                            ),
                            op: op.to_string(),
                        });
                    }

                    let mut child_states = Vec::with_capacity(args.len());
                    let mut children = Vec::with_capacity(args.len());
                    for arg in args {
                        let child_position = allocate_selfdriving_position(&mut next_position);
                        let child_state = arg.state();
                        child_states.push((child_state, child_position, false));
                        children.push(match view.node(child_state) {
                            AutomatonNode::Var => SelfDrivingChild::Capture {
                                channel: compact_position_channel(
                                    "cap",
                                    language_fingerprint,
                                    root_site,
                                    child_position,
                                ),
                            },
                            AutomatonNode::App { .. } => SelfDrivingChild::Descend {
                                route_key: selfdriving_route_key(child_position),
                            },
                        });
                    }
                    pending.extend(child_states.into_iter().rev());
                    routes.push(SelfDrivingRoute {
                        route_key: selfdriving_route_key(position),
                        op: op.to_string(),
                        loc_channel: compact_position_channel(
                            "loc",
                            language_fingerprint,
                            root_site,
                            position,
                        ),
                        children,
                    });
                },
            }
        }

        let previous = root_routes.insert(schedule.root_op.clone(), root_route_key.clone());
        debug_assert!(previous.is_none(), "duplicate roots are rejected before route planning");
        entries.push(SelfDrivingEntry {
            pattern_id: view.entry_id(entry),
            schedule,
        });
    }

    Ok(SelfDrivingPlan { entries, routes, root_routes })
}

/// A HEAD-tag dispatch pattern `[⌜label⌝ ...]` — a tagged `EList` whose single
/// listed element is the ground tag and whose REMAINDER is a wildcard, so it
/// matches a reflected node of ANY arity with that head (the arity-erased
/// dispatch the `^respread-root` dispatcher needs: it routes on the head alone
/// and forwards the WHOLE node `t`, never destructuring children).
fn head_tag_remainder_pattern(language_fingerprint: &str, label: &str) -> Par {
    let wildcard_remainder = Var {
        var_instance: Some(VarInstance::Wildcard(WildcardMsg {})),
    };
    new_elist_par(
        vec![trs::tag_par(language_fingerprint, label)],
        Vec::new(),
        true,
        Some(wildcard_remainder),
        Vec::new(),
        true,
    )
}

/// [`build_accept_send`] with the trailing OUT slot replaced by an ARBITRARY
/// ground channel NAME `Par` (here: the `^respread-root` `GPrivate`). Byte-for-
/// byte the shared accept otherwise — same accept channel, same σ `BoundVar`
/// frame, same slot order — so the language's INSTALLED σ-receiver (which binds
/// `out` as its LAST formal and threads it dynamically: `sigma_receiver_par`
/// sends the reduct on `BoundVar(0)`; `subst_seed_receiver_par` threads it as
/// the β cascade's continuation) delivers the fired reduct TO THE DISPATCHER
/// with no change to the installed program. This is R3's ONE deviation from the
/// shared firing contract (pre-registered, by design): the reduct's DESTINATION
/// is the in-session dispatcher instead of the observation channel.
fn build_accept_send_to_name(
    accept_channel: &str,
    out_name: Par,
    arity: usize,
    first_occ: &[usize],
) -> Par {
    let mut data: Vec<Par> = first_occ
        .iter()
        .map(|&p| {
            let idx = arity - 1 - p;
            new_boundvar_par(idx as i32, bits(&[idx]), false)
        })
        .collect();
    data.push(out_name);
    let free_indices: Vec<usize> = first_occ.iter().map(|&p| arity - 1 - p).collect();
    let accept_free = bits(&free_indices);
    new_send_par(
        new_gstring_par(accept_channel.to_string(), Vec::new(), false),
        data,
        false,
        accept_free.clone(),
        false,
        accept_free,
        false,
    )
}

/// ONE entry's R3 receiver at the ROOT site: the SAME persistent-root /
/// one-shot-descent / capture-chain schedule as [`naive_kt_entry_receiver_par`]
/// (PatternGuard demand — R3 is PatternGuard-only), with the innermost accept
/// swapped to [`build_accept_send_to_name`] targeting the `^respread-root`
/// dispatcher. Deliberately NOT refactored into the frozen primary emitter
/// (its byte-shape is pinned by the pre-registered protocol's tests); the
/// ~15 duplicated lines are annotated against it.
fn selfdriving_entry_receiver_par(
    schedule: &NaiveEntrySchedule,
    accept_channel: &str,
    language_fingerprint: &str,
    fired_rule_label: Option<&str>,
) -> Par {
    // Linear entry ⇒ first_occ = [0,…,k-1] (see `naive_kt_entry_receiver_par`).
    let k = schedule.captures.len();
    let first_occ: Vec<usize> = (0..k).collect();
    let respread_root = trs::tag_par(language_fingerprint, RESPREAD_ROOT_RESERVED_LABEL);
    let mut accept = build_accept_send_to_name(accept_channel, respread_root, k, &first_occ);
    if let Some(rule_label) = fired_rule_label {
        let ledger = trs::send(
            trs::ground(new_gstring_par(
                drive_fired_channel(language_fingerprint),
                Vec::new(),
                false,
            )),
            vec![trs::ground(new_gstring_par(rule_label.to_string(), Vec::new(), false))],
        );
        accept = accept.append(ledger.par);
    }
    let mut body = wrap_capture_chain(&schedule.captures, accept);
    for descent in schedule.descents.iter().rev() {
        let tag =
            GPrivateBuilder::new_par_from_string(reflect_tag(language_fingerprint, &descent.op));
        body = naive_tag_receive(
            &descent.loc_channel,
            tag,
            body,
            false,
            NaiveGuardEncoding::PatternGuard,
        );
    }
    let root_tag =
        GPrivateBuilder::new_par_from_string(reflect_tag(language_fingerprint, &schedule.root_op));
    naive_tag_receive(
        &schedule.root_channel,
        root_tag,
        body,
        true,
        NaiveGuardEncoding::PatternGuard,
    )
}

/// Collect the subject's constructor labels (pre-order), running the R3
/// admission gates for AC carriers and reserved control labels. The set
/// classifies known non-redex roots for dispatcher termination; walker shapes
/// come exclusively from the pattern route PDA, so one label may safely occur
/// at multiple subject arities.
fn collect_selfdriving_labels(
    term: &GroundTerm,
    labels: &mut BTreeSet<String>,
) -> Result<(), NaiveKtUnsupported> {
    let mut work = vec![term];
    while let Some(term) = work.pop() {
        if term.coll_type.is_some() {
            return Err(NaiveKtUnsupported::SelfDrivingCollectionSubject {
                op: term.constructor.clone(),
            });
        }
        if respread_reserved_labels().contains(&term.constructor.as_str()) {
            return Err(NaiveKtUnsupported::SelfDrivingReservedLabel {
                op: term.constructor.clone(),
            });
        }
        labels.insert(term.constructor.clone());
        work.extend(term.children.iter().rev());
    }
    Ok(())
}

/// The R3 ROOT DISPATCHER `for(t <= ⌜^respread-root⌝){ match t { … } }` — the
/// persistent 1-ary contract every R3 firing's reduct is delivered to (it is
/// the accept's dynamic `out`; the installed σ-receiver / β-cascade sends
/// `out!(⟦reduct⟧)` and that send IS this contract's COMM):
///
/// * head tag ∈ `redex_root_routes` (the ruleset's entry root ops) → the reduct
///   can match again at the root: seed the walker with that entry's fixed route
///   identity, so it re-materializes exactly the compact channels demanded by
///   the persistent matcher — matching continues in-session;
/// * head tag ∈ `nf_labels` (subject constructors that are NOT rule roots) →
///   the session normal form: `@out_channel!(t)` lands the reflected NF ONCE
///   on the observation channel (the R3 analogue of the per-step drive's final
///   observed reduct — the in-Rho replacement of the host's
///   inject-next-or-stop loop);
/// * anything else → fail closed: `⌜^respread-err⌝!(t)`.
///
/// Dispatch is on the HEAD TAG ALONE ([`head_tag_remainder_pattern`], arity-
/// erased); arms are emitted in sorted label order (deterministic bytes), and
/// all arms' patterns are pairwise-disjoint ground tags, so arm order never
/// affects which arm fires.
fn respread_root_receiver_par(
    language_fingerprint: &str,
    out_channel: &str,
    redex_root_routes: &BTreeMap<String, String>,
    nf_labels: &BTreeSet<String>,
    production_diagnostics: bool,
) -> Par {
    let fp = language_fingerprint;
    let chan = trs::tag_par(fp, RESPREAD_ROOT_RESERVED_LABEL);
    let env = trs::Env::root(&["t"]);
    let mut cases: Vec<trs::Case> =
        Vec::with_capacity(redex_root_routes.len() + nf_labels.len() + 1);
    for (op, route_key) in redex_root_routes {
        cases.push(trs::Case {
            pattern: head_tag_remainder_pattern(fp, op),
            free_count: 0,
            body: trs::send(
                trs::ground(trs::tag_par(fp, RESPREAD_RESERVED_LABEL)),
                vec![
                    env.var("t"),
                    trs::ground(new_gstring_par(route_key.clone(), Vec::new(), false)),
                ],
            ),
        });
    }
    for label in nf_labels {
        cases.push(trs::Case {
            pattern: head_tag_remainder_pattern(fp, label),
            free_count: 0,
            body: trs::send(
                trs::ground(new_gstring_par(out_channel.to_string(), Vec::new(), false)),
                vec![env.var("t")],
            ),
        });
    }
    let respread_error =
        trs::send(trs::ground(trs::tag_par(fp, RESPREAD_ERR_RESERVED_LABEL)), vec![env.var("t")]);
    let error_body = if production_diagnostics {
        trs::par2(
            respread_error,
            trs::send(
                trs::ground(new_gstring_par(drive_err_channel(fp), Vec::new(), false)),
                vec![env.var("t")],
            ),
        )
    } else {
        respread_error
    };
    cases.push(trs::Case {
        pattern: trs::pat_wildcard(),
        free_count: 0,
        body: error_body,
    });
    let body = trs::match_(env.var("t"), cases);
    trs::persistent_contract(chan, 1, body).par
}

/// The R3 WALKER `for(t, route <= ⌜^respread⌝){ match t { … } }` — a
/// persistent reflected-term pushdown automaton specialized from term
/// rewriting to demand-directed re-spreading.  Each outer arm destructures one
/// pattern-required `(label, arity)`; its inner route dispatch selects one
/// exact pattern state and publishes directly to its compact channel:
///
/// ```text
/// [⌜L⌝, c₀, …, c_{m-1}] ; route = r =>
///     @loc(r)!(⌜L⌝)
///   | @cap(r,i)!(cᵢ)             when child i is a pattern variable
///   | ^respread!(cᵢ, child(r,i)) when child i is a constructor state
/// ```
///
/// A captured child is already the byte-identical reflected subtree the
/// matcher needs, so it is never traversed.  Consequently retained route data
/// is linear in the pattern forest, every route/channel token has fixed width,
/// and a deep captured reduct does not create a quadratic ladder of growing
/// path strings or dead per-node publications.
///
/// Fail-closed: a head tag outside the compiled pattern constructors hits the
/// wildcard arm and emits on `⌜^respread-err⌝`.  A known constructor at a route
/// that expects another constructor produces no route case, which is exactly a
/// failed pattern demand: no accept can fire.
fn respread_walker_receiver_par(
    language_fingerprint: &str,
    routes: &[SelfDrivingRoute],
    production_diagnostics: bool,
) -> Par {
    let fp = language_fingerprint;
    let chan = trs::tag_par(fp, RESPREAD_RESERVED_LABEL);
    let env = trs::Env::root(&["t", "route"]);
    let mut grouped: BTreeMap<(String, usize), Vec<&SelfDrivingRoute>> = BTreeMap::new();
    for route in routes {
        grouped
            .entry((route.op.clone(), route.children.len()))
            .or_default()
            .push(route);
    }
    let mut cases: Vec<trs::Case> = Vec::with_capacity(grouped.len() + 1);
    for ((label, arity), group) in grouped {
        let child_pats: Vec<Par> = (0..arity).map(trs::pat_free).collect();
        cases.push(trs::Case {
            pattern: trs::pat_tagged(fp, &label, child_pats),
            free_count: arity,
            body: {
                let child_names: Vec<String> = (0..arity).map(|i| format!("c{i}")).collect();
                let child_refs: Vec<&str> = child_names.iter().map(String::as_str).collect();
                let env = env.push(&child_refs);
                let mut route_cases = Vec::with_capacity(group.len());
                for route in group {
                    let mut composed = trs::send(
                        trs::ground(new_gstring_par(route.loc_channel.clone(), Vec::new(), false)),
                        vec![trs::ground(trs::tag_par(fp, &label))],
                    );
                    for (child, action) in child_refs.iter().zip(&route.children) {
                        let next = match action {
                            SelfDrivingChild::Descend { route_key } => trs::send(
                                trs::ground(trs::tag_par(fp, RESPREAD_RESERVED_LABEL)),
                                vec![
                                    env.var(child),
                                    trs::ground(new_gstring_par(
                                        route_key.clone(),
                                        Vec::new(),
                                        false,
                                    )),
                                ],
                            ),
                            SelfDrivingChild::Capture { channel } => trs::send(
                                trs::ground(new_gstring_par(channel.clone(), Vec::new(), false)),
                                vec![env.var(child)],
                            ),
                        };
                        composed = trs::par2(composed, next);
                    }
                    route_cases.push(trs::Case {
                        pattern: new_gstring_par(route.route_key.clone(), Vec::new(), false),
                        free_count: 0,
                        body: composed,
                    });
                }
                trs::match_(env.var("route"), route_cases)
            },
        });
    }
    let respread_error =
        trs::send(trs::ground(trs::tag_par(fp, RESPREAD_ERR_RESERVED_LABEL)), vec![env.var("t")]);
    let error_body = if production_diagnostics {
        trs::par2(
            respread_error,
            trs::send(
                trs::ground(new_gstring_par(drive_err_channel(fp), Vec::new(), false)),
                vec![env.var("t")],
            ),
        )
    } else {
        respread_error
    };
    cases.push(trs::Case {
        pattern: trs::pat_wildcard(),
        free_count: 0,
        body: error_body,
    });
    let body = trs::match_(env.var("t"), cases);
    trs::persistent_contract(chan, 2, body).par
}

/// Track B — R3, the SELF-DRIVING naive call (EXPLORATORY; PRE-REGISTERED
/// deviation from the shared firing contract, USER-approved 2026-07-19;
/// PatternGuard only): ONE session that installs, at `root_site`,
///
/// 1. every entry's R3 receiver ([`selfdriving_entry_receiver_par`]) — the
///    Appendix-A persistent per-site receiver whose accept's OUT slot is the
///    `^respread-root` dispatcher instead of the observation channel;
/// 2. the `^respread-root` dispatcher + finite `^respread` route PDA, compiled
///    from the admitted pattern forest by [`build_selfdriving_plan`];
/// 3. one reflected subject sent to the root route (or directly to OUT when it
///    is already a known normal form).
///
/// # The self-driving loop (why one injection normalizes a chain)
///
/// firing k: the persistent root receiver consumes the CURRENT root spread
/// (`loc:`/`cap:` — `matching_tau`), its accept COMM fires the installed
/// σ-receiver (`sa:` — `firing_visible`, exactly one per firing, so
/// `firing_visible` remains the per-session firing count the ground truth
/// pins), the language's OWN firing machinery computes the reduct (for a
/// `SubstRewrite` β entry: the reserved `^subst` cascade — `subst_tau`,
/// identical work to the per-step column) and delivers it on the accept's
/// dynamic `out` = the `^respread-root` dispatcher (`respread_tau`), which
/// re-spreads a redex-rooted reduct through the pattern route PDA (walker COMMs
/// — `respread_tau`, one per demanded constructor state) — re-arming the SAME persistent receiver —
/// or lands a normal-form reduct ONCE on `out_channel`. NOTE the reduct is
/// COMPUTED by the installed firing contract, never assumed: R3 does not
/// special-case the identity-λ chain (re-spreading the captured argument
/// directly would); the walker re-spreads whatever the cascade delivered.
///
/// # Determinism (per-channel single-liveness)
///
/// Rounds are causally ordered (walk k's sends exist only after firing k's
/// captures were consumed), and per round each demanded channel carries
/// exactly one live message. Variable children are published directly and not
/// traversed, so the persistent session retains neither stale deep-path sends
/// nor growing path strings.
///
/// Returns the call and the installed ENTRY-receiver count (the matcher
/// installs; the dispatcher/walker contracts are firing-side infrastructure,
/// counted with the installed program like the subst TRS receivers, not here).
pub fn naive_kt_selfdriving_call_par(
    ruleset: &InRhoMatchingRuleset,
    subject: &GroundTerm,
    root_site: &str,
    out_channel: &str,
) -> Result<(Par, usize), NaiveKtUnsupported> {
    selfdriving_call_par(ruleset, subject, root_site, out_channel, None, false)
}

fn selfdriving_call_par(
    ruleset: &InRhoMatchingRuleset,
    subject: &GroundTerm,
    root_site: &str,
    out_channel: &str,
    fired_rule_labels: Option<&BTreeMap<PatternId, String>>,
    production_diagnostics: bool,
) -> Result<(Par, usize), NaiveKtUnsupported> {
    let view = ruleset.automaton.view();
    validate_naive_ruleset(&view)?;
    let mut subject_labels = BTreeSet::new();
    collect_selfdriving_labels(subject, &mut subject_labels)?;
    let plan = build_selfdriving_plan(&view, &ruleset.language_fingerprint, root_site)?;

    // The dispatcher's redex set: the ruleset's entry ROOT ops (a reduct with
    // such a head can fire again at the root). NF labels: every OTHER subject
    // constructor. A redex-rooted reduct whose demanded nested constructor
    // differs from its pattern route cannot produce an accept; a reduct whose
    // ROOT leaves both sets fails closed in the dispatcher.
    let nf_labels: BTreeSet<String> = subject_labels
        .iter()
        .filter(|label| !plan.root_routes.contains_key(*label))
        .cloned()
        .collect();

    let mut call = Par::default();
    let mut installed = 0usize;
    for (entry, planned) in plan.entries.iter().enumerate() {
        let accept_channel = entry_accept_channel(ruleset, view.entry_id(entry));
        let fired_rule_label = fired_rule_labels
            .and_then(|labels| labels.get(&planned.pattern_id))
            .map(String::as_str);
        let receiver = selfdriving_entry_receiver_par(
            &planned.schedule,
            accept_channel,
            &ruleset.language_fingerprint,
            fired_rule_label,
        );
        call = call.append(receiver);
        installed += 1;
    }
    call = call.append(respread_root_receiver_par(
        &ruleset.language_fingerprint,
        out_channel,
        &plan.root_routes,
        &nf_labels,
        production_diagnostics,
    ));
    call = call.append(respread_walker_receiver_par(
        &ruleset.language_fingerprint,
        &plan.routes,
        production_diagnostics,
    ));

    let reflected = trs::ground(reflect_ground_term_par(subject, &ruleset.language_fingerprint));
    let initial = if let Some(route_key) = plan.root_routes.get(&subject.constructor) {
        trs::send(
            trs::ground(trs::tag_par(&ruleset.language_fingerprint, RESPREAD_RESERVED_LABEL)),
            vec![reflected, trs::ground(new_gstring_par(route_key.clone(), Vec::new(), false))],
        )
    } else if nf_labels.contains(&subject.constructor) {
        trs::send(
            trs::ground(new_gstring_par(out_channel.to_string(), Vec::new(), false)),
            vec![reflected],
        )
    } else {
        trs::send(
            trs::ground(trs::tag_par(&ruleset.language_fingerprint, RESPREAD_ERR_RESERVED_LABEL)),
            vec![reflected],
        )
    };
    Ok((call.append(initial.par), installed))
}

/// A term-and-ruleset proof that the persistent root PDA is a total
/// quiescence driver for this invocation.
///
/// The admitted class is semantic rather than benchmark-sized: one linear
/// substitution rewrite has the reflected shape
/// `R(^lambda(scope), replacement)`, and the subject is an arbitrary-length
/// spine of `R(^lambda(^bound(^Z)), rest)`.  Every firing therefore contracts
/// exactly to `rest`, strictly decreases the spine length, and ends in a
/// subtree containing no occurrence of `R`.  The proof is computed by an
/// iterative walk and imposes no traversal-depth limit.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PersistentRootDriveCertificate {
    pattern_id: PatternId,
    /// The generated rewrite label emitted to the production firing ledger.
    pub rule_label: String,
    /// Root constructor of the certified substitution rewrite.
    pub root_constructor: String,
    /// Exact number of root contractions before the normal-form tail.
    pub contractions: usize,
}

/// Prove that `subject` belongs to the persistent root PDA's total sound
/// envelope.  `None` is an ordinary routing decision: the generated caller
/// falls back to the general congruence-capable quiescence driver.
pub fn persistent_root_drive_certificate(
    def: &LanguageDef,
    ruleset: &InRhoMatchingRuleset,
    subject: &GroundTerm,
) -> Option<PersistentRootDriveCertificate> {
    // The fast path currently proves the complete rewrite system, not one
    // family in isolation. Value-producing dispatch families or deferred rules
    // could introduce redexes not represented by the positional root PDA.
    // Contextual families are allowed: the tail proof below establishes that
    // their premise rewrite is absent at every nested position.
    let deferred_are_congruence_closure = ruleset.deferred.iter().all(|entry| {
        def.rewrites
            .iter()
            .find(|rewrite| rewrite.name.to_string() == entry.rule_label)
            .is_some_and(|rewrite| rewrite.congruence_premise().is_some())
    });
    if !deferred_are_congruence_closure
        || !ruleset.native_dispatch.is_empty()
        || !ruleset.ac_dispatch.is_empty()
        || !ruleset.structural_ac_dispatch.is_empty()
        || !ruleset.nested_structural_ac_dispatch.is_empty()
    {
        return None;
    }

    let view = ruleset.automaton.view();
    if view.entry_count() != 1 || validate_naive_ruleset(&view).is_err() {
        return None;
    }
    let pattern_id = view.entry_id(0);
    let rewrite = def.rewrites.get(pattern_id.0)?;
    crate::rho_net_lower::subst_rule_shape(&rewrite.left, &rewrite.right)?;

    // Prove the compiled LHS shape, independently of source spelling:
    // R(^lambda(scope), replacement), with both leaves linear variables.
    let AutomatonNode::App { op: root_op, args: root_args } = view.node(view.entry_root_state(0))
    else {
        return None;
    };
    let [binder_pattern, replacement_pattern] = root_args else {
        return None;
    };
    if !matches!(view.node(replacement_pattern.state()), AutomatonNode::Var) {
        return None;
    }
    let AutomatonNode::App { op: binder_op, args: binder_args } = view.node(binder_pattern.state())
    else {
        return None;
    };
    let [scope_pattern] = binder_args else {
        return None;
    };
    if binder_op.as_str() != LAMBDA_REFLECT_LABEL
        || !matches!(view.node(scope_pattern.state()), AutomatonNode::Var)
    {
        return None;
    }

    let mut contractions = 0usize;
    let mut tail = subject;
    while tail.coll_type.is_none()
        && tail.constructor == root_op.as_str()
        && tail.children.len() == 2
    {
        let binder = &tail.children[0];
        let replacement = &tail.children[1];
        let identity_body = binder.coll_type.is_none()
            && binder.constructor == LAMBDA_REFLECT_LABEL
            && binder.children.len() == 1
            && binder.children[0].coll_type.is_none()
            && binder.children[0].constructor == BOUND_VAR_REFLECT_LABEL
            && binder.children[0].children.len() == 1
            && binder.children[0].children[0].coll_type.is_none()
            && binder.children[0].children[0].constructor == PEANO_ZERO_REFLECT_LABEL
            && binder.children[0].children[0].children.is_empty();
        if !identity_body {
            return None;
        }
        contractions = contractions.checked_add(1)?;
        tail = replacement;
    }
    if contractions == 0 {
        return None;
    }

    // The terminal subtree must already be globally normal for the positional
    // rewrite system. Contextual dispatch records merely close these same
    // rewrites under constructors; because no rewrite root remains anywhere,
    // none of those congruence families is applicable. Any nested occurrence
    // of the rewrite root needs congruence and therefore routes to the general
    // driver instead.
    let mut work = vec![tail];
    while let Some(term) = work.pop() {
        if term.coll_type.is_some()
            || term.constructor == root_op.as_str()
            || respread_reserved_labels().contains(&term.constructor.as_str())
        {
            return None;
        }
        work.extend(term.children.iter().rev());
    }

    Some(PersistentRootDriveCertificate {
        pattern_id,
        rule_label: rewrite.name.to_string(),
        root_constructor: root_op.to_string(),
        contractions,
    })
}

/// Assemble a production persistent-root invocation when
/// [`persistent_root_drive_certificate`] succeeds.  The call emits the same
/// OUT, firing-ledger, and typed-error observations as the general production
/// driver.  It returns `Ok(None)` outside the proved envelope so generated code
/// can preserve the general driver as a sound fallback.
pub fn persistent_root_drive_invocation(
    def: &LanguageDef,
    ruleset: &InRhoMatchingRuleset,
    subject: &GroundTerm,
    out_channel: &str,
) -> Result<Option<RhoNetDriveInvocation>, String> {
    let Some(certificate) = persistent_root_drive_certificate(def, ruleset, subject) else {
        return Ok(None);
    };
    let mut labels = BTreeMap::new();
    labels.insert(certificate.pattern_id, certificate.rule_label.clone());
    let (call, _installed) = selfdriving_call_par(
        ruleset,
        subject,
        "@production-root",
        out_channel,
        Some(&labels),
        true,
    )
    .map_err(|error| format!("persistent root drive rejected its certified subject: {error}"))?;
    let reflected = reflect_ground_term_par(subject, &ruleset.language_fingerprint);
    Ok(Some(RhoNetDriveInvocation {
        call,
        subject: reflected,
        strategy: RhoNetDriveStrategy::PersistentRootIdentityBeta {
            contractions: certificate.contractions,
        },
        per_path_fuel: i64::try_from(certificate.contractions).unwrap_or(i64::MAX),
        out_channel: out_channel.to_string(),
        fired_channel: drive_fired_channel(&ruleset.language_fingerprint),
        err_channel: drive_err_channel(&ruleset.language_fingerprint),
        fuel_channel: drive_fuel_channel(&ruleset.language_fingerprint),
    }))
}

#[cfg(test)]
#[path = "../tests/support/rho_net_pattern_guard_recursive_oracle.rs"]
mod recursive_oracle;

#[cfg(test)]
mod tests {
    use super::*;
    use dovetail::rules::Pattern;
    use dovetail::set_automaton::SetAutomaton;
    use models::rhoapi::expr::ExprInstance;
    use proptest::prelude::*;

    use crate::rho_net_lower::RhoNetContextualMatchEntry;

    const FP: &str = "fp";

    fn positional_subject() -> GroundTerm {
        let branch = |name| {
            GroundTerm::new(
                name,
                vec![
                    GroundTerm::nullary("a"),
                    GroundTerm::nullary("b"),
                    GroundTerm::nullary("c"),
                    GroundTerm::nullary("d"),
                ],
            )
        };
        GroundTerm::new("root", vec![branch("p0"), branch("p1"), branch("p2"), branch("p3")])
    }

    fn subject_for_pattern(pattern: &Pattern<String>) -> GroundTerm {
        enum Task<'a> {
            Visit(&'a Pattern<String>),
            Assemble { op: &'a str, arity: usize },
        }
        let mut tasks = vec![Task::Visit(pattern)];
        let mut values = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                Task::Visit(Pattern::Var(_)) => values.push(GroundTerm::nullary("value")),
                Task::Visit(Pattern::App { op, args }) => {
                    tasks.push(Task::Assemble { op, arity: args.len() });
                    tasks.extend(args.iter().rev().map(Task::Visit));
                },
                Task::Visit(other) => panic!("test expected positional pattern, got {other:?}"),
                Task::Assemble { op, arity } => {
                    let first_child = values.len() - arity;
                    let children = values.split_off(first_child);
                    values.push(GroundTerm::new(op, children));
                },
            }
        }
        values.pop().expect("pattern produces one subject")
    }

    fn indexed_channel(subject: &GroundTerm, family: &str, child_path: &[usize]) -> String {
        let locations = SubjectLocationIndex::new(subject);
        let mut position = SubjectPosition::ROOT;
        for &child in child_path {
            position = locations
                .child(position, child)
                .expect("test subject contains position");
        }
        locations.channel(family, FP, "site0", position)
    }

    fn gstring(par: &Par) -> Option<&str> {
        match par.exprs.first()?.expr_instance.as_ref()? {
            ExprInstance::GString(v) => Some(v.as_str()),
            _ => None,
        }
    }

    fn boundvar_index(par: &Par) -> Option<i32> {
        use models::rhoapi::var::VarInstance;
        match par.exprs.first()?.expr_instance.as_ref()? {
            ExprInstance::EVarBody(ev) => match ev.v.as_ref()?.var_instance.as_ref()? {
                VarInstance::BoundVar(i) => Some(*i),
                _ => None,
            },
            _ => None,
        }
    }

    fn tag_par(op: &str) -> Par {
        GPrivateBuilder::new_par_from_string(reflect_tag(FP, op))
    }

    /// Assemble a direct positional ruleset (mirrors the admission-matrix test's
    /// direct construction; every field of `InRhoMatchingRuleset` is `pub`).
    fn direct_ruleset(
        patterns: Vec<(PatternId, Pattern<String>)>,
        accepts: Vec<(PatternId, &str)>,
        contextual: Vec<RhoNetContextualMatchEntry>,
    ) -> InRhoMatchingRuleset {
        let automaton =
            SetAutomaton::compile_structural(patterns).expect("the test patterns are AC-free");
        InRhoMatchingRuleset {
            automaton,
            accept_channels: accepts
                .into_iter()
                .map(|(pid, channel)| (pid, channel.to_string()))
                .collect(),
            language_fingerprint: FP.to_string(),
            deferred: Vec::new(),
            native_dispatch: Vec::new(),
            ac_dispatch: Vec::new(),
            contextual_dispatch: contextual,
            structural_ac_dispatch: Vec::new(),
            nested_structural_ac_dispatch: Vec::new(),
        }
    }

    fn swap_automaton() -> SetAutomaton<String> {
        SetAutomaton::compile_structural([(
            PatternId(0),
            Pattern::app("Swap".to_string(), vec![Pattern::var("x"), Pattern::var("y")]),
        )])
        .expect("Swap(x, y) compiles")
    }

    fn assert_closed(par: &Par, what: &str) {
        assert!(par.locally_free.is_empty(), "{what} must be a closed contract");
        assert!(!par.connective_used, "{what} must not be connective-marked");
    }

    #[test]
    fn pattern_guard_swap_emits_a_persistent_root_receive_and_the_shared_accept() {
        let automaton = swap_automaton();
        let subject = positional_subject();
        let network = naive_kt_entry_receiver_par(
            &automaton.view(),
            0,
            &subject,
            "site0",
            "sa:acc",
            "OUT",
            FP,
            NaiveGuardEncoding::PatternGuard,
        )
        .expect("the flat Swap entry emits");
        assert_closed(&network, "the naive Swap receiver");

        // Root: for(⌜Swap⌝ <= loc:site0){ … } — PERSISTENT, tag-as-pattern.
        assert_eq!(network.receives.len(), 1);
        let root = &network.receives[0];
        assert!(root.persistent, "the Appendix-A rule receiver is persistent at its site");
        assert_eq!(root.bind_count, 0, "PatternGuard binds nothing at the tag");
        assert_eq!(root.binds[0].free_count, 0);
        assert_eq!(
            gstring(root.binds[0].source.as_ref().expect("source")),
            Some(indexed_channel(&subject, "loc", &[]).as_str())
        );
        assert_eq!(
            root.binds[0].patterns[0],
            tag_par("Swap"),
            "the expected head tag IS the receive pattern"
        );

        // Captures: for(v1 <- cap⟨site0,p1⟩){ for(v2 <- cap⟨site0,p2⟩){ accept } }.
        let cap_x = &root.body.as_ref().expect("root body").receives[0];
        assert!(!cap_x.persistent, "captures are one-shot");
        assert_eq!(
            gstring(cap_x.binds[0].source.as_ref().expect("source")),
            Some(indexed_channel(&subject, "cap", &[0]).as_str())
        );
        let cap_y = &cap_x.body.as_ref().expect("x body").receives[0];
        assert_eq!(
            gstring(cap_y.binds[0].source.as_ref().expect("source")),
            Some(indexed_channel(&subject, "cap", &[1]).as_str())
        );

        // Accept: sa:acc!(BoundVar(1), BoundVar(0), @"OUT") — the SHARED
        // build_accept_send tuple, byte-identical by function identity.
        let accept_body = cap_y.body.as_ref().expect("y body");
        assert_eq!(accept_body.sends.len(), 1);
        assert_eq!(
            accept_body.sends[0],
            build_accept_send("sa:acc", "OUT", 2, &[0, 1]).sends[0],
            "the naive accept send is the automaton's build_accept_send output"
        );
    }

    #[test]
    fn nested_f_g_x_emits_two_level_tag_receives_then_the_deep_capture() {
        let subject = positional_subject();
        let automaton = SetAutomaton::compile_structural([(
            PatternId(0),
            Pattern::app(
                "f".to_string(),
                vec![Pattern::app("g".to_string(), vec![Pattern::var("x")])],
            ),
        )])
        .expect("f(g(x)) compiles");
        let network = naive_kt_entry_receiver_par(
            &automaton.view(),
            0,
            &subject,
            "site0",
            "sa:acc",
            "OUT",
            FP,
            NaiveGuardEncoding::PatternGuard,
        )
        .expect("the nested entry emits");
        assert_closed(&network, "the naive f(g(x)) receiver");

        // Level 1: persistent for(⌜f⌝ <= loc⟨site0,p(root)⟩).
        let root = &network.receives[0];
        assert!(root.persistent);
        assert_eq!(
            gstring(root.binds[0].source.as_ref().expect("source")),
            Some(indexed_channel(&subject, "loc", &[]).as_str())
        );
        assert_eq!(root.binds[0].patterns[0], tag_par("f"));
        // Level 2: one-shot for(⌜g⌝ <- loc⟨site0,p([0])⟩).
        let descent = &root.body.as_ref().expect("root body").receives[0];
        assert!(!descent.persistent, "descent tag receives are one-shot");
        assert_eq!(
            gstring(descent.binds[0].source.as_ref().expect("source")),
            Some(indexed_channel(&subject, "loc", &[0]).as_str())
        );
        assert_eq!(descent.binds[0].patterns[0], tag_par("g"));
        // Capture: for(v <- cap⟨site0,p([0,0])⟩){ accept } — the deep collapse value.
        let capture = &descent.body.as_ref().expect("descent body").receives[0];
        assert_eq!(
            gstring(capture.binds[0].source.as_ref().expect("source")),
            Some(indexed_channel(&subject, "cap", &[0, 0]).as_str())
        );
        let accept = &capture.body.as_ref().expect("capture body").sends[0];
        assert_eq!(gstring(accept.chan.as_ref().expect("chan")), Some("sa:acc"));
        assert_eq!(accept.data.len(), 2, "σ[x] + @out");
        assert_eq!(boundvar_index(&accept.data[0]), Some(0), "σ[x] = BoundVar(0)");
        assert_eq!(gstring(&accept.data[1]), Some("OUT"));
    }

    #[test]
    fn ternary_pattern_captures_in_dfs_order_with_the_general_frame() {
        let subject = positional_subject();
        let automaton = SetAutomaton::compile_structural([(
            PatternId(0),
            Pattern::app(
                "Triple".to_string(),
                vec![Pattern::var("x"), Pattern::var("y"), Pattern::var("z")],
            ),
        )])
        .expect("Triple(x, y, z) compiles");
        let network = naive_kt_entry_receiver_par(
            &automaton.view(),
            0,
            &subject,
            "site0",
            "sa:acc",
            "OUT",
            FP,
            NaiveGuardEncoding::PatternGuard,
        )
        .expect("the ternary entry emits");
        assert_closed(&network, "the naive Triple receiver");

        let mut body = network.receives[0].body.as_ref().expect("root body");
        for expected in [
            indexed_channel(&subject, "cap", &[0]),
            indexed_channel(&subject, "cap", &[1]),
            indexed_channel(&subject, "cap", &[2]),
        ] {
            let receive = &body.receives[0];
            assert_eq!(
                gstring(receive.binds[0].source.as_ref().expect("source")),
                Some(expected.as_str())
            );
            body = receive.body.as_ref().expect("capture body");
        }
        let send = &body.sends[0];
        assert_eq!(send.data.len(), 4, "σ_x, σ_y, σ_z, @out");
        assert_eq!(boundvar_index(&send.data[0]), Some(2), "σ[x] = BoundVar(2)");
        assert_eq!(boundvar_index(&send.data[1]), Some(1), "σ[y] = BoundVar(1)");
        assert_eq!(boundvar_index(&send.data[2]), Some(0), "σ[z] = BoundVar(0)");
    }

    #[test]
    fn var_capture_wiring_matches_the_automaton_cap_abi_with_a_flat_sibling() {
        let subject = positional_subject();
        // f(g(x), y): x is captured at p([0,0]), y at direct-child p([1]);
        // DFS order [x, y] ⇒ σ[x] = BoundVar(1),
        // σ[y] = BoundVar(0) — the automaton's exact capture ABI.
        let automaton = SetAutomaton::compile_structural([(
            PatternId(0),
            Pattern::app(
                "f".to_string(),
                vec![Pattern::app("g".to_string(), vec![Pattern::var("x")]), Pattern::var("y")],
            ),
        )])
        .expect("f(g(x), y) compiles");
        let network = naive_kt_entry_receiver_par(
            &automaton.view(),
            0,
            &subject,
            "site0",
            "sa:acc",
            "OUT",
            FP,
            NaiveGuardEncoding::PatternGuard,
        )
        .expect("the mixed entry emits");
        assert_closed(&network, "the naive f(g(x), y) receiver");

        let descent = &network.receives[0]
            .body
            .as_ref()
            .expect("root body")
            .receives[0];
        assert_eq!(descent.binds[0].patterns[0], tag_par("g"));
        let cap_x = &descent.body.as_ref().expect("descent body").receives[0];
        assert_eq!(
            gstring(cap_x.binds[0].source.as_ref().expect("source")),
            Some(indexed_channel(&subject, "cap", &[0, 0]).as_str())
        );
        let cap_y = &cap_x.body.as_ref().expect("x body").receives[0];
        assert_eq!(
            gstring(cap_y.binds[0].source.as_ref().expect("source")),
            Some(indexed_channel(&subject, "cap", &[1]).as_str())
        );
        let send = &cap_y.body.as_ref().expect("y body").sends[0];
        assert_eq!(boundvar_index(&send.data[0]), Some(1), "σ[x] = BoundVar(1) (DFS-first)");
        assert_eq!(boundvar_index(&send.data[1]), Some(0), "σ[y] = BoundVar(0)");
    }

    #[test]
    fn consume_test_binds_the_tag_and_republishes_on_mismatch() {
        let automaton = swap_automaton();
        let subject = positional_subject();
        let network = naive_kt_entry_receiver_par(
            &automaton.view(),
            0,
            &subject,
            "site0",
            "sa:acc",
            "OUT",
            FP,
            NaiveGuardEncoding::ConsumeTest,
        )
        .expect("the ConsumeTest Swap entry emits");
        assert_closed(&network, "the ConsumeTest Swap receiver");

        // Root: for(h <= loc:site0){ match h { ⌜Swap⌝ => … ; _ => loc:site0!(h) } }.
        let root = &network.receives[0];
        assert!(root.persistent);
        assert_eq!(root.bind_count, 1, "ConsumeTest binds the tag free");
        assert_eq!(root.binds[0].free_count, 1);
        let m = &root.body.as_ref().expect("root body").matches[0];
        assert_eq!(boundvar_index(m.target.as_ref().expect("target")), Some(0));
        assert_eq!(m.cases.len(), 2, "tag case + republish else-arm");
        assert_eq!(m.cases[0].pattern.as_ref().expect("tag case"), &tag_par("Swap"));
        assert_eq!(m.cases[0].free_count, 0);
        // Else-arm: wildcard pattern, body republishes h = BoundVar(0) on loc:site0.
        assert_eq!(
            m.cases[1].pattern.as_ref().expect("else pattern"),
            &new_wildcard_par(Vec::new(), true)
        );
        let republish = &m.cases[1].source.as_ref().expect("else body").sends[0];
        assert_eq!(
            gstring(republish.chan.as_ref().expect("chan")),
            Some(indexed_channel(&subject, "loc", &[]).as_str())
        );
        assert_eq!(boundvar_index(&republish.data[0]), Some(0), "republishes the consumed tag");

        // The continuation under the tag case still ends in the SAME accept
        // frame (the tag binders sit OUTSIDE the capture chain, so the σ
        // BoundVars are unshifted).
        let cap_x = &m.cases[0].source.as_ref().expect("tag case body").receives[0];
        let cap_y = &cap_x.body.as_ref().expect("x body").receives[0];
        let send = &cap_y.body.as_ref().expect("y body").sends[0];
        assert_eq!(
            send,
            &build_accept_send("sa:acc", "OUT", 2, &[0, 1]).sends[0],
            "ConsumeTest reaches the byte-identical shared accept send"
        );
    }

    #[test]
    fn rejects_a_variable_root_pattern() {
        let automaton = SetAutomaton::compile_structural([(PatternId(0), Pattern::var("x"))])
            .expect("a bare-variable pattern compiles");
        assert_eq!(
            naive_kt_entry_receiver_par(
                &automaton.view(),
                0,
                &positional_subject(),
                "site0",
                "sa:acc",
                "OUT",
                FP,
                NaiveGuardEncoding::PatternGuard,
            ),
            Err(NaiveKtUnsupported::VariableRootPattern)
        );
        let ruleset = direct_ruleset(
            vec![(PatternId(0), Pattern::var("x"))],
            vec![(PatternId(0), "sa:acc")],
            Vec::new(),
        );
        assert_eq!(
            naive_kt_match_call_par(
                &ruleset,
                &GroundTerm::nullary("A"),
                "site0",
                "OUT",
                NaiveGuardEncoding::PatternGuard,
            ),
            Err(NaiveKtUnsupported::VariableRootPattern)
        );
    }

    #[test]
    fn rejects_a_non_linear_entry() {
        let automaton = SetAutomaton::compile_structural([(
            PatternId(0),
            Pattern::app("f".to_string(), vec![Pattern::var("x"), Pattern::var("x")]),
        )])
        .expect("f(x, x) compiles");
        assert_eq!(
            naive_kt_entry_receiver_par(
                &automaton.view(),
                0,
                &positional_subject(),
                "site0",
                "sa:acc",
                "OUT",
                FP,
                NaiveGuardEncoding::PatternGuard,
            ),
            Err(NaiveKtUnsupported::NonLinearEntry)
        );
        // A DEEP repeat is caught by the same DFS name walk: f(g(x), x).
        let deep = SetAutomaton::compile_structural([(
            PatternId(0),
            Pattern::app(
                "f".to_string(),
                vec![Pattern::app("g".to_string(), vec![Pattern::var("x")]), Pattern::var("x")],
            ),
        )])
        .expect("f(g(x), x) compiles");
        assert_eq!(
            naive_kt_entry_receiver_par(
                &deep.view(),
                0,
                &positional_subject(),
                "site0",
                "sa:acc",
                "OUT",
                FP,
                NaiveGuardEncoding::PatternGuard,
            ),
            Err(NaiveKtUnsupported::NonLinearEntry)
        );
    }

    #[test]
    fn rejects_overlapping_tag_demand_nested_vs_root() {
        // Entry 0's non-root op g == entry 1's root op g: at any subject
        // position with head g, entry 0's descent and entry 1's installed root
        // receiver would demand the same single loc: message.
        let ruleset = direct_ruleset(
            vec![
                (
                    PatternId(0),
                    Pattern::app(
                        "f".to_string(),
                        vec![Pattern::app("g".to_string(), vec![Pattern::var("x")])],
                    ),
                ),
                (PatternId(1), Pattern::app("g".to_string(), vec![Pattern::var("y")])),
            ],
            vec![(PatternId(0), "sa:fg"), (PatternId(1), "sa:g")],
            Vec::new(),
        );
        assert_eq!(
            naive_kt_match_call_par(
                &ruleset,
                &GroundTerm::nullary("A"),
                "site0",
                "OUT",
                NaiveGuardEncoding::PatternGuard,
            ),
            Err(NaiveKtUnsupported::OverlappingTagDemand {
                op: "g".to_string(),
                demanding_entry: PatternId(0),
                root_entry: PatternId(1),
            })
        );
    }

    #[test]
    fn rejects_overlapping_tag_demand_self_recursive() {
        // f(f(x)): the entry's OWN root op appears as a non-root node, so its
        // receiver at an outer site and its receiver at the inner site would
        // demand the same loc: message.
        let ruleset = direct_ruleset(
            vec![(
                PatternId(0),
                Pattern::app(
                    "f".to_string(),
                    vec![Pattern::app("f".to_string(), vec![Pattern::var("x")])],
                ),
            )],
            vec![(PatternId(0), "sa:ff")],
            Vec::new(),
        );
        assert_eq!(
            naive_kt_match_call_par(
                &ruleset,
                &GroundTerm::nullary("A"),
                "site0",
                "OUT",
                NaiveGuardEncoding::PatternGuard,
            ),
            Err(NaiveKtUnsupported::OverlappingTagDemand {
                op: "f".to_string(),
                demanding_entry: PatternId(0),
                root_entry: PatternId(0),
            })
        );
    }

    #[test]
    fn rejects_overlapping_tag_demand_duplicate_roots() {
        // Two DISTINCT entries share the root op Swap: both per-site receivers
        // would demand one head-tag message (the optimized network instead
        // shares the match and fans out both accepts — O3, unshareable here).
        let ruleset = direct_ruleset(
            vec![
                (
                    PatternId(0),
                    Pattern::app("Swap".to_string(), vec![Pattern::var("x"), Pattern::var("y")]),
                ),
                (
                    PatternId(1),
                    Pattern::app("Swap".to_string(), vec![Pattern::var("a"), Pattern::var("b")]),
                ),
            ],
            vec![(PatternId(0), "sa:one"), (PatternId(1), "sa:two")],
            Vec::new(),
        );
        assert_eq!(
            naive_kt_match_call_par(
                &ruleset,
                &GroundTerm::nullary("A"),
                "site0",
                "OUT",
                NaiveGuardEncoding::PatternGuard,
            ),
            Err(NaiveKtUnsupported::OverlappingTagDemand {
                op: "Swap".to_string(),
                demanding_entry: PatternId(1),
                root_entry: PatternId(0),
            })
        );
    }

    #[test]
    fn beta_shape_passes_the_overlap_gate() {
        // App(^lambda(fun), arg): the internal ^lambda op is NOT a root op, so
        // the gate admits β — the λ-chain workload family is naive-emittable.
        let ruleset = direct_ruleset(
            vec![(
                PatternId(0),
                Pattern::app(
                    "App".to_string(),
                    vec![
                        Pattern::app(
                            crate::rho_net_lower::LAMBDA_REFLECT_LABEL.to_string(),
                            vec![Pattern::var("fun")],
                        ),
                        Pattern::var("arg"),
                    ],
                ),
            )],
            vec![(PatternId(0), "sa:beta")],
            Vec::new(),
        );
        let subject = GroundTerm::new(
            "App",
            vec![
                GroundTerm::new(
                    crate::rho_net_lower::LAMBDA_REFLECT_LABEL,
                    vec![GroundTerm::nullary("F")],
                ),
                GroundTerm::nullary("A0"),
            ],
        );
        let (call, installed) = naive_kt_match_call_par(
            &ruleset,
            &subject,
            "site0",
            "OUT",
            NaiveGuardEncoding::PatternGuard,
        )
        .expect("β passes the overlap gate");
        assert_eq!(installed, 1, "one head-App position");
        assert_closed(&call, "the naive β match call");
    }

    #[test]
    fn match_call_installs_one_receiver_per_head_matching_position() {
        // Pair(Swap(A,B), Pair(Swap(B,A), Swap(A,A))): three head-Swap
        // positions (Pair is inert) ⇒ 3 installed receivers + one spread.
        let ruleset = direct_ruleset(
            vec![(
                PatternId(0),
                Pattern::app("Swap".to_string(), vec![Pattern::var("x"), Pattern::var("y")]),
            )],
            vec![(PatternId(0), "sa:swap")],
            Vec::new(),
        );
        let swap = |a: &str, b: &str| {
            GroundTerm::new("Swap", vec![GroundTerm::nullary(a), GroundTerm::nullary(b)])
        };
        let subject = GroundTerm::new(
            "Pair",
            vec![swap("A", "B"), GroundTerm::new("Pair", vec![swap("B", "A"), swap("A", "A")])],
        );
        let (call, installed) = naive_kt_match_call_par(
            &ruleset,
            &subject,
            "site0",
            "OUT",
            NaiveGuardEncoding::PatternGuard,
        )
        .expect("the flat comb emits");
        assert_eq!(installed, 3, "one receiver per head-Swap position");
        assert_closed(&call, "the naive comb match call");

        // The three persistent per-site root receives read the three sites'
        // loc: channels (the spread's derivation).
        let persistent_sources: Vec<Option<&str>> = call
            .receives
            .iter()
            .filter(|receive| receive.persistent)
            .map(|receive| gstring(receive.binds[0].source.as_ref().expect("source")))
            .collect();
        for expected in [
            indexed_channel(&subject, "loc", &[0]),
            indexed_channel(&subject, "loc", &[1, 0]),
            indexed_channel(&subject, "loc", &[1, 1]),
        ] {
            assert!(
                persistent_sources.contains(&Some(expected.as_str())),
                "a per-site receiver must read {expected} (got {persistent_sources:?})"
            );
        }
        // Exactly one spread of the whole subject: its root head-tag send on the
        // INV-S6-scoped root location channel is present.
        let root_tag_sends = call
            .sends
            .iter()
            .filter(|send| {
                gstring(send.chan.as_ref().expect("chan"))
                    == Some(indexed_channel(&subject, "loc", &[]).as_str())
            })
            .count();
        assert_eq!(root_tag_sends, 1, "exactly ONE spread is appended");
    }

    #[test]
    fn per_rule_installs_are_per_entry_unshared() {
        // Two entries with DISTINCT ops f and h over a subject with two
        // f-positions and one h-position: 3 installed receivers (2 for f's
        // rule + 1 for h's rule) — the per-rule ∥-comprehension, unshared.
        let ruleset = direct_ruleset(
            vec![
                (PatternId(0), Pattern::app("f".to_string(), vec![Pattern::var("x")])),
                (PatternId(1), Pattern::app("h".to_string(), vec![Pattern::var("y")])),
            ],
            vec![(PatternId(0), "sa:f"), (PatternId(1), "sa:h")],
            Vec::new(),
        );
        let subject = GroundTerm::new(
            "Pair",
            vec![
                GroundTerm::new("f", vec![GroundTerm::nullary("A")]),
                GroundTerm::new(
                    "Pair",
                    vec![
                        GroundTerm::new("f", vec![GroundTerm::nullary("B")]),
                        GroundTerm::new("h", vec![GroundTerm::nullary("C")]),
                    ],
                ),
            ],
        );
        let (call, installed) = naive_kt_match_call_par(
            &ruleset,
            &subject,
            "site0",
            "OUT",
            NaiveGuardEncoding::PatternGuard,
        )
        .expect("distinct-op entries emit");
        assert_eq!(installed, 3, "2 f-sites + 1 h-site, per rule");
        assert_closed(&call, "the two-rule naive match call");
    }

    #[test]
    fn contextual_call_mirrors_the_bridge_and_swaps_in_the_naive_locator() {
        let ruleset = direct_ruleset(
            vec![(
                PatternId(0),
                Pattern::app("Swap".to_string(), vec![Pattern::var("x"), Pattern::var("y")]),
            )],
            vec![(PatternId(0), "sa:flip")],
            vec![RhoNetContextualMatchEntry {
                fired_rule_label: "WrapCong".to_string(),
                premise_channels: vec!["ctx:WrapCong:p0".to_string()],
                hole_positions: vec![vec![("Wrap".to_string(), 0)]],
            }],
        );
        let subject = GroundTerm::new(
            "Wrap",
            vec![GroundTerm::new(
                "Swap",
                vec![GroundTerm::nullary("A"), GroundTerm::nullary("B")],
            )],
        );
        let call = naive_kt_contextual_match_call_par(
            &ruleset,
            &subject,
            "site0",
            "OUT",
            NaiveGuardEncoding::PatternGuard,
        )
        .expect("the 1-hole contextual workload emits naively");
        assert_closed(&call, "the naive contextual match call");

        // The VERBATIM hole bridge reads ph:{premise} and re-delivers on the
        // premise channel with @out (the last — here only — hole).
        let hole_channel = "ph:ctx:WrapCong:p0";
        let bridge = call
            .receives
            .iter()
            .find(|receive| {
                gstring(receive.binds[0].source.as_ref().expect("source")) == Some(hole_channel)
            })
            .expect("the hole bridge is co-installed");
        let bridge_send = &bridge.body.as_ref().expect("bridge body").sends[0];
        assert_eq!(
            gstring(bridge_send.chan.as_ref().expect("chan")),
            Some("ctx:WrapCong:p0"),
            "the bridge re-delivers on the join's premise channel"
        );
        assert_eq!(gstring(&bridge_send.data[1]), Some("OUT"), "the last hole carries @out");

        // The naive locator at the hole site: a persistent tag receive on the
        // hole's loc: channel whose accept routes to the ph: hole channel.
        let locator = call
            .receives
            .iter()
            .find(|receive| {
                receive.persistent
                    && gstring(receive.binds[0].source.as_ref().expect("source"))
                        == Some(indexed_channel(&subject, "loc", &[0]).as_str())
            })
            .expect("the naive locator is installed at the hole site");
        let cap_x = &locator.body.as_ref().expect("locator body").receives[0];
        let cap_y = &cap_x.body.as_ref().expect("x body").receives[0];
        let accept = &cap_y.body.as_ref().expect("y body").sends[0];
        assert_eq!(gstring(accept.chan.as_ref().expect("chan")), Some("sa:flip"));
        assert_eq!(
            gstring(&accept.data[2]),
            Some(hole_channel),
            "the locator's accept out is the hole's ph: channel"
        );
    }

    #[test]
    fn contextual_call_fails_closed_off_the_context_shape() {
        let ruleset = direct_ruleset(
            vec![(
                PatternId(0),
                Pattern::app("Swap".to_string(), vec![Pattern::var("x"), Pattern::var("y")]),
            )],
            vec![(PatternId(0), "sa:flip")],
            vec![RhoNetContextualMatchEntry {
                fired_rule_label: "WrapCong".to_string(),
                premise_channels: vec!["ctx:WrapCong:p0".to_string()],
                hole_positions: vec![vec![("Wrap".to_string(), 0)]],
            }],
        );
        // A normal-form hole: no located redex ⇒ the bijection fails closed
        // with the SAME typed reason as the optimized driver.
        let normal = GroundTerm::new(
            "Wrap",
            vec![GroundTerm::new(
                "Pair",
                vec![GroundTerm::nullary("A"), GroundTerm::nullary("B")],
            )],
        );
        assert_eq!(
            naive_kt_contextual_match_call_par(
                &ruleset,
                &normal,
                "site0",
                "OUT",
                NaiveGuardEncoding::PatternGuard,
            ),
            Err(NaiveKtContextualUnsupported::Context(
                AutomatonUnsupported::ContextualHoleMismatch
            ))
        );
        // No contextual family at all ⇒ fail closed identically.
        let no_ctx = direct_ruleset(
            vec![(
                PatternId(0),
                Pattern::app("Swap".to_string(), vec![Pattern::var("x"), Pattern::var("y")]),
            )],
            vec![(PatternId(0), "sa:flip")],
            Vec::new(),
        );
        assert_eq!(
            naive_kt_contextual_match_call_par(
                &no_ctx,
                &normal,
                "site0",
                "OUT",
                NaiveGuardEncoding::PatternGuard,
            ),
            Err(NaiveKtContextualUnsupported::Context(
                AutomatonUnsupported::ContextualHoleMismatch
            ))
        );
    }

    #[test]
    fn every_unsupported_variant_displays() {
        // Display is part of the fail-closed surface (benchmark logs print it).
        let variants = [
            NaiveKtUnsupported::VariableRootPattern,
            NaiveKtUnsupported::NonLinearEntry,
            NaiveKtUnsupported::OverlappingTagDemand {
                op: "g".to_string(),
                demanding_entry: PatternId(0),
                root_entry: PatternId(1),
            },
        ];
        for variant in variants {
            assert!(!variant.to_string().is_empty(), "{variant:?} must render");
        }
        let contextual =
            NaiveKtContextualUnsupported::Context(AutomatonUnsupported::ContextualHoleMismatch);
        assert!(!contextual.to_string().is_empty());
        let wrapped = NaiveKtContextualUnsupported::Naive(NaiveKtUnsupported::NonLinearEntry);
        assert!(!wrapped.to_string().is_empty());
    }

    // ── R3 (self-driving) unit tests ─────────────────────────────────────────

    /// The β-shaped direct ruleset `App(^lambda(fun), arg) → sa:beta` and the
    /// depth-2 identity chain subject the R3 tests share.
    fn beta_ruleset_and_chain() -> (InRhoMatchingRuleset, GroundTerm) {
        let ruleset = direct_ruleset(
            vec![(
                PatternId(0),
                Pattern::app(
                    "App".to_string(),
                    vec![
                        Pattern::app(
                            crate::rho_net_lower::LAMBDA_REFLECT_LABEL.to_string(),
                            vec![Pattern::var("fun")],
                        ),
                        Pattern::var("arg"),
                    ],
                ),
            )],
            vec![(PatternId(0), "sa:beta")],
            Vec::new(),
        );
        let identity = GroundTerm::new(
            crate::rho_net_lower::LAMBDA_REFLECT_LABEL,
            vec![GroundTerm::new(
                crate::rho_net_lower::BOUND_VAR_REFLECT_LABEL,
                vec![GroundTerm::nullary(crate::rho_net_lower::PEANO_ZERO_REFLECT_LABEL)],
            )],
        );
        let chain = GroundTerm::new(
            "App",
            vec![
                identity.clone(),
                GroundTerm::new("App", vec![identity, GroundTerm::nullary("A")]),
            ],
        );
        (ruleset, chain)
    }

    /// The persistent receive of `call` whose single-bind SOURCE is exactly
    /// `source` (a ground channel `Par`), or panic.
    fn persistent_receive_on<'a>(call: &'a Par, source: &Par, what: &str) -> &'a Receive {
        call.receives
            .iter()
            .find(|receive| receive.persistent && receive.binds[0].source.as_ref() == Some(source))
            .unwrap_or_else(|| panic!("{what}: no persistent receive on {source:?}"))
    }

    /// R3 emission shape: one installed entry receiver whose innermost accept
    /// targets the `^respread-root` dispatcher; the dispatcher (1 formal) and
    /// route walker (2 formals) are persistent contracts on their reserved
    /// `GPrivate` channels; exactly one reflected-subject route seed is
    /// appended; the whole call is closed.
    #[test]
    fn selfdriving_call_emits_dispatcher_walker_and_the_rerouted_accept() {
        let (ruleset, chain) = beta_ruleset_and_chain();
        let (call, installed) = naive_kt_selfdriving_call_par(&ruleset, &chain, "site0", "OUT")
            .expect("the β chain admits the R3 self-driving call");
        assert_eq!(installed, 1, "one entry ⇒ one installed R3 root receiver");
        assert_closed(&call, "the R3 self-driving call");

        // The matcher: persistent on the compact root location, tag-as-pattern ⌜App⌝.
        let loc_root = new_gstring_par(indexed_channel(&chain, "loc", &[]), Vec::new(), false);
        let matcher = persistent_receive_on(&call, &loc_root, "R3 matcher");
        assert_eq!(matcher.binds[0].patterns[0], tag_par("App"));
        assert_eq!(matcher.bind_count, 0, "PatternGuard binds nothing at the tag");

        // The innermost accept: sa:beta!(σ_fun, σ_arg, ⌜^respread-root⌝) — the
        // shared σ frame with the OUT slot swapped to the dispatcher channel.
        let descent = &matcher.body.as_ref().expect("matcher body").receives[0];
        let cap_fun = &descent.body.as_ref().expect("descent body").receives[0];
        let cap_arg = &cap_fun.body.as_ref().expect("fun body").receives[0];
        let accept = &cap_arg.body.as_ref().expect("arg body").sends[0];
        assert_eq!(gstring(accept.chan.as_ref().expect("chan")), Some("sa:beta"));
        assert_eq!(accept.data.len(), 3, "σ_fun, σ_arg, dispatcher");
        assert_eq!(boundvar_index(&accept.data[0]), Some(1), "σ[fun] = BoundVar(1)");
        assert_eq!(boundvar_index(&accept.data[1]), Some(0), "σ[arg] = BoundVar(0)");
        assert_eq!(
            accept.data[2],
            trs::tag_par(FP, RESPREAD_ROOT_RESERVED_LABEL),
            "the accept's OUT slot is the ^respread-root dispatcher channel"
        );
        // Byte-identity of everything EXCEPT the swapped slot: the σ prefix
        // equals the shared build_accept_send's σ prefix.
        let shared = build_accept_send("sa:beta", "OUT", 2, &[0, 1]);
        assert_eq!(accept.data[..2], shared.sends[0].data[..2]);
        assert_eq!(accept.chan, shared.sends[0].chan);

        // The dispatcher: persistent 1-formal contract on ⌜^respread-root⌝.
        let dispatcher = persistent_receive_on(
            &call,
            &trs::tag_par(FP, RESPREAD_ROOT_RESERVED_LABEL),
            "R3 dispatcher",
        );
        assert_eq!(dispatcher.bind_count, 1, "dispatcher binds the delivered reduct");

        // The walker: persistent 2-formal contract on ⌜^respread⌝.
        let walker =
            persistent_receive_on(&call, &trs::tag_par(FP, RESPREAD_RESERVED_LABEL), "R3 walker");
        assert_eq!(walker.bind_count, 2, "walker binds (t, route)");

        // Exactly one initial route seed carries the whole reflected subject.
        let seeds: Vec<_> = call
            .sends
            .iter()
            .filter(|send| send.chan.as_ref() == Some(&trs::tag_par(FP, RESPREAD_RESERVED_LABEL)))
            .collect();
        assert_eq!(seeds.len(), 1, "exactly one initial route seed is appended");
        assert_eq!(seeds[0].data.len(), 2, "^respread!(reflected-subject, route)");
        assert_eq!(gstring(&seeds[0].data[1]), Some("@r2:0000000000000000"));
    }

    /// The dispatcher routes a REDEX-rooted reduct to the walker seeded with
    /// the entry's fixed route, an admitted NF-rooted reduct to OUT, and any
    /// alien head to the typed `^respread-err` channel (fail-closed).
    #[test]
    fn selfdriving_dispatcher_routes_redex_nf_and_alien_heads() {
        let (ruleset, chain) = beta_ruleset_and_chain();
        let (call, _) = naive_kt_selfdriving_call_par(&ruleset, &chain, "site0", "OUT")
            .expect("the β chain admits");
        let dispatcher = persistent_receive_on(
            &call,
            &trs::tag_par(FP, RESPREAD_ROOT_RESERVED_LABEL),
            "R3 dispatcher",
        );
        let dispatch = &dispatcher.body.as_ref().expect("dispatcher body").matches[0];
        // Arms: 1 redex root (App) + 4 NF labels (A, Z, ^bound, ^lambda) + 1
        // wildcard = 6, sorted-label deterministic.
        assert_eq!(dispatch.cases.len(), 6, "1 redex + 4 NF + wildcard arms");

        // The App arm seeds the walker with (t, root-route).
        let app_arm = dispatch
            .cases
            .iter()
            .find(|case| {
                case.pattern
                    .as_ref()
                    .is_some_and(|pattern| format!("{pattern:?}").contains("EListBody"))
                    && format!("{:?}", case.pattern)
                        .contains(&format!("{:?}", tag_par("App").unforgeables[0]))
            })
            .expect("the App redex arm exists");
        let seed = &app_arm.source.as_ref().expect("App arm body").sends[0];
        assert_eq!(
            seed.chan.as_ref(),
            Some(&trs::tag_par(FP, RESPREAD_RESERVED_LABEL)),
            "a redex-rooted reduct is sent to the walker"
        );
        assert_eq!(seed.data.len(), 2, "^respread!(t, route)");
        assert_eq!(boundvar_index(&seed.data[0]), Some(0), "t is the bound reduct");
        assert_eq!(gstring(&seed.data[1]), Some("@r2:0000000000000000"));

        // An NF arm (the terminal atom A) sends the reduct to OUT.
        let a_arm = dispatch
            .cases
            .iter()
            .find(|case| {
                format!("{:?}", case.pattern)
                    .contains(&format!("{:?}", tag_par("A").unforgeables[0]))
            })
            .expect("the A NF arm exists");
        let out_send = &a_arm.source.as_ref().expect("A arm body").sends[0];
        assert_eq!(gstring(out_send.chan.as_ref().expect("chan")), Some("OUT"));
        assert_eq!(boundvar_index(&out_send.data[0]), Some(0), "the NF is forwarded whole");

        // The LAST arm is the fail-closed wildcard → ^respread-err.
        let last = dispatch.cases.last().expect("wildcard arm");
        assert_eq!(last.pattern.as_ref(), Some(&new_wildcard_par(Vec::new(), true)));
        let err_send = &last.source.as_ref().expect("wildcard body").sends[0];
        assert_eq!(
            err_send.chan.as_ref(),
            Some(&trs::tag_par(FP, RESPREAD_ERR_RESERVED_LABEL)),
            "an alien head fails closed to the typed error channel"
        );
    }

    /// The walker carries one exact-arity arm per pattern constructor shape
    /// plus the fail-closed wildcard. Each route publishes one compact head
    /// tag, captures variable children directly, and descends only into child
    /// constructor states.
    #[test]
    fn selfdriving_walker_arms_cover_pattern_routes_and_fail_closed() {
        let (ruleset, chain) = beta_ruleset_and_chain();
        let (call, _) = naive_kt_selfdriving_call_par(&ruleset, &chain, "site0", "OUT")
            .expect("the β chain admits");
        let walker =
            persistent_receive_on(&call, &trs::tag_par(FP, RESPREAD_RESERVED_LABEL), "R3 walker");
        let dispatch = &walker.body.as_ref().expect("walker body").matches[0];
        // Pattern constructor map {(App,2), (^lambda,1)} + wildcard = 3.
        assert_eq!(dispatch.cases.len(), 3, "2 pattern constructor arms + wildcard");

        // The App route: @loc!(⌜App⌝), one descent into ^lambda, and one
        // direct capture of arg. The captured argument's subtree is not walked.
        let app_arm = dispatch
            .cases
            .iter()
            .find(|case| {
                case.free_count == 2
                    && format!("{:?}", case.pattern)
                        .contains(&format!("{:?}", tag_par("App").unforgeables[0]))
            })
            .expect("the binary App arm exists");
        let route_dispatch = &app_arm.source.as_ref().expect("App arm body").matches[0];
        assert_eq!(route_dispatch.cases.len(), 1, "one App route in the β pattern");
        let body = route_dispatch.cases[0]
            .source
            .as_ref()
            .expect("App route body");
        assert_eq!(body.sends.len(), 3, "tag + one descent + one direct capture");
        let recursions: Vec<_> = body
            .sends
            .iter()
            .filter(|send| send.chan.as_ref() == Some(&trs::tag_par(FP, RESPREAD_RESERVED_LABEL)))
            .collect();
        assert_eq!(recursions.len(), 1, "only the constructor child is traversed");
        assert_eq!(recursions[0].data.len(), 2, "^respread!(child, fixed-route)");
        assert_eq!(gstring(&recursions[0].data[1]), Some("@r2:0000000000000001"));
        assert!(
            !format!("{call:?}").contains("EPlusPlusBody"),
            "R3 must not rebuild channel paths with runtime string concatenation"
        );

        // The wildcard arm fails closed to ^respread-err.
        let last = dispatch.cases.last().expect("wildcard arm");
        assert_eq!(last.pattern.as_ref(), Some(&new_wildcard_par(Vec::new(), true)));
        let err_send = &last.source.as_ref().expect("wildcard body").sends[0];
        assert_eq!(err_send.chan.as_ref(), Some(&trs::tag_par(FP, RESPREAD_ERR_RESERVED_LABEL)));
    }

    /// Route and compact-channel identities stay fixed width as a pattern
    /// grows; no identity contains its ancestors' constructor text.
    #[test]
    fn selfdriving_route_and_channel_tokens_are_fixed_width() {
        let route_width = selfdriving_route_key(0).len();
        for position in [0, 1, 17, 65_535, u64::MAX - 1] {
            assert_eq!(selfdriving_route_key(position).len(), route_width);
            assert_eq!(
                compact_position_channel("loc", FP, "site0", position).len(),
                compact_position_channel("loc", FP, "site0", 0).len()
            );
        }
    }

    /// R3 admission matrix: repeated labels at different subject arities are
    /// safe under route dispatch, while a reserved control label and an AC
    /// carrier still reject before emission.
    #[test]
    fn selfdriving_admits_mixed_arities_and_rejects_reserved_or_collection_subjects() {
        let (ruleset, _) = beta_ruleset_and_chain();
        // A occurs at arity 1 and arity 0 below a valid App root. The route PDA
        // does not dispatch on subject-wide arity metadata, so this is safe.
        let mixed_arity = GroundTerm::new(
            "App",
            vec![
                GroundTerm::new(
                    crate::rho_net_lower::LAMBDA_REFLECT_LABEL,
                    vec![GroundTerm::new(
                        crate::rho_net_lower::BOUND_VAR_REFLECT_LABEL,
                        vec![GroundTerm::nullary(crate::rho_net_lower::PEANO_ZERO_REFLECT_LABEL)],
                    )],
                ),
                GroundTerm::new("A", vec![GroundTerm::nullary("A")]),
            ],
        );
        assert!(
            naive_kt_selfdriving_call_par(&ruleset, &mixed_arity, "site0", "OUT").is_ok(),
            "fixed pattern routes make subject-wide arity conflicts irrelevant"
        );
        // A reserved rendezvous label as a subject constructor.
        let reserved = GroundTerm::new(RESPREAD_RESERVED_LABEL, vec![GroundTerm::nullary("A")]);
        assert_eq!(
            naive_kt_selfdriving_call_par(&ruleset, &reserved, "site0", "OUT"),
            Err(NaiveKtUnsupported::SelfDrivingReservedLabel {
                op: RESPREAD_RESERVED_LABEL.to_string(),
            })
        );
        // An AC collection node.
        let bag = GroundTerm::collection(
            mettail_ast::types::CollectionType::HashBag,
            "PPar",
            vec![GroundTerm::nullary("A")],
        );
        assert_eq!(
            naive_kt_selfdriving_call_par(&ruleset, &bag, "site0", "OUT"),
            Err(NaiveKtUnsupported::SelfDrivingCollectionSubject { op: "PPar".to_string() })
        );
        // The new variants render (fail-closed Display surface).
        for variant in [
            NaiveKtUnsupported::SelfDrivingReservedLabel { op: "^respread".to_string() },
            NaiveKtUnsupported::SelfDrivingCollectionSubject { op: "PPar".to_string() },
        ] {
            assert!(!variant.to_string().is_empty(), "{variant:?} must render");
        }
    }

    /// A random LINEAR, App-ROOTED pattern for the accept byte-identity
    /// property: a small App tree over a 3-op alphabet whose Var leaves are
    /// named `v{0}`, `v{1}`, … in DFS order (distinct by construction ⇒
    /// linear). The root is FORCED to be an App (a Var root is the separate
    /// `rejects_a_variable_root_pattern` case, not this property's domain).
    fn linear_pattern_strategy() -> impl Strategy<Value = Pattern<String>> {
        fn op_strategy() -> impl Strategy<Value = String> {
            prop::sample::select(vec!["f".to_string(), "g".to_string(), "h".to_string()])
        }
        // Sub-pattern: a Var leaf or a nested App (names assigned afterwards).
        let node = Just(Pattern::var("placeholder")).prop_recursive(3, 12, 3, |inner| {
            (op_strategy(), prop::collection::vec(inner, 1..=3))
                .prop_map(|(op, args)| Pattern::app(op, args))
        });
        // Root: always an App over 1..=3 sub-patterns.
        (op_strategy(), prop::collection::vec(node, 1..=3))
            .prop_map(|(op, args)| Pattern::app(op, args))
            .prop_map(|pattern| {
                let mut counter = 0usize;
                rename_vars_dfs(&pattern, &mut counter)
            })
    }

    /// Rebuild `pattern` with DFS-fresh variable names `v0, v1, …` (linear).
    fn rename_vars_dfs(pattern: &Pattern<String>, counter: &mut usize) -> Pattern<String> {
        match pattern {
            Pattern::Var(_) => {
                let name = format!("v{counter}");
                *counter += 1;
                Pattern::var(name)
            },
            Pattern::App { op, args } => {
                let renamed = args
                    .iter()
                    .map(|arg| rename_vars_dfs(arg, counter))
                    .collect::<Vec<_>>();
                Pattern::app(op.clone(), renamed)
            },
            // The strategy never generates AC patterns.
            other => panic!("linear_pattern_strategy generated a non-structural node: {other:?}"),
        }
    }

    /// Descend a naive receiver to its innermost accept send (through tag
    /// receives / captures and, for ConsumeTest, the tag `Match` cases).
    fn innermost_send(par: &Par) -> &models::rhoapi::Send {
        let mut node = par;
        loop {
            if let Some(send) = node.sends.first() {
                return send;
            }
            if let Some(receive) = node.receives.first() {
                node = receive.body.as_ref().expect("receive body");
                continue;
            }
            if let Some(m) = node.matches.first() {
                // The tag case (case 0) holds the continuation; the else-arm
                // republish is a send but lives in case 1, never on this path.
                node = m.cases[0].source.as_ref().expect("tag case body");
                continue;
            }
            panic!("no innermost send found in the naive receiver");
        }
    }

    proptest! {
        /// For ARBITRARY linear entries, under BOTH encodings, the naive
        /// receiver's innermost accept send equals `build_accept_send`'s output
        /// for the same (accept, out, k, first_occ) — the accept ABI
        /// byte-identity the benchmark equivalence rests on. (`Par` is a prost
        /// message with pure-data fields, so structural equality is
        /// serialization equality.)
        #[test]
        fn naive_accept_send_is_byte_identical_to_the_shared_accept(
            pattern in linear_pattern_strategy(),
            consume_test in proptest::bool::ANY,
        ) {
            let subject = subject_for_pattern(&pattern);
            let automaton = SetAutomaton::compile_structural([(PatternId(0), pattern)])
                .expect("a linear structural pattern compiles");
            let view = automaton.view();
            // k = the number of Var leaves (DFS) — recount independently.
            let mut descents = Vec::new();
            let mut captures = Vec::new();
            let mut capture_slots = Vec::new();
            let locations = SubjectLocationIndex::new(&subject);
            if let AutomatonNode::App { args, .. } = view.node(view.entry_root_state(0)) {
                for (index, arg) in args.iter().enumerate() {
                    collect_nested_schedule(
                        &view,
                        arg.state(),
                        arg.parent_slots().collect(),
                        &locations,
                        "site0",
                        FP,
                        locations.matcher_child(
                            MatcherPosition::Live(SubjectPosition::ROOT),
                            index,
                        ),
                        &mut descents,
                        &mut captures,
                        &mut capture_slots,
                    );
                }
            }
            let k = captures.len();
            let first_occ: Vec<usize> = (0..k).collect();
            let expected = build_accept_send("sa:acc", "OUT", k, &first_occ);

            let encoding = if consume_test {
                NaiveGuardEncoding::ConsumeTest
            } else {
                NaiveGuardEncoding::PatternGuard
            };
            let network = naive_kt_entry_receiver_par(
                &view, 0, &subject, "site0", "sa:acc", "OUT", FP, encoding,
            )
            .expect("a linear entry emits");
            prop_assert!(network.locally_free.is_empty(), "the receiver is closed");
            prop_assert!(!network.connective_used);
            let actual = innermost_send(&network);
            prop_assert_eq!(
                actual,
                &expected.sends[0],
                "the naive accept send must be build_accept_send's output byte-for-byte"
            );
        }
    }
}
