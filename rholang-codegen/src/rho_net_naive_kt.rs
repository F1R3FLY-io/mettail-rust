//! Track B — B1: the NAIVE Knotted-Topoi Appendix-A baseline emitter
//! (BENCHMARK-ONLY, quarantined behind the `bench-naive-baseline` feature).
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
//! fingerprint), reads the SAME spread ABI (every channel derived through
//! [`spread_root_location`] / [`spread_child_location`] /
//! [`collapse_capture_location`] — the one shared derivation), and emits its
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
//! # Quarantine
//!
//! Behind `bench-naive-baseline` ONLY. No production entry point, driver, or
//! macro-generated code references this module; budgets/metering remain
//! entirely F1r3node's concern and no cost surface exists here.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use dovetail::set_automaton::{AutomatonNode, PatternId, SetAutomatonView};
use models::rhoapi::expr::ExprInstance;
use models::rhoapi::var::{VarInstance, WildcardMsg};
use models::rhoapi::{EPlusPlus, Expr, MatchCase, Par, Receive, ReceiveBind, Var};
use models::rust::rholang::implicits::GPrivateBuilder;
use models::rust::utils::{
    new_boundvar_par, new_elist_par, new_freevar_par, new_gstring_par, new_match_par, new_send_par,
    new_wildcard_par,
};

use crate::rho_net_automaton::{
    bits, build_accept_send, collect_nested_schedule, wrap_capture_chain, AutomatonUnsupported,
    Descent,
};
use crate::rho_net_lower::{
    collapse_capture_location, contextual_hole_bridge_par, contextual_premise_hole_channel,
    reflect_tag, spread_child_location, spread_root_location, spread_term_par,
    walk_ground_term_locations, GroundTerm,
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
    /// R3 (self-driving) only: the subject uses one constructor label at two
    /// DIFFERENT arities, so the `^respread` walker cannot carry one exact-arity
    /// dispatch arm per label — the emitter fails closed rather than emit a
    /// walker whose wildcard arm would swallow a live constructor shape.
    SelfDrivingArityConflict {
        /// The conflicting constructor label.
        op: String,
        /// The first arity observed for `op` (subject pre-order).
        arity_a: usize,
        /// The conflicting arity observed later.
        arity_b: usize,
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
            Self::SelfDrivingArityConflict { op, arity_a, arity_b } => write!(
                f,
                "naive Knotted-Topoi R3 (self-driving): subject constructor `{op}` occurs at \
                 arity {arity_a} AND arity {arity_b} — the ^respread walker needs one exact-arity \
                 arm per label"
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
    descents: Vec<Descent>,
    captures: Vec<String>,
}

/// Collect one entry's schedule at `site`, running the per-entry admission
/// gates: a Var root fails closed ([`NaiveKtUnsupported::VariableRootPattern`]),
/// a repeated Var name fails closed ([`NaiveKtUnsupported::NonLinearEntry`]).
fn collect_entry_schedule(
    view: &SetAutomatonView<'_, String>,
    entry: usize,
    language_fingerprint: &str,
    site: &str,
) -> Result<NaiveEntrySchedule, NaiveKtUnsupported> {
    let root = view.entry_root_state(entry);
    match view.node(root) {
        AutomatonNode::Var(_) => Err(NaiveKtUnsupported::VariableRootPattern),
        AutomatonNode::App { op, args } => {
            let root_op = op.to_string();
            let root_loc = spread_root_location(language_fingerprint, site);
            let cap_root = collapse_capture_location(language_fingerprint, site);
            let mut descents: Vec<Descent> = Vec::new();
            let mut captures: Vec<String> = Vec::new();
            let mut names: Vec<String> = Vec::new();
            for (index, &arg) in args.iter().enumerate() {
                let child_loc = spread_child_location(&root_loc, &root_op, index);
                let child_cap = spread_child_location(&cap_root, &root_op, index);
                collect_nested_schedule(
                    view,
                    arg,
                    &child_loc,
                    &child_cap,
                    &mut descents,
                    &mut captures,
                    &mut names,
                );
            }
            let is_linear = names
                .iter()
                .enumerate()
                .all(|(i, name)| !names[..i].contains(name));
            if !is_linear {
                return Err(NaiveKtUnsupported::NonLinearEntry);
            }
            Ok(NaiveEntrySchedule { root_op, descents, captures })
        },
    }
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
            AutomatonNode::Var(_) => {},
            AutomatonNode::App { op, args } => {
                ops.push(op.to_string());
                work.extend(args.iter().rev().copied());
            },
        }
    }
}

/// The RULESET-level admission gates, run BEFORE any emission:
///
/// 1. per-entry: Var root / non-linear entry (via [`collect_entry_schedule`]
///    at a probe site AND a probe INV-S6 scope — only names and node kinds
///    matter, so neither the site string nor the fingerprint scope can change
///    the verdict);
/// 2. [`NaiveKtUnsupported::OverlappingTagDemand`]: no entry's NON-ROOT op may
///    equal any entry's ROOT op (nested-vs-root demand), and no two DISTINCT
///    entries may share a ROOT op (duplicate-root demand). See the variant's
///    rustdoc for why each shape drops a match under the once-published spread.
fn validate_naive_ruleset(view: &SetAutomatonView<'_, String>) -> Result<(), NaiveKtUnsupported> {
    /// The INV-S6 scope the admission PROBE derives its throwaway channel names under.
    /// `validate_naive_ruleset` inspects only `schedule.root_op` and the linearity of the
    /// capture names, never a channel string, so the scope cannot reach the verdict — the
    /// same reason the probe passes a fixed `"gate-probe"` site. Using a fixed probe value
    /// keeps the gate callable where no language fingerprint is in scope.
    const GATE_PROBE_FINGERPRINT: &str = "mettail-langdef-v1:0000000000000000";

    let entry_count = view.entry_count();
    // Per-entry root op (also runs the Var-root + linearity gates).
    let mut root_ops: Vec<(PatternId, String)> = Vec::with_capacity(entry_count);
    for entry in 0..entry_count {
        let schedule = collect_entry_schedule(view, entry, GATE_PROBE_FINGERPRINT, "gate-probe")?;
        root_ops.push((view.entry_id(entry), schedule.root_op));
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
            for &arg in args {
                collect_non_root_ops(view, arg, &mut non_root_ops);
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
    site: &str,
    accept_channel: &str,
    out_channel: &str,
    language_fingerprint: &str,
    encoding: NaiveGuardEncoding,
) -> Result<Par, NaiveKtUnsupported> {
    let schedule = collect_entry_schedule(view, entry, language_fingerprint, site)?;
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
    Ok(naive_tag_receive(
        &spread_root_location(language_fingerprint, site),
        root_tag,
        body,
        true,
        encoding,
    ))
}

/// Collect the per-position SITE strings of `node` whose head constructor is
/// `root_op` — the single-rule specialization of the optimized driver's
/// `collect_redex_sites` walk, with the SAME site-string derivation
/// ([`spread_child_location`] folded from `location`), so a receiver built at a
/// collected site reads exactly the channels the ONE spread publishes there.
fn collect_entry_sites(node: &GroundTerm, location: &str, root_op: &str, sites: &mut Vec<String>) {
    walk_ground_term_locations(node, location, |node, location| {
        if node.constructor == root_op {
            sites.push(location.to_string());
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

    let mut call = Par::default();
    let mut installed = 0usize;
    for entry in 0..view.entry_count() {
        let root_op = match view.node(view.entry_root_state(entry)) {
            AutomatonNode::App { op, .. } => op.to_string(),
            // Unreachable past `validate_naive_ruleset`, kept total + typed.
            AutomatonNode::Var(_) => return Err(NaiveKtUnsupported::VariableRootPattern),
        };
        let accept_channel = entry_accept_channel(ruleset, view.entry_id(entry));
        let mut sites: Vec<String> = Vec::new();
        collect_entry_sites(subject, root_site, &root_op, &mut sites);
        for site in &sites {
            let receiver = naive_kt_entry_receiver_par(
                &view,
                entry,
                site,
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

/// The subject subterm at a contextual HOLE path (each `(op, index)` step must
/// match the subject's constructor at that level — the same shape the expected
/// site string encodes), or `None` on a drift. The bijection check has already
/// verified the located/expected correspondence, so a `None` here is defensive
/// (it fails closed as a hole mismatch, mirroring the optimized driver's
/// defensive arms).
fn subject_subterm_at<'t>(
    subject: &'t GroundTerm,
    path: &[(String, usize)],
) -> Option<&'t GroundTerm> {
    let mut node = subject;
    for (op, index) in path {
        if node.constructor != *op {
            return None;
        }
        node = node.children.get(*index)?;
    }
    Some(node)
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
/// hole sites are disjoint-prefix sibling positions, so two per-hole naive
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

    // The `n` expected hole sites — the SAME `spread_child_location` fold.
    let expected_sites: Vec<String> = entry
        .hole_positions
        .iter()
        .map(|path| {
            path.iter()
                .fold(root_site.to_string(), |site, (op, index)| {
                    spread_child_location(&site, op, *index)
                })
        })
        .collect();

    // LOAD-BEARING bijection check: the subject's located rule-root redexes must
    // be EXACTLY the `n` expected hole positions (as a multiset).
    let roots = crate::rule_lhs_root_constructors(ruleset);
    let mut located: Vec<String> = Vec::new();
    collect_ruleset_sites(subject, root_site, &roots, &mut located);
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
    for (index, expected_site) in expected_sites.iter().enumerate() {
        let premise_channel = &entry.premise_channels[index];
        let hole_channel = contextual_premise_hole_channel(premise_channel);

        // The subject's head at the hole (defensive: a drift fails closed).
        let hole_subterm = subject_subterm_at(subject, &entry.hole_positions[index]).ok_or(
            NaiveKtContextualUnsupported::Context(AutomatonUnsupported::ContextualHoleMismatch),
        )?;
        // Install the head-matching entry's receiver AT the hole site, its
        // accept routed to the hole's intermediate `ph:` channel (the join's
        // premise ABI is completed by the bridge below). After the
        // duplicate-root gate at most one entry matches; the bijection check
        // guarantees at least one does (the hole head is a rule root).
        for automaton_entry in 0..view.entry_count() {
            let root_op = match view.node(view.entry_root_state(automaton_entry)) {
                AutomatonNode::App { op, .. } => op.to_string(),
                AutomatonNode::Var(_) => {
                    return Err(NaiveKtContextualUnsupported::Naive(
                        NaiveKtUnsupported::VariableRootPattern,
                    ))
                },
            };
            if root_op != hole_subterm.constructor {
                continue;
            }
            let accept_channel = entry_accept_channel(ruleset, view.entry_id(automaton_entry));
            let receiver = naive_kt_entry_receiver_par(
                &view,
                automaton_entry,
                expected_site,
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
/// to `rho_net_ruleset`; the walk is four lines and derivation-shared via
/// [`spread_child_location`]).
fn collect_ruleset_sites(
    node: &GroundTerm,
    location: &str,
    roots: &std::collections::BTreeSet<String>,
    sites: &mut Vec<String>,
) {
    walk_ground_term_locations(node, location, |node, location| {
        if roots.contains(&node.constructor) {
            sites.push(location.to_string());
        }
        true
    });
}

// ─────────────────────────────────────────────────────────────────────────────
// R3 — the SELF-DRIVING exploratory variant (the PERSISTENT-fire regime probe)
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

/// GString `++` concatenation `a ++ b` as a TRS [`trs::Node`] — the ONE
/// combinator the walker needs beyond the subst-TRS set: a child's `loc:`/`cap:`
/// channel NAME is computed IN RHOLANG from the parent's name plus the constant
/// suffix `"/{op}.{index}"`, exactly [`spread_child_location`]'s derivation
/// (`format!("{parent}/{op}.{index}")`), so the walker's re-spread rendezvouses
/// with the SAME channels the matcher's static schedule reads. The reducer
/// evaluates `EPlusPlus` over two `GString`s to their concatenation (reduce.rs
/// `ExprInstance::EPlusPlusBody`, the string arm) both in channel and in data
/// position, so the computed name is materialized before every produce.
fn concat_str(a: trs::Node, b: trs::Node) -> trs::Node {
    let free = trs::union_free(&[a.free.as_slice(), b.free.as_slice()]);
    let free_bits = trs::free_bits(&free);
    let mut par = Par::default();
    par.exprs = vec![Expr {
        expr_instance: Some(ExprInstance::EPlusPlusBody(EPlusPlus {
            p1: Some(a.par),
            p2: Some(b.par),
        })),
    }];
    par.locally_free = free_bits;
    trs::Node { par, free }
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
    view: &SetAutomatonView<'_, String>,
    entry: usize,
    site: &str,
    accept_channel: &str,
    language_fingerprint: &str,
) -> Result<Par, NaiveKtUnsupported> {
    let schedule = collect_entry_schedule(view, entry, language_fingerprint, site)?;
    // Linear entry ⇒ first_occ = [0,…,k-1] (see `naive_kt_entry_receiver_par`).
    let k = schedule.captures.len();
    let first_occ: Vec<usize> = (0..k).collect();
    let respread_root = trs::tag_par(language_fingerprint, RESPREAD_ROOT_RESERVED_LABEL);
    let accept = build_accept_send_to_name(accept_channel, respread_root, k, &first_occ);
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
    Ok(naive_tag_receive(
        &spread_root_location(language_fingerprint, site),
        root_tag,
        body,
        true,
        NaiveGuardEncoding::PatternGuard,
    ))
}

/// Collect the subject's constructor → arity map (pre-order), running the R3
/// admission gates: an AC collection node fails closed
/// ([`NaiveKtUnsupported::SelfDrivingCollectionSubject`]), a label colliding
/// with a `^respread`-family rendezvous label fails closed
/// ([`NaiveKtUnsupported::SelfDrivingReservedLabel`]), and one label at two
/// arities fails closed ([`NaiveKtUnsupported::SelfDrivingArityConflict`]).
/// This map IS the walker's admitted dispatch set: β (the subst TRS) can only
/// rearrange/duplicate subject subtrees and rebuild `^bound`/Peano leaves that
/// already occur in the subject, so for the λ-chain family every reduct's
/// constructors are covered; anything else hits the walker's fail-closed
/// wildcard arm at runtime (a typed `^respread-err` send).
fn collect_selfdriving_arity_map(
    term: &GroundTerm,
    map: &mut BTreeMap<String, usize>,
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
        match map.get(&term.constructor) {
            Some(&arity) if arity != term.children.len() => {
                return Err(NaiveKtUnsupported::SelfDrivingArityConflict {
                    op: term.constructor.clone(),
                    arity_a: arity,
                    arity_b: term.children.len(),
                });
            },
            Some(_) => {},
            None => {
                map.insert(term.constructor.clone(), term.children.len());
            },
        }
        work.extend(term.children.iter().rev());
    }
    Ok(())
}

/// The R3 ROOT DISPATCHER `for(t <= ⌜^respread-root⌝){ match t { … } }` — the
/// persistent 1-ary contract every R3 firing's reduct is delivered to (it is
/// the accept's dynamic `out`; the installed σ-receiver / β-cascade sends
/// `out!(⟦reduct⟧)` and that send IS this contract's COMM):
///
/// * head tag ∈ `redex_root_ops` (the ruleset's entry root ops) → the reduct
///   can match again at the root: seed the walker
///   `^respread!(t, "loc:{root_site}", "cap:{root_site}")` so its spread
///   re-materializes at the SAME site prefix the persistent matcher reads —
///   matching continues in-session;
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
pub fn respread_root_receiver_par(
    language_fingerprint: &str,
    root_site: &str,
    out_channel: &str,
    redex_root_ops: &BTreeSet<String>,
    nf_labels: &BTreeSet<String>,
) -> Par {
    let fp = language_fingerprint;
    let chan = trs::tag_par(fp, RESPREAD_ROOT_RESERVED_LABEL);
    let env = trs::Env::root(&["t"]);
    let mut cases: Vec<trs::Case> = Vec::with_capacity(redex_root_ops.len() + nf_labels.len() + 1);
    for op in redex_root_ops {
        cases.push(trs::Case {
            pattern: head_tag_remainder_pattern(fp, op),
            free_count: 0,
            body: trs::send(
                trs::ground(trs::tag_par(fp, RESPREAD_RESERVED_LABEL)),
                vec![
                    env.var("t"),
                    trs::ground(new_gstring_par(
                        spread_root_location(fp, root_site),
                        Vec::new(),
                        false,
                    )),
                    trs::ground(new_gstring_par(
                        collapse_capture_location(fp, root_site),
                        Vec::new(),
                        false,
                    )),
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
    cases.push(trs::Case {
        pattern: trs::pat_wildcard(),
        free_count: 0,
        body: trs::send(
            trs::ground(trs::tag_par(fp, RESPREAD_ERR_RESERVED_LABEL)),
            vec![env.var("t")],
        ),
    });
    let body = trs::match_(env.var("t"), cases);
    trs::persistent_contract(chan, 1, body).par
}

/// The R3 WALKER `for(t, loc, cap <= ⌜^respread⌝){ match t { … } }` — the
/// persistent 3-ary reflected-term walker that re-emits one subtree's SPREAD at
/// a site prefix, fully in Rho (the `^subst`/`^shift` cascade's Match-dispatch
/// pattern over the reflected-term ABI, specialized from term REWRITING to term
/// RE-SPREADING). One exact-arity arm per admitted `(label, arity)`:
///
/// ```text
/// [⌜L⌝, c₀, …, c_{m-1}] =>
///     @loc!(⌜L⌝)                                  ← the head tag at loc:π
///   | @cap!(t)                                    ← ⟦subtree⟧ at cap:π (M-collapse)
///   | ^respread!(cᵢ, loc ++ "/L.i", cap ++ "/L.i")  per child  ← recurse
/// ```
///
/// so after a walk of `⟦t⟧` seeded at `(loc:π, cap:π)`, every node of `t` has
/// its head tag on its `loc:` channel and its reflected subtree on its `cap:`
/// channel — exactly the channels [`spread_term_par`]'s spread publishes at π
/// and the matcher's static schedule reads (child names derived by the SAME
/// `"{parent}/{op}.{index}"` rule, computed in-Rho by [`concat_str`]).
///
/// DELIBERATE difference from the host spread: NO `col:` publication. The
/// spread's `col:` channels exist only as the bottom-up collapse fold's
/// internal rendezvous (each consumed exactly once by the parent's fold); the
/// walker already HOLDS every node's collapsed value (`t` itself — a reflected
/// node IS its collapse, byte-identical per the `spread_term_par` rustdoc), so
/// it publishes `cap:` directly, installs no fold, and emitting `col:` values
/// would only rest as dead messages no receiver ever reads. Consequence for
/// the B4 counters: a re-spread contributes NO `col:`-join `matching_tau`
/// COMMs — its volume is measured by the NEW `respread_tau` class (one COMM
/// per walked node) instead.
///
/// Fail-closed: a head tag outside `arity_map` hits the wildcard arm — a typed
/// `⌜^respread-err⌝!(t)` send (resting; no receiver) — never a silent spread.
pub fn respread_walker_receiver_par(
    language_fingerprint: &str,
    arity_map: &BTreeMap<String, usize>,
) -> Par {
    let fp = language_fingerprint;
    let chan = trs::tag_par(fp, RESPREAD_RESERVED_LABEL);
    let env = trs::Env::root(&["t", "loc", "cap"]);
    let mut cases: Vec<trs::Case> = Vec::with_capacity(arity_map.len() + 1);
    for (label, &arity) in arity_map {
        let child_pats: Vec<Par> = (0..arity).map(trs::pat_free).collect();
        cases.push(trs::Case {
            pattern: trs::pat_tagged(fp, label, child_pats),
            free_count: arity,
            body: {
                // The `arity` captured children bind innermost (`FreeVar(i)` ⟹
                // `BoundVar(arity-1-i)`) — the subst-TRS congruence-arm frame.
                let child_names: Vec<String> = (0..arity).map(|i| format!("c{i}")).collect();
                let child_refs: Vec<&str> = child_names.iter().map(String::as_str).collect();
                let env = env.push(&child_refs);
                // @loc!(⌜L⌝) — this node's head tag on its location channel.
                let mut composed =
                    trs::send(env.var("loc"), vec![trs::ground(trs::tag_par(fp, label))]);
                // @cap!(t) — the reflected node IS its own collapse value.
                composed = trs::par2(composed, trs::send(env.var("cap"), vec![env.var("t")]));
                for (i, child) in child_refs.iter().enumerate() {
                    // The `spread_child_location` suffix "/{op}.{index}",
                    // appended in-Rho to BOTH prefixes.
                    let suffix = new_gstring_par(format!("/{label}.{i}"), Vec::new(), false);
                    let recurse = trs::send(
                        trs::ground(trs::tag_par(fp, RESPREAD_RESERVED_LABEL)),
                        vec![
                            env.var(child),
                            concat_str(env.var("loc"), trs::ground(suffix.clone())),
                            concat_str(env.var("cap"), trs::ground(suffix)),
                        ],
                    );
                    composed = trs::par2(composed, recurse);
                }
                composed
            },
        });
    }
    cases.push(trs::Case {
        pattern: trs::pat_wildcard(),
        free_count: 0,
        body: trs::send(
            trs::ground(trs::tag_par(fp, RESPREAD_ERR_RESERVED_LABEL)),
            vec![env.var("t")],
        ),
    });
    let body = trs::match_(env.var("t"), cases);
    trs::persistent_contract(chan, 3, body).par
}

/// Track B — R3, the SELF-DRIVING naive call (EXPLORATORY; PRE-REGISTERED
/// deviation from the shared firing contract, USER-approved 2026-07-19;
/// PatternGuard only): ONE session that installs, at `root_site`,
///
/// 1. every entry's R3 receiver ([`selfdriving_entry_receiver_par`]) — the
///    Appendix-A persistent per-site receiver whose accept's OUT slot is the
///    `^respread-root` dispatcher instead of the observation channel;
/// 2. the `^respread-root` dispatcher + `^respread` walker family
///    ([`respread_root_receiver_par`] / [`respread_walker_receiver_par`]),
///    whose admitted constructor set is the SUBJECT's own constructor → arity
///    map ([`collect_selfdriving_arity_map`], fail-closed);
/// 3. ONE [`spread_term_par`] of the whole subject.
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
/// re-spreads a redex-rooted reduct at `root_site` (walker COMMs —
/// `respread_tau`, one per node) — re-arming the SAME persistent receiver —
/// or lands a normal-form reduct ONCE on `out_channel`. NOTE the reduct is
/// COMPUTED by the installed firing contract, never assumed: R3 does not
/// special-case the identity-λ chain (re-spreading the captured argument
/// directly would); the walker re-spreads whatever the cascade delivered.
///
/// # Determinism (per-channel single-liveness)
///
/// Rounds are causally ordered (walk k's sends exist only after firing k's
/// captures were consumed), and per round each channel the matcher reads
/// carries exactly ONE live message: the round's own re-spread value. Stale
/// deep messages accumulate on channels no receiver demands (exactly as the
/// per-step architecture's unconsumed spread rests, but in ONE runtime) — they
/// are dead by construction, so scheduling nondeterminism never becomes value
/// nondeterminism.
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
    let view = ruleset.automaton.view();
    validate_naive_ruleset(&view)?;
    let mut arity_map: BTreeMap<String, usize> = BTreeMap::new();
    collect_selfdriving_arity_map(subject, &mut arity_map)?;

    // The dispatcher's redex set: the ruleset's entry ROOT ops (a reduct with
    // such a head can fire again at the root). NF labels: every OTHER subject
    // constructor. A redex-rooted reduct whose deeper nodes leave the admitted
    // map fails closed in the walker (wildcard → ^respread-err), and a reduct
    // whose ROOT leaves both sets fails closed in the dispatcher.
    let mut redex_root_ops: BTreeSet<String> = BTreeSet::new();
    for entry in 0..view.entry_count() {
        match view.node(view.entry_root_state(entry)) {
            AutomatonNode::App { op, .. } => {
                redex_root_ops.insert(op.to_string());
            },
            // Unreachable past `validate_naive_ruleset`, kept total + typed.
            AutomatonNode::Var(_) => return Err(NaiveKtUnsupported::VariableRootPattern),
        }
    }
    let nf_labels: BTreeSet<String> = arity_map
        .keys()
        .filter(|label| !redex_root_ops.contains(*label))
        .cloned()
        .collect();

    let mut call = Par::default();
    let mut installed = 0usize;
    for entry in 0..view.entry_count() {
        let accept_channel = entry_accept_channel(ruleset, view.entry_id(entry));
        let receiver = selfdriving_entry_receiver_par(
            &view,
            entry,
            root_site,
            accept_channel,
            &ruleset.language_fingerprint,
        )?;
        call = call.append(receiver);
        installed += 1;
    }
    call = call.append(respread_root_receiver_par(
        &ruleset.language_fingerprint,
        root_site,
        out_channel,
        &redex_root_ops,
        &nf_labels,
    ));
    call = call.append(respread_walker_receiver_par(&ruleset.language_fingerprint, &arity_map));

    let spread = spread_term_par(subject, &ruleset.language_fingerprint, root_site);
    Ok((call.append(spread), installed))
}

#[cfg(test)]
#[path = "../tests/support/rho_net_naive_kt_recursive_oracle.rs"]
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
        let network = naive_kt_entry_receiver_par(
            &automaton.view(),
            0,
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
            Some(spread_root_location(FP, "site0").as_str())
        );
        assert_eq!(
            root.binds[0].patterns[0],
            tag_par("Swap"),
            "the expected head tag IS the receive pattern"
        );

        // Captures: for(v1 <- cap:site0/Swap.0){ for(v2 <- cap:site0/Swap.1){ accept } }.
        let cap_x = &root.body.as_ref().expect("root body").receives[0];
        assert!(!cap_x.persistent, "captures are one-shot");
        assert_eq!(
            gstring(cap_x.binds[0].source.as_ref().expect("source")),
            Some(
                spread_child_location(&collapse_capture_location(FP, "site0"), "Swap", 0).as_str()
            )
        );
        let cap_y = &cap_x.body.as_ref().expect("x body").receives[0];
        assert_eq!(
            gstring(cap_y.binds[0].source.as_ref().expect("source")),
            Some(
                spread_child_location(&collapse_capture_location(FP, "site0"), "Swap", 1).as_str()
            )
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
            "site0",
            "sa:acc",
            "OUT",
            FP,
            NaiveGuardEncoding::PatternGuard,
        )
        .expect("the nested entry emits");
        assert_closed(&network, "the naive f(g(x)) receiver");

        // Level 1: persistent for(⌜f⌝ <= loc:site0).
        let root = &network.receives[0];
        assert!(root.persistent);
        assert_eq!(
            gstring(root.binds[0].source.as_ref().expect("source")),
            Some(spread_root_location(FP, "site0").as_str())
        );
        assert_eq!(root.binds[0].patterns[0], tag_par("f"));
        // Level 2: one-shot for(⌜g⌝ <- loc:site0/f.0).
        let descent = &root.body.as_ref().expect("root body").receives[0];
        assert!(!descent.persistent, "descent tag receives are one-shot");
        assert_eq!(
            gstring(descent.binds[0].source.as_ref().expect("source")),
            Some(spread_child_location(&spread_root_location(FP, "site0"), "f", 0).as_str())
        );
        assert_eq!(descent.binds[0].patterns[0], tag_par("g"));
        // Capture: for(v <- cap:site0/f.0/g.0){ accept } — the deep collapse value.
        let capture = &descent.body.as_ref().expect("descent body").receives[0];
        assert_eq!(
            gstring(capture.binds[0].source.as_ref().expect("source")),
            Some(
                spread_child_location(
                    &spread_child_location(&collapse_capture_location(FP, "site0"), "f", 0),
                    "g",
                    0
                )
                .as_str()
            )
        );
        let accept = &capture.body.as_ref().expect("capture body").sends[0];
        assert_eq!(gstring(accept.chan.as_ref().expect("chan")), Some("sa:acc"));
        assert_eq!(accept.data.len(), 2, "σ[x] + @out");
        assert_eq!(boundvar_index(&accept.data[0]), Some(0), "σ[x] = BoundVar(0)");
        assert_eq!(gstring(&accept.data[1]), Some("OUT"));
    }

    #[test]
    fn ternary_pattern_captures_in_dfs_order_with_the_general_frame() {
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
            spread_child_location(&collapse_capture_location(FP, "site0"), "Triple", 0),
            spread_child_location(&collapse_capture_location(FP, "site0"), "Triple", 1),
            spread_child_location(&collapse_capture_location(FP, "site0"), "Triple", 2),
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
        // f(g(x), y): x is captured DEEP (cap:site0/f.0/g.0), y at the direct
        // child (cap:site0/f.1); DFS order [x, y] ⇒ σ[x] = BoundVar(1),
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
            Some(
                spread_child_location(
                    &spread_child_location(&collapse_capture_location(FP, "site0"), "f", 0),
                    "g",
                    0
                )
                .as_str()
            )
        );
        let cap_y = &cap_x.body.as_ref().expect("x body").receives[0];
        assert_eq!(
            gstring(cap_y.binds[0].source.as_ref().expect("source")),
            Some(spread_child_location(&collapse_capture_location(FP, "site0"), "f", 1).as_str())
        );
        let send = &cap_y.body.as_ref().expect("y body").sends[0];
        assert_eq!(boundvar_index(&send.data[0]), Some(1), "σ[x] = BoundVar(1) (DFS-first)");
        assert_eq!(boundvar_index(&send.data[1]), Some(0), "σ[y] = BoundVar(0)");
    }

    #[test]
    fn consume_test_binds_the_tag_and_republishes_on_mismatch() {
        let automaton = swap_automaton();
        let network = naive_kt_entry_receiver_par(
            &automaton.view(),
            0,
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
            Some(spread_root_location(FP, "site0").as_str())
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
            spread_child_location(&spread_root_location(FP, "site0"), "Pair", 0),
            spread_child_location(
                &spread_child_location(&spread_root_location(FP, "site0"), "Pair", 1),
                "Pair",
                0,
            ),
            spread_child_location(
                &spread_child_location(&spread_root_location(FP, "site0"), "Pair", 1),
                "Pair",
                1,
            ),
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
                    == Some(spread_root_location(FP, "site0").as_str())
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
                        == Some(
                            spread_child_location(&spread_root_location(FP, "site0"), "Wrap", 0)
                                .as_str(),
                        )
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
    /// the walker (3 formals) are persistent contracts on their reserved
    /// `GPrivate` channels; exactly ONE spread is appended; the whole call is
    /// a closed contract.
    #[test]
    fn selfdriving_call_emits_dispatcher_walker_and_the_rerouted_accept() {
        let (ruleset, chain) = beta_ruleset_and_chain();
        let (call, installed) = naive_kt_selfdriving_call_par(&ruleset, &chain, "site0", "OUT")
            .expect("the β chain admits the R3 self-driving call");
        assert_eq!(installed, 1, "one entry ⇒ one installed R3 root receiver");
        assert_closed(&call, "the R3 self-driving call");

        // The matcher: persistent on loc:site0, tag-as-pattern ⌜App⌝.
        let loc_root = new_gstring_par(spread_root_location(FP, "site0"), Vec::new(), false);
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

        // The walker: persistent 3-formal contract on ⌜^respread⌝.
        let walker =
            persistent_receive_on(&call, &trs::tag_par(FP, RESPREAD_RESERVED_LABEL), "R3 walker");
        assert_eq!(walker.bind_count, 3, "walker binds (t, loc, cap)");

        // Exactly ONE spread: one head-tag send rests on loc:site0.
        let root_tag_sends = call
            .sends
            .iter()
            .filter(|send| {
                gstring(send.chan.as_ref().expect("chan"))
                    == Some(spread_root_location(FP, "site0").as_str())
            })
            .count();
        assert_eq!(root_tag_sends, 1, "exactly ONE spread is appended");
    }

    /// The dispatcher routes a REDEX-rooted reduct to the walker seeded with
    /// the root-site prefixes, an admitted NF-rooted reduct to OUT, and any
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

        // The App arm seeds the walker with (t, loc-root, cap-root) — both INV-S6 scoped.
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
        assert_eq!(seed.data.len(), 3, "^respread!(t, loc, cap)");
        assert_eq!(boundvar_index(&seed.data[0]), Some(0), "t is the bound reduct");
        assert_eq!(gstring(&seed.data[1]), Some(spread_root_location(FP, "site0").as_str()));
        assert_eq!(gstring(&seed.data[2]), Some(collapse_capture_location(FP, "site0").as_str()));

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

    /// The walker carries one exact-arity arm per subject constructor plus the
    /// fail-closed wildcard, and each arm re-emits the head tag on @loc, the
    /// whole node on @cap, and one recursion per child whose channel names are
    /// computed with the `spread_child_location` suffix.
    #[test]
    fn selfdriving_walker_arms_cover_the_subject_map_and_fail_closed() {
        let (ruleset, chain) = beta_ruleset_and_chain();
        let (call, _) = naive_kt_selfdriving_call_par(&ruleset, &chain, "site0", "OUT")
            .expect("the β chain admits");
        let walker =
            persistent_receive_on(&call, &trs::tag_par(FP, RESPREAD_RESERVED_LABEL), "R3 walker");
        let dispatch = &walker.body.as_ref().expect("walker body").matches[0];
        // Subject map {App:2, ^lambda:1, ^bound:1, Z:0, A:0} + wildcard = 6.
        assert_eq!(dispatch.cases.len(), 6, "5 constructor arms + the wildcard");

        // The App arm: free_count 2, body = @loc!(⌜App⌝) | @cap!(t) | 2 recursions.
        let app_arm = dispatch
            .cases
            .iter()
            .find(|case| {
                case.free_count == 2
                    && format!("{:?}", case.pattern)
                        .contains(&format!("{:?}", tag_par("App").unforgeables[0]))
            })
            .expect("the binary App arm exists");
        let body = app_arm.source.as_ref().expect("App arm body");
        assert_eq!(body.sends.len(), 4, "tag + cap + one recursion per child");
        let recursions: Vec<_> = body
            .sends
            .iter()
            .filter(|send| send.chan.as_ref() == Some(&trs::tag_par(FP, RESPREAD_RESERVED_LABEL)))
            .collect();
        assert_eq!(recursions.len(), 2, "one ^respread recursion per App child");
        for recursion in &recursions {
            assert_eq!(recursion.data.len(), 3, "^respread!(child, loc', cap')");
            // The child channel names are ++-computed with the shared suffix.
            let rendered = format!("{:?}", recursion.data[1]);
            assert!(
                rendered.contains("EPlusPlusBody"),
                "the child loc name is a ++ concat, got {rendered}"
            );
        }

        // The wildcard arm fails closed to ^respread-err.
        let last = dispatch.cases.last().expect("wildcard arm");
        assert_eq!(last.pattern.as_ref(), Some(&new_wildcard_par(Vec::new(), true)));
        let err_send = &last.source.as_ref().expect("wildcard body").sends[0];
        assert_eq!(err_send.chan.as_ref(), Some(&trs::tag_par(FP, RESPREAD_ERR_RESERVED_LABEL)));
    }

    /// The walker's in-Rho child-suffix rule IS `spread_child_location`'s:
    /// `parent ++ "/{op}.{i}"` (pinned so the derivations can never drift).
    #[test]
    fn selfdriving_child_suffix_matches_spread_child_location() {
        for (op, index) in [("App", 0usize), ("App", 1), ("^lambda", 0), ("^bound", 0)] {
            assert_eq!(
                spread_child_location("", op, index),
                format!("/{op}.{index}"),
                "the walker's baked suffix must equal the shared derivation"
            );
        }
    }

    /// R3 admission fail-closed matrix: an arity-conflicted subject, a subject
    /// label colliding with a reserved `^respread` rendezvous label, and an AC
    /// collection subject each reject BEFORE any emission.
    #[test]
    fn selfdriving_rejects_conflicting_reserved_and_collection_subjects() {
        let (ruleset, _) = beta_ruleset_and_chain();
        // One label at two arities: f(A, f(B)) uses f at arity 2 and arity 1.
        let conflicted = GroundTerm::new(
            "f",
            vec![GroundTerm::nullary("A"), GroundTerm::new("f", vec![GroundTerm::nullary("B")])],
        );
        assert_eq!(
            naive_kt_selfdriving_call_par(&ruleset, &conflicted, "site0", "OUT"),
            Err(NaiveKtUnsupported::SelfDrivingArityConflict {
                op: "f".to_string(),
                arity_a: 2,
                arity_b: 1,
            })
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
            NaiveKtUnsupported::SelfDrivingArityConflict {
                op: "f".to_string(),
                arity_a: 2,
                arity_b: 1,
            },
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
            let automaton = SetAutomaton::compile_structural([(PatternId(0), pattern)])
                .expect("a linear structural pattern compiles");
            let view = automaton.view();
            // k = the number of Var leaves (DFS) — recount independently.
            let mut descents = Vec::new();
            let mut captures = Vec::new();
            let mut names = Vec::new();
            if let AutomatonNode::App { op, args } = view.node(view.entry_root_state(0)) {
                let root_loc = spread_root_location(FP, "site0");
                let cap_root = collapse_capture_location(FP, "site0");
                for (index, &arg) in args.iter().enumerate() {
                    collect_nested_schedule(
                        &view,
                        arg,
                        &spread_child_location(&root_loc, op, index),
                        &spread_child_location(&cap_root, op, index),
                        &mut descents,
                        &mut captures,
                        &mut names,
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
                &view, 0, "site0", "sa:acc", "OUT", FP, encoding,
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
