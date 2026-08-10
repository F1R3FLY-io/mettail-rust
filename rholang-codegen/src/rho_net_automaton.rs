//! Serialize a compiled positional set automaton into an in-Rho `sa:`-receiver
//! network that MATCHES the spread subject term (M0's
//! [`spread_term_par`](crate::spread_term_par)) directly on the Rholang
//! interpreter, and on an accepting match hands σ to the existing flat
//! σ-receiver via its accept channel — so the base rewrite fires unchanged.
//!
//! Each App state becomes one `for`-receive (the τ symbol inspection of the two
//! set-automaton papers): the head tag published by the spread on a node's `loc:`
//! location channel is received and `Match`-dispatched on the state's constructor
//! (the root, then every NESTED App by descent). Each Var-leaf state instead reads
//! the node's `cap:` COLLAPSE channel — the FULLY COLLAPSED `⟦subtree⟧` the spread's
//! bottom-up fold publishes — so σ is correct for a matched subject of ARBITRARY
//! depth (Stage 4 M-collapse), not just a nullary leaf. On reaching the accepting
//! configuration the network sends `accept_channel!(σ₀,…,σ_{k-1}, @out)` — byte-
//! identical to the message the host σ-injection builds — so the persistent
//! `sigma_receiver_par` contract fires and lands `⟦R⟧σ` (INV-3/4/10/13 by construction).
//!
//! Scope: App-rooted patterns at any depth via descend-then-collapse
//! ([`build_nested_case_body`]), including non-linear repeats through an atomic `eq:`
//! consistency join over the collapsed values. A bare-variable root or a same-op
//! arity/partition clash fails closed ([`AutomatonUnsupported`]) rather than emitting
//! an incorrect network.
//! The De Bruijn / `locally_free` frame is validated end-to-end by the runtime match
//! tests (the RSpace reducer is the true `locally_free` oracle).

use std::collections::BTreeSet;

use dovetail::set_automaton::{AutomatonNode, PatternId, SetAutomatonView, SlotId, StateId};
use models::create_bit_vector;
use models::rhoapi::expr::ExprInstance;
use models::rhoapi::{EAnd, EEq, Expr, MatchCase, Par, Receive, ReceiveBind};
use models::rust::rholang::implicits::GPrivateBuilder;
use models::rust::utils::{
    new_boundvar_par, new_freevar_par, new_gstring_par, new_match_par, new_receive_par,
    new_send_par,
};

use crate::rho_net_location::{MatcherPosition, SubjectLocationIndex, SubjectPosition};
use crate::rho_net_lower::{reflect_tag, GroundTerm};

/// Shapes that cannot share one sound M1 automaton network. Each fails closed
/// rather than emitting an incorrect network.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AutomatonUnsupported {
    /// Not exactly one compiled pattern entry at the SINGLE-pattern
    /// [`automaton_receiver_network_par`] entry point — use
    /// [`multi_pattern_receiver_network_par`] for ≥2 patterns.
    MultiPattern,
    /// Two entries share a root op but induce different variable-repetition partitions —
    /// one guarded `eq:` join cannot host both (one would gate the shared consume the other
    /// must not); fail closed (a per-accept `If`-gate is the follow-up).
    NonLinearSharedOp,
    /// A bare-variable root pattern — not an App-rooted rewrite the σ-receiver fires.
    VariableRootPattern,
    /// Two entries share a root op but differ in arity — one `Match` case cannot host
    /// both (and a typed algebra never produces it: op determines arity).
    ConflictingArityForOp,
    /// A compiled entry has no accept target (its `PatternId` is absent from the
    /// caller's `accept_targets`) — the accept could not be routed to a rule.
    MissingAcceptTarget,
    /// The Stage-4 locate-all multi-site install ([`in_rho_match_all_sites_call_par`]) was
    /// asked to co-install per-position networks for a ruleset with a NESTED-App entry. A
    /// nested entry DESCENDS `loc:` head tags into its arguments, and a co-installed root
    /// attempt at a descent position would then contend for that same `loc:` head-tag send
    /// (one linear message, two readers) — potentially DROPPING a match. Flat-only rulesets
    /// (every entry an App over Var leaves) read only their own root `loc:` + leaf `cap:`
    /// channels, which are disjoint across positions, so they co-install soundly; a
    /// nested-entry ruleset fails closed here to the σ-replay driver (still correct, just
    /// off the in-Rho locate-all path). See `in_rho_match_all_sites_call_par`.
    ///
    /// [`in_rho_match_all_sites_call_par`]: crate::in_rho_match_all_sites_call_par
    NestedEntryMultiSite,
    /// The Stage-4 S-contextual match ([`contextual_match_call_par`](crate::contextual_match_call_par))
    /// was asked to serialize a contextual JOIN whose subject does not match the outer context `K`'s
    /// hole structure: 0 or ≥2 contextual families, a premise-channel/hole-position count drift, or —
    /// the load-bearing check — the subject's LOCATED rule-root redexes are not EXACTLY the `n`
    /// expected hole positions (a normal form with 0 hole redexes, a deeper nested redex inside a
    /// hole, or an extra redex outside the holes). Each of the `n` reduced holes must come from
    /// EXACTLY one in-Rho nested firing at its hole position `ℓ_i` for the reused
    /// [`contextual_join_receiver_par`](crate::contextual_join_receiver_par) to reassemble ⟦K'⟧ from
    /// the `n` located firings; anything else fails closed here. Never a wrong reassembly.
    ContextualHoleMismatch,
}

/// The `locally_free` index set `indices` as a rhoapi bit vector (empty when none).
/// `pub(crate)`: shared with the Track-B naive baseline emitter (`rho_net_naive_kt`,
/// feature `bench-naive-baseline`) so both emitters compute the De Bruijn frame
/// identically.
pub(crate) fn bits(indices: &[usize]) -> Vec<u8> {
    if indices.is_empty() {
        Vec::new()
    } else {
        create_bit_vector(indices)
    }
}

/// Shift a `locally_free` set down through ONE binder: drop index 0 (now bound)
/// and decrement the rest — the De Bruijn frame under a new innermost binder.
fn shift_under_binder(free: &[usize]) -> Vec<usize> {
    free.iter().filter(|&&i| i != 0).map(|&i| i - 1).collect()
}

/// A single-bind receiver `for(h <- channel){ body }` whose `body` has free De
/// Bruijn set `body_free`; the receiver binds one name, so its own free set is
/// `shift_under_binder(body_free)`. Mirrors `sigma_receiver_par`'s ReceiveBind.
fn for_receive(channel: &str, body: Par, body_free: &[usize]) -> Par {
    let receiver_free = shift_under_binder(body_free);
    let free_bits = bits(&receiver_free);
    new_receive_par(
        vec![ReceiveBind {
            patterns: vec![new_freevar_par(0, Vec::new())],
            source: Some(new_gstring_par(channel.to_string(), Vec::new(), false)),
            remainder: None,
            free_count: 1,
        }],
        body,
        false,
        false,
        1,
        free_bits.clone(),
        false,
        free_bits,
        false,
    )
}

/// The accepting send for ONE entry: `accept_channel!(σ_0,…,σ_{k-1}, @out)` with ONE σ
/// slot per DISTINCT LHS variable (`k = first_occ.len()`), `σ_d = BoundVar(arity-1-p)` where
/// `p = first_occ[d]` is that variable's first occurrence position. The child bound at
/// position `p` is `BoundVar(arity-1-p)` (the reverse De Bruijn convention of the `arity`
/// child binders); that child binder is the node's `cap:` COLLAPSE channel, which carries the
/// FULLY COLLAPSED subterm `⟦subtree⟧` (M-collapse), so the σ slot IS `⟦subtree⟧` for a matched
/// subject of ARBITRARY depth — NOT `EList[head tag]`, which held only for a nullary leaf and
/// dropped every non-nullary subject's children. This distinct-var arity is the TRIAD-coherence
/// point: the σ-receiver has `k` formals (`lower_lhs_vars` dedups repeats), so a non-linear
/// accept must send `k` slots, not `arity`. For a LINEAR entry `first_occ = [0,…,arity-1]`,
/// reducing to the M1/M2a positional send. Built manually (NOT `term_contract_call`, which
/// hardcodes empty `locally_free`): the σ args reference BoundVars, so the send is free in
/// `{arity-1-p : p ∈ first_occ}`.
/// `pub(crate)`: the Track-B naive baseline emitter (`rho_net_naive_kt`, feature
/// `bench-naive-baseline`) calls THIS function for its innermost accept, so the
/// naive scheme's accept send is byte-identical to the optimized network's by
/// construction — the σ-receivers / firing contracts downstream are shared
/// unchanged between the two emitters.
pub(crate) fn build_accept_send(
    accept_channel: &str,
    out_channel: &str,
    arity: usize,
    first_occ: &[usize],
) -> Par {
    let mut data: Vec<Par> = first_occ
        .iter()
        .map(|&p| {
            let idx = arity - 1 - p;
            // The child binder is the `cap:` collapse channel value = `⟦subtree⟧`, so the σ
            // slot IS that value. No `EList[tag]` wrap (that reconstructed a NULLARY leaf and
            // silently dropped a non-nullary subject's children — the M-collapse soundness fix).
            new_boundvar_par(idx as i32, bits(&[idx]), false)
        })
        .collect();
    data.push(new_gstring_par(out_channel.to_string(), Vec::new(), false));
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

/// The accept for one op group: the parallel composition of every entry's accept send
/// (the O3 "share the match, announce to every rule" fan-out). For a single entry this is
/// exactly that entry's [`build_accept_send`]. Free in `{arity-1-p : p ∈ first_occ}` (the
/// shared distinct-var σ BoundVars, identical across entries of the same op partition).
fn parallel_accept(accepts: &[(String, String)], arity: usize, first_occ: &[usize]) -> Par {
    let mut accept = Par::default();
    for (accept_channel, out_channel) in accepts {
        accept = accept.append(build_accept_send(accept_channel, out_channel, arity, first_occ));
    }
    if !first_occ.is_empty() {
        let free_indices: Vec<usize> = first_occ.iter().map(|&p| arity - 1 - p).collect();
        accept.locally_free = bits(&free_indices);
    }
    accept
}

/// Wrap the `arity` Var `for`s innermost-first around `accept`, reading the node's `cap:`
/// COLLAPSE channels (`capture_root·(op,i)`), NOT the `loc:` head-tag channels — so each binds
/// the FULLY COLLAPSED subterm `⟦subtree⟧` (M-collapse), the positional σ for a subject of
/// arbitrary depth. The FLAT special case of [`wrap_capture_chain`] (the `k = arity` direct-child
/// captures at positions `0..arity`).
fn direct_child_channels(
    locations: &SubjectLocationIndex<'_>,
    root_position: SubjectPosition,
    family: &str,
    language_fingerprint: &str,
    root_site: &str,
    arity: usize,
) -> Vec<String> {
    (0..arity)
        .map(|index| {
            let position = locations
                .child(root_position, index)
                .map_or(MatcherPosition::Dead, MatcherPosition::Live);
            locations.channel(family, language_fingerprint, root_site, position)
        })
        .collect()
}

fn wrap_children(
    locations: &SubjectLocationIndex<'_>,
    root_position: SubjectPosition,
    language_fingerprint: &str,
    root_site: &str,
    arity: usize,
    accept: Par,
) -> Par {
    let channels = direct_child_channels(
        locations,
        root_position,
        "cap",
        language_fingerprint,
        root_site,
        arity,
    );
    wrap_capture_chain(&channels, accept)
}

/// Wrap the `k = capture_channels.len()` Var-leaf `for`s innermost-first around `accept`,
/// tracking the free De Bruijn set (accept is free in `{0..k-1}`; each wrap shifts under a
/// binder), down to the closed (`locally_free = {}`) case body. Each `for` reads one Var leaf's
/// `cap:` COLLAPSE channel (a nested pattern's leaves live at arbitrary DFS paths), binding
/// `⟦subtree⟧`. `capture_channels[i]` is bound as `BoundVar(k-1-i)`, so the DFS-first leaf gets
/// the highest De Bruijn index — matching [`build_accept_send`]'s `σ_d = BoundVar(k-1-p)`.
/// `pub(crate)`: the Track-B naive baseline emitter (`rho_net_naive_kt`, feature
/// `bench-naive-baseline`) wraps its Var-leaf captures through THIS function, so its
/// capture ABI (channel order + De Bruijn frame) is the automaton's by construction.
pub(crate) fn wrap_capture_chain(capture_channels: &[String], accept: Par) -> Par {
    let k = capture_channels.len();
    let mut body = accept;
    let mut body_free: Vec<usize> = (0..k).collect();
    for channel in capture_channels.iter().rev() {
        let receiver = for_receive(channel, body, &body_free);
        body_free = shift_under_binder(&body_free);
        body = receiver;
    }
    body
}

/// One nested App node the automaton must DESCEND into: its `loc:` head-tag channel and the
/// constructor `op` whose tag the deep `Match` dispatches on (the reified τ symbol inspection at
/// a deep position of the set-automaton papers).
/// `pub(crate)`: the Track-B naive baseline emitter (`rho_net_naive_kt`, feature
/// `bench-naive-baseline`) consumes the SAME descent schedule (as pre-order tag
/// receives instead of `Match` cases).
pub(crate) struct Descent {
    pub(crate) loc_channel: String,
    pub(crate) op: String,
}

/// Iterate over a nested pattern subtree rooted at `state` — whose head tag is published on `loc_channel`
/// and whose collapse value is published on `cap_channel` — collecting the DESCENTS (nested App
/// nodes, `loc:`, pre-order) and CAPTURES (Var leaves, `cap:`, DFS order) plus each leaf's
/// canonical root slot. A Var leaf contributes a capture; an App node contributes a descent and
/// schedules children left-to-right, so the capture order is the pattern's first-occurrence
/// slot order — the σ-receiver's formal order.
/// `pub(crate)`: the Track-B naive baseline emitter (`rho_net_naive_kt`, feature
/// `bench-naive-baseline`) collects its per-entry schedule through THIS function, so
/// its descent/capture order is the automaton's by construction.
pub(crate) fn collect_nested_schedule(
    view: &SetAutomatonView<'_, String>,
    state: StateId,
    root_slots: Vec<SlotId>,
    locations: &SubjectLocationIndex<'_>,
    root_site: &str,
    language_fingerprint: &str,
    position: MatcherPosition,
    descents: &mut Vec<Descent>,
    captures: &mut Vec<String>,
    capture_slots: &mut Vec<SlotId>,
) {
    debug_assert_eq!(root_slots.len(), view.state_slot_count(state));
    let mut work = vec![(state, root_slots, position)];
    while let Some((state, root_slots, position)) = work.pop() {
        match view.node(state) {
            AutomatonNode::Var => {
                captures.push(locations.channel("cap", language_fingerprint, root_site, position));
                capture_slots.push(root_slots[0]);
            },
            AutomatonNode::App { op, args } => {
                descents.push(Descent {
                    loc_channel: locations.channel(
                        "loc",
                        language_fingerprint,
                        root_site,
                        position,
                    ),
                    op: op.to_string(),
                });
                for (index, arg) in args.iter().enumerate().rev() {
                    let child_root_slots = arg
                        .parent_slots()
                        .map(|parent| root_slots[parent.index()])
                        .collect();
                    work.push((
                        arg.state(),
                        child_root_slots,
                        locations.matcher_child(position, index),
                    ));
                }
            },
        }
    }
}

/// A DESCENT receiver `for(h <- loc){ match h { op̲ => closed_body } }`: consume the nested App
/// node's head tag on its `loc:` channel and dispatch on `op_tag` (free_count 0 — the tag is a
/// ground discriminator), then run the closed inner body. `closed_body` MUST have
/// `locally_free = {}` (the capture chain closes its own σ binders), so the descent binds only
/// `h` and closes to `{}` — the nested analogue of the root Match, one level deep.
fn wrap_descent(loc_channel: &str, op_tag: Par, closed_body: Par) -> Par {
    let case = MatchCase {
        pattern: Some(op_tag),
        source: Some(closed_body),
        free_count: 0,
        guard: None,
    };
    let match_target = new_boundvar_par(0, bits(&[0]), false);
    let match_free = bits(&[0]);
    let match_par =
        new_match_par(match_target, vec![case], match_free.clone(), false, match_free, false);
    for_receive(loc_channel, match_par, &[0])
}

/// The `Match` case body for a NESTED entry (`descend-then-collapse`). Linear captures use the
/// sequential capture chain; repeated slots use one guarded polyadic join so equality is tested
/// atomically. The nested App descents wrap that closed capture body in DFS-REVERSE order (the
/// deepest App innermost, the root's direct App children outermost). The root op's own `Match` is
/// the shared per-op case, so the schedule is collected over the root's ARGS, never the root.
fn build_nested_case_body(
    capture_channels: &[String],
    capture_partition: &[usize],
    descents: &[Descent],
    accept: Par,
    language_fingerprint: &str,
) -> Par {
    let distinct = capture_partition
        .iter()
        .copied()
        .max()
        .map(|slot| slot + 1)
        .unwrap_or(0);
    let mut body = if distinct == capture_channels.len() {
        wrap_capture_chain(capture_channels, accept)
    } else {
        join_capture_receiver(capture_channels, capture_partition, accept)
    };
    for descent in descents.iter().rev() {
        let op_tag =
            GPrivateBuilder::new_par_from_string(reflect_tag(language_fingerprint, &descent.op));
        body = wrap_descent(&descent.loc_channel, op_tag, body);
    }
    body
}

/// A ground `Par` carrying the single binary expression `instance`, free in `free`.
fn expr_par(instance: ExprInstance, free: &[usize]) -> Par {
    let mut par = Par::default();
    par.exprs = vec![Expr { expr_instance: Some(instance) }];
    par.locally_free = bits(free);
    par.connective_used = false;
    par
}

/// The consistency `condition` for a NON-LINEAR op partition: the conjunction (`EAnd`) of
/// `EEq(BoundVar(arity-1-q0), BoundVar(arity-1-qj))` over every repeated variable's
/// occurrence positions `q0 < q1 < … < q_{m-1}` (m ≥ 2). This is Def 4.9's enable-gate: the
/// guarded `consume` commits iff every repeated occurrence bound the SAME value (name-equal
/// head tags), and is reject-safe otherwise. Precondition: the partition has ≥1 repeat, so at
/// least one conjunct is emitted.
fn consistency_guard(arity: usize, partition: &[usize]) -> Par {
    let distinct = partition.iter().copied().max().map(|d| d + 1).unwrap_or(0);
    let mut conjuncts: Vec<(Par, Vec<usize>)> = Vec::new();
    for d in 0..distinct {
        let occs: Vec<usize> = (0..arity).filter(|&q| partition[q] == d).collect();
        if occs.len() < 2 {
            continue;
        }
        let idx0 = arity - 1 - occs[0];
        for &qj in &occs[1..] {
            let idxj = arity - 1 - qj;
            let eq = expr_par(
                ExprInstance::EEqBody(EEq {
                    p1: Some(new_boundvar_par(idx0 as i32, bits(&[idx0]), false)),
                    p2: Some(new_boundvar_par(idxj as i32, bits(&[idxj]), false)),
                }),
                &[idx0.min(idxj), idx0.max(idxj)],
            );
            conjuncts.push((eq, vec![idx0, idxj]));
        }
    }
    let (mut guard, mut free) = conjuncts[0].clone();
    for (conjunct, conjunct_free) in conjuncts.into_iter().skip(1) {
        let mut union = free.clone();
        union.extend(conjunct_free);
        union.sort_unstable();
        union.dedup();
        guard =
            expr_par(ExprInstance::EAndBody(EAnd { p1: Some(guard), p2: Some(conjunct) }), &union);
        free = union;
    }
    guard
}

/// Wrap `accept` in the `eq:`-guarded polyadic JOIN for a NON-LINEAR op partition: one atomic
/// `for(v_0 <- cap⟨ρ,p_0⟩ ; … ; v_{arity-1} <- cap⟨ρ,p_{arity-1}⟩){ accept }`
/// whose `condition`
/// is [`consistency_guard`]. Each `v_i` is the node's `cap:` COLLAPSE value `⟦subtree_i⟧`
/// (M-collapse), so the guard compares FULLY COLLAPSED subterms — repeated occurrences match
/// iff their whole subtrees are equal, not merely their head tags. Unlike the nested
/// [`wrap_children`] chain, the join binds every child in ONE receive so the depth-1-substituted
/// guard can compare the repeated occurrences, and on inequality the reducer's `check_commit`
/// vetoes the WHOLE consume — consuming no child (the reject-safe `merge_substs → None`, at the
/// strongest granularity). Child `i` is `BoundVar(arity-1-i)` (the join binds flattened in bind
/// order), so the guard and `accept` share the reverse De Bruijn frame; the receive binds all
/// `arity` indices, closing the case body (`locally_free = {}`).
fn join_children_receiver(
    locations: &SubjectLocationIndex<'_>,
    root_position: SubjectPosition,
    language_fingerprint: &str,
    root_site: &str,
    arity: usize,
    partition: &[usize],
    accept: Par,
) -> Par {
    let channels = direct_child_channels(
        locations,
        root_position,
        "cap",
        language_fingerprint,
        root_site,
        arity,
    );
    join_capture_receiver(&channels, partition, accept)
}

fn join_capture_receiver(capture_channels: &[String], partition: &[usize], accept: Par) -> Par {
    debug_assert_eq!(capture_channels.len(), partition.len());
    let binds: Vec<ReceiveBind> = capture_channels
        .iter()
        .map(|channel| ReceiveBind {
            patterns: vec![new_freevar_par(0, Vec::new())],
            source: Some(new_gstring_par(channel.clone(), Vec::new(), false)),
            remainder: None,
            free_count: 1,
        })
        .collect();
    let guard = consistency_guard(capture_channels.len(), partition);
    let receive = Receive {
        binds,
        body: Some(accept),
        persistent: false,
        peek: false,
        bind_count: capture_channels.len() as i32,
        locally_free: Vec::new(),
        connective_used: false,
        condition: Some(guard),
    };
    Par::default().with_receives(vec![receive])
}

/// Where an accepting match for one compiled entry fires — the entry's OWN rewrite
/// rule's σ-receiver source. One per entry; the multi-pattern accept routes each match
/// to the correct rule by [`AutomatonAcceptTarget::pattern`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AutomatonAcceptTarget {
    /// The compiled entry this target routes (must equal some `view.entry_id(e)`).
    pub pattern: PatternId,
    /// The rule's σ-receiver SOURCE channel (`rho_net_injection_sites`'s site channel).
    pub accept_channel: String,
    /// The out channel appended last to the σ tuple (`@out`).
    pub out_channel: String,
}

/// Serialize a compiled positional set automaton with ≥1 App-rooted linear entries
/// into ONE in-Rho `sa:`-receiver network sharing a single root `loc:` receive: the
/// root head tag is received once and `Match`-dispatched (one case per distinct root
/// op — the reified `app_roots` router); entries sharing an op+arity share the child
/// `for`-receives and announce in parallel to each rule's accept channel (O3 fan-out).
///
/// `root_location` is the spread's site root ρ; each `accept_targets` entry's
/// `accept_channel` MUST be its rule's σ-receiver source, and all tags MUST share
/// `language_fingerprint`, or the accept sends and σ-receivers would not rendezvous.
pub fn multi_pattern_receiver_network_par(
    view: &SetAutomatonView<'_, String>,
    subject: &GroundTerm,
    root_location: &str,
    accept_targets: &[AutomatonAcceptTarget],
    language_fingerprint: &str,
) -> Result<Par, AutomatonUnsupported> {
    let locations = SubjectLocationIndex::new(subject);
    multi_pattern_receiver_network_indexed_par(
        view,
        &locations,
        SubjectPosition::ROOT,
        root_location,
        accept_targets,
        language_fingerprint,
    )
}

/// Serialize the same compiled pattern set at every concrete subject position
/// whose constructor is one of its entry-root operators.  The compact subject
/// index is constructed exactly once, and every returned network shares the
/// exact identities used by one [`spread_term_par`](crate::spread_term_par)
/// call over `subject` and `root_location`.  The count is the number of
/// candidate positions serialized.
///
/// This lower-level surface is for callers that have independently proved the
/// requested networks can be co-installed without competing for a linear
/// `loc:` publication.  General locate-all execution should use
/// [`in_rho_match_all_sites_call_par`](crate::in_rho_match_all_sites_call_par),
/// which enforces that admission condition.
pub fn multi_pattern_receiver_networks_at_rule_roots_par(
    view: &SetAutomatonView<'_, String>,
    subject: &GroundTerm,
    root_location: &str,
    accept_targets: &[AutomatonAcceptTarget],
    language_fingerprint: &str,
) -> Result<(Par, usize), AutomatonUnsupported> {
    let locations = SubjectLocationIndex::new(subject);
    let root_ops: BTreeSet<&str> = (0..view.entry_count())
        .filter_map(|entry| match view.node(view.entry_root_state(entry)) {
            AutomatonNode::App { op, .. } => Some(op.as_str()),
            AutomatonNode::Var => None,
        })
        .collect();
    let mut positions = Vec::new();
    locations.walk(SubjectPosition::ROOT, |position, term| {
        if root_ops.contains(term.constructor.as_str()) {
            positions.push(position);
        }
        true
    });

    let mut networks = Par::default();
    for &position in &positions {
        networks = networks.append(multi_pattern_receiver_network_indexed_par(
            view,
            &locations,
            position,
            root_location,
            accept_targets,
            language_fingerprint,
        )?);
    }
    Ok((networks, positions.len()))
}

pub(crate) fn multi_pattern_receiver_network_indexed_par(
    view: &SetAutomatonView<'_, String>,
    locations: &SubjectLocationIndex<'_>,
    root_position: SubjectPosition,
    root_location: &str,
    accept_targets: &[AutomatonAcceptTarget],
    language_fingerprint: &str,
) -> Result<Par, AutomatonUnsupported> {
    if view.entry_count() == 0 {
        return Err(AutomatonUnsupported::MissingAcceptTarget);
    }
    if !view.variable_root_entries().is_empty() {
        return Err(AutomatonUnsupported::VariableRootPattern);
    }

    let root_channel = locations.channel("loc", language_fingerprint, root_location, root_position);

    // Group entries by root op (first-seen order). Flat entries share by their
    // slot partition; nested entries share when their canonical root StateId is
    // equal, which is precisely equality modulo entry-local alpha names.
    struct OpGroup {
        op: String,
        arity: usize,
        /// `partition[pos]` = the distinct-variable index the child at `pos` binds.
        partition: Vec<usize>,
        /// `first_occ[d]` = the first position binding distinct variable `d` (so
        /// `k = first_occ.len()` = the σ-receiver's formal count).
        first_occ: Vec<usize>,
        accepts: Vec<(String, String)>,
    }
    struct NestedGroup {
        op: String,
        root: StateId,
        descents: Vec<Descent>,
        captures: Vec<String>,
        partition: Vec<usize>,
        first_occ: Vec<usize>,
        accepts: Vec<(String, String)>,
    }
    let mut groups: Vec<OpGroup> = Vec::new();
    let mut nested_groups: Vec<NestedGroup> = Vec::new();
    for entry in 0..view.entry_count() {
        let root = view.entry_root_state(entry);
        let (op, args) = match view.node(root) {
            AutomatonNode::App { op, args } => (op.to_string(), args.to_vec()),
            AutomatonNode::Var => return Err(AutomatonUnsupported::VariableRootPattern),
        };
        let arity = args.len();
        let pid = view.entry_id(entry);
        let target = accept_targets
            .iter()
            .find(|t| t.pattern == pid)
            .ok_or(AutomatonUnsupported::MissingAcceptTarget)?;
        let accept = (target.accept_channel.clone(), target.out_channel.clone());

        // NESTED: some direct child is an App — the automaton descends `loc:` head tags to the
        // nested App(s) and collapses `cap:` at the Var leaves (removing the M1 rejection).
        let is_nested = args
            .iter()
            .any(|arg| matches!(view.node(arg.state()), AutomatonNode::App { .. }));
        if is_nested {
            if groups.iter().any(|group| group.op == op) {
                return Err(AutomatonUnsupported::ConflictingArityForOp);
            }
            if let Some(group) = nested_groups.iter_mut().find(|group| group.op == op) {
                if group.root != root {
                    return Err(AutomatonUnsupported::NonLinearSharedOp);
                }
                group.accepts.push(accept);
                continue;
            }
            // DFS the root's ARGS (the root op is this case's Match) → descents + captures.
            let mut descents: Vec<Descent> = Vec::new();
            let mut captures: Vec<String> = Vec::new();
            let mut capture_slots: Vec<SlotId> = Vec::new();
            for (index, arg) in args.iter().enumerate() {
                let child_position = locations
                    .child(root_position, index)
                    .map_or(MatcherPosition::Dead, MatcherPosition::Live);
                collect_nested_schedule(
                    view,
                    arg.state(),
                    arg.parent_slots().collect(),
                    locations,
                    root_location,
                    language_fingerprint,
                    child_position,
                    &mut descents,
                    &mut captures,
                    &mut capture_slots,
                );
            }
            let mut first_occ = vec![usize::MAX; view.state_slot_count(root)];
            let partition: Vec<usize> = capture_slots
                .iter()
                .enumerate()
                .map(|(position, slot)| {
                    let slot = slot.index();
                    if first_occ[slot] == usize::MAX {
                        first_occ[slot] = position;
                    }
                    slot
                })
                .collect();
            debug_assert!(first_occ.iter().all(|&position| position != usize::MAX));
            nested_groups.push(NestedGroup {
                op,
                root,
                descents,
                captures,
                partition,
                first_occ,
                accepts: vec![accept],
            });
            continue;
        }

        if nested_groups.iter().any(|group| group.op == op) {
            return Err(AutomatonUnsupported::ConflictingArityForOp);
        }

        // FLAT: partition the direct-child positions by which distinct variable each binds
        // (first-occurrence order). A repeated variable (`k = first_occ.len() < arity`) is matched
        // by the `eq:` consistency join.
        let mut partition: Vec<usize> = Vec::with_capacity(arity);
        let mut first_occ = vec![usize::MAX; view.state_slot_count(root)];
        for (pos, arg) in args.iter().enumerate() {
            match view.node(arg.state()) {
                AutomatonNode::Var => {
                    let slot = arg.parent_slot(SlotId::from_index(0)).index();
                    partition.push(slot);
                    if first_occ[slot] == usize::MAX {
                        first_occ[slot] = pos;
                    }
                },
                // An App child means the entry is nested — routed to the descend path above.
                AutomatonNode::App { .. } => {
                    unreachable!("a nested entry (App child) takes the descend path")
                },
            }
        }
        debug_assert!(first_occ.iter().all(|&position| position != usize::MAX));
        match groups.iter_mut().find(|g| g.op == op) {
            Some(group) => {
                if group.arity != arity {
                    return Err(AutomatonUnsupported::ConflictingArityForOp);
                }
                // Entries sharing a root op must induce the SAME repetition partition to
                // share one guarded join and fan out accepts (the O3 constraint made precise).
                if group.partition != partition {
                    return Err(AutomatonUnsupported::NonLinearSharedOp);
                }
                group.accepts.push(accept);
            },
            None => {
                groups.push(OpGroup {
                    op,
                    arity,
                    partition,
                    first_occ,
                    accepts: vec![accept],
                });
            },
        }
    }

    // One `Match` case per distinct root op: the flat partition cases (linear child chain OR the
    // `eq:`-guarded join) plus the nested descend-then-collapse cases.
    let mut cases = Vec::with_capacity(groups.len() + nested_groups.len());
    for group in &groups {
        let accept = parallel_accept(&group.accepts, group.arity, &group.first_occ);
        let body = if group.first_occ.len() == group.arity {
            wrap_children(
                locations,
                root_position,
                language_fingerprint,
                root_location,
                group.arity,
                accept,
            )
        } else {
            join_children_receiver(
                locations,
                root_position,
                language_fingerprint,
                root_location,
                group.arity,
                &group.partition,
                accept,
            )
        };
        let head_tag =
            GPrivateBuilder::new_par_from_string(reflect_tag(language_fingerprint, &group.op));
        cases.push(MatchCase {
            pattern: Some(head_tag),
            source: Some(body),
            free_count: 0,
            guard: None,
        });
    }
    for group in nested_groups {
        let accept = parallel_accept(&group.accepts, group.captures.len(), &group.first_occ);
        let body = build_nested_case_body(
            &group.captures,
            &group.partition,
            &group.descents,
            accept,
            language_fingerprint,
        );
        let head_tag =
            GPrivateBuilder::new_par_from_string(reflect_tag(language_fingerprint, &group.op));
        cases.push(MatchCase {
            pattern: Some(head_tag),
            source: Some(body),
            free_count: 0,
            guard: None,
        });
    }

    // The root head tag (BoundVar(0)) is Match-dispatched; the Match is free in {0}, the
    // case bodies are closed, and the root `for` closes the network to {}.
    let match_target = new_boundvar_par(0, bits(&[0]), false);
    let match_free = bits(&[0]);
    let match_par =
        new_match_par(match_target, cases, match_free.clone(), false, match_free, false);
    Ok(for_receive(&root_channel, match_par, &[0]))
}

/// Serialize a SINGLE App-rooted, linear set automaton — the M1 special case, which
/// delegates to [`multi_pattern_receiver_network_par`] with one accept target (a single
/// entry produces one `Match` case with one accept send = the M1 frame, byte-identical).
///
/// `root_location` is the spread's site root ρ (the same string
/// [`spread_term_par`](crate::spread_term_par) was called with); `accept_channel` MUST
/// be the rule's σ-receiver SOURCE channel (`rho_net_injection_sites`'s site channel),
/// or the accept send and the σ-receiver would not rendezvous.
pub fn automaton_receiver_network_par(
    view: &SetAutomatonView<'_, String>,
    subject: &GroundTerm,
    root_location: &str,
    accept_channel: &str,
    out_channel: &str,
    language_fingerprint: &str,
) -> Result<Par, AutomatonUnsupported> {
    if view.entry_count() != 1 {
        return Err(AutomatonUnsupported::MultiPattern);
    }
    let target = AutomatonAcceptTarget {
        pattern: view.entry_id(0),
        accept_channel: accept_channel.to_string(),
        out_channel: out_channel.to_string(),
    };
    multi_pattern_receiver_network_par(
        view,
        subject,
        root_location,
        &[target],
        language_fingerprint,
    )
}

#[cfg(test)]
#[path = "../tests/support/rho_net_automaton_schedule_recursive_oracle.rs"]
mod schedule_recursive_oracle;

#[cfg(test)]
mod tests {
    use super::*;
    use dovetail::rules::Pattern;
    use dovetail::set_automaton::{PatternId, SetAutomaton};
    use models::rhoapi::expr::ExprInstance;

    /// The INV-S6 scope these automaton wiring tests derive their channel names under.
    /// Expectations use the production subject-position index shared by spread and
    /// matcher construction.  That is the agreement invariant: both sides rendezvous
    /// on the same exact, fixed-width positional identity without retaining full paths.
    const FP: &str = "mettail-langdef-v1:0000000000000000";

    fn positional_subject() -> GroundTerm {
        let branch = |name| {
            GroundTerm::new(
                name,
                vec![GroundTerm::nullary("a"), GroundTerm::nullary("b"), GroundTerm::nullary("c")],
            )
        };
        GroundTerm::new("root", vec![branch("left"), branch("middle"), branch("right")])
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

    fn swap_automaton() -> SetAutomaton<String> {
        SetAutomaton::compile_structural([(
            PatternId(0),
            Pattern::app("Swap".to_string(), vec![Pattern::var("x"), Pattern::var("y")]),
        )])
        .expect("Swap(x, y) compiles")
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

    #[test]
    fn rejects_out_of_scope_patterns() {
        let subject = positional_subject();
        // Multi-pattern.
        let multi = SetAutomaton::compile_structural([
            (PatternId(0), Pattern::app("f".to_string(), vec![Pattern::var("x")])),
            (PatternId(1), Pattern::app("g".to_string(), vec![Pattern::var("y")])),
        ])
        .unwrap();
        assert_eq!(
            automaton_receiver_network_par(&multi.view(), &subject, "s", "acc", "OUT", FP),
            Err(AutomatonUnsupported::MultiPattern)
        );

        // Bare-variable root.
        let var_root =
            SetAutomaton::compile_structural([(PatternId(0), Pattern::var("x"))]).unwrap();
        assert_eq!(
            automaton_receiver_network_par(&var_root.view(), &subject, "s", "acc", "OUT", FP),
            Err(AutomatonUnsupported::VariableRootPattern)
        );
    }

    #[test]
    fn serializes_a_nested_app_pattern_by_descending_then_collapsing() {
        // f(g(x)): the M-collapse nested path. The root Match dispatches f at indexed position
        // p(root), DESCENDS to p([0]) (matching g), then CAPTURES x at p([0,0]). The assertions
        // below pin the exact compact `loc:`/`cap:` channel ABI for those positions.
        let nested = SetAutomaton::compile_structural([(
            PatternId(0),
            Pattern::app(
                "f".to_string(),
                vec![Pattern::app("g".to_string(), vec![Pattern::var("x")])],
            ),
        )])
        .unwrap();
        let subject = positional_subject();
        let network =
            automaton_receiver_network_par(&nested.view(), &subject, "site0", "sa:acc", "OUT", FP)
                .expect("a nested-App pattern now descends-then-collapses");
        assert!(network.locally_free.is_empty(), "the nested network is a closed contract");

        // Root: for(h <- loc⟨site0,p(root)⟩){ match h { f => <descent> } }.
        let root = &network.receives[0];
        assert_eq!(
            gstring(root.binds[0].source.as_ref().unwrap()),
            Some(indexed_channel(&subject, "loc", &[]).as_str())
        );
        let f_case = &root.body.as_ref().unwrap().matches[0].cases[0];
        // Descent: for(h1 <- loc⟨site0,p([0])⟩){ match h1 { g => <capture> } }.
        let descent = &f_case.source.as_ref().unwrap().receives[0];
        assert_eq!(
            gstring(descent.binds[0].source.as_ref().unwrap()),
            Some(indexed_channel(&subject, "loc", &[0]).as_str())
        );
        let g_case = &descent.body.as_ref().unwrap().matches[0].cases[0];
        // Capture: for(v <- cap⟨site0,p([0,0])⟩){ accept }.
        let capture = &g_case.source.as_ref().unwrap().receives[0];
        assert_eq!(
            gstring(capture.binds[0].source.as_ref().unwrap()),
            Some(indexed_channel(&subject, "cap", &[0, 0]).as_str()),
            "the Var leaf captures the COLLAPSED subterm at its deep cap: channel"
        );
        // Accept: sa:acc!( BoundVar(0), @"OUT" ) — the single σ slot at p([0,0]).
        let accept = &capture.body.as_ref().unwrap().sends[0];
        assert_eq!(gstring(accept.chan.as_ref().unwrap()), Some("sa:acc"));
        assert_eq!(accept.data.len(), 2, "σ[x] + @out");
        assert_eq!(boundvar_index(&accept.data[0]), Some(0), "σ[x] = BoundVar(0)");
        assert_eq!(gstring(&accept.data[1]), Some("OUT"));
    }

    #[test]
    fn serializes_a_nested_pattern_with_a_flat_sibling_leaf() {
        // f(g(x), y): x is captured at p([0,0]) and y at p([1]).
        // Both σ slots are bound INSIDE the g descent's closed frame, in DFS
        // (first-occurrence) order [x, y] → σ[x] = BoundVar(1), σ[y] = BoundVar(0).
        let nested = SetAutomaton::compile_structural([(
            PatternId(0),
            Pattern::app(
                "f".to_string(),
                vec![Pattern::app("g".to_string(), vec![Pattern::var("x")]), Pattern::var("y")],
            ),
        )])
        .unwrap();
        let subject = positional_subject();
        let network =
            automaton_receiver_network_par(&nested.view(), &subject, "site0", "sa:acc", "OUT", FP)
                .expect("a nested pattern with a flat sibling serializes");
        let f_case = &network.receives[0].body.as_ref().unwrap().matches[0].cases[0];
        let descent = &f_case.source.as_ref().unwrap().receives[0];
        let g_case = &descent.body.as_ref().unwrap().matches[0].cases[0];
        // Inside the g descent: for(vx <- cap⟨site0,p([0,0])⟩){
        // for(vy <- cap⟨site0,p([1])⟩){ accept } }.
        let cap_x = &g_case.source.as_ref().unwrap().receives[0];
        assert_eq!(
            gstring(cap_x.binds[0].source.as_ref().unwrap()),
            Some(indexed_channel(&subject, "cap", &[0, 0]).as_str())
        );
        let cap_y = &cap_x.body.as_ref().unwrap().receives[0];
        assert_eq!(
            gstring(cap_y.binds[0].source.as_ref().unwrap()),
            Some(indexed_channel(&subject, "cap", &[1]).as_str())
        );
        let accept = &cap_y.body.as_ref().unwrap().sends[0];
        assert_eq!(accept.data.len(), 3, "σ[x], σ[y], @out");
        assert_eq!(boundvar_index(&accept.data[0]), Some(1), "σ[x] = BoundVar(1) (DFS-first)");
        assert_eq!(boundvar_index(&accept.data[1]), Some(0), "σ[y] = BoundVar(0)");
        assert_eq!(gstring(&accept.data[2]), Some("OUT"));
    }

    #[test]
    fn serializes_nested_nonlinear_slots_with_one_atomic_capture_join() {
        let subject = positional_subject();
        let automaton = SetAutomaton::compile_structural([(
            PatternId(0),
            Pattern::app(
                "f".to_string(),
                vec![
                    Pattern::app("g".to_string(), vec![Pattern::var("x")]),
                    Pattern::app("h".to_string(), vec![Pattern::var("x")]),
                ],
            ),
        )])
        .expect("the nested nonlinear pattern compiles");
        let network = automaton_receiver_network_par(
            &automaton.view(),
            &subject,
            "site0",
            "sa:acc",
            "OUT",
            FP,
        )
        .expect("the repeated canonical slot uses a guarded deep capture join");

        let f_case = &network.receives[0].body.as_ref().unwrap().matches[0].cases[0];
        let g_recv = &f_case.source.as_ref().unwrap().receives[0];
        let g_case = &g_recv.body.as_ref().unwrap().matches[0].cases[0];
        let h_recv = &g_case.source.as_ref().unwrap().receives[0];
        let h_case = &h_recv.body.as_ref().unwrap().matches[0].cases[0];
        let join = &h_case.source.as_ref().unwrap().receives[0];

        assert_eq!(join.bind_count, 2);
        assert!(join.condition.is_some(), "the two occurrences of slot 0 are compared");
        assert_eq!(join.body.as_ref().unwrap().sends[0].data.len(), 2, "one σ slot plus out");
    }

    #[test]
    fn alpha_renamed_nested_entries_share_one_network_and_fan_out_accepts() {
        let subject = positional_subject();
        let shape = |name: &str| {
            Pattern::app(
                "f".to_string(),
                vec![Pattern::app("g".to_string(), vec![Pattern::var(name)])],
            )
        };
        let automaton = SetAutomaton::compile_structural([
            (PatternId(0), shape("x")),
            (PatternId(1), shape("renamed")),
        ])
        .expect("alpha-renamed nested entries compile");
        let view = automaton.view();
        assert_eq!(view.entry_root_state(0), view.entry_root_state(1));
        let targets = [
            AutomatonAcceptTarget {
                pattern: PatternId(0),
                accept_channel: "sa:left".to_string(),
                out_channel: "OUT".to_string(),
            },
            AutomatonAcceptTarget {
                pattern: PatternId(1),
                accept_channel: "sa:right".to_string(),
                out_channel: "OUT".to_string(),
            },
        ];
        let network = multi_pattern_receiver_network_par(&view, &subject, "site0", &targets, FP)
            .expect("one canonical nested state fans out to both rules");

        let root_match = &network.receives[0].body.as_ref().unwrap().matches[0];
        assert_eq!(root_match.cases.len(), 1, "one root case is shared");
        let descent = &root_match.cases[0].source.as_ref().unwrap().receives[0];
        let nested_case = &descent.body.as_ref().unwrap().matches[0].cases[0];
        let capture = &nested_case.source.as_ref().unwrap().receives[0];
        assert_eq!(capture.body.as_ref().unwrap().sends.len(), 2, "both accepts fan out");
    }

    #[test]
    fn serializes_a_nonlinear_pattern_with_the_eq_guard() {
        let subject = positional_subject();
        // f(x, x): the two positions share variable x, so the case body is ONE guarded join
        // (not the nested chain), carrying an EEq(BoundVar(1), BoundVar(0)) consistency
        // condition, and the accept sends ONE distinct-var σ slot — matching the σ-receiver's
        // single formal (the triad-coherence point).
        let automaton = SetAutomaton::compile_structural([(
            PatternId(0),
            Pattern::app("f".to_string(), vec![Pattern::var("x"), Pattern::var("x")]),
        )])
        .expect("f(x, x) compiles");
        let network = automaton_receiver_network_par(
            &automaton.view(),
            &subject,
            "site0",
            "sa:acc",
            "OUT",
            FP,
        )
        .expect("f(x, x) serializes with the eq: guard");
        assert!(network.locally_free.is_empty(), "the network is still a closed contract");

        let root_recv = &network.receives[0];
        let m = &root_recv.body.as_ref().unwrap().matches[0];
        let case_body = m.cases[0].source.as_ref().unwrap();
        assert_eq!(case_body.receives.len(), 1, "the non-linear case body is one guarded join");
        let join = &case_body.receives[0];

        // Two binds, on the two child CAPTURE (collapse) channels — one atomic polyadic join.
        assert_eq!(join.bind_count, 2, "the join binds both children in one receive");
        assert_eq!(
            gstring(join.binds[0].source.as_ref().unwrap()),
            Some(indexed_channel(&subject, "cap", &[0]).as_str())
        );
        assert_eq!(
            gstring(join.binds[1].source.as_ref().unwrap()),
            Some(indexed_channel(&subject, "cap", &[1]).as_str())
        );

        // The consistency condition: EEq(BoundVar(1), BoundVar(0)) (occurrence 0 == occurrence 1).
        let guard = join
            .condition
            .as_ref()
            .expect("the non-linear join carries a condition");
        match guard.exprs.first().unwrap().expr_instance.as_ref().unwrap() {
            ExprInstance::EEqBody(eq) => {
                assert_eq!(boundvar_index(eq.p1.as_ref().unwrap()), Some(1));
                assert_eq!(boundvar_index(eq.p2.as_ref().unwrap()), Some(0));
            },
            other => panic!("expected an EEq consistency guard, got {other:?}"),
        }

        // The accept sends ONE σ slot (x = BoundVar(1), the collapsed value) + @out — NOT two.
        let send = &join.body.as_ref().unwrap().sends[0];
        assert_eq!(gstring(send.chan.as_ref().unwrap()), Some("sa:acc"));
        assert_eq!(send.data.len(), 2, "one distinct-var σ slot + @out");
        assert_eq!(
            boundvar_index(&send.data[0]),
            Some(1),
            "σ[x] = BoundVar(1) = ⟦subterm⟧ (first occurrence's collapse value)"
        );
        assert_eq!(gstring(&send.data[1]), Some("OUT"));
    }

    #[test]
    fn serializes_partial_nonlinear_f_x_x_y() {
        let subject = positional_subject();
        // f(x, x, y): x repeats at positions 0,1 (distinct 0); y at position 2 (distinct 1).
        // Guard EEq(BoundVar(2), BoundVar(1)); accept σ = [ EList[BoundVar(2)] (x),
        // EList[BoundVar(0)] (y) ] — two distinct-var slots for a ternary pattern.
        let automaton = SetAutomaton::compile_structural([(
            PatternId(0),
            Pattern::app(
                "f".to_string(),
                vec![Pattern::var("x"), Pattern::var("x"), Pattern::var("y")],
            ),
        )])
        .expect("f(x, x, y) compiles");
        let network = automaton_receiver_network_par(
            &automaton.view(),
            &subject,
            "site0",
            "sa:acc",
            "OUT",
            FP,
        )
        .expect("f(x, x, y) serializes");
        let root_recv = &network.receives[0];
        let m = &root_recv.body.as_ref().unwrap().matches[0];
        let join = &m.cases[0].source.as_ref().unwrap().receives[0];
        assert_eq!(join.bind_count, 3, "all three children bound in one join");

        let guard = join.condition.as_ref().expect("condition");
        match guard.exprs.first().unwrap().expr_instance.as_ref().unwrap() {
            ExprInstance::EEqBody(eq) => {
                assert_eq!(boundvar_index(eq.p1.as_ref().unwrap()), Some(2));
                assert_eq!(boundvar_index(eq.p2.as_ref().unwrap()), Some(1));
            },
            other => panic!("expected EEq, got {other:?}"),
        }
        let send = &join.body.as_ref().unwrap().sends[0];
        assert_eq!(send.data.len(), 3, "two distinct-var σ slots + @out");
        assert_eq!(boundvar_index(&send.data[0]), Some(2), "σ[x] = BoundVar(2) (collapse value)");
        assert_eq!(boundvar_index(&send.data[1]), Some(0), "σ[y] = BoundVar(0) (collapse value)");
        assert_eq!(gstring(&send.data[2]), Some("OUT"));
    }

    #[test]
    fn rejects_mixed_linearity_shared_op() {
        let subject = positional_subject();
        // f(x, y) is linear, f(x, x) is non-linear — a shared op with differing repetition
        // partitions cannot share one guarded join; fail closed.
        let automaton = SetAutomaton::compile_structural([
            (
                PatternId(0),
                Pattern::app("f".to_string(), vec![Pattern::var("x"), Pattern::var("y")]),
            ),
            (
                PatternId(1),
                Pattern::app("f".to_string(), vec![Pattern::var("x"), Pattern::var("x")]),
            ),
        ])
        .expect("both f entries compile");
        let targets = vec![
            AutomatonAcceptTarget {
                pattern: PatternId(0),
                accept_channel: "sa:one".to_string(),
                out_channel: "OUT".to_string(),
            },
            AutomatonAcceptTarget {
                pattern: PatternId(1),
                accept_channel: "sa:two".to_string(),
                out_channel: "OUT".to_string(),
            },
        ];
        assert_eq!(
            multi_pattern_receiver_network_par(&automaton.view(), &subject, "site0", &targets, FP,),
            Err(AutomatonUnsupported::NonLinearSharedOp)
        );
    }

    #[test]
    fn serializes_swap_to_the_worked_out_frame() {
        let subject = positional_subject();
        let automaton = swap_automaton();
        let network = automaton_receiver_network_par(
            &automaton.view(),
            &subject,
            "site0",
            "sa:acc",
            "OUT",
            FP,
        )
        .expect("Swap(x, y) serializes");

        // Root: exactly one receive on loc:site0, closed (locally_free empty).
        assert_eq!(network.receives.len(), 1);
        assert!(network.locally_free.is_empty(), "the network is a closed contract");
        let root_recv = &network.receives[0];
        assert_eq!(root_recv.bind_count, 1);
        assert_eq!(
            gstring(root_recv.binds[0].source.as_ref().unwrap()),
            Some(indexed_channel(&subject, "loc", &[]).as_str())
        );

        // Root body: match BoundVar(0) { GPrivate(⌜Swap⌝) => <Var fors> }.
        let root_body = root_recv.body.as_ref().unwrap();
        assert_eq!(root_body.matches.len(), 1, "root body dispatches on the head tag");
        let m = &root_body.matches[0];
        assert_eq!(
            boundvar_index(m.target.as_ref().unwrap()),
            Some(0),
            "match target is BoundVar(0)"
        );
        assert_eq!(m.cases.len(), 1);
        assert_eq!(m.cases[0].free_count, 0, "ground head-tag discriminator binds nothing");

        // Case body: for(v1 <- cap⟨site0,p1⟩){ for(v2 <- cap⟨site0,p2⟩){ accept } } — the
        // children read the `cap:` COLLAPSE channels (the fully collapsed subterms), NOT `loc:`.
        let r1 = m.cases[0].source.as_ref().unwrap();
        assert_eq!(
            gstring(r1.receives[0].binds[0].source.as_ref().unwrap()),
            Some(indexed_channel(&subject, "cap", &[0]).as_str())
        );
        let r1_body = r1.receives[0].body.as_ref().unwrap();
        assert_eq!(
            gstring(r1_body.receives[0].binds[0].source.as_ref().unwrap()),
            Some(indexed_channel(&subject, "cap", &[1]).as_str())
        );

        // Accept send: sa:acc!( BoundVar(1), BoundVar(0), @"OUT" ) — each σ slot is the bound
        // collapse value `⟦subterm⟧` DIRECTLY (no `EList[tag]` wrap).
        let accept = r1_body.receives[0].body.as_ref().unwrap();
        assert_eq!(accept.sends.len(), 1, "the accept is a single send");
        let send = &accept.sends[0];
        assert_eq!(
            gstring(send.chan.as_ref().unwrap()),
            Some("sa:acc"),
            "accept fires the σ-receiver source"
        );
        assert_eq!(send.data.len(), 3, "σ[x], σ[y], @out");
        // σ[x] = BoundVar(1) (v1); σ[y] = BoundVar(0) (v2) — the collapsed child values.
        assert_eq!(boundvar_index(&send.data[0]), Some(1), "σ[x] = BoundVar(1)");
        assert_eq!(boundvar_index(&send.data[1]), Some(0), "σ[y] = BoundVar(0)");
        assert_eq!(gstring(&send.data[2]), Some("OUT"), "out channel appended last");
    }

    #[test]
    fn serializes_a_ternary_pattern_with_the_arity_general_frame() {
        let subject = positional_subject();
        // Triple(x, y, z): three nested Var fors; the accept's σ slots follow the
        // general frame σ_i = EList[BoundVar(arity-1-i)] = EList[BoundVar(2-i)].
        let automaton = SetAutomaton::compile_structural([(
            PatternId(0),
            Pattern::app(
                "Triple".to_string(),
                vec![Pattern::var("x"), Pattern::var("y"), Pattern::var("z")],
            ),
        )])
        .expect("Triple(x, y, z) compiles");
        let network = automaton_receiver_network_par(
            &automaton.view(),
            &subject,
            "site0",
            "sa:acc",
            "OUT",
            FP,
        )
        .expect("the ternary automaton serializes");

        // Descend root for → Match → for x → for y → for z → accept.
        let r_x = network.receives[0].body.as_ref().unwrap().matches[0].cases[0]
            .source
            .as_ref()
            .unwrap();
        assert_eq!(
            gstring(r_x.receives[0].binds[0].source.as_ref().unwrap()),
            Some(indexed_channel(&subject, "cap", &[0]).as_str())
        );
        let r_y = r_x.receives[0].body.as_ref().unwrap();
        assert_eq!(
            gstring(r_y.receives[0].binds[0].source.as_ref().unwrap()),
            Some(indexed_channel(&subject, "cap", &[1]).as_str())
        );
        let r_z = r_y.receives[0].body.as_ref().unwrap();
        assert_eq!(
            gstring(r_z.receives[0].binds[0].source.as_ref().unwrap()),
            Some(indexed_channel(&subject, "cap", &[2]).as_str())
        );
        let accept = r_z.receives[0].body.as_ref().unwrap();

        let send = &accept.sends[0];
        assert_eq!(send.data.len(), 4, "σ_x, σ_y, σ_z, @out");
        // Each σ slot is the bound collapse value DIRECTLY (σ_i = BoundVar(arity-1-i)).
        assert_eq!(boundvar_index(&send.data[0]), Some(2), "σ[x] = BoundVar(2)");
        assert_eq!(boundvar_index(&send.data[1]), Some(1), "σ[y] = BoundVar(1)");
        assert_eq!(boundvar_index(&send.data[2]), Some(0), "σ[z] = BoundVar(0)");
    }

    // Descend `arity` child for-receives of a Match case body to its accept Par.
    fn accept_of(case_body: &Par, arity: usize) -> &Par {
        let mut body = case_body;
        for _ in 0..arity {
            body = body.receives[0].body.as_ref().unwrap();
        }
        body
    }

    fn target(pattern: PatternId, accept_channel: &str) -> AutomatonAcceptTarget {
        AutomatonAcceptTarget {
            pattern,
            accept_channel: accept_channel.to_string(),
            out_channel: "OUT".to_string(),
        }
    }

    #[test]
    fn multi_pattern_dispatch_router_shares_one_root_receive() {
        let subject = positional_subject();
        // Two distinct-op patterns share ONE root loc: receive + a Match router with one
        // case per op; each op-case is its own children chain ending in its own accept.
        let automaton = SetAutomaton::compile_structural([
            (
                PatternId(0),
                Pattern::app("Swap".to_string(), vec![Pattern::var("x"), Pattern::var("y")]),
            ),
            (
                PatternId(1),
                Pattern::app("Pair".to_string(), vec![Pattern::var("a"), Pattern::var("b")]),
            ),
        ])
        .expect("two distinct-op patterns compile");
        let targets = [target(PatternId(0), "sa:swap"), target(PatternId(1), "sa:pair")];
        let network =
            multi_pattern_receiver_network_par(&automaton.view(), &subject, "site0", &targets, FP)
                .expect("two distinct-op patterns serialize");

        assert_eq!(network.receives.len(), 1, "one shared root receive");
        let root = &network.receives[0];
        assert_eq!(
            gstring(root.binds[0].source.as_ref().unwrap()),
            Some(indexed_channel(&subject, "loc", &[]).as_str())
        );
        let m = &root.body.as_ref().unwrap().matches[0];
        assert_eq!(m.cases.len(), 2, "one Match case per distinct root op");

        let channels: Vec<Option<&str>> = m
            .cases
            .iter()
            .map(|case| {
                let accept = accept_of(case.source.as_ref().unwrap(), 2);
                assert_eq!(accept.sends.len(), 1, "distinct-op: exactly one accept per case");
                gstring(accept.sends[0].chan.as_ref().unwrap())
            })
            .collect();
        assert!(channels.contains(&Some("sa:swap")), "Swap routes to sa:swap");
        assert!(channels.contains(&Some("sa:pair")), "Pair routes to sa:pair");
    }

    #[test]
    fn same_op_entries_share_the_subtree_and_fan_out_the_accept() {
        let subject = positional_subject();
        // Two rules with the SAME LHS op+arity share ONE children subtree; the accept is
        // the PARALLEL composition of both rules' sends (O3 announce-to-every-rule).
        let automaton = SetAutomaton::compile_structural([
            (
                PatternId(0),
                Pattern::app("Swap".to_string(), vec![Pattern::var("x"), Pattern::var("y")]),
            ),
            (
                PatternId(1),
                Pattern::app("Swap".to_string(), vec![Pattern::var("x"), Pattern::var("y")]),
            ),
        ])
        .expect("two same-op rules compile");
        let targets = [target(PatternId(0), "sa:one"), target(PatternId(1), "sa:two")];
        let network =
            multi_pattern_receiver_network_par(&automaton.view(), &subject, "site0", &targets, FP)
                .expect("two same-op rules serialize");

        let m = &network.receives[0].body.as_ref().unwrap().matches[0];
        assert_eq!(m.cases.len(), 1, "one Match case for the shared op");
        let accept = accept_of(m.cases[0].source.as_ref().unwrap(), 2);
        assert_eq!(accept.sends.len(), 2, "both rules announce in parallel (O3 fan-out)");
        let channels: Vec<Option<&str>> = accept
            .sends
            .iter()
            .map(|s| gstring(s.chan.as_ref().unwrap()))
            .collect();
        assert!(channels.contains(&Some("sa:one")) && channels.contains(&Some("sa:two")));
    }

    #[test]
    fn rejects_conflicting_arity_for_the_same_op() {
        let subject = positional_subject();
        let automaton = SetAutomaton::compile_structural([
            (PatternId(0), Pattern::app("f".to_string(), vec![Pattern::var("x")])),
            (
                PatternId(1),
                Pattern::app("f".to_string(), vec![Pattern::var("x"), Pattern::var("y")]),
            ),
        ])
        .expect("patterns compile");
        let targets = [target(PatternId(0), "a"), target(PatternId(1), "b")];
        assert_eq!(
            multi_pattern_receiver_network_par(&automaton.view(), &subject, "site0", &targets, FP,),
            Err(AutomatonUnsupported::ConflictingArityForOp)
        );
    }

    #[test]
    fn rejects_an_entry_without_an_accept_target() {
        let subject = positional_subject();
        let automaton = SetAutomaton::compile_structural([(
            PatternId(5),
            Pattern::app("Swap".to_string(), vec![Pattern::var("x"), Pattern::var("y")]),
        )])
        .expect("pattern compiles");
        let targets = [target(PatternId(0), "sa:swap")]; // wrong id — no target for PatternId(5)
        assert_eq!(
            multi_pattern_receiver_network_par(&automaton.view(), &subject, "site0", &targets, FP,),
            Err(AutomatonUnsupported::MissingAcceptTarget)
        );
    }
}
