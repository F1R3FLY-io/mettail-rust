//! Stage 1 M1b: serialize a compiled positional set automaton into an in-Rho
//! `sa:`-receiver network that MATCHES the spread subject term (M0's
//! [`spread_term_par`](crate::spread_term_par)) directly on the Rholang
//! interpreter, and on an accepting match hands σ to the existing flat
//! σ-receiver via its accept channel — so the base rewrite fires unchanged.
//!
//! Each automaton state becomes one `for`-receive (the τ symbol inspection of
//! the two set-automaton papers): the head tag published by the spread at a
//! node's location channel is received and `Match`-dispatched on the state's
//! constructor. On reaching the accepting configuration the network sends
//! `accept_channel!(σ₀,…,σ_{k-1}, @out)` — byte-identical to the message the
//! host σ-injection builds — so the persistent `sigma_receiver_par` contract
//! fires and lands `⟦R⟧σ` (INV-3/4/10/13 by construction).
//!
//! M1 scope: ONE App-rooted, linear pattern whose argument states are Var leaves
//! matching NULLARY subterms (σ = `EList[received head tag]` = `⟦leaf⟧`). Every
//! other shape fails closed to a later slice ([`AutomatonUnsupported`]) rather
//! than emitting an incorrect receiver network. The De Bruijn / `locally_free`
//! frame is validated end-to-end by the runtime match test (the RSpace reducer
//! is the true `locally_free` oracle).

use dovetail::set_automaton::{AutomatonNode, PatternId, SetAutomatonView};
use models::create_bit_vector;
use models::rhoapi::expr::ExprInstance;
use models::rhoapi::{EAnd, EEq, Expr, MatchCase, Par, Receive, ReceiveBind};
use models::rust::rholang::implicits::GPrivateBuilder;
use models::rust::utils::{
    new_boundvar_par, new_elist_par, new_freevar_par, new_gstring_par, new_match_par,
    new_receive_par, new_send_par,
};

use crate::rho_net_lower::{reflect_tag, spread_child_location, spread_root_location};

/// The pattern shapes the M1 automaton serializer does not yet handle — each
/// fails closed to a later slice rather than emitting an incorrect network.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AutomatonUnsupported {
    /// Not exactly one compiled pattern entry at the SINGLE-pattern
    /// [`automaton_receiver_network_par`] entry point — use
    /// [`multi_pattern_receiver_network_par`] for ≥2 patterns.
    MultiPattern,
    /// A repeated LHS variable in a shape Stage 2's `eq:` join cannot yet host (reserved
    /// for the deep-position non-linear path; nullary-leaf repeats ARE handled — a guarded
    /// polyadic join with an `EEq`/`EAnd` consistency `condition`).
    NonLinearVariable,
    /// Two entries share a root op but induce different variable-repetition partitions —
    /// one guarded `eq:` join cannot host both (one would gate the shared consume the other
    /// must not); fail closed (a per-accept `If`-gate is the follow-up).
    NonLinearSharedOp,
    /// A Var whose matched subterm may be non-nullary — the general σ needs the
    /// in-Rho collapse (a later slice); M1 handles nullary Var leaves only.
    NonNullaryVarSubtree,
    /// A bare-variable root pattern — not an App-rooted rewrite the σ-receiver fires.
    VariableRootPattern,
    /// Two entries share a root op but differ in arity — one `Match` case cannot host
    /// both (and a typed algebra never produces it: op determines arity).
    ConflictingArityForOp,
    /// A compiled entry has no accept target (its `PatternId` is absent from the
    /// caller's `accept_targets`) — the accept could not be routed to a rule.
    MissingAcceptTarget,
}

/// The `locally_free` index set `indices` as a rhoapi bit vector (empty when none).
fn bits(indices: &[usize]) -> Vec<u8> {
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
/// slot per DISTINCT LHS variable (`k = first_occ.len()`), `σ_d = EList[BoundVar(arity-1-p)]`
/// where `p = first_occ[d]` is that variable's first occurrence position. The child bound
/// at position `p` is `BoundVar(arity-1-p)` (the reverse De Bruijn convention of the `arity`
/// child binders); a nullary Var subterm's spread is a single head-tag send, so
/// `EList[received tag] = ⟦leaf⟧`. This distinct-var arity is the TRIAD-coherence point: the
/// σ-receiver has `k` formals (`lower_lhs_vars` dedups repeats), so a non-linear accept must
/// send `k` slots, not `arity`. For a LINEAR entry `first_occ = [0,…,arity-1]`, reducing to
/// the M1/M2a positional send byte-identically. Built manually (NOT `term_contract_call`,
/// which hardcodes empty `locally_free`): the σ args reference BoundVars, so the send is free
/// in `{arity-1-p : p ∈ first_occ}`.
fn build_accept_send(
    accept_channel: &str,
    out_channel: &str,
    arity: usize,
    first_occ: &[usize],
) -> Par {
    let mut data: Vec<Par> = first_occ
        .iter()
        .map(|&p| {
            let idx = arity - 1 - p;
            let received = new_boundvar_par(idx as i32, bits(&[idx]), false);
            let free = bits(&[idx]);
            new_elist_par(vec![received], free.clone(), false, None, free, false)
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

/// Wrap the `arity` Var `for`s innermost-first around `accept`, tracking the free De
/// Bruijn set (accept is free in `{0..arity-1}`; each wrap shifts under a binder), down
/// to the closed (`locally_free = {}`) `Match` case body.
fn wrap_children(root_channel: &str, op: &str, arity: usize, accept: Par) -> Par {
    let mut body = accept;
    let mut body_free: Vec<usize> = (0..arity).collect();
    for i in (0..arity).rev() {
        let child_channel = spread_child_location(root_channel, op, i);
        let receiver = for_receive(&child_channel, body, &body_free);
        body_free = shift_under_binder(&body_free);
        body = receiver;
    }
    body
}

/// A ground `Par` carrying the single binary expression `instance`, free in `free`.
fn expr_par(instance: ExprInstance, free: &[usize]) -> Par {
    Par {
        exprs: vec![Expr { expr_instance: Some(instance) }],
        locally_free: bits(free),
        connective_used: false,
        ..Par::default()
    }
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
        guard = expr_par(ExprInstance::EAndBody(EAnd { p1: Some(guard), p2: Some(conjunct) }), &union);
        free = union;
    }
    guard
}

/// Wrap `accept` in the `eq:`-guarded polyadic JOIN for a NON-LINEAR op partition: one atomic
/// `for(h_0 <- loc:ρ/op.0 ; … ; h_{arity-1} <- loc:ρ/op.{arity-1}){ accept }` whose `condition`
/// is [`consistency_guard`]. Unlike the nested [`wrap_children`] chain, the join binds every
/// child in ONE receive so the depth-1-substituted guard can compare the repeated occurrences,
/// and on inequality the reducer's `check_commit` vetoes the WHOLE consume — consuming no child
/// (the reject-safe `merge_substs → None`, at the strongest granularity). Child `i` is
/// `BoundVar(arity-1-i)` (the join binds flattened in bind order), so the guard and `accept`
/// share the reverse De Bruijn frame; the receive binds all `arity` indices, closing the case
/// body (`locally_free = {}`).
fn join_children_receiver(
    root_channel: &str,
    op: &str,
    arity: usize,
    partition: &[usize],
    accept: Par,
) -> Par {
    let binds: Vec<ReceiveBind> = (0..arity)
        .map(|i| ReceiveBind {
            patterns: vec![new_freevar_par(0, Vec::new())],
            source: Some(new_gstring_par(spread_child_location(root_channel, op, i), Vec::new(), false)),
            remainder: None,
            free_count: 1,
        })
        .collect();
    let guard = consistency_guard(arity, partition);
    let receive = Receive {
        binds,
        body: Some(accept),
        persistent: false,
        peek: false,
        bind_count: arity as i32,
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

    // Group entries by root op (first-seen order), collecting each entry's positional
    // accept target; reject nested-App children, non-linear vars, and op/arity clashes.
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
    let mut groups: Vec<OpGroup> = Vec::new();
    for entry in 0..view.entry_count() {
        let root = view.entry_root_state(entry);
        let (op, args) = match view.node(root) {
            AutomatonNode::App { op, args } => (op.to_string(), args.to_vec()),
            AutomatonNode::Var(_) => return Err(AutomatonUnsupported::VariableRootPattern),
        };
        let arity = args.len();
        // Partition the positions by which distinct variable each binds (first-occurrence
        // order). A repeated variable (`k = first_occ.len() < arity`) is matched by the
        // `eq:` consistency join; every position must be a nullary Var leaf (M2a scope).
        let mut names: Vec<String> = Vec::new();
        let mut partition: Vec<usize> = Vec::with_capacity(arity);
        let mut first_occ: Vec<usize> = Vec::new();
        for (pos, &arg) in args.iter().enumerate() {
            match view.node(arg) {
                AutomatonNode::Var(name) => match names.iter().position(|v| v == name) {
                    Some(d) => partition.push(d),
                    None => {
                        partition.push(names.len());
                        first_occ.push(pos);
                        names.push(name.to_string());
                    },
                },
                AutomatonNode::App { .. } => {
                    return Err(AutomatonUnsupported::NonNullaryVarSubtree)
                },
            }
        }
        let pid = view.entry_id(entry);
        let target = accept_targets
            .iter()
            .find(|t| t.pattern == pid)
            .ok_or(AutomatonUnsupported::MissingAcceptTarget)?;
        let accept = (target.accept_channel.clone(), target.out_channel.clone());
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
            None => groups.push(OpGroup { op, arity, partition, first_occ, accepts: vec![accept] }),
        }
    }

    let root_channel = spread_root_location(root_location);

    // One `Match` case per distinct root op: the parallel distinct-var accept, wrapped in
    // the linear child chain OR (for a repeated-variable partition) the `eq:`-guarded join.
    let mut cases = Vec::with_capacity(groups.len());
    for group in &groups {
        let accept = parallel_accept(&group.accepts, group.arity, &group.first_occ);
        let body = if group.first_occ.len() == group.arity {
            wrap_children(&root_channel, &group.op, group.arity, accept)
        } else {
            join_children_receiver(&root_channel, &group.op, group.arity, &group.partition, accept)
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

    // The root head tag (BoundVar(0)) is Match-dispatched; the Match is free in {0}, the
    // case bodies are closed, and the root `for` closes the network to {}.
    let match_target = new_boundvar_par(0, bits(&[0]), false);
    let match_free = bits(&[0]);
    let match_par = new_match_par(
        match_target,
        cases,
        match_free.clone(),
        false,
        match_free,
        false,
    );
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
    multi_pattern_receiver_network_par(view, root_location, &[target], language_fingerprint)
}

#[cfg(test)]
mod tests {
    use super::*;
    use dovetail::rules::Pattern;
    use dovetail::set_automaton::{PatternId, SetAutomaton};
    use models::rhoapi::expr::ExprInstance;

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
        // Multi-pattern.
        let multi = SetAutomaton::compile_structural([
            (PatternId(0), Pattern::app("f".to_string(), vec![Pattern::var("x")])),
            (PatternId(1), Pattern::app("g".to_string(), vec![Pattern::var("y")])),
        ])
        .unwrap();
        assert_eq!(
            automaton_receiver_network_par(&multi.view(), "s", "acc", "OUT", "fp"),
            Err(AutomatonUnsupported::MultiPattern)
        );

        // Bare-variable root.
        let var_root =
            SetAutomaton::compile_structural([(PatternId(0), Pattern::var("x"))]).unwrap();
        assert_eq!(
            automaton_receiver_network_par(&var_root.view(), "s", "acc", "OUT", "fp"),
            Err(AutomatonUnsupported::VariableRootPattern)
        );

        // Nested App child (non-nullary Var subtree).
        let nested = SetAutomaton::compile_structural([(
            PatternId(0),
            Pattern::app(
                "f".to_string(),
                vec![Pattern::app("g".to_string(), vec![Pattern::var("x")])],
            ),
        )])
        .unwrap();
        assert_eq!(
            automaton_receiver_network_par(&nested.view(), "s", "acc", "OUT", "fp"),
            Err(AutomatonUnsupported::NonNullaryVarSubtree)
        );
    }

    /// An `EList[BoundVar(i)]` σ slot's inner index (mirrors `serializes_swap`'s local walk).
    fn elist_boundvar(p: &Par) -> Option<i32> {
        match p.exprs.first()?.expr_instance.as_ref()? {
            ExprInstance::EListBody(l) => boundvar_index(&l.ps[0]),
            _ => None,
        }
    }

    #[test]
    fn serializes_a_nonlinear_pattern_with_the_eq_guard() {
        // f(x, x): the two positions share variable x, so the case body is ONE guarded join
        // (not the nested chain), carrying an EEq(BoundVar(1), BoundVar(0)) consistency
        // condition, and the accept sends ONE distinct-var σ slot — matching the σ-receiver's
        // single formal (the triad-coherence point).
        let automaton = SetAutomaton::compile_structural([(
            PatternId(0),
            Pattern::app("f".to_string(), vec![Pattern::var("x"), Pattern::var("x")]),
        )])
        .expect("f(x, x) compiles");
        let network =
            automaton_receiver_network_par(&automaton.view(), "site0", "sa:acc", "OUT", "fp")
                .expect("f(x, x) serializes with the eq: guard");
        assert!(network.locally_free.is_empty(), "the network is still a closed contract");

        let root_recv = &network.receives[0];
        let m = &root_recv.body.as_ref().unwrap().matches[0];
        let case_body = m.cases[0].source.as_ref().unwrap();
        assert_eq!(case_body.receives.len(), 1, "the non-linear case body is one guarded join");
        let join = &case_body.receives[0];

        // Two binds, on the two child location channels — one atomic polyadic join.
        assert_eq!(join.bind_count, 2, "the join binds both children in one receive");
        assert_eq!(gstring(join.binds[0].source.as_ref().unwrap()), Some("loc:site0/f.0"));
        assert_eq!(gstring(join.binds[1].source.as_ref().unwrap()), Some("loc:site0/f.1"));

        // The consistency condition: EEq(BoundVar(1), BoundVar(0)) (occurrence 0 == occurrence 1).
        let guard = join.condition.as_ref().expect("the non-linear join carries a condition");
        match guard.exprs.first().unwrap().expr_instance.as_ref().unwrap() {
            ExprInstance::EEqBody(eq) => {
                assert_eq!(boundvar_index(eq.p1.as_ref().unwrap()), Some(1));
                assert_eq!(boundvar_index(eq.p2.as_ref().unwrap()), Some(0));
            },
            other => panic!("expected an EEq consistency guard, got {other:?}"),
        }

        // The accept sends ONE σ slot (x = EList[BoundVar(1)]) + @out — NOT two.
        let send = &join.body.as_ref().unwrap().sends[0];
        assert_eq!(gstring(send.chan.as_ref().unwrap()), Some("sa:acc"));
        assert_eq!(send.data.len(), 2, "one distinct-var σ slot + @out");
        assert_eq!(elist_boundvar(&send.data[0]), Some(1), "σ[x] = EList[BoundVar(1)] (first occurrence)");
        assert_eq!(gstring(&send.data[1]), Some("OUT"));
    }

    #[test]
    fn serializes_partial_nonlinear_f_x_x_y() {
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
        let network =
            automaton_receiver_network_par(&automaton.view(), "site0", "sa:acc", "OUT", "fp")
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
        assert_eq!(elist_boundvar(&send.data[0]), Some(2), "σ[x] = EList[BoundVar(2)]");
        assert_eq!(elist_boundvar(&send.data[1]), Some(0), "σ[y] = EList[BoundVar(0)]");
        assert_eq!(gstring(&send.data[2]), Some("OUT"));
    }

    #[test]
    fn rejects_mixed_linearity_shared_op() {
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
            multi_pattern_receiver_network_par(&automaton.view(), "site0", &targets, "fp"),
            Err(AutomatonUnsupported::NonLinearSharedOp)
        );
    }

    #[test]
    fn serializes_swap_to_the_worked_out_frame() {
        let automaton = swap_automaton();
        let network =
            automaton_receiver_network_par(&automaton.view(), "site0", "sa:acc", "OUT", "fp")
                .expect("Swap(x, y) serializes");

        // Root: exactly one receive on loc:site0, closed (locally_free empty).
        assert_eq!(network.receives.len(), 1);
        assert!(network.locally_free.is_empty(), "the network is a closed contract");
        let root_recv = &network.receives[0];
        assert_eq!(root_recv.bind_count, 1);
        assert_eq!(gstring(root_recv.binds[0].source.as_ref().unwrap()), Some("loc:site0"));

        // Root body: match BoundVar(0) { GPrivate(⌜Swap⌝) => <Var fors> }.
        let root_body = root_recv.body.as_ref().unwrap();
        assert_eq!(root_body.matches.len(), 1, "root body dispatches on the head tag");
        let m = &root_body.matches[0];
        assert_eq!(boundvar_index(m.target.as_ref().unwrap()), Some(0), "match target is BoundVar(0)");
        assert_eq!(m.cases.len(), 1);
        assert_eq!(m.cases[0].free_count, 0, "ground head-tag discriminator binds nothing");

        // Case body: for(h1 <- loc:site0/Swap.0){ for(h2 <- loc:site0/Swap.1){ accept } }.
        let r1 = m.cases[0].source.as_ref().unwrap();
        assert_eq!(gstring(r1.receives[0].binds[0].source.as_ref().unwrap()), Some("loc:site0/Swap.0"));
        let r1_body = r1.receives[0].body.as_ref().unwrap();
        assert_eq!(gstring(r1_body.receives[0].binds[0].source.as_ref().unwrap()), Some("loc:site0/Swap.1"));

        // Accept send: sa:acc!( EList[BoundVar(1)], EList[BoundVar(0)], @"OUT" ).
        let accept = r1_body.receives[0].body.as_ref().unwrap();
        assert_eq!(accept.sends.len(), 1, "the accept is a single send");
        let send = &accept.sends[0];
        assert_eq!(gstring(send.chan.as_ref().unwrap()), Some("sa:acc"), "accept fires the σ-receiver source");
        assert_eq!(send.data.len(), 3, "σ[x], σ[y], @out");
        // σ[x] = EList[BoundVar(1)] (h1); σ[y] = EList[BoundVar(0)] (h2).
        let elist_boundvar = |p: &Par| -> Option<i32> {
            match p.exprs.first()?.expr_instance.as_ref()? {
                ExprInstance::EListBody(l) => boundvar_index(&l.ps[0]),
                _ => None,
            }
        };
        assert_eq!(elist_boundvar(&send.data[0]), Some(1), "σ[x] = EList[BoundVar(1)]");
        assert_eq!(elist_boundvar(&send.data[1]), Some(0), "σ[y] = EList[BoundVar(0)]");
        assert_eq!(gstring(&send.data[2]), Some("OUT"), "out channel appended last");
    }

    #[test]
    fn serializes_a_ternary_pattern_with_the_arity_general_frame() {
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
        let network =
            automaton_receiver_network_par(&automaton.view(), "site0", "sa:acc", "OUT", "fp")
                .expect("the ternary automaton serializes");

        // Descend root for → Match → for x → for y → for z → accept.
        let r_x = network.receives[0].body.as_ref().unwrap().matches[0].cases[0]
            .source
            .as_ref()
            .unwrap();
        assert_eq!(gstring(r_x.receives[0].binds[0].source.as_ref().unwrap()), Some("loc:site0/Triple.0"));
        let r_y = r_x.receives[0].body.as_ref().unwrap();
        assert_eq!(gstring(r_y.receives[0].binds[0].source.as_ref().unwrap()), Some("loc:site0/Triple.1"));
        let r_z = r_y.receives[0].body.as_ref().unwrap();
        assert_eq!(gstring(r_z.receives[0].binds[0].source.as_ref().unwrap()), Some("loc:site0/Triple.2"));
        let accept = r_z.receives[0].body.as_ref().unwrap();

        let send = &accept.sends[0];
        assert_eq!(send.data.len(), 4, "σ_x, σ_y, σ_z, @out");
        let elist_boundvar = |p: &Par| -> Option<i32> {
            match p.exprs.first()?.expr_instance.as_ref()? {
                ExprInstance::EListBody(l) => boundvar_index(&l.ps[0]),
                _ => None,
            }
        };
        assert_eq!(elist_boundvar(&send.data[0]), Some(2), "σ[x] = EList[BoundVar(2)]");
        assert_eq!(elist_boundvar(&send.data[1]), Some(1), "σ[y] = EList[BoundVar(1)]");
        assert_eq!(elist_boundvar(&send.data[2]), Some(0), "σ[z] = EList[BoundVar(0)]");
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
            multi_pattern_receiver_network_par(&automaton.view(), "site0", &targets, "fp")
                .expect("two distinct-op patterns serialize");

        assert_eq!(network.receives.len(), 1, "one shared root receive");
        let root = &network.receives[0];
        assert_eq!(gstring(root.binds[0].source.as_ref().unwrap()), Some("loc:site0"));
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
            multi_pattern_receiver_network_par(&automaton.view(), "site0", &targets, "fp")
                .expect("two same-op rules serialize");

        let m = &network.receives[0].body.as_ref().unwrap().matches[0];
        assert_eq!(m.cases.len(), 1, "one Match case for the shared op");
        let accept = accept_of(m.cases[0].source.as_ref().unwrap(), 2);
        assert_eq!(accept.sends.len(), 2, "both rules announce in parallel (O3 fan-out)");
        let channels: Vec<Option<&str>> =
            accept.sends.iter().map(|s| gstring(s.chan.as_ref().unwrap())).collect();
        assert!(channels.contains(&Some("sa:one")) && channels.contains(&Some("sa:two")));
    }

    #[test]
    fn rejects_conflicting_arity_for_the_same_op() {
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
            multi_pattern_receiver_network_par(&automaton.view(), "site0", &targets, "fp"),
            Err(AutomatonUnsupported::ConflictingArityForOp)
        );
    }

    #[test]
    fn rejects_an_entry_without_an_accept_target() {
        let automaton = SetAutomaton::compile_structural([(
            PatternId(5),
            Pattern::app("Swap".to_string(), vec![Pattern::var("x"), Pattern::var("y")]),
        )])
        .expect("pattern compiles");
        let targets = [target(PatternId(0), "sa:swap")]; // wrong id — no target for PatternId(5)
        assert_eq!(
            multi_pattern_receiver_network_par(&automaton.view(), "site0", &targets, "fp"),
            Err(AutomatonUnsupported::MissingAcceptTarget)
        );
    }
}
