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

use dovetail::set_automaton::{AutomatonNode, SetAutomatonView};
use models::create_bit_vector;
use models::rhoapi::{MatchCase, Par, ReceiveBind};
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
    /// More than one compiled pattern entry — multi-pattern dispatch is M2.
    MultiPattern,
    /// A repeated LHS variable — non-linear consistency is Stage 2 (`eq:` receivers).
    NonLinearVariable,
    /// A Var whose matched subterm may be non-nullary — the general σ needs the
    /// in-Rho collapse (a later slice); M1 handles nullary Var leaves only.
    NonNullaryVarSubtree,
    /// A bare-variable root pattern — not an App-rooted rewrite the σ-receiver fires.
    VariableRootPattern,
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

/// Serialize a single App-rooted, linear set automaton (through its
/// [`SetAutomatonView`]) into the in-Rho `sa:`-receiver network.
///
/// `root_location` is the spread's site root ρ (the same string
/// [`spread_term_par`](crate::spread_term_par) was called with); `accept_channel`
/// MUST be the rule's σ-receiver SOURCE channel (`rho_net_injection_sites`'s
/// site channel), or the accept send and the σ-receiver would not rendezvous.
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
    if !view.variable_root_entries().is_empty() {
        return Err(AutomatonUnsupported::VariableRootPattern);
    }
    let root = view.entry_root_state(0);
    let (op, args) = match view.node(root) {
        AutomatonNode::App { op, args } => (op.clone(), args.to_vec()),
        AutomatonNode::Var(_) => return Err(AutomatonUnsupported::VariableRootPattern),
    };

    // The Var leaves in first-occurrence order (= arg order for a linear pattern);
    // reject nested App children (need the collapse) and repeated vars (Stage 2).
    let arity = args.len();
    let mut seen: Vec<String> = Vec::with_capacity(arity);
    for &arg in &args {
        match view.node(arg) {
            AutomatonNode::Var(name) => {
                if seen.iter().any(|v| v == name) {
                    return Err(AutomatonUnsupported::NonLinearVariable);
                }
                seen.push(name.to_string());
            },
            AutomatonNode::App { .. } => return Err(AutomatonUnsupported::NonNullaryVarSubtree),
        }
    }

    let root_channel = spread_root_location(root_location);

    // Accept: σ arg for the i-th Var leaf is EList[BoundVar(arity-1-i)]. The i-th
    // Var's `for` is opened at ordinal 1+i of depth 1+arity, so at the innermost
    // accept it is BoundVar((1+arity)-1-(1+i)) = BoundVar(arity-1-i). A nullary Var
    // subterm's spread is a single head-tag send, so EList[received tag] = ⟦leaf⟧.
    // Built manually (NOT term_contract_call, which hardcodes empty locally_free
    // for ground σ args): the σ args reference BoundVars, so the send is free in
    // {0..arity-1}.
    let mut data: Vec<Par> = (0..arity)
        .map(|i| {
            let idx = arity - 1 - i;
            let received = new_boundvar_par(idx as i32, bits(&[idx]), false);
            let free = bits(&[idx]);
            new_elist_par(vec![received], free.clone(), false, None, free, false)
        })
        .collect();
    data.push(new_gstring_par(out_channel.to_string(), Vec::new(), false));
    let accept_free = bits(&(0..arity).collect::<Vec<_>>());
    let accept = new_send_par(
        new_gstring_par(accept_channel.to_string(), Vec::new(), false),
        data,
        false,
        accept_free.clone(),
        false,
        accept_free,
        false,
    );

    // Wrap the `arity` Var `for`s innermost-first around accept, tracking the free
    // De Bruijn set (accept is free in {0..arity-1}; each wrap shifts under a binder).
    let mut body = accept;
    let mut body_free: Vec<usize> = (0..arity).collect();
    for i in (0..arity).rev() {
        let child_channel = spread_child_location(&root_channel, &op, i);
        let receiver = for_receive(&child_channel, body, &body_free);
        body_free = shift_under_binder(&body_free);
        body = receiver;
    }
    // After `arity` wraps, `body_free == {}` — the Match case body is closed.

    // The root App dispatch: match the root's just-received head tag (BoundVar(0))
    // against `⌜op⌝`. free_count 0 (a ground discriminator binds nothing); the
    // Match is free in {0} (its target), the case body is closed.
    let head_tag = GPrivateBuilder::new_par_from_string(reflect_tag(language_fingerprint, &op));
    let match_target = new_boundvar_par(0, bits(&[0]), false);
    let match_free = bits(&[0]);
    let match_par = new_match_par(
        match_target,
        vec![MatchCase {
            pattern: Some(head_tag),
            source: Some(body),
            free_count: 0,
            guard: None,
        }],
        match_free.clone(),
        false,
        match_free,
        false,
    );

    // The root `for` binds the root head tag and closes the network to {}.
    Ok(for_receive(&root_channel, match_par, &[0]))
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

        // Non-linear variable.
        let nonlinear = SetAutomaton::compile_structural([(
            PatternId(0),
            Pattern::app("f".to_string(), vec![Pattern::var("x"), Pattern::var("x")]),
        )])
        .unwrap();
        assert_eq!(
            automaton_receiver_network_par(&nonlinear.view(), "s", "acc", "OUT", "fp"),
            Err(AutomatonUnsupported::NonLinearVariable)
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
}
