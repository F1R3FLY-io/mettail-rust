//! L9-5 gate — Rholang goes MODAL for FLT (foreign-language template) guest
//! bodies. Proves that the `FltOpen*` modal tokens + raw guest modes + `PFlt*`
//! productions added to `languages/src/rholang.rs` parse a delimited guest
//! region to a native `Proc::PFlt*(Arc<FltNode>)` — WITHOUT perturbing existing
//! Rholang parses (the full `languages` suite is the zero-regression gate; the
//! `existing_parse_unperturbed` case is a spot check of the default mode).
//!
//! Reduction of a `PFlt` is deferred to L9-6 (`lower_proc`'s `PFlt` arm →
//! `FltResolver`); here the node is inert captured data.

use mettail_languages::rholang::*;
use mettail_runtime::FltNode;

fn node_of(term: &Proc) -> &FltNode {
    match term {
        Proc::PFlt(n) | Proc::PFltFence(n) | Proc::PFltBrace(n) => n,
        _ => panic!("expected a PFlt* variant, got {term:?}"),
    }
}

#[test]
fn l9_5_rholang_backtick_flt_parses_to_pflt() {
    // The RUN-SHEET's canonical lambda-form guest body.
    mettail_runtime::clear_var_cache();
    let term = Proc::parse("lam`App(${f}, K)`").expect("backtick FLT parse");
    let n = node_of(&term);
    assert_eq!(n.tag, "lam");
    assert_eq!(n.body_src, "App(${f}, K)");
    assert_eq!(n.holes.len(), 1);
    assert_eq!(n.holes[0].name, "f");
    assert_eq!(n.holes[0].category, None);
    assert_eq!(n.position, 0);
}

#[test]
fn l9_5_rholang_typed_hole_records_category() {
    mettail_runtime::clear_var_cache();
    let term = Proc::parse("lam`id(${f:Proc})`").expect("typed-hole parse");
    let n = node_of(&term);
    assert_eq!(n.holes.len(), 1);
    assert_eq!(n.holes[0].name, "f");
    assert_eq!(n.holes[0].category.as_deref(), Some("Proc"));
}

#[test]
fn l9_5_repeated_holes_share_one_telescope_identity() {
    mettail_runtime::clear_var_cache();
    let term = Proc::parse("lam`pair(${x}, ${x})`").expect("repeated-hole FLT parse");
    let node = node_of(&term);
    assert_eq!(node.holes.len(), 1, "one declaration per hole name");
    let occurrences: Vec<_> = node
        .pieces
        .iter()
        .filter_map(|piece| match piece {
            mettail_runtime::FltTemplatePiece::Hole(id) => Some(*id),
            mettail_runtime::FltTemplatePiece::Text(_) => None,
        })
        .collect();
    assert_eq!(occurrences, vec![node.holes[0].id, node.holes[0].id]);
}

#[test]
fn l9_5_malformed_hole_is_rejected_before_guest_parsing() {
    mettail_runtime::clear_var_cache();
    assert!(
        Proc::parse("lam`pair(${x) , injected}, K)`").is_err(),
        "hole text cannot inject guest punctuation",
    );
    assert!(
        Proc::parse("lam`pair(${x:Term)Bad}, K)`").is_err(),
        "typed-hole categories are qualified identifiers",
    );
}

#[test]
fn l9_5_rholang_fence_and_brace_forms() {
    mettail_runtime::clear_var_cache();
    let fence = Proc::parse("lam```App(${f}, ${g})```").expect("fence FLT parse");
    let fn_node = node_of(&fence);
    assert_eq!(fn_node.tag, "lam");
    assert_eq!(fn_node.holes.len(), 2);

    let brace = Proc::parse("box{ App(${g}) }").expect("brace FLT parse");
    let bn = node_of(&brace);
    assert_eq!(bn.tag, "box");
    assert_eq!(bn.body_src, " App(${g}) ");
    assert_eq!(bn.holes.len(), 1);
    assert_eq!(bn.holes[0].name, "g");
}

#[test]
fn l9_5_rholang_empty_body() {
    mettail_runtime::clear_var_cache();
    let term = Proc::parse("lam``").expect("empty-body FLT parse");
    let n = node_of(&term);
    assert_eq!(n.tag, "lam");
    assert_eq!(n.body_src, "");
    assert!(n.holes.is_empty());
}

#[test]
fn l9_5_rholang_default_mode_unperturbed() {
    // Rholang going modal must not perturb the default (host) mode: a
    // representative sample of existing surface still parses.
    mettail_runtime::clear_var_cache();
    let _ = Proc::parse("Nil").expect("Nil still parses");
    let _ = Proc::parse("@Nil!(0)").expect("send still parses");
    let _ = Proc::parse("{ Nil | Nil }").expect("par still parses");
    let _ = Proc::parse("new x in { Nil }").expect("new still parses");
}

#[test]
fn flt_selector_is_the_same_lexical_variable_as_the_receive_binding() {
    mettail_runtime::clear_var_cache();
    let term = Proc::parse("for(lambda <- ret){lambda`x`}").expect("bound FLT selector parses");
    let Proc::PForUser(rows, body) = &term else {
        panic!("expected a receive");
    };
    let [ForRow::ForRowSingleNoWhere(bind)] = rows.as_slice() else {
        panic!("expected one unguarded receive row");
    };
    let InputBind::InputBind(lhs, _) = bind.as_ref() else {
        panic!("expected one ordinary input binding");
    };
    let Name::NVar(bound_name) = lhs.as_ref() else {
        panic!("expected a variable binding");
    };
    let Proc::PFlt(node) = body.as_ref() else {
        panic!("expected an FLT construction in the continuation");
    };

    assert_eq!(
        &node.selector, bound_name,
        "the FLT opener must denote the received capability, not an ambient tag",
    );
}
