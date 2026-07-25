//! L9-5 gate — RhoCalc goes MODAL for FLT (foreign-language template) guest
//! bodies. Proves that the `FltOpen*` modal tokens + raw guest modes + `PFlt*`
//! productions added to `languages/src/rhocalc.rs` parse a delimited guest
//! region to a native `Proc::PFlt*(Arc<FltNode>)` — WITHOUT perturbing existing
//! RhoCalc parses (the full `languages` suite is the zero-regression gate; the
//! `existing_parse_unperturbed` case is a spot check of the default mode).
//!
//! Reduction of a `PFlt` is deferred to L9-6 (`lower_proc`'s `PFlt` arm →
//! `FltResolver`); here the node is inert captured data.

use mettail_languages::rhocalc::*;
use mettail_runtime::FltNode;

fn node_of(term: &Proc) -> &FltNode {
    match term {
        Proc::PFlt(n) | Proc::PFltFence(n) | Proc::PFltBrace(n) => n,
        _ => panic!("expected a PFlt* variant, got {term:?}"),
    }
}

#[test]
fn l9_5_rhocalc_backtick_flt_parses_to_pflt() {
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
fn l9_5_rhocalc_typed_hole_records_category() {
    mettail_runtime::clear_var_cache();
    let term = Proc::parse("lam`id(${f:Proc})`").expect("typed-hole parse");
    let n = node_of(&term);
    assert_eq!(n.holes.len(), 1);
    assert_eq!(n.holes[0].name, "f");
    assert_eq!(n.holes[0].category.as_deref(), Some("Proc"));
}

#[test]
fn l9_5_rhocalc_fence_and_brace_forms() {
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
fn l9_5_rhocalc_empty_body() {
    mettail_runtime::clear_var_cache();
    let term = Proc::parse("lam``").expect("empty-body FLT parse");
    let n = node_of(&term);
    assert_eq!(n.tag, "lam");
    assert_eq!(n.body_src, "");
    assert!(n.holes.is_empty());
}

#[test]
fn l9_5_rhocalc_default_mode_unperturbed() {
    // RhoCalc going modal must not perturb the default (host) mode: a
    // representative sample of existing surface still parses.
    mettail_runtime::clear_var_cache();
    let _ = Proc::parse("Nil").expect("Nil still parses");
    let _ = Proc::parse("@Nil!(0)").expect("send still parses");
    let _ = Proc::parse("{ Nil | Nil }").expect("par still parses");
    let _ = Proc::parse("new x in { Nil }").expect("new still parses");
}
