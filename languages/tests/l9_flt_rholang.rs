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
    let term = Proc::parse("lam:Proc`App(${f}, K)`").expect("backtick FLT parse");
    let n = node_of(&term);
    assert_eq!(n.selector_name, "lam");
    assert_eq!(n.category, "Proc");
    assert_eq!(n.body_src, "App(${f}, K)");
    assert_eq!(n.holes.len(), 1);
    assert_eq!(n.holes[0].name, "f");
    assert_eq!(n.holes[0].category, None);
    assert_eq!(n.position, 0);
}

#[test]
fn l9_5_rholang_typed_hole_records_category() {
    mettail_runtime::clear_var_cache();
    let term = Proc::parse("lam:Proc`id(${f:Proc})`").expect("typed-hole parse");
    let n = node_of(&term);
    assert_eq!(n.holes.len(), 1);
    assert_eq!(n.holes[0].name, "f");
    assert_eq!(n.holes[0].category.as_deref(), Some("Proc"));
}

#[test]
fn l9_5_repeated_holes_share_one_telescope_identity() {
    mettail_runtime::clear_var_cache();
    let term = Proc::parse("lam:Proc`pair(${x}, ${x})`").expect("repeated-hole FLT parse");
    let node = node_of(&term);
    assert_eq!(node.holes.len(), 1, "one declaration per hole name");
    let occurrences: Vec<_> = node
        .pieces
        .iter()
        .filter_map(|piece| match piece {
            mettail_runtime::FltTemplatePiece::Hole { id, .. } => Some(*id),
            mettail_runtime::FltTemplatePiece::Text { .. } => None,
        })
        .collect();
    assert_eq!(occurrences, vec![node.holes[0].id, node.holes[0].id]);
    assert_eq!(node.holes[0].first_occurrence.start, 5);
    assert_eq!(node.holes[0].first_occurrence.end, 9);
    assert_eq!(
        node.pieces
            .iter()
            .map(|piece| piece.range())
            .collect::<Vec<_>>(),
        vec![
            mettail_runtime::FltSourceRange::new(0, 5),
            mettail_runtime::FltSourceRange::new(5, 9),
            mettail_runtime::FltSourceRange::new(9, 11),
            mettail_runtime::FltSourceRange::new(11, 15),
            mettail_runtime::FltSourceRange::new(15, 16),
        ],
    );
    assert_eq!(node.bounds.body_bytes, 16);
    assert_eq!(node.bounds.source_bytes, 26);
    assert_eq!(node.bounds.piece_count, 5);
    assert_eq!(node.bounds.hole_declarations, 1);
    assert_eq!(node.bounds.hole_occurrences, 2);
}

#[test]
fn l9_5_malformed_hole_is_rejected_before_guest_parsing() {
    mettail_runtime::clear_var_cache();
    assert!(
        Proc::parse("lam:Proc`pair(${x) , injected}, K)`").is_err(),
        "hole text cannot inject guest punctuation",
    );
    assert!(
        Proc::parse("lam:Proc`pair(${x:Term)Bad}, K)`").is_err(),
        "typed-hole categories are qualified identifiers",
    );
}

#[test]
fn l9_5_rholang_fence_and_brace_forms() {
    mettail_runtime::clear_var_cache();
    let fence_source = "lam:Proc```App(${f}, ${g})```";
    let _ = lex(fence_source).expect("linear modal lexer accepts fence FLT");
    let fence = Proc::parse(fence_source).expect("fence FLT parse");
    let fn_node = node_of(&fence);
    assert_eq!(fn_node.selector_name, "lam");
    assert_eq!(fn_node.category, "Proc");
    assert_eq!(fn_node.holes.len(), 2);

    let brace = Proc::parse("lam:Proc{ App(${g}) }").expect("brace FLT parse");
    let bn = node_of(&brace);
    assert_eq!(bn.selector_name, "lam");
    assert_eq!(bn.category, "Proc");
    assert_eq!(bn.body_src, " App(${g}) ");
    assert_eq!(bn.holes.len(), 1);
    assert_eq!(bn.holes[0].name, "g");
}

#[test]
fn l9_5_rholang_empty_body() {
    mettail_runtime::clear_var_cache();
    let source = "lam:Proc``";
    let _ = lex(source).expect("linear modal lexer accepts empty FLT");
    let term = Proc::parse(source).expect("empty-body FLT parse");
    let n = node_of(&term);
    assert_eq!(n.selector_name, "lam");
    assert_eq!(n.category, "Proc");
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
    let uri = Proc::parse("new x(`rho:id`) in { Nil }")
        .expect("an unqualified backtick form remains a URI in its Rholang position");
    assert!(matches!(uri, Proc::PNewUris(_, _)));
    assert!(
        Proc::parse("lam`x`").is_err(),
        "an unqualified identifier must not infer FLT authority",
    );
}

#[test]
fn flt_guest_comment_markers_remain_literal_guest_text() {
    mettail_runtime::clear_var_cache();
    let term = Proc::parse("lam:Proc`App(a // b, /* c */ d)`")
        .expect("host comment channels are inactive in raw guest mode");
    assert_eq!(node_of(&term).body_src, "App(a // b, /* c */ d)");
}

#[test]
fn flt_guest_separator_bytes_do_not_split_the_host_argument_list() {
    mettail_runtime::clear_var_cache();
    Proc::parse("@Nil!(lam:Proc`left),right`, Nil)")
        .expect("closing-paren and comma bytes in one modal guest token are not host delimiters");
}

#[test]
fn auxiliary_comment_is_layout_in_an_empty_variadic_tail() {
    mettail_runtime::clear_var_cache();
    let plain = Proc::parse("@Nil!(Nil,)").expect("empty variadic tail parses");
    let commented = Proc::parse("@Nil!(Nil, /* still empty */)")
        .expect("an auxiliary-channel comment does not populate the tail");
    assert_eq!(format!("{plain:?}"), format!("{commented:?}"));
}

#[test]
fn flt_selector_is_the_same_lexical_variable_as_the_receive_binding() {
    mettail_runtime::clear_var_cache();
    let term =
        Proc::parse("for(lambda <- ret){lambda:Proc`x`}").expect("bound FLT selector parses");
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
