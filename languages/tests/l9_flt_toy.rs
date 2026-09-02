//! L9-4 gate — `*flt(node, FltOpen*, FltClose*)` guest-body capture → FltNode.
//!
//! A TEST fixture (`languages/tests/`, never `languages/src/`). It proves the
//! full L9-4 pipeline: three delimiter forms (backtick / paired brace /
//! fixed fence), each pushing a RAW guest mode, are consumed by a `*flt(...)`
//! GuestBody production that assembles a `mettail_runtime::FltNode`
//! { selector, category, body_src (verbatim via raw-mode tiling), ranged holes,
//! position }. The `${x}` / `${x:Cat}` holes are recorded with byte ranges into
//! `body_src`. (Depth-counted NESTED braces are exercised by the sibling test
//! once depth-counting lands.)

#![allow(unused_imports, dead_code)]

use mettail_runtime::{FltHole, FltNode, Language};

use mettail_macros::language;

language! {
    name: L9FltToy,

    options {
        emit_tests: false,
        emit_simulator: false,
        emit_blockly: false,
    },

    types {
        ![i32] as Num
    },

    tokens {
        // Every opener contains an explicit lexical selector and result category.
        FltOpenBacktick = "[a-zA-Z_][a-zA-Z0-9_]*:[a-zA-Z_][a-zA-Z0-9_]*`" push(flt_body_backtick) ;
        FltOpenFence = "[a-zA-Z_][a-zA-Z0-9_]*:[a-zA-Z_][a-zA-Z0-9_]*```" push(flt_body_fence) ;
        FltOpenBrace = "[a-zA-Z_][a-zA-Z0-9_]*:[a-zA-Z_][a-zA-Z0-9_]*\\{" push(flt_body_brace) ;

        raw mode flt_body_backtick {
            FltCloseBacktick = "`" pop ;
            Hole = "\\$\\{[^}]*\\}" ;
            GuestChunk = "[^`$]+" ;
        }
        raw mode flt_body_fence {
            FltCloseFence = "```" pop ;
            Hole = "\\$\\{[^}]*\\}" ;
            GuestChunk = "[^`$]+" ;
        }
        raw mode flt_body_brace {
            // #13: a bare `{` inside the brace body self-pushes the guest mode, so
            // the mode stack depth-counts nesting and the FLT closes at the DEPTH-0
            // `}`. The `GuestBody` body-scan depth-counts these (text == the opener
            // delimiter `{`); inner `{`/`}` are body content.
            FltBraceOpen = "\\{" push(flt_body_brace) ;
            FltCloseBrace = "\\}" pop ;
            Hole = "\\$\\{[^}]*\\}" ;
            GuestChunk = "[^{}$]+" ;
        }
    },

    terms {
        AddNum . a:Num, b:Num |- a "+" b : Num ![a + b] step;
        // The action reads the assembled FltNode (`node` is `&Arc<FltNode>`):
        // eval() yields the hole count, proving the node reached the action.
        FltBacktick . |- *flt(node, FltOpenBacktick, FltCloseBacktick) : Num ![node.holes.len() as i32];
        FltFence . |- *flt(node, FltOpenFence, FltCloseFence) : Num ![node.holes.len() as i32];
        FltBrace . |- *flt(node, FltOpenBrace, FltCloseBrace) : Num ![node.holes.len() as i32];
    },
}

fn node_of(term: &Num) -> &FltNode {
    match term {
        Num::FltBacktick(n) | Num::FltFence(n) | Num::FltBrace(n) => n,
        _ => panic!("expected an Flt* variant, got {term:?}"),
    }
}

#[test]
fn l9_flt_lexer_interface_resolves() {
    let lang = L9FltToyLanguage;
    assert_eq!(lang.name(), "L9FltToy");
}

#[test]
fn l9_flt_default_mode_parses() {
    mettail_runtime::clear_var_cache();
    let term = Num::parse("1 + 2").expect("default-mode parse");
    assert!(!format!("{}", term).is_empty());
}

#[test]
fn l9_flt_backtick_assembles_node() {
    // The opener pins both the lexical selector and the result category.
    mettail_runtime::clear_var_cache();
    let term = Num::parse("lam:Num`App(${f}, K)`").expect("backtick FLT parse");
    let n = node_of(&term);
    assert_eq!(n.selector_name, "lam");
    assert_eq!(n.category, "Num");
    assert_eq!(n.body_src, "App(${f}, K)");
    assert_eq!(n.holes.len(), 1);
    assert_eq!(n.holes[0].name, "f");
    assert_eq!(n.holes[0].category, None);
    let range = n.holes[0].first_occurrence;
    assert_eq!(&n.body_src[range.start..range.end], "${f}");
    assert_eq!(n.position, 0);
    assert_eq!(term.eval(), 1); // one hole
}

#[test]
fn l9_flt_typed_hole_records_category() {
    // `${f:Proc}` → FltHole{name:"f", category:Some("Proc")}.
    mettail_runtime::clear_var_cache();
    let term = Num::parse("lam:Num`id(${f:Proc})`").expect("typed-hole parse");
    let n = node_of(&term);
    assert_eq!(n.holes.len(), 1);
    assert_eq!(n.holes[0].name, "f");
    assert_eq!(n.holes[0].category.as_deref(), Some("Proc"));
}

#[test]
fn l9_flt_fence_assembles_node() {
    mettail_runtime::clear_var_cache();
    let term = Num::parse("lam:Num```App(${f}, ${g})```").expect("fence FLT parse");
    let n = node_of(&term);
    assert_eq!(n.selector_name, "lam");
    assert_eq!(n.category, "Num");
    assert_eq!(n.body_src, "App(${f}, ${g})");
    assert_eq!(n.holes.len(), 2);
    assert_eq!(n.holes[0].name, "f");
    assert_eq!(n.holes[1].name, "g");
    assert_eq!(term.eval(), 2);
}

#[test]
fn l9_flt_brace_assembles_node() {
    // Explicit-selector brace form (non-nested).
    mettail_runtime::clear_var_cache();
    let term = Num::parse("lam:Num{ App(${f}) }").expect("brace FLT parse");
    let n = node_of(&term);
    assert_eq!(n.selector_name, "lam");
    assert_eq!(n.category, "Num");
    assert_eq!(n.body_src, " App(${f}) ");
    assert_eq!(n.holes.len(), 1);
    assert_eq!(n.holes[0].name, "f");
}

#[test]
fn l9_flt_nested_brace_depth_counts_to_zero_close() {
    // #13: BALANCED nested braces `box{ App(box{ ${f} }, K) }` — the body spans to
    // the DEPTH-0 `}` (the inner `box{ … }` is content), so `body_src` includes the
    // nested braces verbatim and the hole is still recorded.
    mettail_runtime::clear_var_cache();
    let term = Num::parse("lam:Num{ App(box{ ${f} }, K) }").expect("nested-brace FLT parse");
    let n = node_of(&term);
    assert_eq!(n.selector_name, "lam");
    assert_eq!(n.category, "Num");
    assert_eq!(n.body_src, " App(box{ ${f} }, K) ");
    assert_eq!(n.holes.len(), 1);
    assert_eq!(n.holes[0].name, "f");
    let range = n.holes[0].first_occurrence;
    assert_eq!(&n.body_src[range.start..range.end], "${f}");
}

#[test]
fn l9_flt_empty_body_is_clean() {
    // Empty guest body → body_src == "", no holes.
    mettail_runtime::clear_var_cache();
    let term = Num::parse("lam:Num``").expect("empty-body parse");
    let n = node_of(&term);
    assert_eq!(n.selector_name, "lam");
    assert_eq!(n.category, "Num");
    assert_eq!(n.body_src, "");
    assert!(n.holes.is_empty());
    assert_eq!(term.eval(), 0);
}
