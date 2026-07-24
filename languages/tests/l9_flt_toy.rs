//! L9-4 gate — `*flt(node, FltOpen*, FltClose*)` guest-body capture → FltNode.
//!
//! A TEST fixture (`languages/tests/`, never `languages/src/`). It proves the
//! full L9-4 pipeline: three delimiter forms (backtick / reserved-tag brace /
//! fixed fence), each pushing a RAW guest mode, are consumed by a `*flt(...)`
//! GuestBody production that assembles a `mettail_runtime::FltNode`
//! { tag, body_src (verbatim via raw-mode tiling), holes[{name,category,offset}],
//! position }. The `${x}` / `${x:Cat}` holes are recorded with byte offsets into
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
        // Backtick form: `IDENT\`` opens, a bare backtick closes.
        FltOpenBacktick = "[a-z]+`" push(flt_body_backtick) ;
        // Fence form: `IDENT\`\`\`` opens, `\`\`\`` closes.
        FltOpenFence = "[a-z]+```" push(flt_body_fence) ;
        // Reserved-tag brace form: `box{` opens (reserved tag — no bare `id{`
        // ambiguity), `}` closes.
        FltOpenBrace = "box\\{" push(flt_body_brace) ;

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
    // `lam`App(${f}, K)`` → FltBacktick(FltNode{tag:"lam", body_src:"App(${f}, K)",
    // holes:[{name:"f", offset:4}], position:0}).
    mettail_runtime::clear_var_cache();
    let term = Num::parse("lam`App(${f}, K)`").expect("backtick FLT parse");
    let n = node_of(&term);
    assert_eq!(n.tag, "lam");
    assert_eq!(n.body_src, "App(${f}, K)");
    assert_eq!(n.holes.len(), 1);
    assert_eq!(n.holes[0].name, "f");
    assert_eq!(n.holes[0].category, None);
    assert_eq!(&n.body_src[n.holes[0].offset..n.holes[0].offset + 4], "${f}");
    assert_eq!(n.position, 0);
    assert_eq!(term.eval(), 1); // one hole
}

#[test]
fn l9_flt_typed_hole_records_category() {
    // `${f:Proc}` → FltHole{name:"f", category:Some("Proc")}.
    mettail_runtime::clear_var_cache();
    let term = Num::parse("lam`id(${f:Proc})`").expect("typed-hole parse");
    let n = node_of(&term);
    assert_eq!(n.holes.len(), 1);
    assert_eq!(n.holes[0].name, "f");
    assert_eq!(n.holes[0].category.as_deref(), Some("Proc"));
}

#[test]
fn l9_flt_fence_assembles_node() {
    mettail_runtime::clear_var_cache();
    let term = Num::parse("lam```App(${f}, ${g})```").expect("fence FLT parse");
    let n = node_of(&term);
    assert_eq!(n.tag, "lam");
    assert_eq!(n.body_src, "App(${f}, ${g})");
    assert_eq!(n.holes.len(), 2);
    assert_eq!(n.holes[0].name, "f");
    assert_eq!(n.holes[1].name, "g");
    assert_eq!(term.eval(), 2);
}

#[test]
fn l9_flt_brace_assembles_node() {
    // Reserved-tag brace: `box{ App(${f}) }` (NON-nested).
    mettail_runtime::clear_var_cache();
    let term = Num::parse("box{ App(${f}) }").expect("brace FLT parse");
    let n = node_of(&term);
    assert_eq!(n.tag, "box");
    assert_eq!(n.body_src, " App(${f}) ");
    assert_eq!(n.holes.len(), 1);
    assert_eq!(n.holes[0].name, "f");
}

#[test]
fn l9_flt_empty_body_is_clean() {
    // Empty guest body → body_src == "", no holes.
    mettail_runtime::clear_var_cache();
    let term = Num::parse("lam``").expect("empty-body parse");
    let n = node_of(&term);
    assert_eq!(n.tag, "lam");
    assert_eq!(n.body_src, "");
    assert!(n.holes.is_empty());
    assert_eq!(term.eval(), 0);
}
