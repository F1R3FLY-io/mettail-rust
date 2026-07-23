//! L9-3 gate — token-kind capture (`v@Tok`) end-to-end.
//!
//! This TEST fixture (it lives in `languages/tests/`, never `languages/src/`)
//! proves the full L9-3 capture-text pipeline: a `tokens {}` custom kind
//! (`Word`) is consumed by a MID-RULE capture (`Tagged`, exercising S2.2) and a
//! LEADING capture (`Flt`, exercising S2.3 Option-A dispatch), and the matched
//! token text is threaded into the AST as a `String` field, bound in the
//! native `![...]` action, rendered by `Display` (round-trip), and carried
//! inertly through the term operations (Eq/Hash/Ord/subst/normalize).
//!
//! The backtick guest mode is retained from the L9-1 gate so the MODAL lexer
//! path is still exercised alongside the capture path.

#![allow(unused_imports, dead_code)]

use mettail_runtime::Language;
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

use mettail_macros::language;

language! {
    name: L9ModalToy,

    options {
        emit_tests: false,
        emit_simulator: false,
        emit_blockly: false,
    },

    types {
        ![i32] as Num
    },

    tokens {
        // L9-3: a NON-modal custom kind (angle-bracketed word) consumed by the
        // Tagged (mid-rule) and Flt (leading) productions below.
        Word = "<[a-z]+>" ;

        // Backtick opener (retained from L9-1 to keep the modal lexer path live).
        FltOpenBacktick = "[a-z]+`" push(guest_backtick) ;

        mode guest_backtick {
            FltCloseBacktick = "`" pop ;
            GuestChunk = "[^`]+" ;
        }
    },

    terms {
        AddNum . a:Num, b:Num |- a "+" b : Num ![a + b] step;
        // Mid-rule capture (S2.2): dispatch on the "tag" trigger, then consume a
        // Word token. The captured text is bound to `w` and used by the action.
        Tagged . |- "tag" w@Word : Num ![w.len() as i32];
        // Leading capture (S2.3, Option-A dispatch): the rule STARTS with a
        // Word-kind capture, then a "!" literal.
        Flt . |- b@Word "!" : Num ![b.len() as i32];
        // F.1 NO-SWAP: two adjacent same-typed (`String`) captures. If field
        // order drifted, `a` and `b` would swap silently (both String) — the
        // action `![a.len()]` and the AST comparison detect it.
        Two . |- "pair" a@Word b@Word : Num ![a.len() as i32];
    },
}

#[test]
fn l9_modal_toy_lexer_interface_resolves() {
    let lang = L9ModalToyLanguage;
    assert_eq!(lang.name(), "L9ModalToy");
}

#[test]
fn l9_modal_toy_default_mode_parses() {
    mettail_runtime::clear_var_cache();
    let term = Num::parse("1 + 2").expect("default-mode parse should succeed");
    let displayed = format!("{}", term);
    assert!(!displayed.is_empty());
}

#[test]
fn l9_mid_rule_capture_parses_to_node_with_text() {
    // "tag <abc>" -> Num::Tagged("<abc>") (the captured text lands in the AST).
    mettail_runtime::clear_var_cache();
    let term = Num::parse("tag <abc>").expect("mid-rule TokenKindCapture parse");
    assert_eq!(term, Num::Tagged("<abc>".to_string()));
}

#[test]
fn l9_leading_capture_parses_to_node_with_text() {
    // "<xyz>!" -> Num::Flt("<xyz>").
    mettail_runtime::clear_var_cache();
    let term = Num::parse("<xyz>!").expect("leading TokenKindCapture parse");
    assert_eq!(term, Num::Flt("<xyz>".to_string()));
}

#[test]
fn l9_capture_display_round_trips() {
    // THE named gate: parse(display(t)) == t for both capture shapes.
    mettail_runtime::clear_var_cache();
    for src in ["tag <abc>", "<xyz>!"] {
        let term = Num::parse(src).expect("parse");
        let printed = format!("{}", term);
        let reparsed = Num::parse(&printed)
            .unwrap_or_else(|e| panic!("re-parse of display {printed:?} failed: {e:?}"));
        assert_eq!(reparsed, term, "round-trip failed for {src:?} (printed {printed:?})");
    }
}

#[test]
fn l9_capture_text_binds_in_native_eval() {
    // The action `![w.len() as i32]` reads the captured String — "<abc>" has 5
    // chars, so eval() yields 5. Proves seam #3 (capture bound in native eval).
    mettail_runtime::clear_var_cache();
    let term = Num::parse("tag <abc>").expect("parse");
    assert_eq!(term.eval(), 5);
    let leading = Num::parse("<wx>!").expect("parse");
    assert_eq!(leading.eval(), 4); // "<wx>" = 4 chars
}

#[test]
fn l9_capture_eq_hash_ord_leaf_semantics() {
    // Hash-cons / Eq / Hash / Ord identity for the token-text leaf.
    let a1 = Num::Tagged("<a>".to_string());
    let a2 = Num::Tagged("<a>".to_string());
    let b = Num::Tagged("<b>".to_string());
    let flt_a = Num::Flt("<a>".to_string());

    // Eq: same text equal; different text unequal; different discriminant unequal.
    assert_eq!(a1, a2);
    assert_ne!(a1, b);
    assert_ne!(a1, flt_a);

    // Hash consistency with Eq (equal values hash equal; distinct ones differ).
    let h = |t: &Num| {
        let mut s = DefaultHasher::new();
        t.hash(&mut s);
        s.finish()
    };
    assert_eq!(h(&a1), h(&a2));
    assert_ne!(h(&a1), h(&b));
    assert_ne!(h(&a1), h(&flt_a));

    // Ord: text order; reflexive Equal.
    assert_eq!(a1.cmp(&a2), std::cmp::Ordering::Equal);
    assert_eq!(a1.cmp(&b), "<a>".cmp("<b>"));
}

#[test]
fn l9_capture_carries_text_through_normalize_and_subst() {
    // A token's text is not a term: subst/normalize carry the `String` leaf
    // through WITHOUT panic or descent (the design's inertness gate). `Tagged`
    // is a native-eval rule, so `normalize` folds it to its value rather than
    // staying identity — the point is the String reaches the action intact,
    // proven by the eval value surviving normalization (a corrupted/descended
    // String would panic or change the value).
    mettail_runtime::clear_var_cache();
    let term = Num::parse("tag <abc>").expect("parse");
    let normalized = term.clone().normalize();
    assert_eq!(normalized.eval(), term.eval(), "normalize must preserve the captured-text-derived value");
    // Pure substitution (no fold) over an empty env is IDENTITY on a token-text
    // leaf — the String has no free variables to replace and must not be
    // descended into.
    let env = L9ModalToyEnv::new();
    assert_eq!(term.substitute_env_no_normalize(&env), term, "subst must carry the String leaf unchanged");
}

#[test]
fn l9_capture_fields_do_not_swap() {
    // F.1 no-swap: two ADJACENT same-typed (`String`) captures must stay in
    // syntax-pattern order. If `a`/`b` swapped, the AST comparison and the
    // `![a.len()]` action (4 = len "<aa>", not 5 = len "<bbb>") would catch it.
    mettail_runtime::clear_var_cache();
    let term = Num::parse("pair <aa> <bbb>").expect("two-capture parse");
    assert_eq!(term, Num::Two("<aa>".to_string(), "<bbb>".to_string()));
    assert_eq!(term.eval(), 4, "action must read the FIRST capture (a), not the second");
}
