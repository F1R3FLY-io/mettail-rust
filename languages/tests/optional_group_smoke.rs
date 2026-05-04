//! Opt-Group smoke tests (2026-04-29).
//!
//! Validates the WPDS Opt-Group runtime end-to-end via a synthetic
//! grammar (`mettail_languages::optsmoke`) that exercises:
//!   - The take path: `if true then 1 else 2` — Optional present.
//!   - The skip path: `if true then 1` — Optional absent.
//!   - Both branches of the `if` with each Optional state.
//!
//! The grammar's IfElse rule has term context
//!   `cond:Bool, t:Int, #opt(e:Int)`
//! and syntax pattern
//!   `"if" cond "then" t #opt("else" e)`.
//! Codegen emits `Int::IfElse(Box<Bool>, Box<Int>, Option<Box<Int>>)` and
//! the user-action body `if cond { t } else { e.unwrap_or(0) }`.

use mettail_languages::optsmoke::{Bool, Int};

fn parse_int(input: &str) -> Result<Int, String> {
    Int::parse(input).map_err(|e| format!("{}", e))
}

#[test]
fn if_true_with_else_returns_then_branch() {
    let term = parse_int("if true then 1 else 2").expect("parse should succeed");
    // Action returns t when cond is true → 1.
    let evaluated: i32 = term.eval();
    assert_eq!(
        evaluated, 1,
        "if true then 1 else 2 should evaluate to 1, got {}",
        evaluated
    );
}

#[test]
fn if_true_without_else_returns_then_branch() {
    let term = parse_int("if true then 1").expect("parse should succeed");
    let evaluated: i32 = term.eval();
    assert_eq!(
        evaluated, 1,
        "if true then 1 should evaluate to 1, got {}",
        evaluated
    );
}

#[test]
fn if_false_with_else_returns_else_branch() {
    let term = parse_int("if false then 1 else 2").expect("parse should succeed");
    let evaluated: i32 = term.eval();
    assert_eq!(
        evaluated, 2,
        "if false then 1 else 2 should evaluate to 2, got {}",
        evaluated
    );
}

#[test]
fn if_false_without_else_returns_default_zero() {
    let term = parse_int("if false then 1").expect("parse should succeed");
    let evaluated: i32 = term.eval();
    assert_eq!(
        evaluated, 0,
        "if false then 1 should evaluate to 0 (e.unwrap_or(0)), got {}",
        evaluated
    );
}

#[test]
fn ast_shape_present_carries_some_inner_int() {
    // Direct AST-shape verification: the IfElse variant has Option<Box<Int>>
    // for the optional `e:Int` field. Parse the take-path input and check
    // that the third field is Some.
    let term = parse_int("if false then 1 else 99").expect("parse should succeed");
    match term {
        Int::IfElse(ref _cond, ref _t, ref maybe_e) => {
            assert!(
                maybe_e.is_some(),
                "IfElse with else clause should have Some(_) third field, got None"
            );
            let inner = maybe_e.as_ref().unwrap();
            // Inner should be IntLit(99).
            match inner.as_ref() {
                Int::NumLit(n) => assert_eq!(*n, 99, "inner Int should be 99"),
                other => panic!("expected IntLit(99), got {:?}", other),
            }
        }
        other => panic!("expected IfElse variant, got {:?}", other),
    }
}

#[test]
fn ast_shape_absent_carries_none() {
    let term = parse_int("if true then 42").expect("parse should succeed");
    match term {
        Int::IfElse(ref _cond, ref _t, ref maybe_e) => {
            assert!(
                maybe_e.is_none(),
                "IfElse without else clause should have None third field, got Some(_)"
            );
        }
        other => panic!("expected IfElse variant, got {:?}", other),
    }
}

#[test]
fn bool_atoms_parse_directly() {
    // Independence sanity-check: parsing a Bool literal should still work.
    let t = Bool::parse("true").expect("bool true");
    let f = Bool::parse("false").expect("bool false");
    let _ = (t, f);
}

#[test]
fn int_atom_parses_directly() {
    let n = parse_int("42").expect("int literal");
    match n {
        Int::NumLit(v) => assert_eq!(v, 42),
        other => panic!("expected IntLit(42), got {:?}", other),
    }
}

// Stage 3.3 (2026-04-30): nested IfElse + Display→Parse roundtrip
// regressions. The proptest `gen_optsmoke_prop::int_display_parse_roundtrip`
// previously failed at two distinct boundaries:
//   (1) Display tokenization — `<int>else` glommed into Ident `<int>else`
//       because the optional group's "else" word-literal lacked a leading
//       space. Fixed in `display.rs::generate_engine_pattern_op` by
//       embedding spacing inside the gated WriteString. The tests below
//       pin the spacing invariant.
//   (2) Engine-side: nested IfElse with mixed has-else / no-else
//       branches (dangling-else binding) reaches `WpdsState::Incomplete`
//       at end-of-input. Tracked separately if these tests fail.

#[test]
fn nested_ifelse_inner_else_dangling() {
    // Right-associative dangling-else: the `else` binds to the INNER IfElse.
    // Outer A = IfElse(false, B, None); Inner B = IfElse(false, 1, 2).
    let input = "if false then if false then 1 else 2";
    let term = parse_int(input).unwrap_or_else(|e| {
        panic!("nested-IfElse with dangling else should parse: {:?}", e)
    });
    // Display→Parse roundtrip: re-displaying must produce a re-parseable
    // string equivalent under canonicalization.
    let displayed = format!("{}", term);
    let reparsed = parse_int(&displayed).unwrap_or_else(|e| {
        panic!("re-parsing Display output should succeed: {:?}\nDisplay: {:?}", e, displayed)
    });
    assert_eq!(format!("{}", reparsed), displayed,
        "Display must be idempotent; first={:?}, second={:?}",
        displayed, format!("{}", reparsed));
}

#[test]
fn nested_ifelse_both_have_else() {
    // Both outer and inner have else. With right-associative else binding,
    // the closer else binds to the inner first.
    //   Tokens: if false then if false then 1 else 2 else 3
    //   Tree:   A = IfElse(false, B, 3)
    //           B = IfElse(false, 1, 2)
    let input = "if false then if false then 1 else 2 else 3";
    let term = parse_int(input).unwrap_or_else(|e| {
        panic!("doubly-elsed nested IfElse should parse: {:?}", e)
    });
    let displayed = format!("{}", term);
    let reparsed = parse_int(&displayed).unwrap_or_else(|e| {
        panic!("re-parsing should succeed: {:?}\nDisplay: {:?}", e, displayed)
    });
    assert_eq!(format!("{}", reparsed), displayed);
}

#[test]
fn display_int_abuts_else_keyword_separated() {
    // Direct construction (bypass parsing): IfElse with else=Some(N)
    // where N abuts "else" in the displayed form. The fix should
    // insert a space between t-Param and the optional group's "else"
    // literal, AND between the literal and the e-Param.
    let inner = Int::IfElse(
        Box::new(Bool::BoolLit(true)),
        Box::new(Int::NumLit(456913875)),
        None,
    );
    let outer = Int::IfElse(
        Box::new(Bool::BoolLit(false)),
        Box::new(inner),
        Some(Box::new(Int::NumLit(1894040589))),
    );
    let displayed = format!("{}", outer);
    // The displayed string must contain " else " with both flanking
    // spaces; the lexer-aligned `is_word` rule should also separate
    // any word-literal prefix from adjacent ident-class text.
    assert!(
        displayed.contains(" else "),
        "Display must space-separate 'else' from adjacent ident-like text; got: {:?}",
        displayed
    );
    // And: re-parse must succeed.
    let reparsed = parse_int(&displayed).unwrap_or_else(|e| {
        panic!("Display→Parse roundtrip for direct construction failed: {:?}\nDisplay: {:?}",
            e, displayed)
    });
    assert_eq!(format!("{}", reparsed), displayed);
}

#[test]
fn display_int_no_else_no_trailing_whitespace() {
    // None-branch: Opt emits nothing — output must NOT end with whitespace
    // and must re-parse.
    let term = Int::IfElse(
        Box::new(Bool::BoolLit(false)),
        Box::new(Int::NumLit(42)),
        None,
    );
    let displayed = format!("{}", term);
    assert!(
        !displayed.ends_with(' '),
        "Opt-absent must not leave trailing whitespace; got: {:?}",
        displayed
    );
    let _ = parse_int(&displayed).expect("re-parse must succeed for opt-absent");
}
