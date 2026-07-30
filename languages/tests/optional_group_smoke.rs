//! Opt-Group smoke tests (2026-04-29).
//!
//! Validates the WPDS Opt-Group runtime end-to-end via a synthetic
//! grammar (`tests/definitions/optsmoke.rs`) that exercises:
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

// Task #11: OptSmoke is test-hosted (see tests/definitions/optsmoke.rs).
#[path = "definitions/optsmoke.rs"]
mod optsmoke;
use optsmoke::{Bool, Int};

fn parse_int(input: &str) -> Result<Int, String> {
    Int::parse(input).map_err(|e| format!("{}", e))
}

#[test]
fn if_true_with_else_returns_then_branch() {
    let term = parse_int("if true then 1 else 2").expect("parse should succeed");
    // Action returns t when cond is true → 1.
    let evaluated: i32 = term.eval();
    assert_eq!(evaluated, 1, "if true then 1 else 2 should evaluate to 1, got {}", evaluated);
}

#[test]
fn if_true_without_else_returns_then_branch() {
    let term = parse_int("if true then 1").expect("parse should succeed");
    let evaluated: i32 = term.eval();
    assert_eq!(evaluated, 1, "if true then 1 should evaluate to 1, got {}", evaluated);
}

#[test]
fn if_false_with_else_returns_else_branch() {
    let term = parse_int("if false then 1 else 2").expect("parse should succeed");
    let evaluated: i32 = term.eval();
    assert_eq!(evaluated, 2, "if false then 1 else 2 should evaluate to 2, got {}", evaluated);
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
        },
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
        },
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
//       branches (dangling-else binding) reaches `WpdaState::Incomplete`
//       at end-of-input. Tracked separately if these tests fail.

#[test]
fn nested_ifelse_inner_else_dangling() {
    // Right-associative dangling-else: the `else` binds to the INNER IfElse.
    // Outer A = IfElse(false, B, None); Inner B = IfElse(false, 1, 2).
    let input = "if false then if false then 1 else 2";
    let term = parse_int(input)
        .unwrap_or_else(|e| panic!("nested-IfElse with dangling else should parse: {:?}", e));
    // Display→Parse roundtrip: re-displaying must produce a re-parseable
    // string equivalent under canonicalization.
    let displayed = format!("{}", term);
    let reparsed = parse_int(&displayed).unwrap_or_else(|e| {
        panic!("re-parsing Display output should succeed: {:?}\nDisplay: {:?}", e, displayed)
    });
    assert_eq!(
        format!("{}", reparsed),
        displayed,
        "Display must be idempotent; first={:?}, second={:?}",
        displayed,
        format!("{}", reparsed)
    );
}

#[test]
fn nested_ifelse_both_have_else() {
    // Both outer and inner have else. With right-associative else binding,
    // the closer else binds to the inner first.
    //   Tokens: if false then if false then 1 else 2 else 3
    //   Tree:   A = IfElse(false, B, 3)
    //           B = IfElse(false, 1, 2)
    let input = "if false then if false then 1 else 2 else 3";
    let term = parse_int(input)
        .unwrap_or_else(|e| panic!("doubly-elsed nested IfElse should parse: {:?}", e));
    let displayed = format!("{}", term);
    let reparsed = parse_int(&displayed)
        .unwrap_or_else(|e| panic!("re-parsing should succeed: {:?}\nDisplay: {:?}", e, displayed));
    assert_eq!(format!("{}", reparsed), displayed);
}

#[test]
fn display_int_abuts_else_keyword_separated() {
    // Direct construction (bypass parsing): IfElse with else=Some(N)
    // where N abuts "else" in the displayed form. The fix should
    // insert a space between t-Param and the optional group's "else"
    // literal, AND between the literal and the e-Param.
    let inner = Int::IfElse(
        std::sync::Arc::new(Bool::BoolLit(true)),
        std::sync::Arc::new(Int::NumLit(456913875)),
        None,
    );
    let outer = Int::IfElse(
        std::sync::Arc::new(Bool::BoolLit(false)),
        std::sync::Arc::new(inner),
        Some(std::sync::Arc::new(Int::NumLit(1894040589))),
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
        panic!(
            "Display→Parse roundtrip for direct construction failed: {:?}\nDisplay: {:?}",
            e, displayed
        )
    });
    assert_eq!(format!("{}", reparsed), displayed);
}

#[test]
fn display_int_no_else_no_trailing_whitespace() {
    // None-branch: Opt emits nothing — output must NOT end with whitespace
    // and must re-parse.
    let term = Int::IfElse(
        std::sync::Arc::new(Bool::BoolLit(false)),
        std::sync::Arc::new(Int::NumLit(42)),
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

// ════════════════════════════════════════════════════════════════════════
// T-3 (Stage 3.12 closure / Class A.i Opt-Group invariant, Commit 5,
// 2026-05-06): 3-deep nested IfElse dangling-else tests. Verifies that
// right-associative dangling-else semantics — each `else` binds to the
// most-recent unmatched `then` — work correctly through 3 levels of
// nesting. The Opt-Group A.i Fork emission (binder.rs:992-1046) plus
// the BinderListLoop close/sep/ident Fork (Hack #2) plus the InfixLoop
// tier Fork (Hacks #17+#20) all interact at this depth.
//
// Existing tests cover 1-deep dangling-else (basic Opt-Group take/skip)
// and the IfElse AST round-trip. T-3 fills the 3-deep gap.
// ════════════════════════════════════════════════════════════════════════

/// 3-deep nested IfElse with NO `else` clauses: each level's optional
/// is absent. AST = `IfElse(_, IfElse(_, IfElse(_, _, None), None), None)`.
#[test]
fn three_deep_nested_ifelse_no_elses() {
    let term =
        parse_int("if false then if false then if false then 1").expect("parse should succeed");
    match &term {
        Int::IfElse(_, t1, e1) => {
            assert!(e1.is_none(), "outermost else should be None");
            match t1.as_ref() {
                Int::IfElse(_, t2, e2) => {
                    assert!(e2.is_none(), "middle else should be None");
                    match t2.as_ref() {
                        Int::IfElse(_, t3, e3) => {
                            assert!(e3.is_none(), "innermost else should be None");
                            assert!(matches!(t3.as_ref(), Int::NumLit(1)));
                        },
                        _ => panic!("innermost not IfElse: {:?}", t2),
                    }
                },
                _ => panic!("middle not IfElse: {:?}", t1),
            }
        },
        _ => panic!("not IfElse: {:?}", term),
    }
}

/// 3-deep with one `else` — right-associative binds to the INNERMOST
/// unmatched `then`. AST = `IfElse(_, IfElse(_, IfElse(_, 1, Some(2)), None), None)`.
#[test]
fn three_deep_nested_ifelse_innermost_else_only() {
    let term = parse_int("if false then if false then if false then 1 else 2")
        .expect("parse should succeed");
    match &term {
        Int::IfElse(_, t1, e1) => {
            assert!(e1.is_none(), "outermost else should be None");
            match t1.as_ref() {
                Int::IfElse(_, t2, e2) => {
                    assert!(e2.is_none(), "middle else should be None");
                    match t2.as_ref() {
                        Int::IfElse(_, _, e3) => {
                            assert!(e3.is_some(), "innermost else should be Some(2)");
                            assert!(matches!(e3.as_ref().unwrap().as_ref(), Int::NumLit(2)));
                        },
                        _ => panic!("innermost not IfElse: {:?}", t2),
                    }
                },
                _ => panic!("middle not IfElse: {:?}", t1),
            }
        },
        _ => panic!("not IfElse: {:?}", term),
    }
}

/// 3-deep with two `else`s — right-associative binds first to innermost
/// (else 2), second to middle (else 3). Outermost remains None.
/// AST = `IfElse(_, IfElse(_, IfElse(_, 1, Some(2)), Some(3)), None)`.
#[test]
fn three_deep_nested_ifelse_innermost_and_middle_elses() {
    let term = parse_int("if false then if false then if false then 1 else 2 else 3")
        .expect("parse should succeed");
    match &term {
        Int::IfElse(_, t1, e1) => {
            assert!(e1.is_none(), "outermost else should be None");
            match t1.as_ref() {
                Int::IfElse(_, t2, e2) => {
                    assert!(e2.is_some(), "middle else should be Some(3)");
                    assert!(matches!(e2.as_ref().unwrap().as_ref(), Int::NumLit(3)));
                    match t2.as_ref() {
                        Int::IfElse(_, _, e3) => {
                            assert!(e3.is_some(), "innermost else should be Some(2)");
                            assert!(matches!(e3.as_ref().unwrap().as_ref(), Int::NumLit(2)));
                        },
                        _ => panic!("innermost not IfElse: {:?}", t2),
                    }
                },
                _ => panic!("middle not IfElse: {:?}", t1),
            }
        },
        _ => panic!("not IfElse: {:?}", term),
    }
}

/// 3-deep with all three `else`s — innermost gets 2, middle gets 3,
/// outermost gets 4 via right-associative greedy binding.
/// AST = `IfElse(_, IfElse(_, IfElse(_, 1, Some(2)), Some(3)), Some(4))`.
#[test]
fn three_deep_nested_ifelse_all_three_elses() {
    let term = parse_int("if false then if false then if false then 1 else 2 else 3 else 4")
        .expect("parse should succeed");
    match &term {
        Int::IfElse(_, t1, e1) => {
            assert!(e1.is_some(), "outermost else should be Some(4)");
            assert!(matches!(e1.as_ref().unwrap().as_ref(), Int::NumLit(4)));
            match t1.as_ref() {
                Int::IfElse(_, t2, e2) => {
                    assert!(e2.is_some(), "middle else should be Some(3)");
                    assert!(matches!(e2.as_ref().unwrap().as_ref(), Int::NumLit(3)));
                    match t2.as_ref() {
                        Int::IfElse(_, _, e3) => {
                            assert!(e3.is_some(), "innermost else should be Some(2)");
                            assert!(matches!(e3.as_ref().unwrap().as_ref(), Int::NumLit(2)));
                        },
                        _ => panic!("innermost not IfElse: {:?}", t2),
                    }
                },
                _ => panic!("middle not IfElse: {:?}", t1),
            }
        },
        _ => panic!("not IfElse: {:?}", term),
    }
}

/// 3-deep dangling-else parse-display roundtrip: AST → display → re-parse
/// yields the same AST. Verifies the Display impl correctly threads the
/// optional else clauses across three levels of nesting.
#[test]
fn three_deep_nested_ifelse_display_roundtrip() {
    let inputs = [
        "if false then if false then if false then 1",
        "if false then if false then if false then 1 else 2",
        "if false then if false then if false then 1 else 2 else 3",
        "if false then if false then if false then 1 else 2 else 3 else 4",
    ];
    for input in &inputs {
        let term =
            parse_int(input).unwrap_or_else(|e| panic!("parse failed for {:?}: {:?}", input, e));
        let displayed = format!("{}", term);
        let reparsed = parse_int(&displayed)
            .unwrap_or_else(|e| panic!("re-parse failed for {:?}: {:?}", displayed, e));
        let redisplayed = format!("{}", reparsed);
        assert_eq!(
            displayed, redisplayed,
            "round-trip not stable for input {:?}: displayed={:?} redisplayed={:?}",
            input, displayed, redisplayed,
        );
    }
}

// ---------------------------------------------------------------------------
// ★★ #189 RESIDUAL — the OPTIONAL SAME-CATEGORY CHILD, and why this file gained a
// depth test.
//
// `macros/src/gen/native/eval.rs` emits `try_eval` as an `__EvalFrame` work stack for
// every category with a HOL rule, and `IfElse`'s `t` branch has always gone onto that
// stack. Its `#opt(e:Int)` branch did NOT: the emitter classified an optional child as
// a CROSS-category capture (`CrossKind::OptionalNative`) and evaluated it EAGERLY with
// `__b.as_ref().try_eval()?` inside the Visit arm — on the host stack, once per level.
//
// The comment that justified it said the `Some(_)`/`None` branching "doesn't fit the
// unconditional Visit-frame push". The premise is true and the conclusion does not
// follow: what the branching did not fit was the FRAME, which had no way to say the
// child was absent. It now carries a presence flag, the child is Visit-pushed when
// present, and the Reduce arm pops conditionally.
//
// ★ `optsmoke` is the ONLY grammar in the workspace that instantiates the shape — a
// census of all 54 generated `eval.rs` files finds exactly one — so this file is where
// the regression gate belongs.
// ---------------------------------------------------------------------------

/// `if false then 1 else (if false then 1 else (… else 7))` built STRUCTURALLY to
/// `DEPTH` levels, so the ladder is not bounded by the parser.
///
/// ⚠ Built with a loop, never recursion: a recursive builder would overflow before the
/// evaluator got the chance to, and the subject would measure the fixture.
fn deep_else_chain(depth: usize) -> Int {
    use std::sync::Arc;
    let mut term = Int::NumLit(7);
    for _ in 0..depth {
        term = Int::IfElse(
            Arc::new(Bool::BoolLit(false)),
            Arc::new(Int::NumLit(1)),
            Some(Arc::new(term)),
        );
    }
    term
}

/// **The gate: `try_eval` down a deep chain nested through the OPTIONAL branch, on a
/// stack far too small to hold one host frame per level.**
///
/// 200,000 levels on a 256 KiB stack is ~1.3 bytes per level. The pre-conversion
/// emitter spent a full `try_eval` frame there, so this could not have completed —
/// it is a one-directional gate by necessity, because a stack overflow ABORTS the
/// process and cannot be caught and asserted upon.
///
/// ⚠ ANTI-VACUITY: the assertion is on the VALUE, not on completion. Every `cond` is
/// `false`, so the whole chain must be walked to its `NumLit(7)` leaf and unwound
/// through 200,000 `e.unwrap_or(0)` steps; the answer is 7 only if it was. A driver
/// that stopped early would return `1` (the nearest `then` branch) or `0` (the
/// `unwrap_or` default), both of which fail here.
#[test]
fn try_eval_is_stack_safe_through_the_optional_else_branch() {
    const DEPTH: usize = 200_000;
    let handle = std::thread::Builder::new()
        .stack_size(256 * 1024)
        .spawn(|| {
            let term = deep_else_chain(DEPTH);
            let value = term.try_eval();
            // The chain is dropped by the generated pooled iterative `Drop`, which is
            // measured flat by `stack_depth_gate`'s `ast_drop` — so the teardown is not
            // a second, hidden host recursion on this same 256 KiB stack.
            drop(term);
            value
        })
        .expect("spawning the small-stack evaluator thread must succeed");
    let value = handle.join().expect(
        "try_eval on a 200,000-deep chain nested through `#opt(e:Int)` must complete on a \
         256 KiB stack — a panic or abort here means the optional same-category child is \
         being evaluated by host recursion again",
    );
    assert_eq!(
        value,
        Some(7),
        "every `cond` in the chain is `false`, so `try_eval` must walk all {DEPTH} levels to \
         the `NumLit(7)` leaf and carry it back out through every `e.unwrap_or(0)`. A value \
         of 1 means it answered from a `then` branch and 0 means it answered from the \
         `unwrap_or` default — either way it did not descend."
    );
}
