//! M-1b — the SPATIAL surface (`matches`, `PPar`) and the formula compiler,
//! end-to-end on the REAL f1r3node reducer.
//!
//! # What is under test
//!
//! `t matches φ` compiles to ONE
//! `ExprInstance::EMatchesBody(EMatches{ target: ⟦t⟧, pattern: ⟦φ⟧ })`, where
//! `⟦φ⟧` is produced by `rholang-runtime/src/rholang_formula.rs` (§18.1's table)
//! and the match itself is decided by the reducer's OWN spatial matcher through
//! the `SpatialMatch` seam landed by M-1a (f1r3node `99b7b1c4`). MeTTaIL
//! contributes a pattern COMPILER and no matcher, so what these tests establish
//! is that the compiler emits the pattern the paper's semantics calls for — the
//! matcher's correctness is f1r3node's own, already-shipped property.
//!
//! ```text
//!   RhoCalc source                this repo                      f1r3node
//!  ┌────────────────┐   ┌────────────────────────────┐   ┌────────────────────┐
//!  │ for(@x <- @"c" │   │ lower_proc      ⟦t⟧ target │   │ Match::check_commit│
//!  │   where        │──▶│ lower_formula   ⟦φ⟧ pattern│──▶│  → guard_passes    │
//!  │   x matches φ) │   │ ⇒ EMatches{t, φ}           │   │  → rho_pure_eval   │
//!  └────────────────┘   └────────────────────────────┘   │  → SpatialMatcher- │
//!                                                        │      Oracle        │
//!                                                        └────────────────────┘
//! ```
//!
//! # The observation discipline
//!
//! Every guard-position test reads BOTH `@"OUT"` (did the body fire?) and `@"c"`
//! (is the datum still resting?) from the SAME quiescent store, **verbatim as
//! `Par`s**. Verbatim matters here in a way it did not for M-0: the interesting
//! datum for a spatial match is a PROCESS (`{ @"a"!(1) | @"b"!(2) }`), which no
//! ground reader (`par_as_i64`, `par_as_string`, …) decodes — so a typed reader
//! would report an empty channel for a datum that is very much still there, and
//! "fail shut" would appear to fail. See
//! `run::run_normalized_par_for_oracle_and_read_par_channels`.
//!
//! # Companion suites
//!
//! * `rho_matches_differential.rs` — the host-vs-machine agreement lock.
//! * `languages/tests/rhocalc_semantic_predicate_ambiguity.rs` — parse-count
//!   goldens for `matches` / `PPar`.
//! * `languages/tests/rhocalc_tests.rs::matches_*` — the host evaluator.

#![cfg(feature = "rholang-runtime")]

use std::collections::HashMap;

use mettail_languages::rhocalc::formula::{classify, FormulaShape};
use mettail_languages::rhocalc::Proc;
use mettail_rholang_runtime::rholang_formula::{lower_formula, lower_formula_in_env};
use mettail_rholang_runtime::{
    lower_rholang_proc, run_normalized_par_for_oracle_and_read_par_channels, RholangAstLowerError,
};
use mettail_runtime::clear_var_cache;
use models::rhoapi::connective::ConnectiveInstance;
use models::rhoapi::expr::ExprInstance;
use models::rhoapi::var::VarInstance;
use models::rhoapi::Par;

fn parse(source: &str) -> Proc {
    clear_var_cache();
    Proc::parse_via_wpda(source)
        .unwrap_or_else(|err| panic!("rholang parse failed for {source:?}: {err:?}"))
}

fn parse_lower(source: &str) -> Par {
    let proc = parse(source);
    lower_rholang_proc(&proc)
        .unwrap_or_else(|err| panic!("rholang lowering failed for {source:?}: {err:?}"))
}

/// The verdict of one guarded receive, read from a single quiescent store.
struct Verdict {
    /// Datums that landed on `@"OUT"` — non-empty iff the guarded body fired.
    fired: Vec<Par>,
    /// Datums still resting on `@"c"` — non-empty iff the guard rejected and the
    /// datum was NOT consumed.
    resting: Vec<Par>,
}

async fn guarded_receive(formula: &str, datum: &str) -> Verdict {
    let source = format!(
        r#"{{ for(@x <- @"c" where x matches {formula}) {{ @"OUT"!("fired") }} | @"c"!({datum}) }}"#
    );
    let par = parse_lower(&source);
    let observed: HashMap<String, Vec<Par>> =
        run_normalized_par_for_oracle_and_read_par_channels(&par, &["OUT", "c"])
            .await
            .unwrap_or_else(|err| panic!("guarded receive failed for {source:?}: {err}"));
    Verdict {
        fired: observed.get("OUT").cloned().unwrap_or_default(),
        resting: observed.get("c").cloned().unwrap_or_default(),
    }
}

/// Assert the full operational contract for one (formula, datum) pair:
/// on a satisfied formula the body fires and the datum is consumed; on a
/// falsified one the body does NOT fire and the datum is left RESTING —
/// §18.5's fail-shut contract, both halves from the same store.
async fn assert_guard(formula: &str, datum: &str, expected: bool) {
    let Verdict { fired, resting } = guarded_receive(formula, datum).await;
    assert_eq!(
        !fired.is_empty(),
        expected,
        "`{datum} matches {formula}` must be {expected} on the reducer"
    );
    if expected {
        assert!(
            resting.is_empty(),
            "a committed receive consumes its datum (`{datum} matches {formula}`)"
        );
    } else {
        assert_eq!(
            resting.len(),
            1,
            "a rejected datum must stay RESTING, nothing consumed and nothing fabricated \
             (`{datum} matches {formula}`)"
        );
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// 1. Term patterns — the residual `FormulaShape::Term` arm
// ══════════════════════════════════════════════════════════════════════════════

#[tokio::test]
async fn a_term_formula_matches_the_term_it_denotes() {
    // The compiler's `Term` arm delegates to the SAME `lower_proc` that lowered
    // the datum, so a term matches its own denotation by construction. This test
    // is the operational statement of that structural guarantee.
    assert_guard(r#"@"a"!(1)"#, r#"@"a"!(1)"#, true).await;
    assert_guard(r#"@"a"!(2)"#, r#"@"a"!(1)"#, false).await;
    assert_guard(r#"@"b"!(1)"#, r#"@"a"!(1)"#, false).await;
}

// ══════════════════════════════════════════════════════════════════════════════
// 2. The logical constants — `true` ↦ Wildcard, `false` ↦ statically false
// ══════════════════════════════════════════════════════════════════════════════

#[tokio::test]
async fn verum_is_satisfied_by_every_term_and_falsum_by_none() {
    assert_guard("true", r#"@"a"!(1)"#, true).await;
    assert_guard("true", r#"{ @"a"!(1) | @"b"!(2) }"#, true).await;
    assert_guard("false", r#"@"a"!(1)"#, false).await;
    assert_guard("false", r#"{ @"a"!(1) | @"b"!(2) }"#, false).await;
}

#[test]
fn verum_compiles_to_a_wildcard() {
    let pattern = lower_formula(&parse("true")).expect("`true` must compile");
    assert!(
        matches!(
            pattern.exprs.as_slice(),
            [models::rhoapi::Expr {
                expr_instance: Some(ExprInstance::EVarBody(models::rhoapi::EVar {
                    v: Some(models::rhoapi::Var {
                        var_instance: Some(VarInstance::Wildcard(_))
                    })
                }))
            }]
        ),
        "§18.1: `true` ↦ Wildcard, got {pattern:?}"
    );
    assert!(pattern.connective_used, "a wildcard pattern must advertise `connective_used`");
}

#[test]
fn falsum_compiles_to_the_pattern_satisfied_by_nothing() {
    // `ConnNot Wildcard`: "does not match the thing everything matches" = matches
    // nothing. A real bottom of the pattern lattice, not an approximation — which
    // is what lets `false` appear anywhere INSIDE a formula, not only at its root.
    let pattern = lower_formula(&parse("false")).expect("`false` must compile");
    let connective = match pattern.connectives.as_slice() {
        [connective] => connective
            .connective_instance
            .as_ref()
            .expect("a connective instance"),
        other => panic!("`false` must compile to exactly one connective, got {other:?}"),
    };
    let negated = match connective {
        ConnectiveInstance::ConnNotBody(body) => body,
        other => panic!("`false` must compile to ConnNotBody, got {other:?}"),
    };
    assert!(
        matches!(
            negated.exprs.as_slice(),
            [models::rhoapi::Expr {
                expr_instance: Some(ExprInstance::EVarBody(models::rhoapi::EVar {
                    v: Some(models::rhoapi::Var {
                        var_instance: Some(VarInstance::Wildcard(_))
                    })
                }))
            }]
        ),
        "`false` ↦ ConnNot(Wildcard), got {negated:?}"
    );
}

#[test]
fn a_statically_false_formula_folds_the_whole_guard_to_gbool_false() {
    // §18.1's fold: when the formula is unsatisfiable by construction, the match
    // is `false` for EVERY target, so the guard collapses to a literal and the
    // matcher is never invoked. Asserted structurally — the point of the fold is
    // that no `EMatches` reaches the machine at all.
    for source in [
        "true matches false",
        "true matches (false and true)",
        "true matches (false or false)",
        "true matches (not true)",
        "true matches (true implies false)",
        "true matches { false | true }",
    ] {
        let par = parse_lower(source);
        assert!(
            matches!(
                par.exprs.as_slice(),
                [models::rhoapi::Expr {
                    expr_instance: Some(ExprInstance::GBool(false))
                }]
            ),
            "{source:?} must fold to GBool(false) at lowering, got {par:?}"
        );
    }

    // The control: a formula that is NOT statically false must still emit a real
    // `EMatches`, or the fold would be silently swallowing live matches.
    let par = parse_lower(r#"true matches (false or @"a"!(1))"#);
    assert!(
        matches!(
            par.exprs.as_slice(),
            [models::rhoapi::Expr {
                expr_instance: Some(ExprInstance::EMatchesBody(_))
            }]
        ),
        "a satisfiable formula must emit a real EMatches, got {par:?}"
    );
}

// ══════════════════════════════════════════════════════════════════════════════
// 3. The propositional connectives, at the PATTERN level
// ══════════════════════════════════════════════════════════════════════════════

#[tokio::test]
async fn pattern_level_connectives_decide_on_the_reducer() {
    // `and` / `or` / `not` / `implies` inside a formula are Rholang's
    // `ConnAndBody` / `ConnOrBody` / `ConnNotBody` — pattern-level connectives
    // decided by the reducer's spatial matcher, NOT boolean operators evaluated
    // before the match.
    let datum = r#"@"a"!(1)"#;
    assert_guard(r#"(@"a"!(1) and true)"#, datum, true).await;
    assert_guard(r#"(@"a"!(1) and @"z"!(1))"#, datum, false).await;
    assert_guard(r#"(@"z"!(1) or @"a"!(1))"#, datum, true).await;
    assert_guard(r#"(@"z"!(1) or @"y"!(1))"#, datum, false).await;
    assert_guard(r#"(not @"a"!(1))"#, datum, false).await;
    assert_guard(r#"(not @"z"!(1))"#, datum, true).await;
    // `φ implies ψ ≡ ¬φ ∨ ψ`, the SAME identity M-0 uses at the expression level.
    assert_guard(r#"(@"a"!(1) implies @"a"!(1))"#, datum, true).await; // T ⇒ T
    assert_guard(r#"(@"a"!(1) implies @"z"!(1))"#, datum, false).await; // T ⇒ F
    assert_guard(r#"(@"z"!(1) implies @"z"!(1))"#, datum, true).await; // F ⇒ F (vacuous)
    assert_guard(r#"(@"z"!(1) implies @"a"!(1))"#, datum, true).await; // F ⇒ T
}

#[test]
fn implication_compiles_to_the_material_identity_at_the_pattern_level() {
    // `ConnOrBody [ ConnNotBody ⟦φ⟧ , ⟦ψ⟧ ]` — asserted structurally, because
    // "Rholang needs no `ConnImplies`" is the load-bearing claim that makes the
    // whole implication arm free.
    let pattern = lower_formula(&parse(r#"(@"a"!(1) implies @"b"!(2))"#))
        .expect("an implication formula must compile");
    let disjuncts = match pattern.connectives.as_slice() {
        [connective] => match connective.connective_instance.as_ref() {
            Some(ConnectiveInstance::ConnOrBody(body)) => &body.ps,
            other => panic!("`implies` must compile to ConnOrBody, got {other:?}"),
        },
        other => panic!("`implies` must compile to one connective, got {other:?}"),
    };
    assert_eq!(disjuncts.len(), 2, "material implication is a BINARY disjunction");
    assert!(
        matches!(
            disjuncts[0].connectives.as_slice(),
            [models::rhoapi::Connective {
                connective_instance: Some(ConnectiveInstance::ConnNotBody(_))
            }]
        ),
        "the ANTECEDENT disjunct must be negated, got {:?}",
        disjuncts[0]
    );
    assert!(
        disjuncts[1].connectives.is_empty(),
        "the CONSEQUENT disjunct must ride verbatim, got {:?}",
        disjuncts[1]
    );
}

// ══════════════════════════════════════════════════════════════════════════════
// 4. ★ The separating conjunction — `{φ|ψ}` and the paper's `PPar(φ,ψ)`
// ══════════════════════════════════════════════════════════════════════════════

#[test]
fn the_papers_ppar_parses_verbatim() {
    // Rubric-3's shape (`PPar(<Comm> true, true)`, omnibus :2010) with the
    // modality still to come at M-2. What is pinned here is that the CONNECTIVE
    // itself parses exactly as the paper writes it — no sugar, no rename, no
    // notation delta.
    let elected = parse("PPar(true, true)");
    match &elected {
        Proc::SpatialPPar(left, right) => {
            assert!(matches!(left.as_ref(), Proc::CastBool(_)), "left operand parses as `true`");
            assert!(matches!(right.as_ref(), Proc::CastBool(_)), "right operand parses as `true`");
        },
        other => panic!("`PPar(true, true)` must parse as SpatialPPar, got {other:?}"),
    }

    // And in the position the rubric actually uses it: as a guard formula.
    let guard = parse("t matches PPar(true, true)");
    match &guard {
        Proc::Matches(_, formula) => assert!(
            matches!(formula.as_ref(), Proc::SpatialPPar(..)),
            "the formula operand must be the spatial connective, got {formula:?}"
        ),
        other => panic!("`t matches PPar(true, true)` must parse as Matches, got {other:?}"),
    }
}

#[tokio::test]
async fn the_separating_conjunction_splits_the_term() {
    // The target `{ @"a"!(1) | @"b"!(2) }` splits into two parallel parts. A
    // separating formula is satisfied iff SOME split satisfies both sides — which
    // is the reducer's `list_match_single_` + `sub_pars` + `MaximumBipartiteMatch`,
    // not anything MeTTaIL computes.
    let target = r#"{ @"a"!(1) | @"b"!(2) }"#;

    // `PPar(true, true)` — rubric-3's shape: any term that splits at all.
    assert_guard("PPar(true, true)", target, true).await;
    // One side pinned to a real component, the other a wildcard remainder.
    assert_guard(r#"PPar(@"a"!(1), true)"#, target, true).await;
    assert_guard(r#"PPar(@"b"!(2), true)"#, target, true).await;
    // A component that is NOT present: no split can satisfy it.
    assert_guard(r#"PPar(@"z"!(9), true)"#, target, false).await;
    // Both sides pinned — the whole term is exactly the two components.
    assert_guard(r#"PPar(@"a"!(1), @"b"!(2))"#, target, true).await;
    assert_guard(r#"PPar(@"a"!(1), @"z"!(9))"#, target, false).await;
}

#[tokio::test]
async fn the_braced_host_spelling_is_the_same_connective() {
    // N6: `{ φ | ψ }` is retained as the idiomatic host spelling and must denote
    // EXACTLY what `PPar(φ, ψ)` denotes. Same targets, same verdicts as above.
    let target = r#"{ @"a"!(1) | @"b"!(2) }"#;
    assert_guard(r#"{ @"a"!(1) | true }"#, target, true).await;
    assert_guard(r#"{ @"z"!(9) | true }"#, target, false).await;
    assert_guard(r#"{ @"a"!(1) | @"b"!(2) }"#, target, true).await;
}

#[test]
fn the_two_spellings_compile_to_the_same_pattern() {
    // Stated as a compiler identity, not only as matching agreement: both
    // spellings classify as `FormulaShape::Separation` and are compiled by the
    // same arm, so the emitted `Par`s must be equal byte for byte.
    let braced = lower_formula(&parse(r#"{ @"a"!(1) | true }"#)).expect("braced form compiles");
    let verbatim = lower_formula(&parse(r#"PPar(@"a"!(1), true)"#)).expect("paper form compiles");
    assert_eq!(
        braced, verbatim,
        "`{{ φ | ψ }}` and `PPar(φ, ψ)` must compile to the SAME separating par-pattern"
    );
}

// ══════════════════════════════════════════════════════════════════════════════
// 5. Composition with the rest of the guard language
// ══════════════════════════════════════════════════════════════════════════════

#[tokio::test]
async fn matches_composes_with_the_boolean_guard_language() {
    // `matches` produces an ordinary boolean `Proc`, so it composes with `and` /
    // `or` / `not` / `implies` at the EXPRESSION level — a different level from
    // the pattern-level connectives of §3, and the two must not be confused.
    let source = |guard: &str| {
        format!(r#"{{ for(@x <- @"c" where {guard}) {{ @"OUT"!("fired") }} | @"c"!(@"a"!(1)) }}"#)
    };
    for (guard, expected) in [
        (r#"x matches @"a"!(1) and true"#, true),
        (r#"x matches @"a"!(1) and false"#, false),
        (r#"x matches @"z"!(9) or true"#, true),
        (r#"not (x matches @"a"!(1))"#, false),
        (r#"x matches @"z"!(9) implies x matches @"a"!(1)"#, true),
        (r#"x matches @"a"!(1) implies x matches @"z"!(9)"#, false),
    ] {
        let par = parse_lower(&source(guard));
        let observed = run_normalized_par_for_oracle_and_read_par_channels(&par, &["OUT", "c"])
            .await
            .unwrap_or_else(|err| panic!("composed guard {guard:?} failed: {err}"));
        let fired = !observed.get("OUT").map(Vec::is_empty).unwrap_or(true);
        assert_eq!(fired, expected, "composed guard {guard:?} must be {expected}");
    }
}

#[test]
fn matches_binds_tighter_than_and_so_multi_subject_guards_parse() {
    // The reading the paper's multi-subject guards need, and the same relative
    // order official Rholang gives (`matches` prec 6 > `and` 5 > `or` 4):
    //   `a matches P and b matches Q`  ⇒  `(a matches P) and (b matches Q)`
    let guard = parse("x matches true and y matches false");
    match &guard {
        Proc::And(left, right) => {
            assert!(matches!(left.as_ref(), Proc::Matches(..)), "left conjunct is a `matches`");
            assert!(matches!(right.as_ref(), Proc::Matches(..)), "right conjunct is a `matches`");
        },
        other => panic!("`and` must be the root, got {other:?}"),
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// 6. Totality of the compiler, and the fail-closed edges
// ══════════════════════════════════════════════════════════════════════════════

#[test]
fn the_formula_compiler_is_total_over_every_shape() {
    // Totality is a property of the CLASSIFICATION plus the arms, so it is tested
    // by exercising at least one representative of every `FormulaShape` and
    // asserting the compiler answers `Ok` or a TYPED error — never panics, never
    // returns a placeholder. The `Term` arm's error case is covered separately
    // below.
    for source in [
        // Verum / Falsum
        "true",
        "false",
        // Conjunction / Disjunction / Negation / Implication
        r#"(@"a"!(1) and true)"#,
        r#"(@"a"!(1) or true)"#,
        r#"(not @"a"!(1))"#,
        r#"(@"a"!(1) implies true)"#,
        // Separation, all three spellings
        r#"PPar(true, true)"#,
        r#"{ @"a"!(1) | true }"#,
        // Term: literals, collections, sends, receives, `new`
        r#"@"a"!(1)"#,
        r#""hello""#,
        "42",
        "[1, 2, 3]",
        "Nil",
        r#"for(@y <- @"d") { Nil }"#,
        r#"new q in { @"a"!(1) }"#,
        // Nested and mixed
        r#"(PPar(@"a"!(1), true) or not { @"b"!(2) | false })"#,
        r#"((true and false) implies { @"a"!(1) | not true })"#,
    ] {
        let formula = parse(source);
        // Every shape is CLASSIFIED — the exhaustive match cannot fall through.
        let _shape = classify(&formula);
        // And every shape COMPILES, to a pattern or to a typed error.
        match lower_formula(&formula) {
            Ok(pattern) => assert!(
                pattern != Par::default() || source == "Nil",
                "{source:?} must compile to a non-trivial pattern (only `Nil` is the empty Par)"
            ),
            Err(err) => panic!("{source:?} must compile, got the typed error {err:?}"),
        }
    }
}

#[test]
fn an_unlowerable_sub_term_surfaces_as_a_typed_error_not_a_placeholder() {
    // The residual `Term` arm delegates to `lower_proc`, so a sub-term `lower_proc`
    // rejects must surface AS `lower_proc`'s typed error — the formula compiler
    // adds no swallow-and-substitute layer. `PPar(φ,ψ)` in TERM position is such a
    // sub-term (it is a pattern former, not a term former), so nesting one inside
    // a term operand of a formula exercises exactly this path.
    let formula = parse(r#"@"a"!(PPar(true, true))"#);
    match lower_formula(&formula) {
        Err(RholangAstLowerError::UnsupportedProc(message)) => assert!(
            message.contains("PPar"),
            "the typed error must name the offending construct, got {message:?}"
        ),
        other => {
            panic!("an unlowerable sub-term must fail CLOSED with a typed error, got {other:?}")
        },
    }
}

#[test]
fn ppar_in_term_position_fails_closed() {
    // `PPar(φ,ψ)` denotes a SPLIT assertion, not a process. Lowering it as an
    // ordinary parallel composition would look like it worked while meaning
    // something else, so term position is a typed error.
    match lower_rholang_proc(&parse("PPar(true, true)")) {
        Err(RholangAstLowerError::UnsupportedProc(message)) => {
            assert!(message.contains("PPar"), "the error must name `PPar`, got {message:?}");
            assert!(
                message.contains("matches"),
                "the error must say WHERE the connective is legal, got {message:?}"
            );
        },
        other => panic!("`PPar` in term position must fail closed, got {other:?}"),
    }
}

#[test]
fn every_shape_is_classified_by_constructor() {
    // The classification is the shared seam between the host evaluator and the
    // pattern compiler (`languages/src/rhocalc/formula.rs`), so its assignment is
    // pinned directly: a drift here would silently change BOTH consumers at once.
    assert!(matches!(classify(&parse("true")), FormulaShape::Verum));
    assert!(matches!(classify(&parse("false")), FormulaShape::Falsum));
    assert!(matches!(classify(&parse("true and false")), FormulaShape::Conjunction(..)));
    assert!(matches!(classify(&parse("true or false")), FormulaShape::Disjunction(..)));
    assert!(matches!(classify(&parse("not true")), FormulaShape::Negation(..)));
    assert!(matches!(classify(&parse("true implies false")), FormulaShape::Implication(..)));
    assert!(matches!(classify(&parse("PPar(true, true)")), FormulaShape::Separation(_)));
    assert!(matches!(
        classify(&parse(r#"{ @"a"!(1) | true }"#)),
        FormulaShape::Separation(_)
    ));
    assert!(matches!(classify(&parse(r#"@"a"!(1)"#)), FormulaShape::Term));
    assert!(matches!(classify(&parse("42")), FormulaShape::Term));
}

#[test]
fn the_environment_free_entry_agrees_with_the_empty_environment() {
    // `lower_formula` is documented as `lower_formula_in_env` at the empty binder
    // environment. Pinned, so the public entry cannot drift into a different
    // default.
    let formula = parse(r#"(PPar(@"a"!(1), true) or not false)"#);
    let direct = lower_formula(&formula).expect("compiles");
    let threaded =
        lower_formula_in_env(&formula, &mettail_rholang_runtime::rholang_ast::BoundEnv::new())
            .expect("compiles");
    assert_eq!(direct, threaded);
}
