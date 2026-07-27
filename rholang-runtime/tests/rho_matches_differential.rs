//! M-1b — the **host-vs-machine agreement lock** for `matches`.
//!
//! # Why this suite exists
//!
//! Rholang guards have TWO evaluators, and the standing obligation on that design
//! is that they never disagree:
//!
//! | | Where | What decides a `matches` |
//! | --- | --- | --- |
//! | **host** | `languages/src/rholang/receive.rs::eval_guard_bool` | `formula::host_matches_verdict` → the generated first-order `Proc::match_pattern` |
//! | **machine** | f1r3node `guard_passes` → `rho_pure_eval::eval_with` | `SpatialMatcherOracle` → the reducer's own `SpatialMatcherContext` |
//!
//! A divergence would be invisible in ordinary use — the host path only runs
//! under Dovetail/oracle normalization — and would surface as a term that
//! normalizes one way locally and another way on the node. That is a consensus
//! hazard, so it is pinned here as an executable property over a matrix that
//! covers every `FormulaShape`, in both a satisfied and a falsified instance.
//!
//! # The three properties
//!
//! ```text
//!   (1) AGREEMENT   host(t, φ) = Some(v)  ⟹  machine(t, φ) = v
//!   (2) GROUNDING   machine(t, φ) = the verdict recorded in MATRIX
//!   (3) SOUNDNESS   host(t, φ) ≠ Some(false)  for a term-pattern φ
//! ```
//!
//! **(1)** is the lock itself. It is one-directional on purpose: the host may
//! answer `None` ("I decline"), which is not a gap in the agreement —
//! `eval_guard_bool`'s callers treat an undecided guard as "do not fire
//! host-side", leaving a `CommWhere` marker, so the decision is DEFERRED to the
//! machine rather than guessed. Fail closed, never fabricate.
//!
//! **(2)** keeps that escape hatch honest. Without an independently-recorded
//! machine verdict, a regression that made the machine answer `false` everywhere
//! would satisfy (1) vacuously on every declined row. The recorded verdicts ARE
//! the semantics the paper's spatial fragment is supposed to have.
//!
//! **(3)** is the reason the host's term arm is positive-only. The generated
//! first-order matcher is not a faithful model of the reducer's spatial matcher
//! in the FAILURE direction — for the target `@"a"!([1, 2])` and the pattern
//! `@"a"!([1, v])` the reducer matches and the generated matcher does not,
//! because the generator's collection-literal arms do not treat an element free
//! variable as a binder. A host match still PROVES a machine match (the
//! containment argument in `formula::host_matches_verdict`), so success may be
//! reported and failure may not.

#![cfg(feature = "rholang-runtime")]

use mettail_languages::rholang::formula::{
    classify, host_matches_verdict, is_statically_false, is_statically_true, FormulaShape,
};
use mettail_languages::rholang::Proc;
use mettail_rholang_runtime::{
    lower_rholang_proc, run_normalized_par_for_oracle_and_read_par_channels,
};
use mettail_runtime::clear_var_cache;

fn parse(source: &str) -> Proc {
    clear_var_cache();
    Proc::parse_via_wpda(source)
        .unwrap_or_else(|err| panic!("rholang parse failed for {source:?}: {err:?}"))
}

/// The MACHINE verdict for `target matches formula`, obtained by running the
/// guard on the real reducer and observing whether the guarded body fired.
async fn machine_verdict(target: &str, formula: &str) -> bool {
    // ⚠ The formula is PARENTHESIZED. `matches` binds tighter than `and`/`or`/
    // `implies` (deliberately — that is the reading multi-subject guards need), so
    // an unparenthesized `x matches φ or ψ` would parse as `(x matches φ) or ψ`,
    // a BOOLEAN disjunction of a match and a process, not the formula-level
    // disjunction the host is asked about. Parenthesizing makes both sides of the
    // differential see the SAME formula, which is the whole point of the suite.
    // (Rholang parentheses are transparent — there is no `PParen` node — so this
    // changes grouping only.)
    let source = format!(
        r#"{{ for(@x <- @"c" where x matches ({formula})) {{ @"OUT"!("fired") }} | @"c"!({target}) }}"#
    );
    clear_var_cache();
    let proc = Proc::parse_via_wpda(&source)
        .unwrap_or_else(|err| panic!("rholang parse failed for {source:?}: {err:?}"));
    let par = lower_rholang_proc(&proc)
        .unwrap_or_else(|err| panic!("rholang lowering failed for {source:?}: {err:?}"));
    let observed = run_normalized_par_for_oracle_and_read_par_channels(&par, &["OUT", "c"])
        .await
        .unwrap_or_else(|err| panic!("guarded receive failed for {source:?}: {err}"));
    let fired = !observed.get("OUT").map(Vec::is_empty).unwrap_or(true);
    let resting = observed.get("c").map(Vec::len).unwrap_or(0);
    // The fail-shut contract is invariant across the whole matrix, so it is
    // checked on every single row rather than in a separate test: a machine
    // "false" that CONSUMED the datum would be a different (and worse) bug than a
    // disagreement.
    assert_eq!(
        resting,
        usize::from(!fired),
        "`{target} matches {formula}`: a rejected datum must rest and a committed one must be \
         consumed (fired = {fired})"
    );
    fired
}

/// The HOST verdict, or `None` where the host declines.
fn host_verdict(target: &str, formula: &str) -> Option<bool> {
    let target = parse(target);
    let formula = parse(formula);
    host_matches_verdict(&target, &formula)
}

/// `(target, formula, expected MACHINE verdict)`.
///
/// The third column is the SEMANTICS — what the paper's spatial fragment says
/// `target ⊨ formula` is — recorded independently of either evaluator, so a
/// regression in one cannot be masked by the other agreeing with it.
const MATRIX: &[(&str, &str, bool)] = &[
    // ── Verum / Falsum ────────────────────────────────────────────────────────
    (r#"@"a"!(1)"#, "true", true),
    (r#"@"a"!(1)"#, "false", false),
    (r#"{ @"a"!(1) | @"b"!(2) }"#, "true", true),
    (r#"{ @"a"!(1) | @"b"!(2) }"#, "false", false),
    // ── Ground term patterns ──────────────────────────────────────────────────
    (r#"@"a"!(1)"#, r#"@"a"!(1)"#, true),
    (r#"@"a"!(1)"#, r#"@"a"!(2)"#, false),
    (r#"@"a"!(1)"#, r#"@"b"!(1)"#, false),
    (r#""hello""#, r#""hello""#, true),
    (r#""hello""#, r#""goodbye""#, false),
    ("Nil", "Nil", true),
    // ── Negation ──────────────────────────────────────────────────────────────
    (r#"@"a"!(1)"#, r#"(not @"a"!(1))"#, false),
    (r#"@"a"!(1)"#, r#"(not @"z"!(9))"#, true),
    (r#"@"a"!(1)"#, "(not false)", true),
    // ── Conjunction ───────────────────────────────────────────────────────────
    (r#"@"a"!(1)"#, r#"(@"a"!(1) and true)"#, true),
    (r#"@"a"!(1)"#, r#"(@"a"!(1) and @"z"!(9))"#, false),
    (r#"@"a"!(1)"#, "(true and true)", true),
    // ── Disjunction ───────────────────────────────────────────────────────────
    (r#"@"a"!(1)"#, r#"(@"z"!(9) or @"a"!(1))"#, true),
    (r#"@"a"!(1)"#, r#"(@"z"!(9) or @"y"!(8))"#, false),
    (r#"@"a"!(1)"#, "(false or true)", true),
    // ── Implication — the four rows of `⇒`, at the PATTERN level ──────────────
    (r#"@"a"!(1)"#, r#"(@"a"!(1) implies @"a"!(1))"#, true),
    (r#"@"a"!(1)"#, r#"(@"a"!(1) implies @"z"!(9))"#, false),
    (r#"@"a"!(1)"#, r#"(@"z"!(9) implies @"z"!(9))"#, true),
    (r#"@"a"!(1)"#, r#"(@"z"!(9) implies @"a"!(1))"#, true),
    // ── Separation — the host declines these ──────────────────────────────────
    (r#"{ @"a"!(1) | @"b"!(2) }"#, "PPar(true, true)", true),
    (r#"{ @"a"!(1) | @"b"!(2) }"#, r#"PPar(@"a"!(1), true)"#, true),
    (r#"{ @"a"!(1) | @"b"!(2) }"#, r#"PPar(@"z"!(9), true)"#, false),
    (r#"{ @"a"!(1) | @"b"!(2) }"#, r#"{ @"a"!(1) | true }"#, true),
    (r#"{ @"a"!(1) | @"b"!(2) }"#, r#"{ @"z"!(9) | true }"#, false),
    // ── Separation under a settled connective: statically decided, so the host
    //    must NOT decline even though a `Separation` is present.
    (r#"@"a"!(1)"#, r#"(false and PPar(true, true))"#, false),
    (r#"@"a"!(1)"#, r#"(true or PPar(@"z"!(9), true))"#, true),
    // ── ★ Free variables in PATTERN position ──────────────────────────────────
    //
    // In TERM position an unbound variable lowers to a distinguishable MARKER
    // datum (`@"mtl#out"!("mtl:v")`); inside a formula it must instead lower to a
    // `Wildcard` (`BoundEnv::free_vars_are_patterns`). Without that switch
    // `@"a"!(1) matches @"a"!(v)` is FALSE — the machine would be comparing the
    // datum against a marker — and `matches` would silently mean something no
    // reader intends.
    (r#"@"a"!(1)"#, "v", true),
    (r#"{ @"a"!(1) | @"b"!(2) }"#, "v", true),
    (r#""hello""#, "v", true),
    (r#"@"a"!(1)"#, r#"@"a"!(v)"#, true),
    (r#"@"a"!(1)"#, r#"@"b"!(v)"#, false),
    (r#"@"a"!(1)"#, r#"@"a"!(v) or @"z"!(9)"#, true),
    (r#"@"a"!(1)"#, r#"not @"a"!(v)"#, false),
    // Non-linear: the SAME variable twice. `MatchBindings::merge` EXTENDS rather
    // than rejecting a conflict, so the host imposes no equality constraint —
    // which is exactly what two independent wildcards do on the machine.
    (r#"@"a"!(1)"#, r#"@"a"!(v) and @"a"!(v)"#, true),
    // ── Free variables under each COMPOSITE the lowering builds ───────────────
    //
    // `connective_used` is a per-node cached summary and the matcher
    // short-circuits to structural EQUALITY when it is false, so a placeholder
    // buried inside a composite matches only if every ANCESTOR node reports it.
    // A construction site that still ASSERTS `connective_used: false` shows up
    // here as a machine verdict of `false` where `true` is recorded.
    (r#"@"a"!([1, 2])"#, r#"@"a"!([1, v])"#, true),
    (r#"@"a"!([1, 2])"#, r#"@"a"!([1, 9])"#, false),
    (r#"@"a"!({"k": 1})"#, r#"@"a"!({"k": v})"#, true),
    (r#"@"a"!({"k": 1})"#, r#"@"a"!({"k": 1})"#, true),
    (r#"{ @"a"!(1) | @"b"!(2) }"#, r#"{ @"a"!(v) | @"b"!(2) }"#, true),
    (r#"{ @"a"!(1) | @"b"!(2) }"#, r#"{ @"a"!(v) | @"b"!(9) }"#, false),
    (r#"@"a"!(@"b"!(@"c"!(1)))"#, r#"@"a"!(@"b"!(@"c"!(v)))"#, true),
    (r#"@"a"!(@"b"!(@"c"!(1)))"#, r#"@"a"!(@"b"!(@"z"!(v)))"#, false),
    // ── ★ D11 — CARDINALITY of a par payload (2026-07-25) ─────────────────────
    //
    // A par is a MULTISET, and a pattern must account for EVERY element of the
    // ground: `1 | 2` does not match the pattern `1`. The generated `HashBag`
    // collection arm claimed one ground element per PATTERN element and never
    // compared cardinalities, so every leftover ground element was silently
    // ignored and `pattern ⊆ ground` MATCHED. The sibling `Vec` arm has always
    // had the guard (`g_vec.len() != p_vec.len()`), so the omission was an
    // asymmetry rather than a considered choice.
    //
    // This row is a WRONG-ANSWER witness, not a coverage gap: it is reachable
    // through `host_matches_verdict` because `classify` sees a send at the top
    // (a `Term`, not a `Separation`), so the term arm fires and descends into
    // the payload par. The host answered `Some(true)` where the machine answers
    // false — a live violation of property (1).
    (r#"@"a"!({1 | 2})"#, r#"@"a"!({1})"#, false),
    (r#"@"a"!({1 | 2 | 3})"#, r#"@"a"!({1 | 2})"#, false),
    // The satisfied companion, so the guard is not merely "reject everything".
    (r#"@"a"!({1 | 2})"#, r#"@"a"!({1 | 2})"#, true),
];

// ══════════════════════════════════════════════════════════════════════════════
// (1) AGREEMENT
// ══════════════════════════════════════════════════════════════════════════════

#[tokio::test]
async fn wherever_the_host_decides_the_machine_agrees() {
    let mut decided = 0usize;
    let mut declined = 0usize;
    for (target, formula, _expected) in MATRIX {
        let host = host_verdict(target, formula);
        let machine = machine_verdict(target, formula).await;
        match host {
            Some(verdict) => {
                assert_eq!(
                    verdict, machine,
                    "HOST/MACHINE DISAGREEMENT on `{target} matches {formula}`: \
                     host says {verdict}, the reducer says {machine}"
                );
                decided += 1;
            },
            None => declined += 1,
        }
    }
    // The agreement property is vacuous if the host decides nothing, and it tests
    // nothing about the escape hatch if the host decides everything, so BOTH sides
    // of the split are required to be non-trivial. The bounds are deliberately
    // loose — the exact split is a consequence of the positive-only term arm and
    // will move as rows are added — but they cannot both be satisfied by a
    // degenerate `host_matches_verdict`.
    assert!(
        decided * 3 >= MATRIX.len(),
        "at least a third of the matrix must be DECIDED host-side, got {decided}/{}",
        MATRIX.len()
    );
    assert!(
        declined >= 5,
        "the matrix must exercise the DECLINED fragment too, got {declined}"
    );
}

// ══════════════════════════════════════════════════════════════════════════════
// (2) GROUNDING
// ══════════════════════════════════════════════════════════════════════════════

#[tokio::test]
async fn the_machine_decides_every_row_as_specified() {
    // Independent of the host entirely. This is what stops (1) from being
    // satisfiable by a machine that answers `false` everywhere, and it is where
    // the SEMANTICS of the spatial fragment is actually pinned.
    for (target, formula, expected) in MATRIX {
        assert_eq!(
            machine_verdict(target, formula).await,
            *expected,
            "the reducer must decide `{target} matches {formula}` = {expected}"
        );
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// (3) SOUNDNESS of the positive-only term arm
// ══════════════════════════════════════════════════════════════════════════════

#[test]
fn the_term_arm_never_reports_a_negative_verdict() {
    // A host non-match proves nothing about the reducer, so it must be reported as
    // `None`, never as `Some(false)`. A formula whose value is settled statically
    // is exempt: that verdict comes from `is_statically_false`, not from the
    // matcher, and is sound on its own.
    for (target, formula, _expected) in MATRIX {
        let formula_proc = parse(formula);
        if !matches!(classify(&formula_proc), FormulaShape::Term)
            || is_statically_false(&formula_proc)
        {
            continue;
        }
        assert_ne!(
            host_verdict(target, formula),
            Some(false),
            "`{target} matches {formula}`: a term-pattern NON-match must be `None`, \
             never `Some(false)`"
        );
    }
}

#[test]
fn the_separating_fragment_is_never_decided_by_the_matcher() {
    // The host owns no AC-with-remainder matcher and must never appear to. The
    // only separating formulas it may answer are the ones whose value is forced
    // syntactically (`false and PPar(…)`, `true or PPar(…)`), where no matching
    // happens at all.
    for (target, formula, _expected) in MATRIX {
        let formula_proc = parse(formula);
        if is_statically_false(&formula_proc) || is_statically_true(&formula_proc) {
            continue;
        }
        if mentions_separation(&formula_proc) {
            assert_eq!(
                host_verdict(target, formula),
                None,
                "`{target} matches {formula}` contains a separating conjunction, so the host \
                 must defer it to the machine"
            );
        }
    }
}

/// Does `formula` contain a separating conjunction anywhere? Derived from the
/// shared classification rather than from the source text, so a new spelling of
/// the connective is covered automatically.
fn mentions_separation(formula: &Proc) -> bool {
    match classify(formula) {
        FormulaShape::Separation(_) => true,
        FormulaShape::Conjunction(left, right)
        | FormulaShape::Disjunction(left, right)
        | FormulaShape::Implication(left, right) => {
            mentions_separation(left) || mentions_separation(right)
        },
        FormulaShape::Negation(inner) => mentions_separation(inner),
        FormulaShape::Verum | FormulaShape::Falsum | FormulaShape::Term => false,
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// The statically-false fold is observationally invisible
// ══════════════════════════════════════════════════════════════════════════════

#[tokio::test]
async fn the_host_and_the_machine_agree_on_the_statically_false_fold() {
    // The lowering folds a statically-false formula to `GBool(false)` and never
    // invokes the matcher; the host reaches the same verdict through
    // `formula::is_statically_false`. Both must say `false`, and the datum must
    // rest — i.e. the optimization changes nothing observable.
    for formula in [
        "false",
        "(false and true)",
        "(false or false)",
        "(not true)",
        "(true implies false)",
        "{ false | true }",
    ] {
        let target = r#"@"a"!(1)"#;
        assert_eq!(
            host_verdict(target, formula),
            Some(false),
            "the host must decide {formula:?} statically false"
        );
        assert!(
            !machine_verdict(target, formula).await,
            "the machine must decide {formula:?} false"
        );
    }
}
