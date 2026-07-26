//! Guard-expression lowering: `where`-clauses over BOUND data, and the monadic receive arity.
//!
//! # Why this suite exists
//!
//! Two silent correctness bugs were measured on 2026-07-26 and root-caused here. Both were
//! *silent*: no error, no diagnostic, just a COMM that never happened. `where`-guard failure is
//! structurally undiagnosable at the point of decision, because f1r3node's
//! `matcher/match.rs::guard_passes` deliberately collapses "the guard is false", "the guard is not
//! a boolean" and "the guard failed to evaluate" into ONE guard-fail verdict — a consensus-visible
//! collapse that must not be changed. So a *lowering* defect and a *false guard* are
//! indistinguishable from the outside, and the only defence is a matrix that pins both directions.
//!
//! ## Defect 1 — the projection surface (guards over bound data never fired)
//!
//! `Proc::parse` (= `parse_structured`) starts from `parse_via_wpda(input)`, which is correct, and
//! then — whenever `display(parsed) != input` — REPLACES the returned representative with the
//! reparse of its own DISPLAY, accepting it as soon as the display is a fixpoint. Display
//! stability is not term preservation, and RhoCalc's display is not term-preserving for a
//! projection operand of an arithmetic / relational / boolean operator: such an operand is
//! rendered through a PROJECTION SURFACE (`macros/src/gen/syntax/display.rs`,
//! `find_projection_surface_wrapper`), which for a `Proc` operand elects
//! `POutputNil . q:Proc |- "@" "Nil" "!" "(" q ")"`. Hence
//!
//! ```text
//!   parse_via_wpda("1 + 2") = Add(CastInt 1, CastInt 2)        ← correct
//!   display(that)           = "@Nil!(1) + @Nil!(2)"            ← NOT term-preserving
//!   Proc::parse("1 + 2")    = Add(POutputNil 1, POutputNil 2)  ← two SENDS
//! ```
//!
//! Lowering that faithfully yields `EPlus(Send, Send)`, so:
//!   * arithmetic / relational operators raise `"parallel or non expression found where
//!     expression expected"`;
//!   * boolean connectives raise `"Multiple expressions given."`;
//!   * and — silently — `where x == 42` becomes `EEq(BoundVar 0, Send)`. `EEq` is decided
//!     STRUCTURALLY (`rho-pure-eval::eq_binop` evaluates both sides then compares the `Par`s), so
//!     it answers `false`, while `where x != 43` answers `true` for the same wrong reason. That
//!     asymmetry — `!=` firing while `==` does not — is this suite's sharpest witness.
//!
//! The `rhocalc` binary was the SOLE production caller of `Proc::parse`; every other production
//! caller already used `parse_via_wpda`. This suite exercises the same production entry.
//!
//! ## Defect 2 — the monadic receive arity (`canonicalize_arity_pattern`)
//!
//! A send carries exactly ONE datum and encodes non-scalar arity INTO it as a list
//! (`c!()` → `[]`, `c!(a,b)` → `[a,b]`). The receive side wrapped every MONADIC quoted pattern
//! except `CastList`/`PVar` in a one-element list, so no scalar ground pattern could match a
//! scalar send: `for(@42 <- c)` did not match `c!(42)` but DID match `c!([42])`.
//!
//! # The teeth test
//!
//! A guard that does not fire and a harness that cannot detect firing look identical, so every
//! row publishes the distinctive marker [`FIRED_MARKER`] rather than a value that could collide
//! with a literal appearing in the guard or the datum (a boolean `false` or a numeric `1` both
//! match inside an un-fired residual). [`harness_has_teeth`] proves the detector separates a
//! known firing from a known non-firing before any other row is trusted.
#![cfg(feature = "rhocalc-runtime")]

use mettail_languages::rhocalc::Proc;
use mettail_rholang_runtime::{
    lower_rhocalc_proc_with_options, run_normalized_par_for_oracle_and_read_runtime_values,
    LoweringOptions,
};
use mettail_runtime::{clear_var_cache, RuntimeObservationValue};
use models::rhoapi::Par;

/// The distinctive firing marker. Deliberately not a bare `true` / `1` / `"fired"`: it must not
/// be a substring of any guard, datum, or residual term in this suite.
const FIRED_MARKER: &str = "ZQFIREDZQ";

/// Parse via the PRODUCTION entry — `parse_via_wpda`, never `Proc::parse`. See the module header:
/// `Proc::parse` round-trips through the display and can return a term the input does not denote.
fn parse(source: &str) -> Proc {
    clear_var_cache();
    Proc::parse_via_wpda(source)
        .unwrap_or_else(|err| panic!("rhocalc parse failed for {source:?}: {err:?}"))
}

fn lower_with(source: &str, options: LoweringOptions) -> Par {
    lower_rhocalc_proc_with_options(&parse(source), options)
        .unwrap_or_else(|err| panic!("rhocalc lowering failed for {source:?}: {err:?}"))
}

fn lower(source: &str) -> Par {
    lower_with(source, LoweringOptions::PRODUCTION)
}

/// Run `source` to rest under `options` and return every observation resting on `@"OUT"`.
async fn observations_with(
    source: &str,
    options: LoweringOptions,
) -> Vec<RuntimeObservationValue> {
    let par = lower_with(source, options);
    run_normalized_par_for_oracle_and_read_runtime_values(&par, "OUT")
        .await
        .unwrap_or_else(|err| panic!("reduction failed for {source:?}: {err}"))
}

/// Run `source` to rest under production options.
async fn observations(source: &str) -> Vec<RuntimeObservationValue> {
    observations_with(source, LoweringOptions::PRODUCTION).await
}

/// Did the guarded body fire under `options`? True iff the marker is resting on `@"OUT"`.
async fn fired_with(source: &str, options: LoweringOptions) -> bool {
    observations_with(source, options)
        .await
        .iter()
        .any(|value| matches!(value, RuntimeObservationValue::Text(text) if text == FIRED_MARKER))
}

/// Did the guarded body fire under production options?
async fn fired(source: &str) -> bool {
    fired_with(source, LoweringOptions::PRODUCTION).await
}

/// ★ Every guard row is checked under BOTH switch positions of S-D0 compile-time guard discharge.
///
/// Under `PRODUCTION` a guard the host can decide statically is DISCHARGED — the condition is
/// simply not populated, and `check_commit` short-circuits `None` to `true`. That is correct, but
/// it means a ground guard like `true and true` would be answered by the HOST fold and never
/// reach the machine at all, so a `PRODUCTION`-only matrix could not distinguish "the machine
/// evaluates this correctly" from "the host folded it away". Under `NO_DISCHARGE` every guard is
/// emitted verbatim and decided by the machine (`rho_pure_eval` under the reducer's own
/// `SpatialMatcherOracle`, via `matcher/match.rs::guard_passes`). Both must agree — which is also
/// the anti-divergence property S-D0's fence exists to protect.
async fn fired_under_both_discharge_settings(source: &str) -> (bool, bool) {
    let production = fired_with(source, LoweringOptions::PRODUCTION).await;
    let verbatim = fired_with(source, LoweringOptions::NO_DISCHARGE).await;
    assert_eq!(
        production, verbatim,
        "compile-time guard discharge changed the verdict — the host and machine guard \
         evaluators DIVERGE on this guard\n{source}"
    );
    (production, verbatim)
}

/// A single-bind guarded receive whose datum is present and whose guard is the parameter.
fn guarded(guard: &str, datum: &str) -> String {
    format!(
        r#"{{ for(@x <- @"c" where {guard}) {{ @"OUT"!("{FIRED_MARKER}") }} | @"c"!({datum}) }}"#
    )
}

/// A monadic receive with a ground quoted pattern, and a send of `datum`.
fn monadic(pattern: &str, datum: &str) -> String {
    format!(
        r#"{{ for(@{pattern} <- @"c") {{ @"OUT"!("{FIRED_MARKER}") }} | @"c"!({datum}) }}"#
    )
}

// ══════════════════════════════════════════════════════════════════════════════════════════════
//  0 — THE TEETH TEST. Nothing below may be believed until this passes.
// ══════════════════════════════════════════════════════════════════════════════════════════════

/// The detector must separate a KNOWN firing from a KNOWN non-firing. Without this, every
/// "does not fire" assertion below would also be satisfied by a harness that can never observe a
/// firing at all.
#[tokio::test]
async fn harness_has_teeth() {
    assert!(
        fired(&guarded("true", "42")).await,
        "the harness cannot observe a firing at all: `where true` must publish the marker"
    );
    assert!(
        !fired(&guarded("false", "42")).await,
        "the harness reports a firing that did not happen: `where false` must publish nothing"
    );
}

// ══════════════════════════════════════════════════════════════════════════════════════════════
//  1 — THE GUARD MATRIX. Every row: the datum is present and the guard is semantically TRUE,
//      so the ONLY correct verdict is FIRE. Rows marked ⚠ did not fire before the fix.
// ══════════════════════════════════════════════════════════════════════════════════════════════

#[tokio::test]
async fn guards_that_mention_no_bound_variable_fire() {
    for (guard, datum) in [
        ("true", "42"),
        ("1 == 1", "42"),
        ("42 == 42", "42"),
        ("1 < 46", "42"),            // ⚠ ELt over two projection-surface operands
        ("true and true", "42"),     // ⚠ EAnd  "
        ("true or false", "42"),     // ⚠ EOr   "
        ("not false", "42"),         // ⚠ ENot  "
        ("not (not true)", "42"),    // ⚠ nested ENot
        ("1 + 1 == 2", "42"),        // ⚠ EPlus under EEq
    ] {
        let source = guarded(guard, datum);
        let (production, _) = fired_under_both_discharge_settings(&source).await;
        assert!(production, "`where {guard}` is TRUE and must fire\n{source}");
    }
}

#[tokio::test]
async fn guards_over_bound_data_fire() {
    for (guard, datum) in [
        ("x", "true"),
        ("not x", "false"),
        ("x == x", "42"),
        ("x == 42", "42"),        // ⚠ THE headline row: EEq(BoundVar, GInt) — structural equality
        ("x == \"a\"", "\"a\""),  // ⚠ the same over GString
        ("x == true", "true"),    // ⚠ the same over GBool
        ("x != 43", "42"),        // fired BEFORE the fix too — for the WRONG reason (see header)
        ("x < 46", "42"),         // ⚠ ELt with one bound operand
        ("x > 0", "7"),           // ⚠ EGt   "
        ("x <= 42", "42"),        // ⚠ ELte  "
        ("x >= 42", "42"),        // ⚠ EGte  "
        ("x + 1 > 0", "7"),       // ⚠ arithmetic under a relation
        ("x - 1 == 6", "7"),      // ⚠ EMinus
        ("x * 2 == 14", "7"),     // ⚠ EMult
        ("x or false", "true"),   // ⚠ EOr with one bound operand
        ("x and true", "true"),   // ⚠ EAnd  "
        ("x matches 42", "42"),   // ⚠ EMatches against a projection-surface pattern
    ] {
        let source = guarded(guard, datum);
        let (production, _) = fired_under_both_discharge_settings(&source).await;
        assert!(
            production,
            "`where {guard}` with datum {datum} is TRUE and must fire\n{source}"
        );
    }
}

// ══════════════════════════════════════════════════════════════════════════════════════════════
//  2 — THE CONTROLS. Every row: the guard is semantically FALSE, so the only correct verdict is
//      DO NOT FIRE. Without these the matrix above would be satisfied by "always commit".
// ══════════════════════════════════════════════════════════════════════════════════════════════

#[tokio::test]
async fn false_guards_do_not_fire() {
    for (guard, datum) in [
        ("false", "42"),
        ("1 == 2", "42"),
        ("1 > 46", "42"),
        ("true and false", "42"),
        ("false or false", "42"),
        ("not true", "42"),
        ("x == 99", "42"),
        ("x != 42", "42"),
        ("x > 100", "42"),
        ("x < 0", "42"),
        ("x and false", "true"),
        ("x matches 99", "42"),
        ("not x", "true"),
    ] {
        let source = guarded(guard, datum);
        let (production, _) = fired_under_both_discharge_settings(&source).await;
        assert!(
            !production,
            "`where {guard}` with datum {datum} is FALSE and must NOT fire\n{source}"
        );
    }
}

/// A guard-failing datum is not consumed: it must still be resting afterwards. This separates
/// "the guard refused" from "the COMM committed but the body produced nothing".
#[tokio::test]
async fn a_refused_guard_leaves_its_datum_resting() {
    let source = guarded("x == 99", "42");
    let par = lower(&source);
    let resting = run_normalized_par_for_oracle_and_read_runtime_values(&par, "c")
        .await
        .expect("the guarded program must reduce");
    assert_eq!(
        resting,
        vec![RuntimeObservationValue::Int(42)],
        "a refused guard must leave the rejected datum available\n{source}"
    );
}

// ══════════════════════════════════════════════════════════════════════════════════════════════
//  3 — THE DIAGNOSTIC ROWS. The same operators in SEND position. These share the root with the
//      guard rows (an operand that is a PROCESS rather than an expression), and they fail LOUDLY
//      rather than silently, which is what made the root findable.
// ══════════════════════════════════════════════════════════════════════════════════════════════

#[tokio::test]
async fn operators_in_send_position_evaluate_on_the_reducer() {
    use RuntimeObservationValue::{Bool, Int};
    for (payload, expected) in [
        ("1", Int(1)),
        ("1 + 2", Int(3)),          // ⚠ was ReduceError "parallel or non expression found …"
        ("7 - 2", Int(5)),          // ⚠
        ("3 * 4", Int(12)),         // ⚠
        ("1 < 46", Bool(true)),     // ⚠ was ReduceError "parallel or non expression found …"
        ("46 < 1", Bool(false)),    // ⚠
        ("1 == 1", Bool(true)),     //   passed before — EEq compared two IDENTICAL wrong operands
        ("1 == 2", Bool(false)),    //   ditto
        ("true and true", Bool(true)),  // ⚠ was ReduceError "Multiple expressions given."
        ("true or false", Bool(true)),  // ⚠
        ("not false", Bool(true)),      // ⚠
        ("not true", Bool(false)),      // ⚠
    ] {
        let source = format!(r#"{{ @"OUT"!({payload}) }}"#);
        assert_eq!(
            observations(&source).await,
            vec![expected.clone()],
            "`@\"OUT\"!({payload})` must evaluate to {expected:?} on the reducer\n{source}"
        );
    }
}

// ══════════════════════════════════════════════════════════════════════════════════════════════
//  4 — THE MONADIC RECEIVE ARITY (defect 2). A scalar send carries its payload as its ONE datum,
//      so a scalar ground pattern must match it VERBATIM — and must NOT match a one-element list.
// ══════════════════════════════════════════════════════════════════════════════════════════════

/// Every scalar ground pattern shape the RhoCalc grammar admits. Before the fix ONLY the two
/// exempted shapes (`CastList`, `PVar`) matched a scalar send; every other shape here silently
/// never committed.
#[tokio::test]
async fn a_scalar_ground_pattern_matches_a_scalar_send() {
    for subject in [
        "42",          // ⚠ CastInt
        "\"hi\"",      // ⚠ CastStr
        "true",        // ⚠ CastBool
        "{1:2}",       // ⚠ CastMap
        "Set(1,2)",    // ⚠ CastSet
        "#{1|2}#",     // ⚠ CastBag
        "[1,2]",       //   CastList — matched before the fix (the exemption)
    ] {
        let source = monadic(subject, subject);
        assert!(
            fired(&source).await,
            "`for(@{subject} <- c)` must match `c!({subject})`\n{source}"
        );
    }
}

/// The dual: a scalar pattern must NOT match a ONE-ELEMENT-LIST send. Before the fix this was
/// exactly backwards — `for(@42 <- c)` matched `c!([42])` and not `c!(42)` — so asserting only
/// the positive direction would not detect a regression back to the wrapping behaviour.
#[tokio::test]
async fn a_scalar_ground_pattern_does_not_match_a_listed_send() {
    for (pattern, listed) in
        [("42", "[42]"), ("\"hi\"", "[\"hi\"]"), ("true", "[true]"), ("{1:2}", "[{1:2}]")]
    {
        let source = monadic(pattern, listed);
        assert!(
            !fired(&source).await,
            "`for(@{pattern} <- c)` must NOT match `c!({listed})`\n{source}"
        );
    }
}

/// ══ ⚠ CHARACTERIZATION TEST — the BEHAVIOURAL face of an OPEN divergence from consensus
///    Rholang. The ARTIFACT-level matrix that actually governs it lives in
///    `rhocalc_ground_literal_conformance.rs`; this test is retained because it is the row where
///    the divergence is directly observable as a COMM that does not happen. ═══════════════════
///
/// A sign-abutted numeral lowers to an unevaluated `ENeg` (`rhocalc_ast.rs::lower_int_value`
/// carries the full argument). Send data are evaluated before they are stored; patterns are not.
/// So `@"c"!(-7)` stores `GInt(-7)` while `for(@-7 <- @"c")` matches against `ENeg(GInt(7))`, and
/// no COMM occurs. Consensus Rholang DOES commit it — measured against f1r3node's own normalizer
/// and reducer, `for (@-7 <- @"c") { @"OUT"!(1) } | @"c"!(-7)` leaves `1` on `@"OUT"`.
///
/// ★ MECHANISM, CORRECTED 2026-07-26. f1r3node folds nothing: its LEXER puts the sign inside the
/// numeric literal token (`long_literal /-?\d+/` and siblings), so no negation node is ever built
/// for an abutted numeral. The discriminator is ADJACENCY — `- 7` and `-(7)` build a real `ENeg`
/// on both sides and already conform. The fix is therefore a FRONT-END fix, in two parts, and
/// **not** a fold in `lower_int_value`: by lowering time `-7`, `- 7` and `-(7)` are the same term,
/// so folding there would break the spellings that conform today. The full derivation, the two
/// refuted grounds for declining it, and the two fix sites are recorded above `lower_int_value`.
///
/// ★ WHEN THIS TEST FAILS, the divergence has been FIXED. Move `-7` into
/// [`a_scalar_ground_pattern_matches_a_scalar_send`], delete this characterization test, and
/// update `rhocalc_ground_literal_conformance.rs` (whose per-row pins are the authority) together
/// with the ⚠ note in `lower_int_value`.
///
/// ⚠ Do NOT weaken this to "some negative literal does not match": the `-7n`/`-1.5f64`/`-1.5p2`
/// spellings DO commit today, for the wrong reason (both sides carry the same *unevaluated*
/// `ENeg`, so they are structurally equal while both differ from f1r3node's artifact). Only the
/// artifact matrix distinguishes that false pass; see
/// `rhocalc_ground_literal_conformance.rs::false_agreement_is_not_conformance`.
#[tokio::test]
async fn negative_literal_patterns_are_an_open_divergence() {
    let source = monadic("-7", "-7");
    assert!(
        !fired(&source).await,
        "`for(@-7 <- c)` now matches `c!(-7)` — the sign-abutted numeric-literal divergence \
         recorded above `lower_int_value` has been FIXED. Move `-7` into \
         `a_scalar_ground_pattern_matches_a_scalar_send`, delete this characterization test, and \
         update `rhocalc_ground_literal_conformance.rs` + the divergence note in \
         `lower_int_value`.\n{source}"
    );

    // The POSITIVE twin commits, which is what isolates the defect to the sign rather than to the
    // arity fix or to anything else in this file.
    let positive = monadic("7", "7");
    assert!(fired(&positive).await, "`for(@7 <- c)` must match `c!(7)`\n{positive}");

    // The NON-ABUTTED twin behaves identically in MeTTaIL and in f1r3node (both build a real
    // `ENeg` pattern against an evaluated `GInt(-7)` datum, so neither commits). Pinned here so a
    // fold applied at the wrong layer — which would make this row start firing — is caught by the
    // behavioural suite too, not only by the artifact matrix.
    let spaced = monadic("- 7", "- 7");
    assert!(
        !fired(&spaced).await,
        "`for(@- 7 <- c)` now matches `c!(- 7)`. f1r3node does NOT commit that COMM: with the \
         sign detached, its pattern is a real `ENeg` and its datum evaluates to `GInt(-7)`. This \
         is the signature of a fold applied AFTER parsing, where adjacency is no longer \
         observable — move the fix into the lexer/parser.\n{spaced}"
    );
}

/// A binder pattern still matches any single datum (the shape whose breakage would have been
/// obvious, and therefore the one the old exemption list protected).
#[tokio::test]
async fn a_binder_pattern_matches_any_scalar_send() {
    for datum in ["42", "\"hi\"", "true", "[1,2]", "{1:2}"] {
        let source = monadic("y", datum);
        assert!(fired(&source).await, "`for(@y <- c)` must match `c!({datum})`\n{source}");
    }
}

/// The non-monadic arities are unchanged: they really are list-encoded on BOTH sides. This pins
/// the send/receive arity table in [`canonicalize_arity_pattern`]'s doc comment end-to-end, so
/// the monadic fix cannot be "generalized" into the empty/polyadic forms.
#[tokio::test]
async fn empty_and_polyadic_arities_still_agree() {
    let empty = format!(r#"{{ for(<- @"c") {{ @"OUT"!("{FIRED_MARKER}") }} | @"c"!() }}"#);
    assert!(fired(&empty).await, "`for(<- c)` must match `c!()`\n{empty}");

    let polyadic = format!(
        r#"{{ for(@a, @b <- @"c") {{ @"OUT"!("{FIRED_MARKER}") }} | @"c"!(1, 2) }}"#
    );
    assert!(fired(&polyadic).await, "`for(@a, @b <- c)` must match `c!(1, 2)`\n{polyadic}");
}

// ══════════════════════════════════════════════════════════════════════════════════════════════
//  5 — THE LOWERING ARTIFACT, pinned structurally. The behavioural rows above prove the fix
//      end-to-end; these prove the SHAPE, so a regression is localized instead of merely observed.
// ══════════════════════════════════════════════════════════════════════════════════════════════

/// A guard operand that is a literal must lower to a ground `Expr`, never to a `Send`. This is
/// the projection-surface artifact stated as a structural invariant: no `Par` reachable inside a
/// `Receive.condition` may carry process structure.
///
/// ⚠ Lowered under `NO_DISCHARGE` deliberately. Under `PRODUCTION`, S-D0 discharges any guard the
/// host can decide statically by NOT populating `Receive.condition` at all — so `where true and
/// true` has no condition to inspect and the strongest rows would vacuously pass. `NO_DISCHARGE`
/// emits every guard verbatim, which is exactly the artifact this invariant is about.
#[tokio::test]
async fn a_guard_condition_carries_no_process_structure() {
    fn assert_expression_only(par: &Par, source: &str, path: &str) {
        assert!(
            par.sends.is_empty()
                && par.receives.is_empty()
                && par.news.is_empty()
                && par.matches.is_empty()
                && par.bundles.is_empty()
                && par.unforgeables.is_empty(),
            "guard operand at {path} carries PROCESS structure — the projection-surface \
             artifact is back\nsource: {source}\npar: {par:?}"
        );
        for expr in &par.exprs {
            for (index, child) in operand_pars(expr).into_iter().enumerate() {
                assert_expression_only(&child, source, &format!("{path}.{index}"));
            }
        }
    }

    /// The operand `Par`s of one expression, for every `Expr` shape a guard can contain.
    fn operand_pars(expr: &models::rhoapi::Expr) -> Vec<Par> {
        use models::rhoapi::expr::ExprInstance::*;
        let Some(instance) = expr.expr_instance.as_ref() else {
            return Vec::new();
        };
        // Two operands for every binary form, one for the unary forms, none for grounds. The
        // `EMatches` PATTERN is deliberately excluded: a pattern legitimately carries connectives
        // and is never evaluated as an expression.
        match instance {
            EPlusBody(e) => vec![e.p1.clone(), e.p2.clone()],
            EMinusBody(e) => vec![e.p1.clone(), e.p2.clone()],
            EMultBody(e) => vec![e.p1.clone(), e.p2.clone()],
            EDivBody(e) => vec![e.p1.clone(), e.p2.clone()],
            EModBody(e) => vec![e.p1.clone(), e.p2.clone()],
            ELtBody(e) => vec![e.p1.clone(), e.p2.clone()],
            ELteBody(e) => vec![e.p1.clone(), e.p2.clone()],
            EGtBody(e) => vec![e.p1.clone(), e.p2.clone()],
            EGteBody(e) => vec![e.p1.clone(), e.p2.clone()],
            EEqBody(e) => vec![e.p1.clone(), e.p2.clone()],
            ENeqBody(e) => vec![e.p1.clone(), e.p2.clone()],
            EAndBody(e) => vec![e.p1.clone(), e.p2.clone()],
            EOrBody(e) => vec![e.p1.clone(), e.p2.clone()],
            ENotBody(e) => vec![e.p.clone()],
            ENegBody(e) => vec![e.p.clone()],
            EMatchesBody(e) => vec![e.target.clone()],
            _ => Vec::new(),
        }
        .into_iter()
        .flatten()
        .collect()
    }

    for (guard, datum) in [
        ("x == 42", "42"),
        ("x < 46", "42"),
        ("x + 1 > 0", "7"),
        ("true and true", "42"),
        ("not false", "42"),
        ("1 < 46", "42"),
        ("x matches 42", "42"),
    ] {
        let source = guarded(guard, datum);
        let par = lower_with(&source, LoweringOptions::NO_DISCHARGE);
        let receive = par.receives.first().expect("the program contains one receive");
        let condition = receive.condition.as_ref().unwrap_or_else(|| {
            panic!(
                "`where {guard}` must lower to a populated Receive.condition under \
                 NO_DISCHARGE\n{source}"
            )
        });
        assert_expression_only(condition, &source, "condition");
    }
}

/// A monadic ground pattern lowers to the payload pattern VERBATIM — not to a one-element
/// `EList`. The structural twin of [`a_scalar_ground_pattern_matches_a_scalar_send`].
#[tokio::test]
async fn a_monadic_ground_pattern_lowers_verbatim() {
    use models::rhoapi::expr::ExprInstance;

    for (pattern, expected) in [
        ("42", ExprInstance::GInt(42)),
        ("true", ExprInstance::GBool(true)),
        ("\"hi\"", ExprInstance::GString("hi".to_string())),
    ] {
        let source = format!(r#"{{ for(@{pattern} <- @"c") {{ @"OUT"!("Z") }} }}"#);
        let par = lower(&source);
        let receive = par.receives.first().expect("the program contains one receive");
        let bind = receive.binds.first().expect("the receive has one bind");
        let [only_pattern] = bind.patterns.as_slice() else {
            panic!("a monadic bind must carry exactly ONE pattern\n{source}");
        };
        assert_eq!(
            only_pattern.exprs.first().and_then(|e| e.expr_instance.clone()),
            Some(expected.clone()),
            "`for(@{pattern} <- c)` must lower its pattern VERBATIM, not wrapped in a list\n\
             source: {source}\npattern: {only_pattern:?}"
        );
    }
}
