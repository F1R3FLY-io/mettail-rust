//! Stage 3d end-to-end: a GENERATED language's Ambient-calculus `OpenRule` fires end-to-end as ONE
//! atomic COMM on the live f1r3node Rholang interpreter — the FIRST STRUCTURAL non-linear AC firing.
//!
//! `AmbDemo` is a generated `language!` whose only rewrite is the Ambient open rule
//!
//!     OpenRule . |- (PPar {(POpen N P), (PAmb N Q), ...rest}) ~> (PPar {P, Q, ...rest})
//!
//! i.e. `open(n, P) | n[Q]  ~>  P | Q`, spliced into the residual bag. It is the STRUCTURAL twin of
//! the RhoCalc `Comm` rule (`rho_net_comm_firing`): the SAME non-linear AC firing shape MINUS the
//! substitution. It composes, in ONE COMM on the reducer:
//!
//!   * a HashBag AC match over `PPar` with k=2 STRUCTURED fixed elements (the capability `POpen N P`
//!     = `open(n, P)` and the ambient `PAmb N Q` = `n[Q]`) + `...rest` — the order-independent
//!     process-soup carrier, tag-routed element patterns;
//!   * a NON-LINEAR consistency guard: the ambient name `N` occurs in BOTH structured elements, so
//!     each occurrence binds a DISTINCT σ slot, and the installed receiver's `Receive.condition`
//!     `EEq(N_open, N_amb)` — the `where`-clause the reducer commits the COMM under only when it
//!     evaluates to `GBool(true)` — enforces `N ≡ N`, reject-safe;
//!   * a PURE STRUCTURAL reduct: UNLIKE `Comm` (whose reduct is the host-computed substitution
//!     `cont[Q/y]`, delivered as the firing's contractum), `OpenRule` unwraps `P` from `open(n, P)`
//!     and `Q` from `n[Q]` and splices `{P, Q, ...rest}`. Both `P` and `Q` are LHS-element
//!     arguments, so the firing's σ already carries them; the σ-injection recovers them DIRECTLY
//!     from σ (no host computation, no contractum), and the receiver body emits the bag RHS
//!     `@"ac:PPar"!(P) | @"ac:PPar"!(Q) | rest`.
//!
//! ## Firing drive (AUTOMATED — the same pipeline as every other Stage)
//!
//! Like base/AC/AC2b/contextual/binder/native/Comm, the OpenRule drives its injection from
//! `dovetail_report_for → rho_net_invocation_from_dovetail_to`. The three seams the Comm campaign
//! closed apply verbatim (A-1: AC metapatterns lower on the typed fold path; A-2: a non-linear AC
//! NATIVE rule records a `rewrite_justification`, the two `N` occurrences hashcons to one e-class),
//! plus Stage 3d's structural piece: `is_structural_ac_rewrite` routes the OpenRule onto the typed
//! native lane; its dispatch does NO substitution — it splices `op{ σ[P], σ[Q], ...rest }` directly
//! from the AC-matched σ, so `dovetail_report_for` PRODUCES the OpenRule justification (σ carries the
//! whole operand bag AND the two reduct elements P, Q, since each is an LHS-element arg). The
//! generated structural-AC σ-injection F-function reconstructs the operand bag from σ and recovers
//! the reducts `P`/`Q` DIRECTLY from σ, and assembles `structural_ac_contract_call(⟦bag⟧, [⟦P⟧, ⟦Q⟧],
//! @out)` — the installed `RhoNetLoweredRule::StructuralAcRewrite` receiver, the COMM real on the
//! live reducer, the non-linear `Receive.condition` the belt-and-suspenders gate.
//!
//! Scoped to `OpenRule`: the full `Ambient`'s `InRule`/`OutRule` are DEEP nested-ambient AC
//! reductions (a nested `PAmb` carrying a nested `PPar`), which stay `Unsupported` (fail-closed) on
//! the Rho backend — this demo proves the CLEAN OpenRule half fires end-to-end.
#![cfg(feature = "amb-demo-runtime")]

use mettail_languages::ambdemo::AmbDemoLanguage;
use mettail_rholang_codegen::{
    lower_language_def, plan_rho_default_backend, reconstruct_language_def,
    rho_net_structural_ac_injection_sites, suggest_rejected_rule_dispositions, RhoCoverageEvidence,
    RhoDefaultBackendRequirements, RhoGuardCoverageEvidence,
};
use mettail_rholang_runtime::PlannedRhoBackend;
use mettail_runtime::{Language, RuntimeObservationValue, RuntimeReflectedSubterm};

/// Reconstruct AmbDemo's augmented `LanguageDef`, plan its Rho-default backend (the `OpenRule`
/// structural non-linear AC σ-receiver installs alongside the structural constructors), and return
/// the planned backend, its definition fingerprint, and the OpenRule receiver's SOURCE channel.
fn amb_demo_backend() -> (PlannedRhoBackend, String, String) {
    let source = AmbDemoLanguage
        .metadata()
        .definition_source()
        .expect("generated AmbDemoLanguage must expose its definition_source");
    let def = reconstruct_language_def(source)
        .expect("AmbDemoLanguage definition_source must reconstruct as a LanguageDef");

    // The OpenRule receiver's source channel (the channel the structural-AC injection targets).
    let sites = rho_net_structural_ac_injection_sites(&def);
    assert_eq!(sites.len(), 1, "AmbDemo has exactly one structural AC rewrite");
    let channel = sites[0].channel.clone();
    assert_eq!(sites[0].rule_label, "OpenRule");
    assert_eq!(sites[0].op, "PPar");
    assert_eq!(sites[0].nonlinear_var, "N");
    assert_eq!(sites[0].reduct_vars, vec!["P".to_string(), "Q".to_string()]);

    let lowering = lower_language_def(&def);
    let requirements = RhoDefaultBackendRequirements {
        coverage: RhoCoverageEvidence::CoveredRejectedRules(suggest_rejected_rule_dispositions(
            &def, &lowering,
        )),
        guard_coverage: RhoGuardCoverageEvidence::NoGuardObligations,
    };
    let plan = plan_rho_default_backend(&def, requirements)
        .expect("AmbDemo (structural non-linear AC OpenRule) must flip to the Rho backend");
    let fingerprint = plan.definition_fingerprint().to_string();
    (PlannedRhoBackend::from_plan(plan), fingerprint, channel)
}

/// A nullary process observation value (e.g. the unwrapped `PA` = `A`).
fn proc_leaf(constructor: &str) -> RuntimeObservationValue {
    RuntimeObservationValue::Term { constructor: constructor.to_string(), children: Vec::new() }
}

/// Assert `value` is a bag whose multiset of elements is exactly `expected` (each multiplicity 1).
fn assert_bag_is(value: &RuntimeObservationValue, expected: &[RuntimeObservationValue]) {
    let RuntimeObservationValue::Bag(entries) = value else {
        panic!("OUT must be a bag (the restructured result), got {value:?}");
    };
    let total: usize = entries.iter().map(|(_, count)| *count).sum();
    assert_eq!(total, expected.len(), "the restructured bag has {} elements, got {value:?}", expected.len());
    for element in expected {
        assert!(
            entries.iter().any(|(observed, count)| observed == element && *count == 1),
            "the restructured bag must contain {element:?} (multiplicity 1), got {value:?}"
        );
    }
}

/// (Stage 3d GATE) `dovetail_report_for(AmbDemo subject)` PRODUCES the OpenRule justification — the
/// AUTOMATED Dovetail pipeline drives the Ambient `OpenRule` on the typed native lane.
///
/// The redex `{ open(na, A) | na[B] }` (both names `na`) reduces on the typed native lane: the
/// structural-AC native rule AC-matches the non-linear soup (`N ≡ N` by e-class equality), and the
/// dispatch splices `op{ σ[P], σ[Q], ...rest } = { A, B }` DIRECTLY from σ (no substitution). The sole
/// `rewrite_justifications` entry is the `OpenRule` firing whose σ reconstructs the operand bag — it
/// binds the ambient name `N = na`, the two unwrapped processes `P = a` and `Q = b`, and the residual
/// `rest` (an empty `PPar` bag). This is the report the structural-AC σ-injection reads.
#[test]
fn ambdemo_dovetail_report_produces_the_open_justification() {
    mettail_runtime::clear_var_cache();
    let term = AmbDemoLanguage
        .parse_term("{ open(na, A) | na[B] }")
        .expect("AmbDemo must parse the OpenRule redex");

    let report = AmbDemoLanguage::dovetail_report_for(term.as_ref(), 64, 1_000_000)
        .expect("AmbDemo Dovetail report must compile on the typed native lane");
    assert!(
        report.is_complete(),
        "the acyclic OpenRule reduction must report Complete, got {:?}",
        report.completeness
    );
    assert_eq!(
        report.rewrite_justifications.len(),
        1,
        "exactly one OpenRule firing must be recorded, got {:?}",
        report.rewrite_justifications
    );
    let justification = &report.rewrite_justifications[0];
    assert_eq!(justification.rule_label, "OpenRule", "the fired rule is OpenRule");

    // σ reconstructs the operand bag: N (ambient name), P + Q (the unwrapped processes), rest.
    let sigma = |name: &str| {
        justification
            .sigma
            .iter()
            .find(|(n, _)| n == name)
            .map(|(_, subterm)| subterm)
            .unwrap_or_else(|| panic!("σ must bind {name}, got {:?}", justification.sigma))
    };
    assert_eq!(sigma("N").constructor, "Na", "the non-linear ambient name N is `na`");
    assert_eq!(sigma("P").constructor, "PA", "the unwrapped open-body P is `A`");
    assert_eq!(sigma("Q").constructor, "PB", "the unwrapped ambient-body Q is `B`");
    assert_eq!(sigma("rest").constructor, "PPar", "rest is the residual PPar bag");
    assert!(sigma("rest").children.is_empty(), "the residual bag is empty here");
}

/// POSITIVE (empty rest): `{ open(na, A) | na[B] }` — both names `na` — fires as ONE COMM, landing
/// `{ A | B }` (= `P | Q`) on OUT. The non-linear `Receive.condition` holds.
#[tokio::test]
async fn ambdemo_open_fires_as_a_comm_on_the_reducer() {
    mettail_runtime::clear_var_cache();
    let (backend, fingerprint, _channel) = amb_demo_backend();

    // Fingerprint coherence: the installed OpenRule σ-receiver (from the reconstructed def) and the
    // structural-AC σ-injection (which reflects the reconstructed bag + reducts with
    // `metadata().definition_fingerprint()`) must agree, or the soup would decode inconsistently.
    assert_eq!(
        AmbDemoLanguage.metadata().definition_fingerprint(),
        Some(fingerprint.as_str()),
        "planned backend fingerprint must equal the generated metadata fingerprint"
    );

    // (1) AUTOMATED Dovetail report. The redex `{ open(na, A) | na[B] }` (both names `na`) reduces on
    // the typed native lane; the sole firing is the `OpenRule` firing.
    let term = AmbDemoLanguage
        .parse_term("{ open(na, A) | na[B] }")
        .expect("AmbDemo must parse the OpenRule redex");
    let report = AmbDemoLanguage::dovetail_report_for(term.as_ref(), 64, 1_000_000)
        .expect("AmbDemo Dovetail report must compile");

    // (2) The generated structural-AC σ-injection F-function reconstructs the operand bag from σ and
    // the two reduct elements `P`/`Q` DIRECTLY from σ, and assembles the `structural_ac_contract_call`.
    let invocation =
        AmbDemoLanguage::rho_net_invocation_from_dovetail_to(term.as_ref(), &report, "OUT")
            .expect("the structural-AC σ-injection must assemble from a complete report");
    assert_eq!(invocation.out_channel, "OUT");

    // (3) RHO-MACHINE EXECUTION: run the installed OpenRule σ-receiver ∥ call and observe OUT.
    let observation = backend
        .run_rho_net_with_call_and_observe_runtime_values(&invocation.call, &invocation.out_channel)
        .await
        .expect("the structural-AC injection must execute on the Rho runtime");

    assert_eq!(
        observation.observed_count(),
        1,
        "the non-linear OpenRule receiver must fire exactly once (got {:?})",
        observation.values
    );
    assert_bag_is(&observation.values[0], &[proc_leaf("PA"), proc_leaf("PB")]);
}

/// POSITIVE (with rest): `{ open(na, A) | na[B] | 0 }` — the residual `0` (a `PZero`, distinct tag)
/// rides the `rest` remainder and is spliced back, so OUT is `{ A | B | 0 }`.
#[tokio::test]
async fn ambdemo_open_splices_the_residual_bag() {
    mettail_runtime::clear_var_cache();
    let (backend, fingerprint, _channel) = amb_demo_backend();
    assert_eq!(
        AmbDemoLanguage.metadata().definition_fingerprint(),
        Some(fingerprint.as_str()),
        "planned backend fingerprint must equal the generated metadata fingerprint"
    );

    // `{ open(na, A) | na[B] | 0 }` — the residual `0` (a `PZero`) rides the `rest` remainder.
    // AUTOMATED: σ binds `rest = { 0 }`; the F-fn reconstructs the whole operand bag (splicing the
    // `rest` children) and recovers the reducts `A`/`B` DIRECTLY from σ; the receiver splices
    // `a | b | 0`.
    let term = AmbDemoLanguage
        .parse_term("{ open(na, A) | na[B] | 0 }")
        .expect("AmbDemo must parse the with-rest OpenRule redex");
    let report = AmbDemoLanguage::dovetail_report_for(term.as_ref(), 64, 1_000_000)
        .expect("AmbDemo Dovetail report must compile");
    let invocation =
        AmbDemoLanguage::rho_net_invocation_from_dovetail_to(term.as_ref(), &report, "OUT")
            .expect("the structural-AC σ-injection must assemble from a complete report");

    let observation = backend
        .run_rho_net_with_call_and_observe_runtime_values(&invocation.call, &invocation.out_channel)
        .await
        .expect("the structural-AC injection must execute on the Rho runtime");

    assert_eq!(
        observation.observed_count(),
        1,
        "the OpenRule receiver must fire exactly once (got {:?})",
        observation.values
    );
    // The restructured bag = { P, Q, rest } = { A, B, 0 }.
    assert_bag_is(
        &observation.values[0],
        &[proc_leaf("PA"), proc_leaf("PB"), proc_leaf("PZero")],
    );
}

/// NEGATIVE (mismatched names): `{ open(na, A) | nb[B] }` — the open name `na` ≠ the ambient name
/// `nb`. On the AUTOMATED pipeline the NON-LINEAR AC guard VETOES at the Dovetail matcher: the
/// structural-AC native rule finds NO pairing (`N ≡ N` is unsatisfiable — `na` and `nb` are distinct
/// e-classes, so `collect_ac_matches` prunes by evidence), so the report carries NO OpenRule firing
/// and the σ-injection has nothing to inject — nothing lands on OUT. (`open` cannot dissolve a
/// NON-matching ambient — the belt-and-suspenders `Receive.condition` `EEq(N_open, N_amb)` is the
/// same guard, redundant here since the Dovetail matcher already vetoes upstream.)
#[test]
fn ambdemo_mismatched_name_does_not_fire() {
    mettail_runtime::clear_var_cache();

    // POpen on `na`, PAmb on `nb` — ambient names disagree.
    let term = AmbDemoLanguage
        .parse_term("{ open(na, A) | nb[B] }")
        .expect("AmbDemo must parse the mismatched-name soup");
    let report = AmbDemoLanguage::dovetail_report_for(term.as_ref(), 64, 1_000_000)
        .expect("AmbDemo Dovetail report must compile");

    // The reduction is a normal form: the non-linear AC guard vetoed, so NO OpenRule fired.
    assert!(
        report.is_complete(),
        "the mismatched-name soup is a normal form (Complete), got {:?}",
        report.completeness
    );
    assert!(
        report.rewrite_justifications.is_empty(),
        "the non-linear AC guard must VETO the mismatched-name soup — no OpenRule firing (got {:?})",
        report.rewrite_justifications
    );

    // Consequently the structural-AC σ-injection fails closed (no firing to inject).
    assert!(
        AmbDemoLanguage::rho_net_invocation_from_dovetail_to(term.as_ref(), &report, "OUT")
            .is_err(),
        "no OpenRule firing ⇒ the σ-injection has nothing to inject (nothing lands on OUT)"
    );
}

/// #24 default-path (Stage 4 S-binder SLICE 3b) — the DEFAULT `rho_net_match_invocation_from_dovetail_to`
/// (the match-or-replay GATE's MATCH branch) admits the Ambient `OpenRule` and fires it IN RHO via the
/// SPREAD. The direct analogue of the AC / native / contextual default-path proofs: unlike the
/// report-path `rho_net_invocation_from_dovetail_to` (which the other AmbDemo tests drive DIRECTLY,
/// reconstructing the bag + reducts from σ), this STRUCTURALLY reflects the WHOLE subject and re-sources
/// the operand bag from the spread — the structural-AC redex is located by the same descent walk that
/// rides a `^lambda` binder image, and a per-site MATCH receiver binds the k elements + reducts + `rest`
/// from the bag and splices `{P, Q, ...rest}` on `@out` under the `N ≡ N` guard.
#[tokio::test]
async fn ambdemo_open_matches_in_rho_via_the_spread() {
    mettail_runtime::clear_var_cache();
    let (backend, _fingerprint, _channel) = amb_demo_backend();

    let term = AmbDemoLanguage
        .parse_term("{ open(na, A) | na[B] }")
        .expect("AmbDemo must parse the OpenRule redex");
    let report = AmbDemoLanguage::dovetail_report_for(term.as_ref(), 64, 1_000_000)
        .expect("AmbDemo Dovetail report must compile");

    // The MATCH path (NOT the replay branch — the retirement proof for OpenRule): it admits the
    // OpenRule and assembles the in-Rho spread-match call.
    let invocation =
        AmbDemoLanguage::rho_net_match_invocation_from_dovetail_to(term.as_ref(), &report, "OUT")
            .expect("the structural-AC MATCH path admits OpenRule and assembles the spread call");
    assert_eq!(invocation.out_channel, "OUT");

    let observation = backend
        .run_rho_net_with_call_and_observe_runtime_values(&invocation.call, &invocation.out_channel)
        .await
        .expect("the in-Rho structural-AC match + firing executes on the reducer");

    assert_eq!(
        observation.observed_count(),
        1,
        "the OpenRule MATCH receiver fires exactly once (got {:?})",
        observation.values
    );
    assert_bag_is(&observation.values[0], &[proc_leaf("PA"), proc_leaf("PB")]);
}

/// S-AC structural (Stage 4 S-binder SLICE 3b) — the DECISIVE probe that the structural-AC operand
/// BAG AND its reducts are re-sourced from the SPREAD of the reflected subject, NOT the host report σ.
/// The structural-AC analogue of `s_ac_bag_is_produced_by_the_spread_not_the_report`.
///
/// We take a real, complete report for `{ open(na, A) | na[B] }` and CORRUPT its σ (the ambient name
/// `N`, the two unwrapped processes `P`/`Q`, and the residual `rest` — the SAME σ the report-path
/// `structural_ac_contract_call` reconstructs the bag + reducts from) to a decoy `PZero`, leaving the
/// rule label (`OpenRule`) valid so the in-Rho match GATE still admits. The Stage-4
/// `rho_net_match_invocation_from_dovetail_to` STRUCTURALLY reflects the WHOLE subject (M-reflect, NOT
/// the report σ); the match driver LOCATES the bag, publishes its soup on the SITE-KEYED `ac:` carrier
/// from the SUBJECT's ground elements, and the co-installed MATCH receiver binds the two elements +
/// `P`/`Q` + `rest` ON the reducer and splices `{P, Q}`.
///
/// Because the operand bag AND the reducts are built from `term`, not the corrupted σ, OUT is
/// `{ A | B }` (= `{ PA | PB }`). A report-σ arm would have reconstructed `{ PZero | PZero }`. So a
/// positive, correct OUT is non-vacuous evidence the bag + reducts came from the spread, not the
/// report — structural-AC matching is a genuine in-Rho replacement (the σ-replay duplicate is retired).
#[tokio::test]
async fn s_ac_structural_bag_is_produced_by_the_spread_not_the_report() {
    mettail_runtime::clear_var_cache();
    let (backend, _fingerprint, _channel) = amb_demo_backend();

    let term = AmbDemoLanguage
        .parse_term("{ open(na, A) | na[B] }")
        .expect("AmbDemo must parse the OpenRule redex");
    let mut report = AmbDemoLanguage::dovetail_report_for(term.as_ref(), 64, 1_000_000)
        .expect("AmbDemo Dovetail report must compile");
    assert!(
        !report.rewrite_justifications.is_empty(),
        "the OpenRule must surface at least one firing justification"
    );

    // Deliberately WRONG σ: a report-σ structural-AC arm would reconstruct the bag + reducts from
    // these and fire `{ PZero | PZero }`. The rule label (`OpenRule`) stays valid so the in-Rho match
    // gate admits the path; ONLY the σ (the bag + reduct source) is corrupted.
    let decoy = RuntimeReflectedSubterm { constructor: "PZero".to_string(), children: Vec::new() };
    let decoy_rest =
        RuntimeReflectedSubterm { constructor: "PPar".to_string(), children: Vec::new() };
    for justification in &mut report.rewrite_justifications {
        assert_eq!(justification.rule_label, "OpenRule", "the fired rule label stays valid");
        justification.sigma = vec![
            ("N".to_string(), decoy.clone()),
            ("P".to_string(), decoy.clone()),
            ("Q".to_string(), decoy.clone()),
            ("rest".to_string(), decoy_rest.clone()),
        ];
    }

    let invocation =
        AmbDemoLanguage::rho_net_match_invocation_from_dovetail_to(term.as_ref(), &report, "OUT")
            .expect("the MATCH path admits OpenRule despite the corrupted report σ");

    let observation = backend
        .run_rho_net_with_call_and_observe_runtime_values(&invocation.call, &invocation.out_channel)
        .await
        .expect("the in-Rho structural-AC match + firing executes on the reducer");

    assert_eq!(
        observation.observed_count(),
        1,
        "the located OpenRule redex fires exactly once (got {:?})",
        observation.values
    );
    // OUT is `{ A | B }` from the SPREAD subject — never the corrupted σ's `{ PZero | PZero }`.
    assert_bag_is(&observation.values[0], &[proc_leaf("PA"), proc_leaf("PB")]);
    assert_ne!(
        &observation.values[0],
        &RuntimeObservationValue::Bag(vec![(proc_leaf("PZero"), 2)]),
        "the reduct bag was re-sourced from the spread, not the corrupted report σ"
    );
}
