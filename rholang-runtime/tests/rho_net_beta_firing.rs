//! Stage 4 S-binder SLICE 2a end-to-end: a GENERATED λ-calculus language's β-reduction FIRES FULLY
//! IN-RHO — matching AND capture-avoiding substitution — as a cascade of COMMs on the live f1r3node
//! Rholang interpreter. The host reduct is RETIRED: the reduct `b[a/0]` is computed BY THE REDUCER.
//!
//! `LambdaDemo` is a generated `language!` whose base rewrite `Beta: App(Lam(^x. b), a) ~>
//! subst(b, x := a)` (written `(App (Lam fun) arg) ~> (eval fun arg)`) is the BINDER/substitution
//! family (D2(d)). The in-Rho β pipeline:
//!
//!  1. [`LambdaDemoLanguage::rho_net_match_invocation_from_dovetail_to`] (the MATCH path,
//!     `match_body`) M-reflects the whole subject `App(Lam(^x. f(x)), A)` STRUCTURALLY to
//!     `App(^lambda(F(^bound(Z))), A)` (the de-Bruijn binder body reflects to `^bound(peano(scope))`),
//!     admits `Beta` as the `^lambda`-remapped nested App automaton entry, and the positional
//!     set-automaton LOCATES the redex + CAPTURES the RAW `(body, arg)` ON the reducer;
//!  2. the accept fires the installed `Beta` `SubstRewrite` σ-receiver — now the β SEED
//!     ([`subst_seed_receiver_par`]) — whose body SENDS `^subst(⟦Z⟧, arg, body, out)` on the reserved
//!     `^subst` channel (THIS ONE COMM is the observable β-FIRE);
//!  3. the installed generated de-Bruijn subst/shift TRS (the five reserved receivers) self-drives the
//!     τ-cascade to the β-normal form `f(A)` on `out` — object descent into `F`, `^bound Z` compares
//!     `Eq`, `^shiftk(Z, A) = A` — NO host loop, NO `Value → GroundTerm` de-reflection.
//!
//! `App(Lam(^x. f(x)), A)` reduces to `f(A)`, and `f(A) ≠ App(Lam(^x. f(x)), A)`, so a positive OUT
//! observation of `f(A)` is non-vacuous evidence β-reduction fired FULLY in-Rho (the substitution is
//! the reducer's, not the host's).
//!
//! FV (SLICE 2b, NOT built here): `DeBruijnSubstTRS.v` (SN + confluence + `NF = b[a/0]`) +
//! `InRhoBetaCascadeWeakBisim.v` (object-β with the in-Rho subst cascade ≈ abstract β) + the
//! `InRhoMatchPositional.v` reduct-separation arm. The receiver mechanism is de-risked (as the
//! spike's real-`Par` analogue) in `rho_net_subst_trs_reducer.rs`.
#![cfg(feature = "lambda-demo-runtime")]

use mettail_languages::lambdademo::LambdaDemoLanguage;
use mettail_rholang_codegen::{
    lower_language_def, plan_rho_default_backend, reconstruct_language_def, reflect_ground_term_par,
    subst_seed_send_par, suggest_rejected_rule_dispositions, GroundTerm, RhoCoverageEvidence,
    RhoDefaultBackendRequirements, RhoGuardCoverageEvidence, BOUND_VAR_REFLECT_LABEL,
    FREE_VAR_REFLECT_LABEL, LAMBDA_REFLECT_LABEL, PEANO_SUCC_REFLECT_LABEL, PEANO_ZERO_REFLECT_LABEL,
};
use mettail_rholang_runtime::PlannedRhoBackend;
use mettail_runtime::{Language, RuntimeObservationValue, RuntimeReflectedSubterm};

/// Reconstruct LambdaDemo's augmented `LanguageDef` from the generated metadata's
/// `definition_source()` and plan its Rho-default backend (the `Beta` β SEED σ-receiver installs
/// alongside the five reserved TRS receivers + the `Lam`/`App`/`F`/`A` structural constructors).
/// Returns the planned backend and the plan's definition fingerprint (which the reflection tags —
/// the M-reflect subject, the automaton entry ops, the reserved `^subst` channel — all share).
fn lambda_demo_backend() -> (PlannedRhoBackend, String) {
    let source = LambdaDemoLanguage
        .metadata()
        .definition_source()
        .expect("generated LambdaDemoLanguage must expose its definition_source");
    let def = reconstruct_language_def(source)
        .expect("LambdaDemoLanguage definition_source must reconstruct as a LanguageDef");

    let lowering = lower_language_def(&def);
    let requirements = RhoDefaultBackendRequirements {
        coverage: RhoCoverageEvidence::CoveredRejectedRules(suggest_rejected_rule_dispositions(
            &def, &lowering,
        )),
        guard_coverage: RhoGuardCoverageEvidence::NoGuardObligations,
    };
    let plan = plan_rho_default_backend(&def, requirements)
        .expect("LambdaDemo (β base rewrite) must flip to the Rho backend");
    let fingerprint = plan.definition_fingerprint().to_string();
    (PlannedRhoBackend::from_plan(plan), fingerprint)
}

/// A nullary observation term, e.g. `A`.
fn onullary(constructor: &str) -> RuntimeObservationValue {
    RuntimeObservationValue::Term { constructor: constructor.to_string(), children: Vec::new() }
}
fn oterm(constructor: &str, children: Vec<RuntimeObservationValue>) -> RuntimeObservationValue {
    RuntimeObservationValue::Term { constructor: constructor.to_string(), children }
}

// ── reflected-term (GroundTerm) builders, for the direct-seed spike cases ──────────────────────
fn g_nullary(label: &str) -> GroundTerm {
    GroundTerm::nullary(label)
}
fn g_node(label: &str, children: Vec<GroundTerm>) -> GroundTerm {
    GroundTerm::new(label, children)
}
/// `^bound(peano(depth))`.
fn g_bound(depth: usize) -> GroundTerm {
    let mut peano = g_nullary(PEANO_ZERO_REFLECT_LABEL);
    for _ in 0..depth {
        peano = g_node(PEANO_SUCC_REFLECT_LABEL, vec![peano]);
    }
    g_node(BOUND_VAR_REFLECT_LABEL, vec![peano])
}
fn g_free(name: &str) -> GroundTerm {
    g_node(FREE_VAR_REFLECT_LABEL, vec![g_nullary(name)])
}
fn g_lambda(body: GroundTerm) -> GroundTerm {
    g_node(LAMBDA_REFLECT_LABEL, vec![body])
}

/// THE full in-Rho β firing: `App(Lam(^x. f(x)), A)` reduces to `f(A)` via the MATCH path + the TRS
/// SEED — matching AND the capture-avoiding substitution both happen ON the reducer (the host reduct
/// is retired). This is the binder analogue of the base `dovetail_report_semantics_match_rho_machine
/// _execution_for_swap`, the AC `acdemo_ac_rewrite_fires_as_a_comm_on_the_reducer`, and the
/// contextual `ctxdemo_contextual_rewrite_fires_as_a_join_comm_on_the_reducer`.
///
/// PATH: `rho_net_match_invocation_from_dovetail_to` (`match_body`), NOT the retired host-σ
/// `rho_net_invocation_from_dovetail_to` (whose `subst_site_arms` are commented out — a `Beta`
/// firing there now has no dispatch arm). The automaton reflects + locates + captures the RAW body;
/// the installed β SEED σ-receiver seeds `^subst(⟦Z⟧, arg, body, out)`; the installed TRS reduces it.
#[tokio::test]
async fn lambdademo_beta_reduction_fires_as_a_comm_on_the_reducer() {
    mettail_runtime::clear_var_cache();
    let (backend, fingerprint) = lambda_demo_backend();

    // Fingerprint coherence: the installed `Beta` SEED σ-receiver + the reserved TRS channels (both
    // from the reconstructed def) and the M-reflect subject (which reflects with
    // `metadata().definition_fingerprint()`) must agree, or the `^subst` seed would not rendezvous
    // with the installed TRS.
    assert_eq!(
        LambdaDemoLanguage.metadata().definition_fingerprint(),
        Some(fingerprint.as_str()),
        "planned backend fingerprint must equal the generated metadata fingerprint"
    );

    // The concrete redex `App(Lam(^x. f(x)), A)` = `(lam x. f(x), A)`. `f(A) ≠ (lam x. f(x), A)`, so
    // a positive OUT observation of `f(A)` is non-vacuous evidence β fired fully in-Rho.
    let term = LambdaDemoLanguage
        .parse_term("(lam x. f(x), A)")
        .expect("LambdaDemo must parse the β-redex (lam x. f(x), A)");

    // The Dovetail report GATES the match path (which rules fired + completeness); the reduct is NOT
    // read from it — the automaton reflects the subject + the TRS computes the reduct.
    let report = LambdaDemoLanguage::dovetail_report_for(term.as_ref(), 64, 1_000_000)
        .expect("LambdaDemo Dovetail report must compile");
    assert!(report.is_complete(), "the acyclic β-reduction must report Complete");
    assert_eq!(report.rewrite_justifications.len(), 1, "exactly one Beta fires");
    assert_eq!(report.rewrite_justifications[0].rule_label, "Beta", "the fired rule is Beta");

    // The MATCH path: M-reflect the subject, admit `Beta`, LOCATE + CAPTURE the raw `(body, arg)`,
    // fire the SEED, drive the TRS cascade — all on the reducer.
    let invocation =
        LambdaDemoLanguage::rho_net_match_invocation_from_dovetail_to(term.as_ref(), &report, "OUT")
            .expect("the in-Rho β MATCH path admits (lam x. f(x), A)");
    assert_eq!(invocation.out_channel, "OUT");

    let observation = backend
        .run_rho_net_with_call_and_observe_runtime_values(&invocation.call, &invocation.out_channel)
        .await
        .expect("the in-Rho β fires on the reducer");

    assert_eq!(
        observation.observed_count(),
        1,
        "OUT must carry exactly one value — the β cascade must deliver its NF (got {:?})",
        observation.values
    );
    // EQUIVALENCE: the reducer landed `f(A)`, the β-normal form the in-Rho TRS computed (NOT a host
    // reduct), non-vacuous against the input `App(Lam(^x. f(x)), A)`.
    assert_eq!(
        observation.values[0],
        oterm("F", vec![onullary("A")]),
        "β fired FULLY in-Rho (match + subst TRS) and landed the reduct f(A)"
    );
}

/// ★ The corrected report-σ-INDEPENDENCE probe: the in-Rho β reduct is a function of the SUBJECT (the
/// automaton's reflected capture + the TRS cascade), NOT of the Dovetail report. We route `Beta`
/// through the MATCH path (`match_body`) and corrupt BOTH `justification.sigma` AND
/// `justification.contractum` to nonsense, leaving ONLY `rule_label = "Beta"` + the completeness gate
/// valid (the two things `match_body` reads the report for — `assert_complete` + the fired labels).
/// A positive `OUT == ⟦f(A)⟧` is non-vacuous evidence NEITHER the report σ (a redex locator) NOR the
/// report contractum (the retired host reduct) feeds the reduct — the automaton LOCATES + CAPTURES,
/// and the TRS SEED COMPUTES, entirely from the reflected subject.
///
/// STRICTLY STRONGER than the S-native residue probe (there the host still supplies the native VALUE;
/// here the reduct has ZERO host residue). Replaces the SLICE-1 `s_binder_matches_the_beta_redex_in_rho`
/// (which asserted the RAW captured body `F(^bound Z)` — reduct fail-closed; the reduct now FIRES in-Rho).
#[tokio::test]
async fn s_binder_reduct_is_report_sigma_independent() {
    mettail_runtime::clear_var_cache();
    let (backend, _fingerprint) = lambda_demo_backend();

    let term = LambdaDemoLanguage
        .parse_term("(lam x. f(x), A)")
        .expect("LambdaDemo must parse the β-redex (lam x. f(x), A)");

    let mut report = LambdaDemoLanguage::dovetail_report_for(term.as_ref(), 64, 1_000_000)
        .expect("LambdaDemo Dovetail report must compile");
    assert_eq!(report.rewrite_justifications.len(), 1, "(lam x. f(x), A) fires exactly one Beta");

    // Corrupt BOTH the σ (a report-σ locator would key off it and never find the real
    // `App(^lambda(F(^bound Z)), A)`) AND the contractum (the RETIRED host reduct). Leave the fired
    // label + completeness valid — the only report reads the MATCH path makes.
    let nonsense = RuntimeReflectedSubterm { constructor: "NONSENSE".to_string(), children: Vec::new() };
    for justification in &mut report.rewrite_justifications {
        justification.sigma =
            vec![("fun".to_string(), nonsense.clone()), ("arg".to_string(), nonsense.clone())];
        justification.contractum = Some(nonsense.clone());
        assert_eq!(justification.rule_label, "Beta", "the fired label stays valid (gate only)");
    }
    assert!(report.is_complete(), "completeness stays valid (gate only)");

    let invocation =
        LambdaDemoLanguage::rho_net_match_invocation_from_dovetail_to(term.as_ref(), &report, "OUT")
            .expect("the MATCH path admits the β-redex despite a corrupted report σ + contractum");

    let observation = backend
        .run_rho_net_with_call_and_observe_runtime_values(&invocation.call, &invocation.out_channel)
        .await
        .expect("the in-Rho β match + subst cascade executes on the reducer");

    assert_eq!(observation.observed_count(), 1, "the located β-redex must fire exactly once");
    // The cascade NF `f(A)`, produced from the REFLECTED SUBJECT — NOT the corrupted report σ/contractum.
    assert_eq!(
        observation.values[0],
        oterm("F", vec![onullary("A")]),
        "the in-Rho β reduct f(A) is report-σ-INDEPENDENT (automaton capture + TRS SEED, not the report)"
    );
    // Made explicit: the reduct is NOT the corrupted contractum, and NOT the raw captured body.
    assert_ne!(
        observation.values[0],
        oterm("NONSENSE", Vec::new()),
        "the reduct did not come from the corrupted report contractum"
    );
    assert_ne!(
        observation.values[0],
        oterm("F", vec![oterm(BOUND_VAR_REFLECT_LABEL, vec![onullary(PEANO_ZERO_REFLECT_LABEL)])]),
        "the reduct is the SUBSTITUTED NF f(A), not the raw captured body f(^bound ^Z)"
    );
}

/// spike `case2` — `(λ.λ.1) c → λ.c` — the C1 depth-INCREMENT + `^shiftk`, as a REAL-codegen seed on
/// the INSTALLED program. Seeding `^subst(Z, ^free c, ^lambda(^bound(S Z)), @OUT)` on the reserved
/// channel drives the installed TRS: descend `^lambda` (`Z → S Z`); `^bound(S Z)` compares `Eq`;
/// `^shiftk(S Z, ^free c) = ^shift(Z, ^free c) = ^free c` (free vars inert). NF `^lambda(^free c)`.
/// (A parseable full-β subject needs a free-var argument, which LambdaDemo's grammar has no
/// production for, so this exercises the depth-increment via the installed TRS + a direct seed.)
#[tokio::test]
async fn lambdademo_beta_case2_nested_binder_depth_increment_fires_in_rho() {
    mettail_runtime::clear_var_cache();
    let (backend, fingerprint) = lambda_demo_backend();

    let seed = subst_seed_send_par(
        &fingerprint,
        reflect_ground_term_par(&g_free("c"), &fingerprint),
        reflect_ground_term_par(&g_lambda(g_bound(1)), &fingerprint),
        "OUT",
    );
    let observation = backend
        .run_rho_net_with_call_and_observe_runtime_values(&seed, "OUT")
        .await
        .expect("the installed TRS reduces the case2 seed on the reducer");

    assert_eq!(
        observation.values,
        vec![oterm(LAMBDA_REFLECT_LABEL, vec![oterm(FREE_VAR_REFLECT_LABEL, vec![onullary("c")])])],
        "(λ.λ.1) c must reduce to λ.c — depth increment + shiftk fired on the installed TRS",
    );
}

/// spike `case3` — object-descent widening `subst(Z, A, App(^bound Z, ^bound Z)) → App(A, A)` — as a
/// REAL-codegen seed on the INSTALLED program. The C2 object-congruence arm for the binary object
/// constructor `App` spawns TWO sibling `^subst(Z, A, ^bound Z)` redexes that co-reduce to `A` and
/// rejoin via the atomic continuation JOIN (`for(@s0<-r0 & @s1<-r1){ret!(App(s0, s1))}`) — the
/// red-team's `NestedEntryMultiSite` trigger reduces with NO widening (the cascade uses sends, off
/// the all-sites locator).
#[tokio::test]
async fn lambdademo_beta_case3_object_descent_two_sibling_substs_coreduce_in_rho() {
    mettail_runtime::clear_var_cache();
    let (backend, fingerprint) = lambda_demo_backend();

    let seed = subst_seed_send_par(
        &fingerprint,
        reflect_ground_term_par(&g_nullary("A"), &fingerprint),
        reflect_ground_term_par(&g_node("App", vec![g_bound(0), g_bound(0)]), &fingerprint),
        "OUT",
    );
    let observation = backend
        .run_rho_net_with_call_and_observe_runtime_values(&seed, "OUT")
        .await
        .expect("the installed TRS reduces the case3 seed on the reducer");

    assert_eq!(
        observation.values,
        vec![oterm("App", vec![onullary("A"), onullary("A")])],
        "subst(Z, A, App(^bound Z, ^bound Z)) must reduce to App(A, A) — sibling co-reduction, no widening",
    );
}
