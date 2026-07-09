//! Stage 3c end-to-end: a GENERATED λ-calculus language's β-reduction fires end-to-end as a
//! COMM on the live f1r3node Rholang interpreter.
//!
//! `LambdaDemo` is a generated `language!` whose base rewrite `Beta: App(Lam(^x. b), a) ~>
//! subst(b, x := a)` (written `(App (Lam fun) arg) ~> (eval fun arg)` in the DSL — the `eval`
//! operator IS the capture-avoiding substitution) is the BINDER/substitution family (D2(d)).
//! The pipeline exercised here is the BINDER analogue of the base-rewrite σ-injection proven in
//! `rho_net_equivalence.rs`, the AC firing in `rho_net_ac_firing.rs`, and the contextual join in
//! `rho_net_contextual_firing.rs`:
//!
//!  1. [`LambdaDemoLanguage::dovetail_report_for`] saturates the redex `App(Lam(^x. f(x)), A)`:
//!     `Beta` fires and the host (Dovetail, model-b) does the matching AND the capture-avoiding
//!     substitution, so the sole `rewrite_justifications` entry is the `Beta` firing whose
//!     CONTRACTUM is the reduced term `f(A)` (`RHS[σ]` after substitution);
//!  2. the generated [`LambdaDemoLanguage::rho_net_invocation_from_dovetail_to`] σ-injection
//!     F-function (its substitution arm — base | AC | contextual | subst) reflects that
//!     contractum at the scope variable's σ slot and assembles `c_beta!(⟦f(A)⟧, ⟦A⟧, @OUT)` via
//!     `term_contract_call`, where `c_beta` is the `Beta` σ-receiver's source channel;
//!  3. the runtime bridge runs `installed_rho_net_program_par() ∥ call` on the f1r3node
//!     RhoRuntime, where the installed `SubstRewrite` σ-receiver
//!     (`for([fun, arg, out] <- c_beta){ out!(fun) }`) forwards the scope slot (the reduct
//!     `f(A)`) on `@OUT` — one atomic COMM (INV-3).
//!
//! `App(Lam(^x. f(x)), A)` reduces to `f(A)`, and `App(Lam(^x. f(x)), A) ≠ f(A)`, so a positive
//! OUT observation is non-vacuous evidence β-reduction fired as a COMM with the reduct Dovetail
//! computed (the substitution is host-side — model-b — exactly as the base/AC/contextual arms,
//! and the firing itself runs on the reducer).
//!
//! FV: `formal/rocq/rho_bridge/theories/BinderReflectionTotalOrReject.v` (the De Bruijn LHS
//! σ-variable extraction excludes the binder + preserves the body's free variables, and the
//! binder-node reflection is injective / collision-free) + the inherited base-rewrite
//! correspondence (`LinearCommCorrespondence.v`) and install boundary
//! (`RhoLoweringTotalOrRejects.v`).
#![cfg(feature = "lambda-demo-runtime")]

use mettail_languages::lambdademo::LambdaDemoLanguage;
use mettail_rholang_codegen::{
    lower_language_def, plan_rho_default_backend, reconstruct_language_def,
    suggest_rejected_rule_dispositions, RhoCoverageEvidence, RhoDefaultBackendRequirements,
    RhoGuardCoverageEvidence,
};
use mettail_rholang_runtime::{
    build_rho_net_injection_invocation_from_contract, PlannedRhoBackend, RhoMachineInvocation,
};
use mettail_runtime::{Language, RuntimeObservationValue, RuntimeReflectedSubterm};

/// Reconstruct LambdaDemo's augmented `LanguageDef` from the generated metadata's
/// `definition_source()` and plan its Rho-default backend (the `Beta` `SubstRewrite` σ-receiver
/// installs alongside the `Lam`/`App`/`F`/`A` structural constructors), exactly as the
/// Rho/Dovetail installer does. Returns the planned backend and the plan's definition
/// fingerprint (which must equal the generated metadata fingerprint the subst injection reflects
/// the contractum with).
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
fn nullary(constructor: &str) -> RuntimeObservationValue {
    RuntimeObservationValue::Term { constructor: constructor.to_string(), children: Vec::new() }
}

/// The generated substitution σ-injection fires the installed `Beta` σ-receiver as ONE COMM,
/// landing the reduct `f(A)` on OUT. This is the BINDER analogue of
/// `dovetail_report_semantics_match_rho_machine_execution_for_swap` (base) and
/// `ctxdemo_contextual_rewrite_fires_as_a_join_comm_on_the_reducer` (contextual): INV-3, a
/// binder/β-substitution rewrite firing as a COMM on the reducer with a host-computed reduct.
#[tokio::test]
async fn lambdademo_beta_reduction_fires_as_a_comm_on_the_reducer() {
    mettail_runtime::clear_var_cache();
    let (backend, fingerprint) = lambda_demo_backend();

    // Fingerprint coherence: the installed `Beta` σ-receiver (from the reconstructed def) and the
    // subst σ-injection (which reflects the contractum with `metadata().definition_fingerprint()`)
    // must agree, or the forwarded reduct would decode inconsistently.
    assert_eq!(
        LambdaDemoLanguage.metadata().definition_fingerprint(),
        Some(fingerprint.as_str()),
        "planned backend fingerprint must equal the generated metadata fingerprint"
    );

    // The concrete redex `App(Lam(^x. f(x)), A)` = `(lam x. f(x), A)`, parsed through the
    // generated parser (the binder body references the bound `x`). `f(A) ≠ (lam x. f(x), A)`, so
    // a positive OUT observation is non-vacuous evidence β-reduction fired.
    let term = LambdaDemoLanguage
        .parse_term("(lam x. f(x), A)")
        .expect("LambdaDemo must parse the β-redex (lam x. f(x), A)");

    // (1) DOVETAIL REPORT SEMANTICS: `Beta` fires and the host applies the capture-avoiding
    // substitution, so the acyclic reduction is Complete with EXACTLY the single `Beta` firing,
    // whose CONTRACTUM is the reduced term `f(A)`.
    let report = LambdaDemoLanguage::dovetail_report_for(term.as_ref(), 64, 1_000_000)
        .expect("LambdaDemo Dovetail report must compile");
    assert!(
        report.is_complete(),
        "the acyclic β-reduction must report Complete, got {:?}",
        report.completeness
    );
    assert_eq!(
        report.rewrite_justifications.len(),
        1,
        "exactly one β-reduction fires for (lam x. f(x), A), got {:?}",
        report.rewrite_justifications
    );
    let justification = &report.rewrite_justifications[0];
    assert_eq!(justification.rule_label, "Beta", "the fired rule is Beta");

    // The firing's contractum IS the host-computed reduct `f(A)` — the whole point of model-b:
    // the substitution `b[x := a]` is applied host-side and handed to the σ-injection.
    let f_of_a = RuntimeReflectedSubterm {
        constructor: "F".to_string(),
        children: vec![RuntimeReflectedSubterm { constructor: "A".to_string(), children: Vec::new() }],
    };
    assert_eq!(
        justification.contractum.as_ref(),
        Some(&f_of_a),
        "the Beta firing's contractum is the reduced term f(A) the host computed, got {:?}",
        justification.contractum
    );

    // (2) The generated σ-injection F-function (subst arm) reflects the contractum at the scope
    // slot and assembles `c_beta!(⟦f(A)⟧, ⟦A⟧, @OUT)` for the `Beta` σ-receiver.
    let invocation =
        LambdaDemoLanguage::rho_net_invocation_from_dovetail_to(term.as_ref(), &report, "OUT")
            .expect("LambdaDemo subst injection must assemble from a complete report");
    assert_eq!(invocation.out_channel, "OUT");

    // The Epic-4 bridge selects the INSTALLED-σ-receiver observation shape so the receiver fires.
    match build_rho_net_injection_invocation_from_contract(invocation.clone()) {
        RhoMachineInvocation::RunRhoNetWithCallAndObserveRuntimeValues { out_channel, .. } => {
            assert_eq!(out_channel, "OUT", "the bridge must preserve the out channel");
        },
        other => panic!("the subst injection must map to RunRhoNet…, got {other:?}"),
    }

    // (3) RHO-MACHINE EXECUTION: run the installed program (the `Beta` σ-receiver) ∥ call, and
    // observe OUT. The receiver binds the delivered σ tuple and forwards the scope slot (the
    // reduct `f(A)`) on `@OUT` — one atomic COMM (INV-3).
    let observation = backend
        .run_rho_net_with_call_and_observe_runtime_values(&invocation.call, &invocation.out_channel)
        .await
        .expect("the subst injection must execute on the Rho runtime");

    // Non-vacuity: the σ-receiver fired exactly once and left exactly one value on OUT.
    assert_eq!(
        observation.observed_count(),
        1,
        "OUT must carry exactly one value — the β σ-receiver must fire (got {:?})",
        observation.values
    );

    // EQUIVALENCE: the Rho machine landed the reduct `f(A)`, the substituted β-normal form,
    // non-vacuous against the input `App(Lam(^x. f(x)), A)`.
    let f_a = RuntimeObservationValue::Term {
        constructor: "F".to_string(),
        children: vec![nullary("A")],
    };
    assert_eq!(
        observation.values[0], f_a,
        "the β-reduction fired as a COMM on the reducer and landed the reduct f(A)"
    );
}

/// S-binder SLICE 1 (Stage 4) — the set-automaton LOCATES the β-redex `App(Lam(^x. b), a)` IN RHO
/// and CAPTURES `(body, arg)` from the REFLECTED SUBJECT, not the host report. The binder analogue
/// of the base `m_reflect_sigma_is_produced_by_the_automaton_not_the_report` (`rho_net_equivalence.rs`)
/// and the S-native `s_native_location_is_produced_by_the_automaton_not_the_report`
/// (`rho_net_native_firing.rs`).
///
/// The MATCH path (`rho_net_match_invocation_from_dovetail_to`) M-reflects the whole subject
/// `(lam x. f(x), A)` STRUCTURALLY to `App(^lambda(F(^bound(Z))), A)` — the de-Bruijn binder body
/// reflects to a `^bound(peano(scope))` leaf (scope 0 ⟹ `Z`) — admits `Beta` as the
/// `^lambda`-remapped nested App automaton entry `App(^lambda(body), arg)`, and the positional
/// set-automaton LOCATES that redex + CAPTURES `(body, arg)` ON the reducer. Its accept routes to
/// the installed `Beta` `SubstRewrite` σ-receiver (`for([fun, arg, out] <- c_beta){ out!(fun) }`),
/// which forwards the captured scope-BODY slot (`fun`) on `@OUT`.
///
/// SLICE BOUNDARY (reduct fail-closed): the delivered value is the RAW captured body
/// `F(^bound(Z))` — the automaton's in-Rho CAPTURE — NOT the substituted β-reduct `F(A)`. The
/// capture-avoiding substitution (the in-Rho subst TRS + `^subst` seed send) is S-binder SLICE 2;
/// this slice proves the MATCH (locate + capture) ONLY. β STILL REDUCES CORRECTLY on the host-σ
/// path — `lambdademo_beta_reduction_fires_as_a_comm_on_the_reducer` above uses
/// `rho_net_invocation_from_dovetail_to` (the σ-injection F-function), which is UNCHANGED, so the
/// `fun` slot there carries the host-computed reduct `f(A)` and OUT is `f(A)`.
///
/// We CORRUPT the report σ to nonsense (leaving `rule_label = "Beta"` + the completeness gate
/// valid — the only things the MATCH path reads the report for), so a positive, correct CAPTURE
/// observation is non-vacuous evidence the captured body came from the AUTOMATON (the reflected
/// subject spread), NOT the report. A report-σ locator would key off the nonsense and never find
/// the real `App(^lambda(...), ...)`.
///
/// FV: `BinderReflectionTotalOrReject.v` (the indexed-Peano MATCH reflection is total-or-reject +
/// injective: `^lambda`/`^bound(peano)`/`^free` shapes pairwise-distinct, `peano` injective) +
/// `InRhoMatchPositional.v` (the binder-frame arm: the automaton LOCATES `App(^lambda(body), arg)`
/// and binds the positional σ `(body, arg)`).
#[tokio::test]
async fn s_binder_matches_the_beta_redex_in_rho() {
    mettail_runtime::clear_var_cache();
    let (backend, _fingerprint) = lambda_demo_backend();

    // The β-redex `App(Lam(^x. f(x)), A)` = `(lam x. f(x), A)` — the SAME subject the host-σ firing
    // test reduces. `f(A) ≠ (lam x. f(x), A)` and the captured body `f(^bound(Z)) ≠ f(A)`, so a
    // positive OUT observation is non-vacuous.
    let term = LambdaDemoLanguage
        .parse_term("(lam x. f(x), A)")
        .expect("LambdaDemo must parse the β-redex (lam x. f(x), A)");

    let mut report = LambdaDemoLanguage::dovetail_report_for(term.as_ref(), 64, 1_000_000)
        .expect("LambdaDemo Dovetail report must compile");
    assert_eq!(
        report.rewrite_justifications.len(),
        1,
        "(lam x. f(x), A) fires exactly one Beta, got {:?}",
        report.rewrite_justifications
    );

    // Deliberately WRONG σ (the matched-subterm LOCATION): a report-σ locator would key off these
    // and never find the real App(^lambda(F(^bound(Z))), A). The rule label (the location-independent
    // identity) stays valid — only the LOCATION σ is corrupted.
    let nonsense = RuntimeReflectedSubterm { constructor: "A".to_string(), children: Vec::new() };
    for justification in &mut report.rewrite_justifications {
        justification.sigma =
            vec![("fun".to_string(), nonsense.clone()), ("arg".to_string(), nonsense.clone())];
        assert_eq!(
            justification.rule_label, "Beta",
            "the fired rule label (the location-independent identity) stays valid"
        );
    }

    // The MATCH path admits the β-redex despite the corrupted σ: it M-reflects `term` to
    // `App(^lambda(F(^bound(Z))), A)`, admits `Beta` as the nested `App(^lambda(body), arg)` entry,
    // and the automaton LOCATES it + CAPTURES `(body, arg)`.
    let invocation =
        LambdaDemoLanguage::rho_net_match_invocation_from_dovetail_to(term.as_ref(), &report, "OUT")
            .expect("the MATCH path admits the β-redex (lam x. f(x), A) with a corrupted report σ");
    assert_eq!(invocation.out_channel, "OUT");

    let observation = backend
        .run_rho_net_with_call_and_observe_runtime_values(&invocation.call, &invocation.out_channel)
        .await
        .expect("the in-Rho β-redex match + capture executes on the reducer");

    // Non-vacuity: the automaton located the β-redex and the σ-receiver fired exactly once.
    assert_eq!(
        observation.observed_count(),
        1,
        "OUT must carry exactly one value — the located β-redex must fire (got {:?})",
        observation.values
    );

    // The RAW CAPTURED BODY `F(^bound(Z))` — the automaton's in-Rho capture from the reflected
    // subject (the de-Bruijn `x` reflects to `^bound(Z)`), located by the `sa:` automaton (from
    // `term`), NOT the corrupted report σ. This is the MATCH-only delivery: the un-substituted body.
    let captured_body = RuntimeObservationValue::Term {
        constructor: "F".to_string(),
        children: vec![RuntimeObservationValue::Term {
            constructor: "^bound".to_string(),
            children: vec![nullary("Z")],
        }],
    };
    assert_eq!(
        observation.values[0], captured_body,
        "the automaton LOCATED App(^lambda(body), arg) and CAPTURED the body F(^bound(Z)) IN RHO \
         (from the reflected term, not the corrupted report σ)"
    );

    // SLICE BOUNDARY, made explicit: the captured body is NOT the substituted β-reduct `F(A)` — the
    // capture-avoiding substitution is S-binder slice 2's in-Rho TRS. Slice 1 MATCHES + captures.
    let reduct = RuntimeObservationValue::Term {
        constructor: "F".to_string(),
        children: vec![nullary("A")],
    };
    assert_ne!(
        observation.values[0], reduct,
        "slice 1 delivers the RAW captured body (MATCH-only); the substituted reduct F(A) is slice 2"
    );
}
