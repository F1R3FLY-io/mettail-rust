//! Epic 4 (R-5) end-to-end equivalence: **Dovetail report semantics** vs
//! **RhoNet/Rho-machine execution**, driven entirely through the GENERATED path
//! (pgmcp #2010).
//!
//! Where the hand-built `rho_net_injection_demo` (R-2) supplies σ directly as the
//! call arguments, this test derives σ from the generated
//! [`SwapDemoLanguage::dovetail_report_for`] — the report producer that resolves +
//! bare-ifies σ provenance (R-4) — then feeds that report to the generated
//! [`SwapDemoLanguage::rho_net_invocation_from_dovetail_to`] σ-injection F-function,
//! bridges it through [`build_rho_net_injection_invocation_from_contract`] (the
//! Epic-4 injection adapter), and runs it against the language's INSTALLED
//! σ-receiver program on the real in-memory f1r3node Rho machine.
//!
//! The equivalence claim is checked against the report's OWN σ, not a hard-coded
//! oracle: the Rho machine must land exactly `RHS(SwapStep) = Pair(y, x)` with the
//! substitution the Dovetail report computed applied — `Pair(σ[y], σ[x])`. Because
//! `Swap(A, B) ≠ Pair(B, A)`, a positive OUT observation is non-vacuous evidence
//! the base rewrite fired with Dovetail's σ, and the two engines agree.
//!
//! Fingerprint coherence is asserted explicitly: the planned backend (reconstructed
//! from the generated `definition_source`, exactly as the production installer does)
//! must carry the same `definition_fingerprint` the generated metadata exposes, so
//! the σ-receiver's reflected RHS constructors and the σ-injection's reflected σ
//! arguments tag identically — otherwise the receiver would never fire.
#![cfg(feature = "swap-demo-runtime")]

use std::collections::HashMap;
use std::sync::Arc;

use dovetail::rules::Pattern;
use dovetail::set_automaton::{AutomatonNode, PatternId, SetAutomaton};
use mettail_languages::swapdemo::{Proc, SwapDemoLanguage, SwapDemoTerm};
use mettail_rholang_codegen::{
    ac_bag_pattern, ac_sigma_receiver_par, automaton_receiver_network_par,
    compile_in_rho_matching_ruleset, in_rho_match_call_par, lower_language_def,
    multi_pattern_receiver_network_par, plan_rho_default_backend, reconstruct_language_def,
    reflect_ground_term_par,
    rho_net_injection_sites, spread_term_par, suggest_rejected_rule_dispositions,
    AutomatonAcceptTarget, CollectionType, GroundTerm, RhoCoverageEvidence, RhoDefaultBackendRequirements,
    RhoGuardCoverageEvidence, RhoNetRuleKind,
};
use mettail_rholang_runtime::{
    build_rho_net_injection_invocation_from_contract,
    build_rho_net_replay_invocation_from_contracts, install_dovetail_rho_runtime_backend,
    run_normalized_par_for_oracle_and_read_runtime_values, PlannedRhoBackend, RhoBackendInvocation,
    RhoMachineInvocation,
};
use mettail_runtime::{
    Language, RuntimeBackend, RuntimeDovetailRunReport, RuntimeObservationValue,
    RuntimeReflectedSubterm, Term,
};

/// Reconstruct SwapDemo's augmented `LanguageDef` from the generated metadata's
/// `definition_source()` (the macro-time def, composition + auto-injection),
/// exactly as the Rho/Dovetail installer does for a real language, then plan its
/// Rho-default backend. Returns the planned backend and the plan's definition
/// fingerprint (which must equal the generated metadata fingerprint).
fn swap_demo_backend() -> (PlannedRhoBackend, String) {
    let source = SwapDemoLanguage
        .metadata()
        .definition_source()
        .expect("generated SwapDemoLanguage must expose its definition_source");
    let def = reconstruct_language_def(source)
        .expect("SwapDemoLanguage definition_source must reconstruct as a LanguageDef");

    // The four non-scalar `Proc` constructors are rejected by scalar lowering and
    // covered by the language-derived structural dispositions; SwapDemo has no
    // guards, so the flip gate passes with `NoGuardObligations`.
    let lowering = lower_language_def(&def);
    let requirements = RhoDefaultBackendRequirements {
        coverage: RhoCoverageEvidence::CoveredRejectedRules(suggest_rejected_rule_dispositions(
            &def, &lowering,
        )),
        guard_coverage: RhoGuardCoverageEvidence::NoGuardObligations,
    };
    let plan = plan_rho_default_backend(&def, requirements)
        .expect("Swap→Pair language must flip to the Rho backend");
    let fingerprint = plan.definition_fingerprint().to_string();
    (PlannedRhoBackend::from_plan(plan), fingerprint)
}

/// Rebuild a runtime-neutral report σ sub-term into the structural observation
/// value it must equal on OUT (both are the same `{ constructor, children }`
/// shape). Used to derive the expected Rho output from the report's OWN σ.
fn reflected_to_observation(subterm: &RuntimeReflectedSubterm) -> RuntimeObservationValue {
    RuntimeObservationValue::Term {
        constructor: subterm.constructor.clone(),
        children: subterm.children.iter().map(reflected_to_observation).collect(),
    }
}

/// A bare nullary σ sub-term, e.g. `A` or `B`, as the report carries it post-R-4.
fn nullary_subterm(constructor: &str) -> RuntimeReflectedSubterm {
    RuntimeReflectedSubterm { constructor: constructor.to_string(), children: Vec::new() }
}

#[tokio::test]
async fn dovetail_report_semantics_match_rho_machine_execution_for_swap() {
    mettail_runtime::clear_var_cache();
    let (backend, fingerprint) = swap_demo_backend();

    // Fingerprint coherence: the σ-receiver (installed from the reconstructed def)
    // and the σ-injection (which reflects with `metadata().definition_fingerprint()`)
    // must agree, or the receiver could not recognize the reflected σ.
    assert_eq!(
        SwapDemoLanguage.metadata().definition_fingerprint(),
        Some(fingerprint.as_str()),
        "planned backend fingerprint must equal the generated metadata fingerprint"
    );

    // The concrete term `Swap(A, B)`, built directly through the generated term
    // wrapper (no parse — sidesteps any keyword-`A`/`B` vs auto-`PVar` ambiguity).
    // `Swap(A, B) ≠ Pair(B, A)`, so a positive OUT observation is non-vacuous
    // evidence the rewrite fired.
    let term = SwapDemoTerm(Proc::Swap(Arc::new(Proc::A), Arc::new(Proc::B)));

    // (1) DOVETAIL REPORT SEMANTICS. The generated producer resolves + bare-ifies σ
    // (R-4); `Swap(A, B) → Pair(B, A)` saturates acyclically, so the report is
    // Complete.
    let report = SwapDemoLanguage::dovetail_report_for(&term, 64, 1_000_000)
        .expect("SwapDemo Dovetail report must compile");
    assert!(
        report.is_complete(),
        "the acyclic Swap→Pair reduction must report Complete, got {:?}",
        report.completeness
    );

    // Dovetail's structural match result: exactly one firing, rule `SwapStep`, with
    // σ = {x ↦ A, y ↦ B} — each constructor bare-ified to its source identity (R-4),
    // so it reflects identically to the σ-receiver's compiled RHS constructors.
    assert_eq!(
        report.rewrite_justifications.len(),
        1,
        "exactly one base rewrite fires for Swap(A, B)"
    );
    let justification = &report.rewrite_justifications[0];
    assert_eq!(justification.rule_label, "SwapStep", "the fired rule is SwapStep");
    let sigma: HashMap<&str, &RuntimeReflectedSubterm> = justification
        .sigma
        .iter()
        .map(|(name, subterm)| (name.as_str(), subterm))
        .collect();
    assert_eq!(*sigma["x"], nullary_subterm("A"), "Dovetail bound the LHS variable x ↦ A");
    assert_eq!(*sigma["y"], nullary_subterm("B"), "Dovetail bound the LHS variable y ↦ B");

    // (2) The generated σ-injection F-function reads that report and assembles the
    // closed injection `call` (reordering σ into the σ-receiver's LHS variable order
    // and reflecting each sub-term with the metadata fingerprint).
    let invocation = SwapDemoLanguage::rho_net_invocation_from_dovetail_to(&term, &report, "OUT")
        .expect("SwapDemo σ-injection must assemble from a complete report");
    assert_eq!(invocation.out_channel, "OUT");

    // The Epic-4 bridge adapter selects the INSTALLED-σ-receiver observation shape
    // (not the scalar `program()` shape), so the base rewrite actually fires.
    match build_rho_net_injection_invocation_from_contract(invocation.clone()) {
        RhoMachineInvocation::RunRhoNetWithCallAndObserveRuntimeValues { out_channel, .. } => {
            assert_eq!(out_channel, "OUT", "the bridge must preserve the out channel");
        },
        other => panic!("the Rho-net injection must map to RunRhoNet…, got {other:?}"),
    }

    // (3) RHO-MACHINE EXECUTION. Run the installed σ-receiver program ∥ call and
    // observe closed Rho ground values on OUT.
    let observation = backend
        .run_rho_net_with_call_and_observe_runtime_values(&invocation.call, &invocation.out_channel)
        .await
        .expect("the σ injection must execute on the Rho runtime");

    // Non-vacuity (the R-2 vacuity trap): the σ-receiver fired exactly once and left
    // exactly one value on OUT. A composition that reached no contract would be empty.
    assert_eq!(
        observation.observed_count(),
        1,
        "OUT must carry exactly one value — the σ-receiver must fire (got {:?})",
        observation.values
    );

    // EQUIVALENCE, checked against the report's OWN σ (not a hard-coded oracle): the
    // Rho machine must land `RHS(SwapStep) = Pair(y, x)` with Dovetail's σ applied,
    // i.e. `Pair(σ[y], σ[x])`. This is precisely "Dovetail report semantics" realized
    // by "Rho-machine execution".
    let expected_from_report = RuntimeObservationValue::Term {
        constructor: "Pair".to_string(),
        children: vec![reflected_to_observation(sigma["y"]), reflected_to_observation(sigma["x"])],
    };
    assert_eq!(
        observation.values[0], expected_from_report,
        "Rho execution must equal Pair(σ[y], σ[x]) — the report's RHS under its own σ"
    );

    // …and that normal form is concretely `Pair(B, A)`, non-vacuous against the input
    // `Swap(A, B)`.
    let pair_b_a = RuntimeObservationValue::Term {
        constructor: "Pair".to_string(),
        children: vec![
            RuntimeObservationValue::Term { constructor: "B".to_string(), children: Vec::new() },
            RuntimeObservationValue::Term { constructor: "A".to_string(), children: Vec::new() },
        ],
    };
    assert_eq!(
        observation.values[0], pair_b_a,
        "the Rho machine reduced Swap(A, B) to the reflected normal form Pair(B, A)"
    );
}

/// Stage 0 multi-firing replay: a multi-redex term (`Pair(Swap(A, B), Swap(B, A))`)
/// yields TWO distinct base-rewrite firings in one Dovetail report, and the replay
/// driver fires each as its own atomic COMM against the same installed σ-receiver
/// program, observing both `⟦R⟧σ`. This generalizes the single-firing bridge above:
/// every non-semantic-predicate rewrite of a multi-step reduction executes as a
/// `c(ℓ)` COMM on the Rho machine.
#[tokio::test]
async fn multi_firing_replay_fires_each_redex_as_its_own_comm() {
    mettail_runtime::clear_var_cache();
    let (backend, _fingerprint) = swap_demo_backend();

    // Two DISTINCT redexes — structurally-equal Swaps would hash-cons to one
    // e-class and fire once, so use `Swap(A, B)` and `Swap(B, A)`.
    let term = SwapDemoTerm(Proc::Pair(
        Arc::new(Proc::Swap(Arc::new(Proc::A), Arc::new(Proc::B))),
        Arc::new(Proc::Swap(Arc::new(Proc::B), Arc::new(Proc::A))),
    ));

    let report = SwapDemoLanguage::dovetail_report_for(&term, 64, 1_000_000)
        .expect("SwapDemo multi-redex Dovetail report must compile");
    assert!(report.is_complete(), "the acyclic multi-redex reduction must report Complete");
    assert_eq!(
        report.rewrite_justifications.len(),
        2,
        "Pair(Swap(A,B), Swap(B,A)) fires two distinct SwapSteps, got {:?}",
        report.rewrite_justifications
    );

    // One σ-injection per firing (distinct out channel each), plus the report-derived
    // expected `RHS(SwapStep) = Pair(σ[y], σ[x])` for that firing's own σ.
    let mut firings = Vec::new();
    let mut expected = Vec::new();
    for i in 0..report.rewrite_justifications.len() {
        let out = format!("OUT{i}");
        let invocation =
            SwapDemoLanguage::rho_net_invocation_from_dovetail_to_firing(&term, &report, &out, i)
                .expect("per-firing σ-injection must assemble from the complete report");
        assert_eq!(invocation.out_channel, out, "each firing keeps its own out channel");
        let sigma: HashMap<&str, &RuntimeReflectedSubterm> = report.rewrite_justifications[i]
            .sigma
            .iter()
            .map(|(name, subterm)| (name.as_str(), subterm))
            .collect();
        expected.push(RuntimeObservationValue::Term {
            constructor: "Pair".to_string(),
            children: vec![
                reflected_to_observation(sigma["y"]),
                reflected_to_observation(sigma["x"]),
            ],
        });
        firings.push((invocation.call, invocation.out_channel));
    }

    // Replay: install the σ-receiver program ONCE, fire each firing as its own atomic
    // COMM, and observe every firing's `⟦R⟧σ` in firing order.
    let observation = backend
        .run_rho_net_replay_and_observe_runtime_values(&firings)
        .await
        .expect("the multi-firing replay must execute on the Rho runtime");

    assert_eq!(
        observation.observed_count(),
        2,
        "each firing lands exactly one value on its out channel — both must fire (got {:?})",
        observation.values
    );
    assert_eq!(
        observation.values, expected,
        "each replayed firing must land Pair(σ[y], σ[x]) for its own σ, in firing order"
    );

    // Concretely: Swap(A,B) → Pair(B,A) and Swap(B,A) → Pair(A,B), non-vacuous.
    let pair = |a: &str, b: &str| RuntimeObservationValue::Term {
        constructor: "Pair".to_string(),
        children: vec![
            RuntimeObservationValue::Term { constructor: a.to_string(), children: Vec::new() },
            RuntimeObservationValue::Term { constructor: b.to_string(), children: Vec::new() },
        ],
    };
    assert!(observation.values.contains(&pair("B", "A")), "Swap(A,B) replayed to Pair(B,A)");
    assert!(observation.values.contains(&pair("A", "B")), "Swap(B,A) replayed to Pair(A,B)");
}

/// Stage 0 default-wire: the GENERATED replay wiring end-to-end. The generated
/// `rho_net_replay_invocation_from_dovetail_to` builds one σ-injection per firing,
/// `build_rho_net_replay_invocation_from_contracts` maps them to the replay
/// invocation, and the driver fires each as its own atomic COMM. This is the
/// production wiring a multi-redex reduction runs through — capability-gated by
/// the installed σ-receiver program (fail-closed at `installed_rho_net_program_par`).
#[tokio::test]
async fn generated_replay_wiring_fires_every_firing_as_a_comm() {
    mettail_runtime::clear_var_cache();
    let (backend, _fingerprint) = swap_demo_backend();

    let term = SwapDemoTerm(Proc::Pair(
        Arc::new(Proc::Swap(Arc::new(Proc::A), Arc::new(Proc::B))),
        Arc::new(Proc::Swap(Arc::new(Proc::B), Arc::new(Proc::A))),
    ));
    let report = SwapDemoLanguage::dovetail_report_for(&term, 64, 1_000_000)
        .expect("multi-redex report must compile");

    // Generated wiring: one injection per firing, then the replay invocation.
    let injections =
        SwapDemoLanguage::rho_net_replay_invocation_from_dovetail_to(&term, &report, "OUT")
            .expect("the generated replay method must build one injection per firing");
    assert_eq!(injections.len(), 2, "two firings ⇒ two σ-injections");

    let firings = match build_rho_net_replay_invocation_from_contracts(injections) {
        RhoMachineInvocation::RunRhoNetReplayAndObserveRuntimeValues { firings } => firings,
        other => panic!("the replay bridge must map to RunRhoNetReplay…, got {other:?}"),
    };

    let observation = backend
        .run_rho_net_replay_and_observe_runtime_values(&firings)
        .await
        .expect("the generated replay wiring must execute on the Rho runtime");
    assert_eq!(observation.observed_count(), 2, "both firings fire as COMMs");

    let pair = |a: &str, b: &str| RuntimeObservationValue::Term {
        constructor: "Pair".to_string(),
        children: vec![
            RuntimeObservationValue::Term { constructor: a.to_string(), children: Vec::new() },
            RuntimeObservationValue::Term { constructor: b.to_string(), children: Vec::new() },
        ],
    };
    assert!(observation.values.contains(&pair("B", "A")));
    assert!(observation.values.contains(&pair("A", "B")));
}

/// A normal-form term replays to NOTHING (no redex → no COMM) — a valid state,
/// distinct from the single-firing `rho_net_invocation_from_dovetail_to`, which
/// fails closed when nothing fires. The replay of an already-normal term is a
/// no-op, so the whole reduction still executes only as COMMs (zero of them).
#[tokio::test]
async fn generated_replay_wiring_is_empty_for_a_normal_form() {
    mettail_runtime::clear_var_cache();
    let (backend, _fingerprint) = swap_demo_backend();

    let term = SwapDemoTerm(Proc::Pair(Arc::new(Proc::A), Arc::new(Proc::B)));
    let report = SwapDemoLanguage::dovetail_report_for(&term, 64, 1_000_000)
        .expect("normal-form report must compile");

    let injections =
        SwapDemoLanguage::rho_net_replay_invocation_from_dovetail_to(&term, &report, "OUT")
            .expect("replay of a normal form is an empty sequence, not an error");
    assert!(injections.is_empty(), "a normal form has no firing to replay");

    let firings = match build_rho_net_replay_invocation_from_contracts(injections) {
        RhoMachineInvocation::RunRhoNetReplayAndObserveRuntimeValues { firings } => firings,
        other => panic!("the replay bridge must map to RunRhoNetReplay…, got {other:?}"),
    };
    let observation = backend
        .run_rho_net_replay_and_observe_runtime_values(&firings)
        .await
        .expect("an empty replay is a valid no-op");
    assert_eq!(observation.observed_count(), 0, "no redex ⇒ no COMM ⇒ no observation");
}

#[tokio::test]
async fn injection_fails_closed_when_no_rewrite_fires() {
    mettail_runtime::clear_var_cache();

    // `Pair(A, B)` is already a normal form — no base rewrite matches it, so the
    // complete report carries no rewrite justification.
    let term = SwapDemoTerm(Proc::Pair(Arc::new(Proc::A), Arc::new(Proc::B)));
    let report = SwapDemoLanguage::dovetail_report_for(&term, 64, 1_000_000)
        .expect("a normal-form term still produces a complete report");
    assert!(report.is_complete(), "a normal form saturates immediately");
    assert!(
        report.rewrite_justifications.is_empty(),
        "no redex ⇒ no firing ⇒ no σ justification (got {:?})",
        report.rewrite_justifications
    );

    // With nothing to inject, the generated F-function must fail closed rather than
    // fabricate a call against the σ-receiver.
    let error = SwapDemoLanguage::rho_net_invocation_from_dovetail_to(&term, &report, "OUT")
        .expect_err("with no firing the injection must fail closed");
    assert!(
        error.contains("no rewrite justification at firing index"),
        "the fail-closed error must name the missing justification, got: {error}"
    );
}

/// Stage 1 M1c: the first genuine IN-RHO match. The SwapStep LHS `Swap(x, y)` is
/// compiled to the positional set automaton, serialized to an `sa:`-receiver
/// network, and composed with the σ-receiver program and the spread subject
/// `Swap(A, B)`. The automaton matches the spread ON THE RHOLANG INTERPRETER (the
/// τ `sa:` COMMs) — the host does NOT inject σ here — and on accept fires the
/// σ-receiver, landing `Pair(B, A)` on OUT. Because `Swap(A, B) ≠ Pair(B, A)`, a
/// positive OUT is non-vacuous evidence the match + firing happened in Rho, and
/// (the point of this test) the RSpace reducer validates the automaton's De Bruijn
/// / `locally_free` frame end-to-end.
#[tokio::test]
async fn m1_matches_swap_in_rho_and_fires_the_rewrite() {
    mettail_runtime::clear_var_cache();
    let (backend, fingerprint) = swap_demo_backend();

    // The SwapStep σ-receiver SOURCE channel; the automaton's accept channel MUST
    // equal it, sourced from the SAME rho_net_injection_sites derivation (coherence).
    let source = SwapDemoLanguage
        .metadata()
        .definition_source()
        .expect("SwapDemo exposes its definition source");
    let def = reconstruct_language_def(source).expect("SwapDemo def reconstructs");
    let site = rho_net_injection_sites(&def)
        .into_iter()
        .find(|site| site.rule_label == "SwapStep")
        .expect("the SwapStep base rewrite has a σ-receiver site");

    // Compile the SwapStep LHS `Swap(x, y)` into the positional automaton, then
    // serialize it to its in-Rho `sa:`-receiver network.
    let automaton = SetAutomaton::compile_structural([(
        PatternId(0),
        Pattern::app("Swap".to_string(), vec![Pattern::var("x"), Pattern::var("y")]),
    )])
    .expect("Swap(x, y) compiles to a positional automaton");
    let network =
        automaton_receiver_network_par(&automaton.view(), "site0", &site.channel, "OUT", &fingerprint)
            .expect("the automaton serializes to a receiver network");

    // The subject `Swap(A, B)` spread across per-location channels (M0).
    let subject = spread_term_par(
        &GroundTerm::new(
            "Swap",
            vec![GroundTerm::new("A", Vec::new()), GroundTerm::new("B", Vec::new())],
        ),
        &fingerprint,
        "site0",
    );

    // σ-receiver ∥ (automaton ∥ subject): the automaton matches the spread IN RHO
    // and on accept fires the σ-receiver. run_rho_net_with_call composes the
    // installed σ-receiver program with this call.
    let call = network.append(subject);
    let observation = backend
        .run_rho_net_with_call_and_observe_runtime_values(&call, "OUT")
        .await
        .expect("the in-Rho match + firing must execute on the Rho runtime");

    assert_eq!(
        observation.observed_count(),
        1,
        "the in-Rho automaton must match Swap(A, B) and fire exactly once (got {:?})",
        observation.values
    );
    let pair_b_a = RuntimeObservationValue::Term {
        constructor: "Pair".to_string(),
        children: vec![
            RuntimeObservationValue::Term { constructor: "B".to_string(), children: Vec::new() },
            RuntimeObservationValue::Term { constructor: "A".to_string(), children: Vec::new() },
        ],
    };
    assert_eq!(
        observation.values[0], pair_b_a,
        "Swap(A, B) matched IN RHO and fired the rewrite → Pair(B, A)"
    );
}

/// Compile the SwapStep LHS `Swap(x, y)` into its in-Rho `sa:`-receiver network,
/// wired to the SwapStep σ-receiver's own source channel (coherence).
fn swap_step_network(fingerprint: &str) -> models::rhoapi::Par {
    let source = SwapDemoLanguage.metadata().definition_source().unwrap();
    let def = reconstruct_language_def(source).unwrap();
    let site = rho_net_injection_sites(&def)
        .into_iter()
        .find(|site| site.rule_label == "SwapStep")
        .expect("the SwapStep base rewrite has a σ-receiver site");
    let automaton = SetAutomaton::compile_structural([(
        PatternId(0),
        Pattern::app("Swap".to_string(), vec![Pattern::var("x"), Pattern::var("y")]),
    )])
    .expect("Swap(x, y) compiles");
    automaton_receiver_network_par(&automaton.view(), "site0", &site.channel, "OUT", fingerprint)
        .expect("the automaton serializes")
}

/// A test observer for the automaton's accept:
/// `for(y_0,…,y_{k-1}, o <- accept_channel){ o!(y_0) | … | o!(y_{k-1}) }` — it
/// forwards each received σ slot to the out channel the accept named, so a match's
/// σ can be observed WITHOUT a language σ-receiver (which exists only for SwapDemo).
/// De Bruijn (the `k+1` binds are `[y_0,…,y_{k-1}, o]`): `o = BoundVar(0)`,
/// `y_i = BoundVar(arity-i)`; the body is closed by the receive (`locally_free = {}`).
fn sigma_echo_receiver(accept_channel: &str, arity: usize) -> models::rhoapi::Par {
    use models::create_bit_vector;
    use models::rhoapi::{Par, ReceiveBind};
    use models::rust::utils::{
        new_boundvar_par, new_freevar_par, new_gstring_par, new_receive_par, new_send_par,
    };

    let mut body = Par::default();
    for i in 0..arity {
        let yi = arity - i; // y_i = BoundVar(arity - i)
        let send = new_send_par(
            new_boundvar_par(0, create_bit_vector(&[0]), false), // channel o = BoundVar(0)
            vec![new_boundvar_par(yi as i32, create_bit_vector(&[yi]), false)],
            false,
            create_bit_vector(&[0, yi]),
            false,
            create_bit_vector(&[0, yi]),
            false,
        );
        body = body.append(send);
    }
    // The body references BoundVar(0..=arity) (o and every y_i); set it explicitly so
    // the receive binds a body with the correct free set.
    if arity > 0 {
        body.locally_free = create_bit_vector(&(0..=arity).collect::<Vec<_>>());
    }
    new_receive_par(
        vec![ReceiveBind {
            patterns: (0..arity + 1)
                .map(|i| new_freevar_par(i as i32, Vec::new()))
                .collect(),
            source: Some(new_gstring_par(accept_channel.to_string(), Vec::new(), false)),
            remainder: None,
            free_count: (arity + 1) as i32,
        }],
        body,
        false,
        false,
        (arity + 1) as i32,
        Vec::new(),
        false,
        Vec::new(),
        false,
    )
}

/// Stage 1 M1: the in-Rho match GENERALIZES beyond the binary Swap case, at runtime.
/// `Triple(x, y, z)` matched against `Triple(A, B, C)` ON the interpreter binds
/// σ = [⟦A⟧, ⟦B⟧, ⟦C⟧]; the σ-echo forwards those slots to OUT (no σ-receiver needed).
/// The arity-3 runtime companion of `m1_matches_swap…` (arity 2); it also exercises
/// the σ-echo observer that the property-based oracle reuses.
#[tokio::test]
async fn m1_matches_a_ternary_pattern_in_rho() {
    mettail_runtime::clear_var_cache();
    let (_backend, fingerprint) = swap_demo_backend();

    let automaton = SetAutomaton::compile_structural([(
        PatternId(0),
        Pattern::app(
            "Triple".to_string(),
            vec![Pattern::var("x"), Pattern::var("y"), Pattern::var("z")],
        ),
    )])
    .expect("Triple(x, y, z) compiles");
    let network =
        automaton_receiver_network_par(&automaton.view(), "site0", "MATCH", "OUT", &fingerprint)
            .expect("the ternary automaton serializes");

    let subject = spread_term_par(
        &GroundTerm::new(
            "Triple",
            vec![
                GroundTerm::new("A", Vec::new()),
                GroundTerm::new("B", Vec::new()),
                GroundTerm::new("C", Vec::new()),
            ],
        ),
        &fingerprint,
        "site0",
    );

    let echo = sigma_echo_receiver("MATCH", 3);
    let program = echo.append(network).append(subject);
    let mut observed = run_normalized_par_for_oracle_and_read_runtime_values(&program, "OUT")
        .await
        .expect("the in-Rho ternary match must execute");

    // The echo's parallel sends land on OUT in nondeterministic order — compare as a
    // multiset by constructor.
    observed.sort_by_key(|value| match value {
        RuntimeObservationValue::Term { constructor, .. } => constructor.clone(),
        _ => "?".to_string(),
    });
    let expected = vec![
        RuntimeObservationValue::Term { constructor: "A".to_string(), children: Vec::new() },
        RuntimeObservationValue::Term { constructor: "B".to_string(), children: Vec::new() },
        RuntimeObservationValue::Term { constructor: "C".to_string(), children: Vec::new() },
    ];
    assert_eq!(observed, expected, "Triple(A, B, C) matched in Rho binds σ = [A, B, C]");
}

/// Stage 2: `f(x, x)` matched against `f(A, A)` ON the interpreter — the `eq:` consistency
/// join's condition `EEq(h0, h1)` holds (equal head tags), so the guarded consume commits and
/// the accept binds the single distinct-var σ = [⟦A⟧]. The σ-echo forwards it to OUT.
#[tokio::test]
async fn nonlinear_matches_equal_args_in_rho() {
    mettail_runtime::clear_var_cache();
    let (_backend, fingerprint) = swap_demo_backend();

    let automaton = SetAutomaton::compile_structural([(
        PatternId(0),
        Pattern::app("f".to_string(), vec![Pattern::var("x"), Pattern::var("x")]),
    )])
    .expect("f(x, x) compiles");
    let network =
        automaton_receiver_network_par(&automaton.view(), "site0", "MATCH", "OUT", &fingerprint)
            .expect("f(x, x) serializes with the eq: guard");

    let subject = spread_term_par(
        &GroundTerm::new(
            "f",
            vec![GroundTerm::new("A", Vec::new()), GroundTerm::new("A", Vec::new())],
        ),
        &fingerprint,
        "site0",
    );
    // k = 1 distinct variable (x), so the accept sends one σ slot.
    let program = sigma_echo_receiver("MATCH", 1).append(network).append(subject);
    let observed = run_normalized_par_for_oracle_and_read_runtime_values(&program, "OUT")
        .await
        .expect("the in-Rho non-linear match must execute");

    let expected =
        vec![RuntimeObservationValue::Term { constructor: "A".to_string(), children: Vec::new() }];
    assert_eq!(observed, expected, "f(A, A) matched in Rho (equal args) binds σ = [A]");
}

/// Stage 2 reject-safety: `f(x, x)` against `f(A, B)` — the condition `EEq(h0, h1)` is false
/// (distinct head tags), so the reducer's `check_commit` VETOES the whole join consume
/// (mirroring `merge_substs → None`): no accept fires, nothing lands on OUT. The RSpace reducer
/// is the true reject-safety oracle.
#[tokio::test]
async fn nonlinear_rejects_unequal_args_in_rho() {
    mettail_runtime::clear_var_cache();
    let (_backend, fingerprint) = swap_demo_backend();

    let automaton = SetAutomaton::compile_structural([(
        PatternId(0),
        Pattern::app("f".to_string(), vec![Pattern::var("x"), Pattern::var("x")]),
    )])
    .expect("f(x, x) compiles");
    let network =
        automaton_receiver_network_par(&automaton.view(), "site0", "MATCH", "OUT", &fingerprint)
            .expect("f(x, x) serializes with the eq: guard");

    let subject = spread_term_par(
        &GroundTerm::new(
            "f",
            vec![GroundTerm::new("A", Vec::new()), GroundTerm::new("B", Vec::new())],
        ),
        &fingerprint,
        "site0",
    );
    let program = sigma_echo_receiver("MATCH", 1).append(network).append(subject);
    let observed = run_normalized_par_for_oracle_and_read_runtime_values(&program, "OUT")
        .await
        .expect("the in-Rho non-linear match must execute");

    assert!(
        observed.is_empty(),
        "f(A, B) does NOT match — the eq: guard vetoes reject-safely (got {observed:?})"
    );
}

/// Stage AC1: the AC connective bag pattern MATCHES the process-`Par` carrier soup ON the
/// interpreter. A HashBag operand `PPar{A, B}` reflects to a two-send soup (AC0); the receiver
/// `for( @"ac:PPar"!(x) | rest  <- c_ac ){ OUT!(x) }` (built from `ac_bag_pattern`) matches it
/// ORDER-INDEPENDENTLY — binding `x` to ONE element (any) and `rest` to the residual — and
/// echoes the matched element to OUT: the order-independent multiset match in Rho.
#[tokio::test]
async fn ac_bag_pattern_matches_the_process_soup_in_rho() {
    use models::create_bit_vector;
    use models::rhoapi::ReceiveBind;
    use models::rust::utils::{new_boundvar_par, new_gstring_par, new_receive_par, new_send_par};

    mettail_runtime::clear_var_cache();
    let (_backend, fingerprint) = swap_demo_backend();

    // The subject: ⟦PPar{A, B}⟧ = the process-Par carrier soup (AC0).
    let soup = reflect_ground_term_par(
        &GroundTerm::collection(
            CollectionType::HashBag,
            "PPar",
            vec![GroundTerm::nullary("A"), GroundTerm::nullary("B")],
        ),
        &fingerprint,
    );

    // The receiver: for(<ac_bag_pattern PPar/1> <- c_ac){ OUT!(x) }. The pattern binds the
    // element x = FreeVar(0) and rest = FreeVar(1); at the body's depth 2 the element is
    // BoundVar(1) (reverse De Bruijn over the bind's 2 free vars).
    let pattern = ac_bag_pattern("PPar", 1);
    let body = new_send_par(
        new_gstring_par("OUT".to_string(), Vec::new(), false),
        vec![new_boundvar_par(1, create_bit_vector(&[1]), false)],
        false,
        create_bit_vector(&[1]),
        false,
        create_bit_vector(&[1]),
        false,
    );
    let receiver = new_receive_par(
        vec![ReceiveBind {
            patterns: vec![pattern],
            source: Some(new_gstring_par("c_ac".to_string(), Vec::new(), false)),
            remainder: None,
            free_count: 2,
        }],
        body,
        false,
        false,
        2,
        Vec::new(),
        false,
        Vec::new(),
        false,
    );

    // The injection: c_ac!(⟦bag⟧).
    let injection = new_send_par(
        new_gstring_par("c_ac".to_string(), Vec::new(), false),
        vec![soup],
        false,
        Vec::new(),
        false,
        Vec::new(),
        false,
    );

    let program = receiver.append(injection);
    let observed = run_normalized_par_for_oracle_and_read_runtime_values(&program, "OUT")
        .await
        .expect("the in-Rho AC match must execute");

    // One element is matched (any, order-independent) and echoed; it is A or B.
    assert_eq!(observed.len(), 1, "the connective pattern matches one element (got {observed:?})");
    let matched = observation_constructor(&observed[0]);
    assert!(matched == "A" || matched == "B", "matched element is a bag element, got {matched}");
}

/// Stage AC1c: the AC receiver FIRES on the DYNAMIC out channel the injection provides — the
/// σ-receiver shape. The bind `[<collection pattern>, out]` over `c_ac`, with the injection
/// `c_ac!(⟦PPar{A,B}⟧, @"OUT")`, binds the matched element `x` and the out channel, then fires
/// `x` on `out` (= @"OUT"). AC1b's match extended to the σ-receiver's dynamic-out firing.
#[tokio::test]
async fn ac_receiver_fires_the_matched_element_on_the_dynamic_out() {
    use models::create_bit_vector;
    use models::rhoapi::ReceiveBind;
    use models::rust::utils::{
        new_boundvar_par, new_freevar_par, new_gstring_par, new_receive_par, new_send_par,
    };

    mettail_runtime::clear_var_cache();
    let (_backend, fingerprint) = swap_demo_backend();

    let soup = reflect_ground_term_par(
        &GroundTerm::collection(
            CollectionType::HashBag,
            "PPar",
            vec![GroundTerm::nullary("A"), GroundTerm::nullary("B")],
        ),
        &fingerprint,
    );

    // Bind [collection pattern (element FreeVar(0), rest FreeVar(1)), out FreeVar(2)]. The body
    // fires on out = BoundVar(0) the element = BoundVar(2) (reverse De Bruijn, 3 bind free vars).
    let pattern = ac_bag_pattern("PPar", 1);
    let out_pattern = new_freevar_par(2, Vec::new());
    let body = new_send_par(
        new_boundvar_par(0, create_bit_vector(&[0]), false),
        vec![new_boundvar_par(2, create_bit_vector(&[2]), false)],
        false,
        create_bit_vector(&[0, 2]),
        false,
        create_bit_vector(&[0, 2]),
        false,
    );
    let receiver = new_receive_par(
        vec![ReceiveBind {
            patterns: vec![pattern, out_pattern],
            source: Some(new_gstring_par("c_ac".to_string(), Vec::new(), false)),
            remainder: None,
            free_count: 3,
        }],
        body,
        false,
        false,
        3,
        Vec::new(),
        false,
        Vec::new(),
        false,
    );

    // c_ac!(⟦bag⟧, @"OUT").
    let injection = new_send_par(
        new_gstring_par("c_ac".to_string(), Vec::new(), false),
        vec![soup, new_gstring_par("OUT".to_string(), Vec::new(), false)],
        false,
        Vec::new(),
        false,
        Vec::new(),
        false,
    );

    let program = receiver.append(injection);
    let observed = run_normalized_par_for_oracle_and_read_runtime_values(&program, "OUT")
        .await
        .expect("the in-Rho AC firing must execute");

    assert_eq!(observed.len(), 1, "the AC receiver fires once on the dynamic out (got {observed:?})");
    let fired = observation_constructor(&observed[0]);
    assert!(fired == "A" || fired == "B", "fired the matched element, got {fired}");
}

/// Stage AC1d: the codegen `ac_sigma_receiver_par` builds a WORKING AC receiver. Building the
/// receiver via the codegen fn (not hand-built) + injecting `c_ac!(⟦PPar{A,B}⟧, @"OUT")` fires
/// the element σ (rhs = element `BoundVar(2)`) on the out channel → OUT = [A or B], proving the
/// fn packages the verified receiver (pattern + out + body + De Bruijn) correctly.
#[tokio::test]
async fn ac_sigma_receiver_par_builds_a_working_receiver() {
    use models::create_bit_vector;
    use models::rust::utils::{new_boundvar_par, new_gstring_par, new_send_par};

    mettail_runtime::clear_var_cache();
    let (_backend, fingerprint) = swap_demo_backend();

    let soup = reflect_ground_term_par(
        &GroundTerm::collection(
            CollectionType::HashBag,
            "PPar",
            vec![GroundTerm::nullary("A"), GroundTerm::nullary("B")],
        ),
        &fingerprint,
    );

    // rhs = the element σ (BoundVar(k+1-0) = BoundVar(2) for k=1) — fired on out by the receiver.
    let rhs = new_boundvar_par(2, create_bit_vector(&[2]), false);
    let receiver = ac_sigma_receiver_par(
        "PPar",
        1,
        rhs,
        new_gstring_par("c_ac".to_string(), Vec::new(), false),
    );
    let injection = new_send_par(
        new_gstring_par("c_ac".to_string(), Vec::new(), false),
        vec![soup, new_gstring_par("OUT".to_string(), Vec::new(), false)],
        false,
        Vec::new(),
        false,
        Vec::new(),
        false,
    );

    let program = receiver.append(injection);
    let observed = run_normalized_par_for_oracle_and_read_runtime_values(&program, "OUT")
        .await
        .expect("the codegen AC receiver must fire");

    assert_eq!(observed.len(), 1, "the codegen AC receiver fires once (got {observed:?})");
    let fired = observation_constructor(&observed[0]);
    assert!(fired == "A" || fired == "B", "fired the matched element, got {fired}");
}

/// Multiset sort key for observation comparison (the σ-echo's parallel sends land on
/// OUT in nondeterministic order).
fn observation_constructor(value: &RuntimeObservationValue) -> String {
    match value {
        RuntimeObservationValue::Term { constructor, .. } => constructor.clone(),
        _ => "?".to_string(),
    }
}

/// The [Swap, Pair] multi-pattern automaton, accepting to `MATCH_SWAP` / `MATCH_PAIR`.
fn swap_pair_network(fingerprint: &str) -> models::rhoapi::Par {
    let automaton = SetAutomaton::compile_structural([
        (
            PatternId(0),
            Pattern::app("Swap".to_string(), vec![Pattern::var("x"), Pattern::var("y")]),
        ),
        (
            PatternId(1),
            Pattern::app("Pair".to_string(), vec![Pattern::var("a"), Pattern::var("b")]),
        ),
    ])
    .expect("[Swap, Pair] compiles");
    let targets = [
        AutomatonAcceptTarget {
            pattern: PatternId(0),
            accept_channel: "MATCH_SWAP".to_string(),
            out_channel: "OUT".to_string(),
        },
        AutomatonAcceptTarget {
            pattern: PatternId(1),
            accept_channel: "MATCH_PAIR".to_string(),
            out_channel: "OUT".to_string(),
        },
    ];
    multi_pattern_receiver_network_par(&automaton.view(), "site0", &targets, fingerprint)
        .expect("the multi-pattern network serializes")
}

/// Stage 1 M2 — the multi-pattern Match router dispatches to the RIGHT pattern, in Rho.
/// One [Swap, Pair] network; a `Swap(A, B)` subject fires ONLY the Swap accept (σ=[A, B]
/// forwarded to OUT by its echo), and the Pair case never fires (no Pair spread), so OUT
/// carries exactly [A, B] — evidence the router discriminates on the head tag in Rho.
#[tokio::test]
async fn m2_dispatches_to_the_matching_pattern_in_rho() {
    mettail_runtime::clear_var_cache();
    let (_backend, fingerprint) = swap_demo_backend();

    let network = swap_pair_network(&fingerprint);
    let echoes = sigma_echo_receiver("MATCH_SWAP", 2).append(sigma_echo_receiver("MATCH_PAIR", 2));
    let subject = spread_term_par(
        &GroundTerm::new(
            "Swap",
            vec![GroundTerm::new("A", Vec::new()), GroundTerm::new("B", Vec::new())],
        ),
        &fingerprint,
        "site0",
    );
    let program = echoes.append(network).append(subject);
    let mut observed = run_normalized_par_for_oracle_and_read_runtime_values(&program, "OUT")
        .await
        .expect("the in-Rho multi-pattern match executes");

    observed.sort_by_key(observation_constructor);
    let expected = vec![
        RuntimeObservationValue::Term { constructor: "A".to_string(), children: Vec::new() },
        RuntimeObservationValue::Term { constructor: "B".to_string(), children: Vec::new() },
    ];
    assert_eq!(
        observed, expected,
        "only the Swap case fires on a Swap subject (Pair stays silent)"
    );
}

/// Stage 1 M2 — the O3 fan-out: two rules with the same LHS `Swap(x, y)` share ONE
/// children subtree and announce in PARALLEL to both rules' accept channels. A single
/// `Swap(A, B)` subject fires BOTH echoes, so OUT carries σ=[A, B] twice.
#[tokio::test]
async fn m2_o3_fan_out_fires_both_same_op_rules_in_rho() {
    mettail_runtime::clear_var_cache();
    let (_backend, fingerprint) = swap_demo_backend();

    let automaton = SetAutomaton::compile_structural([
        (
            PatternId(0),
            Pattern::app("Swap".to_string(), vec![Pattern::var("x"), Pattern::var("y")]),
        ),
        (
            PatternId(1),
            Pattern::app("Swap".to_string(), vec![Pattern::var("x"), Pattern::var("y")]),
        ),
    ])
    .expect("two same-op rules compile");
    let targets = [
        AutomatonAcceptTarget {
            pattern: PatternId(0),
            accept_channel: "MATCH1".to_string(),
            out_channel: "OUT".to_string(),
        },
        AutomatonAcceptTarget {
            pattern: PatternId(1),
            accept_channel: "MATCH2".to_string(),
            out_channel: "OUT".to_string(),
        },
    ];
    let network = multi_pattern_receiver_network_par(&automaton.view(), "site0", &targets, &fingerprint)
        .expect("the O3 fan-out network serializes");
    let echoes = sigma_echo_receiver("MATCH1", 2).append(sigma_echo_receiver("MATCH2", 2));
    let subject = spread_term_par(
        &GroundTerm::new(
            "Swap",
            vec![GroundTerm::new("A", Vec::new()), GroundTerm::new("B", Vec::new())],
        ),
        &fingerprint,
        "site0",
    );
    let program = echoes.append(network).append(subject);
    let mut observed = run_normalized_par_for_oracle_and_read_runtime_values(&program, "OUT")
        .await
        .expect("the in-Rho O3 fan-out executes");

    observed.sort_by_key(observation_constructor);
    let expected = vec![
        RuntimeObservationValue::Term { constructor: "A".to_string(), children: Vec::new() },
        RuntimeObservationValue::Term { constructor: "A".to_string(), children: Vec::new() },
        RuntimeObservationValue::Term { constructor: "B".to_string(), children: Vec::new() },
        RuntimeObservationValue::Term { constructor: "B".to_string(), children: Vec::new() },
    ];
    assert_eq!(observed, expected, "both same-op rules fire (σ=[A, B] announced twice)");
}

/// Stage 1 M1: no false-positive matches. The Swap automaton over a `Pair(A, B)`
/// subject must NOT accept — the root `Match` dispatches on the head tag, and
/// `Pair` ≠ `Swap`, so no accept send is emitted, the σ-receiver never fires, and
/// OUT stays empty. This is the negative half of the in-Rho match relation.
#[tokio::test]
async fn m1_does_not_match_a_non_matching_head_in_rho() {
    mettail_runtime::clear_var_cache();
    let (backend, fingerprint) = swap_demo_backend();

    let network = swap_step_network(&fingerprint);
    // The subject is Pair(A, B) — same arity as Swap(x, y), but a different head.
    let subject = spread_term_par(
        &GroundTerm::new(
            "Pair",
            vec![GroundTerm::new("A", Vec::new()), GroundTerm::new("B", Vec::new())],
        ),
        &fingerprint,
        "site0",
    );
    let call = network.append(subject);
    let observation = backend
        .run_rho_net_with_call_and_observe_runtime_values(&call, "OUT")
        .await
        .expect("the composition executes even when nothing matches");

    assert_eq!(
        observation.observed_count(),
        0,
        "a non-matching head (Pair ≠ Swap) must not fire the rewrite (got {:?})",
        observation.values
    );
}

/// Stage 3 piece 2: compiling SwapDemo's rules into the in-Rho matching ruleset yields
/// one automaton entry (the SwapStep base rewrite) whose accept channel IS the rule's
/// σ-receiver source (the coherence anchor) and whose fingerprint is the shared one;
/// nothing is deferred.
#[test]
fn stage3_swapdemo_ruleset_compiles_the_base_rewrite_coherently() {
    let source = SwapDemoLanguage
        .metadata()
        .definition_source()
        .expect("SwapDemo exposes its definition source");
    let def = reconstruct_language_def(source).expect("SwapDemo def reconstructs");
    let ruleset = compile_in_rho_matching_ruleset(&def);

    assert_eq!(ruleset.automaton.view().entry_count(), 1, "one base rewrite → one entry");
    assert!(ruleset.deferred.is_empty(), "SwapDemo has no deferred rewrites: {:?}", ruleset.deferred);
    assert_eq!(ruleset.accept_channels.len(), 1);

    // The accept channel equals the SwapStep σ-receiver source (the triad coherence).
    let site = rho_net_injection_sites(&def)
        .into_iter()
        .find(|s| s.rule_label == "SwapStep")
        .expect("SwapStep site");
    assert_eq!(ruleset.accept_channels[0].1, site.channel, "accept channel = σ-receiver source");

    // The compiled entry's root is the Swap constructor.
    let view = ruleset.automaton.view();
    match view.node(view.entry_root_state(0)) {
        AutomatonNode::App { op, .. } => assert_eq!(op, "Swap"),
        AutomatonNode::Var(_) => panic!("SwapStep LHS root must be an App"),
    }

    // One shared language fingerprint, coherent with the plan's.
    let (_backend, fingerprint) = swap_demo_backend();
    assert_eq!(ruleset.language_fingerprint, fingerprint, "one shared language fingerprint");
}

/// Stage 3 piece 3: the WHOLE chain from the DERIVED ruleset (not hand-built). Swap(A, B)
/// is matched in Rho by the compiled automaton over the spread — the host does NOT inject
/// σ — and fires the SwapStep σ-receiver → Pair(B, A). This is `m1_matches_swap` with the
/// automaton, accept channel, and spread ALL derived from SwapDemo's `LanguageDef`.
#[tokio::test]
async fn stage3_swapdemo_matches_and_fires_from_the_derived_ruleset() {
    mettail_runtime::clear_var_cache();
    let (backend, _fingerprint) = swap_demo_backend();
    let source = SwapDemoLanguage
        .metadata()
        .definition_source()
        .expect("SwapDemo exposes its definition source");
    let def = reconstruct_language_def(source).expect("SwapDemo def reconstructs");
    let ruleset = compile_in_rho_matching_ruleset(&def);

    let subject = GroundTerm::new(
        "Swap",
        vec![GroundTerm::new("A", Vec::new()), GroundTerm::new("B", Vec::new())],
    );
    let call = in_rho_match_call_par(&ruleset, &subject, "site0", "OUT")
        .expect("the derived ruleset serializes a match call");
    let observation = backend
        .run_rho_net_with_call_and_observe_runtime_values(&call, "OUT")
        .await
        .expect("the in-Rho match + firing must execute");

    assert_eq!(
        observation.observed_count(),
        1,
        "the derived ruleset matched Swap(A, B) in Rho and fired once (got {:?})",
        observation.values
    );
    let pair_b_a = RuntimeObservationValue::Term {
        constructor: "Pair".to_string(),
        children: vec![
            RuntimeObservationValue::Term { constructor: "B".to_string(), children: Vec::new() },
            RuntimeObservationValue::Term { constructor: "A".to_string(), children: Vec::new() },
        ],
    };
    assert_eq!(
        observation.values[0], pair_b_a,
        "Swap(A, B) matched from the derived ruleset → Pair(B, A)"
    );
}

/// Stage 3 piece 5: the WHOLE production default-backend stack. Install SwapDemo's
/// Dovetail+Rho backend with the SAME capability-gated in-Rho-match closure the repl's
/// `swapdemo_backed()` uses (the closure IS the production closure, re-instantiated — no
/// test-only wiring), then drive `Swap(A, B)` through `run_backend_report(RhoMachine, …)`.
/// The report → gate → ruleset → network‖spread → installed σ-receivers → OUT chain matches
/// in Rho and fires → Pair(B, A).
#[test]
fn stage3_swapdemo_default_backend_matches_in_rho_via_run_backend_report() {
    mettail_runtime::clear_var_cache();
    let (backend, _fingerprint) = swap_demo_backend();

    let language = install_dovetail_rho_runtime_backend(
        SwapDemoLanguage,
        backend,
        |term: &dyn Term| SwapDemoLanguage::dovetail_report_for(term, 64, 1_000_000),
        |term: &dyn Term| SwapDemoLanguage::dovetail_report_for(term, 64, 1_000_000),
        |term: &dyn Term,
         report: &RuntimeDovetailRunReport|
         -> Result<RhoBackendInvocation, String> {
            match SwapDemoLanguage::rho_net_match_invocation_from_dovetail_to(term, report, "OUT") {
                Ok(invocation) => Ok(RhoBackendInvocation::from(
                    build_rho_net_injection_invocation_from_contract(invocation),
                )),
                Err(_reject) => {
                    let injections = SwapDemoLanguage::rho_net_replay_invocation_from_dovetail_to(
                        term, report, "OUT",
                    )?;
                    Ok(RhoBackendInvocation::from(
                        build_rho_net_replay_invocation_from_contracts(injections),
                    ))
                },
            }
        },
    )
    .expect("SwapDemo Dovetail+Rho backend installs");

    let term = SwapDemoTerm(Proc::Swap(Arc::new(Proc::A), Arc::new(Proc::B)));

    // The match path (not the σ-replay fallback) admits this root-rooted redex.
    let report =
        SwapDemoLanguage::dovetail_report_for(&term, 64, 1_000_000).expect("SwapDemo report");
    assert!(
        SwapDemoLanguage::rho_net_match_invocation_from_dovetail_to(&term, &report, "OUT").is_ok(),
        "the in-Rho match invocation admits Swap(A, B)"
    );

    // The whole production stack via run_backend_report.
    let backend_report = language
        .run_backend_report(RuntimeBackend::RhoMachine, &term)
        .expect("run_backend_report on the RhoMachine");
    let observation = backend_report
        .observations_for_channel("OUT")
        .expect("an OUT observation");
    assert_eq!(observation.observed_count(), 1, "one firing observed on OUT");

    let pair_b_a = RuntimeObservationValue::Term {
        constructor: "Pair".to_string(),
        children: vec![
            RuntimeObservationValue::Term { constructor: "B".to_string(), children: Vec::new() },
            RuntimeObservationValue::Term { constructor: "A".to_string(), children: Vec::new() },
        ],
    };
    assert_eq!(
        observation.values[0], pair_b_a,
        "the default RhoMachine backend matched Swap(A, B) in Rho and fired → Pair(B, A)"
    );
}

#[test]
fn swap_demo_exposes_its_rho_net_program_directly() {
    // Epic 6 #2030: a generated language exposes its RhoNet planning artifact —
    // planned channels + rule identities — DIRECTLY via `rho_net_program()`,
    // without the caller reconstructing the `LanguageDef` by hand.
    let program =
        SwapDemoLanguage::rho_net_program().expect("SwapDemo exposes its RhoNet program");
    let swap_rule = program
        .rules
        .iter()
        .find(|rule| rule.label.as_deref() == Some("SwapStep"))
        .expect("the SwapStep base rewrite is a planned RhoNet rule");
    assert_eq!(swap_rule.kind, RhoNetRuleKind::BaseRewrite);
    assert!(
        !swap_rule.input_channels.is_empty(),
        "the planned σ-receiver rule carries a source channel"
    );
    assert!(!program.channels.is_empty(), "the program plans at least one channel");
}

/// Property-based Stage 0 verification: the replay driver faithfully reproduces
/// the Dovetail report's per-firing `RHS[σ]` for ARBITRARY well-formed SwapDemo
/// terms — however many redexes a term has (including zero), every one executes
/// as its own atomic COMM and lands exactly its report-derived normal form, with
/// no spurious value. This exercises the σ-reflection/injection round-trip across
/// the full space of σ shapes (nested terms ⇒ nested σ), not just one example.
mod replay_property {
    use super::*;
    use proptest::prelude::*;

    /// A bounded strategy for well-formed SwapDemo `Proc` terms: `A`/`B` leaves and
    /// binary `Swap`/`Pair` nodes, to `max_depth` levels.
    fn arb_swap_proc(max_depth: u32) -> impl Strategy<Value = Proc> {
        let leaf = prop_oneof![Just(Proc::A), Just(Proc::B)];
        leaf.prop_recursive(max_depth, 32, 2, |inner| {
            prop_oneof![
                (inner.clone(), inner.clone())
                    .prop_map(|(l, r)| Proc::Swap(Arc::new(l), Arc::new(r))),
                (inner.clone(), inner).prop_map(|(l, r)| Proc::Pair(Arc::new(l), Arc::new(r))),
            ]
        })
    }

    proptest! {
        #![proptest_config(ProptestConfig { cases: 24, ..ProptestConfig::default() })]

        #[test]
        fn replay_observations_equal_report_rhs_for_arbitrary_swap_terms(
            proc in arb_swap_proc(3),
        ) {
            mettail_runtime::clear_var_cache();
            let (backend, _fingerprint) = swap_demo_backend();
            let term = SwapDemoTerm(proc);

            let report = SwapDemoLanguage::dovetail_report_for(&term, 512, 8_000_000)
                .expect("SwapDemo report must compile");
            prop_assert!(report.is_complete(), "the acyclic Swap→Pair reduction must complete");

            // The report-derived expected observation per firing, in firing order.
            let expected: Vec<RuntimeObservationValue> = report
                .rewrite_justifications
                .iter()
                .map(|justification| {
                    let sigma: HashMap<&str, &RuntimeReflectedSubterm> = justification
                        .sigma
                        .iter()
                        .map(|(name, subterm)| (name.as_str(), subterm))
                        .collect();
                    RuntimeObservationValue::Term {
                        constructor: "Pair".to_string(),
                        children: vec![
                            reflected_to_observation(sigma["y"]),
                            reflected_to_observation(sigma["x"]),
                        ],
                    }
                })
                .collect();

            let injections =
                SwapDemoLanguage::rho_net_replay_invocation_from_dovetail_to(&term, &report, "OUT")
                    .expect("generated replay wiring must build one injection per firing");
            prop_assert_eq!(injections.len(), expected.len());

            let firings = match build_rho_net_replay_invocation_from_contracts(injections) {
                RhoMachineInvocation::RunRhoNetReplayAndObserveRuntimeValues { firings } => firings,
                other => panic!("replay bridge must map to RunRhoNetReplay…, got {other:?}"),
            };

            let runtime =
                tokio::runtime::Runtime::new().expect("tokio runtime for the replay property");
            let observation = runtime
                .block_on(backend.run_rho_net_replay_and_observe_runtime_values(&firings))
                .expect("the replay must execute on the Rho runtime");

            prop_assert_eq!(observation.values, expected);
        }
    }
}

/// Stage 1 M1 — the executable oracle for obligation (i): the in-Rho match set equals
/// the positional matching relation. For a random single linear App pattern
/// `op(x_0,…,x_{k-1})` and a nullary-leaf subject `op(l_0,…,l_{k-1})`, the compiled
/// automaton matched ON the interpreter must bind σ = `[⟦l_0⟧,…,⟦l_{k-1}⟧]` — the
/// positional σ. This generalizes the fixed-shape `m1_matches_swap` / ternary examples
/// across random constructors and arities 1..3, the property-based floor under the
/// forthcoming `InRhoMatchPositional` Rocq theorem.
mod in_rho_match_property {
    use super::*;
    use proptest::prelude::*;

    fn observation_key(value: &RuntimeObservationValue) -> String {
        match value {
            RuntimeObservationValue::Term { constructor, .. } => constructor.clone(),
            _ => "?".to_string(),
        }
    }

    proptest! {
        #![proptest_config(ProptestConfig { cases: 24, ..ProptestConfig::default() })]

        #[test]
        fn in_rho_match_binds_the_positional_sigma_for_random_linear_patterns(
            op in "[A-Z][a-z]{1,4}",
            leaves in prop::collection::vec("[A-Z][a-z]{0,3}", 1..4),
        ) {
            mettail_runtime::clear_var_cache();
            let (_backend, fingerprint) = swap_demo_backend();
            let arity = leaves.len();

            // The pattern op(x_0,…,x_{k-1}) with distinct linear variables.
            let pattern_args: Vec<Pattern<String>> =
                (0..arity).map(|i| Pattern::var(format!("x{i}"))).collect();
            let automaton = SetAutomaton::compile_structural([(
                PatternId(0),
                Pattern::app(op.clone(), pattern_args),
            )])
            .expect("a linear App pattern compiles");
            let network = automaton_receiver_network_par(
                &automaton.view(),
                "site0",
                "MATCH",
                "OUT",
                &fingerprint,
            )
            .expect("the automaton serializes");

            // The subject op(l_0,…,l_{k-1}) with nullary leaves.
            let subject_children: Vec<GroundTerm> =
                leaves.iter().map(|l| GroundTerm::new(l, Vec::new())).collect();
            let subject =
                spread_term_par(&GroundTerm::new(&op, subject_children), &fingerprint, "site0");

            let echo = sigma_echo_receiver("MATCH", arity);
            let program = echo.append(network).append(subject);

            let runtime =
                tokio::runtime::Runtime::new().expect("tokio runtime for the match property");
            let mut observed = runtime
                .block_on(run_normalized_par_for_oracle_and_read_runtime_values(&program, "OUT"))
                .expect("the in-Rho match must execute");

            // The echo's parallel sends land on OUT in nondeterministic order; compare as
            // a multiset by constructor label.
            observed.sort_by_key(observation_key);
            let mut expected: Vec<RuntimeObservationValue> = leaves
                .iter()
                .map(|l| RuntimeObservationValue::Term {
                    constructor: l.clone(),
                    children: Vec::new(),
                })
                .collect();
            expected.sort_by_key(observation_key);
            prop_assert_eq!(observed, expected);
        }
    }
}
