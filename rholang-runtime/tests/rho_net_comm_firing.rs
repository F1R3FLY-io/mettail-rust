//! Stage 3b end-to-end: a GENERATED language's canonical single-receive Rholang COMMUNICATION rule
//! fires end-to-end as ONE atomic COMM on the live f1r3node Rholang interpreter — the FIRST
//! NON-LINEAR AC firing.
//!
//! `CommDemo` is a generated `language!` whose only rewrite is the communication rule
//!
//!     Comm . |- (PPar {(PFor N cont), (POutput N Q), ...rest}) ~> (PPar {(eval cont Q), ...rest})
//!
//! i.e. `for(y <- N){ cont } | N!(Q)  ~>  cont[Q/y]`, spliced into the residual bag. It composes,
//! in ONE COMM on the reducer:
//!
//!   * a HashBag AC match over `PPar` with k=2 STRUCTURED fixed elements (the `PFor` receive and the
//!     `POutput` send) + `...rest` — the order-independent process-soup carrier (`AcBagDemo`'s
//!     `reflect_hashbag_soup_par`, but the receiver's element patterns are structured, tag-routed);
//!   * a NON-LINEAR consistency guard: `N` occurs in BOTH elements, so each occurrence binds a
//!     DISTINCT σ slot (a Rholang pattern free variable may occur at most once), and the installed
//!     receiver's `Receive.condition` `EEq(N_recv, N_send)` — the `where`-clause the reducer commits
//!     the COMM under only when it evaluates to `GBool(true)` — enforces `N ≡ N`, reject-safe;
//!   * host-computed capture-avoiding substitution `cont[Q/y]` (model-b, exactly as the Stage 3c
//!     binder path) delivered as the firing's CONTRACTUM at a dedicated σ slot;
//!   * a bag RHS `PPar{ cont[Q/y], ...rest }` — the receiver body `@"ac:PPar"!(reduct) | rest`.
//!
//! ## Firing drive (deviation, documented)
//!
//! Every other Stage (base/AC/AC2b/contextual/binder/native) drives its injection from
//! `dovetail_report_for → rho_net_invocation_from_dovetail_to`. The Comm rule CANNOT take that path:
//! the generated Dovetail compiler REJECTS the Comm RHS (a `MultiSubst` nested inside an AC `PPar` is
//! `Err("multi-substitution patterns require generated substitution lowering")`), and even a
//! STRUCTURAL non-linear AC rewrite (Ambient's `OpenRule` shape) records NO `rewrite_justifications`
//! on the untyped e-graph path while the typed path does not lower AC collections at all. RhoCalc's
//! communication is handled by the separate `receive::try_comm_rw_proc` engine for exactly this
//! reason. So — as the backend explicitly anticipates (`run_rho_net_with_call_and_observe_runtime_values`
//! documents "a hand-built (or … Dovetail-report-derived) σ injection actually fires its receiver")
//! — the Comm injection here is HAND-BUILT (`comm_contract_call`) from the operand bag + the
//! host-computed reduct (model-b). The INSTALLED RECEIVER is the codegen-materialized
//! `RhoNetLoweredRule::CommRewrite` (from `CommDemo`'s def, via `installed_rho_net_program_par`), the
//! COMM is real on the live reducer, and the non-linear `Receive.condition` is the real gate.
#![cfg(feature = "comm-demo-runtime")]

use mettail_languages::commdemo::CommDemoLanguage;
use mettail_rholang_codegen::{
    lower_language_def, plan_rho_default_backend, reconstruct_language_def,
    rho_net_comm_injection_sites, suggest_rejected_rule_dispositions, RhoCoverageEvidence,
    RhoDefaultBackendRequirements, RhoGuardCoverageEvidence,
};
use mettail_rholang_runtime::PlannedRhoBackend;
use mettail_runtime::{Language, RuntimeObservationValue, RuntimeReflectedSubterm};

/// Reconstruct CommDemo's augmented `LanguageDef`, plan its Rho-default backend (the `Comm`
/// non-linear AC σ-receiver installs alongside the structural constructors), and return the planned
/// backend, its definition fingerprint, and the Comm receiver's SOURCE channel.
fn comm_demo_backend() -> (PlannedRhoBackend, String, String) {
    let source = CommDemoLanguage
        .metadata()
        .definition_source()
        .expect("generated CommDemoLanguage must expose its definition_source");
    let def = reconstruct_language_def(source)
        .expect("CommDemoLanguage definition_source must reconstruct as a LanguageDef");

    // The Comm receiver's source channel (the channel the Comm injection targets).
    let sites = rho_net_comm_injection_sites(&def);
    assert_eq!(sites.len(), 1, "CommDemo has exactly one Comm rewrite");
    let channel = sites[0].channel.clone();
    assert_eq!(sites[0].rule_label, "Comm");
    assert_eq!(sites[0].op, "PPar");
    assert_eq!(sites[0].nonlinear_var, "N");

    let lowering = lower_language_def(&def);
    let requirements = RhoDefaultBackendRequirements {
        coverage: RhoCoverageEvidence::CoveredRejectedRules(suggest_rejected_rule_dispositions(
            &def, &lowering,
        )),
        guard_coverage: RhoGuardCoverageEvidence::NoGuardObligations,
    };
    let plan = plan_rho_default_backend(&def, requirements)
        .expect("CommDemo (non-linear AC communication) must flip to the Rho backend");
    let fingerprint = plan.definition_fingerprint().to_string();
    (PlannedRhoBackend::from_plan(plan), fingerprint, channel)
}

/// Assert `value` is the singleton observed bag whose sole element is `expected` (multiplicity 1).
fn assert_singleton_bag(value: &RuntimeObservationValue, expected: &RuntimeObservationValue) {
    let RuntimeObservationValue::Bag(entries) = value else {
        panic!("OUT must be a bag (the communicated result), got {value:?}");
    };
    assert_eq!(entries.len(), 1, "the communicated bag has one element, got {value:?}");
    assert_eq!(entries[0].1, 1, "multiplicity 1, got {value:?}");
    assert_eq!(&entries[0].0, expected, "the communicated element is cont[Q/y], got {value:?}");
}

/// `POutput(chan, val)` as an observation value (the decoded reduct / carried element).
fn output_value(chan: &str, val: &str) -> RuntimeObservationValue {
    let leaf = |p: &str| RuntimeObservationValue::Term {
        constructor: p.to_string(),
        children: Vec::new(),
    };
    RuntimeObservationValue::Term {
        constructor: "POutput".to_string(),
        children: vec![leaf(chan), leaf(val)],
    }
}

/// A nullary `RuntimeReflectedSubterm`, e.g. the Name `Nb`.
fn reflected_nullary(constructor: &str) -> RuntimeReflectedSubterm {
    RuntimeReflectedSubterm { constructor: constructor.to_string(), children: Vec::new() }
}

/// `POutput(chan, val)` as a reflected σ/contractum sub-term.
fn reflected_output(chan: &str, val: &str) -> RuntimeReflectedSubterm {
    RuntimeReflectedSubterm {
        constructor: "POutput".to_string(),
        children: vec![reflected_nullary(chan), reflected_nullary(val)],
    }
}

/// (A-3 GATE) `dovetail_report_for(CommDemo subject)` now PRODUCES the Comm justification — the
/// AUTOMATED Dovetail pipeline drives the RhoCalc `Comm` rule, removing the hand-built-σ workaround.
///
/// The redex `{ for(y <- na){ y!(nc) } | na!(nb) }` (both channels `na`) reduces on the typed native
/// lane: the Comm native rule AC-matches the non-linear soup (`N ≡ N` by e-class equality), the
/// dispatch host-computes `cont[Q/y] = (y!(nc))[nb/y] = nb!(nc)` (model-b) and splices it into the
/// residual (here empty) bag. The sole `rewrite_justifications` entry is the `Comm` firing whose:
///   * σ reconstructs the operand bag — it binds the channel `N = na`, the continuation `cont`, the
///     sent name `Q = nb`, and the residual `rest` (an empty `PPar` bag);
///   * CONTRACTUM is the communicated bag `PPar{ nb!(nc) }`, whose sole element is `cont[Q/y]`.
/// This is the report the Comm σ-injection (A-4) reads INSTEAD of the hand-built `comm_contract_call`.
#[test]
fn commdemo_dovetail_report_produces_the_comm_justification() {
    mettail_runtime::clear_var_cache();
    let term = CommDemoLanguage
        .parse_term("{ for(y <- na){ y!(nc) } | na!(nb) }")
        .expect("CommDemo must parse the Comm redex");

    let report = CommDemoLanguage::dovetail_report_for(term.as_ref(), 64, 1_000_000)
        .expect("CommDemo Dovetail report must compile on the typed native lane");
    assert!(
        report.is_complete(),
        "the acyclic Comm reduction must report Complete, got {:?}",
        report.completeness
    );
    assert_eq!(
        report.rewrite_justifications.len(),
        1,
        "exactly one Comm firing must be recorded, got {:?}",
        report.rewrite_justifications
    );
    let justification = &report.rewrite_justifications[0];
    assert_eq!(justification.rule_label, "Comm", "the fired rule is Comm");

    // σ reconstructs the operand bag: N (channel), cont (continuation), Q (sent name), rest.
    let sigma = |name: &str| {
        justification
            .sigma
            .iter()
            .find(|(n, _)| n == name)
            .map(|(_, subterm)| subterm)
            .unwrap_or_else(|| panic!("σ must bind {name}, got {:?}", justification.sigma))
    };
    assert_eq!(sigma("N").constructor, "Na", "the non-linear channel N is `na`");
    assert_eq!(sigma("Q").constructor, "Nb", "the sent name Q is `nb`");
    assert_eq!(sigma("rest").constructor, "PPar", "rest is the residual PPar bag");
    assert!(sigma("rest").children.is_empty(), "the residual bag is empty here");
    // `cont` (the receive continuation) is bound too — the binder body the dispatch substitutes.
    let _ = sigma("cont");

    // The CONTRACTUM is the communicated bag `PPar{ cont[Q/y] }`; its sole element (rest empty) is
    // `cont[nb/y] = nb!(nc) = POutput(Nb, Nc)` — the host-computed reduct the σ-injection reflects.
    let contractum = justification
        .contractum
        .as_ref()
        .expect("the Comm firing carries a contractum (the communicated bag)");
    assert_eq!(contractum.constructor, "PPar", "the contractum is the reduced bag");
    assert_eq!(
        contractum.children.len(),
        1,
        "empty rest ⇒ a singleton communicated bag, got {contractum:?}"
    );
    assert_eq!(
        contractum.children[0],
        reflected_output("Nb", "Nc"),
        "the communicated element is cont[Q/y] = nb!(nc), got {:?}",
        contractum.children[0]
    );
}

/// POSITIVE (empty rest): `{ for(y <- na){ y!(nc) } | na!(nb) }` — both channels `na` — fires as ONE
/// COMM, landing `{ nb!(nc) }` (= `cont[Q/y]`) on OUT. The non-linear `Receive.condition` holds.
#[tokio::test]
async fn commdemo_communication_fires_as_a_comm_on_the_reducer() {
    mettail_runtime::clear_var_cache();
    let (backend, fingerprint, _channel) = comm_demo_backend();

    // Fingerprint coherence: the installed Comm σ-receiver (from the reconstructed def) and the
    // Comm σ-injection (which reflects the reconstructed bag + reduct with
    // `metadata().definition_fingerprint()`) must agree, or the soup would decode inconsistently.
    assert_eq!(
        CommDemoLanguage.metadata().definition_fingerprint(),
        Some(fingerprint.as_str()),
        "planned backend fingerprint must equal the generated metadata fingerprint"
    );

    // (1) AUTOMATED Dovetail report — NO hand-built σ. The redex `{ for(y <- na){ y!(nc) } | na!(nb) }`
    // (both channels `na`) reduces on the typed native lane; the sole firing is the `Comm` firing.
    let term = CommDemoLanguage
        .parse_term("{ for(y <- na){ y!(nc) } | na!(nb) }")
        .expect("CommDemo must parse the Comm redex");
    let report = CommDemoLanguage::dovetail_report_for(term.as_ref(), 64, 1_000_000)
        .expect("CommDemo Dovetail report must compile");

    // (2) The generated Comm σ-injection F-function reconstructs the operand bag from σ and the
    // reduct `cont[Q/y]` from the contractum, and assembles the `comm_contract_call` — REPLACING the
    // hand-built σ that was the deviation this campaign removes.
    let invocation =
        CommDemoLanguage::rho_net_invocation_from_dovetail_to(term.as_ref(), &report, "OUT")
            .expect("the Comm σ-injection must assemble from a complete report");
    assert_eq!(invocation.out_channel, "OUT");

    // (3) RHO-MACHINE EXECUTION: run the installed Comm σ-receiver ∥ call and observe OUT.
    let observation = backend
        .run_rho_net_with_call_and_observe_runtime_values(&invocation.call, &invocation.out_channel)
        .await
        .expect("the Comm injection must execute on the Rho runtime");

    assert_eq!(
        observation.observed_count(),
        1,
        "the non-linear Comm receiver must fire exactly once (got {:?})",
        observation.values
    );
    assert_singleton_bag(&observation.values[0], &output_value("Nb", "Nc"));
}

/// POSITIVE (with rest): `{ for(y <- na){ y!(nc) } | na!(nb) | 0 }` — the residual `0` (a `PZero`,
/// distinct tag) rides the `rest` remainder and is spliced back, so OUT is `{ nb!(nc) | 0 }`.
#[tokio::test]
async fn commdemo_communication_splices_the_residual_bag() {
    mettail_runtime::clear_var_cache();
    let (backend, fingerprint, _channel) = comm_demo_backend();
    assert_eq!(
        CommDemoLanguage.metadata().definition_fingerprint(),
        Some(fingerprint.as_str()),
        "planned backend fingerprint must equal the generated metadata fingerprint"
    );

    // `{ for(y <- na){ y!(nc) } | na!(nb) | 0 }` — the residual `0` (a `PZero`) rides the `rest`
    // remainder. AUTOMATED: σ binds `rest = { 0 }`; the F-fn reconstructs the whole operand bag
    // (splicing the `rest` children) and recovers the reduct `nb!(nc)` from the contractum
    // `PPar{ nb!(nc), 0 }` minus `rest`; the receiver splices `nb!(nc) | 0`.
    let term = CommDemoLanguage
        .parse_term("{ for(y <- na){ y!(nc) } | na!(nb) | 0 }")
        .expect("CommDemo must parse the with-rest Comm redex");
    let report = CommDemoLanguage::dovetail_report_for(term.as_ref(), 64, 1_000_000)
        .expect("CommDemo Dovetail report must compile");
    let invocation =
        CommDemoLanguage::rho_net_invocation_from_dovetail_to(term.as_ref(), &report, "OUT")
            .expect("the Comm σ-injection must assemble from a complete report");

    let observation = backend
        .run_rho_net_with_call_and_observe_runtime_values(&invocation.call, &invocation.out_channel)
        .await
        .expect("the Comm injection must execute on the Rho runtime");

    assert_eq!(
        observation.observed_count(),
        1,
        "the Comm receiver must fire exactly once (got {:?})",
        observation.values
    );
    let RuntimeObservationValue::Bag(entries) = &observation.values[0] else {
        panic!("OUT must be the spliced bag, got {:?}", observation.values[0]);
    };
    let total: usize = entries.iter().map(|(_, count)| *count).sum();
    assert_eq!(total, 2, "the communicated bag = {{ cont[Q/y], rest }}, got {entries:?}");
    assert!(
        entries
            .iter()
            .any(|(element, _)| *element == output_value("Nb", "Nc")),
        "the substituted element cont[Q/y] = nb!(nc) is present, got {entries:?}"
    );
    assert!(
        entries.iter().any(|(element, _)| matches!(
            element,
            RuntimeObservationValue::Term { constructor, children }
                if constructor == "PZero" && children.is_empty()
        )),
        "the residual `0` is spliced back intact, got {entries:?}"
    );
}

/// NEGATIVE (mismatched channels): `{ for(y <- na){ y!(nc) } | nb!(nd) }` — the receive channel `na`
/// ≠ the send channel `nb`. On the AUTOMATED pipeline the NON-LINEAR AC guard VETOES at the Dovetail
/// matcher: the Comm native rule finds NO pairing (`N ≡ N` is unsatisfiable — `na` and `nb` are
/// distinct e-classes, so `collect_ac_matches` prunes by evidence, A-2), so the report carries NO
/// Comm firing and the Comm σ-injection has nothing to inject — nothing lands on OUT. (The
/// installed receiver's `Receive.condition` `EEq(N_recv, N_send)` is the same guard, redundant here
/// since the Dovetail matcher already vetoes upstream.)
#[test]
fn commdemo_mismatched_channel_does_not_fire() {
    mettail_runtime::clear_var_cache();

    // PFor on `na`, POutput on `nb` — channels disagree.
    let term = CommDemoLanguage
        .parse_term("{ for(y <- na){ y!(nc) } | nb!(nd) }")
        .expect("CommDemo must parse the mismatched-channel soup");
    let report = CommDemoLanguage::dovetail_report_for(term.as_ref(), 64, 1_000_000)
        .expect("CommDemo Dovetail report must compile");

    // The reduction is a normal form: the non-linear AC guard vetoed, so NO Comm fired.
    assert!(
        report.is_complete(),
        "the mismatched-channel soup is a normal form (Complete), got {:?}",
        report.completeness
    );
    assert!(
        report.rewrite_justifications.is_empty(),
        "the non-linear AC guard must VETO the mismatched-channel soup — no Comm firing (got {:?})",
        report.rewrite_justifications
    );

    // Consequently the Comm σ-injection fails closed (no firing to inject) — nothing reaches OUT.
    assert!(
        CommDemoLanguage::rho_net_invocation_from_dovetail_to(term.as_ref(), &report, "OUT")
            .is_err(),
        "no Comm firing ⇒ the σ-injection has nothing to inject (nothing lands on OUT)"
    );
}
