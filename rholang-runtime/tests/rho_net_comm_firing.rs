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
    comm_contract_call, lower_language_def, plan_rho_default_backend, reconstruct_language_def,
    rho_net_comm_injection_sites, suggest_rejected_rule_dispositions, CollectionType, GroundTerm,
    RhoCoverageEvidence, RhoDefaultBackendRequirements, RhoGuardCoverageEvidence,
};
use mettail_rholang_runtime::PlannedRhoBackend;
use mettail_runtime::{Language, RuntimeObservationValue};

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

/// The receive `for(y <- chan){ … }`: `PFor(chan, cont)`. The continuation is wildcarded by the
/// Comm receiver (model-b: the host computes `cont[Q/y]`, delivered as the reduct), so a nullary
/// placeholder `PZero` stands in for it — the firing reads only the PFor tag + the channel.
fn pfor(chan: &str) -> GroundTerm {
    GroundTerm::new("PFor", vec![GroundTerm::nullary(chan), GroundTerm::nullary("PZero")])
}

/// The send `chan!(val)`: `POutput(chan, val)` over nullary Name constants.
fn poutput(chan: &str, val: &str) -> GroundTerm {
    GroundTerm::new("POutput", vec![GroundTerm::nullary(chan), GroundTerm::nullary(val)])
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

/// POSITIVE (empty rest): `{ for(y <- na){ y!(nc) } | na!(nb) }` — both channels `na` — fires as ONE
/// COMM, landing `{ nb!(nc) }` (= `cont[Q/y]`) on OUT. The non-linear `Receive.condition` holds.
#[tokio::test]
async fn commdemo_communication_fires_as_a_comm_on_the_reducer() {
    mettail_runtime::clear_var_cache();
    let (backend, fingerprint, channel) = comm_demo_backend();

    // Operand bag `PPar{ PFor(na, cont), POutput(na, nb) }` (both channels `na`) + host reduct
    // `cont[nb/y]` = `nb!(nc)` = `POutput(nb, nc)`.
    let operand_bag = GroundTerm::collection(
        CollectionType::HashBag,
        "PPar",
        vec![pfor("Na"), poutput("Na", "Nb")],
    );
    let reduct = poutput("Nb", "Nc");
    let call = comm_contract_call(&channel, &operand_bag, &reduct, &fingerprint, "OUT");

    let observation = backend
        .run_rho_net_with_call_and_observe_runtime_values(&call, "OUT")
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
    let (backend, fingerprint, channel) = comm_demo_backend();

    let operand_bag = GroundTerm::collection(
        CollectionType::HashBag,
        "PPar",
        vec![pfor("Na"), poutput("Na", "Nb"), GroundTerm::nullary("PZero")],
    );
    let reduct = poutput("Nb", "Nc");
    let call = comm_contract_call(&channel, &operand_bag, &reduct, &fingerprint, "OUT");

    let observation = backend
        .run_rho_net_with_call_and_observe_runtime_values(&call, "OUT")
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
/// ≠ the send channel `nb`, so the non-linear `Receive.condition` `EEq(N_recv, N_send)` VETOES the
/// COMM: nothing lands on OUT (the data rests — the `merge_substs → None` / reject-safe analogue).
#[tokio::test]
async fn commdemo_mismatched_channel_does_not_fire() {
    mettail_runtime::clear_var_cache();
    let (backend, fingerprint, channel) = comm_demo_backend();

    // PFor on `na`, POutput on `nb` — channels disagree.
    let operand_bag = GroundTerm::collection(
        CollectionType::HashBag,
        "PPar",
        vec![pfor("Na"), poutput("Nb", "Nd")],
    );
    // A well-formed reduct is still supplied; the guard vetoes BEFORE the body runs.
    let reduct = poutput("Nb", "Nd");
    let call = comm_contract_call(&channel, &operand_bag, &reduct, &fingerprint, "OUT");

    let observation = backend
        .run_rho_net_with_call_and_observe_runtime_values(&call, "OUT")
        .await
        .expect("the mismatched Comm injection must still execute (and observe nothing)");

    assert_eq!(
        observation.observed_count(),
        0,
        "the non-linear guard must VETO a mismatched-channel soup — nothing fires (got {:?})",
        observation.values
    );
}
