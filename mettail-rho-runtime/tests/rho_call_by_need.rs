//! M-RHO.2 call-by-need oracle.
//!
//! The generated, validated AST program models a lowered thunk as a private contract plus
//! an explicit cold/hot state token and persistent memo cell. The first force
//! computes and memoizes; the second force reads the memo. Public observations
//! are read from RSpace after one runtime evaluation.

use mettail_rho_codegen::{
    plan_call_by_need_thunk_with_spec, plan_call_by_need_thunk_with_spec_and_evidence_audit,
    CallByNeedBudget, CallByNeedInitialState, CallByNeedPlanEvidence, CallByNeedThunkSpec,
    RhoAstLiteral,
};
use mettail_rho_runtime::{PlannedCallByNeedThunk, PlannedCallByNeedThunkError};

mod support;

fn evidence() -> CallByNeedPlanEvidence {
    CallByNeedPlanEvidence {
        proof_evidence_refs: vec![
            "formal/rocq/rho_bridge/theories/RhoCallByNeedObservation.v".to_string()
        ],
        runtime_oracle_evidence_refs: vec![
            "mettail-rho-runtime/tests/rho_call_by_need.rs".to_string()
        ],
        budget_evidence_refs: vec![
            "formal/rocq/rho_bridge/theories/RhoCallByNeedBudget.v".to_string()
        ],
    }
}

fn budget_for(initial_state: CallByNeedInitialState) -> CallByNeedBudget {
    match initial_state {
        CallByNeedInitialState::Cold => CallByNeedBudget::new(2, 1),
        CallByNeedInitialState::Hot => CallByNeedBudget::new(2, 0),
    }
}

async fn run_need(initial_state: CallByNeedInitialState) -> (Vec<String>, Vec<String>) {
    run_need_spec(CallByNeedThunkSpec::default_for(initial_state)).await
}

async fn run_need_spec(spec: CallByNeedThunkSpec) -> (Vec<String>, Vec<String>) {
    let audit_policy = support::strict_evidence_audit_policy();
    let plan = plan_call_by_need_thunk_with_spec_and_evidence_audit(
        spec.clone(),
        budget_for(spec.initial_state()),
        evidence(),
        &audit_policy,
    )
    .expect("call-by-need thunk plan must pass budget, evidence, and artifact gates");
    let backend = PlannedCallByNeedThunk::from_plan(plan)
        .expect("audited call-by-need plan should build executable thunk");
    let mut observed = backend
        .run_and_read_need_channels()
        .await
        .unwrap_or_else(|e| panic!("planned call-by-need AST program failed:\n{e}"));
    let mut out = observed.remove(spec.out_channel()).unwrap_or_default();
    out.sort();
    let mut evals = observed.remove(spec.eval_channel()).unwrap_or_default();
    evals.sort();
    (out, evals)
}

#[tokio::test]
async fn call_by_need_force_miss_memoizes_and_repeated_force_reuses_value() {
    let (out, evals) = run_need(CallByNeedInitialState::Cold).await;
    assert_eq!(
        out,
        vec!["value".to_string(), "value".to_string()],
        "both forces must observe the source value"
    );
    assert_eq!(
        evals,
        vec!["compute".to_string()],
        "a cold thunk must compute exactly once and reuse the memo thereafter"
    );
}

#[tokio::test]
async fn call_by_need_memo_hit_observes_value_without_compute_marker() {
    let (out, evals) = run_need(CallByNeedInitialState::Hot).await;
    assert_eq!(
        out,
        vec!["value".to_string(), "value".to_string()],
        "memo-hit forces must observe the memoized value"
    );
    assert!(evals.is_empty(), "a hot thunk must not execute the cold compute branch");
}

#[tokio::test]
async fn call_by_need_parameterized_payload_and_channels_observe_generated_values() {
    let spec = CallByNeedThunkSpec::new(
        CallByNeedInitialState::Cold,
        RhoAstLiteral::String("answer".to_string()),
        "calculator-add",
        "RESULT",
        "TRACE",
    )
    .expect("generated-language thunk spec should be valid");

    let (out, evals) = run_need_spec(spec).await;
    assert_eq!(
        out,
        vec!["answer".to_string(), "answer".to_string()],
        "both forces must observe the generated-language value"
    );
    assert_eq!(
        evals,
        vec!["calculator-add".to_string()],
        "a cold generated-language thunk must compute exactly once"
    );
}

#[test]
fn planned_need_runtime_rejects_unaudited_plan() {
    let spec = CallByNeedThunkSpec::default_for(CallByNeedInitialState::Hot);
    let plan = plan_call_by_need_thunk_with_spec(spec, CallByNeedBudget::new(2, 0), evidence())
        .expect("non-audited need plan still passes model gates");

    assert!(!plan.is_evidence_audited());
    let err = PlannedCallByNeedThunk::from_plan(plan)
        .expect_err("runtime-executable need thunks require strict evidence auditing");
    assert_eq!(err, PlannedCallByNeedThunkError::EvidenceNotAudited);
}
