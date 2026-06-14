//! M-RHO.2 call-by-need oracle.
//!
//! The generated, validated AST program models a lowered thunk as a private contract plus
//! an explicit cold/hot state token and persistent memo cell. The first force
//! computes and memoizes; the second force reads the memo. Public observations
//! are read from RSpace after one runtime evaluation.

use mettail_rho_codegen::{
    plan_call_by_need_thunk, CallByNeedBudget, CallByNeedInitialState, CallByNeedPlanEvidence,
};
use mettail_rho_runtime::PlannedCallByNeedThunk;

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
    let plan = plan_call_by_need_thunk(initial_state, budget_for(initial_state), evidence())
        .expect("call-by-need thunk plan must pass budget, evidence, and artifact gates");
    let backend = PlannedCallByNeedThunk::from_plan(plan);
    let mut observed = backend
        .run_and_read_string_channels(&["OUT", "EVAL"])
        .await
        .unwrap_or_else(|e| panic!("planned call-by-need AST program failed:\n{e}"));
    let mut out = observed.remove("OUT").unwrap_or_default();
    out.sort();
    let mut evals = observed.remove("EVAL").unwrap_or_default();
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
