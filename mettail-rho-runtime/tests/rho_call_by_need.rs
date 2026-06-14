//! M-RHO.2 call-by-need oracle.
//!
//! The generated, validated AST program models a lowered thunk as a private contract plus
//! an explicit cold/hot state token and persistent memo cell. The first force
//! computes and memoizes; the second force reads the memo. Public observations
//! are read from RSpace after one runtime evaluation.

use mettail_rho_codegen::{
    build_call_by_need_thunk_program, CallByNeedInitialState, ValidatedRhoProgram,
};
use mettail_rho_runtime::run_validated_program_and_read_string_channels;

async fn run_need(initial_state: CallByNeedInitialState) -> (Vec<String>, Vec<String>) {
    let program = build_call_by_need_thunk_program(initial_state);
    let validated = ValidatedRhoProgram::try_from(program)
        .expect("call-by-need thunk program must pass generated artifact validation");
    let mut observed = run_validated_program_and_read_string_channels(&validated, &["OUT", "EVAL"])
        .await
        .unwrap_or_else(|e| panic!("validated call-by-need AST program failed:\n{e}"));
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
