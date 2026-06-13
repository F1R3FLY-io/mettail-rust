//! M-RHO.2 call-by-need oracle.
//!
//! The source program models a lowered thunk as a private contract plus an
//! explicit cold/hot state token and persistent memo cell. The first force
//! computes and memoizes; the second force reads the memo. Public observations
//! are read from RSpace after one runtime evaluation.

use mettail_rho_runtime::run_rholang_source_sequence_for_oracle_and_read_strings;

async fn run_need(program: &str) -> (Vec<String>, Vec<String>) {
    let mut observed =
        run_rholang_source_sequence_for_oracle_and_read_strings(&[program], &["OUT", "EVAL"])
            .await
            .unwrap_or_else(|e| panic!("call-by-need program failed:\n{program}\n{e}"));
    let mut out = observed.remove("OUT").unwrap_or_default();
    out.sort();
    let mut evals = observed.remove("EVAL").unwrap_or_default();
    evals.sort();
    (out, evals)
}

#[tokio::test]
async fn call_by_need_force_miss_memoizes_and_repeated_force_reuses_value() {
    let program = r#"
      new thunk, state, memo, ret1, ret2 in {
        state!("cold") |
        contract thunk(k) = {
          for (@s <- state) {
            match s {
              "cold" => {
                state!("hot") |
                memo!!("value") |
                @"EVAL"!("compute") |
                k!("value")
              }
              "hot" => {
                state!("hot") |
                for (@v <<- memo) { k!(v) }
              }
            }
          }
        } |
        thunk!(*ret1) |
        for (@v1 <- ret1) { @"OUT"!(v1) | thunk!(*ret2) } |
        for (@v2 <- ret2) { @"OUT"!(v2) }
      }
    "#;

    let (out, evals) = run_need(program).await;
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
    let program = r#"
      new thunk, state, memo, ret1, ret2 in {
        state!("hot") |
        memo!!("value") |
        contract thunk(k) = {
          for (@s <- state) {
            match s {
              "cold" => {
                state!("hot") |
                memo!!("value") |
                @"EVAL"!("compute") |
                k!("value")
              }
              "hot" => {
                state!("hot") |
                for (@v <<- memo) { k!(v) }
              }
            }
          }
        } |
        thunk!(*ret1) |
        for (@v1 <- ret1) { @"OUT"!(v1) | thunk!(*ret2) } |
        for (@v2 <- ret2) { @"OUT"!(v2) }
      }
    "#;

    let (out, evals) = run_need(program).await;
    assert_eq!(
        out,
        vec!["value".to_string(), "value".to_string()],
        "memo-hit forces must observe the memoized value"
    );
    assert!(evals.is_empty(), "a hot thunk must not execute the cold compute branch");
}
