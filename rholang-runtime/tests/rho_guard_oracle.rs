//! M-RHO.3 guarded-COMM oracle.
//!
//! These tests run real Rholang `where` receive guards through f1r3node's host
//! `RhoRuntime`. They check the operational side of the formal
//! `GuardedCommSoundness.v` contract: a failed guard does not consume resting
//! data, and a later satisfying datum can still commit.

use mettail_rholang_runtime::run_rholang_source_sequence_for_oracle_and_read_ints;

fn take(mut observed: std::collections::HashMap<String, Vec<i64>>, channel: &str) -> Vec<i64> {
    let mut values = observed.remove(channel).unwrap_or_default();
    values.sort();
    values
}

#[tokio::test]
async fn false_single_bind_guard_leaves_data_and_emits_no_output() {
    let program = r#"
      for (@x <- @"c" where x > 0) { @"OUT"!(x) }
      | @"c"!(-3)
    "#;

    let observed = run_rholang_source_sequence_for_oracle_and_read_ints(&[program], &["OUT", "c"])
        .await
        .unwrap_or_else(|e| panic!("guarded receive sequence failed: {e}"));

    assert!(
        take(observed.clone(), "OUT").is_empty(),
        "failed guard must not emit the guarded body"
    );
    assert_eq!(
        take(observed, "c"),
        vec![-3],
        "failed guard must leave the rejected datum resting"
    );
}

#[tokio::test]
async fn guard_filters_multiple_messages_without_consuming_failed_candidate() {
    let programs =
        [r#"for (@x <- @"c" where x > 0) { @"OUT"!(x) }"#, r#"@"c"!(-1)"#, r#"@"c"!(7)"#];

    let observed = run_rholang_source_sequence_for_oracle_and_read_ints(&programs, &["OUT", "c"])
        .await
        .unwrap_or_else(|e| panic!("guarded receive sequence failed: {e}"));

    assert_eq!(
        take(observed.clone(), "OUT"),
        vec![7],
        "the later satisfying datum must fire the guarded receive"
    );
    assert_eq!(
        take(observed, "c"),
        vec![-1],
        "the earlier guard-failing datum must remain available"
    );
}

#[tokio::test]
async fn false_cross_bind_guard_leaves_all_join_inputs() {
    let program = r#"
      for (@x <- @"a" & @y <- @"b" where x + y > 10) { @"OUT"!(x + y) }
      | @"a"!(3)
      | @"b"!(5)
    "#;

    let observed =
        run_rholang_source_sequence_for_oracle_and_read_ints(&[program], &["OUT", "a", "b"])
            .await
            .unwrap_or_else(|e| panic!("cross-bind guarded receive sequence failed: {e}"));

    assert!(
        take(observed.clone(), "OUT").is_empty(),
        "failed cross-bind guard must not emit the guarded body"
    );
    assert_eq!(take(observed.clone(), "a"), vec![3]);
    assert_eq!(
        take(observed, "b"),
        vec![5],
        "failed cross-bind guard must leave every join input resting"
    );
}

#[tokio::test]
async fn cross_bind_guard_can_commit_later_without_consuming_failed_pair() {
    let programs = [
        r#"for (@x <- @"a" & @y <- @"b" where x + y > 10) { @"OUT"!(x + y) }"#,
        r#"@"a"!(3)"#,
        r#"@"b"!(5)"#,
        r#"@"b"!(20)"#,
    ];

    let observed =
        run_rholang_source_sequence_for_oracle_and_read_ints(&programs, &["OUT", "a", "b"])
            .await
            .unwrap_or_else(|e| panic!("cross-bind guarded receive sequence failed: {e}"));

    assert_eq!(
        take(observed.clone(), "OUT"),
        vec![23],
        "the later satisfying pair must fire the guarded receive"
    );
    assert!(
        take(observed.clone(), "a").is_empty(),
        "the committed pair consumes the matching a input"
    );
    assert_eq!(
        take(observed, "b"),
        vec![5],
        "the earlier guard-failing b input remains after the later pair commits"
    );
}
