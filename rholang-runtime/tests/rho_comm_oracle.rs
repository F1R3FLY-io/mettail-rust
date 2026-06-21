//! M-RHO.1 transport-pure COMM oracle.
//!
//! These tests exercise the Rho-native path directly on the host `RhoRuntime`.
//! Each program is a source-text rendering of a transport-pure rhocalc COMM
//! member from `docs/design/rho-flip/01-mrho1-execution-contract.md`.
//! Process-valued payloads are grounded as sentinel sends to the public `OUT`
//! channel; successful COMM is observed by the resting sentinel data.

use mettail_rholang_runtime::{
    run_rholang_source_for_oracle, run_rholang_source_for_oracle_and_read_ints,
    run_rholang_source_for_oracle_and_read_strings,
    run_rholang_source_for_oracle_then_consume_strings,
    run_rholang_source_sequence_for_oracle_and_read_strings,
};

async fn read_strings(program: &str) -> Vec<String> {
    let mut values = run_rholang_source_for_oracle_and_read_strings(program, "OUT")
        .await
        .unwrap_or_else(|e| panic!("rho COMM oracle string read failed:\n{program}\n{e}"));
    values.sort();
    values
}

async fn read_ints(program: &str, channel: &str) -> Vec<i64> {
    let mut values = run_rholang_source_for_oracle_and_read_ints(program, channel)
        .await
        .unwrap_or_else(|e| {
            panic!("rho COMM oracle int read failed on {channel}:\n{program}\n{e}")
        });
    values.sort();
    values
}

#[tokio::test]
async fn transport_pure_comm_corpus_green() {
    let cases: &[(&str, &str, &[&str])] = &[
        (
            "single_channel",
            r#"
              for (x <- @"c") { *x }
              | @"c"!({ @"OUT"!("p") })
            "#,
            &["p"],
        ),
        (
            "multi_input_two_channels",
            r#"
              for (x <- @"c" & y <- @"d") { *x | *y }
              | @"c"!({ @"OUT"!("p") })
              | @"d"!({ @"OUT"!("q") })
            "#,
            &["p", "q"],
        ),
        (
            "multi_input_uses_both_vars",
            r#"
              for (left <- @"left" & right <- @"right") { *left | *right }
              | @"left"!({ @"OUT"!("p") })
              | @"right"!({ @"OUT"!("q") })
            "#,
            &["p", "q"],
        ),
        (
            "multi_input_three_channels",
            r#"
              for (x <- @"c1" & y <- @"c2" & z <- @"c3") { *x | *y | *z }
              | @"c1"!({ @"OUT"!("p") })
              | @"c2"!({ @"OUT"!("q") })
              | @"c3"!({ @"OUT"!("r") })
            "#,
            &["p", "q", "r"],
        ),
        (
            "comm_with_remaining_parallel",
            r#"
              for (x <- @"c") { *x }
              | @"c"!({ @"OUT"!("p") })
              | @"OUT"!("q")
            "#,
            &["p", "q"],
        ),
        (
            "two_same_payloads_on_distinct_join_channels",
            r#"
              for (x <- @"c" & y <- @"d") { *x | *y }
              | @"c"!({ @"OUT"!("a") })
              | @"d"!({ @"OUT"!("a") })
            "#,
            &["a", "a"],
        ),
    ];

    for &(name, program, expected) in cases {
        let observed = read_strings(program).await;
        let mut expected = expected
            .iter()
            .map(|s| (*s).to_string())
            .collect::<Vec<_>>();
        expected.sort();
        assert_eq!(observed, expected, "COMM corpus member {name}");
    }
}

#[tokio::test]
async fn comm_substitutes_quoted_ground_value_without_errors() {
    let program = r#"
      for (x <- @"c") { *x }
      | @"c"!(0)
    "#;
    run_rholang_source_for_oracle(program)
        .await
        .unwrap_or_else(|e| panic!("ground-value COMM must evaluate without errors: {e}"));
    assert!(
        read_strings(program).await.is_empty(),
        "ground-value COMM should not emit sentinel data"
    );
}

#[tokio::test]
async fn received_name_can_be_used_as_channel() {
    let program = r#"
      new p in {
        for (x <- @"c") { x!(0) }
        | @"c"!(*p)
        | for (@v <- p) { @"OUT"!(v) }
      }
    "#;
    assert_eq!(read_ints(program, "OUT").await, vec![0]);
}

#[tokio::test]
async fn new_channel_eval_smoke_has_no_public_leak() {
    let program = r#"new x in { x!(0) }"#;
    run_rholang_source_for_oracle(program)
        .await
        .unwrap_or_else(|e| panic!("new-channel smoke must evaluate without errors: {e}"));
    assert!(
        read_ints(program, "OUT").await.is_empty(),
        "private new-channel datum must not leak to OUT"
    );
}

#[tokio::test]
async fn duplicate_receive_channels_are_source_parser_rejected() {
    let program = r#"
      for (x <- @"c" & y <- @"c") { *x | *y }
      | @"c"!({ @"OUT"!("a") })
      | @"c"!({ @"OUT"!("b") })
    "#;
    let err = run_rholang_source_for_oracle(program)
        .await
        .expect_err("source-text parser rejects duplicate receive channels");
    assert!(
        err.contains("Receiving on the same channels"),
        "unexpected duplicate-channel diagnostic: {err}"
    );
}

#[tokio::test]
async fn duplicate_receive_channels_supported_by_direct_rspace_consume() {
    let program = r#"@"c"!("a") | @"c"!("b")"#;
    let mut matched = run_rholang_source_for_oracle_then_consume_strings(program, &["c", "c"])
        .await
        .unwrap_or_else(|e| panic!("duplicate-channel direct consume failed: {e}"))
        .expect("two sends on c must enable the duplicate-channel join");
    matched.sort();
    assert_eq!(
        matched,
        vec!["a".to_string(), "b".to_string()],
        "direct RSpace consume_result must consume two distinct datums from the same channel"
    );
}

#[tokio::test]
async fn duplicate_receive_channels_need_two_available_datums() {
    let program = r#"@"c"!("a")"#;
    let matched = run_rholang_source_for_oracle_then_consume_strings(program, &["c", "c"])
        .await
        .unwrap_or_else(|e| panic!("duplicate-channel direct consume failed: {e}"));
    assert!(
        matched.is_none(),
        "one datum on c must not satisfy a two-premise same-channel join"
    );
}

async fn one_bind_race(arrivals: &[&str]) -> (Vec<String>, Vec<String>) {
    let mut programs = vec![r#"for (@x <- @"c") { @"OUT"!(x) }"#];
    for value in arrivals {
        match *value {
            "a" => programs.push(r#"@"c"!("a")"#),
            "b" => programs.push(r#"@"c"!("b")"#),
            other => panic!("unsupported race value: {other}"),
        }
    }
    let mut observed =
        run_rholang_source_sequence_for_oracle_and_read_strings(&programs, &["OUT", "c"])
            .await
            .unwrap_or_else(|e| panic!("single-bind race sequence failed: {e}"));
    let mut fired = observed.remove("OUT").unwrap_or_default();
    fired.sort();
    let mut resting = observed.remove("c").unwrap_or_default();
    resting.sort();
    (fired, resting)
}

#[tokio::test]
async fn single_bind_race_permutation_enumeration_covers_outcome_set() {
    let ab = one_bind_race(&["a", "b"]).await;
    let ba = one_bind_race(&["b", "a"]).await;

    assert_eq!(ab, (vec!["a".to_string()], vec!["b".to_string()]));
    assert_eq!(ba, (vec!["b".to_string()], vec!["a".to_string()]));

    let mut fingerprints = vec![
        format!("fired={:?};resting={:?}", ab.0, ab.1),
        format!("fired={:?};resting={:?}", ba.0, ba.1),
    ];
    fingerprints.sort();
    assert_eq!(
        fingerprints,
        vec![
            "fired=[\"a\"];resting=[\"b\"]".to_string(),
            "fired=[\"b\"];resting=[\"a\"]".to_string(),
        ],
        "enumerating send-arrival permutations must cover both eager race outcomes"
    );
}
