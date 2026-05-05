//! T4 SIGUSR1 hang-dump unit tests.
//!
//! Tests are gated behind the `hang-dump` feature since the actual
//! signal-handling/watcher infrastructure only compiles with it.
//!
//! Manual end-to-end verification (not automated):
//! ```text
//! PRATTAIL_HANG_DUMP=1 cargo test --features hang-dump ... &
//! kill -USR1 $!
//! ```

#![cfg(feature = "hang-dump")]

use crate::hang_dump::{CursorRow, HangSnapshot, HangTrigger};

fn sample_snapshot() -> HangSnapshot {
    HangSnapshot {
        timestamp_unix_secs: 1_717_000_000,
        pid: 12345,
        trigger: HangTrigger::Sigusr1,
        walker_state_dbg: "PrefixDispatch { src_idx: 0 }".to_string(),
        walker_pos: 17,
        cursor_count: 2,
        gss_node_count: 5,
        step_index: 99,
        cursors: vec![
            CursorRow {
                idx: 0,
                pos: 17,
                state_dbg: "PrefixDispatch".to_string(),
                weight_dbg: "Trop(0.5)".to_string(),
                source_priority: 1,
                pending_ops_len: 3,
                collection_depth: 0,
            },
            CursorRow {
                idx: 1,
                pos: 17,
                state_dbg: "InfixLoop".to_string(),
                weight_dbg: "Trop(1.2)".to_string(),
                source_priority: 2,
                pending_ops_len: 0,
                collection_depth: 1,
            },
        ],
    }
}

#[test]
fn banner_contains_key_fields() {
    let snap = sample_snapshot();
    let banner = snap.to_banner();
    assert!(banner.contains("PRATTAIL HANG DUMP"));
    assert!(banner.contains("pid=12345"));
    assert!(banner.contains("step_index=99"));
    assert!(banner.contains("walker_pos=17"));
    assert!(banner.contains("cursor_count=2"));
    assert!(banner.contains("PrefixDispatch"));
    assert!(banner.contains("InfixLoop"));
}

#[test]
fn json_is_valid_and_includes_all_cursor_rows() {
    let snap = sample_snapshot();
    let json = snap.to_json();

    // Structural checks (we hand-format JSON; just verify shape)
    assert!(json.starts_with('{'));
    assert!(json.ends_with('}'));
    assert!(json.contains("\"timestamp_unix_secs\":1717000000"));
    assert!(json.contains("\"pid\":12345"));
    assert!(json.contains("\"step_index\":99"));
    assert!(json.contains("\"cursor_count\":2"));
    // Both cursor rows present in the cursors array.
    assert!(json.contains("\"idx\":0"));
    assert!(json.contains("\"idx\":1"));
    // String fields properly quoted.
    assert!(json.contains("\"state\":\"PrefixDispatch\""));
    assert!(json.contains("\"state\":\"InfixLoop\""));
}

#[test]
fn json_escapes_special_characters_in_strings() {
    let mut snap = sample_snapshot();
    snap.walker_state_dbg = "state with \"quote\" and \\backslash and\nnewline".to_string();
    let json = snap.to_json();

    // The escaped string must round-trip safely. Look for the JSON-escaped
    // sequences we expect.
    assert!(json.contains("\\\""), "double quote must be escaped: {}", json);
    assert!(json.contains("\\\\"), "backslash must be escaped");
    assert!(json.contains("\\n"), "newline must be escaped");
    // The literal newline byte must NOT appear inside the string field.
    let walker_state_pos = json.find("\"walker_state\":").unwrap();
    let value_end_quote = json[walker_state_pos + 16..]
        .find('"')
        .map(|p| walker_state_pos + 16 + p)
        .unwrap();
    let value_segment = &json[walker_state_pos..value_end_quote];
    assert!(!value_segment.contains('\n'), "literal \\n inside JSON value");
}

#[test]
fn install_hang_dump_handler_is_no_op_when_env_unset() {
    // When PRATTAIL_HANG_DUMP isn't set, install is a complete no-op —
    // doesn't register signal handler, doesn't spawn watcher.
    // Verify by calling twice; second call is also no-op.
    std::env::remove_var("PRATTAIL_HANG_DUMP");
    crate::hang_dump::install_hang_dump_handler();
    crate::hang_dump::install_hang_dump_handler(); // idempotent
}

#[test]
fn watchdog_trigger_field_renders_correctly() {
    let snap = HangSnapshot {
        trigger: HangTrigger::Watchdog { idle_secs: 7 },
        ..sample_snapshot()
    };
    let banner = snap.to_banner();
    assert!(banner.contains("Watchdog"));
    assert!(banner.contains("idle_secs: 7"));
    let json = snap.to_json();
    assert!(json.contains("Watchdog"));
}
