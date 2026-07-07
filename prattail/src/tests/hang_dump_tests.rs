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

/// T4 Sub-commit 4 (2026-05-12): publish → take_snapshot pipeline test.
///
/// Verifies that:
/// 1. `test_force_snapshot` populates the slot (mirroring the production
///    `publish_snapshot` path).
/// 2. `test_take_snapshot` returns the published snapshot wrapped in Arc.
/// 3. The trigger field is OVERRIDDEN to the take-time trigger (the
///    documented contract — the snapshot is captured by the walker with
///    one trigger; the watcher overlays its own trigger on dump).
/// 4. All other fields (step_index, walker_pos, cursors, etc.) are
///    preserved verbatim.
#[test]
fn publish_then_take_overrides_trigger_and_preserves_fields() {
    crate::hang_dump::test_clear_slot();
    let original = sample_snapshot();
    crate::hang_dump::test_force_snapshot(original);

    let taken = crate::hang_dump::test_take_snapshot(HangTrigger::Watchdog { idle_secs: 7 });
    let snap = taken.expect("test_take_snapshot returned None after force_snapshot");

    // Preserved fields.
    assert_eq!(snap.step_index, 99);
    assert_eq!(snap.walker_pos, 17);
    assert_eq!(snap.cursor_count, 2);
    assert_eq!(snap.cursors.len(), 2);
    assert_eq!(snap.pid, 12345);

    // Trigger overridden by the take call.
    assert!(
        matches!(snap.trigger, HangTrigger::Watchdog { idle_secs: 7 }),
        "trigger should be overridden to Watchdog {{ idle_secs: 7 }}, got {:?}",
        snap.trigger,
    );

    // Banner reflects the override.
    let banner = snap.to_banner();
    assert!(banner.contains("Watchdog"));
    assert!(banner.contains("idle_secs: 7"));

    // take_snapshot clones (doesn't consume) — second take with a
    // different trigger returns the same data with the new trigger overlay.
    let second_take = crate::hang_dump::test_take_snapshot(HangTrigger::Sigusr1)
        .expect("second take_snapshot returned None — slot should still be populated");
    assert!(
        matches!(second_take.trigger, HangTrigger::Sigusr1),
        "second take should overlay Sigusr1 trigger; got {:?}",
        second_take.trigger,
    );
    assert_eq!(second_take.step_index, 99, "underlying data preserved");
}

/// T4 Sub-commit 5 (2026-05-12): walker → publish e2e test.
///
/// Drives a minimal scripted-engine walker through `run_to_end_of_input`
/// and verifies that `publish_to_hang_dump_slot` (wired in Sub-commit 1)
/// fires per-step, leaving a snapshot in the slot that `take_snapshot`
/// returns.
///
/// This is the acceptance test for the wiring fix in Sub-commit 1 —
/// it would have failed BEFORE the fix (`run_to_end_of_input` lacked
/// the `publish_to_hang_dump_slot` call) and passes AFTER.
#[test]
fn walker_publishes_snapshot_during_run_to_end_of_input() {
    use crate::automata::lex_weight::LexicographicWeight;
    use crate::gss::{WpdaGss, WpdaGssNode};
    use crate::wpda_runtime::{SliceTokenSource, StackSymbolV2, WpdaState, WpdaTokenSource};
    use crate::wpda_walker::{WpdaEngine, WpdaStepAction, WpdaWalker};
    use std::cell::RefCell;

    // Local minimal ScriptedEngine — pop the next action from a Vec
    // each call. Mirrors the pattern at wpda_walker.rs:7000+.
    struct ScriptedEngine {
        script: RefCell<Vec<WpdaStepAction<LexicographicWeight>>>,
    }
    impl WpdaEngine<LexicographicWeight> for ScriptedEngine {
        fn step(
            &self,
            _state: &WpdaState,
            _gss: &WpdaGss<LexicographicWeight>,
            _frontier_top: Option<&WpdaGssNode>,
            _pos: usize,
            _tokens: &dyn WpdaTokenSource,
            _frame_ctx: crate::wpda_runtime::FrameCtx,
        ) -> WpdaStepAction<LexicographicWeight> {
            self.script
                .borrow_mut()
                .pop()
                .unwrap_or(WpdaStepAction::Idle)
        }
    }

    crate::hang_dump::test_clear_slot();

    // Two-step script: Push then Accept. Drives run_to_end_of_input
    // through one non-terminal step (Push → PrefixDispatch) and one
    // terminal-transition step (Accept).
    let engine = ScriptedEngine {
        script: RefCell::new(vec![
            WpdaStepAction::Accept,
            WpdaStepAction::Push {
                symbol: StackSymbolV2::category_entry(0),
                weight: LexicographicWeight::from_cost(0.0, 0, 0),
                new_state: WpdaState::PrefixDispatch { pos: 0, cur_bp: 0 },
            },
        ]),
    };
    let mut walker: WpdaWalker<LexicographicWeight, _> = WpdaWalker::new(engine, 0);
    let token_src = SliceTokenSource::new(&[]);

    walker
        .run_to_end_of_input(10, &token_src)
        .expect("max_steps not exceeded");

    // Snapshot was published per-step; take it now. Slot being populated
    // at all is the wiring-acceptance test — pre-Sub-commit-1,
    // `run_to_end_of_input` did NOT call `publish_to_hang_dump_slot`
    // and the slot would remain empty (test_clear_slot cleared it).
    let snap = crate::hang_dump::test_take_snapshot(HangTrigger::Sigusr1).expect(
        "snapshot slot empty after run_to_end_of_input — \
             publish_to_hang_dump_slot wiring is broken",
    );
    assert!(
        snap.cursor_count >= 1,
        "cursor_count should be >= 1 (singleton at least); got {}",
        snap.cursor_count,
    );
    // pid + timestamp are populated by publish path; verify non-zero.
    assert_eq!(snap.pid, std::process::id());
}
