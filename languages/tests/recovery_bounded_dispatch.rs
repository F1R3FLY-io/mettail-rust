//! Bounded recovery dispatch acceptance tests (Stage 3.20 / L12, 2026-05-06).
//!
//! T1-T6 from the user-approved bounded-recovery plan:
//! - T1: All-junk input terminates within recovery depth cap.
//! - T2: Skip bad infix recovers a partial parse.
//! - T3: Unbalanced parens terminate cleanly.
//! - T4: Cursor-cycle scenario caught by visited-set.
//! - T5: Shipped-grammar regression smoke.
//! - T6: Timing bound — every recovery test completes in under 500 ms.
//!
//! These tests time JUST `Int::parse_recovering(...)`, not the
//! Ascent-evaluation phase (`lang.run_ascent(...)`). Recovery dispatch
//! is a parse-time concern; the bound triggers within the parse loop,
//! so eval never runs for junk inputs.
//!
//! The 500 ms ceiling is an order-of-magnitude bound on the bounded
//! recovery's worst case: even with K=8 branches per Fork and depth
//! cap 3, the total branch count is at most 8^3 = 512, each cursor
//! taking O(grammar) work. On modern hardware this should be milli-
//! to tens-of-milliseconds; 500 ms gives ample slack for CI variance.

use mettail_languages::calculator::Int;
use std::time::Instant;

const TIMING_CAP_MS: u128 = 500;

/// Returns (result, error_count, elapsed_ms). `Int::parse_recovering`
/// returns `(Option<Int>, Vec<ParseError>)`; we count the errors but
/// don't inspect them, since lex-min selection of recovery actions
/// is per-grammar and we only test the timing/termination bound.
fn time_parse_recovering(input: &str) -> (Option<Int>, usize, u128) {
    mettail_runtime::clear_var_cache();
    let start = Instant::now();
    let (result, errors) = Int::parse_recovering(input);
    let elapsed_ms = start.elapsed().as_millis();
    (result, errors.len(), elapsed_ms)
}

/// T1 — All-junk input. With max_recovery_depth=3 and the visited-set
/// cycle defense, recovery dispatches at most a few times before
/// returning Error or running out of forward-progress branches. Must
/// terminate inside the timing cap.
#[test]
fn t1_all_junk_terminates_within_recovery_depth_cap() {
    let (_result, _errors, elapsed_ms) = time_parse_recovering("@@@@");
    assert!(
        elapsed_ms < TIMING_CAP_MS,
        "T1 all-junk parse took {}ms (cap {}ms) — bounded recovery violated",
        elapsed_ms,
        TIMING_CAP_MS,
    );
}

/// T2 — Stray infix operator. The bad `+` at position 2 should be
/// either skipped (RecoveryEvent::SkipToSync) or deleted
/// (RecoveryEvent::DeleteToken). Either way the parser should make
/// forward progress. The test only requires terminating inside the
/// cap; it doesn't pin the exact recovery action since the lex-min
/// winner depends on per-grammar weights.
#[test]
fn t2_skip_bad_infix_terminates_within_cap() {
    let (_result, _errors, elapsed_ms) = time_parse_recovering("1 + + 2");
    assert!(
        elapsed_ms < TIMING_CAP_MS,
        "T2 stray-infix parse took {}ms (cap {}ms) — bounded recovery violated",
        elapsed_ms,
        TIMING_CAP_MS,
    );
}

/// T3 — Unbalanced parens. Recovery may attempt InsertToken to
/// synthesize the missing `)`, which is a non-advancing repair
/// (synthetic splice). The visited-set defense ensures that even
/// when InsertToken doesn't advance pos, the cursor is refused on
/// re-dispatch at the same configuration.
#[test]
fn t3_unbalanced_parens_terminates_within_cap() {
    let (_result, _errors, elapsed_ms) = time_parse_recovering("((((1");
    assert!(
        elapsed_ms < TIMING_CAP_MS,
        "T3 unbalanced-parens parse took {}ms (cap {}ms) — bounded recovery violated",
        elapsed_ms,
        TIMING_CAP_MS,
    );
}

/// T4 — Single junk token. The most cycle-prone scenario: at pos=0
/// the parser sees `@` (no prefix arm matches), recovery fires. If
/// the lex-min winner is InsertToken (non-advancing) the cursor's
/// inner_state stays at PrefixDispatch{pos=0}; the next dispatch
/// would be at the same configuration and the visited-set rejects
/// it cleanly.
#[test]
fn t4_cursor_cycle_caught_by_visited_set() {
    let (_result, _errors, elapsed_ms) = time_parse_recovering("@");
    assert!(
        elapsed_ms < TIMING_CAP_MS,
        "T4 cursor-cycle parse took {}ms (cap {}ms) — visited-set defense \
         likely failed",
        elapsed_ms,
        TIMING_CAP_MS,
    );
}

/// T5 — Shipped-grammar smoke. A canonical valid input must parse
/// correctly with bounded recovery enabled (no recovery fires
/// because no dead-end is reached). Verifies the bounded-recovery
/// machinery is dormant on the success path.
#[test]
fn t5_shipped_grammar_regression_smoke() {
    let (result, errors, elapsed_ms) = time_parse_recovering("1 + 2 * 3");
    assert!(
        elapsed_ms < TIMING_CAP_MS,
        "T5 valid parse took {}ms (cap {}ms) — bounded recovery should be \
         dormant on the success path",
        elapsed_ms,
        TIMING_CAP_MS,
    );
    assert!(
        result.is_some(),
        "T5 valid input '1 + 2 * 3' must parse successfully; got result_some={} \
         errors={}",
        result.is_some(),
        errors,
    );
    assert_eq!(errors, 0, "T5 valid input must not trigger recovery; got {} errors", errors,);
}

/// T6 — Timing bound. Aggregates the timing assertion across a
/// representative input set. If any single input exceeds the cap,
/// the bound has slipped somewhere — depth cap not honored, visited
/// set not catching cycles, or forward-progress filter not dropping
/// non-advancing branches.
#[test]
fn t6_recovery_completes_under_timing_cap() {
    let inputs = ["@@@@", "1 + + 2", "((((1", "@", "1 @ 2 @ 3 @ 4 @ 5", "1 + ", " + 2"];
    for input in inputs {
        let (_result, _errors, elapsed_ms) = time_parse_recovering(input);
        assert!(
            elapsed_ms < TIMING_CAP_MS,
            "T6 input {:?} took {}ms (cap {}ms) — bounded recovery violated",
            input,
            elapsed_ms,
            TIMING_CAP_MS,
        );
    }
}
