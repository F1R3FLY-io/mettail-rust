//! Phase F.13 Task #117 (2026-05-23) — recovery cohort cache
//! Welch's t-test benchmark.
//!
//! Loops a fixed-set of recovery-heavy malformed inputs ITERATIONS
//! times and prints the total wall-time in milliseconds (a single
//! line, parseable by the t-test harness). The workload is designed
//! to MAXIMIZE recovery cohort cache hit rate by exercising cascading
//! errors that fan out many cursors hitting the same
//! `(pos, state_cat_src_idx, cur_bp, frame_kind, frontier_size)`
//! dispatch site.
//!
//! Run with:
//!   cargo run --release -p mettail-languages --bench recovery_cohort_bench
//!
//! Comparison protocol:
//!   N=15 trials at HEAD (cache ON)
//!   N=15 trials at aa0be44 baseline (cache absent)
//!   Welch's t-test via /tmp/welch_ttest.py at p<0.05
//!   Accept iff p<0.05 AND HEAD_mean < baseline_mean (per
//!   feedback-optimization-t-test).

use mettail_languages::calculator::Int;
use std::time::Instant;

const ITERATIONS: usize = 100;

fn workload() -> Vec<&'static str> {
    vec![
        // Cascading operators — recovery fires at each `+ +`, fanning
        // out branches across cursor frontier.
        "1 + + + + 2 + + + 3 + + + 4 + + + 5",
        // Deep nested unclosed parens — recovery fires at EOF across
        // every open paren level (same recovery dispatch site many times).
        "((((((((((1 + 2",
        // Mixed-junk multistep — exercises Viterbi multi-step recovery
        // (the heavier of the two recovery searches).
        "1 + * / @ ; 2 + * / @ ; 3",
        // Stray-infix repeated — recovery cohort fanout at each `@`.
        "1 @ 2 @ 3 @ 4 @ 5 @ 6 @ 7 @ 8 @ 9 @ 10",
        // Trailing tokens — recovery at multiple positions on cascaded
        // single-token errors.
        "1 2 3 4 5 6 7 8 9 10",
        // ── Evidence-pruning P0 extension (2026-06-11; plan v3 P0.4 /
        // round-2 m-4): zero-innovation stall inputs for the P4
        // demotion panel. These park cursors on ε/recovery edges
        // WITHOUT consuming (repeated leading junk before any
        // consumable token), so the P4 innovation-demotion reordering
        // has stalled members to demote — the original five inputs
        // maximize cohort-cache hits, not innovation stalls. ──
        "@ @ @ @ @ 1 + 2",
        "( ( ( @ @ @",
        "+ + + + + + + + 1",
    ]
}

fn main() {
    // Evidence-pruning P0 (2026-06-11): the P4 demotion arm. The walker
    // reads `PRATTAIL_EP_P4_DEMOTE` once per construction (off|shadow|
    // on); this bench just LABELS the emitted line with the active arm
    // so the Welch driver can interleave control/treatment runs.
    let arm = std::env::var("PRATTAIL_EP_P4_DEMOTE").unwrap_or_else(|_| "off".to_string());
    let inputs = workload();
    // Warm-up iteration (excluded from timing) to populate any one-time
    // lazy-init caches (token_id_map, RecoveryInfra build, etc.).
    for input in &inputs {
        mettail_runtime::clear_var_cache();
        let _ = Int::parse_recovering(input);
    }

    let start = Instant::now();
    for _ in 0..ITERATIONS {
        for input in &inputs {
            mettail_runtime::clear_var_cache();
            let _ = Int::parse_recovering(input);
        }
    }
    let elapsed_ms = start.elapsed().as_millis();
    // Single-line output for the t-test harness (arm-labelled since the
    // P0 extension; the legacy harness splits on ',' and takes the last
    // field).
    println!("{},{}", arm, elapsed_ms);
}
