//! Sig-B Blocker-2 chain Welch bench (pgmcp experiment #9, 2026-05-31).
//!
//! Times the {left,right}_assoc_chain workloads via `Int::parse`. The arm
//! (control = base[sigb-gll], treatment = +Blocker-2) is selected by the
//! `B2_DISABLE` env var read inside the walker (`b2_crosswrap_disabled`):
//! set → the cross-wrap drain + §3d backstop are skipped (control); unset →
//! they run (treatment). The chain workloads are cast-free, so they never
//! reach the gated code (the drain block is behind a non-empty
//! `pending_cohort_drain_keys`, empty for chains) — the panel is the
//! load-bearing R4 guard confirming Blocker-2 is byte-identical on chains.
//!
//! Emits one CSV line per (arm,config,sample) to stdout:
//!   `<arm>,<config>,<sample>,<nanos>`
//! The outer driver alternates `B2_DISABLE=1` (control) / unset (treatment)
//! runs to interleave and average out system drift.

use std::time::Instant;
use mettail_languages::calculator::Int;

fn right_assoc_chain(depth: usize) -> String {
    let mut s = String::with_capacity(depth * 4);
    for i in 0..depth {
        if i > 0 {
            s.push_str(" ^ ");
        }
        s.push('2');
    }
    s
}

fn left_assoc_chain(depth: usize) -> String {
    let mut s = String::with_capacity(depth * 4);
    for i in 0..depth {
        if i > 0 {
            s.push_str(" + ");
        }
        s.push('1');
    }
    s
}

fn main() {
    let arm = if std::env::var_os("B2_DISABLE").is_some() {
        "control"
    } else {
        "treatment"
    };
    // N samples per config (default 51; overridable).
    let n: usize = std::env::var("B2_N")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(51);

    // Build the workloads up front so string construction is not timed.
    let configs: Vec<(&str, String)> = vec![
        ("left_50", left_assoc_chain(50)),
        ("left_100", left_assoc_chain(100)),
        ("left_200", left_assoc_chain(200)),
        ("right_50", right_assoc_chain(50)),
        ("right_100", right_assoc_chain(100)),
        ("right_200", right_assoc_chain(200)),
        ("right_1000", right_assoc_chain(1000)),
        // RSS-sentinel configs (timed too; the driver also tracks peak RSS).
        ("right_2000", right_assoc_chain(2000)),
    ];

    // Warm-up: parse each once (untimed) to amortize first-call init.
    for (_, input) in &configs {
        mettail_runtime::clear_var_cache();
        let _ = Int::parse(input);
    }

    for (label, input) in &configs {
        for sample in 0..n {
            mettail_runtime::clear_var_cache();
            let t0 = Instant::now();
            let r = Int::parse(input);
            let dt = t0.elapsed().as_nanos();
            // Guard: every chain must parse OK in both arms (correctness).
            assert!(
                r.is_ok(),
                "[{}] {} sample {} FAILED to parse: {:?}",
                arm,
                label,
                sample,
                r.err()
            );
            println!("{},{},{},{}", arm, label, sample, dt);
        }
    }
}
