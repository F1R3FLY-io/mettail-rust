//! Evidence-pruning P-series Welch panel (P0 deliverable, 2026-06-11) —
//! the cast-tower / cast-then-compare workload (plan
//! `docs/design/evidence-pruning/02-staged-implementation-plan.md` v3;
//! red-team round-1 F5: the Welch gates had no panel to run against).
//!
//! Emits one CSV line per (config, input, sample) to stdout —
//! `<config>,<input_idx>,<reps>,<sample>,<total_nanos>` — and the outer
//! driver alternates `PRATTAIL_EP_<STAGE>` env arms (off|shadow|on; read
//! inside the walker once per construction) to interleave
//! control/treatment and average out system drift. Per-input rows make
//! the depth-independence claim (CastLookaheadGateBound: gated frontier
//! ~ trigger count, NOT tower depth) directly testable input-by-input.
//!
//! Workload: the P1 probe corpus — cast towers and cast-then-compare
//! shapes that exercise the cross-cat-LHS delegate fan (calculator
//! grammar: `int(...)`/`float(...)` casts with comparison/arithmetic
//! continuations).
//!
//! TIERS (P0 smoke finding, 2026-06-11 @ f1ea267c, debug): bare towers
//! scale gently with depth (d3 29.6ms, d5 121ms) but a compare
//! continuation behind the tower explodes the frontier ~K^depth
//! (d3+cmp 1.17s = 40x its bare tower; d5+cmp >>30s = >250x) — the
//! exact P1 pathology. The heavy inputs therefore run reps=1 per
//! sample (they are individually long enough for the timer), else the
//! base arm could never complete a sample.
//!
//! Env knobs:
//! - `PRATTAIL_EP_CONFIG`        — arm label written to the CSV (default `base`).
//! - `CAST_TOWER_SAMPLES`        — samples per input (default 30; >=15 per I5).
//! - `CAST_TOWER_HEAVY`          — `off` skips the heavy tier (debug smokes).
//! - `CAST_TOWER_PATHOLOGICAL`   — `on` ALSO enables the pathological
//!   input (idx 6, d5+cmp: right-censored > 580 s debug at the P0
//!   baseline — it cannot be a default panel input on the base arm;
//!   treatment arms and P2 acceptance runs opt in, and base-arm
//!   evidence for it is a right-censored wall-clock bound, not a
//!   t-test sample).
//!
//! Protocol (per the plan's I5): N>=15 samples/arm, `/tmp/welch_ttest.py`,
//! two-tailed p<0.05, per input_idx; ACCEPT iff p<0.05 AND treatment mean
//! < control AND zero behavioral diffs; chains (b2_chain_bench) must stay
//! neutral. Panel runs use the RELEASE profile (debug is for smokes).

use mettail_languages::calculator::{Bool, Int};
use std::time::Instant;

const DEFAULT_SAMPLES: usize = 30;
const LIGHT_REPS: usize = 20;
const HEAVY_REPS: usize = 1;
/// Workload index of the pathological d5+cmp input (opt-in via
/// `CAST_TOWER_PATHOLOGICAL=on`; see module docs).
const PATHOLOGICAL_IDX: usize = 6;

enum Shape {
    Int,
    Bool,
}

/// (input, result shape, reps per sample). reps == HEAVY_REPS marks the
/// heavy tier (cast-then-compare frontier blowup, see module docs).
fn workload() -> Vec<(&'static str, Shape, usize)> {
    vec![
        // P1 probe set (plan §P1 Step-0).
        ("int(3) == 3", Shape::Bool, LIGHT_REPS),
        ("int(3) + 3", Shape::Int, LIGHT_REPS),
        ("int(3)", Shape::Int, LIGHT_REPS),
        ("int(float(int(3.14)))", Shape::Int, LIGHT_REPS),
        ("int(float(int(3.14))) == 3", Shape::Bool, HEAVY_REPS),
        // Deeper towers — the depth-independence claim
        // (CastLookaheadGateBound: gated frontier ~ trigger count, not
        // depth).
        ("int(float(int(float(int(3.14)))))", Shape::Int, LIGHT_REPS),
        ("int(float(int(float(int(3.14))))) == 3", Shape::Bool, HEAVY_REPS),
        // Cast-then-compare chains (multiple triggers in the suffix).
        ("int(1) == 1 and int(2) == 2", Shape::Bool, LIGHT_REPS),
        ("float(3) >= 3.0", Shape::Bool, LIGHT_REPS),
    ]
}

fn parse_once(input: &str, shape: &Shape) {
    mettail_runtime::clear_var_cache();
    match shape {
        Shape::Int => {
            let _ = Int::parse(input);
        },
        Shape::Bool => {
            let _ = Bool::parse(input);
        },
    }
}

fn main() {
    let samples: usize = std::env::var("CAST_TOWER_SAMPLES")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(DEFAULT_SAMPLES);
    let heavy_on = std::env::var("CAST_TOWER_HEAVY").map(|v| v != "off").unwrap_or(true);
    let pathological_on =
        std::env::var("CAST_TOWER_PATHOLOGICAL").map(|v| v == "on").unwrap_or(false);
    let config = std::env::var("PRATTAIL_EP_CONFIG").unwrap_or_else(|_| "base".to_string());

    let inputs: Vec<(usize, (&'static str, Shape, usize))> = workload()
        .into_iter()
        .enumerate()
        .filter(|(idx, (_, _, reps))| {
            if *idx == PATHOLOGICAL_IDX {
                pathological_on
            } else {
                heavy_on || *reps != HEAVY_REPS
            }
        })
        .collect();

    // Warm-up (excluded): one-time lazy inits (token maps, WFST tables)
    // — enabled inputs only (a heavy warm-up parse costs >30s debug).
    for (_, (input, shape, _)) in &inputs {
        parse_once(input, shape);
    }

    for sample in 0..samples {
        for (input_idx, (input, shape, reps)) in &inputs {
            let start = Instant::now();
            for _ in 0..*reps {
                parse_once(input, shape);
            }
            let nanos = start.elapsed().as_nanos();
            println!("{},{},{},{},{}", config, input_idx, reps, sample, nanos);
        }
    }
}
