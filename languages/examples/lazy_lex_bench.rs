//! M2L (2026-06-17): lazy-vs-eager lex-DAG benchmark (pgmcp experiment 69).
//!
//! Pre-registered protocol:
//! - **TIME** metric `lex_build_ns`: per replicate, the wall-time to construct
//!   the token source AND drive the WPDA parse to the extent the parse demands
//!   (lex + parse, end-to-end). Control = eager `lex_dag` + `LatticeTokenSource`
//!   + parse; treatment = lazy `lex_dag_lazy` + parse. ≥51 samples per arm per
//!   input-class after 3 warm-ups.
//! - **SPACE** metric `lex_nodes_materialized`: nodes the eager DAG builds vs
//!   nodes the lazy source materializes for the SAME parse, per input.
//!
//! Results are reported SEPARATELY for full-parse vs early-failure input
//! classes (the hypothesis predicts the space win concentrates on
//! early-failure).
//!
//! Output is RAW per-replicate CSV on stdout:
//!   `kind=time,lang,class,arm,input_idx,sample,lex_build_ns`
//!   `kind=space,lang,class,input_idx,eager_nodes,lazy_nodes`
//!
//! Run (single-CCD pinned, perf governor recommended):
//!   taskset -c 2,3 cargo run --release -p mettail-languages --example lazy_lex_bench
//!
//! Env:
//!   LAZY_LEX_SAMPLES   (default 60)  — samples per arm per input
//!   LAZY_LEX_WARMUPS   (default 3)
//!   LAZY_LEX_REPS      (default 200) — inner reps per sample (amortizes timer)

use std::hint::black_box;
use std::time::Instant;

use mettail_languages::{calculator, rhocalc};
use mettail_prattail::wpda_runtime::LatticeTokenSource;

// ── Corpora (identical to the equivalence gate) ─────────────────────────────────

const CALC_FULL: &[&str] = &[
    "1 + 2 * 3",
    "int(3) == 3",
    "1 - 2 - 3",
    "-3!",
    "(1 + 2) * (3 + 4)",
    "1 + 2 == 3 and 4 == 4",
    "1 ? 2 : 3 ? 4 : 5",
    "1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9 + 10 + 11 + 12 + 13 + 14 + 15 + 16 + 17 + 18 + 19 + 20",
];

const CALC_EARLY_FAIL: &[&str] = &[
    "1 + + + + + + + + + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9 + 10 + 11 + 12 + 13 + 14 + 15 + 16",
    "} } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } }",
    "int( + + + + + + + + + + + + + + + + + + + + + + + + + + + + + + + + + + + +",
    "* 1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9 + 10 + 11 + 12 + 13 + 14 + 15 + 16 + 17 + 18",
];

const RHO_FULL: &[&str] = &[
    "{0 | 1 | 2}",
    "new(x,y) in { {x!(0) | y!(1)} }",
    "{0}",
    "{0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 | 16 | 17 | 18 | 19}",
];

const RHO_EARLY_FAIL: &[&str] = &[
    "{ } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } }",
    "{0 | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | |}",
    "new new new new new new new new new new new new new new new new new new new new",
];

// ── Per-arm work units (lex + parse, end-to-end) ────────────────────────────────

#[inline(never)]
fn calc_eager(input: &str) {
    // Construct the token source AND drive the parse — the full lex+parse path
    // for the EAGER control. Build the DAG, wrap in LatticeTokenSource (only on
    // the ambiguous path, matching the facade; for unambiguous DAGs the facade
    // uses the slice path, but to compare like-for-like with the lazy lattice
    // source we always drive the lattice backend here).
    match calculator::lex_dag(input) {
        Ok(dag) => {
            let source = LatticeTokenSource::new(dag);
            let mut pos = 0usize;
            let r = calculator::parse_Proc_via_wpda_with_source(&source, &mut pos, 0);
            black_box(&r);
        },
        Err(e) => {
            black_box(&e);
        },
    }
}

#[inline(never)]
fn calc_lazy(input: &str) {
    let source = calculator::lex_dag_lazy(input);
    let mut pos = 0usize;
    let r = calculator::parse_Proc_via_wpda_with_source(&source, &mut pos, 0);
    black_box(&r);
}

#[inline(never)]
fn rho_eager(input: &str) {
    match rhocalc::lex_dag(input) {
        Ok(dag) => {
            let source = LatticeTokenSource::new(dag);
            let mut pos = 0usize;
            let r = rhocalc::parse_Proc_via_wpda_with_source(&source, &mut pos, 0);
            black_box(&r);
        },
        Err(e) => {
            black_box(&e);
        },
    }
}

#[inline(never)]
fn rho_lazy(input: &str) {
    let source = rhocalc::lex_dag_lazy(input);
    let mut pos = 0usize;
    let r = rhocalc::parse_Proc_via_wpda_with_source(&source, &mut pos, 0);
    black_box(&r);
}

// ── Space metric ────────────────────────────────────────────────────────────────

fn calc_space(input: &str) -> (usize, usize) {
    let eager = calculator::lex_dag(input)
        .map(|d| d.nodes.len())
        .unwrap_or(0);
    let lazy_src = calculator::lex_dag_lazy(input);
    let mut pos = 0usize;
    let _ = calculator::parse_Proc_via_wpda_with_source(&lazy_src, &mut pos, 0);
    (eager, lazy_src.nodes_materialized())
}

fn rho_space(input: &str) -> (usize, usize) {
    let eager = rhocalc::lex_dag(input).map(|d| d.nodes.len()).unwrap_or(0);
    let lazy_src = rhocalc::lex_dag_lazy(input);
    let mut pos = 0usize;
    let _ = rhocalc::parse_Proc_via_wpda_with_source(&lazy_src, &mut pos, 0);
    (eager, lazy_src.nodes_materialized())
}

// ── Harness ─────────────────────────────────────────────────────────────────────

type WorkFn = fn(&str);

#[allow(clippy::too_many_arguments)]
fn time_arm(
    lang: &str,
    class: &str,
    arm: &str,
    inputs: &[&str],
    work: WorkFn,
    samples: usize,
    warmups: usize,
    reps: usize,
) {
    // Warm-ups (excluded): one-time lazy inits (token maps, WFST tables).
    for _ in 0..warmups {
        for &input in inputs {
            for _ in 0..reps {
                work(input);
            }
        }
    }
    for sample in 0..samples {
        for (input_idx, &input) in inputs.iter().enumerate() {
            let start = Instant::now();
            for _ in 0..reps {
                work(input);
            }
            let elapsed = start.elapsed().as_nanos();
            // Per-replicate datum = mean ns per single lex+parse over `reps`
            // (timer-amortized). Emitted as an integer nanosecond count.
            let per_op = (elapsed as f64 / reps as f64).round() as u128;
            println!("kind=time,{},{},{},{},{},{}", lang, class, arm, input_idx, sample, per_op);
        }
    }
}

fn main() {
    let samples: usize = std::env::var("LAZY_LEX_SAMPLES")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(60);
    let warmups: usize = std::env::var("LAZY_LEX_WARMUPS")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(3);
    let reps: usize = std::env::var("LAZY_LEX_REPS")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(200);

    eprintln!(
        "lazy_lex_bench: samples={} warmups={} reps={} (per-op ns = elapsed/reps)",
        samples, warmups, reps
    );

    // ── SPACE metric (deterministic; emit first) ────────────────────────────────
    println!("# SPACE: kind=space,lang,class,input_idx,eager_nodes,lazy_nodes");
    for (lang, class, inputs, spacefn) in [
        ("calculator", "full", CALC_FULL, calc_space as fn(&str) -> (usize, usize)),
        ("calculator", "earlyfail", CALC_EARLY_FAIL, calc_space),
        ("rhocalc", "full", RHO_FULL, rho_space),
        ("rhocalc", "earlyfail", RHO_EARLY_FAIL, rho_space),
    ] {
        for (input_idx, &input) in inputs.iter().enumerate() {
            let (eager, lazy) = spacefn(input);
            println!("kind=space,{},{},{},{},{}", lang, class, input_idx, eager, lazy);
        }
    }

    // ── TIME metric ─────────────────────────────────────────────────────────────
    println!("# TIME: kind=time,lang,class,arm,input_idx,sample,lex_build_ns");
    time_arm("calculator", "full", "eager", CALC_FULL, calc_eager, samples, warmups, reps);
    time_arm("calculator", "full", "lazy", CALC_FULL, calc_lazy, samples, warmups, reps);
    time_arm(
        "calculator",
        "earlyfail",
        "eager",
        CALC_EARLY_FAIL,
        calc_eager,
        samples,
        warmups,
        reps,
    );
    time_arm(
        "calculator",
        "earlyfail",
        "lazy",
        CALC_EARLY_FAIL,
        calc_lazy,
        samples,
        warmups,
        reps,
    );
    time_arm("rhocalc", "full", "eager", RHO_FULL, rho_eager, samples, warmups, reps);
    time_arm("rhocalc", "full", "lazy", RHO_FULL, rho_lazy, samples, warmups, reps);
    time_arm(
        "rhocalc",
        "earlyfail",
        "eager",
        RHO_EARLY_FAIL,
        rho_eager,
        samples,
        warmups,
        reps,
    );
    time_arm("rhocalc", "earlyfail", "lazy", RHO_EARLY_FAIL, rho_lazy, samples, warmups, reps);

    eprintln!("lazy_lex_bench: done");
}
