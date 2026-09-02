//! Reproducible p99 microbenchmark for the typed SMT preflight boundary.
//!
//! The primary metric is nanoseconds per validated raw AST node.  A second metric
//! measures rejection of an adversarial maximum bitvector width before modulus or
//! Z3 allocation.  Run the release binary once on a pinned performance-governor CPU;
//! the benchmark performs its own warm-up and emits one machine-readable JSON row.

use std::hint::black_box;
use std::time::Instant;

use mettail_prattail::logict_smt::{
    validate_constraint_with_budget, SmtConstraint, SmtTerm, SmtWorkBudget,
};

const TERM_DEPTH: usize = 4_096;
const FORMULA_NODES: u64 = 2 * TERM_DEPTH as u64 + 3;
const WARMUP_RUNS: usize = 20;
const SAMPLES: usize = 200;
const HOSTILE_SAMPLES: usize = 2_000;

fn benchmark_formula() -> SmtConstraint {
    let mut term = SmtTerm::int(1);
    for _ in 0..TERM_DEPTH {
        term = SmtTerm::Add(Box::new(term), Box::new(SmtTerm::int(1)));
    }
    SmtConstraint::Eq(term, SmtTerm::int((TERM_DEPTH + 1) as u64))
}

fn percentile_99(samples: &mut [f64]) -> f64 {
    samples.sort_by(f64::total_cmp);
    let rank = (99 * samples.len()).div_ceil(100);
    samples[rank.saturating_sub(1)]
}

fn main() {
    let formula = benchmark_formula();
    let budget = SmtWorkBudget::default();
    let report = validate_constraint_with_budget(&formula, &budget)
        .expect("benchmark formula must pass typed preflight");
    assert_eq!(report.demand.ast_nodes, FORMULA_NODES);

    for _ in 0..WARMUP_RUNS {
        black_box(
            validate_constraint_with_budget(black_box(&formula), black_box(&budget))
                .expect("warm-up validation"),
        );
    }

    let mut per_node = Vec::with_capacity(SAMPLES);
    for _ in 0..SAMPLES {
        let started = Instant::now();
        black_box(
            validate_constraint_with_budget(black_box(&formula), black_box(&budget))
                .expect("measured validation"),
        );
        per_node.push(started.elapsed().as_nanos() as f64 / FORMULA_NODES as f64);
    }
    let p99_ns_per_node = percentile_99(&mut per_node);

    let hostile = SmtConstraint::Eq(
        SmtTerm::BvVar("hostile".into(), u32::MAX),
        SmtTerm::BvVar("hostile".into(), u32::MAX),
    );
    let hostile_budget = SmtWorkBudget { max_bitvector_width: 256, ..budget };
    let mut hostile_ns = Vec::with_capacity(HOSTILE_SAMPLES);
    for _ in 0..HOSTILE_SAMPLES {
        let started = Instant::now();
        black_box(
            validate_constraint_with_budget(black_box(&hostile), black_box(&hostile_budget))
                .expect_err("hostile width must reject"),
        );
        hostile_ns.push(started.elapsed().as_nanos() as f64);
    }
    let hostile_p99_ns = percentile_99(&mut hostile_ns);

    println!(
        "{{\"metric\":\"p99_preflight_latency_ns_per_ast_node\",\"value\":{p99_ns_per_node:.6},\"unit\":\"ns/node\",\"samples\":{SAMPLES},\"ast_nodes\":{FORMULA_NODES},\"hostile_width_p99_ns\":{hostile_p99_ns:.3},\"hostile_samples\":{HOSTILE_SAMPLES}}}"
    );
}
