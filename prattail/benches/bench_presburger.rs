//! Presburger arithmetic benchmarks.
//!
//! Measures satisfiability checking throughput for:
//! - Single-variable constraints (vs IntervalAlgebra baseline)
//! - Two-variable constraints
//! - Three-variable constraints
//! - Negation handling
//! - NFA construction time
//! - ConstraintTheory propagation throughput

use criterion::{black_box, criterion_group, criterion_main, Criterion};
use mettail_prattail::presburger::*;
use mettail_prattail::logict::ConstraintTheory;

fn bench_nfa_construction(c: &mut Criterion) {
    let mut group = c.benchmark_group("presburger/nfa_construction");

    // Single-variable constraint: x <= 100
    group.bench_function("1var", |b| {
        b.iter(|| {
            let constraint = LinearConstraint::new(vec![(0, 1)], 100);
            let nfa = PresburgerNfa::from_constraint(&constraint, 1, 16);
            black_box(nfa);
        });
    });

    // Two-variable constraint: x + y <= 100
    group.bench_function("2var", |b| {
        b.iter(|| {
            let constraint = LinearConstraint::new(vec![(0, 1), (1, 1)], 100);
            let nfa = PresburgerNfa::from_constraint(&constraint, 2, 16);
            black_box(nfa);
        });
    });

    // Three-variable constraint: x + y + z <= 100
    group.bench_function("3var", |b| {
        b.iter(|| {
            let constraint = LinearConstraint::new(vec![(0, 1), (1, 1), (2, 1)], 100);
            let nfa = PresburgerNfa::from_constraint(&constraint, 3, 16);
            black_box(nfa);
        });
    });

    group.finish();
}

fn bench_satisfiability(c: &mut Criterion) {
    let mut group = c.benchmark_group("presburger/satisfiability");

    // Simple satisfiable: x >= 3 AND x <= 7
    group.bench_function("simple_sat", |b| {
        let theory = PresburgerTheory::new(16);
        let c1 = LinearConstraint::from_gte(vec![(0, 1)], 3);
        let c2 = LinearConstraint::new(vec![(0, 1)], 7);
        b.iter(|| {
            let store = theory.empty_store();
            let store = theory.propagate(&store, &c1).expect("c1 consistent");
            let result = theory.propagate(&store, &c2);
            black_box(result);
        });
    });

    // Simple unsatisfiable: x >= 10 AND x <= 5
    group.bench_function("simple_unsat", |b| {
        let theory = PresburgerTheory::new(16);
        let c1 = LinearConstraint::from_gte(vec![(0, 1)], 10);
        let c2 = LinearConstraint::new(vec![(0, 1)], 5);
        b.iter(|| {
            let store = theory.empty_store();
            let store = theory.propagate(&store, &c1).expect("c1 consistent");
            let result = theory.propagate(&store, &c2);
            black_box(result);
        });
    });

    // Two-variable satisfiability: x + y <= 100 AND x >= 10 AND y >= 20
    group.bench_function("2var_sat", |b| {
        let theory = PresburgerTheory::new(16);
        let c1 = LinearConstraint::new(vec![(0, 1), (1, 1)], 100);
        let c2 = LinearConstraint::from_gte(vec![(0, 1)], 10);
        let c3 = LinearConstraint::from_gte(vec![(1, 1)], 20);
        b.iter(|| {
            let store = theory.empty_store();
            let store = theory.propagate(&store, &c1).expect("c1 consistent");
            let store = theory.propagate(&store, &c2).expect("c2 consistent");
            let result = theory.propagate(&store, &c3);
            black_box(result);
        });
    });

    // Chain of constraints: x0 <= 100, x0 >= 0, x0 + x1 <= 50, x1 >= 5
    group.bench_function("chain_4_constraints", |b| {
        let theory = PresburgerTheory::new(16);
        let constraints = vec![
            LinearConstraint::new(vec![(0, 1)], 100),
            LinearConstraint::from_gte(vec![(0, 1)], 0),
            LinearConstraint::new(vec![(0, 1), (1, 1)], 50),
            LinearConstraint::from_gte(vec![(1, 1)], 5),
        ];
        b.iter(|| {
            let mut store = theory.empty_store();
            for c in &constraints {
                store = theory.propagate(&store, c).expect("consistent");
            }
            black_box(store);
        });
    });

    group.finish();
}

fn bench_witness_generation(c: &mut Criterion) {
    let mut group = c.benchmark_group("presburger/witness");

    group.bench_function("1var_witness", |b| {
        let theory = PresburgerTheory::new(16);
        let c1 = LinearConstraint::from_gte(vec![(0, 1)], 3);
        let c2 = LinearConstraint::new(vec![(0, 1)], 7);
        let store = theory.empty_store();
        let store = theory.propagate(&store, &c1).expect("c1 consistent");
        let store = theory.propagate(&store, &c2).expect("c2 consistent");
        b.iter(|| {
            let w = theory.witness(&store);
            black_box(w);
        });
    });

    group.finish();
}

fn bench_evaluation(c: &mut Criterion) {
    let mut group = c.benchmark_group("presburger/evaluation");

    group.bench_function("evaluate_single", |b| {
        let theory = PresburgerTheory::new(16);
        let constraint = LinearConstraint::new(vec![(0, 1), (1, 1)], 100);
        let assignment = IntAssignment::new(vec![40, 50]);
        b.iter(|| {
            let result = theory.evaluate(&constraint, &assignment);
            black_box(result);
        });
    });

    // Evaluate batch of 100 assignments against same constraint
    group.bench_function("evaluate_batch_100", |b| {
        let theory = PresburgerTheory::new(16);
        let constraint = LinearConstraint::new(vec![(0, 1), (1, 1)], 100);
        let assignments: Vec<IntAssignment> = (0..100)
            .map(|i| IntAssignment::new(vec![i, 100 - i]))
            .collect();
        b.iter(|| {
            let mut count = 0;
            for a in &assignments {
                if theory.evaluate(&constraint, a) {
                    count += 1;
                }
            }
            black_box(count);
        });
    });

    group.finish();
}

criterion_group!(
    benches,
    bench_nfa_construction,
    bench_satisfiability,
    bench_witness_generation,
    bench_evaluation,
);
criterion_main!(benches);
