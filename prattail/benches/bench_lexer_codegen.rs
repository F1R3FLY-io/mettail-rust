//! Lexer codegen benchmarks.
//!
//! Benchmarks the string-based code generation pipeline.
//!
//! Groups:
//! 1. `lexer_codegen/full` — Full lexer code generation
//! 2. `lexer_codegen/scaling` — Scaling with synthetic specs

mod bench_specs;

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use std::time::Duration;

use mettail_prattail::automata::codegen::generate_lexer_code;

use bench_specs::{complex_spec, medium_spec, minimal_spec, prepare, small_spec, synthetic_spec};

fn bench_full_codegen(c: &mut Criterion) {
    let mut group = c.benchmark_group("lexer_codegen/full");
    group.warm_up_time(Duration::from_secs(3));
    group.measurement_time(Duration::from_secs(5));
    group.sample_size(200);

    let specs = [
        ("minimal", minimal_spec()),
        ("small", small_spec()),
        ("medium", medium_spec()),
        ("complex", complex_spec()),
    ];

    for (name, spec) in &specs {
        let prepared = prepare(spec);
        group.bench_with_input(BenchmarkId::from_parameter(name), &prepared, |b, prepared| {
            b.iter(|| {
                generate_lexer_code(
                    &prepared.min_dfa,
                    &prepared.partition,
                    &prepared.token_kinds,
                    &prepared.spec.name,
                )
            });
        });
    }

    group.finish();
}

fn bench_codegen_scaling(c: &mut Criterion) {
    let mut group = c.benchmark_group("lexer_codegen/scaling");
    group.warm_up_time(Duration::from_secs(3));
    group.measurement_time(Duration::from_secs(5));
    group.sample_size(200);

    for n in [5, 10, 20, 50, 100] {
        let spec = synthetic_spec(n);
        let prepared = prepare(&spec);
        let n_terminals = prepared.lexer_input.terminals.len() as u64;
        group.throughput(Throughput::Elements(n_terminals));
        group.bench_with_input(BenchmarkId::from_parameter(n), &prepared, |b, prepared| {
            b.iter(|| {
                generate_lexer_code(
                    &prepared.min_dfa,
                    &prepared.partition,
                    &prepared.token_kinds,
                    &prepared.spec.name,
                )
            });
        });
    }

    group.finish();
}

criterion_group!(benches, bench_full_codegen, bench_codegen_scaling,);
criterion_main!(benches);
