//! Microbenchmarks for the production retained Foreign Language Term matcher.
//!
//! `warm_match` compares identical successful captures from the retained
//! matcher and f1r3node's spatial matcher. Pattern conversion, automaton
//! compilation, and target construction are outside the measured region for
//! both arms. `batch_prepare` measures canonical whole-program compilation of
//! pattern families with a shared suffix. Every fixture is checked for exact
//! oracle equality before Criterion may measure it.

use criterion::{
    black_box, criterion_group, criterion_main, BatchSize, BenchmarkId, Criterion, Throughput,
};
use mettail_rholang_codegen::{
    reflect_flt_pattern, reflect_ground_term_par, FltHole, GroundTerm, FREE_VAR_REFLECT_LABEL,
};
use mettail_rholang_runtime::guard_par_substrate::SubstrateGuardMatcher;
use models::rhoapi::{BindPattern, ListParWithRandom, Par, Receive, ReceiveBind};
use models::rust::utils::new_gstring_par;
use rholang::rust::interpreter::matcher::r#match::Matcher;
use rspace_plus_plus::rspace::r#match::Match;

const FP: &str = "flt-automaton-microbench-v1";
const MATCH_DEPTHS: &[usize] = &[1, 8, 64, 512];
const PREPARE_RULES: &[usize] = &[1, 8, 64, 256];
const SHARED_DEPTH: usize = 8;

fn node(label: impl Into<String>, children: Vec<GroundTerm>) -> GroundTerm {
    GroundTerm::new(label, children)
}

fn free() -> GroundTerm {
    node(FREE_VAR_REFLECT_LABEL, vec![GroundTerm::nullary("x")])
}

fn bind_pattern(template: &GroundTerm) -> BindPattern {
    let reflected = reflect_flt_pattern(template, &[FltHole::new("x")], FP)
        .expect("benchmark FLT pattern is valid");
    BindPattern {
        patterns: vec![reflected.pattern],
        remainder: None,
        free_count: reflected.free_count,
    }
}

fn unary_spine(mut leaf: GroundTerm, depth: usize) -> GroundTerm {
    for _ in 0..depth {
        leaf = node("Spine", vec![leaf]);
    }
    leaf
}

fn receive_program(patterns: Vec<BindPattern>) -> Par {
    let receives = patterns
        .into_iter()
        .enumerate()
        .map(|(index, pattern)| Receive {
            binds: vec![ReceiveBind {
                patterns: pattern.patterns,
                source: Some(new_gstring_par(format!("flt-bench-{index}"), Vec::new(), false)),
                remainder: pattern.remainder,
                free_count: pattern.free_count,
            }],
            body: Some(Par::default()),
            persistent: false,
            peek: false,
            bind_count: pattern.free_count,
            locally_free: Vec::new(),
            connective_used: false,
            condition: None,
        })
        .collect();
    Par::default().with_receives(receives)
}

struct MatchFixture {
    pattern: BindPattern,
    data: ListParWithRandom,
    retained: SubstrateGuardMatcher,
}

fn match_fixture(depth: usize) -> MatchFixture {
    let template = unary_spine(free(), depth);
    let target = unary_spine(GroundTerm::nullary("Leaf"), depth);
    let pattern = bind_pattern(&template);
    let data = ListParWithRandom {
        pars: vec![reflect_ground_term_par(&target, FP)],
        random_state: vec![2, 7, 1, 8, 2, 8],
    };
    let retained = SubstrateGuardMatcher::new();
    retained
        .prepare_flt_patterns(&receive_program(vec![pattern.clone()]))
        .expect("benchmark pattern prepares");
    assert_eq!(retained.get(&pattern, &data), Matcher.get(&pattern, &data));
    MatchFixture { pattern, data, retained }
}

fn shared_patterns(rule_count: usize) -> Vec<BindPattern> {
    (0..rule_count)
        .map(|rule| {
            let suffix = unary_spine(free(), SHARED_DEPTH);
            bind_pattern(&node(format!("Rule{rule}"), vec![suffix]))
        })
        .collect()
}

fn bench_warm_match(c: &mut Criterion) {
    let mut group = c.benchmark_group("flt_retained/warm_match");
    for &depth in MATCH_DEPTHS {
        let fixture = match_fixture(depth);
        group.throughput(Throughput::Elements((depth + 1) as u64));
        group.bench_with_input(BenchmarkId::new("retained", depth), &depth, |b, _| {
            b.iter(|| {
                black_box(
                    fixture
                        .retained
                        .get(black_box(&fixture.pattern), black_box(&fixture.data)),
                )
            })
        });
        group.bench_with_input(BenchmarkId::new("spatial_oracle", depth), &depth, |b, _| {
            b.iter(|| black_box(Matcher.get(black_box(&fixture.pattern), black_box(&fixture.data))))
        });
    }
    group.finish();
}

fn bench_batch_prepare(c: &mut Criterion) {
    let mut group = c.benchmark_group("flt_retained/batch_prepare");
    for &rule_count in PREPARE_RULES {
        let patterns = shared_patterns(rule_count);
        let program = receive_program(patterns);
        let evidence = SubstrateGuardMatcher::new();
        assert_eq!(
            evidence
                .prepare_flt_patterns(&program)
                .expect("shared benchmark program prepares"),
            rule_count
        );
        let stats = evidence.flt_automaton_stats();
        assert_eq!(stats.extensions, 0, "initial preparation must be one batch");
        assert_eq!(stats.automaton_states, stats.serialized_states);
        eprintln!(
            "batch_prepare/{rule_count}: {} patterns, {} shared states",
            stats.registered_patterns, stats.automaton_states,
        );

        group.throughput(Throughput::Elements(rule_count as u64));
        group.bench_with_input(BenchmarkId::from_parameter(rule_count), &program, |b, program| {
            b.iter_batched(
                SubstrateGuardMatcher::new,
                |matcher| {
                    black_box(
                        matcher
                            .prepare_flt_patterns(black_box(program))
                            .expect("measured benchmark program prepares"),
                    )
                },
                BatchSize::SmallInput,
            )
        });
    }
    group.finish();
}

criterion_group!(benches, bench_warm_match, bench_batch_prepare);
criterion_main!(benches);
