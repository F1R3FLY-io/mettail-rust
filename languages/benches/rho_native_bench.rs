//! Epic 9 #2053 baseline benchmarks for the rho-native surface the campaign
//! touches — Dovetail saturation (the D-stage) and RhoNet lowering (the F-stage
//! artifact) — which the existing parser benches (`parse_bench`, prattail benches)
//! do not cover.
//!
//! Run with CPU affinity on one CCD (governor already `performance`):
//!   taskset -c 0-7 cargo bench -p mettail-languages --bench rho_native_bench
//!
//! These establish the pre-optimization baseline for #2005-2007 (in-Rho matching)
//! and Epic 9 #2054-2061 (matching-efficiency / allocation / caching), per the
//! benchmark-before-optimize discipline. Requires the crate's default features
//! (`dovetail-codegen` + `rho-codegen`).

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};
use mettail_runtime::Language;

const MAX_ITERS: usize = 64;
const MAX_NODES: usize = 100_000;

/// Dovetail saturation (D-stage): parse a term, then run the generated
/// `dovetail_report_for` — the equality-saturation the whole rho-native path
/// depends on. Calculator exercises native-fold arithmetic saturation.
fn bench_dovetail_saturation(c: &mut Criterion) {
    use mettail_languages::calculator::CalculatorLanguage;

    let lang = CalculatorLanguage;
    let inputs: &[(&str, &str)] = &[
        ("add", "1 + 2"),
        ("nested", "(2 + 3) * (4 - 1)"),
        ("deep", "((1 + 2) * (3 + 4)) - ((5 - 1) * (2 + 2))"),
    ];

    let mut group = c.benchmark_group("dovetail_saturation");
    for (name, src) in inputs {
        let term = lang.parse_term(src).expect("calculator term parses");
        group.bench_with_input(BenchmarkId::from_parameter(name), &term, |b, term| {
            b.iter(|| {
                black_box(CalculatorLanguage::dovetail_report_for(
                    term.as_ref(),
                    MAX_ITERS,
                    MAX_NODES,
                ))
            })
        });
    }
    group.finish();
}

/// RhoNet lowering (F-stage artifact): reconstruct a generated language's
/// `LanguageDef` and lower it to the RhoNet plan + concrete Rho AST. SwapDemo is
/// the minimal base-rewrite σ-receiver; Calculator adds native folds + casts.
fn bench_rho_net_lowering(c: &mut Criterion) {
    use mettail_rholang_codegen::{lower_language_def, reconstruct_language_def, RhoNetProgram};

    fn reconstructed_def(source: &str) -> mettail_ast::language::LanguageDef {
        reconstruct_language_def(source).expect("definition source reconstructs")
    }

    let swap_src = mettail_languages::swapdemo::SwapDemoLanguage
        .metadata()
        .definition_source()
        .expect("SwapDemo exposes its definition source");
    let calc_src = mettail_languages::calculator::CalculatorLanguage
        .metadata()
        .definition_source()
        .expect("Calculator exposes its definition source");

    let cases: &[(&str, &str)] = &[("swapdemo", swap_src), ("calculator", calc_src)];

    let mut group = c.benchmark_group("rho_net_lowering");
    for (name, src) in cases {
        let def = reconstructed_def(src);
        group.bench_with_input(BenchmarkId::from_parameter(name), &def, |b, def| {
            b.iter(|| {
                let lowering = lower_language_def(black_box(def));
                let program = RhoNetProgram::from_language_def(def, &lowering);
                black_box(program.lower_to_par(def, &lowering))
            })
        });
    }
    group.finish();
}

criterion_group!(benches, bench_dovetail_saturation, bench_rho_net_lowering);
criterion_main!(benches);
