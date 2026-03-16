use criterion::{black_box, criterion_group, criterion_main, Criterion};
use mettail_prattail::confluence::{RewriteRule, Term};
use mettail_prattail::egraph::{AstSize, EGraph, EGraphConfig, ENode, ERewriteRule, Pattern};

fn bench_add_term(c: &mut Criterion) {
    // Build a balanced binary tree of depth 6 (~63 nodes)
    fn make_tree(depth: usize) -> Term {
        if depth == 0 {
            Term::constant("leaf")
        } else {
            Term::app("node", vec![make_tree(depth - 1), make_tree(depth - 1)])
        }
    }
    let term = make_tree(6);
    c.bench_function("egraph/add_term", |b| {
        b.iter(|| {
            let mut eg = EGraph::new();
            black_box(eg.add_term(black_box(&term)));
        });
    });
}

fn bench_saturation_commutative(c: &mut Criterion) {
    let rule = ERewriteRule {
        lhs: Pattern::App {
            symbol: "f".to_string(),
            args: vec![
                Pattern::Var("x".to_string()),
                Pattern::Var("y".to_string()),
            ],
        },
        rhs: Pattern::App {
            symbol: "f".to_string(),
            args: vec![
                Pattern::Var("y".to_string()),
                Pattern::Var("x".to_string()),
            ],
        },
        label: Some("comm".to_string()),
    };

    c.bench_function("egraph/saturation_commutative", |b| {
        b.iter(|| {
            let mut eg = EGraph::new();
            let a = eg.add(ENode { symbol: "a".into(), children: vec![] });
            let b_id = eg.add(ENode { symbol: "b".into(), children: vec![] });
            let c_id = eg.add(ENode { symbol: "c".into(), children: vec![] });
            eg.add(ENode { symbol: "f".into(), children: vec![a, b_id] });
            eg.add(ENode { symbol: "f".into(), children: vec![b_id, c_id] });
            eg.add(ENode { symbol: "f".into(), children: vec![a, c_id] });
            black_box(eg.saturate(black_box(&[&rule].map(|r| ERewriteRule {
                lhs: r.lhs.clone(),
                rhs: r.rhs.clone(),
                label: r.label.clone(),
            }))));
        });
    });
}

fn bench_saturation_arithmetic(c: &mut Criterion) {
    // Identity rules: f(x, 0) → x, f(0, x) → x
    let rules = vec![
        ERewriteRule {
            lhs: Pattern::App {
                symbol: "add".to_string(),
                args: vec![
                    Pattern::Var("x".to_string()),
                    Pattern::App { symbol: "zero".to_string(), args: vec![] },
                ],
            },
            rhs: Pattern::Var("x".to_string()),
            label: Some("add-zero-r".to_string()),
        },
        ERewriteRule {
            lhs: Pattern::App {
                symbol: "add".to_string(),
                args: vec![
                    Pattern::App { symbol: "zero".to_string(), args: vec![] },
                    Pattern::Var("x".to_string()),
                ],
            },
            rhs: Pattern::Var("x".to_string()),
            label: Some("add-zero-l".to_string()),
        },
    ];

    c.bench_function("egraph/saturation_arithmetic", |b| {
        b.iter(|| {
            let mut eg = EGraph::new();
            let zero = eg.add(ENode { symbol: "zero".into(), children: vec![] });
            let one = eg.add(ENode { symbol: "one".into(), children: vec![] });
            let two = eg.add(ENode { symbol: "two".into(), children: vec![] });
            eg.add(ENode { symbol: "add".into(), children: vec![one, zero] });
            eg.add(ENode { symbol: "add".into(), children: vec![zero, two] });
            eg.add(ENode { symbol: "add".into(), children: vec![one, two] });
            black_box(eg.saturate(black_box(&rules)));
        });
    });
}

fn bench_extract_ast_size(c: &mut Criterion) {
    c.bench_function("egraph/extract_ast_size", |b| {
        b.iter(|| {
            let mut eg = EGraph::new();
            // Build a tree and saturate with idempotence
            let a = eg.add(ENode { symbol: "a".into(), children: vec![] });
            let fa = eg.add(ENode { symbol: "f".into(), children: vec![a] });
            let ffa = eg.add(ENode { symbol: "f".into(), children: vec![fa] });
            eg.merge(a, ffa);
            eg.rebuild();
            black_box(eg.extract(black_box(a), &AstSize));
        });
    });
}

fn bench_pattern_matching(c: &mut Criterion) {
    let pattern = Pattern::App {
        symbol: "f".to_string(),
        args: vec![Pattern::Var("x".to_string()), Pattern::Var("y".to_string())],
    };

    c.bench_function("egraph/pattern_matching", |b| {
        b.iter(|| {
            let mut eg = EGraph::new();
            // Build ~100 e-classes with various f-nodes
            let mut ids = Vec::new();
            for i in 0..20 {
                ids.push(eg.add(ENode { symbol: format!("c{}", i), children: vec![] }));
            }
            for i in 0..20 {
                for j in 0..5 {
                    let left = ids[i];
                    let right = ids[(i + j + 1) % 20];
                    eg.add(ENode { symbol: "f".into(), children: vec![left, right] });
                }
            }
            black_box(eg.search_pattern(black_box(&pattern)));
        });
    });
}

criterion_group!(
    benches,
    bench_add_term,
    bench_saturation_commutative,
    bench_saturation_arithmetic,
    bench_extract_ast_size,
    bench_pattern_matching,
);
criterion_main!(benches);
