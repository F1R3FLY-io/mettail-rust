use criterion::{criterion_group, criterion_main, Criterion};
use std::sync::Arc;

use mettail_prattail::sft::{
    case_fold_sft, compose_chain, OutputFunction, SymbolicFiniteTransducer,
};
use mettail_prattail::symbolic::{IntervalAlgebra, IntervalPred};

fn bench_transduce_identity(c: &mut Criterion) {
    let alg = IntervalAlgebra::new(0, 1000);
    let mut sft = SymbolicFiniteTransducer::new(alg.clone(), alg);
    let q0 = sft.add_state(true, None);
    sft.set_initial(q0);
    sft.add_transition(q0, q0, IntervalPred::True, OutputFunction::Identity);

    let input: Vec<i64> = (0..100).collect();

    c.bench_function("sft/transduce_identity", |b| {
        b.iter(|| sft.transduce(&input))
    });
}

fn bench_transduce_case_fold(c: &mut Criterion) {
    let sft = case_fold_sft();
    let input: Vec<char> = "The Quick Brown Fox Jumps Over The Lazy Dog"
        .chars()
        .collect();

    c.bench_function("sft/transduce_case_fold", |b| {
        b.iter(|| sft.transduce(&input))
    });
}

fn bench_compose_chain(c: &mut Criterion) {
    let alg = IntervalAlgebra::new(0, 1000);
    let chain: Vec<SymbolicFiniteTransducer<IntervalAlgebra, IntervalAlgebra>> = (0..5)
        .map(|_| {
            let mut sft = SymbolicFiniteTransducer::new(alg.clone(), alg.clone());
            let q0 = sft.add_state(true, None);
            sft.set_initial(q0);
            sft.add_transition(q0, q0, IntervalPred::True, OutputFunction::Identity);
            sft
        })
        .collect();

    c.bench_function("sft/compose_chain", |b| {
        b.iter(|| compose_chain(&chain))
    });
}

fn bench_pre_image(c: &mut Criterion) {
    let alg = IntervalAlgebra::new(0, 1000);
    let mut sft = SymbolicFiniteTransducer::new(alg.clone(), alg.clone());
    let q0 = sft.add_state(true, None);
    sft.set_initial(q0);
    sft.add_transition(q0, q0, IntervalPred::True, OutputFunction::Identity);

    let mut acceptor = mettail_prattail::symbolic::SymbolicAutomaton::new(alg);
    let s0 = acceptor.add_state(true, None);
    acceptor.set_initial(s0);
    acceptor.add_transition(s0, s0, IntervalPred::Range(0, 500));

    c.bench_function("sft/pre_image", |b| {
        b.iter(|| sft.pre_image(&acceptor))
    });
}

fn bench_is_functional(c: &mut Criterion) {
    let alg = IntervalAlgebra::new(0, 1000);
    let mut sft = SymbolicFiniteTransducer::new(alg.clone(), alg);
    // Build a 20-state SFT with various transitions.
    let mut states = Vec::with_capacity(20);
    for i in 0..20 {
        let s = sft.add_state(i == 19, None);
        states.push(s);
    }
    sft.set_initial(states[0]);
    for i in 0..19 {
        let lo = (i * 50) as i64;
        let hi = lo + 50;
        sft.add_transition(
            states[i],
            states[i + 1],
            IntervalPred::Range(lo, hi),
            OutputFunction::Map(Arc::new(move |x: &i64| x + 1)),
        );
    }

    c.bench_function("sft/is_functional", |b| {
        b.iter(|| sft.is_functional())
    });
}

criterion_group!(
    benches,
    bench_transduce_identity,
    bench_transduce_case_fold,
    bench_compose_chain,
    bench_pre_image,
    bench_is_functional,
);
criterion_main!(benches);
