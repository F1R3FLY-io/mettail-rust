use criterion::{black_box, criterion_group, criterion_main, Criterion};
use std::collections::HashMap;

use mettail_prattail::lattice_theory::{LatticeStore, LatticeTheory, SubtypeConstraint, TypeId};
use mettail_prattail::logict::ConstraintTheory;
use mettail_prattail::type_system::{LatticeTypeSystem, TypeSystem};

// ── Helpers ────────────────────────────────────────────────────────────────

/// Build a chain lattice: T0 <: T1 <: ... <: T_{depth-1}
fn build_lattice_type_system(depth: usize) -> (LatticeTypeSystem, Vec<TypeId>) {
    let ids: Vec<TypeId> = (0..depth).collect();

    let mut names = HashMap::with_capacity(depth);
    for &id in &ids {
        names.insert(id, format!("T{}", id));
    }
    let theory = LatticeTheory::new(ids.clone(), names);
    let mut store = LatticeStore::new();

    for i in 0..depth.saturating_sub(1) {
        let constraint = SubtypeConstraint {
            sub: ids[i],
            sup: ids[i + 1],
        };
        store = theory
            .propagate(&store, &constraint)
            .expect("propagation should succeed");
    }

    let sys = LatticeTypeSystem::new(theory, store, HashMap::new());
    (sys, ids)
}

/// Build a diamond lattice: Bot <: Left, Bot <: Right, Left <: Top, Right <: Top
fn build_diamond_lattice() -> (LatticeTypeSystem, Vec<TypeId>) {
    let bot: TypeId = 0;
    let left: TypeId = 1;
    let right: TypeId = 2;
    let top: TypeId = 3;

    let ids = vec![bot, left, right, top];
    let mut names = HashMap::new();
    names.insert(bot, "Bot".to_string());
    names.insert(left, "Left".to_string());
    names.insert(right, "Right".to_string());
    names.insert(top, "Top".to_string());

    let theory = LatticeTheory::new(ids.clone(), names);
    let mut store = LatticeStore::new();

    for (sub, sup) in &[(bot, left), (bot, right), (left, top), (right, top)] {
        let constraint = SubtypeConstraint {
            sub: *sub,
            sup: *sup,
        };
        store = theory
            .propagate(&store, &constraint)
            .expect("propagation should succeed");
    }

    let sys = LatticeTypeSystem::new(theory, store, HashMap::new());
    (sys, ids)
}

// ── Benchmarks ─────────────────────────────────────────────────────────────

fn bench_lattice_subtype(c: &mut Criterion) {
    let mut group = c.benchmark_group("type_system/lattice_subtype");

    for &depth in &[5, 20, 100] {
        let (sys, ids) = build_lattice_type_system(depth);
        let env = sys.empty_env();

        group.bench_function(format!("chain_{}_reflexive", depth), |b| {
            b.iter(|| {
                for id in &ids {
                    black_box(sys.is_subtype(&env, id, id));
                }
            })
        });

        group.bench_function(format!("chain_{}_transitive", depth), |b| {
            b.iter(|| {
                // Check first <: last (longest transitive chain)
                black_box(sys.is_subtype(&env, &ids[0], &ids[depth - 1]));
            })
        });

        group.bench_function(format!("chain_{}_negative", depth), |b| {
            b.iter(|| {
                // Check last <: first (should be false)
                black_box(sys.is_subtype(&env, &ids[depth - 1], &ids[0]));
            })
        });
    }

    group.finish();
}

fn bench_lattice_join_meet(c: &mut Criterion) {
    let mut group = c.benchmark_group("type_system/lattice_join_meet");

    let (sys, ids) = build_diamond_lattice();
    let env = sys.empty_env();

    group.bench_function("diamond_join", |b| {
        b.iter(|| {
            // join(Left, Right) should be Top
            black_box(sys.join(&env, &ids[1], &ids[2]));
        })
    });

    group.bench_function("diamond_meet", |b| {
        b.iter(|| {
            // meet(Left, Right) should be Bot
            black_box(sys.meet(&env, &ids[1], &ids[2]));
        })
    });

    group.finish();
}

fn bench_refinement_satisfiability(c: &mut Criterion) {
    let mut group = c.benchmark_group("type_system/refinement_satisfiability");

    let (base_sys, ids) = build_lattice_type_system(10);
    let env = base_sys.empty_env();

    group.bench_function("base_inhabited_check", |b| {
        b.iter(|| {
            for id in &ids {
                black_box(base_sys.is_inhabited(&env, id));
            }
        })
    });

    group.finish();
}

fn bench_refinement_subtyping(c: &mut Criterion) {
    let mut group = c.benchmark_group("type_system/refinement_subtyping");

    let (sys, ids) = build_lattice_type_system(20);
    let env = sys.empty_env();

    // Pairwise subtype checking (simulates refinement dispatch analysis)
    group.bench_function("pairwise_20_types", |b| {
        b.iter(|| {
            let mut count = 0usize;
            for i in 0..ids.len() {
                for j in (i + 1)..ids.len() {
                    if sys.is_subtype(&env, &ids[i], &ids[j]) {
                        count += 1;
                    }
                }
            }
            black_box(count);
        })
    });

    group.finish();
}

fn bench_set_theoretic_inclusion(c: &mut Criterion) {
    let mut group = c.benchmark_group("type_system/set_theoretic");

    #[cfg(feature = "set-theoretic-types")]
    {
        use mettail_prattail::type_system::{SetTheoreticTypeSystem, SetType};

        let mut ctors = HashMap::new();
        for i in 0..10 {
            ctors.insert(format!("C{}", i), 0); // nullary constructors
        }
        let sys = SetTheoreticTypeSystem::new(ctors);
        let env = sys.empty_env();

        let atom_a = SetType::Atom("C0".to_string());
        let atom_b = SetType::Atom("C1".to_string());
        let union_ab = SetType::Union(Box::new(atom_a.clone()), Box::new(atom_b.clone()));

        group.bench_function("atom_subtype_union", |b| {
            b.iter(|| {
                black_box(sys.is_subtype(&env, &atom_a, &union_ab));
            })
        });

        group.bench_function("union_subtype_atom", |b| {
            b.iter(|| {
                black_box(sys.is_subtype(&env, &union_ab, &atom_a));
            })
        });

        let intersection =
            SetType::Intersection(Box::new(atom_a.clone()), Box::new(atom_b.clone()));

        group.bench_function("intersection_inhabited", |b| {
            b.iter(|| {
                black_box(sys.is_inhabited(&env, &intersection));
            })
        });

        let negation = SetType::Negation(Box::new(atom_a.clone()));

        group.bench_function("negation_subtype", |b| {
            b.iter(|| {
                black_box(sys.is_subtype(&env, &negation, &SetType::Top));
            })
        });
    }

    #[cfg(not(feature = "set-theoretic-types"))]
    {
        group.bench_function("skipped_no_feature", |b| b.iter(|| black_box(true)));
    }

    group.finish();
}

fn bench_sfa_dispatch(c: &mut Criterion) {
    let mut group = c.benchmark_group("type_system/sfa_dispatch");

    let (sys, ids) = build_lattice_type_system(10);
    let env = sys.empty_env();

    group.bench_function("pairwise_overlap_10", |b| {
        b.iter(|| {
            let mut disjoint = 0usize;
            let mut overlap = 0usize;
            for i in 0..ids.len() {
                for j in (i + 1)..ids.len() {
                    if sys.is_subtype(&env, &ids[i], &ids[j])
                        || sys.is_subtype(&env, &ids[j], &ids[i])
                    {
                        overlap += 1;
                    } else {
                        disjoint += 1;
                    }
                }
            }
            black_box((disjoint, overlap));
        })
    });

    group.finish();
}

criterion_group!(
    benches,
    bench_lattice_subtype,
    bench_lattice_join_meet,
    bench_refinement_satisfiability,
    bench_refinement_subtyping,
    bench_set_theoretic_inclusion,
    bench_sfa_dispatch,
);
criterion_main!(benches);
