use mettail_prattail::algebra_tower::Sat3;
use mettail_prattail::guard_formula::{
    ground_verdict_with, satisfiable, GuardAssignment, GuardAtom, GuardAtomKind, GuardFormula,
    GuardVarMap, SubstrateConfig,
};
use mettail_prattail::kat::BooleanTest;
use mettail_prattail::presburger::PresburgerPred;

const DEPTH: usize = 20_000;
const SMALL_STACK_BYTES: usize = 256 * 1024;

fn on_small_stack(test: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .name("guard-formula-small-stack".to_string())
        .stack_size(SMALL_STACK_BYTES)
        .spawn(test)
        .expect("spawn GuardFormula small-stack gate")
        .join()
        .expect("GuardFormula small-stack gate panicked");
}

fn atom(id: u32) -> GuardFormula {
    GuardFormula::Atom(GuardAtom { id, kind: GuardAtomKind::Uncovered })
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum DebugOracle {
    True,
    False,
    And(Box<DebugOracle>, Box<DebugOracle>),
    Or(Box<DebugOracle>, Box<DebugOracle>),
    Not(Box<DebugOracle>),
    Implies(Box<DebugOracle>, Box<DebugOracle>),
    Atom(GuardAtom),
}

fn recursive_ground<F>(formula: &GuardFormula, resolve_atom: &mut F) -> Sat3
where
    F: FnMut(GuardAtom) -> Sat3,
{
    match formula {
        GuardFormula::True => Sat3::Sat,
        GuardFormula::False => Sat3::Unsat,
        GuardFormula::And(left, right) => match recursive_ground(left, resolve_atom) {
            Sat3::Sat => recursive_ground(right, resolve_atom),
            Sat3::Unsat => Sat3::Unsat,
            Sat3::DontKnow => Sat3::DontKnow,
        },
        GuardFormula::Or(left, right) => match recursive_ground(left, resolve_atom) {
            Sat3::Unsat => recursive_ground(right, resolve_atom),
            Sat3::Sat => Sat3::Sat,
            Sat3::DontKnow => Sat3::DontKnow,
        },
        GuardFormula::Not(inner) => recursive_ground(inner, resolve_atom).not(),
        GuardFormula::Implies(left, right) => match recursive_ground(left, resolve_atom) {
            Sat3::Sat => recursive_ground(right, resolve_atom),
            Sat3::Unsat => Sat3::Sat,
            Sat3::DontKnow => Sat3::DontKnow,
        },
        GuardFormula::Atom(atom) => resolve_atom(*atom),
        GuardFormula::Linear(_)
        | GuardFormula::Prop(_)
        | GuardFormula::Scalar { .. }
        | GuardFormula::ScalarRel { .. } => {
            panic!("the shallow recursive oracle only accepts boolean/opaque formulae")
        },
    }
}

fn verdict_for(atom: GuardAtom) -> Sat3 {
    match atom.id % 3 {
        0 => Sat3::Sat,
        1 => Sat3::Unsat,
        _ => Sat3::DontKnow,
    }
}

#[test]
fn lifecycle_and_debug_match_the_former_recursive_derives() {
    let guard_atom = GuardAtom { id: 7, kind: GuardAtomKind::Spatial };
    let formula = GuardFormula::Implies(
        Box::new(GuardFormula::And(
            Box::new(GuardFormula::True),
            Box::new(GuardFormula::Not(Box::new(GuardFormula::Atom(guard_atom)))),
        )),
        Box::new(GuardFormula::Or(
            Box::new(GuardFormula::False),
            Box::new(GuardFormula::Atom(guard_atom)),
        )),
    );
    let oracle = DebugOracle::Implies(
        Box::new(DebugOracle::And(
            Box::new(DebugOracle::True),
            Box::new(DebugOracle::Not(Box::new(DebugOracle::Atom(guard_atom)))),
        )),
        Box::new(DebugOracle::Or(
            Box::new(DebugOracle::False),
            Box::new(DebugOracle::Atom(guard_atom)),
        )),
    );

    assert_eq!(format!("{formula:?}"), format!("{oracle:?}"));
    assert_eq!(formula, formula.clone());
}

#[test]
fn iterative_ground_pda_matches_the_left_strict_recursive_oracle() {
    let formulas = [
        GuardFormula::And(Box::new(atom(2)), Box::new(atom(0))),
        GuardFormula::Or(Box::new(atom(0)), Box::new(atom(1))),
        GuardFormula::Implies(Box::new(atom(1)), Box::new(atom(2))),
        GuardFormula::Not(Box::new(GuardFormula::Or(
            Box::new(atom(1)),
            Box::new(GuardFormula::And(Box::new(atom(0)), Box::new(atom(2)))),
        ))),
    ];
    let assignment = GuardAssignment::with_len(0);
    let vars = GuardVarMap::new();

    for formula in formulas {
        let mut oracle_trace = Vec::new();
        let oracle = recursive_ground(&formula, &mut |atom| {
            oracle_trace.push(atom.id);
            verdict_for(atom)
        });

        let mut pda_trace = Vec::new();
        let pda = ground_verdict_with(
            &formula,
            &assignment,
            &vars,
            SubstrateConfig::DEFAULT,
            &mut |atom| {
                pda_trace.push(atom.id);
                verdict_for(atom)
            },
        );

        assert_eq!(pda, oracle);
        assert_eq!(pda_trace, oracle_trace, "resolver order or short-circuiting changed");
    }
}

#[test]
fn lifecycle_walkers_and_ground_evaluation_are_stack_safe_at_depth_20k() {
    on_small_stack(|| {
        let mut formula = atom(0);
        for id in 1..=DEPTH as u32 {
            formula = GuardFormula::And(Box::new(formula), Box::new(atom(id)));
        }

        let cloned = formula.clone();
        assert_eq!(formula, cloned);
        assert!(!formula.reaches_substrate());
        assert_eq!(formula.atoms().len(), DEPTH + 1);
        assert!(formula.int_vars().is_empty());
        assert!(formula.prop_names().is_empty());
        assert!(formula.scalar_vars().is_empty());

        let debug = format!("{formula:?}");
        assert!(debug.starts_with("And(And("));
        assert!(debug.ends_with(')'));

        let mut expected_id = 0u32;
        let verdict = ground_verdict_with(
            &formula,
            &GuardAssignment::with_len(0),
            &GuardVarMap::new(),
            SubstrateConfig::DEFAULT,
            &mut |atom| {
                assert_eq!(atom.id, expected_id, "resolver traversal order changed");
                expected_id += 1;
                Sat3::Sat
            },
        );
        assert_eq!(verdict, Sat3::Sat);
        assert_eq!(expected_id as usize, DEPTH + 1);

        drop(cloned);
        drop(formula);
    });
}

#[test]
fn theory_projection_and_mixed_conjunct_partition_are_stack_safe_at_depth_20k() {
    on_small_stack(|| {
        let mut linear = GuardFormula::Linear(PresburgerPred::leq(vec![(7, 1)], 0));
        for _ in 0..DEPTH {
            linear = GuardFormula::Not(Box::new(linear));
        }
        assert_eq!(linear.int_vars(), vec![7]);
        assert_eq!(satisfiable(&linear, SubstrateConfig { bit_width: 1 }), Sat3::Sat);
        drop(linear);

        let mut mixed = GuardFormula::And(
            Box::new(GuardFormula::Linear(PresburgerPred::leq(vec![(0, 1)], 0))),
            Box::new(GuardFormula::Prop(BooleanTest::Atom("ready".to_string()))),
        );
        for _ in 0..DEPTH {
            mixed = GuardFormula::And(Box::new(mixed), Box::new(GuardFormula::True));
        }
        assert_eq!(mixed.int_vars(), vec![0]);
        assert_eq!(mixed.prop_names(), vec!["ready".to_string()]);
        assert_eq!(satisfiable(&mixed, SubstrateConfig { bit_width: 1 }), Sat3::Sat);
        drop(mixed);
    });
}
