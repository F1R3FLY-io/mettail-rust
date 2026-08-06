use std::collections::{HashMap, HashSet};

use mettail_prattail::alternating::BranchingMode;
use mettail_prattail::automata::semiring::{BooleanWeight, Semiring};
use mettail_prattail::parity_tree::{evaluate_term, ParityAlternatingTreeAutomaton, Term};

fn recursive_oracle(
    automaton: &ParityAlternatingTreeAutomaton<BooleanWeight>,
    term: &Term,
) -> bool {
    let Some(initial) = automaton.initial_state else {
        return false;
    };
    if automaton.num_states() == 0 || initial >= automaton.num_states() {
        return false;
    }

    let mut transitions = HashMap::new();
    for transition in &automaton.transitions {
        transitions
            .entry((transition.from, transition.symbol.as_str()))
            .or_insert_with(Vec::new)
            .push(&transition.directions);
    }

    fn eval<'a>(
        term: &Term,
        automaton: &'a ParityAlternatingTreeAutomaton<BooleanWeight>,
        transitions: &HashMap<(usize, &'a str), Vec<&'a Vec<(usize, usize, BooleanWeight)>>>,
    ) -> HashSet<usize> {
        let child_results = term
            .children
            .iter()
            .map(|child| eval(child, automaton, transitions))
            .collect::<Vec<_>>();
        let mut accepting = HashSet::new();
        for state in &automaton.states {
            let Some(candidates) = transitions.get(&(state.id, term.symbol.as_str())) else {
                continue;
            };
            let satisfies = |directions: &&Vec<(usize, usize, BooleanWeight)>| {
                directions.iter().all(|&(child, target, weight)| {
                    weight == BooleanWeight::zero()
                        || child_results
                            .get(child)
                            .is_some_and(|states| states.contains(&target))
                })
            };
            let accepted = match state.branching {
                BranchingMode::Existential => candidates.iter().any(satisfies),
                BranchingMode::Universal => candidates.iter().all(satisfies),
            };
            if accepted {
                accepting.insert(state.id);
            }
        }
        accepting
    }

    eval(term, automaton, &transitions).contains(&initial)
}

fn differential_automaton() -> ParityAlternatingTreeAutomaton<BooleanWeight> {
    let mut automaton = ParityAlternatingTreeAutomaton::new(2);
    let any_a = automaton.add_state(BranchingMode::Existential, 0, None);
    let all_b = automaton.add_state(BranchingMode::Universal, 0, None);
    let root = automaton.add_state(BranchingMode::Existential, 0, None);
    automaton.initial_state = Some(root);
    automaton.add_transition(any_a, "a".into(), Vec::new());
    automaton.add_transition(any_a, "f".into(), vec![(0, any_a, BooleanWeight::one())]);
    automaton.add_transition(all_b, "b".into(), Vec::new());
    automaton.add_transition(
        all_b,
        "f".into(),
        vec![(0, all_b, BooleanWeight::one()), (1, all_b, BooleanWeight::one())],
    );
    automaton.add_transition(
        root,
        "pair".into(),
        vec![(0, any_a, BooleanWeight::one()), (1, all_b, BooleanWeight::one())],
    );
    automaton
}

#[test]
fn iterative_evaluator_matches_the_recursive_oracle() {
    let automaton = differential_automaton();
    let corpus = [
        Term::leaf("a"),
        Term::leaf("pair"),
        Term::node("pair", vec![Term::leaf("a"), Term::leaf("b")]),
        Term::node(
            "pair",
            vec![
                Term::node("f", vec![Term::leaf("a")]),
                Term::node("f", vec![Term::leaf("b"), Term::leaf("b")]),
            ],
        ),
        Term::node("pair", vec![Term::leaf("wrong"), Term::leaf("b")]),
        Term::node("pair", vec![Term::leaf("a"), Term::node("f", vec![Term::leaf("b")])]),
    ];

    for term in &corpus {
        assert_eq!(
            evaluate_term(&automaton, term),
            recursive_oracle(&automaton, term),
            "iterative evaluator diverged for {term:?}",
        );
    }
}

#[test]
fn deep_evaluation_and_lifecycle_fit_on_a_small_native_stack() {
    const DEPTH: usize = 20_000;
    let handle = std::thread::Builder::new()
        .name("parity-tree-small-stack".into())
        .stack_size(256 * 1024)
        .spawn(|| {
            let mut automaton = ParityAlternatingTreeAutomaton::new(1);
            let state = automaton.add_state(BranchingMode::Existential, 0, None);
            automaton.initial_state = Some(state);
            automaton.add_transition(state, "leaf".into(), Vec::new());
            automaton.add_transition(state, "node".into(), vec![(0, state, BooleanWeight::one())]);

            let mut term = Term::leaf("leaf");
            for _ in 0..DEPTH {
                term = Term::node("node", vec![term]);
            }

            assert!(evaluate_term(&automaton, &term));
            let cloned = term.clone();
            assert_eq!(term, cloned);
            let display = term.to_string();
            assert!(display.starts_with("node(node("));
            assert!(display.ends_with("))"));
            let debug = format!("{term:?}");
            assert!(debug.starts_with("Term { symbol: \"node\", children: [Term"));
            assert!(debug.ends_with("] }"));
            drop(cloned);
            drop(term);
        })
        .expect("small-stack parity-tree test thread must spawn");
    handle
        .join()
        .expect("parity-tree operations must not overflow the native stack");
}
