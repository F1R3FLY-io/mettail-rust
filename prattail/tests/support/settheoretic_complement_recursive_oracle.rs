//! Bounded reference equations for the former set-type/complement helper cycle.
//!
//! Production shares one non-recursive universal-automaton constructor. This
//! test-only module retains the historical Negation-to-empty-complement-to-Top
//! call path to pin exact state allocation and transition ordering.

use super::*;
use crate::automata::semiring::BooleanWeight;
use crate::tree_automaton::{TreeAutomaton, TreeTransition};

fn type_to_automaton_recursive(
    system: &SetTheoreticTypeSystem,
    ty: &SetType,
) -> TreeAutomaton<BooleanWeight> {
    match ty {
        SetType::Top => {
            let mut automaton = TreeAutomaton::new();
            let state = automaton.add_state(true);
            for (symbol, &arity) in &system.constructors {
                automaton.add_transition(TreeTransition {
                    symbol: symbol.clone(),
                    child_states: vec![state; arity],
                    target_state: state,
                    weight: BooleanWeight(true),
                });
            }
            automaton
        },
        SetType::Bottom => TreeAutomaton::new(),
        SetType::Negation(inner) => {
            let inner = type_to_automaton_recursive(system, inner);
            complement_automaton_recursive(system, &inner)
        },
        _ => unreachable!("the bounded oracle exercises only Bottom, Negation, and Top"),
    }
}

fn complement_automaton_recursive(
    system: &SetTheoreticTypeSystem,
    automaton: &TreeAutomaton<BooleanWeight>,
) -> TreeAutomaton<BooleanWeight> {
    if automaton.num_states() == 0 {
        type_to_automaton_recursive(system, &SetType::Top)
    } else {
        unreachable!("the bounded oracle complements only the empty automaton")
    }
}

#[test]
fn factored_universal_constructor_preserves_exact_recursive_topology() {
    let mut constructors = HashMap::new();
    constructors.insert("Zero".to_string(), 0);
    constructors.insert("Succ".to_string(), 1);
    constructors.insert("Pair".to_string(), 2);
    let system = SetTheoreticTypeSystem::new(constructors);
    let ty = SetType::Negation(Box::new(SetType::Bottom));

    let actual = system.type_to_automaton(&ty);
    let expected = type_to_automaton_recursive(&system, &ty);
    assert_eq!(actual.states, expected.states);
    assert_eq!(actual.transitions.len(), expected.transitions.len());
    for (actual, expected) in actual.transitions.iter().zip(&expected.transitions) {
        assert_eq!(
            format!("{actual:?}"),
            format!("{expected:?}"),
            "the factored constructor preserves exact transition order"
        );
    }
    assert_eq!(actual.final_states, expected.final_states);
    assert_eq!(actual.ranked_alphabet, expected.ranked_alphabet);
}
