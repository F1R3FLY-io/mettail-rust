use super::*;
use crate::automata::semiring::{BooleanWeight, TropicalWeight};
use crate::runtime_types::Range;
use crate::vpa::{build_token_tree, SymbolKind, TokenTree};

mod recursive {
    #[derive(Debug, Clone, PartialEq, Eq)]
    pub struct Term {
        pub symbol: String,
        pub children: Vec<Term>,
    }

    #[allow(dead_code)]
    #[derive(Debug, Clone)]
    pub enum TokenTree<T> {
        Token(T, crate::runtime_types::Range),
        Group {
            open: (T, crate::runtime_types::Range),
            close: (T, crate::runtime_types::Range),
            children: Vec<TokenTree<T>>,
        },
    }
}

fn recursive_term(term: &Term) -> recursive::Term {
    recursive::Term {
        symbol: term.symbol.clone(),
        children: term.children.iter().map(recursive_term).collect(),
    }
}

fn recursive_bottom_up<W: Semiring>(
    automaton: &TreeAutomaton<W>,
    term: &Term,
) -> HashMap<usize, W> {
    let child_maps: Vec<_> = term
        .children
        .iter()
        .map(|child| recursive_bottom_up(automaton, child))
        .collect();
    let mut result = HashMap::new();
    for transition in &automaton.transitions {
        if transition.symbol != term.symbol || transition.child_states.len() != term.children.len()
        {
            continue;
        }
        let mut weight = transition.weight;
        let mut matched = true;
        for (child_map, &required_state) in child_maps.iter().zip(&transition.child_states) {
            match child_map.get(&required_state) {
                Some(child_weight) => weight = weight.times(child_weight),
                None => {
                    matched = false;
                    break;
                },
            }
        }
        if matched {
            result
                .entry(transition.target_state)
                .and_modify(|existing: &mut W| *existing = existing.plus(&weight))
                .or_insert(weight);
        }
    }
    result
}

fn recursive_propagate<W: Semiring>(
    automaton: &TreeAutomaton<W>,
    term: &Term,
    current_states: &HashMap<usize, W>,
    annotations: &mut [HashMap<usize, W>],
    node_index: usize,
) -> usize {
    for (&state, weight) in current_states {
        annotations[node_index]
            .entry(state)
            .and_modify(|existing| *existing = existing.plus(weight))
            .or_insert(*weight);
    }
    if term.children.is_empty() {
        return node_index + 1;
    }
    let mut child_maps = vec![HashMap::new(); term.children.len()];
    for (&parent_state, parent_weight) in current_states {
        for transition in &automaton.transitions {
            if transition.target_state != parent_state
                || transition.symbol != term.symbol
                || transition.child_states.len() != term.children.len()
            {
                continue;
            }
            let weight = parent_weight.times(&transition.weight);
            for (child_map, &child_state) in child_maps.iter_mut().zip(&transition.child_states) {
                child_map
                    .entry(child_state)
                    .and_modify(|existing: &mut W| *existing = existing.plus(&weight))
                    .or_insert(weight);
            }
        }
    }
    let mut next_index = node_index + 1;
    for (child, child_map) in term.children.iter().zip(&child_maps) {
        next_index = recursive_propagate(automaton, child, child_map, annotations, next_index);
    }
    next_index
}

fn recursive_top_down<W: Semiring>(
    automaton: &TreeAutomaton<W>,
    term: &Term,
    root_states: &HashMap<usize, W>,
) -> Vec<HashMap<usize, W>> {
    let mut annotations = vec![HashMap::new(); term.size()];
    recursive_propagate(automaton, term, root_states, &mut annotations, 0);
    annotations
}

fn recursive_token_term<T: std::fmt::Debug>(
    tree: &TokenTree<T>,
    symbol: &dyn Fn(&T) -> String,
) -> Term {
    match tree {
        TokenTree::Token(token, _) => Term::leaf(symbol(token)),
        TokenTree::Group { open, children, .. } => Term::new(
            symbol(&open.0),
            children
                .iter()
                .map(|child| recursive_token_term(child, symbol))
                .collect(),
        ),
    }
}

fn recursive_token_tree<T: Clone>(tree: &TokenTree<T>) -> recursive::TokenTree<T> {
    match tree {
        TokenTree::Token(token, range) => recursive::TokenTree::Token(token.clone(), *range),
        TokenTree::Group { open, close, children } => recursive::TokenTree::Group {
            open: open.clone(),
            close: close.clone(),
            children: children.iter().map(recursive_token_tree).collect(),
        },
    }
}

fn fixture_automaton() -> TreeAutomaton<TropicalWeight> {
    let mut automaton = TreeAutomaton::new();
    let leaf = automaton.add_state(false);
    let expr = automaton.add_state(true);
    automaton.add_transition(TreeTransition::leaf("A", leaf, TropicalWeight(1.0)));
    automaton.add_transition(TreeTransition::leaf("B", leaf, TropicalWeight(2.0)));
    automaton.add_transition(TreeTransition::binary("Pair", leaf, leaf, expr, TropicalWeight(3.0)));
    automaton
}

#[test]
fn iterative_tree_operations_match_recursive_oracles() {
    let automaton = fixture_automaton();
    let term = Term::new("Pair", vec![Term::leaf("A"), Term::leaf("B")]);
    let recursive_term = recursive_term(&term);
    assert_eq!(format!("{term:?}"), format!("{recursive_term:?}"));
    assert_eq!(term.clone(), term);
    assert_eq!(term.size(), 3);
    assert_eq!(term.to_string(), "Pair(A, B)");

    let actual_bottom_up = bottom_up_evaluate(&automaton, &term);
    let expected_bottom_up = recursive_bottom_up(&automaton, &term);
    assert_eq!(actual_bottom_up, expected_bottom_up);
    assert_eq!(
        top_down_propagate(&automaton, &term, &actual_bottom_up),
        recursive_top_down(&automaton, &term, &expected_bottom_up)
    );

    let range = Range::zero();
    let tree = TokenTree::Group {
        open: ("Pair".to_string(), range),
        close: (")".to_string(), range),
        children: vec![
            TokenTree::Token("A".to_string(), range),
            TokenTree::Token("B".to_string(), range),
        ],
    };
    assert_eq!(format!("{tree:?}"), format!("{:?}", recursive_token_tree(&tree)));
    assert_eq!(
        token_tree_to_term(&tree, &Clone::clone),
        recursive_token_term(&tree, &Clone::clone)
    );
}

#[test]
fn tree_automaton_and_token_tree_pdas_handle_depth_20k_on_a_256k_stack() {
    std::thread::Builder::new()
        .name("prattail-tree-automaton-small-stack".to_string())
        .stack_size(256 * 1024)
        .spawn(|| {
            const DEPTH: usize = 20_000;
            let mut automaton = TreeAutomaton::new();
            let state = automaton.add_state(true);
            automaton.add_transition(TreeTransition::leaf("X", state, BooleanWeight(true)));
            automaton.add_transition(TreeTransition::unary("N", state, state, BooleanWeight(true)));

            let mut term = Term::leaf("X");
            for _ in 0..DEPTH {
                term = Term::new("N", vec![term]);
            }
            assert_eq!(term.clone(), term);
            assert_eq!(term.size(), DEPTH + 1);
            assert!(format!("{term:?}").starts_with("Term { symbol: \"N\""));
            assert!(term.to_string().starts_with("N(N(N("));
            let root_states = bottom_up_evaluate(&automaton, &term);
            assert_eq!(root_states[&state], BooleanWeight(true));
            assert_eq!(top_down_propagate(&automaton, &term, &root_states).len(), DEPTH + 1);

            let range = Range::zero();
            let mut tokens = Vec::with_capacity(DEPTH * 2 + 1);
            tokens.extend((0..DEPTH).map(|_| ("N".to_string(), range)));
            tokens.push(("X".to_string(), range));
            tokens.extend((0..DEPTH).map(|_| (")".to_string(), range)));
            let mut skip = vec![None; tokens.len()];
            for index in 0..DEPTH {
                skip[index] = Some(DEPTH * 2 - index);
            }
            let trees = build_token_tree(&tokens, &skip, |token| match token.as_str() {
                "N" => SymbolKind::Call,
                ")" => SymbolKind::Return,
                _ => SymbolKind::Internal,
            });
            assert_eq!(trees.len(), 1);
            let converted = token_tree_to_term(&trees[0], &Clone::clone);
            assert_eq!(converted, term);
            assert_eq!(trees[0].clone().children_depth_for_test(), DEPTH);
        })
        .expect("small-stack thread starts")
        .join()
        .expect("tree-automaton and token-tree PDAs do not overflow a 256 KiB stack");
}

trait TokenTreeDepthForTest {
    fn children_depth_for_test(&self) -> usize;
}

impl<T> TokenTreeDepthForTest for TokenTree<T> {
    fn children_depth_for_test(&self) -> usize {
        let mut depth = 0;
        let mut current = self;
        while let TokenTree::Group { children, .. } = current {
            depth += 1;
            current = &children[0];
        }
        depth
    }
}
