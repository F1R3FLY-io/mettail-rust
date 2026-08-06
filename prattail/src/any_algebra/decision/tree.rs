use std::collections::{BTreeSet, HashMap, HashSet};

use crate::sym_tree::{SymTerm, TreeAlgebra, TreeNode, TreePred};
use crate::symbolic::BooleanAlgebra;

use super::super::{AnyAlgebra, AnyDomain, AnyPred};
use super::solver::DecisionOracle;

struct TreeEdge {
    constructor: String,
    payload_guard: Option<AnyPred>,
    child_states: Vec<usize>,
    target: usize,
}

pub(super) struct DecisionTree {
    num_states: usize,
    transitions: Vec<TreeEdge>,
    accepting: HashSet<usize>,
    arities: HashMap<String, usize>,
}

impl DecisionTree {
    fn new() -> Self {
        Self {
            num_states: 0,
            transitions: Vec::new(),
            accepting: HashSet::new(),
            arities: HashMap::new(),
        }
    }

    fn union(mut self, other: Self) -> Self {
        let offset = self.num_states;
        self.num_states += other.num_states;
        self.transitions
            .extend(other.transitions.into_iter().map(|edge| {
                TreeEdge {
                    constructor: edge.constructor,
                    payload_guard: edge.payload_guard,
                    child_states: edge
                        .child_states
                        .into_iter()
                        .map(|state| state + offset)
                        .collect(),
                    target: edge.target + offset,
                }
            }));
        self.accepting
            .extend(other.accepting.into_iter().map(|state| state + offset));
        self.arities.extend(other.arities);
        self
    }
}

fn universal(algebra: &TreeAlgebra<AnyAlgebra>) -> DecisionTree {
    let mut automaton = DecisionTree::new();
    automaton.arities = algebra.arities.clone();
    automaton.num_states = 1;
    automaton.accepting.insert(0);
    for (constructor, arity) in &algebra.arities {
        automaton.transitions.push(TreeEdge {
            constructor: constructor.clone(),
            payload_guard: algebra
                .payloaded
                .contains(constructor)
                .then(|| algebra.elem.true_pred()),
            child_states: vec![0; *arity],
            target: 0,
        });
    }
    automaton
}

fn empty(algebra: &TreeAlgebra<AnyAlgebra>) -> DecisionTree {
    let mut automaton = DecisionTree::new();
    automaton.arities = algebra.arities.clone();
    automaton.num_states = 1;
    automaton
}

fn assemble_node(
    algebra: &TreeAlgebra<AnyAlgebra>,
    constructor: String,
    mut payload_guard: Option<AnyPred>,
    mut children: Vec<DecisionTree>,
) -> DecisionTree {
    let mut child_accepting = vec![Vec::new(); children.len()];
    let base = children
        .iter()
        .enumerate()
        .max_by_key(|(_, automaton)| (automaton.transitions.len(), automaton.num_states))
        .map(|(index, _)| index);
    let mut result = if let Some(index) = base {
        let automaton = std::mem::replace(&mut children[index], DecisionTree::new());
        child_accepting[index] = automaton.accepting.iter().copied().collect();
        automaton
    } else {
        DecisionTree::new()
    };
    for (index, child) in children.into_iter().enumerate() {
        if Some(index) == base {
            continue;
        }
        let offset = result.num_states;
        result.num_states += child.num_states;
        result.arities.extend(child.arities);
        result
            .transitions
            .extend(child.transitions.into_iter().map(|edge| {
                TreeEdge {
                    constructor: edge.constructor,
                    payload_guard: edge.payload_guard,
                    child_states: edge
                        .child_states
                        .into_iter()
                        .map(|state| state + offset)
                        .collect(),
                    target: edge.target + offset,
                }
            }));
        child_accepting[index] = child
            .accepting
            .into_iter()
            .map(|state| state + offset)
            .collect();
    }
    result.arities.extend(algebra.arities.clone());
    let target = result.num_states;
    result.num_states += 1;
    result.accepting.clear();
    result.accepting.insert(target);
    let mut combinations = cartesian(&child_accepting).into_iter().peekable();
    while let Some(child_states) = combinations.next() {
        let edge_guard = if combinations.peek().is_some() {
            payload_guard.clone()
        } else {
            payload_guard.take()
        };
        result.transitions.push(TreeEdge {
            constructor: constructor.clone(),
            payload_guard: edge_guard,
            child_states,
            target,
        });
    }
    result
}

fn cartesian(slots: &[Vec<usize>]) -> Vec<Vec<usize>> {
    let mut combinations = vec![Vec::new()];
    for slot in slots {
        let mut next = Vec::new();
        for prefix in &combinations {
            for state in slot {
                let mut combination = prefix.clone();
                combination.push(*state);
                next.push(combination);
            }
        }
        combinations = next;
    }
    combinations
}

pub(super) async fn compile<'a>(
    oracle: &DecisionOracle<'a>,
    algebra: &'a TreeAlgebra<AnyAlgebra>,
    predicate: TreePred<AnyPred>,
) -> DecisionTree {
    enum Task {
        Visit(TreePred<AnyPred>),
        Node {
            constructor: String,
            payload_guard: Option<AnyPred>,
            child_count: usize,
        },
        And,
        Or,
        Not,
    }
    let mut tasks = vec![Task::Visit(predicate)];
    let mut values = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            Task::Visit(predicate) => match predicate.into_node() {
                TreeNode::True | TreeNode::Wild => values.push(universal(algebra)),
                TreeNode::False => values.push(empty(algebra)),
                TreeNode::Node { constructor, payload_guard, children } => {
                    tasks.push(Task::Node {
                        constructor,
                        payload_guard,
                        child_count: children.len(),
                    });
                    for child in children.into_iter().rev() {
                        tasks.push(Task::Visit(child));
                    }
                },
                TreeNode::And(left, right) => {
                    tasks.push(Task::And);
                    tasks.push(Task::Visit(*right));
                    tasks.push(Task::Visit(*left));
                },
                TreeNode::Or(left, right) => {
                    tasks.push(Task::Or);
                    tasks.push(Task::Visit(*right));
                    tasks.push(Task::Visit(*left));
                },
                TreeNode::Not(body) => {
                    tasks.push(Task::Not);
                    tasks.push(Task::Visit(*body));
                },
            },
            Task::Node { constructor, payload_guard, child_count } => {
                let start = values
                    .len()
                    .checked_sub(child_count)
                    .expect("tree decision lost child automata");
                let children = values.split_off(start);
                values.push(assemble_node(algebra, constructor, payload_guard, children));
            },
            Task::And => {
                let right = values.pop().expect("tree decision lost right intersection");
                let left = values.pop().expect("tree decision lost left intersection");
                values.push(intersect(oracle, &algebra.elem, &left, &right).await);
            },
            Task::Or => {
                let right = values.pop().expect("tree decision lost right union");
                let left = values.pop().expect("tree decision lost left union");
                values.push(left.union(right));
            },
            Task::Not => {
                let body = values.pop().expect("tree decision lost complement body");
                values.push(complement(oracle, algebra, &body).await);
            },
        }
    }
    values.pop().expect("tree decision produced no automaton")
}

async fn intersect<'a>(
    oracle: &DecisionOracle<'a>,
    algebra: &'a AnyAlgebra,
    left: &DecisionTree,
    right: &DecisionTree,
) -> DecisionTree {
    let mut result = DecisionTree::new();
    result.arities.extend(left.arities.clone());
    result.arities.extend(right.arities.clone());
    let mut states = HashMap::new();
    for left_transition in &left.transitions {
        for right_transition in &right.transitions {
            if left_transition.constructor != right_transition.constructor
                || left_transition.child_states.len() != right_transition.child_states.len()
            {
                continue;
            }
            let guard = match (&left_transition.payload_guard, &right_transition.payload_guard) {
                (None, None) => None,
                (Some(left_guard), Some(right_guard)) => {
                    let guard = algebra.and(left_guard, right_guard);
                    if !oracle.sat(algebra, guard.clone()).await {
                        continue;
                    }
                    Some(guard)
                },
                _ => continue,
            };
            let children = left_transition
                .child_states
                .iter()
                .zip(&right_transition.child_states)
                .map(|(&left_state, &right_state)| {
                    state_for(&mut states, &mut result, left_state, right_state)
                })
                .collect();
            let target = state_for(
                &mut states,
                &mut result,
                left_transition.target,
                right_transition.target,
            );
            result.transitions.push(TreeEdge {
                constructor: left_transition.constructor.clone(),
                payload_guard: guard,
                child_states: children,
                target,
            });
        }
    }
    for ((left_state, right_state), state) in states {
        if left.accepting.contains(&left_state) && right.accepting.contains(&right_state) {
            result.accepting.insert(state);
        }
    }
    result
}

fn state_for(
    states: &mut HashMap<(usize, usize), usize>,
    automaton: &mut DecisionTree,
    left: usize,
    right: usize,
) -> usize {
    *states.entry((left, right)).or_insert_with(|| {
        let state = automaton.num_states;
        automaton.num_states += 1;
        state
    })
}

fn index_tuples(width: usize, arity: usize) -> Vec<Vec<usize>> {
    let mut tuples = vec![Vec::new()];
    for _ in 0..arity {
        let mut next = Vec::with_capacity(tuples.len().saturating_mul(width));
        for prefix in &tuples {
            for state in 0..width {
                let mut tuple = prefix.clone();
                tuple.push(state);
                next.push(tuple);
            }
        }
        tuples = next;
    }
    tuples
}

struct ConstructorRegions {
    guards: Vec<AnyPred>,
    regions: Vec<Option<super::solver::Minterm>>,
}

async fn constructor_regions<'a>(
    oracle: &DecisionOracle<'a>,
    algebra: &'a AnyAlgebra,
    automaton: &DecisionTree,
) -> HashMap<String, ConstructorRegions> {
    let mut result = HashMap::new();
    for constructor in automaton.arities.keys() {
        let mut guards = Vec::new();
        let mut has_payload = false;
        for transition in automaton
            .transitions
            .iter()
            .filter(|transition| &transition.constructor == constructor)
        {
            if let Some(guard) = &transition.payload_guard {
                has_payload = true;
                if !guards.iter().any(|candidate| candidate == guard) {
                    guards.push(guard.clone());
                }
            }
        }
        let regions = if has_payload {
            super::solver::minterms(oracle, algebra, &guards)
                .await
                .into_iter()
                .map(Some)
                .collect()
        } else {
            vec![None]
        };
        result.insert(constructor.clone(), ConstructorRegions { guards, regions });
    }
    result
}

fn target_for(
    automaton: &DecisionTree,
    constructor: &str,
    regions: &ConstructorRegions,
    region: &Option<super::solver::Minterm>,
    children: &[&BTreeSet<usize>],
) -> BTreeSet<usize> {
    let mut target = BTreeSet::new();
    for transition in &automaton.transitions {
        if transition.constructor != constructor || transition.child_states.len() != children.len()
        {
            continue;
        }
        let compatible = match (region, &transition.payload_guard) {
            (None, None) => true,
            (Some(region), Some(guard)) => {
                let index = regions
                    .guards
                    .iter()
                    .position(|candidate| candidate == guard)
                    .expect("tree minterm lost a payload guard");
                region.positive[index]
            },
            _ => false,
        };
        if compatible
            && transition
                .child_states
                .iter()
                .zip(children)
                .all(|(state, set)| set.contains(state))
        {
            target.insert(transition.target);
        }
    }
    target
}

async fn determinize<'a>(
    oracle: &DecisionOracle<'a>,
    algebra: &'a TreeAlgebra<AnyAlgebra>,
    automaton: &DecisionTree,
    complement_accepting: bool,
) -> DecisionTree {
    let regions = constructor_regions(oracle, &algebra.elem, automaton).await;
    let mut discovered = vec![BTreeSet::new()];
    let mut seen = HashSet::from([BTreeSet::new()]);
    loop {
        let snapshot = discovered.clone();
        let previous = discovered.len();
        for (constructor, &arity) in &automaton.arities {
            for tuple in index_tuples(snapshot.len(), arity) {
                let children: Vec<&BTreeSet<usize>> =
                    tuple.iter().map(|index| &snapshot[*index]).collect();
                for region in &regions[constructor].regions {
                    let target = target_for(
                        automaton,
                        constructor,
                        &regions[constructor],
                        region,
                        &children,
                    );
                    if seen.insert(target.clone()) {
                        discovered.push(target);
                    }
                }
            }
        }
        if discovered.len() == previous {
            break;
        }
    }
    let ids: HashMap<BTreeSet<usize>, usize> = discovered
        .iter()
        .enumerate()
        .map(|(index, states)| (states.clone(), index))
        .collect();
    let mut result = DecisionTree::new();
    result.num_states = discovered.len();
    result.arities = automaton.arities.clone();
    for (constructor, &arity) in &automaton.arities {
        for tuple in index_tuples(discovered.len(), arity) {
            let children: Vec<&BTreeSet<usize>> =
                tuple.iter().map(|index| &discovered[*index]).collect();
            for region in &regions[constructor].regions {
                let target =
                    target_for(automaton, constructor, &regions[constructor], region, &children);
                result.transitions.push(TreeEdge {
                    constructor: constructor.clone(),
                    payload_guard: region.as_ref().map(|region| region.predicate.clone()),
                    child_states: tuple.clone(),
                    target: ids[&target],
                });
            }
        }
    }
    for (states, id) in ids {
        let intersects = states
            .iter()
            .any(|state| automaton.accepting.contains(state));
        if intersects != complement_accepting {
            result.accepting.insert(id);
        }
    }
    result
}

async fn complement<'a>(
    oracle: &DecisionOracle<'a>,
    algebra: &'a TreeAlgebra<AnyAlgebra>,
    automaton: &DecisionTree,
) -> DecisionTree {
    determinize(oracle, algebra, automaton, true).await
}

pub(super) async fn is_empty<'a>(
    oracle: &DecisionOracle<'a>,
    algebra: &'a AnyAlgebra,
    automaton: DecisionTree,
) -> bool {
    struct Transition {
        children: Vec<usize>,
        target: usize,
    }
    let mut transitions = Vec::with_capacity(automaton.transitions.len());
    for transition in automaton.transitions {
        let satisfiable = match transition.payload_guard {
            None => true,
            Some(guard) => oracle.sat(algebra, guard).await,
        };
        if satisfiable {
            transitions.push(Transition {
                children: transition.child_states,
                target: transition.target,
            });
        }
    }
    let mut productive = std::collections::HashSet::new();
    loop {
        let mut changed = false;
        for transition in &transitions {
            if productive.contains(&transition.target)
                || !transition
                    .children
                    .iter()
                    .all(|state| productive.contains(state))
            {
                continue;
            }
            productive.insert(transition.target);
            changed = true;
        }
        if !changed {
            break;
        }
    }
    !automaton
        .accepting
        .iter()
        .any(|state| productive.contains(state))
}

pub(super) async fn witness<'a>(
    oracle: &DecisionOracle<'a>,
    algebra: &'a AnyAlgebra,
    automaton: DecisionTree,
) -> Option<SymTerm<AnyDomain>> {
    struct Transition {
        constructor: String,
        payload: Option<AnyDomain>,
        children: Vec<usize>,
        target: usize,
    }
    let mut transitions = Vec::with_capacity(automaton.transitions.len());
    for transition in automaton.transitions {
        let payload = match transition.payload_guard {
            None => None,
            Some(guard) => {
                let Some(payload) = oracle.witness(algebra, guard).await else {
                    continue;
                };
                Some(payload)
            },
        };
        transitions.push(Transition {
            constructor: transition.constructor,
            payload,
            children: transition.child_states,
            target: transition.target,
        });
    }
    struct Node {
        constructor: String,
        payload: Option<AnyDomain>,
        children: Vec<usize>,
        size: usize,
    }
    let mut arena: Vec<Node> = Vec::new();
    let mut by_state = std::collections::HashMap::new();
    loop {
        let mut changed = false;
        for transition in &mut transitions {
            if by_state.contains_key(&transition.target)
                || !transition
                    .children
                    .iter()
                    .all(|state| by_state.contains_key(state))
            {
                continue;
            }
            let children: Vec<usize> = transition
                .children
                .iter()
                .map(|state| by_state[state])
                .collect();
            let size = 1 + children
                .iter()
                .map(|index| arena[*index].size)
                .sum::<usize>();
            let index = arena.len();
            arena.push(Node {
                constructor: std::mem::take(&mut transition.constructor),
                payload: transition.payload.take(),
                children,
                size,
            });
            by_state.insert(transition.target, index);
            changed = true;
        }
        if !changed {
            break;
        }
    }
    let root = automaton
        .accepting
        .iter()
        .filter_map(|state| by_state.get(state).copied())
        .min_by_key(|index| arena[*index].size)?;
    if arena[root].children.is_empty() {
        let node = &mut arena[root];
        return Some(SymTerm {
            constructor: std::mem::take(&mut node.constructor),
            payload: node.payload.take(),
            children: Vec::new(),
        });
    }
    enum Task {
        Visit(usize),
        Build(usize),
    }
    let mut tasks = vec![Task::Visit(root)];
    let mut values = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            Task::Visit(index) => {
                tasks.push(Task::Build(index));
                for child in arena[index].children.iter().rev() {
                    tasks.push(Task::Visit(*child));
                }
            },
            Task::Build(index) => {
                let node = &arena[index];
                let start = values
                    .len()
                    .checked_sub(node.children.len())
                    .expect("tree witness lost child terms");
                let children = values.split_off(start);
                values.push(SymTerm {
                    constructor: node.constructor.clone(),
                    payload: node.payload.clone(),
                    children,
                });
            },
        }
    }
    values.pop()
}
