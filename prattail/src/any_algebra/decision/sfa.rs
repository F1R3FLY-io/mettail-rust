use std::collections::{BTreeSet, HashMap, HashSet, VecDeque};

use crate::regex_sfa::{EpsNfa, RegexNode, RegexPred};
use crate::symbolic::BooleanAlgebra;

use super::super::{AnyAlgebra, AnyDomain, AnyPred};
use super::solver::DecisionOracle;

struct Edge {
    from: usize,
    to: usize,
    guard: AnyPred,
}

pub(super) struct DecisionSfa {
    accepting: Vec<bool>,
    transitions: Vec<Edge>,
    initials: HashSet<usize>,
}

impl DecisionSfa {
    fn new() -> Self {
        Self {
            accepting: Vec::new(),
            transitions: Vec::new(),
            initials: HashSet::new(),
        }
    }

    fn add_state(&mut self, accepting: bool) -> usize {
        let state = self.accepting.len();
        self.accepting.push(accepting);
        state
    }

    fn set_initial(&mut self, state: usize) {
        self.initials.insert(state);
    }

    fn add_transition(&mut self, from: usize, to: usize, guard: AnyPred) {
        self.transitions.push(Edge { from, to, guard });
    }

    fn accepting_states(&self) -> impl Iterator<Item = usize> + '_ {
        self.accepting
            .iter()
            .enumerate()
            .filter_map(|(state, accepting)| accepting.then_some(state))
    }
}

fn from_eps(nfa: EpsNfa<AnyPred>) -> DecisionSfa {
    let closures = nfa.epsilon_closures();
    let (states, _, transitions, initials, accepts) = nfa.into_parts();
    let mut accepting = vec![false; states];
    for state in &accepts {
        accepting[*state] = true;
    }
    let mut result = DecisionSfa::new();
    for closure in &closures {
        result.add_state(closure.iter().any(|state| accepting[*state]));
    }
    for initial in initials {
        result.set_initial(initial);
    }
    for (from, guard, target) in transitions {
        let mut guard = Some(guard);
        let mut sources = closures
            .iter()
            .enumerate()
            .filter_map(|(source, closure)| closure.contains(&from).then_some(source))
            .peekable();
        while let Some(source) = sources.next() {
            let edge_guard = if sources.peek().is_some() {
                guard
                    .as_ref()
                    .expect("epsilon expansion lost its edge guard")
                    .clone()
            } else {
                guard.take().expect("epsilon expansion lost its edge guard")
            };
            result.add_transition(source, target, edge_guard);
        }
    }
    result
}

fn into_eps(automaton: DecisionSfa) -> EpsNfa<AnyPred> {
    let accepts = automaton.accepting_states().collect();
    EpsNfa::from_parts(
        automaton.accepting.len().max(1),
        Vec::new(),
        automaton
            .transitions
            .into_iter()
            .map(|edge| (edge.from, edge.guard, edge.to))
            .collect(),
        automaton.initials.into_iter().collect(),
        accepts,
    )
}

pub(super) async fn compile<'a>(
    oracle: &DecisionOracle<'a>,
    algebra: &'a AnyAlgebra,
    predicate: RegexPred<AnyPred>,
) -> DecisionSfa {
    enum Task {
        Visit(RegexPred<AnyPred>),
        Concat,
        Alt,
        Star,
        Inter,
        Compl,
    }

    let mut tasks = vec![Task::Visit(predicate)];
    let mut values = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            Task::Visit(predicate) => match predicate.into_node() {
                RegexNode::Empty => values.push(EpsNfa::empty()),
                RegexNode::Epsilon => values.push(EpsNfa::epsilon()),
                RegexNode::Elem(class) => values.push(EpsNfa::elem(class)),
                RegexNode::Length(lower, upper) => {
                    let sigma = || EpsNfa::elem(algebra.true_pred());
                    let mut nfa = EpsNfa::epsilon();
                    for _ in 0..lower {
                        nfa = EpsNfa::concat(nfa, sigma());
                    }
                    match upper {
                        None => nfa = EpsNfa::concat(nfa, EpsNfa::star(sigma())),
                        Some(upper) => {
                            for _ in 0..upper.saturating_sub(lower) {
                                nfa = EpsNfa::concat(nfa, EpsNfa::alt(EpsNfa::epsilon(), sigma()));
                            }
                        },
                    }
                    values.push(nfa);
                },
                RegexNode::Concat(left, right) => {
                    tasks.push(Task::Concat);
                    tasks.push(Task::Visit(*right));
                    tasks.push(Task::Visit(*left));
                },
                RegexNode::Alt(left, right) => {
                    tasks.push(Task::Alt);
                    tasks.push(Task::Visit(*right));
                    tasks.push(Task::Visit(*left));
                },
                RegexNode::Star(body) => {
                    tasks.push(Task::Star);
                    tasks.push(Task::Visit(*body));
                },
                RegexNode::Inter(left, right) => {
                    tasks.push(Task::Inter);
                    tasks.push(Task::Visit(*right));
                    tasks.push(Task::Visit(*left));
                },
                RegexNode::Compl(body) => {
                    tasks.push(Task::Compl);
                    tasks.push(Task::Visit(*body));
                },
            },
            Task::Concat => {
                let right = values.pop().expect("regex decision lost right concatenand");
                let left = values.pop().expect("regex decision lost left concatenand");
                values.push(EpsNfa::concat(left, right));
            },
            Task::Alt => {
                let right = values.pop().expect("regex decision lost right alternative");
                let left = values.pop().expect("regex decision lost left alternative");
                values.push(EpsNfa::alt(left, right));
            },
            Task::Star => {
                let body = values.pop().expect("regex decision lost star body");
                values.push(EpsNfa::star(body));
            },
            Task::Inter => {
                let right = from_eps(
                    values
                        .pop()
                        .expect("regex decision lost right intersection"),
                );
                let left = from_eps(values.pop().expect("regex decision lost left intersection"));
                values.push(into_eps(intersect(oracle, algebra, &left, &right).await));
            },
            Task::Compl => {
                let body = from_eps(values.pop().expect("regex decision lost complement body"));
                values.push(into_eps(complement(oracle, algebra, &body).await));
            },
        }
    }
    from_eps(values.pop().expect("regex decision produced no automaton"))
}

async fn intersect<'a>(
    oracle: &DecisionOracle<'a>,
    algebra: &'a AnyAlgebra,
    left: &DecisionSfa,
    right: &DecisionSfa,
) -> DecisionSfa {
    let mut result = DecisionSfa::new();
    let mut states = HashMap::new();
    for left_state in 0..left.accepting.len() {
        for right_state in 0..right.accepting.len() {
            let state =
                result.add_state(left.accepting[left_state] && right.accepting[right_state]);
            states.insert((left_state, right_state), state);
        }
    }
    for &left_initial in &left.initials {
        for &right_initial in &right.initials {
            result.set_initial(states[&(left_initial, right_initial)]);
        }
    }
    for left_edge in &left.transitions {
        for right_edge in &right.transitions {
            let guard = algebra.and(&left_edge.guard, &right_edge.guard);
            if oracle.sat(algebra, guard.clone()).await {
                result.add_transition(
                    states[&(left_edge.from, right_edge.from)],
                    states[&(left_edge.to, right_edge.to)],
                    guard,
                );
            }
        }
    }
    result
}

fn unique_guards(guards: &[AnyPred]) -> Vec<AnyPred> {
    let mut unique = Vec::new();
    for guard in guards {
        if !unique.iter().any(|candidate| candidate == guard) {
            unique.push(guard.clone());
        }
    }
    unique
}

async fn determinize<'a>(
    oracle: &DecisionOracle<'a>,
    algebra: &'a AnyAlgebra,
    automaton: &DecisionSfa,
) -> DecisionSfa {
    let mut result = DecisionSfa::new();
    let initial: BTreeSet<usize> = automaton.initials.iter().copied().collect();
    if initial.is_empty() {
        let state = result.add_state(false);
        result.set_initial(state);
        return result;
    }
    let mut state_map = HashMap::new();
    let mut worklist = VecDeque::new();
    let accepting = initial.iter().any(|state| automaton.accepting[*state]);
    let state = result.add_state(accepting);
    result.set_initial(state);
    state_map.insert(initial.clone(), state);
    worklist.push_back(initial);

    let mut outgoing = vec![Vec::new(); automaton.accepting.len()];
    for edge in &automaton.transitions {
        outgoing[edge.from].push((&edge.guard, edge.to));
    }
    while let Some(current) = worklist.pop_front() {
        let guards: Vec<AnyPred> = current
            .iter()
            .flat_map(|state| outgoing[*state].iter().map(|(guard, _)| (*guard).clone()))
            .collect();
        if guards.is_empty() {
            continue;
        }
        let unique = unique_guards(&guards);
        let regions = super::solver::minterms(oracle, algebra, &unique).await;
        for region in regions {
            let mut successor = BTreeSet::new();
            for state in &current {
                for (guard, target) in &outgoing[*state] {
                    let guard_index = unique
                        .iter()
                        .position(|candidate| candidate == *guard)
                        .expect("SFA minterm lost a source guard");
                    if region.positive[guard_index] {
                        successor.insert(*target);
                    }
                }
            }
            if successor.is_empty() {
                continue;
            }
            let successor_id = if let Some(existing) = state_map.get(&successor) {
                *existing
            } else {
                let accepting = successor.iter().any(|state| automaton.accepting[*state]);
                let state = result.add_state(accepting);
                state_map.insert(successor.clone(), state);
                worklist.push_back(successor.clone());
                state
            };
            result.add_transition(state_map[&current], successor_id, region.predicate);
        }
    }
    result
}

async fn complement<'a>(
    oracle: &DecisionOracle<'a>,
    algebra: &'a AnyAlgebra,
    automaton: &DecisionSfa,
) -> DecisionSfa {
    let deterministic = determinize(oracle, algebra, automaton).await;
    let mut result = DecisionSfa::new();
    for accepting in &deterministic.accepting {
        result.add_state(!accepting);
    }
    result.initials = deterministic.initials.clone();
    let mut covered: Vec<AnyPred> = (0..deterministic.accepting.len())
        .map(|_| algebra.false_pred())
        .collect();
    for edge in deterministic.transitions {
        covered[edge.from] = algebra.or(&covered[edge.from], &edge.guard);
        result.add_transition(edge.from, edge.to, edge.guard);
    }
    let sink = result.add_state(true);
    for (state, covered) in covered.into_iter().enumerate() {
        let uncovered = algebra.not(&covered);
        if oracle.sat(algebra, uncovered.clone()).await {
            result.add_transition(state, sink, uncovered);
        }
    }
    result.add_transition(sink, sink, algebra.true_pred());
    result
}

pub(super) async fn is_empty<'a>(
    oracle: &DecisionOracle<'a>,
    algebra: &'a AnyAlgebra,
    automaton: DecisionSfa,
) -> bool {
    if automaton.initials.is_empty() || !automaton.accepting.iter().any(|accepting| *accepting) {
        return true;
    }
    let mut outgoing = vec![Vec::new(); automaton.accepting.len()];
    for edge in automaton.transitions {
        outgoing[edge.from].push((edge.to, edge.guard));
    }
    let mut visited = vec![false; automaton.accepting.len()];
    let mut queue = VecDeque::new();
    for state in automaton.initials {
        visited[state] = true;
        queue.push_back(state);
    }
    while let Some(state) = queue.pop_front() {
        if automaton.accepting[state] {
            return false;
        }
        for (target, guard) in std::mem::take(&mut outgoing[state]) {
            if !visited[target] && oracle.sat(algebra, guard).await {
                visited[target] = true;
                queue.push_back(target);
            }
        }
    }
    true
}

pub(super) async fn shortest_accepted<'a>(
    oracle: &DecisionOracle<'a>,
    algebra: &'a AnyAlgebra,
    automaton: DecisionSfa,
) -> Option<Vec<AnyDomain>> {
    if automaton.initials.is_empty() || !automaton.accepting.iter().any(|accepting| *accepting) {
        return None;
    }
    if automaton
        .initials
        .iter()
        .any(|state| automaton.accepting[*state])
    {
        return Some(Vec::new());
    }
    let mut outgoing = vec![Vec::new(); automaton.accepting.len()];
    for edge in automaton.transitions {
        outgoing[edge.from].push((edge.to, edge.guard));
    }
    let mut visited = vec![false; automaton.accepting.len()];
    let mut predecessor: Vec<Option<(usize, AnyDomain)>> =
        (0..automaton.accepting.len()).map(|_| None).collect();
    let mut queue = VecDeque::new();
    for state in automaton.initials {
        visited[state] = true;
        queue.push_back(state);
    }
    while let Some(state) = queue.pop_front() {
        for (target, guard) in std::mem::take(&mut outgoing[state]) {
            if visited[target] {
                continue;
            }
            let Some(element) = oracle.witness(algebra, guard).await else {
                continue;
            };
            visited[target] = true;
            predecessor[target] = Some((state, element));
            if automaton.accepting[target] {
                let mut word = Vec::new();
                let mut current = target;
                while let Some((previous, element)) = predecessor[current].take() {
                    word.push(element);
                    current = previous;
                }
                word.reverse();
                return Some(word);
            }
            queue.push_back(target);
        }
    }
    None
}
