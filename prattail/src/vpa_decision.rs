//! Exact decision procedures for Boolean visibly pushdown automata.
//!
//! The algorithms in this module never enumerate concrete stacks. Emptiness
//! uses a least fixpoint of well-matched state summaries; determinization uses
//! the Alur–Madhusudan `(S, R)` construction, where `S` is a binary state
//! relation and `R` is the set of currently reachable source states.

use super::*;

const DET_STACK_PREFIX: &str = "\0prattail:vpa:det-stack:";
const DET_BOTTOM: &str = "\0prattail:vpa:det-bottom";

/// Structural errors rejected by exact VPA decision procedures.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum VpaValidationError {
    /// A symbol occurs in more than one alphabet partition.
    AlphabetOverlap { symbol: String },
    /// A state record's public ID does not equal its canonical vector index.
    NonCanonicalStateId { index: usize, id: usize },
    /// A public state reference lies outside `states`.
    UnknownState { role: &'static str, id: usize },
    /// A transition key uses a symbol from the wrong alphabet partition.
    WrongSymbolClass { expected: SymbolKind, symbol: String },
    /// A call transition attempts to push the reserved bottom marker.
    PushesBottom { symbol: String },
}

impl std::fmt::Display for VpaValidationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::AlphabetOverlap { symbol } => {
                write!(f, "symbol {symbol:?} occurs in multiple VPA alphabet partitions")
            },
            Self::NonCanonicalStateId { index, id } => {
                write!(f, "state at vector index {index} carries non-canonical public ID {id}")
            },
            Self::UnknownState { role, id } => {
                write!(f, "{role} references absent VPA state {id}")
            },
            Self::WrongSymbolClass { expected, symbol } => {
                write!(f, "transition symbol {symbol:?} is not declared as {expected:?}")
            },
            Self::PushesBottom { symbol } => {
                write!(f, "call transition on {symbol:?} pushes the reserved bottom marker")
            },
        }
    }
}

impl std::error::Error for VpaValidationError {}

fn check_state(n: usize, role: &'static str, id: usize) -> Result<(), VpaValidationError> {
    if id < n {
        Ok(())
    } else {
        Err(VpaValidationError::UnknownState { role, id })
    }
}

/// Validate the public representation before running an exact decision procedure.
pub(crate) fn validate<W: Semiring>(vpa: &WeightedVpa<W>) -> Result<(), VpaValidationError> {
    for symbol in &vpa.alphabet.call_symbols {
        if vpa.alphabet.return_symbols.contains(symbol)
            || vpa.alphabet.internal_symbols.contains(symbol)
        {
            return Err(VpaValidationError::AlphabetOverlap { symbol: symbol.clone() });
        }
    }
    for symbol in &vpa.alphabet.return_symbols {
        if vpa.alphabet.internal_symbols.contains(symbol) {
            return Err(VpaValidationError::AlphabetOverlap { symbol: symbol.clone() });
        }
    }

    let n = vpa.states.len();
    for (index, state) in vpa.states.iter().enumerate() {
        if state.id != index {
            return Err(VpaValidationError::NonCanonicalStateId { index, id: state.id });
        }
    }
    for &state in &vpa.initial_states {
        check_state(n, "initial state", state)?;
    }
    for &state in &vpa.accepting_states {
        check_state(n, "accepting state", state)?;
    }
    for &state in vpa.initial_weights.keys() {
        check_state(n, "initial weight", state)?;
    }
    for &state in vpa.accepting_weights.keys() {
        check_state(n, "accepting weight", state)?;
    }

    for ((source, symbol), targets) in &vpa.internal_transitions {
        check_state(n, "internal transition source", *source)?;
        if !vpa.alphabet.internal_symbols.contains(symbol) {
            return Err(VpaValidationError::WrongSymbolClass {
                expected: SymbolKind::Internal,
                symbol: symbol.clone(),
            });
        }
        for &(target, _) in targets {
            check_state(n, "internal transition target", target)?;
        }
    }
    for ((source, symbol), targets) in &vpa.call_transitions {
        check_state(n, "call transition source", *source)?;
        if !vpa.alphabet.call_symbols.contains(symbol) {
            return Err(VpaValidationError::WrongSymbolClass {
                expected: SymbolKind::Call,
                symbol: symbol.clone(),
            });
        }
        for &(target, ref pushed, ref weight) in targets {
            check_state(n, "call transition target", target)?;
            if !weight.is_zero() && pushed == &vpa.initial_stack_symbol {
                return Err(VpaValidationError::PushesBottom { symbol: symbol.clone() });
            }
        }
    }
    for ((source, symbol, _stack_top), targets) in &vpa.return_transitions {
        check_state(n, "return transition source", *source)?;
        if !vpa.alphabet.return_symbols.contains(symbol) {
            return Err(VpaValidationError::WrongSymbolClass {
                expected: SymbolKind::Return,
                symbol: symbol.clone(),
            });
        }
        for &(target, _) in targets {
            check_state(n, "return transition target", target)?;
        }
    }
    Ok(())
}

pub(super) fn active_initial<W: Semiring>(vpa: &WeightedVpa<W>, state: usize) -> bool {
    vpa.initial_states.contains(&state)
        && vpa
            .initial_weights
            .get(&state)
            .is_none_or(|weight| !weight.is_zero())
}

pub(super) fn active_accepting<W: Semiring>(vpa: &WeightedVpa<W>, state: usize) -> bool {
    vpa.accepting_states.contains(&state)
        && vpa
            .accepting_weights
            .get(&state)
            .is_none_or(|weight| !weight.is_zero())
}

fn add_summary(
    summary: &mut [Vec<bool>],
    successors: &mut [Vec<usize>],
    predecessors: &mut [Vec<usize>],
    queue: &mut VecDeque<(usize, usize)>,
    from: usize,
    to: usize,
) {
    if !summary[from][to] {
        summary[from][to] = true;
        successors[from].push(to);
        predecessors[to].push(from);
        queue.push_back((from, to));
    }
}

/// Exact emptiness by matched-summary saturation and finite reachability.
pub(crate) fn is_language_empty(vpa: &Vpa) -> Result<bool, VpaValidationError> {
    validate(vpa)?;
    let n = vpa.states.len();
    let mut summary = vec![vec![false; n]; n];
    let mut successors = vec![Vec::new(); n];
    let mut predecessors = vec![Vec::new(); n];
    let mut queue = VecDeque::new();

    for state in 0..n {
        add_summary(&mut summary, &mut successors, &mut predecessors, &mut queue, state, state);
    }
    for ((source, _symbol), targets) in &vpa.internal_transitions {
        for &(target, weight) in targets {
            if !weight.is_zero() {
                add_summary(
                    &mut summary,
                    &mut successors,
                    &mut predecessors,
                    &mut queue,
                    *source,
                    target,
                );
            }
        }
    }

    let mut calls_into: HashMap<(usize, String), Vec<usize>> = HashMap::new();
    for ((source, _symbol), targets) in &vpa.call_transitions {
        for &(target, ref gamma, weight) in targets {
            if !weight.is_zero() {
                calls_into
                    .entry((target, gamma.clone()))
                    .or_default()
                    .push(*source);
            }
        }
    }
    let mut returns_from: HashMap<(usize, String), Vec<usize>> = HashMap::new();
    for ((source, _symbol, gamma), targets) in &vpa.return_transitions {
        if gamma == &vpa.initial_stack_symbol {
            continue;
        }
        for &(target, weight) in targets {
            if !weight.is_zero() {
                returns_from
                    .entry((*source, gamma.clone()))
                    .or_default()
                    .push(target);
            }
        }
    }

    while let Some((from, to)) = queue.pop_front() {
        let left = predecessors[from].clone();
        let right = successors[to].clone();
        for predecessor in left {
            add_summary(
                &mut summary,
                &mut successors,
                &mut predecessors,
                &mut queue,
                predecessor,
                to,
            );
        }
        for successor in right {
            add_summary(
                &mut summary,
                &mut successors,
                &mut predecessors,
                &mut queue,
                from,
                successor,
            );
        }

        let matching_calls: Vec<_> = calls_into
            .iter()
            .filter(|((target, _), _)| *target == from)
            .map(|((_, gamma), sources)| (gamma.clone(), sources.clone()))
            .collect();
        for (gamma, call_sources) in matching_calls {
            if let Some(return_targets) = returns_from.get(&(to, gamma)) {
                let return_targets = return_targets.clone();
                for call_source in &call_sources {
                    for return_target in &return_targets {
                        add_summary(
                            &mut summary,
                            &mut successors,
                            &mut predecessors,
                            &mut queue,
                            *call_source,
                            *return_target,
                        );
                    }
                }
            }
        }
    }

    // At bottom: balanced summaries and returns that read Z0 without popping it.
    let mut ground = vec![false; n];
    let mut ground_queue = VecDeque::new();
    for (state, reachable) in ground.iter_mut().enumerate() {
        if active_initial(vpa, state) {
            *reachable = true;
            ground_queue.push_back(state);
        }
    }
    while let Some(state) = ground_queue.pop_front() {
        for &target in &successors[state] {
            if !ground[target] {
                ground[target] = true;
                ground_queue.push_back(target);
            }
        }
        for symbol in &vpa.alphabet.return_symbols {
            if let Some(targets) = vpa.return_transitions.get(&(
                state,
                symbol.clone(),
                vpa.initial_stack_symbol.clone(),
            )) {
                for &(target, weight) in targets {
                    if !weight.is_zero() && !ground[target] {
                        ground[target] = true;
                        ground_queue.push_back(target);
                    }
                }
            }
        }
    }

    // Above bottom: balanced summaries and calls whose frames remain unmatched.
    let mut reachable = ground;
    let mut reachable_queue: VecDeque<usize> = reachable
        .iter()
        .enumerate()
        .filter_map(|(state, present)| present.then_some(state))
        .collect();
    while let Some(state) = reachable_queue.pop_front() {
        for &target in &successors[state] {
            if !reachable[target] {
                reachable[target] = true;
                reachable_queue.push_back(target);
            }
        }
        for symbol in &vpa.alphabet.call_symbols {
            if let Some(targets) = vpa.call_transitions.get(&(state, symbol.clone())) {
                for &(target, _, weight) in targets {
                    if !weight.is_zero() && !reachable[target] {
                        reachable[target] = true;
                        reachable_queue.push_back(target);
                    }
                }
            }
        }
    }

    Ok(!(0..n).any(|state| reachable[state] && active_accepting(vpa, state)))
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct DetState {
    summary: Vec<bool>,
    reachable: Vec<bool>,
}

fn identity_relation(n: usize) -> Vec<bool> {
    let mut relation = vec![false; n * n];
    for state in 0..n {
        relation[state * n + state] = true;
    }
    relation
}

fn canonical_state(n: usize, summary: Vec<bool>, reachable: Vec<bool>) -> DetState {
    if reachable.iter().any(|present| *present) {
        DetState { summary, reachable }
    } else {
        DetState { summary: vec![false; n * n], reachable }
    }
}

fn intern_state<W: VpaDecisionSemiring>(
    source: &WeightedVpa<W>,
    state: DetState,
    ids: &mut HashMap<DetState, usize>,
    states: &mut Vec<DetState>,
    output: &mut WeightedVpa<W>,
) -> (usize, bool) {
    if let Some(&id) = ids.get(&state) {
        return (id, false);
    }
    let id = output.add_state(Some(format!("summary-{id}", id = states.len())));
    if state
        .reachable
        .iter()
        .enumerate()
        .any(|(q, present)| *present && active_accepting(source, q))
    {
        output.accepting_states.insert(id);
        output.accepting_weights.insert(id, W::one());
    }
    ids.insert(state.clone(), id);
    states.push(state);
    (id, true)
}

fn internal_successor<W: VpaDecisionSemiring>(
    vpa: &WeightedVpa<W>,
    state: &DetState,
    symbol: &str,
) -> DetState {
    let n = vpa.states.len();
    let mut summary = vec![false; n * n];
    let mut reachable = vec![false; n];
    for from in 0..n {
        for middle in 0..n {
            if !state.summary[from * n + middle] {
                continue;
            }
            if let Some(targets) = vpa.internal_transitions.get(&(middle, symbol.to_string())) {
                for &(target, weight) in targets {
                    if !weight.is_zero() {
                        summary[from * n + target] = true;
                    }
                }
            }
        }
    }
    for from in 0..n {
        if state.reachable[from] {
            if let Some(targets) = vpa.internal_transitions.get(&(from, symbol.to_string())) {
                for &(target, weight) in targets {
                    if !weight.is_zero() {
                        reachable[target] = true;
                    }
                }
            }
        }
    }
    canonical_state(n, summary, reachable)
}

fn bottom_return_successor<W: VpaDecisionSemiring>(
    vpa: &WeightedVpa<W>,
    state: &DetState,
    symbol: &str,
) -> DetState {
    let n = vpa.states.len();
    let mut summary = vec![false; n * n];
    let mut reachable = vec![false; n];
    for from in 0..n {
        for middle in 0..n {
            if !state.summary[from * n + middle] {
                continue;
            }
            if let Some(targets) = vpa.return_transitions.get(&(
                middle,
                symbol.to_string(),
                vpa.initial_stack_symbol.clone(),
            )) {
                for &(target, weight) in targets {
                    if !weight.is_zero() {
                        summary[from * n + target] = true;
                    }
                }
            }
        }
    }
    for from in 0..n {
        if state.reachable[from] {
            if let Some(targets) = vpa.return_transitions.get(&(
                from,
                symbol.to_string(),
                vpa.initial_stack_symbol.clone(),
            )) {
                for &(target, weight) in targets {
                    if !weight.is_zero() {
                        reachable[target] = true;
                    }
                }
            }
        }
    }
    canonical_state(n, summary, reachable)
}

fn call_successor<W: VpaDecisionSemiring>(
    vpa: &WeightedVpa<W>,
    state: &DetState,
    symbol: &str,
) -> DetState {
    let n = vpa.states.len();
    let mut reachable = vec![false; n];
    for from in 0..n {
        if state.reachable[from] {
            if let Some(targets) = vpa.call_transitions.get(&(from, symbol.to_string())) {
                for &(target, _, weight) in targets {
                    if !weight.is_zero() {
                        reachable[target] = true;
                    }
                }
            }
        }
    }
    canonical_state(n, identity_relation(n), reachable)
}

fn matched_return_successor<W: VpaDecisionSemiring>(
    vpa: &WeightedVpa<W>,
    caller: &DetState,
    current: &DetState,
    call_symbol: &str,
    return_symbol: &str,
) -> DetState {
    let n = vpa.states.len();
    let mut summary_edge = vec![false; n * n];
    for call_source in 0..n {
        let Some(call_targets) = vpa
            .call_transitions
            .get(&(call_source, call_symbol.to_string()))
        else {
            continue;
        };
        for &(call_target, ref gamma, call_weight) in call_targets {
            if call_weight.is_zero() {
                continue;
            }
            for return_source in 0..n {
                if !current.summary[call_target * n + return_source] {
                    continue;
                }
                if let Some(return_targets) = vpa.return_transitions.get(&(
                    return_source,
                    return_symbol.to_string(),
                    gamma.clone(),
                )) {
                    for &(return_target, return_weight) in return_targets {
                        if !return_weight.is_zero() {
                            summary_edge[call_source * n + return_target] = true;
                        }
                    }
                }
            }
        }
    }

    let mut summary = vec![false; n * n];
    let mut reachable = vec![false; n];
    for from in 0..n {
        for middle in 0..n {
            if !caller.summary[from * n + middle] {
                continue;
            }
            for target in 0..n {
                if summary_edge[middle * n + target] {
                    summary[from * n + target] = true;
                }
            }
        }
    }
    for middle in 0..n {
        if caller.reachable[middle] {
            for target in 0..n {
                if summary_edge[middle * n + target] {
                    reachable[target] = true;
                }
            }
        }
    }
    canonical_state(n, summary, reachable)
}

fn det_stack_symbol(caller_id: usize, call_symbol: &str) -> String {
    format!("{DET_STACK_PREFIX}{caller_id}:{}:{call_symbol}", call_symbol.len())
}

/// Standard summary-state determinization, total over the declared alphabet.
pub(crate) fn determinize<W: VpaDecisionSemiring>(
    vpa: &WeightedVpa<W>,
) -> Result<WeightedVpa<W>, VpaValidationError> {
    validate(vpa)?;
    let n = vpa.states.len();
    let mut output = WeightedVpa::new(vpa.alphabet.clone());
    output.initial_stack_symbol = DET_BOTTOM.to_string();

    let mut initial_reachable = vec![false; n];
    for (state, reachable) in initial_reachable.iter_mut().enumerate() {
        *reachable = active_initial(vpa, state);
    }
    let initial = canonical_state(n, identity_relation(n), initial_reachable);
    let mut ids = HashMap::new();
    let mut states = Vec::new();
    let (initial_id, _) = intern_state(vpa, initial, &mut ids, &mut states, &mut output);
    output.initial_states.insert(initial_id);
    output.initial_weights.insert(initial_id, W::one());

    let mut calls: Vec<_> = vpa.alphabet.call_symbols.iter().cloned().collect();
    let mut returns: Vec<_> = vpa.alphabet.return_symbols.iter().cloned().collect();
    let mut internals: Vec<_> = vpa.alphabet.internal_symbols.iter().cloned().collect();
    calls.sort();
    returns.sort();
    internals.sort();

    let mut basics_processed = 0usize;
    let mut matched_processed: HashSet<(usize, usize, String, String)> = HashSet::new();
    loop {
        while basics_processed < states.len() {
            let current_id = basics_processed;
            let current = states[current_id].clone();
            for symbol in &internals {
                let successor = internal_successor(vpa, &current, symbol);
                let (target, _) = intern_state(vpa, successor, &mut ids, &mut states, &mut output);
                output
                    .internal_transitions
                    .insert((current_id, symbol.clone()), vec![(target, W::one())]);
            }
            for symbol in &calls {
                let successor = call_successor(vpa, &current, symbol);
                let (target, _) = intern_state(vpa, successor, &mut ids, &mut states, &mut output);
                output.call_transitions.insert(
                    (current_id, symbol.clone()),
                    vec![(target, det_stack_symbol(current_id, symbol), W::one())],
                );
            }
            for symbol in &returns {
                let successor = bottom_return_successor(vpa, &current, symbol);
                let (target, _) = intern_state(vpa, successor, &mut ids, &mut states, &mut output);
                output.return_transitions.insert(
                    (current_id, symbol.clone(), output.initial_stack_symbol.clone()),
                    vec![(target, W::one())],
                );
            }
            basics_processed += 1;
        }

        let before = states.len();
        for current_id in 0..before {
            for caller_id in 0..before {
                for call_symbol in &calls {
                    for return_symbol in &returns {
                        if !matched_processed.insert((
                            current_id,
                            caller_id,
                            call_symbol.clone(),
                            return_symbol.clone(),
                        )) {
                            continue;
                        }
                        let successor = matched_return_successor(
                            vpa,
                            &states[caller_id],
                            &states[current_id],
                            call_symbol,
                            return_symbol,
                        );
                        let (target, _) =
                            intern_state(vpa, successor, &mut ids, &mut states, &mut output);
                        output.return_transitions.insert(
                            (
                                current_id,
                                return_symbol.clone(),
                                det_stack_symbol(caller_id, call_symbol),
                            ),
                            vec![(target, W::one())],
                        );
                    }
                }
            }
        }
        if states.len() == before {
            break;
        }
    }

    Ok(output)
}

/// Project the support language of a weighted VPA onto Boolean reachability.
pub(crate) fn boolean_support<W: Semiring>(vpa: &WeightedVpa<W>) -> Vpa {
    let mut support = Vpa::new(vpa.alphabet.clone());
    support.states = vpa.states.clone();
    support.initial_stack_symbol = vpa.initial_stack_symbol.clone();
    support.initial_states = vpa
        .initial_states
        .iter()
        .copied()
        .filter(|state| active_initial(vpa, *state))
        .collect();
    support.accepting_states = vpa
        .accepting_states
        .iter()
        .copied()
        .filter(|state| active_accepting(vpa, *state))
        .collect();
    for &state in &support.initial_states {
        support.initial_weights.insert(state, BooleanWeight::one());
    }
    for &state in &support.accepting_states {
        support
            .accepting_weights
            .insert(state, BooleanWeight::one());
    }
    for (key, targets) in &vpa.internal_transitions {
        let projected: Vec<_> = targets
            .iter()
            .filter(|(_, weight)| !weight.is_zero())
            .map(|(target, _)| (*target, BooleanWeight::one()))
            .collect();
        if !projected.is_empty() {
            support.internal_transitions.insert(key.clone(), projected);
        }
    }
    for (key, targets) in &vpa.call_transitions {
        let projected: Vec<_> = targets
            .iter()
            .filter(|(_, _, weight)| !weight.is_zero())
            .map(|(target, gamma, _)| (*target, gamma.clone(), BooleanWeight::one()))
            .collect();
        if !projected.is_empty() {
            support.call_transitions.insert(key.clone(), projected);
        }
    }
    for (key, targets) in &vpa.return_transitions {
        let projected: Vec<_> = targets
            .iter()
            .filter(|(_, weight)| !weight.is_zero())
            .map(|(target, _)| (*target, BooleanWeight::one()))
            .collect();
        if !projected.is_empty() {
            support.return_transitions.insert(key.clone(), projected);
        }
    }
    support
}
