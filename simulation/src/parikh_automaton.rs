//! Parikh automaton: NFA with Parikh-weight transitions and semilinear set projection.
//!
//! A Parikh automaton extends a finite automaton with a D-dimensional counter
//! vector ([`ParikhWeight<D>`](crate::semiring::ParikhWeight)) attached to each
//! transition. The automaton accepts a word if there exists an accepting run
//! whose cumulative Parikh vector satisfies a semilinear constraint.
//!
//! ## Theoretical Foundations
//!
//! - **Parikh (1966)** — "On context-free languages." Proves that the Parikh
//!   image of every context-free language is semilinear (effectively regular
//!   when projected to counter vectors).
//! - **Klaedtke & Rueß (2003)** — "Monadic second-order logics with Parikh
//!   automata." Formalizes Parikh automata as NFA with output in commutative
//!   monoids, connecting to logical definability.
//! - **Cadilhac, Finkel & McKenzie (2012)** — "Affine Parikh automata."
//!   Extends Parikh automata with affine transformations, characterizing
//!   blind counter languages.
//!
//! ## Architecture
//!
//! ```text
//! ParikhAutomaton<D>
//!   ├── states: Vec<ParikhState>
//!   ├── transitions: Vec<ParikhTransition<D>>
//!   ├── initial_state: StateId
//!   └── accepting_states: HashSet<StateId>
//!
//! Operations:
//!   ├── run(input) → Option<ParikhWeight<D>>   (NFA simulation, returns cumulative weight)
//!   ├── all_runs(input) → Vec<ParikhWeight<D>> (all accepting runs)
//!   ├── project_semilinear() → SemilinearSet<D> (Parikh image as semilinear set)
//!   └── intersect(other) → ParikhAutomaton<D>   (product construction)
//! ```
//!
//! ## Applications
//!
//! - **Resource analysis**: count channel sends/receives per dimension
//! - **Boundedness checking**: detect unbounded counter growth
//! - **Equivalence testing**: compare Parikh images of two automata

use std::collections::{HashMap, HashSet, VecDeque};
use std::fmt;

use crate::semiring::ParikhWeight;

/// State identifier in a Parikh automaton.
pub type StateId = usize;

/// A state in the Parikh automaton.
#[derive(Debug, Clone)]
pub struct ParikhState {
    /// Unique state identifier.
    pub id: StateId,
    /// Human-readable name.
    pub name: String,
}

impl ParikhState {
    /// Create a new Parikh automaton state.
    pub fn new(id: StateId, name: impl Into<String>) -> Self {
        ParikhState { id, name: name.into() }
    }
}

impl fmt::Display for ParikhState {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "q{}({})", self.id, self.name)
    }
}

/// A transition in the Parikh automaton.
///
/// Each transition carries an optional input symbol (epsilon transitions have
/// `symbol = None`) and a Parikh weight that is accumulated along accepting runs.
#[derive(Debug, Clone)]
pub struct ParikhTransition<const D: usize> {
    /// Source state.
    pub from: StateId,
    /// Destination state.
    pub to: StateId,
    /// Input symbol consumed by this transition. `None` for epsilon transitions.
    pub symbol: Option<u8>,
    /// Parikh weight accumulated when this transition fires.
    pub weight: ParikhWeight<D>,
}

impl<const D: usize> ParikhTransition<D> {
    /// Create a new transition with the given symbol and weight.
    pub fn new(from: StateId, to: StateId, symbol: Option<u8>, weight: ParikhWeight<D>) -> Self {
        ParikhTransition { from, to, symbol, weight }
    }

    /// Create an epsilon transition with the given weight.
    pub fn epsilon(from: StateId, to: StateId, weight: ParikhWeight<D>) -> Self {
        ParikhTransition { from, to, symbol: None, weight }
    }

    /// Create a labeled transition with a zero weight.
    pub fn labeled(from: StateId, to: StateId, symbol: u8) -> Self {
        ParikhTransition {
            from,
            to,
            symbol: Some(symbol),
            weight: ParikhWeight::new([0u64; D]),
        }
    }
}

impl<const D: usize> fmt::Display for ParikhTransition<D> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.symbol {
            Some(s) => write!(f, "q{} --{}/{}-> q{}", self.from, s as char, self.weight, self.to),
            None => write!(f, "q{} --eps/{}-> q{}", self.from, self.weight, self.to),
        }
    }
}

/// A Parikh automaton: NFA with D-dimensional counter transitions.
///
/// The automaton operates over byte-valued input symbols. Transitions may be
/// labeled (consuming a byte) or epsilon (consuming no input). Each transition
/// carries a [`ParikhWeight<D>`] that accumulates along runs via component-wise
/// addition (the `times` operation of the Parikh semiring).
#[derive(Debug, Clone)]
pub struct ParikhAutomaton<const D: usize> {
    /// All states.
    pub states: Vec<ParikhState>,
    /// All transitions, indexed by source state for efficient lookup.
    transitions_by_source: HashMap<StateId, Vec<ParikhTransition<D>>>,
    /// Initial state.
    pub initial_state: StateId,
    /// Set of accepting (final) states.
    pub accepting_states: HashSet<StateId>,
}

impl<const D: usize> ParikhAutomaton<D> {
    /// Create a new Parikh automaton with a single initial state.
    pub fn new(initial_name: impl Into<String>) -> Self {
        let initial = ParikhState::new(0, initial_name);
        ParikhAutomaton {
            states: vec![initial],
            transitions_by_source: HashMap::new(),
            initial_state: 0,
            accepting_states: HashSet::new(),
        }
    }

    /// Add a state and return its ID.
    pub fn add_state(&mut self, name: impl Into<String>) -> StateId {
        let id = self.states.len();
        self.states.push(ParikhState::new(id, name));
        id
    }

    /// Mark a state as accepting.
    pub fn set_accepting(&mut self, state: StateId) {
        assert!(state < self.states.len(), "State {} does not exist", state);
        self.accepting_states.insert(state);
    }

    /// Add a transition.
    pub fn add_transition(&mut self, transition: ParikhTransition<D>) {
        assert!(
            transition.from < self.states.len(),
            "Source state {} does not exist",
            transition.from
        );
        assert!(
            transition.to < self.states.len(),
            "Destination state {} does not exist",
            transition.to
        );
        self.transitions_by_source
            .entry(transition.from)
            .or_insert_with(Vec::new)
            .push(transition);
    }

    /// Get all transitions from a given state.
    pub fn transitions_from(&self, state: StateId) -> &[ParikhTransition<D>] {
        self.transitions_by_source
            .get(&state)
            .map(|v| v.as_slice())
            .unwrap_or(&[])
    }

    /// Number of states.
    pub fn num_states(&self) -> usize {
        self.states.len()
    }

    /// Number of transitions.
    pub fn num_transitions(&self) -> usize {
        self.transitions_by_source.values().map(|v| v.len()).sum()
    }

    /// Compute the epsilon closure of a set of (state, weight) pairs.
    ///
    /// Returns all states reachable via epsilon transitions, with accumulated
    /// weights. Uses BFS to avoid stack overflow on long epsilon chains.
    fn epsilon_closure(
        &self,
        start: &[(StateId, ParikhWeight<D>)],
    ) -> Vec<(StateId, ParikhWeight<D>)> {
        use mettail_prattail::automata::semiring::Semiring;

        let mut result: HashMap<StateId, ParikhWeight<D>> = HashMap::new();
        let mut queue: VecDeque<(StateId, ParikhWeight<D>)> =
            VecDeque::with_capacity(start.len() * 2);

        for &(s, ref w) in start {
            result
                .entry(s)
                .and_modify(|existing| *existing = existing.plus(w))
                .or_insert_with(|| w.clone());
            queue.push_back((s, w.clone()));
        }

        while let Some((state, weight)) = queue.pop_front() {
            for t in self.transitions_from(state) {
                if t.symbol.is_none() {
                    let new_weight = weight.times(&t.weight);
                    let entry = result.entry(t.to);
                    let should_enqueue = match entry {
                        std::collections::hash_map::Entry::Occupied(ref e) => {
                            // Only enqueue if we found a new Parikh vector
                            // (for the max-based plus, check if any component increased)
                            let combined = e.get().plus(&new_weight);
                            combined != *e.get()
                        },
                        std::collections::hash_map::Entry::Vacant(_) => true,
                    };
                    if should_enqueue {
                        entry
                            .and_modify(|existing| *existing = existing.plus(&new_weight))
                            .or_insert_with(|| new_weight.clone());
                        queue.push_back((t.to, new_weight));
                    }
                }
            }
        }

        result.into_iter().collect()
    }

    /// Simulate the automaton on an input byte sequence.
    ///
    /// Returns all Parikh weights from accepting runs. If the automaton is
    /// deterministic (or nearly so), this typically returns 0 or 1 results.
    /// For non-deterministic automata, multiple accepting runs may yield
    /// different Parikh vectors.
    ///
    /// Uses BFS over (state, accumulated_weight) configurations to avoid
    /// stack overflow. The work queue is bounded by `max_configs` to prevent
    /// exponential blowup on highly ambiguous automata.
    pub fn all_runs(&self, input: &[u8], max_configs: usize) -> Vec<ParikhWeight<D>> {
        use mettail_prattail::automata::semiring::Semiring;

        let initial_weight = ParikhWeight::one();
        let mut configs = self.epsilon_closure(&[(self.initial_state, initial_weight)]);

        for &byte in input {
            let mut next_configs: Vec<(StateId, ParikhWeight<D>)> = Vec::new();

            for (state, ref weight) in &configs {
                for t in self.transitions_from(*state) {
                    if t.symbol == Some(byte) {
                        let new_weight = weight.times(&t.weight);
                        next_configs.push((t.to, new_weight));
                    }
                }
            }

            configs = self.epsilon_closure(&next_configs);

            // Bound the number of configurations to prevent blowup
            if configs.len() > max_configs {
                configs.truncate(max_configs);
            }
        }

        configs
            .into_iter()
            .filter(|(s, _)| self.accepting_states.contains(s))
            .map(|(_, w)| w)
            .collect()
    }

    /// Simulate the automaton and return the first accepting run's weight.
    ///
    /// Convenience wrapper around [`all_runs`](Self::all_runs) that returns
    /// the first result (if any), using a default config bound of 10000.
    pub fn run(&self, input: &[u8]) -> Option<ParikhWeight<D>> {
        let runs = self.all_runs(input, 10000);
        runs.into_iter().next()
    }

    /// Product construction: intersect two Parikh automata.
    ///
    /// The product automaton accepts a word iff both automata accept it.
    /// The Parikh weight of a transition in the product is the component-wise
    /// sum (times) of the two original weights.
    ///
    /// States in the product are pairs `(s1, s2)`.
    pub fn intersect(&self, other: &ParikhAutomaton<D>) -> ParikhAutomaton<D> {
        use mettail_prattail::automata::semiring::Semiring;

        let n1 = self.num_states();
        let n2 = other.num_states();

        // Map (s1, s2) → product_state_id
        let pair_to_id = |s1: StateId, s2: StateId| -> StateId { s1 * n2 + s2 };

        // Create all product states
        let mut product = ParikhAutomaton {
            states: Vec::with_capacity(n1 * n2),
            transitions_by_source: HashMap::new(),
            initial_state: pair_to_id(self.initial_state, other.initial_state),
            accepting_states: HashSet::new(),
        };

        for s1 in &self.states {
            for s2 in &other.states {
                let id = pair_to_id(s1.id, s2.id);
                product
                    .states
                    .push(ParikhState::new(id, format!("({},{})", s1.name, s2.name)));

                if self.accepting_states.contains(&s1.id) && other.accepting_states.contains(&s2.id)
                {
                    product.accepting_states.insert(id);
                }
            }
        }

        // Build product transitions
        // For labeled transitions: both automata must take the same symbol
        for s1 in 0..n1 {
            for t1 in self.transitions_from(s1) {
                if let Some(sym) = t1.symbol {
                    for s2 in 0..n2 {
                        for t2 in other.transitions_from(s2) {
                            if t2.symbol == Some(sym) {
                                let from = pair_to_id(s1, s2);
                                let to = pair_to_id(t1.to, t2.to);
                                let weight = t1.weight.times(&t2.weight);
                                product.add_transition(ParikhTransition::new(
                                    from,
                                    to,
                                    Some(sym),
                                    weight,
                                ));
                            }
                        }
                    }
                }
            }
        }

        // For epsilon transitions: one automaton takes epsilon, the other stays
        for s1 in 0..n1 {
            for t1 in self.transitions_from(s1) {
                if t1.symbol.is_none() {
                    for s2 in 0..n2 {
                        let from = pair_to_id(s1, s2);
                        let to = pair_to_id(t1.to, s2);
                        product.add_transition(ParikhTransition::epsilon(
                            from,
                            to,
                            t1.weight.clone(),
                        ));
                    }
                }
            }
        }
        for s2 in 0..n2 {
            for t2 in other.transitions_from(s2) {
                if t2.symbol.is_none() {
                    for s1 in 0..n1 {
                        let from = pair_to_id(s1, s2);
                        let to = pair_to_id(s1, t2.to);
                        product.add_transition(ParikhTransition::epsilon(
                            from,
                            to,
                            t2.weight.clone(),
                        ));
                    }
                }
            }
        }

        product
    }

    /// Enumerate all reachable Parikh vectors from accepting runs over all
    /// input words up to a given length.
    ///
    /// This is a brute-force approach suitable for small automata and short
    /// inputs. For larger automata, use symbolic methods or the semilinear
    /// set projection.
    ///
    /// Returns a set of Parikh vectors, one per distinct accepting run.
    pub fn reachable_parikh_vectors(
        &self,
        max_input_len: usize,
        alphabet: &[u8],
    ) -> HashSet<ParikhWeight<D>> {
        let mut result = HashSet::new();

        // BFS over all input words up to max_input_len
        let mut queue: VecDeque<Vec<u8>> = VecDeque::new();
        queue.push_back(Vec::new());

        while let Some(word) = queue.pop_front() {
            // Check runs for this word
            for w in self.all_runs(&word, 1000) {
                result.insert(w);
            }

            // Extend word if under length limit
            if word.len() < max_input_len {
                for &sym in alphabet {
                    let mut extended = word.clone();
                    extended.push(sym);
                    queue.push_back(extended);
                }
            }
        }

        result
    }
}

impl<const D: usize> fmt::Display for ParikhAutomaton<D> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "ParikhAutomaton<{}>:", D)?;
        writeln!(f, "  States: {}", self.states.len())?;
        writeln!(f, "  Transitions: {}", self.num_transitions())?;
        writeln!(f, "  Initial: q{}", self.initial_state)?;
        write!(f, "  Accepting: {{")?;
        for (i, s) in self.accepting_states.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "q{}", s)?;
        }
        writeln!(f, "}}")
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Semilinear sets
// ══════════════════════════════════════════════════════════════════════════════

/// A linear set: `{ base + k₁·p₁ + k₂·p₂ + ... | kᵢ ∈ ℕ }`.
///
/// Represents all vectors obtainable from a base vector by adding non-negative
/// integer multiples of the period vectors.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LinearSet<const D: usize> {
    /// The base (offset) vector.
    pub base: ParikhWeight<D>,
    /// Period vectors. The linear set is `base + span(periods)` over ℕ.
    pub periods: Vec<ParikhWeight<D>>,
}

impl<const D: usize> LinearSet<D> {
    /// Create a linear set with the given base and periods.
    pub fn new(base: ParikhWeight<D>, periods: Vec<ParikhWeight<D>>) -> Self {
        LinearSet { base, periods }
    }

    /// Create a singleton linear set (just the base vector, no periods).
    pub fn singleton(base: ParikhWeight<D>) -> Self {
        LinearSet { base, periods: Vec::new() }
    }

    /// Check whether a given vector is contained in this linear set.
    ///
    /// For zero periods, checks exact equality with the base.
    /// For one period, checks if `(target - base)` is a non-negative multiple.
    /// For multiple periods, uses a bounded search (heuristic for general case).
    pub fn contains(&self, target: &ParikhWeight<D>) -> bool {
        // Check if target >= base (component-wise)
        if !self.base.leq(target) {
            return false;
        }

        if self.periods.is_empty() {
            return *target == self.base;
        }

        // Compute diff = target - base
        let mut diff = [0u64; D];
        for i in 0..D {
            diff[i] = target.counters[i] - self.base.counters[i];
        }

        if self.periods.len() == 1 {
            // Single period: check if diff is a non-negative multiple
            let period = &self.periods[0];
            let mut ratio: Option<u64> = None;
            for i in 0..D {
                if period.counters[i] == 0 {
                    if diff[i] != 0 {
                        return false;
                    }
                } else {
                    let r = diff[i] / period.counters[i];
                    if diff[i] % period.counters[i] != 0 {
                        return false;
                    }
                    match ratio {
                        None => ratio = Some(r),
                        Some(prev) => {
                            if prev != r {
                                return false;
                            }
                        },
                    }
                }
            }
            return true;
        }

        // Multiple periods: bounded search via iterative deepening.
        // This is a heuristic that works for small period vectors.
        // For full generality, an integer linear programming solver would be needed.
        let max_coeff: u64 = diff.iter().copied().max().unwrap_or(0).min(100);
        self.contains_bounded_search(&diff, &self.periods, max_coeff)
    }

    /// Bounded coefficient search for containment with multiple periods.
    ///
    /// Uses iterative work-stack (trampoline) to enumerate coefficient
    /// combinations up to `max_coeff` per period.
    fn contains_bounded_search(
        &self,
        diff: &[u64; D],
        periods: &[ParikhWeight<D>],
        max_coeff: u64,
    ) -> bool {
        if periods.is_empty() {
            return diff.iter().all(|&d| d == 0);
        }

        // Work stack: (period_index, remaining_diff)
        struct Frame<const D: usize> {
            period_idx: usize,
            remaining: [u64; D],
        }

        let mut stack: Vec<Frame<D>> = Vec::with_capacity(64);
        stack.push(Frame { period_idx: 0, remaining: *diff });

        while let Some(frame) = stack.pop() {
            if frame.period_idx >= periods.len() {
                // All periods assigned: check if remaining is zero
                if frame.remaining.iter().all(|&r| r == 0) {
                    return true;
                }
                continue;
            }

            let period = &periods[frame.period_idx];

            // Compute maximum coefficient for this period
            let mut local_max = max_coeff;
            for i in 0..D {
                if period.counters[i] > 0 {
                    local_max = local_max.min(frame.remaining[i] / period.counters[i]);
                }
            }

            // Try coefficients from 0 to local_max
            for k in 0..=local_max {
                let mut new_remaining = frame.remaining;
                let mut valid = true;
                for i in 0..D {
                    let subtracted = k * period.counters[i];
                    if subtracted > new_remaining[i] {
                        valid = false;
                        break;
                    }
                    new_remaining[i] -= subtracted;
                }
                if valid {
                    stack.push(Frame {
                        period_idx: frame.period_idx + 1,
                        remaining: new_remaining,
                    });
                }
            }
        }

        false
    }
}

impl<const D: usize> fmt::Display for LinearSet<D> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{{ {} ", self.base)?;
        for (i, p) in self.periods.iter().enumerate() {
            if i == 0 {
                write!(f, "+ k{} * {} ", i, p)?;
            } else {
                write!(f, "+ k{} * {} ", i, p)?;
            }
        }
        write!(f, "| k_i >= 0 }}")
    }
}

/// A semilinear set: a finite union of linear sets.
///
/// Every Parikh image of a context-free language is a semilinear set
/// (Parikh's theorem). Semilinear sets are closed under union, intersection,
/// and complement (Ginsburg & Spanier 1966).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SemilinearSet<const D: usize> {
    /// The constituent linear sets. The semilinear set is their union.
    pub components: Vec<LinearSet<D>>,
}

impl<const D: usize> SemilinearSet<D> {
    /// Create an empty semilinear set (represents the empty language).
    pub fn empty() -> Self {
        SemilinearSet { components: Vec::new() }
    }

    /// Create a semilinear set from a single linear set.
    pub fn from_linear(linear: LinearSet<D>) -> Self {
        SemilinearSet { components: vec![linear] }
    }

    /// Create a semilinear set from multiple linear sets.
    pub fn from_components(components: Vec<LinearSet<D>>) -> Self {
        SemilinearSet { components }
    }

    /// Check if the semilinear set is empty.
    pub fn is_empty(&self) -> bool {
        self.components.is_empty()
    }

    /// Number of linear set components.
    pub fn num_components(&self) -> usize {
        self.components.len()
    }

    /// Union of two semilinear sets.
    pub fn union(&self, other: &SemilinearSet<D>) -> SemilinearSet<D> {
        let mut components = self.components.clone();
        components.extend(other.components.iter().cloned());
        SemilinearSet { components }
    }

    /// Check whether a given vector belongs to this semilinear set.
    pub fn contains(&self, target: &ParikhWeight<D>) -> bool {
        self.components.iter().any(|ls| ls.contains(target))
    }

    /// Enumerate all vectors in this semilinear set with total count <= bound.
    ///
    /// Returns a set of Parikh weights. Useful for testing and debugging.
    pub fn enumerate(&self, max_total: u64) -> HashSet<ParikhWeight<D>> {
        let mut result = HashSet::new();

        for ls in &self.components {
            if ls.base.total() > max_total {
                continue;
            }
            result.insert(ls.base.clone());

            if !ls.periods.is_empty() {
                // BFS over coefficient combinations
                let mut queue: VecDeque<ParikhWeight<D>> = VecDeque::new();
                queue.push_back(ls.base.clone());

                while let Some(current) = queue.pop_front() {
                    for period in &ls.periods {
                        use mettail_prattail::automata::semiring::Semiring;
                        let next = current.times(period);
                        if next.total() <= max_total && !result.contains(&next) {
                            result.insert(next.clone());
                            queue.push_back(next);
                        }
                    }
                }
            }
        }

        result
    }
}

impl<const D: usize> fmt::Display for SemilinearSet<D> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_empty() {
            return write!(f, "{{}}");
        }
        for (i, ls) in self.components.iter().enumerate() {
            if i > 0 {
                write!(f, " ∪ ")?;
            }
            write!(f, "{}", ls)?;
        }
        Ok(())
    }
}

/// Project a Parikh automaton to a semilinear set.
///
/// Computes the Parikh image of the language accepted by the automaton.
/// This is done by enumerating all simple paths (without repeated states)
/// from the initial state to each accepting state, collecting the
/// accumulated Parikh weight as the base vector. Cycle weights become
/// period vectors.
///
/// This implementation handles small automata correctly. For large automata,
/// more sophisticated algorithms (e.g., based on linear algebra over ℕ)
/// would be needed.
pub fn project_semilinear<const D: usize>(automaton: &ParikhAutomaton<D>) -> SemilinearSet<D> {
    use mettail_prattail::automata::semiring::Semiring;

    let n = automaton.num_states();
    let mut components: Vec<LinearSet<D>> = Vec::new();

    // For each accepting state, find all simple paths from the initial state
    // and all simple cycles that can be inserted along those paths.

    // DFS to find simple paths from initial to each accepting state
    struct DfsFrame<const D: usize> {
        state: StateId,
        weight: ParikhWeight<D>,
        visited: Vec<bool>,
        transition_idx: usize,
    }

    for &accept in &automaton.accepting_states {
        let mut visited = vec![false; n];
        visited[automaton.initial_state] = true;

        let mut stack: Vec<DfsFrame<D>> = Vec::with_capacity(n);
        stack.push(DfsFrame {
            state: automaton.initial_state,
            weight: ParikhWeight::one(),
            visited: visited.clone(),
            transition_idx: 0,
        });

        while let Some(frame) = stack.last_mut() {
            let transitions = automaton.transitions_from(frame.state);
            if frame.transition_idx >= transitions.len() {
                stack.pop();
                continue;
            }

            let t = &transitions[frame.transition_idx];
            frame.transition_idx += 1;

            let new_weight = frame.weight.times(&t.weight);

            if t.to == accept {
                // Found a simple path to the accepting state.
                // Collect cycle periods from states along this path.
                let mut periods: Vec<ParikhWeight<D>> = Vec::new();

                // Find simple cycles reachable from states on this path
                for (i, &vis) in frame.visited.iter().enumerate() {
                    if vis {
                        // Check for self-loops and short cycles from state i
                        for ct in automaton.transitions_from(i) {
                            if ct.to == i {
                                // Self-loop
                                let cycle_weight = ct.weight.clone();
                                if !cycle_weight.is_zero() && !periods.contains(&cycle_weight) {
                                    periods.push(cycle_weight);
                                }
                            }
                        }
                    }
                }

                components.push(LinearSet::new(new_weight, periods));
            } else if !frame.visited[t.to] {
                let mut new_visited = frame.visited.clone();
                new_visited[t.to] = true;
                stack.push(DfsFrame {
                    state: t.to,
                    weight: new_weight,
                    visited: new_visited,
                    transition_idx: 0,
                });
            }
        }
    }

    // Deduplicate components
    components.sort_by(|a, b| a.base.cmp(&b.base));
    components.dedup();

    SemilinearSet::from_components(components)
}

#[cfg(test)]
mod tests {
    use super::*;
    use mettail_prattail::automata::semiring::Semiring;

    type P2 = ParikhWeight<2>;

    /// Build a simple automaton: q0 --a/[1,0]--> q1 --b/[0,1]--> q2 (accepting)
    fn simple_counter_automaton() -> ParikhAutomaton<2> {
        let mut aut = ParikhAutomaton::<2>::new("start");
        let q1 = aut.add_state("mid");
        let q2 = aut.add_state("end");
        aut.set_accepting(q2);

        aut.add_transition(ParikhTransition::new(0, q1, Some(b'a'), P2::unit(0)));
        aut.add_transition(ParikhTransition::new(q1, q2, Some(b'b'), P2::unit(1)));
        aut
    }

    #[test]
    fn test_simple_run() {
        let aut = simple_counter_automaton();
        let result = aut.run(b"ab");
        assert!(result.is_some(), "should accept 'ab'");
        let w = result.expect("accepting run should have a weight");
        assert_eq!(w, P2::new([1, 1]), "a counts dim 0, b counts dim 1");
    }

    #[test]
    fn test_reject_wrong_input() {
        let aut = simple_counter_automaton();
        assert!(aut.run(b"ba").is_none(), "should reject 'ba'");
        assert!(aut.run(b"a").is_none(), "should reject 'a' (not accepting)");
        assert!(aut.run(b"").is_none(), "should reject empty (not accepting)");
    }

    #[test]
    fn test_epsilon_transition() {
        let mut aut = ParikhAutomaton::<2>::new("start");
        let q1 = aut.add_state("mid");
        let q2 = aut.add_state("end");
        aut.set_accepting(q2);

        aut.add_transition(ParikhTransition::new(0, q1, Some(b'a'), P2::unit(0)));
        aut.add_transition(ParikhTransition::epsilon(q1, q2, P2::unit(1)));

        let result = aut.run(b"a");
        assert!(result.is_some(), "should accept 'a' via epsilon to accepting");
        let w = result.expect("accepting run should have a weight");
        assert_eq!(w, P2::new([1, 1]), "a + epsilon weight");
    }

    #[test]
    fn test_looping_automaton() {
        // q0 --a/[1,0]--> q0, q0 --b/[0,1]--> q1 (accepting)
        let mut aut = ParikhAutomaton::<2>::new("loop");
        let q1 = aut.add_state("end");
        aut.set_accepting(q1);

        aut.add_transition(ParikhTransition::new(0, 0, Some(b'a'), P2::unit(0)));
        aut.add_transition(ParikhTransition::new(0, q1, Some(b'b'), P2::unit(1)));

        let w1 = aut.run(b"b").expect("should accept 'b'");
        assert_eq!(w1, P2::new([0, 1]));

        let w2 = aut.run(b"aab").expect("should accept 'aab'");
        assert_eq!(w2, P2::new([2, 1]));

        let w3 = aut.run(b"aaaab").expect("should accept 'aaaab'");
        assert_eq!(w3, P2::new([4, 1]));
    }

    #[test]
    fn test_intersection() {
        // Automaton 1: accepts a*b, counting a's in dim 0
        let mut aut1 = ParikhAutomaton::<2>::new("a1_start");
        let q1 = aut1.add_state("a1_end");
        aut1.set_accepting(q1);
        aut1.add_transition(ParikhTransition::new(0, 0, Some(b'a'), P2::unit(0)));
        aut1.add_transition(ParikhTransition::new(0, q1, Some(b'b'), P2::new([0, 0])));

        // Automaton 2: accepts a*b, counting b's in dim 1
        let mut aut2 = ParikhAutomaton::<2>::new("a2_start");
        let q2 = aut2.add_state("a2_end");
        aut2.set_accepting(q2);
        aut2.add_transition(ParikhTransition::new(0, 0, Some(b'a'), P2::new([0, 0])));
        aut2.add_transition(ParikhTransition::new(0, q2, Some(b'b'), P2::unit(1)));

        let product = aut1.intersect(&aut2);
        let w = product.run(b"aab").expect("product should accept 'aab'");
        assert_eq!(w, P2::new([2, 1]), "should count a's and b's from both automata");
    }

    #[test]
    fn test_linear_set_contains() {
        // {[2, 3] + k * [1, 0] | k >= 0}
        let ls = LinearSet::<2>::new(P2::new([2, 3]), vec![P2::unit(0)]);
        assert!(ls.contains(&P2::new([2, 3])), "base should be contained");
        assert!(ls.contains(&P2::new([5, 3])), "[5,3] = [2,3] + 3*[1,0]");
        assert!(!ls.contains(&P2::new([1, 3])), "[1,3] < base");
        assert!(!ls.contains(&P2::new([2, 4])), "dim 1 doesn't match");
    }

    #[test]
    fn test_semilinear_set_contains() {
        let sl = SemilinearSet::from_components(vec![
            LinearSet::singleton(P2::new([1, 0])),
            LinearSet::new(P2::new([0, 1]), vec![P2::unit(1)]),
        ]);

        assert!(sl.contains(&P2::new([1, 0])), "first component");
        assert!(sl.contains(&P2::new([0, 1])), "second component base");
        assert!(sl.contains(&P2::new([0, 5])), "second component with k=4");
        assert!(!sl.contains(&P2::new([1, 1])), "not in either component");
    }

    #[test]
    fn test_semilinear_projection() {
        // Simple automaton: q0 --a/[1,0]--> q1 (accepting)
        let mut aut = ParikhAutomaton::<2>::new("start");
        let q1 = aut.add_state("end");
        aut.set_accepting(q1);
        aut.add_transition(ParikhTransition::new(0, q1, Some(b'a'), P2::unit(0)));

        let sl = project_semilinear(&aut);
        assert!(!sl.is_empty(), "should have at least one component");
        assert!(sl.contains(&P2::new([1, 0])), "should contain [1,0] for input 'a'");
    }

    #[test]
    fn test_display() {
        let aut = simple_counter_automaton();
        let display = format!("{}", aut);
        assert!(display.contains("ParikhAutomaton"), "display should mention type");
        assert!(display.contains("States: 3"), "should have 3 states");
    }

    #[test]
    fn test_all_runs_multiple() {
        // Non-deterministic: two paths ending at DIFFERENT accepting states,
        // producing different Parikh vectors. The semiring merges weights per
        // state, so distinct results require distinct accepting states.
        // Path 1: q0 --a/[1,0]--> q1 --b/[0,1]--> q2a  → weight = [1,1]
        // Path 2: q0 --a/[2,0]--> q3 --b/[0,2]--> q2b  → weight = [2,2]
        let mut aut = ParikhAutomaton::<2>::new("start");
        let q1 = aut.add_state("path1_mid");
        let q2a = aut.add_state("end_a");
        let q3 = aut.add_state("path2_mid");
        let q2b = aut.add_state("end_b");
        aut.set_accepting(q2a);
        aut.set_accepting(q2b);

        aut.add_transition(ParikhTransition::new(0, q1, Some(b'a'), P2::unit(0)));
        aut.add_transition(ParikhTransition::new(q1, q2a, Some(b'b'), P2::unit(1)));
        aut.add_transition(ParikhTransition::new(0, q3, Some(b'a'), P2::new([2, 0])));
        aut.add_transition(ParikhTransition::new(q3, q2b, Some(b'b'), P2::new([0, 2])));

        let runs = aut.all_runs(b"ab", 1000);
        assert_eq!(runs.len(), 2, "should have two accepting runs with distinct Parikh vectors");
        assert!(runs.contains(&P2::new([1, 1])), "path 1 should yield [1,1]");
        assert!(runs.contains(&P2::new([2, 2])), "path 2 should yield [2,2]");
    }

    #[test]
    fn test_reachable_parikh_vectors() {
        let mut aut = ParikhAutomaton::<2>::new("start");
        let q1 = aut.add_state("end");
        aut.set_accepting(q1);
        aut.add_transition(ParikhTransition::new(0, 0, Some(b'a'), P2::unit(0)));
        aut.add_transition(ParikhTransition::new(0, q1, Some(b'b'), P2::unit(1)));

        let vectors = aut.reachable_parikh_vectors(3, &[b'a', b'b']);
        // Words: b -> [0,1], ab -> [1,1], aab -> [2,1], aaab -> [3,1]
        assert!(vectors.contains(&P2::new([0, 1])));
        assert!(vectors.contains(&P2::new([1, 1])));
        assert!(vectors.contains(&P2::new([2, 1])));
    }
}
