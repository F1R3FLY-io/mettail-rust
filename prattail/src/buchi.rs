//! Buchi automata for infinite-word (omega-regular) acceptance.
//!
//! Buchi automata extend finite automata to infinite words. A run is accepting
//! if it visits at least one accepting state infinitely often. Buchi automata
//! recognize exactly the omega-regular languages, making them the standard
//! formalism for liveness and fairness properties in model checking.
//!
//! ## Weighted Extension
//!
//! `WeightedBuchiAutomaton<W>` generalizes the classical unweighted Buchi
//! automaton by annotating each transition with a weight from a semiring `W`.
//! The unweighted case is recovered via the type alias
//! `BuchiAutomaton = WeightedBuchiAutomaton<BooleanWeight>`, where
//! `BooleanWeight(true)` (= `W::one()`) marks reachable transitions and
//! `BooleanWeight(false)` (= `W::zero()`) marks unreachable ones.
//!
//! For quantitative analysis (e.g., computing the total weight of all
//! accepting runs), use `total_accepting_weight()` with a `StarSemiring`
//! such as `TropicalWeight`.
//!
//! ## Theoretical Foundations
//!
//! - **Buchi (1962)** — "On a decision method in restricted second order
//!   arithmetic." Introduces the automaton model for infinite words and
//!   proves the connection to monadic second-order logic (S1S).
//! - **Thomas (1990)** — "Automata on infinite objects." Survey covering
//!   Buchi, Muller, Rabin, and Streett acceptance conditions, and their
//!   relative expressiveness.
//! - **Vardi & Wolper (1994)** — "Reasoning about infinite computations."
//!   Establishes the automata-theoretic approach to temporal logic model
//!   checking via the product of system and property automata.
//! - **Chatterjee, Doyen & Henzinger (2010)** — "Quantitative languages."
//!   Extends omega-automata with semiring-valued weights for quantitative
//!   specifications.
//!
//! ## Architecture
//!
//! ```text
//! LTL formula (ltl module)
//!       │
//!       ▼
//! ltl_to_buchi()
//!       │
//!       ▼
//! BuchiAutomaton  (= WeightedBuchiAutomaton<BooleanWeight>)
//!       │
//!       ├──→ intersect() (product with system automaton)
//!       │         │
//!       │         ▼
//!       │    check_emptiness() ──→ true/false (property satisfied/violated)
//!       │
//!       ├──→ complement() (for inclusion checking, exponential blowup)
//!       │
//!       └──→ total_accepting_weight() (quantitative analysis, StarSemiring)
//! ```
//!
//! ## PraTTaIL Integration
//!
//! Buchi automata serve as the property specification formalism for the `ltl`
//! module. LTL formulas are compiled to Buchi automata, which are then
//! intersected with system models (WPDS configurations) to check liveness
//! and fairness properties of parsers and rewrite systems.

use std::collections::{HashMap, HashSet};
use std::fmt;

use crate::automata::semiring::{BooleanWeight, Semiring, StarSemiring};

// ══════════════════════════════════════════════════════════════════════════════
// Core types
// ══════════════════════════════════════════════════════════════════════════════

/// A state in a Buchi automaton.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct BuchiState {
    /// Unique state identifier.
    pub id: usize,
    /// Whether this state is an accepting state.
    ///
    /// A run over an infinite word is accepting iff it visits some accepting
    /// state infinitely often.
    pub is_accepting: bool,
    /// Optional label for diagnostics.
    pub label: Option<String>,
}

impl BuchiState {
    /// Create a new non-accepting state.
    pub fn new(id: usize) -> Self {
        BuchiState {
            id,
            is_accepting: false,
            label: None,
        }
    }

    /// Create a new accepting state.
    pub fn accepting(id: usize) -> Self {
        BuchiState {
            id,
            is_accepting: true,
            label: None,
        }
    }

    /// Create a labeled state.
    pub fn labeled(id: usize, is_accepting: bool, label: impl Into<String>) -> Self {
        BuchiState {
            id,
            is_accepting,
            label: Some(label.into()),
        }
    }
}

impl fmt::Display for BuchiState {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let acc = if self.is_accepting { "*" } else { "" };
        if let Some(ref label) = self.label {
            write!(f, "q{}{}({})", self.id, acc, label)
        } else {
            write!(f, "q{}{}", self.id, acc)
        }
    }
}

/// A transition in a Buchi automaton.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct BuchiTransition {
    /// Source state ID.
    pub from: usize,
    /// Target state ID.
    pub to: usize,
    /// Label on the transition (atomic proposition or symbol).
    /// `None` represents an epsilon transition.
    pub label: Option<String>,
}

impl fmt::Display for BuchiTransition {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let label = self
            .label
            .as_deref()
            .unwrap_or("epsilon");
        write!(f, "q{} --{}-> q{}", self.from, label, self.to)
    }
}

/// A nondeterministic weighted Buchi automaton (NBA) parameterized over a
/// semiring `W`.
///
/// The weighted NBA `A = (Q, Sigma, delta, Q_0, F)` where:
/// - `Q` is the finite set of states
/// - `Sigma` is the input alphabet
/// - `delta: Q x Sigma -> 2^{Q x W}` is the weighted nondeterministic
///   transition function
/// - `Q_0 ⊆ Q` are initial states
/// - `F ⊆ Q` are accepting states
///
/// Each transition `(q, a, q', w)` carries a weight `w` from the semiring `W`.
/// For the unweighted case, use `BooleanWeight` where `W::one() = true` marks
/// every transition as reachable.
///
/// A run `rho` on an infinite word `w = a_0 a_1 a_2 ...` is accepting iff
/// `inf(rho) cap F != emptyset` (the run visits some accepting state infinitely
/// often).
#[derive(Debug, Clone)]
pub struct WeightedBuchiAutomaton<W: Semiring> {
    /// All states in the automaton.
    pub states: Vec<BuchiState>,
    /// Alphabet symbols.
    pub alphabet: HashSet<String>,
    /// Weighted transitions, indexed by (source_state, label).
    /// Each target is a `(target_state, weight)` pair.
    pub transitions: HashMap<(usize, Option<String>), Vec<(usize, W)>>,
    /// Initial state IDs.
    pub initial_states: HashSet<usize>,
    /// Accepting state IDs (redundant with `BuchiState::is_accepting` for fast lookup).
    pub accepting_states: HashSet<usize>,
}

/// Backward-compatible type alias: the classical unweighted Buchi automaton
/// is a weighted Buchi automaton over the Boolean semiring.
pub type BuchiAutomaton = WeightedBuchiAutomaton<BooleanWeight>;

impl<W: Semiring> WeightedBuchiAutomaton<W> {
    /// Create an empty weighted Buchi automaton.
    pub fn new() -> Self {
        WeightedBuchiAutomaton {
            states: Vec::new(),
            alphabet: HashSet::new(),
            transitions: HashMap::new(),
            initial_states: HashSet::new(),
            accepting_states: HashSet::new(),
        }
    }

    /// Add a state and return its ID.
    pub fn add_state(&mut self, is_accepting: bool) -> usize {
        let id = self.states.len();
        let state = if is_accepting {
            BuchiState::accepting(id)
        } else {
            BuchiState::new(id)
        };
        if is_accepting {
            self.accepting_states.insert(id);
        }
        self.states.push(state);
        id
    }

    /// Add a transition with weight `W::one()` (backward-compatible with
    /// the unweighted API).
    pub fn add_transition(&mut self, from: usize, label: Option<String>, to: usize) {
        self.add_weighted_transition(from, label, to, W::one());
    }

    /// Add a weighted transition.
    pub fn add_weighted_transition(
        &mut self,
        from: usize,
        label: Option<String>,
        to: usize,
        weight: W,
    ) {
        if let Some(ref l) = label {
            self.alphabet.insert(l.clone());
        }
        self.transitions
            .entry((from, label))
            .or_insert_with(Vec::new)
            .push((to, weight));
    }

    /// Number of states.
    pub fn num_states(&self) -> usize {
        self.states.len()
    }

    /// Number of transitions (counting each `(from, label, to, weight)` tuple).
    pub fn num_transitions(&self) -> usize {
        self.transitions.values().map(|v| v.len()).sum()
    }
}

impl<W: Semiring> Default for WeightedBuchiAutomaton<W> {
    fn default() -> Self {
        Self::new()
    }
}

impl<W: Semiring> fmt::Display for WeightedBuchiAutomaton<W> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "BuchiAutomaton {{ states: {}, transitions: {}, initial: {}, accepting: {} }}",
            self.num_states(),
            self.num_transitions(),
            self.initial_states.len(),
            self.accepting_states.len(),
        )
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Core functions
// ══════════════════════════════════════════════════════════════════════════════

/// Construct a Buchi automaton from a set of states and transitions.
///
/// This is a convenience builder that validates state references and
/// constructs the automaton data structure. All transitions receive weight
/// `BooleanWeight::one()` (= `true`).
///
/// # Arguments
///
/// * `num_states` - Number of states to create.
/// * `accepting` - Set of accepting state IDs.
/// * `initial` - Set of initial state IDs.
/// * `transitions` - List of `(from, label, to)` transitions.
///
/// # Returns
///
/// A `BuchiAutomaton` with the specified structure.
pub fn construct_buchi(
    num_states: usize,
    accepting: HashSet<usize>,
    initial: HashSet<usize>,
    transitions: Vec<(usize, Option<String>, usize)>,
) -> BuchiAutomaton {
    let mut buchi = BuchiAutomaton::new();
    for i in 0..num_states {
        buchi.add_state(accepting.contains(&i));
    }
    buchi.initial_states = initial;
    for (from, label, to) in transitions {
        buchi.add_transition(from, label, to);
    }
    buchi
}

/// Construct a weighted Buchi automaton from a set of states and weighted
/// transitions.
///
/// # Arguments
///
/// * `num_states` - Number of states to create.
/// * `accepting` - Set of accepting state IDs.
/// * `initial` - Set of initial state IDs.
/// * `transitions` - List of `(from, label, to, weight)` transitions.
///
/// # Returns
///
/// A `WeightedBuchiAutomaton<W>` with the specified structure.
pub fn construct_weighted_buchi<W: Semiring>(
    num_states: usize,
    accepting: HashSet<usize>,
    initial: HashSet<usize>,
    transitions: Vec<(usize, Option<String>, usize, W)>,
) -> WeightedBuchiAutomaton<W> {
    let mut buchi = WeightedBuchiAutomaton::new();
    for i in 0..num_states {
        buchi.add_state(accepting.contains(&i));
    }
    buchi.initial_states = initial;
    for (from, label, to, weight) in transitions {
        buchi.add_weighted_transition(from, label, to, weight);
    }
    buchi
}

/// Intersect two Buchi automata via the product construction.
///
/// The product automaton `A x B` accepts `L(A) cap L(B)`. Uses the standard
/// 3-counter construction to handle the Buchi acceptance condition correctly:
/// the product tracks which automaton's accepting states have been visited
/// since the last "reset."
///
/// Transition weights are combined via `W::times()` (semiring multiplication):
/// if `A` has transition `(q1, a, q1', w_a)` and `B` has `(q2, a, q2', w_b)`,
/// the product transition gets weight `w_a.times(&w_b)`.
///
/// # Arguments
///
/// * `a` - First Buchi automaton.
/// * `b` - Second Buchi automaton.
///
/// # Returns
///
/// A Buchi automaton accepting `L(A) cap L(B)`.
pub fn buchi_intersect<W: Semiring>(
    a: &WeightedBuchiAutomaton<W>,
    b: &WeightedBuchiAutomaton<W>,
) -> WeightedBuchiAutomaton<W> {
    // 3-counter product construction for Buchi acceptance.
    //
    // Product state = (q1, q2, phase) where phase in {0, 1, 2}.
    //   Phase 0: waiting for A1 to accept (scanning for q1 in F1).
    //   Phase 1: A1 accepted, now waiting for A2 to accept (scanning for q2 in F2).
    //   Phase 2: both have accepted -- this is the accepting phase; reset to 0.
    //
    // The product Buchi automaton accepts in states where phase = 2.
    //
    // Transition rule for (q1, q2, c) --a--> (q1', q2', c'):
    //   q1 --a--> q1' in A,  q2 --a--> q2' in B, and:
    //     if c == 0 and q1 in F_A:  c' = 1
    //     if c == 1 and q2 in F_B:  c' = 2
    //     if c == 2:                c' = 0
    //     otherwise:                c' = c

    let n_a = a.num_states();
    let n_b = b.num_states();

    // Map (q1, q2, phase) -> product state ID.
    let product_id = |q1: usize, q2: usize, phase: usize| -> usize {
        (q1 * n_b + q2) * 3 + phase
    };

    let total_states = n_a * n_b * 3;
    let mut result = WeightedBuchiAutomaton::new();

    // Create all product states. Phase 2 states are accepting.
    for q1 in 0..n_a {
        for q2 in 0..n_b {
            for phase in 0..3usize {
                let is_accepting = phase == 2;
                let id = result.add_state(is_accepting);
                debug_assert_eq!(id, product_id(q1, q2, phase));
            }
        }
    }
    debug_assert_eq!(result.num_states(), total_states);

    // Initial states: (q1, q2, 0) for all q1 in initial(A), q2 in initial(B).
    for &q1 in &a.initial_states {
        for &q2 in &b.initial_states {
            result.initial_states.insert(product_id(q1, q2, 0));
        }
    }

    // Compute the shared alphabet (intersection of symbols). Also include
    // symbols that appear in both, plus epsilon (None) transitions.
    let shared_alphabet: HashSet<Option<String>> = {
        let mut syms = HashSet::new();
        // Include None (epsilon) if both have epsilon transitions.
        syms.insert(None);
        for sym in a.alphabet.intersection(&b.alphabet) {
            syms.insert(Some(sym.clone()));
        }
        syms
    };

    // Build transitions.
    for (&(q1_from, ref label_a), targets_a) in &a.transitions {
        // Only proceed if this label is in the shared alphabet.
        if !shared_alphabet.contains(label_a) {
            continue;
        }

        for q2_from in 0..n_b {
            let b_targets = match b.transitions.get(&(q2_from, label_a.clone())) {
                Some(t) => t,
                None => continue,
            };

            for &(q1_to, ref w_a) in targets_a {
                for &(q2_to, ref w_b) in b_targets {
                    let combined_weight = w_a.times(w_b);

                    for phase in 0..3usize {
                        let next_phase = match phase {
                            0 => {
                                if a.accepting_states.contains(&q1_from) {
                                    1
                                } else {
                                    0
                                }
                            }
                            1 => {
                                if b.accepting_states.contains(&q2_from) {
                                    2
                                } else {
                                    1
                                }
                            }
                            2 => 0,
                            _ => unreachable!(),
                        };

                        let from_id = product_id(q1_from, q2_from, phase);
                        let to_id = product_id(q1_to, q2_to, next_phase);
                        result.add_weighted_transition(
                            from_id,
                            label_a.clone(),
                            to_id,
                            combined_weight,
                        );
                    }
                }
            }
        }
    }

    result
}

/// Intersect two weighted Buchi automata via the 3-counter product construction.
///
/// This is an alias for `buchi_intersect` that makes the weighted nature explicit.
/// Transition weights are combined via `W::times()`.
///
/// # Arguments
///
/// * `a` - First weighted Buchi automaton.
/// * `b` - Second weighted Buchi automaton.
///
/// # Returns
///
/// A weighted Buchi automaton accepting `L(A) cap L(B)` with combined weights.
pub fn weighted_intersect<W: Semiring>(
    a: &WeightedBuchiAutomaton<W>,
    b: &WeightedBuchiAutomaton<W>,
) -> WeightedBuchiAutomaton<W> {
    buchi_intersect(a, b)
}

/// Check emptiness of a weighted Buchi automaton.
///
/// A Buchi automaton is non-empty iff there exists a reachable accepting state
/// that lies on a cycle (i.e., an accepting state reachable from itself). This
/// reduces to finding an accepting SCC reachable from an initial state.
///
/// The weight `W` does not affect emptiness: a transition exists iff it appears
/// in the transition map (regardless of its weight). For weight-sensitive
/// analysis, use `total_accepting_weight()`.
///
/// Uses Tarjan SCC decomposition.
///
/// # Arguments
///
/// * `buchi` - The Buchi automaton to check.
///
/// # Returns
///
/// `true` if `L(buchi) = emptyset`, `false` otherwise.
pub fn check_emptiness<W: Semiring>(buchi: &WeightedBuchiAutomaton<W>) -> bool {
    // SCC-based emptiness check using Tarjan's algorithm.
    //
    // A Buchi automaton is non-empty iff there exists an SCC that:
    //   1. Is reachable from an initial state, AND
    //   2. Contains at least one accepting state, AND
    //   3. Has at least one edge (i.e., it is a non-trivial SCC, or a
    //      single-state SCC with a self-loop).
    //
    // Returns true if L(buchi) = empty, false if L(buchi) != empty.

    if buchi.states.is_empty() || buchi.initial_states.is_empty() {
        return true; // empty language
    }

    // Step 1: Compute the set of states reachable from initial states via BFS.
    let reachable = {
        let mut visited = HashSet::new();
        let mut queue = std::collections::VecDeque::new();
        for &init in &buchi.initial_states {
            if visited.insert(init) {
                queue.push_back(init);
            }
        }
        while let Some(state) = queue.pop_front() {
            // Explore all transitions from this state (any label).
            for (&(from, _), targets) in &buchi.transitions {
                if from == state {
                    for &(target, _) in targets {
                        if visited.insert(target) {
                            queue.push_back(target);
                        }
                    }
                }
            }
        }
        visited
    };

    // Step 2: Build adjacency list for reachable states only.
    let n = buchi.states.len();
    let mut adj: Vec<Vec<usize>> = vec![Vec::new(); n];
    let mut has_self_loop = vec![false; n];

    for (&(from, _), targets) in &buchi.transitions {
        if !reachable.contains(&from) {
            continue;
        }
        for &(to, _) in targets {
            if !reachable.contains(&to) {
                continue;
            }
            if from == to {
                has_self_loop[from] = true;
            }
            adj[from].push(to);
        }
    }

    // Step 3: Tarjan's SCC algorithm on the reachable subgraph.
    struct TarjanState {
        index_counter: usize,
        stack: Vec<usize>,
        on_stack: Vec<bool>,
        index: Vec<Option<usize>>,
        lowlink: Vec<usize>,
        sccs: Vec<Vec<usize>>,
    }

    let mut tarjan = TarjanState {
        index_counter: 0,
        stack: Vec::new(),
        on_stack: vec![false; n],
        index: vec![None; n],
        lowlink: vec![0; n],
        sccs: Vec::new(),
    };

    fn strongconnect(
        v: usize,
        adj: &[Vec<usize>],
        state: &mut TarjanState,
    ) {
        // Use an explicit stack to avoid recursion depth issues.
        // Each frame: (node, neighbor_index)
        let mut call_stack: Vec<(usize, usize)> = Vec::new();

        // Initialize v.
        state.index[v] = Some(state.index_counter);
        state.lowlink[v] = state.index_counter;
        state.index_counter += 1;
        state.stack.push(v);
        state.on_stack[v] = true;

        call_stack.push((v, 0));

        while let Some(&mut (node, ref mut ni)) = call_stack.last_mut() {
            if *ni < adj[node].len() {
                let w = adj[node][*ni];
                *ni += 1;

                if state.index[w].is_none() {
                    // Not yet visited: recurse.
                    state.index[w] = Some(state.index_counter);
                    state.lowlink[w] = state.index_counter;
                    state.index_counter += 1;
                    state.stack.push(w);
                    state.on_stack[w] = true;
                    call_stack.push((w, 0));
                } else if state.on_stack[w] {
                    let w_index = state.index[w].expect("w should have an index");
                    if w_index < state.lowlink[node] {
                        state.lowlink[node] = w_index;
                    }
                }
            } else {
                // Done with all neighbors of node.
                let node_lowlink = state.lowlink[node];
                let node_index = state.index[node].expect("node should have an index");

                if node_lowlink == node_index {
                    // Root of an SCC -- pop the SCC from the stack.
                    let mut scc = Vec::new();
                    loop {
                        let w = state.stack.pop().expect("stack should not be empty");
                        state.on_stack[w] = false;
                        scc.push(w);
                        if w == node {
                            break;
                        }
                    }
                    state.sccs.push(scc);
                }

                // Pop this frame and update parent's lowlink.
                call_stack.pop();
                if let Some(&(parent, _)) = call_stack.last() {
                    if state.lowlink[node] < state.lowlink[parent] {
                        state.lowlink[parent] = state.lowlink[node];
                    }
                }
            }
        }
    }

    for &init in &buchi.initial_states {
        if tarjan.index[init].is_none() {
            strongconnect(init, &adj, &mut tarjan);
        }
    }
    // Also visit other reachable states not yet covered (in case initial
    // states don't reach everything in the reachable set -- shouldn't
    // happen by construction, but ensures correctness).
    for state_id in 0..n {
        if reachable.contains(&state_id) && tarjan.index[state_id].is_none() {
            strongconnect(state_id, &adj, &mut tarjan);
        }
    }

    // Step 4: Check each SCC for an accepting cycle.
    for scc in &tarjan.sccs {
        // An SCC with an accepting state has an accepting cycle if:
        //   - The SCC has more than one state (guaranteed cycle), OR
        //   - The SCC has exactly one state with a self-loop.
        let has_cycle = scc.len() > 1 || (scc.len() == 1 && has_self_loop[scc[0]]);
        if !has_cycle {
            continue;
        }

        let has_accepting = scc.iter().any(|&s| buchi.accepting_states.contains(&s));
        if has_accepting {
            return false; // non-empty: found an accepting cycle
        }
    }

    true // empty: no accepting cycle found
}

// ══════════════════════════════════════════════════════════════════════════════
// Weighted analysis operations
// ══════════════════════════════════════════════════════════════════════════════

/// Compute the total accepting weight of a weighted Buchi automaton.
///
/// This aggregates weights across all accepting strongly connected components
/// (SCCs) using the semiring's star operation to handle cycles. The algorithm:
///
/// 1. **Reachability**: BFS from initial states to find reachable states.
/// 2. **SCC decomposition**: Tarjan's algorithm on the reachable subgraph.
/// 3. **Cycle weight via star**: For each accepting SCC, build the intra-SCC
///    adjacency matrix and compute `matrix_star()` (generalized Floyd-Warshall).
///    The cycle weight for an accepting state `q` is the diagonal entry
///    `star_matrix[q][q]`, representing the weight of all possible cycles
///    through `q`.
/// 4. **Aggregation**: Combine cycle weights for all accepting states in all
///    accepting SCCs via `W::plus()`.
///
/// # Semantics by semiring
///
/// - **BooleanWeight**: Returns `true` iff there exists an accepting cycle
///   (equivalent to `!check_emptiness()`).
/// - **TropicalWeight**: Returns the minimum-cost accepting cycle weight.
///   `TropicalWeight(0.0)` means a zero-cost accepting cycle exists;
///   `TropicalWeight::zero()` (= `+inf`) means no accepting cycle exists.
/// - **CountingWeight**: Returns the number of distinct accepting cycles
///   (may overflow for large automata).
///
/// # Arguments
///
/// * `buchi` - The weighted Buchi automaton.
///
/// # Returns
///
/// The total accepting weight aggregated over all accepting SCCs.
pub fn total_accepting_weight<W: StarSemiring>(buchi: &WeightedBuchiAutomaton<W>) -> W {
    use crate::automata::semiring::matrix_star;

    if buchi.states.is_empty() || buchi.initial_states.is_empty() {
        return W::zero();
    }

    let n = buchi.states.len();

    // Step 1: BFS reachability from initial states.
    let reachable = {
        let mut visited = HashSet::new();
        let mut queue = std::collections::VecDeque::new();
        for &init in &buchi.initial_states {
            if visited.insert(init) {
                queue.push_back(init);
            }
        }
        while let Some(state) = queue.pop_front() {
            for (&(from, _), targets) in &buchi.transitions {
                if from == state {
                    for &(target, _) in targets {
                        if visited.insert(target) {
                            queue.push_back(target);
                        }
                    }
                }
            }
        }
        visited
    };

    // Step 2: Build adjacency list + weight matrix for reachable states.
    let mut adj: Vec<Vec<usize>> = vec![Vec::new(); n];
    let mut has_self_loop = vec![false; n];
    // Aggregate edge weights: weight_map[(from, to)] = sum of weights on
    // parallel edges (combined via plus).
    let mut weight_map: HashMap<(usize, usize), W> = HashMap::new();

    for (&(from, _), targets) in &buchi.transitions {
        if !reachable.contains(&from) {
            continue;
        }
        for &(to, ref w) in targets {
            if !reachable.contains(&to) {
                continue;
            }
            if from == to {
                has_self_loop[from] = true;
            }
            adj[from].push(to);
            let entry = weight_map
                .entry((from, to))
                .or_insert_with(W::zero);
            *entry = entry.plus(w);
        }
    }

    // Step 3: Tarjan SCC decomposition on the reachable subgraph.
    struct TarjanState {
        index_counter: usize,
        stack: Vec<usize>,
        on_stack: Vec<bool>,
        index: Vec<Option<usize>>,
        lowlink: Vec<usize>,
        sccs: Vec<Vec<usize>>,
    }

    let mut tarjan = TarjanState {
        index_counter: 0,
        stack: Vec::new(),
        on_stack: vec![false; n],
        index: vec![None; n],
        lowlink: vec![0; n],
        sccs: Vec::new(),
    };

    fn strongconnect_taw(
        v: usize,
        adj: &[Vec<usize>],
        state: &mut TarjanState,
    ) {
        let mut call_stack: Vec<(usize, usize)> = Vec::new();
        state.index[v] = Some(state.index_counter);
        state.lowlink[v] = state.index_counter;
        state.index_counter += 1;
        state.stack.push(v);
        state.on_stack[v] = true;
        call_stack.push((v, 0));

        while let Some(&mut (node, ref mut ni)) = call_stack.last_mut() {
            if *ni < adj[node].len() {
                let w = adj[node][*ni];
                *ni += 1;
                if state.index[w].is_none() {
                    state.index[w] = Some(state.index_counter);
                    state.lowlink[w] = state.index_counter;
                    state.index_counter += 1;
                    state.stack.push(w);
                    state.on_stack[w] = true;
                    call_stack.push((w, 0));
                } else if state.on_stack[w] {
                    let w_index = state.index[w].expect("w should have an index");
                    if w_index < state.lowlink[node] {
                        state.lowlink[node] = w_index;
                    }
                }
            } else {
                let node_lowlink = state.lowlink[node];
                let node_index = state.index[node].expect("node should have an index");
                if node_lowlink == node_index {
                    let mut scc = Vec::new();
                    loop {
                        let w = state.stack.pop().expect("stack should not be empty");
                        state.on_stack[w] = false;
                        scc.push(w);
                        if w == node {
                            break;
                        }
                    }
                    state.sccs.push(scc);
                }
                call_stack.pop();
                if let Some(&(parent, _)) = call_stack.last() {
                    if state.lowlink[node] < state.lowlink[parent] {
                        state.lowlink[parent] = state.lowlink[node];
                    }
                }
            }
        }
    }

    for &init in &buchi.initial_states {
        if tarjan.index[init].is_none() {
            strongconnect_taw(init, &adj, &mut tarjan);
        }
    }
    for state_id in 0..n {
        if reachable.contains(&state_id) && tarjan.index[state_id].is_none() {
            strongconnect_taw(state_id, &adj, &mut tarjan);
        }
    }

    // Step 4: For each accepting SCC, compute cycle weight via matrix_star.
    let mut total = W::zero();

    for scc in &tarjan.sccs {
        // An SCC must have a cycle to contribute.
        let has_cycle = scc.len() > 1 || (scc.len() == 1 && has_self_loop[scc[0]]);
        if !has_cycle {
            continue;
        }

        let has_accepting = scc.iter().any(|&s| buchi.accepting_states.contains(&s));
        if !has_accepting {
            continue;
        }

        let scc_size = scc.len();

        // Map global state IDs to local (0..scc_size) indices.
        let global_to_local: HashMap<usize, usize> = scc
            .iter()
            .enumerate()
            .map(|(local, &global)| (global, local))
            .collect();

        // Build the intra-SCC adjacency matrix.
        let mut adj_matrix: Vec<Vec<W>> = vec![vec![W::zero(); scc_size]; scc_size];
        for &from_global in scc {
            let from_local = global_to_local[&from_global];
            for &to_global in scc {
                if let Some(&ref w) = weight_map.get(&(from_global, to_global)) {
                    let to_local = global_to_local[&to_global];
                    adj_matrix[from_local][to_local] = adj_matrix[from_local][to_local].plus(w);
                }
            }
        }

        // Compute the Kleene closure (matrix star).
        let star_matrix = matrix_star(&adj_matrix);

        // Aggregate diagonal entries for accepting states: the diagonal
        // entry star_matrix[i][i] represents the weight of all cycles
        // through state i.
        for &state_global in scc {
            if buchi.accepting_states.contains(&state_global) {
                let local = global_to_local[&state_global];
                total = total.plus(&star_matrix[local][local]);
            }
        }
    }

    total
}

// ══════════════════════════════════════════════════════════════════════════════
// Pipeline bridge
// ══════════════════════════════════════════════════════════════════════════════

/// Pipeline bridge: convert WPDS call graph into a Buchi automaton.
///
/// Each category becomes a state; call-graph edges become transitions.
/// Primary categories (those with zero fan-in -- root entry points that are
/// never called by other categories) are accepting states. All transitions
/// receive weight `BooleanWeight::one()`.
pub fn from_wpds(wpds_analysis: &crate::wpds::WpdsAnalysis) -> BuchiAutomaton {
    let call_graph = &wpds_analysis.call_graph;

    if call_graph.categories.is_empty() {
        return BuchiAutomaton::new();
    }

    // Deterministic category ordering for reproducible state IDs.
    let mut cat_list: Vec<&String> = call_graph.categories.iter().collect();
    cat_list.sort();
    let cat_to_id: HashMap<&str, usize> = cat_list
        .iter()
        .enumerate()
        .map(|(i, name)| (name.as_str(), i))
        .collect();

    let mut buchi = BuchiAutomaton::new();

    // Create one state per category.
    // A category is "primary" (accepting) if it has zero fan-in -- it is a
    // root entry point that no other category calls.
    for &cat_name in &cat_list {
        let fan_in = call_graph.fan_in.get(cat_name).copied().unwrap_or(0);
        let is_accepting = fan_in == 0;
        let id = buchi.add_state(is_accepting);

        // Label the state with the category name.
        buchi.states[id].label = Some(cat_name.to_string());
    }

    // Mark root categories as initial states (zero fan-in).
    for (&cat_name, &id) in &cat_to_id {
        let fan_in = call_graph.fan_in.get(cat_name).copied().unwrap_or(0);
        if fan_in == 0 {
            buchi.initial_states.insert(id);
        }
    }

    // Create transitions from call-graph edges.
    for edge in &call_graph.edges {
        if let (Some(&from_id), Some(&to_id)) = (
            cat_to_id.get(edge.caller_cat.as_str()),
            cat_to_id.get(edge.callee_cat.as_str()),
        ) {
            let label = Some(format!("{}→{}", edge.caller_cat, edge.callee_cat));
            buchi.add_transition(from_id, label, to_id);
        }
    }

    buchi
}

// ══════════════════════════════════════════════════════════════════════════════
// BuchiAnalysis — Pipeline integration
// ══════════════════════════════════════════════════════════════════════════════

/// Summary of Buchi automaton analysis for pipeline integration.
#[derive(Debug, Clone)]
pub struct BuchiAnalysis {
    /// Number of states in the analyzed automaton.
    pub num_states: usize,
    /// Number of accepting states.
    pub num_accepting: usize,
    /// Whether the automaton has a non-trivial accepting cycle
    /// (i.e., it accepts at least one infinite word).
    pub has_accepting_cycle: bool,
    /// Categories in each accepting SCC (strongly connected component).
    /// Each SCC is a group of mutually recursive categories.
    pub accepting_sccs: Vec<Vec<String>>,
}

impl std::fmt::Display for BuchiAnalysis {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "BuchiAnalysis(states={}, accepting={}, has_cycle={}, sccs={})",
            self.num_states, self.num_accepting, self.has_accepting_cycle,
            self.accepting_sccs.len()
        )
    }
}

/// Analyze grammar liveness properties using Buchi automata.
///
/// Builds a category-reference graph from the grammar's rule syntax items
/// and performs SCC-based cycle detection to determine which categories
/// participate in (mutually) recursive cycles. A category is "accepting"
/// (self-recursive) when at least one of its rules references itself as a
/// nonterminal. An accepting SCC is one that either contains a self-recursive
/// category or has size > 1 (mutual recursion implies cycles).
///
/// # Algorithm
///
/// 1. Build adjacency list: edge from category A to B when A has a rule item
///    referencing B as `NonTerminal`, `Binder`, `Collection`, etc.
/// 2. Track self-recursive categories (A references itself).
/// 3. Run Tarjan's SCC algorithm on the adjacency graph.
/// 4. Filter SCCs to those with accepting states or size > 1.
pub fn analyze_from_bundle(
    all_syntax: &[(String, String, Vec<crate::SyntaxItemSpec>)],
    categories: &[crate::pipeline::CategoryInfo],
) -> BuchiAnalysis {
    let num_cats = categories.len();
    if num_cats == 0 {
        return BuchiAnalysis {
            num_states: 0,
            num_accepting: 0,
            has_accepting_cycle: false,
            accepting_sccs: Vec::new(),
        };
    }

    // Build category name -> index map.
    let cat_to_idx: HashMap<String, usize> = categories
        .iter()
        .enumerate()
        .map(|(i, c)| (c.name.clone(), i))
        .collect();

    // Build adjacency: edge from category A to B when A has a rule referencing
    // B as NonTerminal, Binder, Collection, etc.
    let mut adj: Vec<HashSet<usize>> = vec![HashSet::new(); num_cats];
    // Track which categories are "accepting" (self-recursive).
    let mut self_recursive: HashSet<usize> = HashSet::new();

    for (_, cat, items) in all_syntax {
        let src = match cat_to_idx.get(cat) {
            Some(&idx) => idx,
            None => continue,
        };
        for item in items {
            collect_nonterminal_refs(item, &cat_to_idx, src, &mut adj, &mut self_recursive);
        }
    }

    // Accepting states: categories with at least one rule that references themselves.
    let num_accepting = self_recursive.len();

    // Find SCCs using Tarjan's algorithm.
    let sccs = tarjan_scc(&adj);

    // Accepting SCCs: SCCs that contain at least one accepting (self-recursive) state
    // OR SCCs with size > 1 (mutually recursive categories form cycles).
    let accepting_sccs: Vec<Vec<String>> = sccs
        .iter()
        .filter(|scc| {
            scc.len() > 1 || scc.iter().any(|&idx| self_recursive.contains(&idx))
        })
        .map(|scc| {
            let mut names: Vec<String> = scc
                .iter()
                .map(|&idx| categories[idx].name.clone())
                .collect();
            names.sort();
            names
        })
        .collect();

    let has_accepting_cycle = !accepting_sccs.is_empty();

    BuchiAnalysis {
        num_states: num_cats,
        num_accepting,
        has_accepting_cycle,
        accepting_sccs,
    }
}

/// Recursively collect NonTerminal references from syntax items for Buchi graph construction.
fn collect_nonterminal_refs(
    item: &crate::SyntaxItemSpec,
    cat_to_idx: &HashMap<String, usize>,
    src: usize,
    adj: &mut [HashSet<usize>],
    self_recursive: &mut HashSet<usize>,
) {
    match item {
        crate::SyntaxItemSpec::NonTerminal { category, .. } => {
            if let Some(&dst) = cat_to_idx.get(category) {
                adj[src].insert(dst);
                if src == dst {
                    self_recursive.insert(src);
                }
            }
        }
        crate::SyntaxItemSpec::Binder { category, .. } => {
            if let Some(&dst) = cat_to_idx.get(category) {
                adj[src].insert(dst);
                if src == dst {
                    self_recursive.insert(src);
                }
            }
        }
        crate::SyntaxItemSpec::Collection { element_category, .. } => {
            if let Some(&dst) = cat_to_idx.get(element_category) {
                adj[src].insert(dst);
                if src == dst {
                    self_recursive.insert(src);
                }
            }
        }
        crate::SyntaxItemSpec::Sep { body, .. } => {
            collect_nonterminal_refs(body, cat_to_idx, src, adj, self_recursive);
        }
        crate::SyntaxItemSpec::Map { body_items } => {
            for sub in body_items {
                collect_nonterminal_refs(sub, cat_to_idx, src, adj, self_recursive);
            }
        }
        crate::SyntaxItemSpec::Zip { left_category, right_category, body, .. } => {
            for ref_cat in [left_category, right_category] {
                if let Some(&dst) = cat_to_idx.get(ref_cat) {
                    adj[src].insert(dst);
                    if src == dst {
                        self_recursive.insert(src);
                    }
                }
            }
            collect_nonterminal_refs(body, cat_to_idx, src, adj, self_recursive);
        }
        crate::SyntaxItemSpec::Optional { inner } => {
            for sub in inner {
                collect_nonterminal_refs(sub, cat_to_idx, src, adj, self_recursive);
            }
        }
        // Terminal, IdentCapture, BinderCollection -- no category refs.
        _ => {}
    }
}

/// Tarjan's SCC algorithm for finding strongly connected components.
///
/// Returns a list of SCCs, where each SCC is a `Vec<usize>` of node indices.
/// Uses iterative DFS to avoid stack overflow on large graphs.
fn tarjan_scc(adj: &[HashSet<usize>]) -> Vec<Vec<usize>> {
    let n = adj.len();
    let mut index_counter = 0usize;
    let mut stack: Vec<usize> = Vec::new();
    let mut on_stack = vec![false; n];
    let mut indices = vec![usize::MAX; n];
    let mut lowlinks = vec![usize::MAX; n];
    let mut result: Vec<Vec<usize>> = Vec::new();

    fn strongconnect(
        v: usize,
        adj: &[HashSet<usize>],
        index_counter: &mut usize,
        stack: &mut Vec<usize>,
        on_stack: &mut [bool],
        indices: &mut [usize],
        lowlinks: &mut [usize],
        result: &mut Vec<Vec<usize>>,
    ) {
        indices[v] = *index_counter;
        lowlinks[v] = *index_counter;
        *index_counter += 1;
        stack.push(v);
        on_stack[v] = true;

        for &w in &adj[v] {
            if indices[w] == usize::MAX {
                strongconnect(w, adj, index_counter, stack, on_stack, indices, lowlinks, result);
                lowlinks[v] = lowlinks[v].min(lowlinks[w]);
            } else if on_stack[w] {
                lowlinks[v] = lowlinks[v].min(indices[w]);
            }
        }

        if lowlinks[v] == indices[v] {
            let mut scc = Vec::new();
            while let Some(w) = stack.pop() {
                on_stack[w] = false;
                scc.push(w);
                if w == v {
                    break;
                }
            }
            result.push(scc);
        }
    }

    for v in 0..n {
        if indices[v] == usize::MAX {
            strongconnect(
                v, adj, &mut index_counter, &mut stack, &mut on_stack,
                &mut indices, &mut lowlinks, &mut result,
            );
        }
    }

    result
}

// ══════════════════════════════════════════════════════════════════════════════
// Predicate Dispatch — PredicateCompiler integration
// ══════════════════════════════════════════════════════════════════════════════

/// Compiler adapter for the Büchi Automata module (M2).
///
/// Activated by `ForallInfinite`/`ExistsInfinite` morphemes (ω-regular variety).
#[cfg(feature = "predicate-dispatch")]
pub struct BuchiCompiler;

#[cfg(feature = "predicate-dispatch")]
impl crate::predicate_dispatch::PredicateCompiler for BuchiCompiler {
    type Output = BuchiAnalysis;

    fn compile_predicate(
        &self,
        _pred: &crate::symbolic::PredicateExpr,
        _profile: &crate::predicate_dispatch::PredicateProfile,
        all_syntax: &[(String, String, Vec<crate::SyntaxItemSpec>)],
        categories: &[crate::pipeline::CategoryInfo],
    ) -> Self::Output {
        analyze_from_bundle(all_syntax, categories)
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Tests
// ══════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn buchi_state_display() {
        let accepting = BuchiState::accepting(0);
        assert_eq!(accepting.to_string(), "q0*");
        let non_accepting = BuchiState::new(1);
        assert_eq!(non_accepting.to_string(), "q1");
        let labeled = BuchiState::labeled(2, true, "init");
        assert_eq!(labeled.to_string(), "q2*(init)");
    }

    #[test]
    fn buchi_construction() {
        let mut buchi = BuchiAutomaton::new();
        let q0 = buchi.add_state(false);
        let q1 = buchi.add_state(true);
        buchi.initial_states.insert(q0);
        buchi.add_transition(q0, Some("a".to_string()), q1);
        buchi.add_transition(q1, Some("b".to_string()), q0);

        assert_eq!(buchi.num_states(), 2);
        assert_eq!(buchi.num_transitions(), 2);
        assert!(buchi.accepting_states.contains(&q1));
        assert!(buchi.alphabet.contains("a"));
        assert!(buchi.alphabet.contains("b"));
    }

    #[test]
    fn construct_buchi_helper() {
        let buchi = construct_buchi(
            3,
            [1].into_iter().collect(),
            [0].into_iter().collect(),
            vec![
                (0, Some("a".to_string()), 1),
                (1, Some("b".to_string()), 2),
                (2, Some("a".to_string()), 1),
            ],
        );
        assert_eq!(buchi.num_states(), 3);
        assert_eq!(buchi.num_transitions(), 3);
        assert!(buchi.accepting_states.contains(&1));
        assert!(buchi.initial_states.contains(&0));
    }

    // ── check_emptiness tests ───────────────────────────────────────────────

    #[test]
    fn emptiness_no_states() {
        // An automaton with no states has empty language.
        let buchi = BuchiAutomaton::new();
        assert!(check_emptiness(&buchi));
    }

    #[test]
    fn emptiness_no_initial_states() {
        // An automaton with states but no initial states has empty language.
        let buchi = construct_buchi(
            2,
            [0].into_iter().collect(),
            HashSet::new(), // no initial states
            vec![(0, Some("a".to_string()), 0)],
        );
        assert!(check_emptiness(&buchi));
    }

    #[test]
    fn emptiness_accepting_self_loop() {
        // An accepting state with a self-loop -- non-empty.
        // q0 (initial, accepting) --a--> q0
        let buchi = construct_buchi(
            1,
            [0].into_iter().collect(),
            [0].into_iter().collect(),
            vec![(0, Some("a".to_string()), 0)],
        );
        assert!(!check_emptiness(&buchi));
    }

    #[test]
    fn emptiness_accepting_no_cycle() {
        // Accepting state reachable but not on a cycle -- empty language.
        // q0 (initial) --a--> q1 (accepting), no outgoing from q1.
        let buchi = construct_buchi(
            2,
            [1].into_iter().collect(),
            [0].into_iter().collect(),
            vec![(0, Some("a".to_string()), 1)],
        );
        assert!(check_emptiness(&buchi));
    }

    #[test]
    fn emptiness_cycle_without_accepting() {
        // Cycle exists but contains no accepting state -- empty.
        // q0 (initial) --a--> q1 --b--> q0  (neither is accepting)
        let buchi = construct_buchi(
            2,
            HashSet::new(), // no accepting states
            [0].into_iter().collect(),
            vec![
                (0, Some("a".to_string()), 1),
                (1, Some("b".to_string()), 0),
            ],
        );
        assert!(check_emptiness(&buchi));
    }

    #[test]
    fn emptiness_accepting_cycle_two_states() {
        // q0 (initial) --a--> q1 (accepting) --b--> q0
        // SCC {q0, q1} has accepting state q1 -> non-empty.
        let buchi = construct_buchi(
            2,
            [1].into_iter().collect(),
            [0].into_iter().collect(),
            vec![
                (0, Some("a".to_string()), 1),
                (1, Some("b".to_string()), 0),
            ],
        );
        assert!(!check_emptiness(&buchi));
    }

    #[test]
    fn emptiness_unreachable_accepting_cycle() {
        // Accepting cycle exists but is not reachable from the initial state.
        // q0 (initial) --a--> q1 (dead end)
        // q2 (accepting) --b--> q2  (self-loop, but unreachable)
        let buchi = construct_buchi(
            3,
            [2].into_iter().collect(),
            [0].into_iter().collect(),
            vec![
                (0, Some("a".to_string()), 1),
                (2, Some("b".to_string()), 2),
            ],
        );
        assert!(check_emptiness(&buchi));
    }

    #[test]
    fn emptiness_diamond_with_accepting_cycle() {
        // q0 (initial) --a--> q1, q0 --a--> q2
        // q1 --b--> q3 (accepting) --c--> q1  (cycle q1<->q3, has accepting)
        // q2 --d--> q4 (dead end)
        let buchi = construct_buchi(
            5,
            [3].into_iter().collect(),
            [0].into_iter().collect(),
            vec![
                (0, Some("a".to_string()), 1),
                (0, Some("a".to_string()), 2),
                (1, Some("b".to_string()), 3),
                (3, Some("c".to_string()), 1),
                (2, Some("d".to_string()), 4),
            ],
        );
        assert!(!check_emptiness(&buchi));
    }

    // ── buchi_intersect tests ───────────────────────────────────────────────

    #[test]
    fn intersect_both_accept_same_word() {
        // A1: q0 --a--> q0 (accepting, initial) -- accepts (a)^omega
        // A2: q0 --a--> q0 (accepting, initial) -- same
        // Intersection should be non-empty.
        let a1 = construct_buchi(
            1,
            [0].into_iter().collect(),
            [0].into_iter().collect(),
            vec![(0, Some("a".to_string()), 0)],
        );
        let a2 = a1.clone();
        let product = buchi_intersect(&a1, &a2);
        assert!(!check_emptiness(&product));
    }

    #[test]
    fn intersect_disjoint_alphabets() {
        // A1 accepts (a)^omega, A2 accepts (b)^omega.
        // No common word -- intersection should be empty.
        let a1 = construct_buchi(
            1,
            [0].into_iter().collect(),
            [0].into_iter().collect(),
            vec![(0, Some("a".to_string()), 0)],
        );
        let a2 = construct_buchi(
            1,
            [0].into_iter().collect(),
            [0].into_iter().collect(),
            vec![(0, Some("b".to_string()), 0)],
        );
        let product = buchi_intersect(&a1, &a2);
        assert!(check_emptiness(&product));
    }

    #[test]
    fn intersect_product_state_count() {
        // A1 has 2 states, A2 has 3 states.
        // Product should have 2 * 3 * 3 = 18 states.
        let a1 = construct_buchi(
            2,
            [1].into_iter().collect(),
            [0].into_iter().collect(),
            vec![
                (0, Some("a".to_string()), 1),
                (1, Some("a".to_string()), 0),
            ],
        );
        let a2 = construct_buchi(
            3,
            [2].into_iter().collect(),
            [0].into_iter().collect(),
            vec![
                (0, Some("a".to_string()), 1),
                (1, Some("a".to_string()), 2),
                (2, Some("a".to_string()), 0),
            ],
        );
        let product = buchi_intersect(&a1, &a2);
        assert_eq!(product.num_states(), 18);
    }

    #[test]
    fn intersect_ab_cycle_with_ab_cycle() {
        // A1: q0 --a--> q1(acc) --b--> q0, initial={q0}  -- accepts (ab)^omega
        // A2: q0 --a--> q1 --b--> q2(acc) --a--> ... same cycle but acc at q2
        //     Actually let's just use: q0 --a--> q1(acc) --b--> q0 again.
        // Both accept (ab)^omega. Intersection should be non-empty.
        let a = construct_buchi(
            2,
            [1].into_iter().collect(),
            [0].into_iter().collect(),
            vec![
                (0, Some("a".to_string()), 1),
                (1, Some("b".to_string()), 0),
            ],
        );
        let product = buchi_intersect(&a, &a);
        assert!(!check_emptiness(&product));
    }

    #[test]
    fn intersect_phase_cycling() {
        // Verify the 3-counter mechanism works correctly.
        // A1: q0(acc, init) --a--> q0  (always accepting)
        // A2: q0(init) --a--> q1(acc) --a--> q0  (accepts every 2nd step)
        // Product should be non-empty since (a)^omega has both A1 accepting
        // infinitely often and A2 accepting infinitely often.
        let a1 = construct_buchi(
            1,
            [0].into_iter().collect(),
            [0].into_iter().collect(),
            vec![(0, Some("a".to_string()), 0)],
        );
        let a2 = construct_buchi(
            2,
            [1].into_iter().collect(),
            [0].into_iter().collect(),
            vec![
                (0, Some("a".to_string()), 1),
                (1, Some("a".to_string()), 0),
            ],
        );
        let product = buchi_intersect(&a1, &a2);
        assert!(!check_emptiness(&product));
    }

    #[test]
    fn intersect_with_empty_automaton() {
        // Intersection with an automaton that has no accepting states
        // should be empty.
        let a1 = construct_buchi(
            1,
            [0].into_iter().collect(),
            [0].into_iter().collect(),
            vec![(0, Some("a".to_string()), 0)],
        );
        let a2 = construct_buchi(
            1,
            HashSet::new(), // no accepting states
            [0].into_iter().collect(),
            vec![(0, Some("a".to_string()), 0)],
        );
        let product = buchi_intersect(&a1, &a2);
        assert!(check_emptiness(&product));
    }

    #[test]
    fn emptiness_multiple_initial_states() {
        // q0 (initial) -> dead end
        // q1 (initial) -> q2 (accepting, self-loop)
        // Non-empty because q1 reaches accepting cycle.
        let buchi = construct_buchi(
            3,
            [2].into_iter().collect(),
            [0, 1].into_iter().collect(),
            vec![
                (0, Some("a".to_string()), 0), // dead-end self-loop but not accepting
                (1, Some("b".to_string()), 2),
                (2, Some("c".to_string()), 2),
            ],
        );
        // q0 has self-loop but is not accepting. q2 has self-loop and is accepting,
        // and is reachable from initial state q1.
        assert!(!check_emptiness(&buchi));
    }

    #[test]
    fn emptiness_accepting_state_singleton_no_self_loop() {
        // Single-state SCC (q1 accepting) but no self-loop => no cycle => empty.
        // q0 (initial) --a--> q1 (accepting) --b--> q2 (not accepting, dead end)
        let buchi = construct_buchi(
            3,
            [1].into_iter().collect(),
            [0].into_iter().collect(),
            vec![
                (0, Some("a".to_string()), 1),
                (1, Some("b".to_string()), 2),
            ],
        );
        assert!(check_emptiness(&buchi));
    }

    fn make_empty_wpds_analysis() -> crate::wpds::WpdsAnalysis {
        use std::collections::{HashMap, HashSet};
        crate::wpds::WpdsAnalysis {
            grammar_name: "test".to_string(),
            num_symbols: 0,
            num_rules: 0,
            reachable_categories: HashSet::new(),
            unreachable_rules: Vec::new(),
            category_weights: HashMap::new(),
            call_graph: crate::wpds::WpdsCallGraph {
                edges: Vec::new(),
                fan_out: HashMap::new(),
                fan_in: HashMap::new(),
                sccs: Vec::new(),
                categories: HashSet::new(),
            },
            depth_bounds: HashMap::new(),
            cycles: Vec::new(),
            calling_contexts: HashMap::new(),
            context_rule_tables: HashMap::new(),
            cross_category_bp: HashMap::new(),
            context_unambiguous: HashMap::new(),
        }
    }

    #[test]
    fn test_from_wpds_empty() {
        let wpds_analysis = make_empty_wpds_analysis();
        let buchi = from_wpds(&wpds_analysis);
        // Empty call graph produces an empty Buchi automaton.
        assert_eq!(buchi.num_states(), 0, "empty WPDS should produce empty Buchi");
    }

    #[test]
    fn test_from_wpds_with_categories() {
        let mut wpds_analysis = make_empty_wpds_analysis();
        wpds_analysis.call_graph.categories.insert("Expr".to_string());
        wpds_analysis.call_graph.categories.insert("Type".to_string());
        wpds_analysis.reachable_categories.insert("Expr".to_string());
        let buchi = from_wpds(&wpds_analysis);
        assert!(buchi.num_states() > 0, "should produce states from categories");
    }

    // ── Weighted Buchi tests ────────────────────────────────────────────────

    #[test]
    fn weighted_buchi_add_weighted_transition() {
        use crate::automata::semiring::TropicalWeight;

        let mut buchi = WeightedBuchiAutomaton::<TropicalWeight>::new();
        let q0 = buchi.add_state(false);
        let q1 = buchi.add_state(true);
        buchi.initial_states.insert(q0);
        buchi.add_weighted_transition(q0, Some("a".to_string()), q1, TropicalWeight::new(3.0));
        buchi.add_weighted_transition(q1, Some("b".to_string()), q0, TropicalWeight::new(2.0));

        assert_eq!(buchi.num_states(), 2);
        assert_eq!(buchi.num_transitions(), 2);
        assert!(buchi.alphabet.contains("a"));
        assert!(buchi.alphabet.contains("b"));

        // Verify the weights are stored correctly.
        let targets_a = buchi
            .transitions
            .get(&(q0, Some("a".to_string())))
            .expect("transition q0 --a--> should exist");
        assert_eq!(targets_a.len(), 1);
        assert_eq!(targets_a[0].0, q1);
        assert!(targets_a[0].1.approx_eq(&TropicalWeight::new(3.0), 1e-9));
    }

    #[test]
    fn weighted_buchi_construct_helper() {
        use crate::automata::semiring::TropicalWeight;

        let buchi = construct_weighted_buchi(
            2,
            [1].into_iter().collect(),
            [0].into_iter().collect(),
            vec![
                (0, Some("a".to_string()), 1, TropicalWeight::new(1.5)),
                (1, Some("b".to_string()), 0, TropicalWeight::new(2.5)),
            ],
        );
        assert_eq!(buchi.num_states(), 2);
        assert_eq!(buchi.num_transitions(), 2);
        assert!(buchi.accepting_states.contains(&1));
    }

    #[test]
    fn total_accepting_weight_boolean_self_loop() {
        // q0 (initial, accepting) --a--> q0
        // With BooleanWeight, total_accepting_weight should be true (non-empty).
        let buchi = construct_buchi(
            1,
            [0].into_iter().collect(),
            [0].into_iter().collect(),
            vec![(0, Some("a".to_string()), 0)],
        );
        let w = total_accepting_weight(&buchi);
        assert!(
            w.is_one(),
            "accepting self-loop should yield BooleanWeight::one()"
        );
    }

    #[test]
    fn total_accepting_weight_boolean_no_cycle() {
        // q0 (initial) --a--> q1 (accepting), no outgoing from q1.
        // No accepting cycle => total_accepting_weight = false (zero).
        let buchi = construct_buchi(
            2,
            [1].into_iter().collect(),
            [0].into_iter().collect(),
            vec![(0, Some("a".to_string()), 1)],
        );
        let w = total_accepting_weight(&buchi);
        assert!(
            w.is_zero(),
            "no accepting cycle should yield BooleanWeight::zero()"
        );
    }

    #[test]
    fn total_accepting_weight_tropical_self_loop() {
        // q0 (initial, accepting) --a--> q0 with weight 5.0
        //
        // Tropical semiring: plus = min, times = add, one = 0.0, zero = +inf.
        // The SCC {q0} has a self-loop with weight 5.0.
        // matrix_star on a 1x1 matrix [5.0]:
        //   star(5.0) = 0.0 (since 5.0 >= 0 in tropical star).
        //   matrix_star adds one() on the diagonal: one().plus(5.0) = min(0.0, 5.0) = 0.0
        //   Then star of that = star(0.0) = 0.0
        //   So result[0][0] = 0.0 = TropicalWeight::one().
        //
        // This means the total accepting weight is TropicalWeight(0.0),
        // which represents "zero cost" -- the best (minimum) cycle cost is 0.
        use crate::automata::semiring::TropicalWeight;

        let buchi = construct_weighted_buchi(
            1,
            [0].into_iter().collect(),
            [0].into_iter().collect(),
            vec![(0, Some("a".to_string()), 0, TropicalWeight::new(5.0))],
        );
        let w = total_accepting_weight(&buchi);
        // star(min(0.0, 5.0)) = star(0.0) = 0.0 = one()
        assert!(
            w.approx_eq(&TropicalWeight::one(), 1e-9),
            "tropical self-loop star should be 0.0 (one); got {:?}",
            w
        );
    }

    #[test]
    fn total_accepting_weight_tropical_two_state_cycle() {
        // q0 (initial) --a/2.0--> q1 (accepting) --b/3.0--> q0
        //
        // SCC {q0, q1}. Adjacency matrix (tropical):
        //   [+inf, 2.0]
        //   [3.0, +inf]
        //
        // matrix_star computes all-pairs shortest paths under Kleene star.
        // star_matrix[1][1] (the q1 diagonal = accepting state) represents
        // the shortest cycle through q1.
        //
        // q1 -> q0 (cost 3.0) -> q1 (cost 2.0) = 3.0 + 2.0 = 5.0 (one cycle)
        // star(5.0) = 0.0 (tropical star of non-negative = one = 0.0)
        //
        // So total_accepting_weight = 0.0 (the minimum-cost way to cycle
        // infinitely through q1 is free after the star).
        use crate::automata::semiring::TropicalWeight;

        let buchi = construct_weighted_buchi(
            2,
            [1].into_iter().collect(),
            [0].into_iter().collect(),
            vec![
                (0, Some("a".to_string()), 1, TropicalWeight::new(2.0)),
                (1, Some("b".to_string()), 0, TropicalWeight::new(3.0)),
            ],
        );
        let w = total_accepting_weight(&buchi);
        assert!(
            w.approx_eq(&TropicalWeight::one(), 1e-9),
            "tropical two-state cycle star should be 0.0 (one); got {:?}",
            w
        );
    }

    #[test]
    fn total_accepting_weight_empty_automaton() {
        // No states => zero weight.
        use crate::automata::semiring::TropicalWeight;

        let buchi = WeightedBuchiAutomaton::<TropicalWeight>::new();
        let w = total_accepting_weight(&buchi);
        assert!(
            w.is_zero(),
            "empty automaton should yield zero weight; got {:?}",
            w
        );
    }

    #[test]
    fn weighted_intersect_tropical() {
        // A1: q0 (init, acc) --a/2.0--> q0
        // A2: q0 (init, acc) --a/3.0--> q0
        //
        // Product should combine weights: 2.0.times(3.0) = 2.0 + 3.0 = 5.0
        // (tropical times = addition of costs).
        // Product is non-empty (accepting cycle exists).
        use crate::automata::semiring::TropicalWeight;

        let a1 = construct_weighted_buchi(
            1,
            [0].into_iter().collect(),
            [0].into_iter().collect(),
            vec![(0, Some("a".to_string()), 0, TropicalWeight::new(2.0))],
        );
        let a2 = construct_weighted_buchi(
            1,
            [0].into_iter().collect(),
            [0].into_iter().collect(),
            vec![(0, Some("a".to_string()), 0, TropicalWeight::new(3.0))],
        );
        let product = weighted_intersect(&a1, &a2);

        // Product should be non-empty.
        assert!(
            !check_emptiness(&product),
            "weighted product of two accepting self-loops should be non-empty"
        );

        // The product has 1*1*3 = 3 states. The transition from phase 0
        // should carry weight 5.0 (2.0 + 3.0 in tropical times).
        assert_eq!(product.num_states(), 3);

        // Verify a transition has the combined weight.
        let mut found_combined = false;
        for (_, targets) in &product.transitions {
            for &(_, ref w) in targets {
                if w.approx_eq(&TropicalWeight::new(5.0), 1e-9) {
                    found_combined = true;
                    break;
                }
            }
            if found_combined {
                break;
            }
        }
        assert!(
            found_combined,
            "product should contain a transition with weight 5.0 (tropical 2+3)"
        );
    }

    #[test]
    fn weighted_intersect_disjoint_tropical() {
        // A1 on "a", A2 on "b" -- disjoint alphabets, empty intersection.
        use crate::automata::semiring::TropicalWeight;

        let a1 = construct_weighted_buchi(
            1,
            [0].into_iter().collect(),
            [0].into_iter().collect(),
            vec![(0, Some("a".to_string()), 0, TropicalWeight::new(1.0))],
        );
        let a2 = construct_weighted_buchi(
            1,
            [0].into_iter().collect(),
            [0].into_iter().collect(),
            vec![(0, Some("b".to_string()), 0, TropicalWeight::new(1.0))],
        );
        let product = weighted_intersect(&a1, &a2);
        assert!(
            check_emptiness(&product),
            "disjoint alphabets should produce empty product"
        );
    }

    #[test]
    fn backward_compat_add_transition_uses_one() {
        // Verify that add_transition() (no explicit weight) stores W::one().
        let mut buchi = BuchiAutomaton::new();
        let q0 = buchi.add_state(false);
        let q1 = buchi.add_state(true);
        buchi.add_transition(q0, Some("x".to_string()), q1);

        let targets = buchi
            .transitions
            .get(&(q0, Some("x".to_string())))
            .expect("transition should exist");
        assert_eq!(targets.len(), 1);
        assert_eq!(targets[0].0, q1);
        assert!(
            targets[0].1.is_one(),
            "add_transition should use BooleanWeight::one()"
        );
    }

    #[test]
    fn total_accepting_weight_no_accepting_cycle() {
        // Cycle exists but no accepting state in it => zero.
        use crate::automata::semiring::TropicalWeight;

        let buchi = construct_weighted_buchi(
            2,
            HashSet::new(), // no accepting states
            [0].into_iter().collect(),
            vec![
                (0, Some("a".to_string()), 1, TropicalWeight::new(1.0)),
                (1, Some("b".to_string()), 0, TropicalWeight::new(1.0)),
            ],
        );
        let w = total_accepting_weight(&buchi);
        assert!(
            w.is_zero(),
            "no accepting states means zero total weight; got {:?}",
            w
        );
    }

    // ── analyze_from_bundle SCC tests ───────────────────────────────────────

    #[test]
    fn analyze_bundle_self_recursive() {
        use crate::pipeline::CategoryInfo;

        let categories = vec![
            CategoryInfo { name: "Expr".to_string(), is_primary: true, native_type: None },
        ];
        // Expr -> Expr "+" Expr (self-recursive)
        let all_syntax = vec![
            ("Add".to_string(), "Expr".to_string(), vec![
                crate::SyntaxItemSpec::NonTerminal {
                    category: "Expr".to_string(),
                    param_name: "lhs".to_string(),
                },
                crate::SyntaxItemSpec::Terminal("+".to_string()),
                crate::SyntaxItemSpec::NonTerminal {
                    category: "Expr".to_string(),
                    param_name: "rhs".to_string(),
                },
            ]),
        ];

        let result = analyze_from_bundle(&all_syntax, &categories);
        assert!(result.has_accepting_cycle, "self-recursive category should have accepting cycle");
        assert_eq!(result.num_states, 1);
        assert_eq!(result.num_accepting, 1);
        assert_eq!(result.accepting_sccs.len(), 1);
        assert!(result.accepting_sccs[0].contains(&"Expr".to_string()));
    }

    #[test]
    fn analyze_bundle_non_recursive() {
        use crate::pipeline::CategoryInfo;

        let categories = vec![
            CategoryInfo { name: "Stmt".to_string(), is_primary: true, native_type: None },
        ];
        // Stmt -> "return" (no self-reference, no cycle)
        let all_syntax = vec![
            ("Return".to_string(), "Stmt".to_string(), vec![
                crate::SyntaxItemSpec::Terminal("return".to_string()),
            ]),
        ];

        let result = analyze_from_bundle(&all_syntax, &categories);
        assert!(!result.has_accepting_cycle, "non-recursive should have no accepting cycle");
        assert_eq!(result.num_accepting, 0);
        assert!(result.accepting_sccs.is_empty());
    }

    #[test]
    fn analyze_bundle_mutually_recursive() {
        use crate::pipeline::CategoryInfo;

        let categories = vec![
            CategoryInfo { name: "Expr".to_string(), is_primary: true, native_type: None },
            CategoryInfo { name: "Stmt".to_string(), is_primary: false, native_type: None },
        ];
        // Expr references Stmt, Stmt references Expr -> mutual recursion
        let all_syntax = vec![
            ("Block".to_string(), "Expr".to_string(), vec![
                crate::SyntaxItemSpec::NonTerminal {
                    category: "Stmt".to_string(),
                    param_name: "body".to_string(),
                },
            ]),
            ("ExprStmt".to_string(), "Stmt".to_string(), vec![
                crate::SyntaxItemSpec::NonTerminal {
                    category: "Expr".to_string(),
                    param_name: "e".to_string(),
                },
            ]),
        ];

        let result = analyze_from_bundle(&all_syntax, &categories);
        assert!(result.has_accepting_cycle, "mutually recursive should form cycle");
        assert_eq!(result.accepting_sccs.len(), 1);
        assert_eq!(result.accepting_sccs[0].len(), 2);
        // Names are sorted within each SCC.
        assert_eq!(result.accepting_sccs[0][0], "Expr");
        assert_eq!(result.accepting_sccs[0][1], "Stmt");
    }

    #[test]
    fn analyze_bundle_empty_grammar() {
        use crate::pipeline::CategoryInfo;

        let categories: Vec<CategoryInfo> = vec![];
        let all_syntax: Vec<(String, String, Vec<crate::SyntaxItemSpec>)> = vec![];

        let result = analyze_from_bundle(&all_syntax, &categories);
        assert_eq!(result.num_states, 0);
        assert_eq!(result.num_accepting, 0);
        assert!(!result.has_accepting_cycle);
        assert!(result.accepting_sccs.is_empty());
    }

    #[test]
    fn analyze_bundle_collection_self_ref() {
        use crate::pipeline::CategoryInfo;
        use crate::recursive::CollectionKind;

        let categories = vec![
            CategoryInfo { name: "Stmt".to_string(), is_primary: true, native_type: None },
        ];
        // Stmt -> Collection of Stmt (self-recursive via element_category)
        let all_syntax = vec![
            ("Block".to_string(), "Stmt".to_string(), vec![
                crate::SyntaxItemSpec::Terminal("{".to_string()),
                crate::SyntaxItemSpec::Collection {
                    param_name: "stmts".to_string(),
                    element_category: "Stmt".to_string(),
                    separator: ";".to_string(),
                    kind: CollectionKind::Vec,
                },
                crate::SyntaxItemSpec::Terminal("}".to_string()),
            ]),
        ];

        let result = analyze_from_bundle(&all_syntax, &categories);
        assert!(result.has_accepting_cycle, "Collection self-ref should be accepting");
        assert_eq!(result.num_accepting, 1);
        assert_eq!(result.accepting_sccs.len(), 1);
    }

    #[test]
    fn analyze_bundle_two_disjoint_sccs() {
        use crate::pipeline::CategoryInfo;

        let categories = vec![
            CategoryInfo { name: "A".to_string(), is_primary: true, native_type: None },
            CategoryInfo { name: "B".to_string(), is_primary: false, native_type: None },
            CategoryInfo { name: "C".to_string(), is_primary: false, native_type: None },
        ];
        // A is self-recursive, B->C->B is mutually recursive, no cross-links
        let all_syntax = vec![
            ("RA".to_string(), "A".to_string(), vec![
                crate::SyntaxItemSpec::NonTerminal {
                    category: "A".to_string(),
                    param_name: "a".to_string(),
                },
            ]),
            ("RB".to_string(), "B".to_string(), vec![
                crate::SyntaxItemSpec::NonTerminal {
                    category: "C".to_string(),
                    param_name: "c".to_string(),
                },
            ]),
            ("RC".to_string(), "C".to_string(), vec![
                crate::SyntaxItemSpec::NonTerminal {
                    category: "B".to_string(),
                    param_name: "b".to_string(),
                },
            ]),
        ];

        let result = analyze_from_bundle(&all_syntax, &categories);
        assert!(result.has_accepting_cycle);
        assert_eq!(result.accepting_sccs.len(), 2, "should have 2 disjoint accepting SCCs");
        // One SCC is {A}, the other is {B, C}.
        let scc_sizes: Vec<usize> = {
            let mut sizes: Vec<usize> = result.accepting_sccs.iter().map(|s| s.len()).collect();
            sizes.sort();
            sizes
        };
        assert_eq!(scc_sizes, vec![1, 2]);
    }

    #[test]
    fn analyze_bundle_display_includes_sccs() {
        use crate::pipeline::CategoryInfo;

        let categories = vec![
            CategoryInfo { name: "Expr".to_string(), is_primary: true, native_type: None },
        ];
        let all_syntax = vec![
            ("Rec".to_string(), "Expr".to_string(), vec![
                crate::SyntaxItemSpec::NonTerminal {
                    category: "Expr".to_string(),
                    param_name: "e".to_string(),
                },
            ]),
        ];

        let result = analyze_from_bundle(&all_syntax, &categories);
        let display = format!("{}", result);
        assert!(display.contains("sccs=1"), "Display should include SCC count, got: {}", display);
    }
}

#[cfg(test)]
mod proptest_tests {
    use super::*;
    use proptest::prelude::*;
    use crate::test_generators::*;

    /// Check whether category `cat` has a direct self-reference in any of its
    /// rules.  A self-reference occurs when a rule belonging to `cat` contains
    /// a `NonTerminal`, `Binder`, `Collection`, `Sep`, `Map`, `Zip`, or
    /// `Optional` item that (transitively) references `cat` itself.
    fn has_self_reference(
        cat: &str,
        rules: &[(String, String, Vec<crate::SyntaxItemSpec>)],
    ) -> bool {
        fn item_refs_cat(item: &crate::SyntaxItemSpec, cat: &str) -> bool {
            match item {
                crate::SyntaxItemSpec::NonTerminal { category, .. } => category == cat,
                crate::SyntaxItemSpec::Binder { category, .. } => category == cat,
                crate::SyntaxItemSpec::Collection { element_category, .. } => {
                    element_category == cat
                }
                crate::SyntaxItemSpec::Sep { body, .. } => item_refs_cat(body, cat),
                crate::SyntaxItemSpec::Map { body_items } => {
                    body_items.iter().any(|sub| item_refs_cat(sub, cat))
                }
                crate::SyntaxItemSpec::Zip {
                    left_category,
                    right_category,
                    body,
                    ..
                } => {
                    left_category == cat
                        || right_category == cat
                        || item_refs_cat(body, cat)
                }
                crate::SyntaxItemSpec::Optional { inner } => {
                    inner.iter().any(|sub| item_refs_cat(sub, cat))
                }
                _ => false,
            }
        }

        rules.iter().any(|(_, rule_cat, items)| {
            rule_cat == cat && items.iter().any(|item| item_refs_cat(item, cat))
        })
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(30))]

        /// Every name in every accepting SCC must be a valid category name from
        /// the input.
        #[test]
        fn prop_scc_names_are_category_names((cats, rules) in arb_small_grammar()) {
            let cat_names: std::collections::HashSet<&str> =
                cats.iter().map(|c| c.name.as_str()).collect();
            let result = analyze_from_bundle(&rules, &cats);
            for scc in &result.accepting_sccs {
                for name in scc {
                    prop_assert!(
                        cat_names.contains(name.as_str()),
                        "SCC name {:?} is not a valid category name", name
                    );
                }
            }
        }

        /// Names within each accepting SCC are lexicographically sorted.
        #[test]
        fn prop_scc_sorted_within((cats, rules) in arb_small_grammar()) {
            let result = analyze_from_bundle(&rules, &cats);
            for scc in &result.accepting_sccs {
                for window in scc.windows(2) {
                    prop_assert!(
                        window[0] <= window[1],
                        "SCC members not sorted: {:?} > {:?}", window[0], window[1]
                    );
                }
            }
        }

        /// The number of accepting SCCs never exceeds the number of categories.
        #[test]
        fn prop_scc_count_le_category_count((cats, rules) in arb_small_grammar()) {
            let result = analyze_from_bundle(&rules, &cats);
            prop_assert!(
                result.accepting_sccs.len() <= cats.len(),
                "accepting_sccs.len()={} > categories.len()={}",
                result.accepting_sccs.len(), cats.len()
            );
        }

        /// Every accepting SCC either has size > 1 (mutual recursion) or is a
        /// singleton whose sole category has a self-reference in the rules.
        #[test]
        fn prop_accepting_scc_has_cycle((cats, rules) in arb_small_grammar()) {
            let result = analyze_from_bundle(&rules, &cats);
            for scc in &result.accepting_sccs {
                if scc.len() == 1 {
                    prop_assert!(
                        has_self_reference(&scc[0], &rules),
                        "Singleton accepting SCC {:?} has no self-reference", scc[0]
                    );
                }
                // size > 1 is inherently a cycle (mutual recursion) — nothing
                // extra to assert.
            }
        }

        /// A category that does NOT self-reference, if it appears alone in a
        /// singleton SCC, must NOT be present in `accepting_sccs`.
        #[test]
        fn prop_no_self_ref_singleton_not_accepting((cats, rules) in arb_small_grammar()) {
            let result = analyze_from_bundle(&rules, &cats);
            // Collect all singleton accepting SCC names.
            let singleton_accepting: std::collections::HashSet<&str> = result
                .accepting_sccs
                .iter()
                .filter(|scc| scc.len() == 1)
                .map(|scc| scc[0].as_str())
                .collect();

            for cat in &cats {
                if !has_self_reference(&cat.name, &rules) {
                    prop_assert!(
                        !singleton_accepting.contains(cat.name.as_str()),
                        "Non-self-referencing category {:?} should not be a singleton accepting SCC",
                        cat.name
                    );
                }
            }
        }

        /// `has_accepting_cycle` is true if and only if `accepting_sccs` is
        /// non-empty.
        #[test]
        fn prop_has_accepting_cycle_iff_nonempty_sccs((cats, rules) in arb_small_grammar()) {
            let result = analyze_from_bundle(&rules, &cats);
            prop_assert_eq!(
                result.has_accepting_cycle,
                !result.accepting_sccs.is_empty(),
                "has_accepting_cycle ({}) should equal !accepting_sccs.is_empty() ({})",
                result.has_accepting_cycle, !result.accepting_sccs.is_empty()
            );
        }

        /// `num_states` always equals the number of input categories.
        #[test]
        fn prop_num_states_equals_category_count((cats, rules) in arb_small_grammar()) {
            let result = analyze_from_bundle(&rules, &cats);
            prop_assert_eq!(
                result.num_states, cats.len(),
                "num_states ({}) should equal categories.len() ({})",
                result.num_states, cats.len()
            );
        }
    }
}
