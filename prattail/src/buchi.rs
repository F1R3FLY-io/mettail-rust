//! Buchi automata for infinite-word (omega-regular) acceptance.
//!
//! Buchi automata extend finite automata to infinite words. A run is accepting
//! if it visits at least one accepting state infinitely often. Buchi automata
//! recognize exactly the omega-regular languages, making them the standard
//! formalism for liveness and fairness properties in model checking.
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
//! BuchiAutomaton
//!       │
//!       ├──→ intersect() (product with system automaton)
//!       │         │
//!       │         ▼
//!       │    check_emptiness() ──→ true/false (property satisfied/violated)
//!       │
//!       └──→ complement() (for inclusion checking, exponential blowup)
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

// NOTE: Semiring import will be used when weighted Buchi analysis is implemented.
#[allow(unused_imports)]
use crate::automata::semiring::Semiring;

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

/// A nondeterministic Buchi automaton (NBA).
///
/// The NBA `A = (Q, Σ, δ, Q₀, F)` where:
/// - `Q` is the finite set of states
/// - `Σ` is the input alphabet
/// - `δ: Q × Σ → 2^Q` is the nondeterministic transition function
/// - `Q₀ ⊆ Q` are initial states
/// - `F ⊆ Q` are accepting states
///
/// A run `ρ` on an infinite word `w = a₀a₁a₂...` is accepting iff
/// `inf(ρ) ∩ F ≠ ∅` (the run visits some accepting state infinitely often).
#[derive(Debug, Clone)]
pub struct BuchiAutomaton {
    /// All states in the automaton.
    pub states: Vec<BuchiState>,
    /// Alphabet symbols.
    pub alphabet: HashSet<String>,
    /// Transitions, indexed by (source_state, label).
    pub transitions: HashMap<(usize, Option<String>), Vec<usize>>,
    /// Initial state IDs.
    pub initial_states: HashSet<usize>,
    /// Accepting state IDs (redundant with `BuchiState::is_accepting` for fast lookup).
    pub accepting_states: HashSet<usize>,
}

impl BuchiAutomaton {
    /// Create an empty Buchi automaton.
    pub fn new() -> Self {
        BuchiAutomaton {
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

    /// Add a transition.
    pub fn add_transition(&mut self, from: usize, label: Option<String>, to: usize) {
        if let Some(ref l) = label {
            self.alphabet.insert(l.clone());
        }
        self.transitions
            .entry((from, label))
            .or_insert_with(Vec::new)
            .push(to);
    }

    /// Number of states.
    pub fn num_states(&self) -> usize {
        self.states.len()
    }

    /// Number of transitions.
    pub fn num_transitions(&self) -> usize {
        self.transitions.values().map(|v| v.len()).sum()
    }
}

impl Default for BuchiAutomaton {
    fn default() -> Self {
        Self::new()
    }
}

impl fmt::Display for BuchiAutomaton {
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
/// constructs the automaton data structure.
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

/// Intersect two Buchi automata via the product construction.
///
/// The product automaton `A × B` accepts `L(A) ∩ L(B)`. Uses the standard
/// 3-counter construction to handle the Buchi acceptance condition correctly:
/// the product tracks which automaton's accepting states have been visited
/// since the last "reset."
///
/// # Arguments
///
/// * `a` - First Buchi automaton.
/// * `b` - Second Buchi automaton.
///
/// # Returns
///
/// A Buchi automaton accepting `L(A) ∩ L(B)`.
pub fn buchi_intersect(a: &BuchiAutomaton, b: &BuchiAutomaton) -> BuchiAutomaton {
    // 3-counter product construction for Buchi acceptance.
    //
    // Product state = (q1, q2, phase) where phase in {0, 1, 2}.
    //   Phase 0: waiting for A1 to accept (scanning for q1 in F1).
    //   Phase 1: A1 accepted, now waiting for A2 to accept (scanning for q2 in F2).
    //   Phase 2: both have accepted — this is the accepting phase; reset to 0.
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
    let mut result = BuchiAutomaton::new();

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
        // We need matching transitions in B on the same label.
        let label_key = (0usize, label_a.clone()); // dummy — we iterate B's transitions
        let _ = label_key;

        // Only proceed if this label is in the shared alphabet.
        if !shared_alphabet.contains(label_a) {
            continue;
        }

        for q2_from in 0..n_b {
            let b_targets = match b.transitions.get(&(q2_from, label_a.clone())) {
                Some(t) => t,
                None => continue,
            };

            for &q1_to in targets_a {
                for &q2_to in b_targets {
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
                        result.add_transition(from_id, label_a.clone(), to_id);
                    }
                }
            }
        }
    }

    result
}

/// Check emptiness of a Buchi automaton.
///
/// A Buchi automaton is non-empty iff there exists a reachable accepting state
/// that lies on a cycle (i.e., an accepting state reachable from itself). This
/// reduces to finding an accepting SCC reachable from an initial state.
///
/// Uses a nested DFS (Schwoon-Somenzi algorithm) or Tarjan SCC decomposition.
///
/// # Arguments
///
/// * `buchi` - The Buchi automaton to check.
///
/// # Returns
///
/// `true` if `L(buchi) = ∅`, `false` otherwise.
pub fn check_emptiness(buchi: &BuchiAutomaton) -> bool {
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
                    for &target in targets {
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
        for &to in targets {
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
                    // Root of an SCC — pop the SCC from the stack.
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
    // states don't reach everything in the reachable set — shouldn't
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
// Pipeline bridge
// ══════════════════════════════════════════════════════════════════════════════

/// Pipeline bridge: convert WPDS call graph into a Buchi automaton.
///
/// Each category becomes a state; call-graph edges become transitions.
/// Primary categories (those with zero fan-in — root entry points that are
/// never called by other categories) are accepting states.
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
    // A category is "primary" (accepting) if it has zero fan-in — it is a
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
        // An accepting state with a self-loop — non-empty.
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
        // Accepting state reachable but not on a cycle — empty language.
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
        // Cycle exists but contains no accepting state — empty.
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
        // A1: q0 --a--> q0 (accepting, initial) — accepts (a)^omega
        // A2: q0 --a--> q0 (accepting, initial) — same
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
        // No common word — intersection should be empty.
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
        // A1: q0 --a--> q1(acc) --b--> q0, initial={q0}  — accepts (ab)^omega
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
}
