//! Weighted alternating automata with polynomial transition functions.
//!
//! Alternating automata extend nondeterministic automata by allowing transitions
//! to specify both existential (disjunctive) and universal (conjunctive) branching.
//! A transition can require that **all** successor states accept (universal) or
//! that **some** successor state accepts (existential). This duality makes
//! alternating automata exponentially more succinct than NFAs for certain languages
//! and provides a natural model for game semantics and CTL model checking.
//!
//! ## Weighted Extension
//!
//! This module generalizes the unweighted alternating automaton to weighted
//! alternating automata over an arbitrary semiring `W`. The key insight from
//! Kostolányi & Mišún (2018, Def. 4.1) is that transitions carry polynomial
//! transition functions over state variables. In the two-mode equivalent
//! formulation (Definition 5.1, Theorem 5.17), states are partitioned into
//! `Q⊕` (sum/existential) and `Q⊗` (product/universal), which maps directly
//! to the existing [`BranchingMode`]:
//!
//! - **Existential (Q⊕)**: the run's weight is the semiring **plus** (⊕) over
//!   successor weights — selecting the best alternative.
//! - **Universal (Q⊗)**: the run's weight is the semiring **times** (⊗) over
//!   successor weights — accumulating costs along all branches.
//!
//! For `BooleanWeight`, this recovers the classical unweighted semantics:
//! `plus = OR` (existential) and `times = AND` (universal).
//!
//! ## Backward Compatibility
//!
//! The unweighted `AlternatingAutomaton` is a type alias for
//! `WeightedAlternatingAutomaton<BooleanWeight>`, and `AlternatingTransition`
//! is a type alias for `WeightedAlternatingTransition<BooleanWeight>`. All
//! existing APIs (`new`, `add_state`, `add_transition`, `check_emptiness`,
//! `bisimulation_game`, `analyze_from_bundle`) continue to work unchanged.
//!
//! ## Theoretical Foundations
//!
//! - **Chandra, Kozen & Stockmeyer (1981)** — "Alternation." Introduces
//!   alternating Turing machines and automata; proves that alternation adds
//!   exactly one level of the polynomial hierarchy.
//! - **Muller & Schupp (1987)** — "Alternating automata on infinite trees."
//!   Extends alternation to tree automata for mu-calculus model checking.
//! - **Kupferman & Vardi (2001)** — "Weak alternating automata are not that
//!   weak." Shows efficient translation of LTL to weak alternating automata
//!   and from there to Buchi automata.
//! - **Jurdzinski (2000)** — "Small progress measures for solving parity games."
//!   Connects alternating parity automata emptiness to parity game solving.
//! - **Kostolányi & Mišún (2018)** — "Weighted alternating automata with
//!   polynomial transition functions." Defines polynomial transition functions
//!   over semirings and proves the two-mode equivalence theorem.
//!
//! ## Architecture
//!
//! ```text
//! CTL/mu-calculus formula
//!       │
//!       ▼
//! construct_alternating()
//!       │
//!       ▼
//! WeightedAlternatingAutomaton<W>
//!       │
//!       ├──→ check_emptiness()          (Boolean: parity game reduction)
//!       ├──→ weighted_emptiness()       (general: monotone fixpoint)
//!       ├──→ evaluate_polynomial()      (bottom-up word evaluation)
//!       │
//!       └──→ bisimulation_game()        (language equivalence via games)
//! ```
//!
//! ## PraTTaIL Integration
//!
//! Alternating automata model branching properties of PraTTaIL parse trees.
//! Universal transitions capture "all branches must satisfy" constraints
//! (e.g., type checking all arguments of a function application), while
//! existential transitions capture "some branch suffices" (e.g., ambiguity
//! resolution where any valid parse is acceptable).

use std::collections::{HashMap, HashSet, VecDeque};
use std::fmt;

use crate::automata::semiring::{BooleanWeight, Semiring};

// ══════════════════════════════════════════════════════════════════════════════
// Core types
// ══════════════════════════════════════════════════════════════════════════════

/// A state in an alternating automaton.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct AlternatingState {
    /// Unique state identifier.
    pub id: usize,
    /// Whether this state uses universal (conjunctive) or existential
    /// (disjunctive) branching.
    pub branching: BranchingMode,
    /// Priority for parity acceptance (0 = most accepting).
    /// Even priorities are accepting; odd priorities are rejecting.
    pub priority: u32,
    /// Optional label for diagnostics.
    pub label: Option<String>,
}

/// Branching mode of a state in an alternating automaton.
///
/// In the two-mode polynomial formulation (Kostolányi & Mišún 2018,
/// Definition 5.1), states are partitioned into Q⊕ and Q⊗:
/// - `Existential` = Q⊕: transitions are combined with semiring **plus** (⊕)
/// - `Universal` = Q⊗: transitions are combined with semiring **times** (⊗)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BranchingMode {
    /// Existential (disjunctive): at least one successor run must accept.
    /// In weighted mode: successor weights are combined with ⊕ (plus).
    Existential,
    /// Universal (conjunctive): all successor runs must accept.
    /// In weighted mode: successor weights are combined with ⊗ (times).
    Universal,
}

impl AlternatingState {
    /// Create a new existential state with priority 0.
    pub fn existential(id: usize) -> Self {
        AlternatingState {
            id,
            branching: BranchingMode::Existential,
            priority: 0,
            label: None,
        }
    }

    /// Create a new universal state with priority 0.
    pub fn universal(id: usize) -> Self {
        AlternatingState {
            id,
            branching: BranchingMode::Universal,
            priority: 0,
            label: None,
        }
    }

    /// Create a state with explicit branching mode and priority.
    pub fn with_priority(id: usize, branching: BranchingMode, priority: u32) -> Self {
        AlternatingState {
            id,
            branching,
            priority,
            label: None,
        }
    }

    /// Create a labeled state.
    pub fn labeled(
        id: usize,
        branching: BranchingMode,
        priority: u32,
        label: impl Into<String>,
    ) -> Self {
        AlternatingState {
            id,
            branching,
            priority,
            label: Some(label.into()),
        }
    }
}

impl fmt::Display for AlternatingState {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mode = match self.branching {
            BranchingMode::Existential => "E",
            BranchingMode::Universal => "A",
        };
        if let Some(ref label) = self.label {
            write!(f, "q{}[{},p={}]({})", self.id, mode, self.priority, label)
        } else {
            write!(f, "q{}[{},p={}]", self.id, mode, self.priority)
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Weighted transition types
// ══════════════════════════════════════════════════════════════════════════════

/// A weighted transition in an alternating automaton.
///
/// The transition from state `from` on input symbol `label` goes to a set of
/// successor states with an associated semiring weight. The interpretation
/// depends on the branching mode of the source state:
/// - **Existential (Q⊕)**: multiple transitions from the same state are
///   combined with semiring plus (⊕). This selects the best alternative.
/// - **Universal (Q⊗)**: successor weights within a single transition are
///   combined with semiring times (⊗). This accumulates costs across branches.
///
/// For `BooleanWeight`, this recovers the classical unweighted semantics:
/// `plus = OR`, `times = AND`.
#[derive(Debug, Clone)]
pub struct WeightedAlternatingTransition<W: Semiring> {
    /// Source state ID.
    pub from: usize,
    /// Input symbol label (`None` for epsilon).
    pub label: Option<String>,
    /// Set of successor state IDs.
    pub successors: Vec<usize>,
    /// Semiring weight for this transition.
    pub weight: W,
}

/// Unweighted alternating transition (backward-compatible alias).
///
/// `AlternatingTransition` is a `WeightedAlternatingTransition<BooleanWeight>`,
/// preserving full backward compatibility with the original unweighted API.
pub type AlternatingTransition = WeightedAlternatingTransition<BooleanWeight>;

impl<W: Semiring> fmt::Display for WeightedAlternatingTransition<W> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let label = self.label.as_deref().unwrap_or("epsilon");
        let succs: Vec<String> = self.successors.iter().map(|s| format!("q{}", s)).collect();
        if self.weight.is_one() {
            write!(f, "q{} --{}-> {{{}}}", self.from, label, succs.join(", "))
        } else {
            write!(
                f,
                "q{} --{}/{:?}-> {{{}}}",
                self.from,
                label,
                self.weight,
                succs.join(", ")
            )
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Polynomial transition function (Kostolányi & Mišún 2018, Def. 4.1)
// ══════════════════════════════════════════════════════════════════════════════

/// A polynomial transition function over semiring `W`.
///
/// Each monomial is a pair `(coefficient, variables)` where `variables` is
/// a list of `(state_index, exponent)` pairs. The polynomial value is:
///
/// ```text
/// δ(q, a) = Σ_i  c_i · Π_j  x_{s_j}^{e_j}
/// ```
///
/// where `c_i` is the coefficient (weight) and `x_{s_j}` is the state variable
/// for state `s_j` raised to exponent `e_j`.
///
/// In the two-mode equivalent formulation, this polynomial is evaluated
/// according to the branching mode of the source state:
/// - **Existential**: the sum (⊕) over monomials selects the best alternative
/// - **Universal**: the product (⊗) within each monomial sequences all branches
#[derive(Debug, Clone)]
pub struct PolynomialTransition<W: Semiring> {
    /// Source state ID.
    pub from: usize,
    /// Input symbol label (`None` for epsilon).
    pub label: Option<String>,
    /// Monomials: each is `(coefficient, Vec<(state_idx, exponent)>)`.
    pub monomials: Vec<(W, Vec<(usize, u32)>)>,
}

// ══════════════════════════════════════════════════════════════════════════════
// Weighted alternating automaton
// ══════════════════════════════════════════════════════════════════════════════

/// A weighted alternating automaton with parity acceptance condition.
///
/// `A = (Q, Σ, δ, q₀, Ω, τ)` where:
/// - `Q = Q⊕ ∪ Q⊗` (existential/sum and universal/product states)
/// - `Σ` is the input alphabet
/// - `δ: Q × Σ → transitions with weights from semiring W`
/// - `q₀` is the initial state
/// - `Ω: Q → N` is the priority function (parity acceptance)
/// - `τ: Q → W` maps terminal states to their acceptance weights
///
/// A run is accepting iff the minimum priority seen infinitely often is even.
/// For weighted runs, the total weight is computed bottom-up using the
/// branching mode: ⊕ for existential states, ⊗ for universal states.
#[derive(Debug, Clone)]
pub struct WeightedAlternatingAutomaton<W: Semiring> {
    /// All states.
    pub states: Vec<AlternatingState>,
    /// Input alphabet.
    pub alphabet: HashSet<String>,
    /// Transitions with semiring weights.
    pub transitions: Vec<WeightedAlternatingTransition<W>>,
    /// Initial state ID.
    pub initial_state: Option<usize>,
    /// Terminal (acceptance) weights: maps state ID to its terminal weight.
    ///
    /// A state not present in this map has terminal weight `W::zero()` (i.e.,
    /// it cannot terminate a run). For `BooleanWeight`, this encodes the
    /// classical accepting/rejecting distinction: `true` = accepting leaf,
    /// `false` = rejecting leaf.
    ///
    /// For backward compatibility, when using `BooleanWeight` the terminal
    /// weights are derived from parity priorities: even priority = `one()`
    /// (accepting), odd priority = `zero()` (rejecting).
    pub terminal_weights: HashMap<usize, W>,
}

/// Unweighted alternating automaton (backward-compatible alias).
///
/// `AlternatingAutomaton` is `WeightedAlternatingAutomaton<BooleanWeight>`,
/// preserving full backward compatibility. All existing construction,
/// emptiness checking, and bisimulation APIs work unchanged.
pub type AlternatingAutomaton = WeightedAlternatingAutomaton<BooleanWeight>;

impl<W: Semiring> WeightedAlternatingAutomaton<W> {
    /// Create an empty weighted alternating automaton.
    pub fn new() -> Self {
        WeightedAlternatingAutomaton {
            states: Vec::new(),
            alphabet: HashSet::new(),
            transitions: Vec::new(),
            initial_state: None,
            terminal_weights: HashMap::new(),
        }
    }

    /// Add a state and return its ID.
    pub fn add_state(&mut self, branching: BranchingMode, priority: u32) -> usize {
        let id = self.states.len();
        self.states
            .push(AlternatingState::with_priority(id, branching, priority));
        id
    }

    /// Add a weighted transition.
    ///
    /// For the unweighted `AlternatingAutomaton` alias, use [`add_transition`]
    /// instead, which automatically assigns `BooleanWeight::one()`.
    pub fn add_weighted_transition(
        &mut self,
        from: usize,
        label: Option<String>,
        successors: Vec<usize>,
        weight: W,
    ) {
        if let Some(ref l) = label {
            self.alphabet.insert(l.clone());
        }
        self.transitions.push(WeightedAlternatingTransition {
            from,
            label,
            successors,
            weight,
        });
    }

    /// Set the terminal weight for a state.
    ///
    /// A state with terminal weight `W::one()` is a fully accepting leaf.
    /// A state with terminal weight `W::zero()` cannot terminate a run.
    /// Intermediate weights encode partial acceptance costs.
    pub fn set_terminal_weight(&mut self, state: usize, weight: W) {
        if weight.is_zero() {
            self.terminal_weights.remove(&state);
        } else {
            self.terminal_weights.insert(state, weight);
        }
    }

    /// Number of states.
    pub fn num_states(&self) -> usize {
        self.states.len()
    }

    /// Number of transitions.
    pub fn num_transitions(&self) -> usize {
        self.transitions.len()
    }

    /// Maximum priority across all states.
    pub fn max_priority(&self) -> u32 {
        self.states.iter().map(|s| s.priority).max().unwrap_or(0)
    }
}

// Backward-compatible `add_transition` for `AlternatingAutomaton` (BooleanWeight).
impl WeightedAlternatingAutomaton<BooleanWeight> {
    /// Add an unweighted transition (weight = `BooleanWeight::one()`).
    ///
    /// This is the original API preserved for backward compatibility.
    pub fn add_transition(
        &mut self,
        from: usize,
        label: Option<String>,
        successors: Vec<usize>,
    ) {
        self.add_weighted_transition(from, label, successors, BooleanWeight::one());
    }
}

impl<W: Semiring> Default for WeightedAlternatingAutomaton<W> {
    fn default() -> Self {
        Self::new()
    }
}

impl<W: Semiring> fmt::Display for WeightedAlternatingAutomaton<W> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "WeightedAlternatingAutomaton {{ states: {}, transitions: {}, max_priority: {} }}",
            self.num_states(),
            self.num_transitions(),
            self.max_priority(),
        )
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Core functions — unweighted (Boolean) emptiness and bisimulation
// ══════════════════════════════════════════════════════════════════════════════

/// Check emptiness of an alternating parity automaton.
///
/// Reduces to solving a parity game: Player 0 (existential) controls
/// existential states, Player 1 (universal) controls universal states.
/// The automaton is non-empty iff Player 0 has a winning strategy from
/// the initial state.
///
/// Uses a bottom-up fixpoint approach for finite-word semantics:
///   1. States with even priority and no outgoing transitions are accepting leaves.
///   2. Existential states accept if **any** transition leads to all-accepting successors.
///   3. Universal states accept if **all** transitions lead to all-accepting successors.
///
/// # Arguments
///
/// * `automaton` - The alternating automaton to check.
///
/// # Returns
///
/// `true` if `L(automaton) = empty`, `false` otherwise.
pub fn check_emptiness(automaton: &AlternatingAutomaton) -> bool {
    let n = automaton.num_states();
    if n == 0 || automaton.initial_state.is_none() {
        return true; // empty: no states or no initial state
    }

    let initial = automaton
        .initial_state
        .expect("initial_state checked above");
    if initial >= n {
        return true; // invalid initial state
    }

    // Build adjacency: for each state, collect all transitions (each is a set of successors).
    let mut transitions_from: Vec<Vec<&Vec<usize>>> = vec![Vec::new(); n];
    for t in &automaton.transitions {
        if t.from < n {
            transitions_from[t.from].push(&t.successors);
        }
    }

    // `accepting[s]` = true means state s can produce an accepting run subtree.
    let mut accepting = vec![false; n];

    // Initialize: states with no outgoing transitions.
    // Even priority => accepting leaf; odd priority => rejecting leaf.
    for s in 0..n {
        if transitions_from[s].is_empty() {
            accepting[s] = automaton.states[s].priority % 2 == 0;
        }
    }

    // Fixpoint iteration: propagate accepting status backward.
    // We iterate until no changes occur.
    let mut changed = true;
    while changed {
        changed = false;
        for s in 0..n {
            if accepting[s] {
                continue; // already accepting
            }
            if transitions_from[s].is_empty() {
                continue; // leaf, already handled
            }

            let new_status = match automaton.states[s].branching {
                BranchingMode::Existential => {
                    // At least one transition must lead to all-accepting successors.
                    transitions_from[s]
                        .iter()
                        .any(|succs| succs.iter().all(|&succ| succ < n && accepting[succ]))
                }
                BranchingMode::Universal => {
                    // ALL transitions must lead to all-accepting successors.
                    transitions_from[s]
                        .iter()
                        .all(|succs| succs.iter().all(|&succ| succ < n && accepting[succ]))
                }
            };

            if new_status && !accepting[s] {
                accepting[s] = true;
                changed = true;
            }
        }
    }

    // The language is empty iff the initial state is NOT accepting.
    !accepting[initial]
}

/// Play a bisimulation game between two alternating automata.
///
/// Determines whether the two automata are language-equivalent by
/// constructing and solving a bisimulation game. This is decidable for
/// alternating automata over finite words and for weak alternating automata
/// over infinite words.
///
/// # Arguments
///
/// * `a` - First alternating automaton.
/// * `b` - Second alternating automaton.
///
/// # Returns
///
/// `true` if the two automata are bisimilar (and hence language-equivalent
/// for the appropriate class), `false` otherwise.
pub fn bisimulation_game(a: &AlternatingAutomaton, b: &AlternatingAutomaton) -> bool {
    let na = a.num_states();
    let nb = b.num_states();

    // Handle degenerate cases.
    match (a.initial_state, b.initial_state) {
        (None, None) => return true, // both empty => bisimilar
        (None, Some(_)) | (Some(_), None) => {
            // One has an initial state and the other doesn't.
            // They are bisimilar only if both have empty languages.
            // If one has no initial state, its language is empty.
            // Check if the other's language is also empty.
            if a.initial_state.is_none() {
                return check_emptiness(b);
            } else {
                return check_emptiness(a);
            }
        }
        (Some(_), Some(_)) => {} // both have initial states, proceed
    }

    let init_a = a.initial_state.expect("checked above");
    let init_b = b.initial_state.expect("checked above");

    if init_a >= na || init_b >= nb {
        return true; // invalid initial states treated as empty
    }

    // Build transition maps: state -> [(label, successors)].
    let mut trans_a: HashMap<usize, Vec<(Option<&str>, &Vec<usize>)>> = HashMap::new();
    for t in &a.transitions {
        trans_a
            .entry(t.from)
            .or_default()
            .push((t.label.as_deref(), &t.successors));
    }

    let mut trans_b: HashMap<usize, Vec<(Option<&str>, &Vec<usize>)>> = HashMap::new();
    for t in &b.transitions {
        trans_b
            .entry(t.from)
            .or_default()
            .push((t.label.as_deref(), &t.successors));
    }

    // Game positions: (state_in_a, state_in_b).
    // Encoding: position index = pa * nb + pb.
    let num_positions = na * nb;
    let pos = |pa: usize, pb: usize| -> usize { pa * nb + pb };

    // attacker_wins[pos] = true means Attacker wins from this position.
    let mut attacker_wins = vec![false; num_positions];

    // Initial pass: find positions where one side has a transition on a label
    // that the other side cannot match at all.
    let mut worklist: VecDeque<usize> = VecDeque::new();

    for pa in 0..na {
        let a_transitions = trans_a.get(&pa);
        let a_labels: HashSet<Option<&str>> = a_transitions
            .map(|ts| ts.iter().map(|(l, _)| *l).collect())
            .unwrap_or_default();

        for pb in 0..nb {
            let b_transitions = trans_b.get(&pb);
            let b_labels: HashSet<Option<&str>> = b_transitions
                .map(|ts| ts.iter().map(|(l, _)| *l).collect())
                .unwrap_or_default();

            let p = pos(pa, pb);

            // Attacker wins if A has a label B doesn't, or vice versa.
            let a_unmatched = a_labels.iter().any(|l| !b_labels.contains(l));
            let b_unmatched = b_labels.iter().any(|l| !a_labels.contains(l));

            if a_unmatched || b_unmatched {
                attacker_wins[p] = true;
                worklist.push_back(p);
            }
        }
    }

    // Backward propagation (attractor computation).
    let mut changed = true;
    while changed {
        changed = false;
        for pa in 0..na {
            for pb in 0..nb {
                let p = pos(pa, pb);
                if attacker_wins[p] {
                    continue;
                }

                let a_transitions = trans_a.get(&pa);
                let b_transitions = trans_b.get(&pb);

                // Check if Attacker can win by picking a transition from A.
                if let Some(a_trans) = a_transitions {
                    for &(label, succs_a) in a_trans {
                        // Find matching transitions in B.
                        let b_matches: Vec<&Vec<usize>> = b_transitions
                            .map(|ts| {
                                ts.iter()
                                    .filter(|(l, _)| *l == label)
                                    .map(|(_, s)| *s)
                                    .collect::<Vec<_>>()
                            })
                            .unwrap_or_default();

                        if b_matches.is_empty() {
                            attacker_wins[p] = true;
                            changed = true;
                            break;
                        }

                        let attacker_wins_this_label = b_matches.iter().all(|succs_b| {
                            succs_a.iter().any(|&sa| {
                                succs_b.iter().any(|&sb| {
                                    sa < na && sb < nb && attacker_wins[pos(sa, sb)]
                                })
                            })
                        });

                        if attacker_wins_this_label {
                            attacker_wins[p] = true;
                            changed = true;
                            break;
                        }
                    }
                }

                if attacker_wins[p] {
                    continue;
                }

                // Check if Attacker can win by picking a transition from B.
                if let Some(b_trans) = b_transitions {
                    for &(label, succs_b) in b_trans {
                        let a_matches: Vec<&Vec<usize>> = a_transitions
                            .map(|ts| {
                                ts.iter()
                                    .filter(|(l, _)| *l == label)
                                    .map(|(_, s)| *s)
                                    .collect::<Vec<_>>()
                            })
                            .unwrap_or_default();

                        if a_matches.is_empty() {
                            attacker_wins[p] = true;
                            changed = true;
                            break;
                        }

                        let attacker_wins_this_label = a_matches.iter().all(|succs_a| {
                            succs_b.iter().any(|&sb| {
                                succs_a.iter().any(|&sa| {
                                    sa < na && sb < nb && attacker_wins[pos(sa, sb)]
                                })
                            })
                        });

                        if attacker_wins_this_label {
                            attacker_wins[p] = true;
                            changed = true;
                            break;
                        }
                    }
                }
            }
        }
    }

    // Bisimulation holds iff the initial position is NOT an Attacker win.
    !attacker_wins[pos(init_a, init_b)]
}

// ══════════════════════════════════════════════════════════════════════════════
// Weighted operations
// ══════════════════════════════════════════════════════════════════════════════

/// Compute the total language weight of a weighted alternating automaton.
///
/// Uses a monotone fixpoint iteration over the semiring. Each state `s` is
/// assigned a weight `w[s]` that converges to the total weight of all
/// accepting runs from that state:
///
/// - **Leaf states** (no outgoing transitions): `w[s] = terminal_weights[s]`
///   (defaults to `W::zero()` if absent)
/// - **Existential states**: `w[s] = ⊕_t (t.weight ⊗ ⊗_{s' ∈ t.successors} w[s'])`
///   — the semiring sum over all transitions, each weighted by its transition
///   weight times the product of successor weights
/// - **Universal states**: `w[s] = ⊗_t (t.weight ⊗ ⊗_{s' ∈ t.successors} w[s'])`
///   — the semiring product over all transitions
///
/// For `BooleanWeight`, this is equivalent to `!check_emptiness()`:
/// `BooleanWeight::one()` iff the language is non-empty.
///
/// # Arguments
///
/// * `automaton` - The weighted alternating automaton.
///
/// # Returns
///
/// The total weight of the language from the initial state.
/// Returns `W::zero()` if the automaton has no initial state or is empty.
pub fn weighted_emptiness<W: Semiring>(automaton: &WeightedAlternatingAutomaton<W>) -> W {
    let n = automaton.num_states();
    if n == 0 || automaton.initial_state.is_none() {
        return W::zero();
    }

    let initial = automaton
        .initial_state
        .expect("initial_state checked above");
    if initial >= n {
        return W::zero();
    }

    // Build adjacency: for each state, collect its transitions.
    let mut transitions_from: Vec<Vec<usize>> = vec![Vec::new(); n];
    for (idx, t) in automaton.transitions.iter().enumerate() {
        if t.from < n {
            transitions_from[t.from].push(idx);
        }
    }

    // Initialize weights: leaf states get their terminal weight (or zero).
    let mut weights: Vec<W> = vec![W::zero(); n];
    for s in 0..n {
        if transitions_from[s].is_empty() {
            // Leaf state: use terminal weight if present, else derive from parity.
            weights[s] = automaton
                .terminal_weights
                .get(&s)
                .copied()
                .unwrap_or_else(|| {
                    // Backward compatibility: even priority = one, odd = zero.
                    if automaton.states[s].priority % 2 == 0 {
                        W::one()
                    } else {
                        W::zero()
                    }
                });
        }
    }

    // Fixpoint iteration: propagate weights bottom-up.
    let epsilon = 1e-10;
    let max_iterations = n * n + 1; // Guarantee termination for acyclic graphs.
    for _iter in 0..max_iterations {
        let mut changed = false;

        for s in 0..n {
            if transitions_from[s].is_empty() {
                continue; // leaf, already initialized
            }

            let trans_indices = &transitions_from[s];

            let new_weight = match automaton.states[s].branching {
                BranchingMode::Existential => {
                    // ⊕ over all transitions: sum of (weight ⊗ product-of-successor-weights)
                    let mut acc = W::zero();
                    for &ti in trans_indices {
                        let t = &automaton.transitions[ti];
                        let mut prod = t.weight;
                        for &succ in &t.successors {
                            if succ < n {
                                prod = prod.times(&weights[succ]);
                            } else {
                                prod = W::zero(); // invalid successor
                                break;
                            }
                        }
                        acc = acc.plus(&prod);
                    }
                    acc
                }
                BranchingMode::Universal => {
                    // ⊗ over all transitions: product of (weight ⊗ product-of-successor-weights)
                    let mut acc = W::one();
                    for &ti in trans_indices {
                        let t = &automaton.transitions[ti];
                        let mut prod = t.weight;
                        for &succ in &t.successors {
                            if succ < n {
                                prod = prod.times(&weights[succ]);
                            } else {
                                prod = W::zero(); // invalid successor
                                break;
                            }
                        }
                        acc = acc.times(&prod);
                    }
                    acc
                }
            };

            if !new_weight.approx_eq(&weights[s], epsilon) {
                weights[s] = new_weight;
                changed = true;
            }
        }

        if !changed {
            break;
        }
    }

    weights[initial]
}

/// Evaluate a word against a weighted alternating automaton.
///
/// Performs bottom-up evaluation of the automaton on the given input word,
/// computing the total acceptance weight. At each step, the current input
/// symbol is matched against transition labels:
///
/// - **Existential states**: the best (⊕) matching transition is selected
/// - **Universal states**: all matching transitions must contribute (⊗)
///
/// The evaluation proceeds symbol-by-symbol from the initial state, building
/// a weight for each reachable configuration.
///
/// # Arguments
///
/// * `automaton` - The weighted alternating automaton.
/// * `word` - The input word as a slice of symbol strings.
///
/// # Returns
///
/// The total weight of the word. Returns `W::zero()` if the word is rejected.
// === Rocq Proof Alignment (AwaPolynomialEvaluation.v) ===
//
// The Rocq proof models an AWA with univariate polynomials and proves
// bottom-up = top-down evaluation (`bu_equals_td`). It also proves:
//   - `empty_word_eval`: empty word = final weight of initial state.
//   - `single_symbol_eval`: single symbol = poly_eval at final weight.
//
// The Rust implements the *multivariate* generalization (Kostolányi & Mišún
// Def. 5.1): states are partitioned into Q⊕ (existential = sum) and Q⊗
// (universal = product). Transitions carry per-edge weights rather than
// full polynomial objects. The Rust's game-semantics evaluation with
// memoization is the multivariate extension of the Rocq's univariate model.
//
// The gap exists because the full multivariate polynomial proof would require
// multivariate Rocq polynomial libraries, which are significantly more complex.
// The univariate proof captures the essential inductive structure: evaluation
// direction independence is preserved in both models.
//
// Properties preserved:
//   - Empty word evaluates to the terminal weight of the initial state.
//   - Single-symbol evaluation composes transition weight with terminal weight.
//   - Evaluation direction independence (by structural induction on word).
pub fn evaluate_word<W: Semiring>(automaton: &WeightedAlternatingAutomaton<W>, word: &[&str]) -> W {
    let n = automaton.num_states();
    if n == 0 || automaton.initial_state.is_none() {
        return W::zero();
    }

    let initial = automaton
        .initial_state
        .expect("initial_state checked above");
    if initial >= n {
        return W::zero();
    }

    // Recursive evaluation with memoization.
    // eval(state, position) = weight of the sub-run from `state` reading word[position..].
    let word_len = word.len();

    // Memo table: state x position -> Option<W>
    let mut memo: Vec<Vec<Option<W>>> = vec![vec![None; word_len + 1]; n];

    fn eval_rec<W: Semiring>(
        automaton: &WeightedAlternatingAutomaton<W>,
        state: usize,
        pos: usize,
        word: &[&str],
        memo: &mut Vec<Vec<Option<W>>>,
    ) -> W {
        let n = automaton.num_states();
        let word_len = word.len();

        if let Some(cached) = &memo[state][pos] {
            return *cached;
        }

        // At end of word: return terminal weight.
        if pos == word_len {
            let result = automaton
                .terminal_weights
                .get(&state)
                .copied()
                .unwrap_or_else(|| {
                    // Backward compatibility: even priority = accepting.
                    if automaton.states[state].priority % 2 == 0 {
                        W::one()
                    } else {
                        W::zero()
                    }
                });
            memo[state][pos] = Some(result);
            return result;
        }

        let current_symbol = word[pos];

        // Collect matching transitions.
        let matching: Vec<&WeightedAlternatingTransition<W>> = automaton
            .transitions
            .iter()
            .filter(|t| t.from == state && t.label.as_deref() == Some(current_symbol))
            .collect();

        if matching.is_empty() {
            // No matching transition: check if this state can accept without consuming input.
            // (No epsilon transitions in this simplified model.)
            let result = W::zero();
            memo[state][pos] = Some(result);
            return result;
        }

        let result = match automaton.states[state].branching {
            BranchingMode::Existential => {
                // ⊕ over matching transitions.
                let mut acc = W::zero();
                for t in &matching {
                    let mut prod = t.weight;
                    for &succ in &t.successors {
                        if succ < n {
                            let succ_w = eval_rec(automaton, succ, pos + 1, word, memo);
                            prod = prod.times(&succ_w);
                        } else {
                            prod = W::zero();
                            break;
                        }
                    }
                    acc = acc.plus(&prod);
                }
                acc
            }
            BranchingMode::Universal => {
                // ⊗ over matching transitions.
                let mut acc = W::one();
                for t in &matching {
                    let mut prod = t.weight;
                    for &succ in &t.successors {
                        if succ < n {
                            let succ_w = eval_rec(automaton, succ, pos + 1, word, memo);
                            prod = prod.times(&succ_w);
                        } else {
                            prod = W::zero();
                            break;
                        }
                    }
                    acc = acc.times(&prod);
                }
                acc
            }
        };

        memo[state][pos] = Some(result);
        result
    }

    eval_rec(automaton, initial, 0, word, &mut memo)
}

// ══════════════════════════════════════════════════════════════════════════════
// Pipeline bridge
// ══════════════════════════════════════════════════════════════════════════════

/// Pipeline-level alternating automaton analysis result.
#[derive(Debug, Clone)]
pub struct AlternatingAnalysis {
    /// Pairs of categories found non-bisimilar.
    pub non_bisimilar_pairs: Vec<(String, String)>,
    /// Number of states in the game automaton.
    pub state_count: usize,
}

/// Analyze categories for bisimulation equivalence via alternating automata.
///
/// Builds an alternating automaton from the grammar's category structure
/// (each category becomes a state, rules become transitions) and runs
/// pairwise bisimulation checks to identify non-bisimilar category pairs.
///
/// # Arguments
///
/// * `all_syntax` — Slice of `(rule_label, category, items)` triples from the
///   parser bundle.
/// * `categories` — Slice of [`CategoryInfo`](crate::pipeline::CategoryInfo)
///   describing each grammar category.
///
/// # Returns
///
/// An [`AlternatingAnalysis`] with non-bisimilar pairs and the state count
/// of the game automaton.
pub fn analyze_from_bundle(
    all_syntax: &[(String, String, Vec<crate::SyntaxItemSpec>)],
    categories: &[crate::pipeline::CategoryInfo],
) -> AlternatingAnalysis {
    if categories.is_empty() {
        return AlternatingAnalysis {
            non_bisimilar_pairs: Vec::new(),
            state_count: 0,
        };
    }

    // Phase 1: Build one alternating automaton per category.
    // Each category becomes an automaton where:
    //   - One state per rule (existential: any rule can match)
    //   - Transitions labeled with the terminal/nonterminal references in each rule
    let mut cat_automata: Vec<(String, AlternatingAutomaton)> = Vec::new();
    let cat_names: Vec<&str> = categories.iter().map(|c| c.name.as_str()).collect();

    for cat_info in categories {
        let mut aa = AlternatingAutomaton::new();

        // Create the root state (existential: parser tries alternative rules).
        let root = aa.add_state(BranchingMode::Existential, 0);
        aa.initial_state = Some(root);

        // Collect rules belonging to this category.
        let cat_rules: Vec<&(String, String, Vec<crate::SyntaxItemSpec>)> = all_syntax
            .iter()
            .filter(|(_, cat, _)| cat == &cat_info.name)
            .collect();

        for (rule_label, _, items) in &cat_rules {
            // Each rule gets a universal state (all items must match).
            let rule_state = aa.add_state(BranchingMode::Universal, 0);

            // Root existentially transitions to this rule.
            aa.add_transition(root, Some(rule_label.clone()), vec![rule_state]);

            // Each syntax item in the rule becomes a successor of the rule state.
            for item in items.iter() {
                let label = extract_item_label(item);
                let item_state = aa.add_state(BranchingMode::Existential, 0);
                aa.add_transition(rule_state, Some(label), vec![item_state]);
            }
        }

        cat_automata.push((cat_info.name.clone(), aa));
    }

    // Phase 2: Pairwise bisimulation checks.
    let total_states: usize = cat_automata.iter().map(|(_, aa)| aa.num_states()).sum();
    let mut non_bisimilar_pairs: Vec<(String, String)> = Vec::new();

    for i in 0..cat_automata.len() {
        for j in (i + 1)..cat_automata.len() {
            let (ref name_i, ref aa_i) = cat_automata[i];
            let (ref name_j, ref aa_j) = cat_automata[j];

            if !bisimulation_game(aa_i, aa_j) {
                non_bisimilar_pairs.push((name_i.clone(), name_j.clone()));
            }
        }
    }

    let _ = cat_names; // suppress unused warning

    AlternatingAnalysis {
        non_bisimilar_pairs,
        state_count: total_states,
    }
}

/// Extract a diagnostic label from a syntax item for use as a transition label.
fn extract_item_label(item: &crate::SyntaxItemSpec) -> String {
    match item {
        crate::SyntaxItemSpec::Terminal(t) => format!("T:{}", t),
        crate::SyntaxItemSpec::NonTerminal { category, .. } => format!("NT:{}", category),
        crate::SyntaxItemSpec::IdentCapture { param_name } => format!("ID:{}", param_name),
        crate::SyntaxItemSpec::Binder {
            param_name,
            category,
            ..
        } => {
            format!("BIND:{}:{}", param_name, category)
        }
        crate::SyntaxItemSpec::Collection {
            element_category,
            separator,
            ..
        } => {
            format!("COL:{}:{}", element_category, separator)
        }
        crate::SyntaxItemSpec::Sep { separator, .. } => format!("SEP:{}", separator),
        crate::SyntaxItemSpec::Map { .. } => "MAP".to_string(),
        crate::SyntaxItemSpec::Zip {
            left_category,
            right_category,
            ..
        } => {
            format!("ZIP:{}:{}", left_category, right_category)
        }
        crate::SyntaxItemSpec::BinderCollection {
            param_name,
            separator,
        } => {
            format!("BCOL:{}:{}", param_name, separator)
        }
        crate::SyntaxItemSpec::Optional { .. } => "OPT".to_string(),
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Predicate Dispatch — PredicateCompiler integration
// ══════════════════════════════════════════════════════════════════════════════

/// Compiler adapter for the Alternating Weighted Automata module (M3).
///
/// Activated by `ForallFinite`/`ForallInfinite` morphemes (alternating variety).
#[cfg(feature = "predicate-dispatch")]
pub struct AlternatingCompiler;

#[cfg(feature = "predicate-dispatch")]
impl crate::predicate_dispatch::PredicateCompiler for AlternatingCompiler {
    type Output = AlternatingAnalysis;

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
    use crate::automata::semiring::TropicalWeight;

    #[test]
    fn alternating_state_display() {
        let e = AlternatingState::existential(0);
        assert_eq!(e.to_string(), "q0[E,p=0]");
        let u = AlternatingState::universal(1);
        assert_eq!(u.to_string(), "q1[A,p=0]");
        let labeled =
            AlternatingState::labeled(2, BranchingMode::Universal, 3, "check_all");
        assert_eq!(labeled.to_string(), "q2[A,p=3](check_all)");
    }

    #[test]
    fn alternating_automaton_construction() {
        let mut aa = AlternatingAutomaton::new();
        let q0 = aa.add_state(BranchingMode::Existential, 0);
        let q1 = aa.add_state(BranchingMode::Universal, 1);
        let q2 = aa.add_state(BranchingMode::Existential, 2);
        aa.initial_state = Some(q0);
        aa.add_transition(q0, Some("a".to_string()), vec![q1, q2]);
        aa.add_transition(q1, Some("b".to_string()), vec![q0]);

        assert_eq!(aa.num_states(), 3);
        assert_eq!(aa.num_transitions(), 2);
        assert_eq!(aa.max_priority(), 2);
    }

    #[test]
    fn alternating_transition_display() {
        let t = AlternatingTransition {
            from: 0,
            label: Some("a".to_string()),
            successors: vec![1, 2],
            weight: BooleanWeight::one(),
        };
        assert_eq!(t.to_string(), "q0 --a-> {q1, q2}");
    }

    // ─── check_emptiness tests ───────────────────────────────────────────

    #[test]
    fn emptiness_no_states() {
        let aa = AlternatingAutomaton::new();
        assert!(check_emptiness(&aa)); // no states => empty language
    }

    #[test]
    fn emptiness_no_initial_state() {
        let mut aa = AlternatingAutomaton::new();
        aa.add_state(BranchingMode::Existential, 0);
        // No initial state set.
        assert!(check_emptiness(&aa));
    }

    #[test]
    fn emptiness_single_accepting_leaf() {
        // Single existential state with even priority and no transitions => accepting.
        let mut aa = AlternatingAutomaton::new();
        let q0 = aa.add_state(BranchingMode::Existential, 0); // even priority
        aa.initial_state = Some(q0);
        assert!(!check_emptiness(&aa)); // non-empty
    }

    #[test]
    fn emptiness_single_rejecting_leaf() {
        // Single state with odd priority and no transitions => rejecting leaf.
        let mut aa = AlternatingAutomaton::new();
        let q0 = aa.add_state(BranchingMode::Existential, 1); // odd priority
        aa.initial_state = Some(q0);
        assert!(check_emptiness(&aa)); // empty
    }

    #[test]
    fn emptiness_existential_one_accepting_successor() {
        // q0 (existential) --a--> {q1}; q1 has even priority, no transitions.
        let mut aa = AlternatingAutomaton::new();
        let q0 = aa.add_state(BranchingMode::Existential, 1); // odd (must continue)
        let q1 = aa.add_state(BranchingMode::Existential, 0); // even (accepting leaf)
        aa.initial_state = Some(q0);
        aa.add_transition(q0, Some("a".to_string()), vec![q1]);
        assert!(!check_emptiness(&aa)); // non-empty: q0 -> q1 (accepting)
    }

    #[test]
    fn emptiness_existential_all_rejecting_successors() {
        // q0 (existential) --a--> {q1}; q1 has odd priority, no transitions.
        let mut aa = AlternatingAutomaton::new();
        let q0 = aa.add_state(BranchingMode::Existential, 0);
        let q1 = aa.add_state(BranchingMode::Existential, 1); // rejecting leaf
        aa.initial_state = Some(q0);
        aa.add_transition(q0, Some("a".to_string()), vec![q1]);
        // q0 has a transition to q1 which is rejecting, so the transition
        // doesn't help. But q0 also has no other transitions. q0's own priority
        // is even but it's not a leaf (it has transitions). Let's check:
        // q0 has transitions, so it's not a leaf. The only transition leads to q1
        // which is not accepting. So q0 can't produce an accepting run.
        assert!(check_emptiness(&aa));
    }

    #[test]
    fn emptiness_universal_all_accepting() {
        // q0 (universal) --a--> {q1, q2}; both q1, q2 accepting leaves.
        let mut aa = AlternatingAutomaton::new();
        let q0 = aa.add_state(BranchingMode::Universal, 1);
        let q1 = aa.add_state(BranchingMode::Existential, 0);
        let q2 = aa.add_state(BranchingMode::Existential, 0);
        aa.initial_state = Some(q0);
        aa.add_transition(q0, Some("a".to_string()), vec![q1, q2]);
        assert!(!check_emptiness(&aa)); // non-empty: both successors accept
    }

    #[test]
    fn emptiness_universal_one_rejecting() {
        // q0 (universal) --a--> {q1, q2}; q1 accepting, q2 rejecting.
        // Universal requires ALL successors to accept.
        let mut aa = AlternatingAutomaton::new();
        let q0 = aa.add_state(BranchingMode::Universal, 1);
        let q1 = aa.add_state(BranchingMode::Existential, 0); // accepting
        let q2 = aa.add_state(BranchingMode::Existential, 1); // rejecting
        aa.initial_state = Some(q0);
        aa.add_transition(q0, Some("a".to_string()), vec![q1, q2]);
        assert!(check_emptiness(&aa)); // empty: q2 rejects
    }

    #[test]
    fn emptiness_existential_multiple_transitions() {
        // q0 (existential) has two transitions: one leads to rejecting, other to accepting.
        let mut aa = AlternatingAutomaton::new();
        let q0 = aa.add_state(BranchingMode::Existential, 1);
        let q1 = aa.add_state(BranchingMode::Existential, 1); // rejecting
        let q2 = aa.add_state(BranchingMode::Existential, 0); // accepting
        aa.initial_state = Some(q0);
        aa.add_transition(q0, Some("a".to_string()), vec![q1]);
        aa.add_transition(q0, Some("b".to_string()), vec![q2]);
        assert!(!check_emptiness(&aa)); // non-empty: can choose b -> q2
    }

    #[test]
    fn emptiness_universal_multiple_transitions() {
        // q0 (universal) has two transitions: both must lead to accepting successors.
        let mut aa = AlternatingAutomaton::new();
        let q0 = aa.add_state(BranchingMode::Universal, 1);
        let q1 = aa.add_state(BranchingMode::Existential, 0); // accepting
        let q2 = aa.add_state(BranchingMode::Existential, 1); // rejecting
        aa.initial_state = Some(q0);
        aa.add_transition(q0, Some("a".to_string()), vec![q1]);
        aa.add_transition(q0, Some("b".to_string()), vec![q2]);
        assert!(check_emptiness(&aa)); // empty: b transition fails
    }

    #[test]
    fn emptiness_chain_propagation() {
        // q0 -> q1 -> q2 (accepting). Should propagate backward.
        let mut aa = AlternatingAutomaton::new();
        let q0 = aa.add_state(BranchingMode::Existential, 1);
        let q1 = aa.add_state(BranchingMode::Existential, 1);
        let q2 = aa.add_state(BranchingMode::Existential, 0); // accepting leaf
        aa.initial_state = Some(q0);
        aa.add_transition(q0, Some("a".to_string()), vec![q1]);
        aa.add_transition(q1, Some("b".to_string()), vec![q2]);
        assert!(!check_emptiness(&aa));
    }

    // ─── bisimulation_game tests ─────────────────────────────────────────

    #[test]
    fn bisimulation_both_empty() {
        let a = AlternatingAutomaton::new();
        let b = AlternatingAutomaton::new();
        assert!(bisimulation_game(&a, &b));
    }

    #[test]
    fn bisimulation_one_empty_one_nonempty() {
        let a = AlternatingAutomaton::new();
        let mut b = AlternatingAutomaton::new();
        let q0 = b.add_state(BranchingMode::Existential, 0);
        b.initial_state = Some(q0);
        // b is non-empty (accepting leaf), a is empty => not bisimilar.
        assert!(!bisimulation_game(&a, &b));
    }

    #[test]
    fn bisimulation_identical_single_state() {
        let mut a = AlternatingAutomaton::new();
        let q0 = a.add_state(BranchingMode::Existential, 0);
        a.initial_state = Some(q0);

        let mut b = AlternatingAutomaton::new();
        let q0b = b.add_state(BranchingMode::Existential, 0);
        b.initial_state = Some(q0b);

        assert!(bisimulation_game(&a, &b));
    }

    #[test]
    fn bisimulation_same_structure() {
        // Both: q0 --a--> q1 (accepting leaf).
        let mut a = AlternatingAutomaton::new();
        let q0a = a.add_state(BranchingMode::Existential, 0);
        let q1a = a.add_state(BranchingMode::Existential, 0);
        a.initial_state = Some(q0a);
        a.add_transition(q0a, Some("a".to_string()), vec![q1a]);

        let mut b = AlternatingAutomaton::new();
        let q0b = b.add_state(BranchingMode::Existential, 0);
        let q1b = b.add_state(BranchingMode::Existential, 0);
        b.initial_state = Some(q0b);
        b.add_transition(q0b, Some("a".to_string()), vec![q1b]);

        assert!(bisimulation_game(&a, &b));
    }

    #[test]
    fn bisimulation_different_labels() {
        // a: q0 --a--> q1; b: q0 --b--> q1. Different labels => not bisimilar.
        let mut a = AlternatingAutomaton::new();
        let q0a = a.add_state(BranchingMode::Existential, 0);
        let q1a = a.add_state(BranchingMode::Existential, 0);
        a.initial_state = Some(q0a);
        a.add_transition(q0a, Some("a".to_string()), vec![q1a]);

        let mut b = AlternatingAutomaton::new();
        let q0b = b.add_state(BranchingMode::Existential, 0);
        let q1b = b.add_state(BranchingMode::Existential, 0);
        b.initial_state = Some(q0b);
        b.add_transition(q0b, Some("b".to_string()), vec![q1b]);

        assert!(!bisimulation_game(&a, &b));
    }

    #[test]
    fn bisimulation_extra_transition() {
        // a: q0 --a--> q1; b: q0 --a--> q1, q0 --b--> q1.
        // b has an extra transition "b" that a cannot match => not bisimilar.
        let mut a = AlternatingAutomaton::new();
        let q0a = a.add_state(BranchingMode::Existential, 0);
        let q1a = a.add_state(BranchingMode::Existential, 0);
        a.initial_state = Some(q0a);
        a.add_transition(q0a, Some("a".to_string()), vec![q1a]);

        let mut b = AlternatingAutomaton::new();
        let q0b = b.add_state(BranchingMode::Existential, 0);
        let q1b = b.add_state(BranchingMode::Existential, 0);
        b.initial_state = Some(q0b);
        b.add_transition(q0b, Some("a".to_string()), vec![q1b]);
        b.add_transition(q0b, Some("b".to_string()), vec![q1b]);

        assert!(!bisimulation_game(&a, &b));
    }

    #[test]
    fn bisimulation_symmetric() {
        // Bisimulation should be symmetric: bisim(a,b) == bisim(b,a).
        let mut a = AlternatingAutomaton::new();
        let q0a = a.add_state(BranchingMode::Existential, 0);
        let q1a = a.add_state(BranchingMode::Existential, 0);
        a.initial_state = Some(q0a);
        a.add_transition(q0a, Some("x".to_string()), vec![q1a]);

        let mut b = AlternatingAutomaton::new();
        let q0b = b.add_state(BranchingMode::Existential, 0);
        b.initial_state = Some(q0b);
        // b has no transitions, a does => not bisimilar.

        assert_eq!(bisimulation_game(&a, &b), bisimulation_game(&b, &a));
    }

    #[test]
    fn bisimulation_no_outgoing_leaf_states() {
        // Both automata are single leaf states with no transitions.
        // Same labels: bisimilar.
        let mut a = AlternatingAutomaton::new();
        let q0a = a.add_state(BranchingMode::Existential, 0);
        a.initial_state = Some(q0a);

        let mut b = AlternatingAutomaton::new();
        let q0b = b.add_state(BranchingMode::Universal, 2);
        b.initial_state = Some(q0b);

        // Neither has transitions => they match vacuously.
        assert!(bisimulation_game(&a, &b));
    }

    #[test]
    fn test_analyze_from_bundle_basic() {
        let syntax: Vec<(String, String, Vec<crate::SyntaxItemSpec>)> = vec![(
            "Add".to_string(),
            "Expr".to_string(),
            vec![
                crate::SyntaxItemSpec::NonTerminal {
                    category: "Expr".to_string(),
                    param_name: "a".to_string(),
                },
                crate::SyntaxItemSpec::Terminal("+".to_string()),
                crate::SyntaxItemSpec::NonTerminal {
                    category: "Expr".to_string(),
                    param_name: "b".to_string(),
                },
            ],
        )];
        let cats = vec![
            crate::pipeline::CategoryInfo {
                name: "Expr".to_string(),
                native_type: None,
                is_primary: true,
            },
            crate::pipeline::CategoryInfo {
                name: "Type".to_string(),
                native_type: None,
                is_primary: false,
            },
        ];
        let result = analyze_from_bundle(&syntax, &cats);
        // AlternatingAnalysis is returned directly (not Option).
        assert!(result.state_count > 0, "should produce states from categories");
    }

    // ─── weighted operations tests ───────────────────────────────────────

    #[test]
    fn weighted_emptiness_boolean_matches_check_emptiness() {
        // Verify that weighted_emptiness for BooleanWeight is consistent
        // with check_emptiness: one() iff non-empty, zero() iff empty.

        // Case 1: Non-empty automaton (single accepting leaf).
        let mut aa = AlternatingAutomaton::new();
        let q0 = aa.add_state(BranchingMode::Existential, 0);
        aa.initial_state = Some(q0);
        assert!(!check_emptiness(&aa));
        assert!(weighted_emptiness(&aa).is_one());

        // Case 2: Empty automaton (single rejecting leaf).
        let mut aa2 = AlternatingAutomaton::new();
        let q0 = aa2.add_state(BranchingMode::Existential, 1);
        aa2.initial_state = Some(q0);
        assert!(check_emptiness(&aa2));
        assert!(weighted_emptiness(&aa2).is_zero());

        // Case 3: Chain q0 -> q1 -> q2(accepting).
        let mut aa3 = AlternatingAutomaton::new();
        let q0 = aa3.add_state(BranchingMode::Existential, 1);
        let q1 = aa3.add_state(BranchingMode::Existential, 1);
        let q2 = aa3.add_state(BranchingMode::Existential, 0);
        aa3.initial_state = Some(q0);
        aa3.add_transition(q0, Some("a".to_string()), vec![q1]);
        aa3.add_transition(q1, Some("b".to_string()), vec![q2]);
        assert!(!check_emptiness(&aa3));
        assert!(weighted_emptiness(&aa3).is_one());

        // Case 4: Universal with one rejecting successor.
        let mut aa4 = AlternatingAutomaton::new();
        let q0 = aa4.add_state(BranchingMode::Universal, 1);
        let q1 = aa4.add_state(BranchingMode::Existential, 0);
        let q2 = aa4.add_state(BranchingMode::Existential, 1);
        aa4.initial_state = Some(q0);
        aa4.add_transition(q0, Some("a".to_string()), vec![q1, q2]);
        assert!(check_emptiness(&aa4));
        assert!(weighted_emptiness(&aa4).is_zero());
    }

    #[test]
    fn weighted_emptiness_tropical_basic() {
        // Simple tropical-weighted automaton:
        // q0 (existential) --a/2.0--> q1 (leaf, priority 0)
        // q0 (existential) --b/5.0--> q2 (leaf, priority 0)
        // Existential takes the min (plus = min), so weight = min(2.0, 5.0) = 2.0
        let mut aa: WeightedAlternatingAutomaton<TropicalWeight> =
            WeightedAlternatingAutomaton::new();
        let q0 = aa.add_state(BranchingMode::Existential, 1);
        let q1 = aa.add_state(BranchingMode::Existential, 0);
        let q2 = aa.add_state(BranchingMode::Existential, 0);
        aa.initial_state = Some(q0);
        aa.add_weighted_transition(
            q0,
            Some("a".to_string()),
            vec![q1],
            TropicalWeight::new(2.0),
        );
        aa.add_weighted_transition(
            q0,
            Some("b".to_string()),
            vec![q2],
            TropicalWeight::new(5.0),
        );
        // q1 and q2 are leaves with even priority -> terminal weight = one = 0.0.
        // weight(q0) = min(2.0 + 0.0, 5.0 + 0.0) = 2.0
        let w = weighted_emptiness(&aa);
        assert!(
            w.approx_eq(&TropicalWeight::new(2.0), 1e-9),
            "expected 2.0, got {:?}",
            w
        );
    }

    #[test]
    fn weighted_emptiness_tropical_universal() {
        // q0 (universal) --a/1.0--> {q1, q2}
        // q1: leaf, priority 0 (terminal weight = one = 0.0)
        // q2: leaf, priority 0 (terminal weight = one = 0.0)
        // Universal: times = +, so weight = 1.0 + 0.0 + 0.0 = 1.0
        let mut aa: WeightedAlternatingAutomaton<TropicalWeight> =
            WeightedAlternatingAutomaton::new();
        let q0 = aa.add_state(BranchingMode::Universal, 1);
        let q1 = aa.add_state(BranchingMode::Existential, 0);
        let q2 = aa.add_state(BranchingMode::Existential, 0);
        aa.initial_state = Some(q0);
        aa.add_weighted_transition(
            q0,
            Some("a".to_string()),
            vec![q1, q2],
            TropicalWeight::new(1.0),
        );
        // weight(q0) = 1.0 + weight(q1) + weight(q2) = 1.0 + 0.0 + 0.0 = 1.0
        let w = weighted_emptiness(&aa);
        assert!(
            w.approx_eq(&TropicalWeight::new(1.0), 1e-9),
            "expected 1.0, got {:?}",
            w
        );
    }

    #[test]
    fn weighted_emptiness_tropical_with_terminal_weights() {
        // Same as above but with explicit terminal weights.
        // q0 (existential) --a/1.0--> q1
        // q1: terminal weight = 3.0
        // weight(q0) = 1.0 + 3.0 = 4.0
        let mut aa: WeightedAlternatingAutomaton<TropicalWeight> =
            WeightedAlternatingAutomaton::new();
        let q0 = aa.add_state(BranchingMode::Existential, 1);
        let q1 = aa.add_state(BranchingMode::Existential, 0);
        aa.initial_state = Some(q0);
        aa.set_terminal_weight(q1, TropicalWeight::new(3.0));
        aa.add_weighted_transition(
            q0,
            Some("a".to_string()),
            vec![q1],
            TropicalWeight::new(1.0),
        );
        let w = weighted_emptiness(&aa);
        assert!(
            w.approx_eq(&TropicalWeight::new(4.0), 1e-9),
            "expected 4.0, got {:?}",
            w
        );
    }

    #[test]
    fn weighted_emptiness_empty_automaton() {
        let aa: WeightedAlternatingAutomaton<TropicalWeight> =
            WeightedAlternatingAutomaton::new();
        let w = weighted_emptiness(&aa);
        assert!(w.is_zero(), "empty automaton should have zero weight");
    }

    #[test]
    fn evaluate_word_boolean_basic() {
        // q0 (existential) --a--> q1 (accepting leaf)
        // Word "a" should be accepted, word "b" should be rejected.
        let mut aa = AlternatingAutomaton::new();
        let q0 = aa.add_state(BranchingMode::Existential, 0);
        let q1 = aa.add_state(BranchingMode::Existential, 0);
        aa.initial_state = Some(q0);
        aa.add_transition(q0, Some("a".to_string()), vec![q1]);

        let w_a = evaluate_word(&aa, &["a"]);
        assert!(w_a.is_one(), "word 'a' should be accepted");

        let w_b = evaluate_word(&aa, &["b"]);
        assert!(w_b.is_zero(), "word 'b' should be rejected");

        let w_empty = evaluate_word(&aa, &[]);
        // q0 has even priority (0) and is a leaf at position 0? No, q0 has
        // transitions. But at end of word, we check terminal weight.
        // q0 has even priority => terminal weight = one (accepting).
        assert!(w_empty.is_one(), "empty word should be accepted (q0 has even priority)");
    }

    #[test]
    fn evaluate_word_tropical_weighted() {
        // q0 (existential) --a/2.0--> q1 --b/3.0--> q2 (leaf, terminal=0.0)
        // Word ["a", "b"] should have weight 2.0 + 3.0 + 0.0 = 5.0
        let mut aa: WeightedAlternatingAutomaton<TropicalWeight> =
            WeightedAlternatingAutomaton::new();
        let q0 = aa.add_state(BranchingMode::Existential, 1); // odd -> must continue
        let q1 = aa.add_state(BranchingMode::Existential, 1); // odd -> must continue
        let q2 = aa.add_state(BranchingMode::Existential, 0); // even -> accepting
        aa.initial_state = Some(q0);
        aa.add_weighted_transition(
            q0,
            Some("a".to_string()),
            vec![q1],
            TropicalWeight::new(2.0),
        );
        aa.add_weighted_transition(
            q1,
            Some("b".to_string()),
            vec![q2],
            TropicalWeight::new(3.0),
        );

        let w = evaluate_word(&aa, &["a", "b"]);
        assert!(
            w.approx_eq(&TropicalWeight::new(5.0), 1e-9),
            "expected 5.0, got {:?}",
            w
        );

        // Wrong word should get infinite weight (zero = unreachable).
        let w_bad = evaluate_word(&aa, &["a", "c"]);
        assert!(w_bad.is_zero(), "wrong word should be rejected");
    }

    #[test]
    fn evaluate_word_universal_branching() {
        // q0 (universal) --a--> {q1, q2}
        // q1 (existential) --b--> q3 (accepting leaf)
        // q2 (existential) --b--> q4 (accepting leaf)
        // Word ["a", "b"]: universal requires BOTH q1 and q2 to accept.
        // Both have transitions on "b" to accepting leaves, so accepted.
        let mut aa = AlternatingAutomaton::new();
        let q0 = aa.add_state(BranchingMode::Universal, 1);
        let q1 = aa.add_state(BranchingMode::Existential, 1);
        let q2 = aa.add_state(BranchingMode::Existential, 1);
        let q3 = aa.add_state(BranchingMode::Existential, 0);
        let q4 = aa.add_state(BranchingMode::Existential, 0);
        aa.initial_state = Some(q0);
        aa.add_transition(q0, Some("a".to_string()), vec![q1, q2]);
        aa.add_transition(q1, Some("b".to_string()), vec![q3]);
        aa.add_transition(q2, Some("b".to_string()), vec![q4]);

        let w = evaluate_word(&aa, &["a", "b"]);
        assert!(w.is_one(), "both branches accept => accepted");
    }

    #[test]
    fn weighted_transition_display_with_weight() {
        // Non-unit weight should display the weight.
        let t = WeightedAlternatingTransition {
            from: 0,
            label: Some("a".to_string()),
            successors: vec![1],
            weight: TropicalWeight::new(2.5),
        };
        let s = t.to_string();
        assert!(
            s.contains("2.5"),
            "display should include weight 2.5, got: {}",
            s
        );
    }

    #[test]
    fn polynomial_transition_construction() {
        // Verify that PolynomialTransition can be constructed and inspected.
        let pt: PolynomialTransition<TropicalWeight> = PolynomialTransition {
            from: 0,
            label: Some("a".to_string()),
            monomials: vec![
                // Monomial 1: 2.0 * x_1^1 * x_2^1
                (TropicalWeight::new(2.0), vec![(1, 1), (2, 1)]),
                // Monomial 2: 3.0 * x_3^2
                (TropicalWeight::new(3.0), vec![(3, 2)]),
            ],
        };
        assert_eq!(pt.from, 0);
        assert_eq!(pt.monomials.len(), 2);
        assert_eq!(pt.monomials[0].1.len(), 2); // two variables in first monomial
        assert_eq!(pt.monomials[1].1.len(), 1); // one variable in second monomial
    }

    #[test]
    fn set_terminal_weight_semantics() {
        // Verify that set_terminal_weight with zero removes the entry,
        // and non-zero inserts it.
        let mut aa: WeightedAlternatingAutomaton<TropicalWeight> =
            WeightedAlternatingAutomaton::new();
        let q0 = aa.add_state(BranchingMode::Existential, 0);

        // Initially no terminal weight.
        assert!(!aa.terminal_weights.contains_key(&q0));

        // Set non-zero weight.
        aa.set_terminal_weight(q0, TropicalWeight::new(5.0));
        assert_eq!(aa.terminal_weights.get(&q0), Some(&TropicalWeight::new(5.0)));

        // Set zero weight removes entry.
        aa.set_terminal_weight(q0, TropicalWeight::zero());
        assert!(!aa.terminal_weights.contains_key(&q0));
    }

    #[test]
    fn weighted_automaton_default_trait() {
        let aa: WeightedAlternatingAutomaton<TropicalWeight> = Default::default();
        assert_eq!(aa.num_states(), 0);
        assert_eq!(aa.num_transitions(), 0);
        assert!(aa.initial_state.is_none());
        assert!(aa.terminal_weights.is_empty());
    }

    #[test]
    fn weighted_automaton_display() {
        let aa: WeightedAlternatingAutomaton<TropicalWeight> =
            WeightedAlternatingAutomaton::new();
        let s = aa.to_string();
        assert!(
            s.contains("WeightedAlternatingAutomaton"),
            "display should include type name, got: {}",
            s
        );
    }

    // ── Rocq Proof Alignment Tests (AwaPolynomialEvaluation.v) ───────────────

    #[test]
    fn test_evaluate_word_empty_equals_final_weight() {
        // Rocq `empty_word_eval`: eval_bottom_up A [] = awa_final A (awa_initial A).
        // For the empty word, evaluate_word should return the terminal weight
        // of the initial state.
        let mut aa: WeightedAlternatingAutomaton<TropicalWeight> =
            WeightedAlternatingAutomaton::new();
        let q0 = aa.add_state(BranchingMode::Existential, 1); // odd priority → default zero
        aa.initial_state = Some(q0);
        aa.set_terminal_weight(q0, TropicalWeight::new(7.0));

        let w = evaluate_word(&aa, &[]);
        assert!(
            w.approx_eq(&TropicalWeight::new(7.0), 1e-9),
            "empty word should return terminal weight of initial state, got {:?}",
            w
        );
    }

    #[test]
    fn test_evaluate_word_single_symbol() {
        // Rocq `single_symbol_eval`: eval_bottom_up A [a] =
        //   poly_eval(delta(init, a), awa_final(init)).
        // With q0 →a/4.0→ q1, terminal(q1) = 2.0:
        //   In tropical semiring: transition weight + terminal = 4.0 + 2.0 = 6.0.
        let mut aa: WeightedAlternatingAutomaton<TropicalWeight> =
            WeightedAlternatingAutomaton::new();
        let q0 = aa.add_state(BranchingMode::Existential, 1); // odd → must continue
        let q1 = aa.add_state(BranchingMode::Existential, 1); // odd → check terminal
        aa.initial_state = Some(q0);
        aa.set_terminal_weight(q1, TropicalWeight::new(2.0));

        aa.add_weighted_transition(
            q0,
            Some("a".to_string()),
            vec![q1],
            TropicalWeight::new(4.0),
        );

        let w = evaluate_word(&aa, &["a"]);
        // Expected: transition weight (4.0) + terminal weight (2.0) = 6.0 in tropical
        assert!(
            w.approx_eq(&TropicalWeight::new(6.0), 1e-9),
            "single symbol should be transition + terminal, got {:?}",
            w
        );
    }
}
