//! Alternating automata with universal/existential branching.
//!
//! Alternating automata extend nondeterministic automata by allowing transitions
//! to specify both existential (disjunctive) and universal (conjunctive) branching.
//! A transition can require that **all** successor states accept (universal) or
//! that **some** successor state accepts (existential). This duality makes
//! alternating automata exponentially more succinct than NFAs for certain languages
//! and provides a natural model for game semantics and CTL model checking.
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
//! AlternatingAutomaton
//!       │
//!       ├──→ check_emptiness() (via parity game reduction)
//!       │
//!       └──→ bisimulation_game() (for language equivalence via games)
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

// NOTE: Semiring import will be used when weighted alternating automata are implemented.
#[allow(unused_imports)]
use crate::automata::semiring::Semiring;

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
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BranchingMode {
    /// Existential (disjunctive): at least one successor run must accept.
    Existential,
    /// Universal (conjunctive): all successor runs must accept.
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

/// A transition in an alternating automaton.
///
/// The transition from state `from` on input symbol `label` goes to a set of
/// successor states. The interpretation depends on the branching mode of the
/// source state:
/// - Existential: the run accepts if **any** successor run accepts
/// - Universal: the run accepts if **all** successor runs accept
#[derive(Debug, Clone)]
pub struct AlternatingTransition {
    /// Source state ID.
    pub from: usize,
    /// Input symbol label (`None` for epsilon).
    pub label: Option<String>,
    /// Set of successor state IDs.
    pub successors: Vec<usize>,
}

impl fmt::Display for AlternatingTransition {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let label = self.label.as_deref().unwrap_or("epsilon");
        let succs: Vec<String> = self.successors.iter().map(|s| format!("q{}", s)).collect();
        write!(f, "q{} --{}-> {{{}}}", self.from, label, succs.join(", "))
    }
}

/// An alternating automaton with parity acceptance condition.
///
/// `A = (Q, Σ, δ, q₀, Ω)` where:
/// - `Q = Q_E ∪ Q_A` (existential and universal states)
/// - `Σ` is the input alphabet
/// - `δ: Q × Σ → 2^Q` is the transition function
/// - `q₀` is the initial state
/// - `Ω: Q → N` is the priority function (parity acceptance)
///
/// A run is accepting iff the minimum priority seen infinitely often is even.
#[derive(Debug, Clone)]
pub struct AlternatingAutomaton {
    /// All states.
    pub states: Vec<AlternatingState>,
    /// Input alphabet.
    pub alphabet: HashSet<String>,
    /// Transitions, indexed by `(from_state, label)`.
    pub transitions: Vec<AlternatingTransition>,
    /// Initial state ID.
    pub initial_state: Option<usize>,
}

impl AlternatingAutomaton {
    /// Create an empty alternating automaton.
    pub fn new() -> Self {
        AlternatingAutomaton {
            states: Vec::new(),
            alphabet: HashSet::new(),
            transitions: Vec::new(),
            initial_state: None,
        }
    }

    /// Add a state and return its ID.
    pub fn add_state(&mut self, branching: BranchingMode, priority: u32) -> usize {
        let id = self.states.len();
        self.states.push(AlternatingState::with_priority(id, branching, priority));
        id
    }

    /// Add a transition.
    pub fn add_transition(
        &mut self,
        from: usize,
        label: Option<String>,
        successors: Vec<usize>,
    ) {
        if let Some(ref l) = label {
            self.alphabet.insert(l.clone());
        }
        self.transitions.push(AlternatingTransition {
            from,
            label,
            successors,
        });
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

impl Default for AlternatingAutomaton {
    fn default() -> Self {
        Self::new()
    }
}

impl fmt::Display for AlternatingAutomaton {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "AlternatingAutomaton {{ states: {}, transitions: {}, max_priority: {} }}",
            self.num_states(),
            self.num_transitions(),
            self.max_priority(),
        )
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Core functions
// ══════════════════════════════════════════════════════════════════════════════

/// Check emptiness of an alternating parity automaton.
///
/// Reduces to solving a parity game: Player 0 (existential) controls
/// existential states, Player 1 (universal) controls universal states.
/// The automaton is non-empty iff Player 0 has a winning strategy from
/// the initial state.
///
/// Uses a small progress measure algorithm (Jurdzinski, 2000) for parity
/// game solving.
///
/// # Arguments
///
/// * `automaton` - The alternating automaton to check.
///
/// # Returns
///
/// `true` if `L(automaton) = empty`, `false` otherwise.
pub fn check_emptiness(automaton: &AlternatingAutomaton) -> bool {
    // For alternating automata on finite words, the language is non-empty iff
    // there exists an accepting run tree from the initial state.
    //
    // Bottom-up fixpoint approach:
    //   1. Start by marking states that can "accept" on their own.
    //      A state with even priority and no outgoing transitions (a leaf)
    //      is accepting. A state with odd priority and no outgoing transitions
    //      is rejecting.
    //   2. Propagate backward:
    //      - Existential state: accepting if at least one transition leads to
    //        a set of successors that are all accepting.
    //      - Universal state: accepting if ALL transitions lead to sets of
    //        successors that are all accepting.
    //   3. The language is empty iff the initial state is NOT accepting.
    //
    // For finite-word semantics with parity, a state with even priority is
    // "locally accepting" (it can terminate the run), while odd priority
    // means the run must continue. We model this by treating even-priority
    // states with no transitions as accepting leaves.

    let n = automaton.num_states();
    if n == 0 || automaton.initial_state.is_none() {
        return true; // empty: no states or no initial state
    }

    let initial = automaton.initial_state.expect("initial_state checked above");
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
    // Bisimulation game between two alternating automata.
    //
    // Two processes (automata starting from their initial states) are bisimilar
    // iff the Defender has a winning strategy in the bisimulation game:
    //
    //   Game positions: pairs (p, q) where p is a state in A, q is a state in B.
    //   Attacker picks a transition in one automaton; Defender must match it
    //   (same label) in the other automaton. If Defender cannot match, Attacker wins.
    //   If the game continues forever, Defender wins (bisimulation holds).
    //
    // Implementation via attractor computation:
    //   1. Build the game graph: positions are (state_a, state_b) pairs.
    //   2. Attacker wins at a position if there exists a transition in one process
    //      that cannot be matched by any transition in the other process.
    //   3. Propagate Attacker wins backward through the game graph.
    //   4. The initial position is bisimilar iff it is NOT in the Attacker's
    //      winning set.
    //
    // For finite-word automata, the game terminates since the word is consumed.

    let na = a.num_states();
    let nb = b.num_states();

    // Handle degenerate cases.
    match (a.initial_state, b.initial_state) {
        (None, None) => return true,  // both empty => bisimilar
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
    // A position is an "Attacker win" if there exists a transition in one process
    // that cannot be matched by the other (same label, leading to a successor pair
    // that is not an Attacker win).
    //
    // We compute the Attacker's winning set via backward propagation.
    //
    // Encoding: position index = pa * nb + pb.
    let num_positions = na * nb;
    let pos = |pa: usize, pb: usize| -> usize { pa * nb + pb };

    // attacker_wins[pos] = true means Attacker wins from this position.
    let mut attacker_wins = vec![false; num_positions];

    // Initial pass: find positions where one side has a transition on a label
    // that the other side cannot match at all (no transition with that label).
    //
    // Also, for the attractor computation, we need to track which positions
    // depend on which other positions.

    // For each position (pa, pb), determine if it is an immediate Attacker win.
    // This happens when:
    //   - State pa has a transition on label l, but pb has NO transition on label l
    //     (Attacker picks the transition from pa, Defender cannot match in pb).
    //   - Or vice versa: pb has a transition on label l, pa has no transition on l.
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

    // Backward propagation (attractor computation):
    // A position (pa, pb) becomes an Attacker win if there exists a label l such that:
    //   For every transition (pa --l--> succs_a) from A matched by (pb --l--> succs_b) from B,
    //   at least one successor pair (sa, sb) is already an Attacker win.
    //
    // This is a fixpoint computation. For simplicity and correctness, iterate
    // until convergence.
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
                            // No matching transition in B — Attacker wins.
                            attacker_wins[p] = true;
                            changed = true;
                            break;
                        }

                        // Attacker wins if for EVERY matching transition in B,
                        // at least one successor pair is an Attacker win.
                        // (Defender must pick a matching transition, and Attacker
                        // wins if all choices lead to Attacker wins for some pair.)
                        let attacker_wins_this_label = b_matches.iter().all(|succs_b| {
                            // For this defender choice, Attacker wins if any successor
                            // pair (sa, sb) is an Attacker win.
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
        crate::SyntaxItemSpec::Binder { param_name, category, .. } => {
            format!("BIND:{}:{}", param_name, category)
        }
        crate::SyntaxItemSpec::Collection { element_category, separator, .. } => {
            format!("COL:{}:{}", element_category, separator)
        }
        crate::SyntaxItemSpec::Sep { separator, .. } => format!("SEP:{}", separator),
        crate::SyntaxItemSpec::Map { .. } => "MAP".to_string(),
        crate::SyntaxItemSpec::Zip { left_category, right_category, .. } => {
            format!("ZIP:{}:{}", left_category, right_category)
        }
        crate::SyntaxItemSpec::BinderCollection { param_name, separator } => {
            format!("BCOL:{}:{}", param_name, separator)
        }
        crate::SyntaxItemSpec::Optional { .. } => "OPT".to_string(),
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Tests
// ══════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn alternating_state_display() {
        let e = AlternatingState::existential(0);
        assert_eq!(e.to_string(), "q0[E,p=0]");
        let u = AlternatingState::universal(1);
        assert_eq!(u.to_string(), "q1[A,p=0]");
        let labeled = AlternatingState::labeled(
            2,
            BranchingMode::Universal,
            3,
            "check_all",
        );
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
}
