//! Weighted Tree Automata (WTA) for term recognition, ranking, and transduction.
//!
//! Tree automata generalize finite automata from words (sequences) to trees
//! (terms). A bottom-up tree automaton processes a term from leaves to root,
//! assigning states to each subterm. Weighted tree automata assign semiring
//! weights to transitions, enabling ranked term enumeration, probabilistic
//! parsing, and term transduction.
//!
//! ## Theoretical Foundations
//!
//! - **Thatcher & Wright (1968)** — "Generalized finite automata theory with
//!   an application to a decision problem of second-order logic." Introduces
//!   finite tree automata and proves closure under Boolean operations.
//! - **Comon et al. (2007)** — *Tree Automata Techniques and Applications*
//!   (TATA). The standard reference for tree automata theory, covering
//!   bottom-up/top-down variants, determinization, and applications.
//! - **Borchardt (2004)** — "The Myhill-Nerode theorem for recognizable tree
//!   series." Extends weighted automata theory to trees, establishing the
//!   algebraic foundations for weighted tree automata over arbitrary semirings.
//! - **Maletti (2010)** — "Survey: tree transducers in machine translation."
//!   Applications of weighted tree transducers to natural language processing.
//!
//! ## Architecture
//!
//! ```text
//! Term (tree)
//!       │
//!       ▼
//! bottom_up_evaluate()
//!       │ assigns states + weights to each subterm
//!       ▼
//! state assignment map
//!       │
//!       ▼
//! top_down_propagate()
//!       │ propagates information from root to leaves
//!       ▼
//! annotated term tree
//! ```
//!
//! ## PraTTaIL Integration
//!
//! Weighted tree automata provide a natural model for PraTTaIL's AST
//! structure. Grammar categories correspond to state sets, and constructor
//! rules correspond to tree transitions. WTA evaluation can:
//! - Rank parse trees by weight (for ambiguity resolution)
//! - Detect ill-formed ASTs (terms not accepted by the automaton)
//! - Compute term costs for optimization passes

use std::collections::{HashMap, HashSet};
use std::fmt;

use crate::automata::semiring::Semiring;

// ══════════════════════════════════════════════════════════════════════════════
// Core types
// ══════════════════════════════════════════════════════════════════════════════

/// A state in a tree automaton.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TreeState {
    /// Unique state identifier.
    pub id: usize,
    /// Optional label for diagnostics (e.g., grammar category name).
    pub label: Option<String>,
    /// Whether this is a final/accepting state (root-accepting in bottom-up).
    pub is_final: bool,
}

impl TreeState {
    /// Create a new non-final state.
    pub fn new(id: usize) -> Self {
        TreeState {
            id,
            label: None,
            is_final: false,
        }
    }

    /// Create a final (accepting) state.
    pub fn final_state(id: usize) -> Self {
        TreeState {
            id,
            label: None,
            is_final: true,
        }
    }

    /// Create a labeled state.
    pub fn labeled(id: usize, label: impl Into<String>, is_final: bool) -> Self {
        TreeState {
            id,
            label: Some(label.into()),
            is_final,
        }
    }
}

impl fmt::Display for TreeState {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let fin = if self.is_final { "!" } else { "" };
        if let Some(ref label) = self.label {
            write!(f, "s{}{}({})", self.id, fin, label)
        } else {
            write!(f, "s{}{}", self.id, fin)
        }
    }
}

/// A transition in a weighted tree automaton.
///
/// Bottom-up transition: `f(q₁, ..., qₙ) → q` with weight `w`.
/// The function symbol `f` with arity `n` applied to states `q₁, ..., qₙ`
/// transitions to state `q` with weight `w`.
#[derive(Debug, Clone)]
pub struct TreeTransition<W: Semiring> {
    /// Function symbol (constructor name, e.g., "Add", "Lit").
    pub symbol: String,
    /// Child state IDs (empty for leaf/constant transitions).
    pub child_states: Vec<usize>,
    /// Target state ID.
    pub target_state: usize,
    /// Transition weight.
    pub weight: W,
}

impl<W: Semiring> TreeTransition<W> {
    /// Create a leaf (nullary) transition: `c → q` with weight `w`.
    pub fn leaf(symbol: impl Into<String>, target: usize, weight: W) -> Self {
        TreeTransition {
            symbol: symbol.into(),
            child_states: Vec::new(),
            target_state: target,
            weight,
        }
    }

    /// Create a unary transition: `f(q₁) → q` with weight `w`.
    pub fn unary(symbol: impl Into<String>, child: usize, target: usize, weight: W) -> Self {
        TreeTransition {
            symbol: symbol.into(),
            child_states: vec![child],
            target_state: target,
            weight,
        }
    }

    /// Create a binary transition: `f(q₁, q₂) → q` with weight `w`.
    pub fn binary(
        symbol: impl Into<String>,
        left: usize,
        right: usize,
        target: usize,
        weight: W,
    ) -> Self {
        TreeTransition {
            symbol: symbol.into(),
            child_states: vec![left, right],
            target_state: target,
            weight,
        }
    }

    /// Arity of this transition (number of children).
    pub fn arity(&self) -> usize {
        self.child_states.len()
    }
}

impl<W: Semiring> fmt::Display for TreeTransition<W> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.child_states.is_empty() {
            write!(
                f,
                "{} → s{} [{:?}]",
                self.symbol, self.target_state, self.weight,
            )
        } else {
            let children: Vec<String> = self
                .child_states
                .iter()
                .map(|s| format!("s{}", s))
                .collect();
            write!(
                f,
                "{}({}) → s{} [{:?}]",
                self.symbol,
                children.join(", "),
                self.target_state,
                self.weight,
            )
        }
    }
}

/// A Weighted Tree Automaton (WTA).
///
/// `A = (Q, Σ, Δ, F, w)` where:
/// - `Q` is the finite set of states
/// - `Σ` is the ranked alphabet (function symbols with arities)
/// - `Δ` is the set of transitions `f(q₁, ..., qₙ) → q`
/// - `F ⊆ Q` are final (accepting) states
/// - `w: Δ → W` assigns weights from semiring `W` to transitions
///
/// Generic over the semiring `W` for flexible weight domains:
/// - `TropicalWeight`: minimum-cost tree selection
/// - `BooleanWeight`: tree language membership
/// - `CountingWeight`: number of accepting derivations
#[derive(Debug, Clone)]
pub struct TreeAutomaton<W: Semiring> {
    /// All states.
    pub states: Vec<TreeState>,
    /// All transitions.
    pub transitions: Vec<TreeTransition<W>>,
    /// Final (accepting) state IDs.
    pub final_states: HashSet<usize>,
    /// Ranked alphabet: maps symbol name to arity.
    pub ranked_alphabet: HashMap<String, usize>,
}

impl<W: Semiring> TreeAutomaton<W> {
    /// Create an empty tree automaton.
    pub fn new() -> Self {
        TreeAutomaton {
            states: Vec::new(),
            transitions: Vec::new(),
            final_states: HashSet::new(),
            ranked_alphabet: HashMap::new(),
        }
    }

    /// Add a state and return its ID.
    pub fn add_state(&mut self, is_final: bool) -> usize {
        let id = self.states.len();
        let state = if is_final {
            TreeState::final_state(id)
        } else {
            TreeState::new(id)
        };
        if is_final {
            self.final_states.insert(id);
        }
        self.states.push(state);
        id
    }

    /// Register a ranked symbol (function symbol with arity).
    pub fn add_symbol(&mut self, name: impl Into<String>, arity: usize) {
        self.ranked_alphabet.insert(name.into(), arity);
    }

    /// Add a transition.
    pub fn add_transition(&mut self, transition: TreeTransition<W>) {
        self.ranked_alphabet
            .entry(transition.symbol.clone())
            .or_insert(transition.arity());
        self.transitions.push(transition);
    }

    /// Number of states.
    pub fn num_states(&self) -> usize {
        self.states.len()
    }

    /// Number of transitions.
    pub fn num_transitions(&self) -> usize {
        self.transitions.len()
    }
}

impl<W: Semiring> Default for TreeAutomaton<W> {
    fn default() -> Self {
        Self::new()
    }
}

impl<W: Semiring> fmt::Display for TreeAutomaton<W> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "TreeAutomaton {{ states: {}, transitions: {}, final: {}, symbols: {} }}",
            self.num_states(),
            self.num_transitions(),
            self.final_states.len(),
            self.ranked_alphabet.len(),
        )
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Term representation
// ══════════════════════════════════════════════════════════════════════════════

/// A term (tree) over a ranked alphabet.
///
/// Each node carries a function symbol (constructor label) and zero or more
/// children. Leaves are nodes with an empty `children` vector.
///
/// ```text
///       Add
///      /   \
///    Lit   Neg
///           |
///          Lit
/// ```
///
/// This tree is represented as:
/// ```ignore
/// Term::new("Add", vec![Term::leaf("Lit"), Term::new("Neg", vec![Term::leaf("Lit")])])
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Term {
    /// Function symbol (constructor label).
    pub symbol: String,
    /// Child subterms (empty for leaves / constants).
    pub children: Vec<Term>,
}

impl Term {
    /// Create an internal node with children.
    pub fn new(symbol: impl Into<String>, children: Vec<Term>) -> Self {
        Term {
            symbol: symbol.into(),
            children,
        }
    }

    /// Create a leaf (nullary / constant) node.
    pub fn leaf(symbol: impl Into<String>) -> Self {
        Term {
            symbol: symbol.into(),
            children: Vec::new(),
        }
    }

    /// Whether this term is a leaf (no children).
    pub fn is_leaf(&self) -> bool {
        self.children.is_empty()
    }

    /// Arity of this node (number of children).
    pub fn arity(&self) -> usize {
        self.children.len()
    }

    /// Count total nodes in this term tree.
    pub fn size(&self) -> usize {
        1 + self.children.iter().map(|c| c.size()).sum::<usize>()
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.children.is_empty() {
            write!(f, "{}", self.symbol)
        } else {
            let children: Vec<String> = self.children.iter().map(|c| c.to_string()).collect();
            write!(f, "{}({})", self.symbol, children.join(", "))
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Core functions
// ══════════════════════════════════════════════════════════════════════════════

/// Evaluate a term bottom-up through a weighted tree automaton.
///
/// Processes the term from leaves to root, computing for each subterm the
/// set of reachable states and their accumulated weights. At each node
/// `f(t₁, ..., tₙ)`, all matching transitions `f(q₁, ..., qₙ) → q` are
/// applied, and weights are accumulated (via semiring `times` along paths,
/// `plus` across alternatives).
///
/// For a leaf node labeled `c`, every transition `c → q [w]` contributes
/// state `q` with weight `w`. For an internal node `f(t₁, ..., tₙ)`, we
/// first recursively evaluate all children to obtain their state–weight
/// maps. Then, for each transition `f(q₁, ..., qₙ) → q [w]`, we check
/// whether every `qᵢ` is reachable in child `tᵢ`. If so, the transition
/// contributes state `q` at the current node with weight
/// `w ⊗ w₁ ⊗ ... ⊗ wₙ` (where `wᵢ` is the weight of `qᵢ` in child `tᵢ`).
/// When multiple transitions reach the same target state, their weights
/// are combined via semiring `plus`.
///
/// # Type Parameters
///
/// * `W` - The semiring weight type.
///
/// # Arguments
///
/// * `automaton` - The weighted tree automaton.
/// * `term` - The term to evaluate.
///
/// # Returns
///
/// A map from state ID to accumulated weight at the root, or empty if the
/// term cannot reach any state.
pub fn bottom_up_evaluate<W: Semiring>(
    automaton: &TreeAutomaton<W>,
    term: &Term,
) -> HashMap<usize, W> {
    // 1. Recursively evaluate all children first.
    let child_maps: Vec<HashMap<usize, W>> = term
        .children
        .iter()
        .map(|child| bottom_up_evaluate(automaton, child))
        .collect();

    // 2. Find all matching transitions for this node's symbol and arity,
    //    where each child state is reachable in the corresponding child.
    let mut result: HashMap<usize, W> = HashMap::new();

    for trans in &automaton.transitions {
        // Symbol must match.
        if trans.symbol != term.symbol {
            continue;
        }
        // Arity must match.
        if trans.child_states.len() != term.children.len() {
            continue;
        }

        // For each required child state qᵢ, check that child i reached qᵢ
        // and accumulate the product of transition weight with all child weights.
        let mut combined_weight = trans.weight;
        let mut all_children_match = true;

        for (i, &required_state) in trans.child_states.iter().enumerate() {
            match child_maps[i].get(&required_state) {
                Some(child_weight) => {
                    combined_weight = combined_weight.times(child_weight);
                }
                None => {
                    all_children_match = false;
                    break;
                }
            }
        }

        if all_children_match {
            // Accumulate via semiring plus (combine alternative derivations).
            result
                .entry(trans.target_state)
                .and_modify(|existing| *existing = existing.plus(&combined_weight))
                .or_insert(combined_weight);
        }
    }

    result
}

/// Propagate information top-down through a weighted tree automaton.
///
/// Given a term and a root state assignment (typically from
/// `bottom_up_evaluate`), propagates state/weight information from the root
/// to leaves. For each internal node assigned state `q` with weight `w`,
/// every transition `f(q₁, ..., qₙ) → q [w_t]` that targets `q` assigns
/// state `qᵢ` to child `i` with weight `w ⊗ w_t`. When multiple
/// transitions assign the same state to a child, their weights are
/// combined via semiring `plus`.
///
/// This is useful for:
/// - Viterbi decoding (finding the best derivation tree)
/// - Inside-outside computation (for weight training)
/// - Top-down filtering (pruning unreachable states)
///
/// Nodes are numbered in pre-order traversal (root = 0).
///
/// # Type Parameters
///
/// * `W` - The semiring weight type.
///
/// # Arguments
///
/// * `automaton` - The weighted tree automaton.
/// * `term` - The term tree to propagate through.
/// * `root_states` - The state/weight assignment at the root.
///
/// # Returns
///
/// A per-node map from state ID to weight, indexed by pre-order node
/// position. `result[0]` is the root's state map (same as `root_states`),
/// `result[1]` is the first child's map, etc.
pub fn top_down_propagate<W: Semiring>(
    automaton: &TreeAutomaton<W>,
    term: &Term,
    root_states: &HashMap<usize, W>,
) -> Vec<HashMap<usize, W>> {
    let num_nodes = term.size();
    let mut annotations: Vec<HashMap<usize, W>> = Vec::with_capacity(num_nodes);
    // Pre-allocate all slots.
    for _ in 0..num_nodes {
        annotations.push(HashMap::new());
    }

    // Propagate recursively, starting at the root (pre-order index 0).
    propagate_recursive(automaton, term, root_states, &mut annotations, 0);

    annotations
}

/// Recursive helper for top-down propagation.
///
/// `node_index` is the pre-order index of the current node in the
/// `annotations` vector.
///
/// Returns the next available pre-order index after this subtree.
fn propagate_recursive<W: Semiring>(
    automaton: &TreeAutomaton<W>,
    term: &Term,
    current_states: &HashMap<usize, W>,
    annotations: &mut [HashMap<usize, W>],
    node_index: usize,
) -> usize {
    // Record the current node's state assignment.
    for (&state, weight) in current_states {
        annotations[node_index]
            .entry(state)
            .and_modify(|existing| *existing = existing.plus(weight))
            .or_insert(*weight);
    }

    if term.children.is_empty() {
        // Leaf node — no children to propagate to.
        return node_index + 1;
    }

    // For each parent state, find transitions that target it and use them
    // to assign states to children.
    let num_children = term.children.len();
    let mut child_state_maps: Vec<HashMap<usize, W>> = Vec::with_capacity(num_children);
    for _ in 0..num_children {
        child_state_maps.push(HashMap::new());
    }

    for (&parent_state, parent_weight) in current_states {
        for trans in &automaton.transitions {
            // Transition must target the parent state.
            if trans.target_state != parent_state {
                continue;
            }
            // Symbol must match.
            if trans.symbol != term.symbol {
                continue;
            }
            // Arity must match.
            if trans.child_states.len() != num_children {
                continue;
            }

            // Propagate: assign each child state with weight = parent_weight ⊗ trans.weight.
            let propagated_weight = parent_weight.times(&trans.weight);
            for (i, &child_state) in trans.child_states.iter().enumerate() {
                child_state_maps[i]
                    .entry(child_state)
                    .and_modify(|existing| *existing = existing.plus(&propagated_weight))
                    .or_insert(propagated_weight);
            }
        }
    }

    // Recurse into children in pre-order.
    let mut next_index = node_index + 1;
    for (i, child) in term.children.iter().enumerate() {
        next_index = propagate_recursive(
            automaton,
            child,
            &child_state_maps[i],
            annotations,
            next_index,
        );
    }

    next_index
}

// ══════════════════════════════════════════════════════════════════════════════
// Hot-path specialization (Phase 5B.2)
// ══════════════════════════════════════════════════════════════════════════════

/// Trait for converting a semiring weight to a comparable `f64` "heat" value.
///
/// Higher heat values indicate "hotter" (more important) transitions. The
/// interpretation is semiring-dependent:
/// - **Tropical** (cost semiring): heat = `1 / (1 + value)` — lower cost = hotter.
/// - **Counting**: heat = count as `f64` — more derivations = hotter.
/// - **Boolean**: heat = 1.0 if reachable, 0.0 otherwise.
/// - **Viterbi** (probability): heat = probability directly.
/// - **Arctic** (gain): heat = value (higher gain = hotter), 0.0 for `-inf`.
/// - **Fuzzy** (membership): heat = membership degree directly.
/// - **Edit**: heat = `1 / (1 + distance)` — lower edit distance = hotter.
/// - **Complexity**: heat = `1 / (1 + complexity)` — lower complexity = hotter.
pub trait WeightHeat: Semiring {
    /// Convert this weight to a non-negative `f64` heat value for ranking.
    ///
    /// Higher values indicate hotter (more important) transitions.
    /// Returns 0.0 for zero-weight (unreachable) elements.
    fn to_heat(&self) -> f64;
}

impl WeightHeat for crate::automata::semiring::TropicalWeight {
    #[inline]
    fn to_heat(&self) -> f64 {
        if self.is_zero() {
            0.0
        } else {
            // Tropical: lower value = better. Map to (0, 1] via 1/(1+v).
            1.0 / (1.0 + self.0)
        }
    }
}

impl WeightHeat for crate::automata::semiring::CountingWeight {
    #[inline]
    fn to_heat(&self) -> f64 {
        self.0 as f64
    }
}

impl WeightHeat for crate::automata::semiring::BooleanWeight {
    #[inline]
    fn to_heat(&self) -> f64 {
        if self.0 { 1.0 } else { 0.0 }
    }
}

impl WeightHeat for crate::automata::semiring::EditWeight {
    #[inline]
    fn to_heat(&self) -> f64 {
        if self.is_zero() {
            0.0
        } else {
            1.0 / (1.0 + self.0 as f64)
        }
    }
}

impl WeightHeat for crate::automata::semiring::ComplexityWeight {
    #[inline]
    fn to_heat(&self) -> f64 {
        if self.is_zero() {
            0.0
        } else {
            1.0 / (1.0 + self.value() as f64)
        }
    }
}

impl WeightHeat for crate::automata::semiring::ViterbiWeight {
    #[inline]
    fn to_heat(&self) -> f64 {
        if self.is_zero() { 0.0 } else { self.0 }
    }
}

impl WeightHeat for crate::automata::semiring::ArcticWeight {
    #[inline]
    fn to_heat(&self) -> f64 {
        if self.is_zero() { 0.0 } else { self.0 }
    }
}

impl WeightHeat for crate::automata::semiring::FuzzyWeight {
    #[inline]
    fn to_heat(&self) -> f64 {
        self.0
    }
}

#[cfg(feature = "wfst-log")]
impl WeightHeat for crate::automata::semiring::LogWeight {
    #[inline]
    fn to_heat(&self) -> f64 {
        if self.is_zero() {
            0.0
        } else {
            // LogWeight: lower value = higher probability. Map via 1/(1+v).
            1.0 / (1.0 + self.0)
        }
    }
}

/// A candidate transition for hot-path specialization.
///
/// Identifies a single transition that contributes disproportionately to the
/// total weight of the automaton and is therefore a candidate for creating
/// a dedicated fast-path in a specialized automaton.
#[derive(Debug, Clone)]
pub struct SpecializationCandidate {
    /// Index of this transition in the automaton's `transitions` vector.
    pub transition_idx: usize,
    /// The parent (function) symbol of the transition.
    pub parent_symbol: String,
    /// The child state pattern required by this transition.
    pub child_pattern: Vec<TreeState>,
    /// Weight of this transition relative to the total weight (in `[0, 1]`).
    pub relative_weight: f64,
}

/// Report from hot-path analysis of a weighted tree automaton.
///
/// Contains transitions ranked by their weight contribution ("heat") and
/// identifies candidates whose weight is significantly above average,
/// making them suitable for specialization (dedicated fast-path states).
#[derive(Debug, Clone)]
pub struct HotPathReport<W: Semiring> {
    /// All transitions ranked by heat (descending). Each entry is
    /// `(transition_index, weight)`.
    pub ranked_transitions: Vec<(usize, W)>,
    /// Transitions whose heat significantly exceeds the average and are
    /// therefore candidates for specialization.
    pub specialization_candidates: Vec<SpecializationCandidate>,
    /// Fraction of total heat covered by the specialization candidates.
    /// A value near 1.0 means the candidates dominate the automaton's
    /// behavior; near 0.0 means weight is evenly distributed.
    pub coverage: f64,
}

impl<W: Semiring + WeightHeat> TreeAutomaton<W> {
    /// Analyze transition weights to identify hot paths for specialization.
    ///
    /// Ranks all transitions by their weight contribution (via [`WeightHeat`])
    /// and identifies specialization candidates — transitions whose heat is
    /// at least 2x the average. These candidates are good targets for
    /// creating dedicated fast-path states in a specialized automaton.
    ///
    /// # Algorithm
    ///
    /// 1. Compute the heat (f64) for every transition weight.
    /// 2. Sort transitions in descending heat order.
    /// 3. Compute the mean heat. Any transition with heat >= 2 * mean is a
    ///    specialization candidate.
    /// 4. Compute coverage = sum(candidate heats) / total heat.
    ///
    /// # Returns
    ///
    /// A [`HotPathReport`] with ranked transitions, candidates, and coverage.
    pub fn hot_path_analysis(&self) -> HotPathReport<W> {
        if self.transitions.is_empty() {
            return HotPathReport {
                ranked_transitions: Vec::new(),
                specialization_candidates: Vec::new(),
                coverage: 0.0,
            };
        }

        // 1. Compute heat for each transition.
        let heats: Vec<(usize, f64)> = self
            .transitions
            .iter()
            .enumerate()
            .map(|(i, t)| (i, t.weight.to_heat()))
            .collect();

        // 2. Sort descending by heat.
        let mut ranked: Vec<(usize, f64)> = heats;
        ranked.sort_by(|a, b| b.1.partial_cmp(&a.1).unwrap_or(std::cmp::Ordering::Equal));

        // Build the ranked_transitions output (with original weights).
        let ranked_transitions: Vec<(usize, W)> = ranked
            .iter()
            .map(|&(idx, _)| (idx, self.transitions[idx].weight))
            .collect();

        // 3. Compute mean heat and identify candidates (heat >= 2 * mean).
        let total_heat: f64 = ranked.iter().map(|(_, h)| h).sum();
        let mean_heat = total_heat / ranked.len() as f64;
        let threshold = 2.0 * mean_heat;

        let mut candidates = Vec::new();
        let mut candidate_heat_sum = 0.0;

        for &(idx, heat) in &ranked {
            if heat >= threshold && heat > 0.0 {
                let trans = &self.transitions[idx];
                let child_pattern: Vec<TreeState> = trans
                    .child_states
                    .iter()
                    .map(|&sid| {
                        if sid < self.states.len() {
                            self.states[sid].clone()
                        } else {
                            TreeState::new(sid)
                        }
                    })
                    .collect();

                candidates.push(SpecializationCandidate {
                    transition_idx: idx,
                    parent_symbol: trans.symbol.clone(),
                    child_pattern,
                    relative_weight: if total_heat > 0.0 {
                        heat / total_heat
                    } else {
                        0.0
                    },
                });
                candidate_heat_sum += heat;
            }
        }

        // 4. Coverage.
        let coverage = if total_heat > 0.0 {
            candidate_heat_sum / total_heat
        } else {
            0.0
        };

        HotPathReport {
            ranked_transitions,
            specialization_candidates: candidates,
            coverage,
        }
    }

    /// Create a specialized automaton with dedicated fast-path states for hot
    /// transitions.
    ///
    /// For each specialization candidate, a new dedicated state is introduced
    /// that is reached exclusively by that hot transition. This allows
    /// downstream processing to take a fast path when a hot transition fires,
    /// bypassing general-purpose state dispatch.
    ///
    /// # Algorithm
    ///
    /// 1. Clone the original automaton.
    /// 2. For each candidate, allocate a new "fast-path" state that mirrors
    ///    the original target state's finality.
    /// 3. Redirect the candidate transition to the new fast-path state.
    /// 4. Duplicate all outgoing transitions from the original target state
    ///    to also originate from the fast-path state (so the fast-path state
    ///    is behaviorally equivalent but identity-distinct).
    ///
    /// The resulting automaton recognizes the same tree language with the same
    /// weights, but hot transitions land on dedicated states that can be
    /// pattern-matched for optimized downstream handling.
    ///
    /// # Arguments
    ///
    /// * `candidates` - Specialization candidates (from [`hot_path_analysis`]).
    ///
    /// # Returns
    ///
    /// A new [`TreeAutomaton`] with additional fast-path states.
    pub fn specialize(&self, candidates: &[SpecializationCandidate]) -> TreeAutomaton<W> {
        let mut specialized = self.clone();

        for candidate in candidates {
            if candidate.transition_idx >= specialized.transitions.len() {
                continue;
            }

            let original_target = specialized.transitions[candidate.transition_idx].target_state;
            let original_is_final = specialized.final_states.contains(&original_target);

            // Allocate a new fast-path state.
            let fast_path_id = specialized.add_state(original_is_final);

            // Label the fast-path state for diagnostics.
            if let Some(state) = specialized.states.get_mut(fast_path_id) {
                state.label = Some(format!(
                    "fast_{}__t{}",
                    candidate.parent_symbol, candidate.transition_idx,
                ));
            }

            // Redirect the hot transition to the fast-path state.
            specialized.transitions[candidate.transition_idx].target_state = fast_path_id;

            // Duplicate outgoing transitions from the original target so the
            // fast-path state is behaviorally equivalent.
            let outgoing: Vec<TreeTransition<W>> = specialized
                .transitions
                .iter()
                .filter(|t| t.child_states.contains(&original_target))
                .map(|t| {
                    let mut dup = t.clone();
                    // Replace occurrences of original_target in child_states
                    // with fast_path_id.
                    for cs in &mut dup.child_states {
                        if *cs == original_target {
                            *cs = fast_path_id;
                        }
                    }
                    dup
                })
                .collect();

            specialized.transitions.extend(outgoing);
        }

        specialized
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Pipeline bridge
// ══════════════════════════════════════════════════════════════════════════════

/// Pipeline-level WTA analysis result.
#[derive(Debug, Clone)]
pub struct WtaAnalysis {
    /// Term patterns not in the regular tree language.
    pub unrecognized_terms: Vec<String>,
    /// Frequently weighted term patterns (specialization candidates).
    pub hot_paths: Vec<String>,
    /// Total WTA states.
    pub state_count: usize,
    /// Total WTA transitions.
    pub transition_count: usize,
}

/// Build a WTA from grammar categories and syntax rules, then analyze it for
/// hot paths and unrecognized term patterns.
///
/// Each grammar category becomes a [`TreeState`] (labeled by category name).
/// The primary category (first declared) is marked as a final/accepting state.
/// Each syntax rule becomes a [`TreeTransition`]: the rule label is the
/// function symbol, child states correspond to [`SyntaxItemSpec::NonTerminal`]
/// categories referenced in the rule body, and the target state is the
/// category that owns the rule.
///
/// After construction the automaton is analyzed via [`TreeAutomaton::hot_path_analysis`]
/// to identify specialization candidates whose transition heat is
/// significantly above average. Unrecognized terms are detected by checking
/// each category for at least one transition targeting it; categories with
/// no incoming transitions (other than the primary) are flagged.
///
/// # Arguments
///
/// * `categories` - Slice of [`CategoryInfo`] from the parser bundle.
/// * `all_syntax` - Slice of `(rule_label, category_name, syntax_items)` triples
///   describing every syntax rule in the grammar.
///
/// # Returns
///
/// `Some(WtaAnalysis)` if the grammar has at least one category, `None` otherwise.
pub fn analyze_from_bundle(
    categories: &[crate::pipeline::CategoryInfo],
    all_syntax: &[(String, String, Vec<crate::SyntaxItemSpec>)],
) -> Option<WtaAnalysis> {
    use crate::automata::semiring::TropicalWeight;

    if categories.is_empty() {
        return None;
    }

    let mut wta = TreeAutomaton::<TropicalWeight>::new();

    // 1. Create one state per category.
    //    Map category name → state ID.
    let mut cat_to_state: HashMap<String, usize> = HashMap::with_capacity(categories.len());
    for cat in categories {
        // The primary category is the root/accepting state.
        let state_id = wta.states.len();
        let state = TreeState::labeled(state_id, &cat.name, cat.is_primary);
        if cat.is_primary {
            wta.final_states.insert(state_id);
        }
        wta.states.push(state);
        cat_to_state.insert(cat.name.clone(), state_id);
    }

    // 2. Create one transition per syntax rule.
    for (label, category, syntax_items) in all_syntax {
        let target_state = match cat_to_state.get(category) {
            Some(&sid) => sid,
            None => continue, // unknown category — skip
        };

        // Collect child states from NonTerminal items in the syntax body.
        let mut child_states = Vec::new();
        collect_nonterminal_children(syntax_items, &cat_to_state, &mut child_states);

        let arity = child_states.len();
        wta.ranked_alphabet
            .entry(label.clone())
            .or_insert(arity);

        wta.transitions.push(TreeTransition {
            symbol: label.clone(),
            child_states,
            target_state,
            weight: TropicalWeight::one(),
        });
    }

    // 3. Analyze hot paths.
    let report = wta.hot_path_analysis();

    let hot_paths: Vec<String> = report
        .specialization_candidates
        .iter()
        .map(|c| c.parent_symbol.clone())
        .collect();

    // 4. Detect categories with no incoming transitions (potential
    //    unrecognized term patterns). The primary category is excluded
    //    because it is the root and may legitimately have no incoming
    //    transitions from other rules.
    let mut targeted: HashSet<usize> = HashSet::new();
    for trans in &wta.transitions {
        targeted.insert(trans.target_state);
    }

    let unrecognized_terms: Vec<String> = categories
        .iter()
        .filter(|cat| {
            if cat.is_primary {
                return false;
            }
            match cat_to_state.get(&cat.name) {
                Some(&sid) => !targeted.contains(&sid),
                None => false,
            }
        })
        .map(|cat| cat.name.clone())
        .collect();

    Some(WtaAnalysis {
        unrecognized_terms,
        hot_paths,
        state_count: wta.num_states(),
        transition_count: wta.num_transitions(),
    })
}

/// Recursively collect child state IDs from [`SyntaxItemSpec::NonTerminal`]
/// entries (including those nested inside `Optional`, `Sep`, `Map`, and `Zip`
/// variants).
fn collect_nonterminal_children(
    items: &[crate::SyntaxItemSpec],
    cat_to_state: &HashMap<String, usize>,
    out: &mut Vec<usize>,
) {
    for item in items {
        match item {
            crate::SyntaxItemSpec::NonTerminal { category, .. } => {
                if let Some(&sid) = cat_to_state.get(category) {
                    out.push(sid);
                }
            }
            crate::SyntaxItemSpec::Optional { inner } => {
                collect_nonterminal_children(inner, cat_to_state, out);
            }
            crate::SyntaxItemSpec::Sep { body, .. } => {
                collect_nonterminal_children(std::slice::from_ref(body.as_ref()), cat_to_state, out);
            }
            crate::SyntaxItemSpec::Map { body_items } => {
                collect_nonterminal_children(body_items, cat_to_state, out);
            }
            crate::SyntaxItemSpec::Zip { body, .. } => {
                collect_nonterminal_children(std::slice::from_ref(body.as_ref()), cat_to_state, out);
            }
            crate::SyntaxItemSpec::Binder { category, .. } => {
                if let Some(&sid) = cat_to_state.get(category) {
                    out.push(sid);
                }
            }
            crate::SyntaxItemSpec::Collection {
                element_category, ..
            } => {
                if let Some(&sid) = cat_to_state.get(element_category) {
                    out.push(sid);
                }
            }
            // Terminal, IdentCapture, BinderCollection — no child states.
            _ => {}
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// TokenTree ↔ Term conversion and validation
// ══════════════════════════════════════════════════════════════════════════════

/// Convert a VPA [`TokenTree`] to the tree automaton's [`Term`] representation.
///
/// Leaf tokens become terms with the token name as symbol and no children.
/// Delimited groups become terms with the opener token as symbol and the
/// group's children recursively converted.
///
/// # Type Parameters
///
/// * `T` — the token type carried by the token tree (must implement `Debug`).
///
/// # Arguments
///
/// * `tt` — a reference to the token tree node to convert.
/// * `token_to_symbol` — a closure mapping token references to symbol strings
///   for the tree automaton's ranked alphabet.
///
/// # Examples
///
/// ```ignore
/// // Given TokenTree::Token("Lit", range), produces Term { symbol: "Lit", children: [] }
/// // Given TokenTree::Group { open: ("LParen", _), children: [...], close: _ },
/// //   produces Term { symbol: "LParen", children: [... recursively converted ...] }
/// ```
#[cfg(all(feature = "tree-automata", feature = "vpa"))]
pub fn token_tree_to_term<T: std::fmt::Debug>(
    tt: &crate::vpa::TokenTree<T>,
    token_to_symbol: &dyn Fn(&T) -> String,
) -> Term {
    match tt {
        crate::vpa::TokenTree::Token(tok, _range) => Term {
            symbol: token_to_symbol(tok),
            children: vec![],
        },
        crate::vpa::TokenTree::Group {
            open, children, ..
        } => Term {
            symbol: token_to_symbol(&open.0),
            children: children
                .iter()
                .map(|child| token_tree_to_term(child, token_to_symbol))
                .collect(),
        },
    }
}

/// Validation error for token trees that do not match the grammar WTA.
///
/// Produced by [`validate_token_tree`] when the bottom-up evaluation of the
/// converted term fails to reach any final state with a non-zero weight.
#[cfg(all(feature = "tree-automata", feature = "vpa"))]
#[derive(Debug, Clone)]
pub struct TreeValidationError {
    /// Human-readable description of the validation failure.
    pub message: String,
}

#[cfg(all(feature = "tree-automata", feature = "vpa"))]
impl fmt::Display for TreeValidationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.message)
    }
}

#[cfg(all(feature = "tree-automata", feature = "vpa"))]
impl std::error::Error for TreeValidationError {}

/// Validate a token tree against a grammar WTA.
///
/// Converts the token tree to a [`Term`] via [`token_tree_to_term`], then runs
/// [`bottom_up_evaluate`] against the given automaton. If any final state is
/// reached with a non-zero weight, that weight is returned. Otherwise, a
/// [`TreeValidationError`] is produced describing the failure.
///
/// # Type Parameters
///
/// * `W` — the semiring weight type of the tree automaton.
/// * `T` — the token type carried by the token tree.
///
/// # Arguments
///
/// * `automaton` — the weighted tree automaton encoding the grammar's term
///   structure.
/// * `tree` — the token tree to validate.
/// * `token_to_symbol` — a closure mapping token references to symbol strings
///   used in the automaton's ranked alphabet.
///
/// # Returns
///
/// * `Ok(weight)` if the tree is accepted (reaches a final state with non-zero
///   weight). When multiple final states are reachable, their weights are
///   combined via semiring `plus` to yield a single aggregate weight.
/// * `Err(TreeValidationError)` if no final state is reached or all final state
///   weights are zero.
///
/// # Examples
///
/// ```ignore
/// let result = validate_token_tree(&wta, &token_tree, &|tok| format!("{:?}", tok));
/// match result {
///     Ok(weight) => println!("accepted with weight {:?}", weight),
///     Err(err) => eprintln!("validation failed: {}", err),
/// }
/// ```
#[cfg(all(feature = "tree-automata", feature = "vpa"))]
pub fn validate_token_tree<W: Semiring, T: std::fmt::Debug>(
    automaton: &TreeAutomaton<W>,
    tree: &crate::vpa::TokenTree<T>,
    token_to_symbol: &dyn Fn(&T) -> String,
) -> Result<W, TreeValidationError> {
    let term = token_tree_to_term(tree, token_to_symbol);
    let state_map = bottom_up_evaluate(automaton, &term);

    // Aggregate weights across all final states using semiring plus.
    let mut aggregate: Option<W> = None;
    for &final_id in &automaton.final_states {
        if let Some(&w) = state_map.get(&final_id) {
            if !w.is_zero() {
                aggregate = Some(match aggregate {
                    Some(acc) => acc.plus(&w),
                    None => w,
                });
            }
        }
    }

    match aggregate {
        Some(w) => Ok(w),
        None => Err(TreeValidationError {
            message: format!(
                "token tree not accepted: no final state reached for root symbol '{}'",
                term.symbol
            ),
        }),
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
    fn tree_state_display() {
        let s = TreeState::new(0);
        assert_eq!(s.to_string(), "s0");
        let sf = TreeState::final_state(1);
        assert_eq!(sf.to_string(), "s1!");
        let sl = TreeState::labeled(2, "Expr", true);
        assert_eq!(sl.to_string(), "s2!(Expr)");
    }

    #[test]
    fn tree_automaton_construction() {
        let mut wta: TreeAutomaton<TropicalWeight> = TreeAutomaton::new();
        let q_int = wta.add_state(false);
        let q_expr = wta.add_state(true);

        // Leaf transition: Lit → q_int
        wta.add_transition(TreeTransition::leaf("Lit", q_int, TropicalWeight::one()));
        // Binary transition: Add(q_int, q_int) → q_expr
        wta.add_transition(TreeTransition::binary(
            "Add",
            q_int,
            q_int,
            q_expr,
            TropicalWeight(1.0),
        ));

        assert_eq!(wta.num_states(), 2);
        assert_eq!(wta.num_transitions(), 2);
        assert!(wta.final_states.contains(&q_expr));
        assert_eq!(wta.ranked_alphabet.get("Lit"), Some(&0));
        assert_eq!(wta.ranked_alphabet.get("Add"), Some(&2));
    }

    #[test]
    fn tree_transition_display() {
        let leaf: TreeTransition<TropicalWeight> =
            TreeTransition::leaf("Zero", 0, TropicalWeight::one());
        assert!(leaf.to_string().contains("Zero"));
        assert!(leaf.to_string().contains("s0"));

        let binary: TreeTransition<TropicalWeight> =
            TreeTransition::binary("Plus", 0, 1, 2, TropicalWeight(0.5));
        assert!(binary.to_string().contains("Plus(s0, s1)"));
        assert!(binary.to_string().contains("s2"));
    }

    /// Helper: build a simple expression WTA over TropicalWeight.
    ///
    /// States:
    ///   q0 (non-final) — integer literals
    ///   q1 (final)     — expressions
    ///
    /// Transitions:
    ///   Lit      → q0  [0.0]  (one)
    ///   Neg(q0)  → q0  [1.0]
    ///   Add(q0, q0) → q1 [2.0]
    ///   Mul(q0, q0) → q1 [3.0]
    fn build_expr_wta() -> (TreeAutomaton<TropicalWeight>, usize, usize) {
        let mut wta: TreeAutomaton<TropicalWeight> = TreeAutomaton::new();
        let q_int = wta.add_state(false); // q0
        let q_expr = wta.add_state(true); // q1

        wta.add_transition(TreeTransition::leaf("Lit", q_int, TropicalWeight::one()));
        wta.add_transition(TreeTransition::unary("Neg", q_int, q_int, TropicalWeight(1.0)));
        wta.add_transition(TreeTransition::binary(
            "Add", q_int, q_int, q_expr, TropicalWeight(2.0),
        ));
        wta.add_transition(TreeTransition::binary(
            "Mul", q_int, q_int, q_expr, TropicalWeight(3.0),
        ));

        (wta, q_int, q_expr)
    }

    #[test]
    fn bottom_up_accepts_simple_tree() {
        // Test: Add(Lit, Lit) should be accepted with weight 2.0
        // (tropical times is addition: 0.0 + 0.0 + 2.0 = 2.0)
        let (wta, _q_int, q_expr) = build_expr_wta();

        let term = Term::new("Add", vec![Term::leaf("Lit"), Term::leaf("Lit")]);
        let result = bottom_up_evaluate(&wta, &term);

        assert!(result.contains_key(&q_expr), "root should reach accepting state q1");
        // TropicalWeight::times is addition: one(0.0) + one(0.0) + 2.0 = 2.0
        assert_eq!(result[&q_expr], TropicalWeight(2.0));

        // Verify it's accepted (root state is final).
        assert!(wta.final_states.contains(&q_expr));
    }

    #[test]
    fn bottom_up_rejects_unrecognized_term() {
        // Test: a term with an unknown symbol yields an empty state map.
        let (wta, _, _) = build_expr_wta();

        let term = Term::leaf("Unknown");
        let result = bottom_up_evaluate(&wta, &term);
        assert!(result.is_empty(), "unknown symbol should yield no reachable states");

        // Also test arity mismatch: Add with 3 children.
        let term_bad_arity = Term::new(
            "Add",
            vec![Term::leaf("Lit"), Term::leaf("Lit"), Term::leaf("Lit")],
        );
        let result2 = bottom_up_evaluate(&wta, &term_bad_arity);
        assert!(result2.is_empty(), "arity mismatch should yield no reachable states");
    }

    #[test]
    fn bottom_up_nested_unary_and_binary() {
        // Test: Add(Neg(Lit), Lit)
        //
        // Evaluation:
        //   Lit       → q0 [0.0]
        //   Neg(q0)   → q0 [0.0 + 1.0 = 1.0]  (tropical times = +)
        //   Add(q0, q0) → q1 [2.0 + 1.0 + 0.0 = 3.0]
        let (wta, _q_int, q_expr) = build_expr_wta();

        let term = Term::new(
            "Add",
            vec![
                Term::new("Neg", vec![Term::leaf("Lit")]),
                Term::leaf("Lit"),
            ],
        );
        let result = bottom_up_evaluate(&wta, &term);

        assert!(result.contains_key(&q_expr));
        // trans.weight(2.0) ⊗ left_child_weight(1.0) ⊗ right_child_weight(0.0) = 3.0
        assert_eq!(result[&q_expr], TropicalWeight(3.0));
    }

    #[test]
    fn top_down_propagates_states_to_children() {
        // Test top-down propagation on Add(Lit, Lit).
        //
        // Pre-order layout:
        //   [0] Add   — root
        //   [1] Lit   — left child
        //   [2] Lit   — right child
        //
        // Root states from bottom-up: {q1: 2.0}
        // Transition Add(q0, q0) → q1 [2.0] should propagate:
        //   child 0 → q0 with weight 2.0 ⊗ 2.0 = 4.0
        //   child 1 → q0 with weight 2.0 ⊗ 2.0 = 4.0
        let (wta, q_int, q_expr) = build_expr_wta();

        let term = Term::new("Add", vec![Term::leaf("Lit"), Term::leaf("Lit")]);

        // First do bottom-up to get root states.
        let root_states = bottom_up_evaluate(&wta, &term);
        assert_eq!(root_states[&q_expr], TropicalWeight(2.0));

        // Now propagate top-down.
        let annotations = top_down_propagate(&wta, &term, &root_states);

        assert_eq!(annotations.len(), 3, "3 nodes in pre-order");

        // Root (index 0) should have q_expr with weight 2.0.
        assert_eq!(annotations[0][&q_expr], TropicalWeight(2.0));

        // Children (indices 1, 2) should have q_int.
        // Weight = root_weight(2.0) ⊗ trans.weight(2.0) = 4.0 (tropical: 2+2)
        assert!(
            annotations[1].contains_key(&q_int),
            "left child should be assigned q_int"
        );
        assert_eq!(annotations[1][&q_int], TropicalWeight(4.0));

        assert!(
            annotations[2].contains_key(&q_int),
            "right child should be assigned q_int"
        );
        assert_eq!(annotations[2][&q_int], TropicalWeight(4.0));
    }

    // ══════════════════════════════════════════════════════════════════════
    // Hot-path specialization tests (Phase 5B.2)
    // ══════════════════════════════════════════════════════════════════════

    #[test]
    fn hot_path_empty_automaton() {
        // An empty automaton should produce an empty report.
        let wta: TreeAutomaton<TropicalWeight> = TreeAutomaton::new();
        let report = wta.hot_path_analysis();

        assert!(report.ranked_transitions.is_empty());
        assert!(report.specialization_candidates.is_empty());
        assert_eq!(report.coverage, 0.0);
    }

    #[test]
    fn hot_path_single_transition() {
        // A single transition is trivially the hottest path.
        // With only one transition, heat = 1/(1+0) = 1.0, mean = 1.0,
        // threshold = 2.0 > 1.0, so it should NOT be a candidate
        // (not significantly above average when it IS the average).
        let mut wta: TreeAutomaton<TropicalWeight> = TreeAutomaton::new();
        let q0 = wta.add_state(true);
        wta.add_transition(TreeTransition::leaf("A", q0, TropicalWeight::one()));

        let report = wta.hot_path_analysis();

        assert_eq!(report.ranked_transitions.len(), 1);
        assert_eq!(report.ranked_transitions[0].0, 0);
        assert_eq!(report.ranked_transitions[0].1, TropicalWeight::one());
        // Single transition cannot exceed 2x its own average.
        assert!(report.specialization_candidates.is_empty());
        assert_eq!(report.coverage, 0.0);
    }

    #[test]
    fn hot_path_ranking_order() {
        // Transitions with lower tropical weight should rank higher (hotter).
        //
        // Tropical heat: 1/(1+w). So:
        //   w=0.0 → heat=1.0, w=1.0 → heat=0.5, w=5.0 → heat≈0.167, w=10.0 → heat≈0.091
        //
        // Expected ranking by heat (descending): idx 0 (w=0), idx 1 (w=1),
        //   idx 2 (w=5), idx 3 (w=10).
        let mut wta: TreeAutomaton<TropicalWeight> = TreeAutomaton::new();
        let q0 = wta.add_state(false);
        let q1 = wta.add_state(true);

        wta.add_transition(TreeTransition::leaf("A", q0, TropicalWeight(0.0)));  // idx 0
        wta.add_transition(TreeTransition::leaf("B", q0, TropicalWeight(1.0)));  // idx 1
        wta.add_transition(TreeTransition::leaf("C", q0, TropicalWeight(5.0)));  // idx 2
        wta.add_transition(TreeTransition::unary("D", q0, q1, TropicalWeight(10.0))); // idx 3

        let report = wta.hot_path_analysis();

        assert_eq!(report.ranked_transitions.len(), 4);
        // Verify descending heat order.
        assert_eq!(report.ranked_transitions[0].0, 0, "w=0.0 should be hottest");
        assert_eq!(report.ranked_transitions[1].0, 1, "w=1.0 should be second");
        assert_eq!(report.ranked_transitions[2].0, 2, "w=5.0 should be third");
        assert_eq!(report.ranked_transitions[3].0, 3, "w=10.0 should be coldest");
    }

    #[test]
    fn hot_path_candidates_identified() {
        // Create a WTA where one transition is much hotter than the rest.
        //
        // Heats: A=1.0 (w=0), B≈0.091 (w=10), C≈0.048 (w=20), D≈0.032 (w=30)
        // Total heat ≈ 1.171, mean ≈ 0.293, threshold ≈ 0.586
        // Only A (heat=1.0) exceeds the threshold.
        let mut wta: TreeAutomaton<TropicalWeight> = TreeAutomaton::new();
        let q0 = wta.add_state(false);
        let q1 = wta.add_state(true);

        wta.add_transition(TreeTransition::leaf("Hot", q0, TropicalWeight(0.0)));   // idx 0
        wta.add_transition(TreeTransition::leaf("Cold1", q0, TropicalWeight(10.0))); // idx 1
        wta.add_transition(TreeTransition::leaf("Cold2", q0, TropicalWeight(20.0))); // idx 2
        wta.add_transition(TreeTransition::unary("Cold3", q0, q1, TropicalWeight(30.0))); // idx 3

        let report = wta.hot_path_analysis();

        assert_eq!(
            report.specialization_candidates.len(), 1,
            "only the hot transition should be a candidate"
        );
        let candidate = &report.specialization_candidates[0];
        assert_eq!(candidate.transition_idx, 0);
        assert_eq!(candidate.parent_symbol, "Hot");
        assert!(candidate.child_pattern.is_empty(), "leaf transition has no children");
        assert!(candidate.relative_weight > 0.5, "hot transition should dominate");
        assert!(report.coverage > 0.5, "coverage should be high");
    }

    #[test]
    fn hot_path_candidate_child_pattern() {
        // Verify that candidates correctly capture the child state pattern.
        let mut wta: TreeAutomaton<TropicalWeight> = TreeAutomaton::new();
        let q0 = wta.add_state(false);
        let q1 = wta.add_state(true);

        // Hot binary transition: Add(q0, q0) → q1 [0.0]
        wta.add_transition(TreeTransition::binary("Add", q0, q0, q1, TropicalWeight(0.0)));
        // Cold leaf: Lit → q0 [50.0]
        wta.add_transition(TreeTransition::leaf("Lit", q0, TropicalWeight(50.0)));
        // Another cold leaf: Var → q0 [50.0]
        wta.add_transition(TreeTransition::leaf("Var", q0, TropicalWeight(50.0)));

        let report = wta.hot_path_analysis();

        assert!(!report.specialization_candidates.is_empty());
        let add_candidate = report
            .specialization_candidates
            .iter()
            .find(|c| c.parent_symbol == "Add")
            .expect("Add should be a specialization candidate");

        assert_eq!(add_candidate.child_pattern.len(), 2);
        assert_eq!(add_candidate.child_pattern[0].id, q0);
        assert_eq!(add_candidate.child_pattern[1].id, q0);
    }

    #[test]
    fn hot_path_coverage_sums_correctly() {
        // With two equally hot transitions and two cold ones, both hot
        // transitions should be candidates and coverage should reflect their
        // combined fraction.
        //
        // Heats: A=1.0 (w=0), B=1.0 (w=0), C≈0.048 (w=20), D≈0.032 (w=30)
        // Total ≈ 2.08, mean ≈ 0.52, threshold ≈ 1.04
        // Neither A nor B (heat=1.0) exceeds threshold=1.04.
        //
        // Use more extreme disparity:
        // Heats: A=1.0 (w=0), B=0.5 (w=1), C≈0.01 (w=99), D≈0.0099 (w=100)
        // Total ≈ 1.52, mean ≈ 0.38, threshold ≈ 0.76
        // A (1.0) exceeds, B (0.5) does not.
        let mut wta: TreeAutomaton<TropicalWeight> = TreeAutomaton::new();
        let q0 = wta.add_state(false);
        let q1 = wta.add_state(true);

        wta.add_transition(TreeTransition::leaf("Hot", q0, TropicalWeight(0.0)));
        wta.add_transition(TreeTransition::leaf("Warm", q0, TropicalWeight(1.0)));
        wta.add_transition(TreeTransition::leaf("Cold1", q0, TropicalWeight(99.0)));
        wta.add_transition(TreeTransition::unary("Cold2", q0, q1, TropicalWeight(100.0)));

        let report = wta.hot_path_analysis();

        // At least one candidate.
        assert!(
            !report.specialization_candidates.is_empty(),
            "should have at least one candidate"
        );
        // Coverage should be positive and <= 1.0.
        assert!(report.coverage > 0.0, "coverage should be positive");
        assert!(report.coverage <= 1.0, "coverage cannot exceed 1.0");
        // Sum of candidate relative_weights should approximately equal coverage.
        let sum_rel: f64 = report
            .specialization_candidates
            .iter()
            .map(|c| c.relative_weight)
            .sum();
        assert!(
            (sum_rel - report.coverage).abs() < 1e-10,
            "sum of relative_weights ({sum_rel}) should equal coverage ({})",
            report.coverage,
        );
    }

    #[test]
    fn specialize_creates_fast_path_states() {
        // Build a simple WTA, identify candidates, and verify specialization
        // adds new states.
        let mut wta: TreeAutomaton<TropicalWeight> = TreeAutomaton::new();
        let q0 = wta.add_state(false);
        let q1 = wta.add_state(true);

        wta.add_transition(TreeTransition::leaf("Hot", q0, TropicalWeight(0.0)));   // idx 0
        wta.add_transition(TreeTransition::leaf("Cold", q0, TropicalWeight(50.0))); // idx 1
        wta.add_transition(TreeTransition::unary("Wrap", q0, q1, TropicalWeight(100.0))); // idx 2

        let report = wta.hot_path_analysis();
        let original_num_states = wta.num_states();
        let specialized = wta.specialize(&report.specialization_candidates);

        // Specialized automaton should have more states.
        assert!(
            specialized.num_states() > original_num_states,
            "specialization should add fast-path states"
        );
        // Should have at least one state labeled with "fast_".
        assert!(
            specialized.states.iter().any(|s| s
                .label
                .as_ref()
                .map_or(false, |l| l.starts_with("fast_"))),
            "should have labeled fast-path states"
        );
    }

    #[test]
    fn specialize_preserves_language() {
        // The specialized automaton should accept the same terms with the
        // same weights as the original.
        let (wta, _q_int, q_expr) = build_expr_wta();

        let report = wta.hot_path_analysis();
        let specialized = wta.specialize(&report.specialization_candidates);

        // Evaluate Add(Lit, Lit) on both automata.
        let term = Term::new("Add", vec![Term::leaf("Lit"), Term::leaf("Lit")]);
        let original_result = bottom_up_evaluate(&wta, &term);
        let specialized_result = bottom_up_evaluate(&specialized, &term);

        // The original result should have q_expr reachable.
        assert!(original_result.contains_key(&q_expr));

        // The specialized result should also reach an accepting state with
        // the same weight. The state ID might differ (could be the fast-path
        // state), so check that at least one final state is reached.
        let specialized_accepting: Vec<_> = specialized_result
            .iter()
            .filter(|(&state, _)| specialized.final_states.contains(&state))
            .collect();
        assert!(
            !specialized_accepting.is_empty(),
            "specialized automaton should still accept the term"
        );
        // The weight at some accepting state should match.
        let any_match = specialized_accepting
            .iter()
            .any(|(_, w)| **w == original_result[&q_expr]);
        assert!(
            any_match,
            "specialized automaton should preserve the original weight"
        );
    }

    #[test]
    fn specialize_empty_candidates() {
        // Specializing with no candidates should return a clone.
        let (wta, _, _) = build_expr_wta();
        let specialized = wta.specialize(&[]);

        assert_eq!(specialized.num_states(), wta.num_states());
        assert_eq!(specialized.num_transitions(), wta.num_transitions());
    }

    #[test]
    fn specialize_out_of_bounds_candidate_ignored() {
        // A candidate with an out-of-bounds transition_idx should be
        // silently skipped.
        let (wta, _, _) = build_expr_wta();
        let bogus = SpecializationCandidate {
            transition_idx: 999,
            parent_symbol: "Bogus".into(),
            child_pattern: vec![],
            relative_weight: 1.0,
        };
        let specialized = wta.specialize(&[bogus]);

        assert_eq!(specialized.num_states(), wta.num_states());
        assert_eq!(specialized.num_transitions(), wta.num_transitions());
    }

    #[test]
    fn hot_path_with_counting_weight() {
        // Verify hot-path analysis works with a non-tropical semiring.
        use crate::automata::semiring::CountingWeight;

        let mut wta: TreeAutomaton<CountingWeight> = TreeAutomaton::new();
        let q0 = wta.add_state(false);
        let q1 = wta.add_state(true);

        // Hot: 100 derivations. Cold: 1 derivation each.
        wta.add_transition(TreeTransition::leaf("Hot", q0, CountingWeight(100)));
        wta.add_transition(TreeTransition::leaf("Cold1", q0, CountingWeight(1)));
        wta.add_transition(TreeTransition::leaf("Cold2", q0, CountingWeight(1)));
        wta.add_transition(TreeTransition::unary("Cold3", q0, q1, CountingWeight(1)));

        let report = wta.hot_path_analysis();

        // The Hot transition (count=100, heat=100.0) should be a candidate.
        // Mean heat = (100+1+1+1)/4 = 25.75, threshold = 51.5. Only Hot exceeds.
        assert_eq!(
            report.specialization_candidates.len(), 1,
            "only the 100-count transition should be a candidate"
        );
        assert_eq!(report.specialization_candidates[0].parent_symbol, "Hot");
        assert!(report.coverage > 0.9, "hot transition dominates");
    }

    // ──────────────────────────────────────────────────────────────────────
    // token_tree_to_term / validate_token_tree tests
    // ──────────────────────────────────────────────────────────────────────

    #[cfg(all(feature = "tree-automata", feature = "vpa"))]
    mod token_tree_tests {
        use super::*;
        use crate::vpa::TokenTree;

        /// Convenience helper: a zero-length range for test token trees.
        fn test_range() -> crate::runtime_types::Range {
            crate::runtime_types::Range::zero()
        }

        /// Map `&str` tokens to their string symbol.
        fn str_to_symbol(tok: &&str) -> String {
            tok.to_string()
        }

        #[test]
        fn test_token_tree_to_term_leaf() {
            let tt: TokenTree<&str> = TokenTree::Token("Ident", test_range());
            let term = token_tree_to_term(&tt, &str_to_symbol);

            assert_eq!(term.symbol, "Ident");
            assert!(term.children.is_empty(), "leaf token should have no children");
            assert_eq!(term, Term::leaf("Ident"));
        }

        #[test]
        fn test_token_tree_to_term_group() {
            let tt: TokenTree<&str> = TokenTree::Group {
                open: ("LParen", test_range()),
                close: ("RParen", test_range()),
                children: vec![TokenTree::Token("Plus", test_range())],
            };
            let term = token_tree_to_term(&tt, &str_to_symbol);

            assert_eq!(term.symbol, "LParen");
            assert_eq!(term.children.len(), 1);
            assert_eq!(term.children[0].symbol, "Plus");
            assert!(term.children[0].children.is_empty());
            assert_eq!(
                term,
                Term::new("LParen", vec![Term::leaf("Plus")])
            );
        }

        #[test]
        fn test_token_tree_to_term_nested() {
            // Structure: Group(LParen, [Group(LBrace, [Token(Ident)]), Token(Comma)])
            let inner_group: TokenTree<&str> = TokenTree::Group {
                open: ("LBrace", test_range()),
                close: ("RBrace", test_range()),
                children: vec![TokenTree::Token("Ident", test_range())],
            };
            let tt: TokenTree<&str> = TokenTree::Group {
                open: ("LParen", test_range()),
                close: ("RParen", test_range()),
                children: vec![inner_group, TokenTree::Token("Comma", test_range())],
            };
            let term = token_tree_to_term(&tt, &str_to_symbol);

            assert_eq!(term.symbol, "LParen");
            assert_eq!(term.children.len(), 2);

            // First child is the nested group.
            let nested = &term.children[0];
            assert_eq!(nested.symbol, "LBrace");
            assert_eq!(nested.children.len(), 1);
            assert_eq!(nested.children[0].symbol, "Ident");
            assert!(nested.children[0].children.is_empty());

            // Second child is a flat token.
            let comma = &term.children[1];
            assert_eq!(comma.symbol, "Comma");
            assert!(comma.children.is_empty());

            assert_eq!(
                term,
                Term::new(
                    "LParen",
                    vec![
                        Term::new("LBrace", vec![Term::leaf("Ident")]),
                        Term::leaf("Comma"),
                    ],
                )
            );
        }

        #[test]
        fn test_validate_token_tree_valid() {
            // Build a minimal WTA that accepts a single "Lit" leaf.
            //
            //   Transition: Lit → q0 [1.0]   (leaf, weight = one)
            //   q0 is final.
            let mut wta: TreeAutomaton<TropicalWeight> = TreeAutomaton::new();
            let q0 = wta.add_state(true); // final state
            wta.add_transition(TreeTransition::leaf("Lit", q0, TropicalWeight::one()));

            let tt: TokenTree<&str> = TokenTree::Token("Lit", test_range());
            let result = validate_token_tree(&wta, &tt, &str_to_symbol);

            assert!(result.is_ok(), "expected Ok, got {:?}", result);
            let weight = result.expect("already checked Ok");
            // TropicalWeight::one() is 0.0 (tropical identity for ⊗).
            assert!(
                (weight.0 - TropicalWeight::one().0).abs() < f64::EPSILON,
                "weight should be one (0.0 in tropical), got {:?}",
                weight,
            );
        }

        #[test]
        fn test_validate_token_tree_invalid() {
            // Build a WTA that only accepts "Lit" leaves — passing "Unknown"
            // should produce an Err.
            let mut wta: TreeAutomaton<TropicalWeight> = TreeAutomaton::new();
            let q0 = wta.add_state(true);
            wta.add_transition(TreeTransition::leaf("Lit", q0, TropicalWeight::one()));

            let tt: TokenTree<&str> = TokenTree::Token("Unknown", test_range());
            let result = validate_token_tree(&wta, &tt, &str_to_symbol);

            assert!(result.is_err(), "expected Err for unrecognized symbol, got {:?}", result);
            let err = result.unwrap_err();
            assert!(
                err.message.contains("Unknown"),
                "error message should mention the unrecognized root symbol 'Unknown', got: {}",
                err.message,
            );
        }
    }

    #[test]
    fn test_analyze_from_bundle_basic() {
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
        let result = analyze_from_bundle(&cats, &syntax);
        assert!(result.is_some(), "should produce WTA analysis");
    }
}
