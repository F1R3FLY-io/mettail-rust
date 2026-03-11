//! Weighted Multi-Tape Automata (Module 8).
//!
//! Provides synchronized multi-stream computation over `K` input tapes. A
//! weighted multi-tape automaton generalizes WFSTs (K=2) to an arbitrary
//! number of synchronized tapes. Each transition reads one symbol (or epsilon)
//! from each of the K tapes simultaneously, with an associated semiring weight.
//!
//! ## Motivation
//!
//! Multi-channel receives in Rholang/MeTTaIL —
//! `for (@x <- ch1, @y <- ch2) { ... }` — naturally map to multi-tape automata:
//! ch1 becomes tape 1, ch2 becomes tape 2. The automaton synchronizes
//! consumption across channels, with semiring weights encoding priority,
//! probability, or cost.
//!
//! ## Key Operations (Kempe 2004)
//!
//! - **pair(a1, a2)**: Combine two single-tape automata into a 2-tape automaton
//!   via product construction.
//! - **project(tape_idx)**: Extract single-tape behavior by projecting onto one
//!   tape (other tapes become epsilon).
//! - **auto_intersect(i, j)**: Constrain tapes `i` and `j` to share identical
//!   label sequences.
//! - **multi_tape_intersect(a, b)**: K-tape product construction with
//!   synchronized tape labels on all K tapes.
//! - **evaluate(inputs)**: Evaluate the automaton on K concrete input streams,
//!   returning the total weight of all accepting runs via BFS over
//!   `(state, positions_per_tape)` configurations.
//!
//! ## Theoretical Foundations
//!
//! - **Kempe (2004)** — *"Weighted Multi-Tape Automata and Transducers for NLP."*
//!   Defines the algebraic framework for K-tape weighted automata, including the
//!   `pair`, `project`, and `auto_intersect` operations used here.
//! - **Rabin & Scott (1959)** — The product construction underlying `pair` and
//!   `multi_tape_intersect` is the standard Rabin-Scott cross-product, extended
//!   to K tapes with semiring weight multiplication.
//!
//! ## Feature Gate
//!
//! This module requires `multi-tape` (which depends on `wfst-log`).

use crate::automata::semiring::Semiring;
use std::collections::{HashMap, HashSet, VecDeque};
use std::fmt;

// ══════════════════════════════════════════════════════════════════════════════
// Core Types
// ══════════════════════════════════════════════════════════════════════════════

/// State in a multi-tape automaton.
///
/// Each state has a unique numeric identifier and an optional human-readable
/// label for diagnostics and display.
#[derive(Debug, Clone)]
pub struct MultiTapeState {
    /// Unique state identifier (0-indexed, assigned by `add_state`).
    pub id: usize,
    /// Optional human-readable label (e.g., "q0", "accept").
    pub label: Option<String>,
}

/// Transition reading from K tapes simultaneously.
///
/// Each element of `labels` corresponds to one tape:
/// - `Some(s)` — read symbol `s` from that tape (consuming one token).
/// - `None` — epsilon (no symbol consumed on that tape).
///
/// A transition where all K labels are `None` is a pure epsilon transition.
#[derive(Debug, Clone)]
pub struct MultiTapeTransition<W: Semiring, const K: usize> {
    /// Source state identifier.
    pub from: usize,
    /// Target state identifier.
    pub to: usize,
    /// One label per tape. `None` = epsilon (no symbol consumed on this tape).
    pub labels: [Option<String>; K],
    /// Semiring weight for this transition.
    pub weight: W,
}

/// A weighted multi-tape automaton with K tapes.
///
/// Generalizes WFSTs (K=2) to K synchronized tapes. The automaton has:
/// - A set of states with unique identifiers.
/// - Transitions labeled with K-tuples of symbols (or epsilon).
/// - Initial states with entry weights.
/// - Accepting (final) states with exit weights.
///
/// Multi-channel receives `for (@x <- ch1, @y <- ch2)` map directly:
/// ch1 -> tape 1, ch2 -> tape 2.
#[derive(Debug, Clone)]
pub struct WeightedMultiTapeAutomaton<W: Semiring, const K: usize> {
    /// All states in the automaton.
    pub states: Vec<MultiTapeState>,
    /// All transitions (edges) in the automaton.
    pub transitions: Vec<MultiTapeTransition<W, K>>,
    /// Initial states mapped to their entry weights.
    pub initial: HashMap<usize, W>,
    /// Accepting (final) states mapped to their exit weights.
    pub accepting: HashMap<usize, W>,
}

// ══════════════════════════════════════════════════════════════════════════════
// Constructor and Basic Methods
// ══════════════════════════════════════════════════════════════════════════════

impl<W: Semiring, const K: usize> WeightedMultiTapeAutomaton<W, K> {
    /// Create a new empty multi-tape automaton with no states or transitions.
    pub fn new() -> Self {
        WeightedMultiTapeAutomaton {
            states: Vec::new(),
            transitions: Vec::new(),
            initial: HashMap::new(),
            accepting: HashMap::new(),
        }
    }

    /// Add a state with an optional human-readable label.
    ///
    /// Returns the unique identifier for the new state. Identifiers are
    /// assigned sequentially starting from 0.
    pub fn add_state(&mut self, label: Option<String>) -> usize {
        let id = self.states.len();
        self.states.push(MultiTapeState { id, label });
        id
    }

    /// Add a transition from `from` to `to` with the given K-tape labels and weight.
    ///
    /// # Panics
    ///
    /// Panics if `from` or `to` are not valid state identifiers (i.e., >= `num_states()`).
    pub fn add_transition(
        &mut self,
        from: usize,
        to: usize,
        labels: [Option<String>; K],
        weight: W,
    ) {
        assert!(
            from < self.states.len(),
            "multi_tape: source state {from} out of range (num_states = {})",
            self.states.len()
        );
        assert!(
            to < self.states.len(),
            "multi_tape: target state {to} out of range (num_states = {})",
            self.states.len()
        );
        self.transitions.push(MultiTapeTransition {
            from,
            to,
            labels,
            weight,
        });
    }

    /// Set a state as initial with the given entry weight.
    ///
    /// If the state was already initial, the weights are combined via semiring
    /// addition (`plus`), selecting the better of the two weights.
    ///
    /// # Panics
    ///
    /// Panics if `state` is not a valid state identifier.
    pub fn set_initial(&mut self, state: usize, weight: W) {
        assert!(
            state < self.states.len(),
            "multi_tape: initial state {state} out of range (num_states = {})",
            self.states.len()
        );
        self.initial
            .entry(state)
            .and_modify(|w| *w = w.plus(&weight))
            .or_insert(weight);
    }

    /// Set a state as accepting with the given exit weight.
    ///
    /// If the state was already accepting, the weights are combined via semiring
    /// addition (`plus`).
    ///
    /// # Panics
    ///
    /// Panics if `state` is not a valid state identifier.
    pub fn set_accepting(&mut self, state: usize, weight: W) {
        assert!(
            state < self.states.len(),
            "multi_tape: accepting state {state} out of range (num_states = {})",
            self.states.len()
        );
        self.accepting
            .entry(state)
            .and_modify(|w| *w = w.plus(&weight))
            .or_insert(weight);
    }

    /// Number of states in the automaton.
    pub fn num_states(&self) -> usize {
        self.states.len()
    }

    /// Number of transitions in the automaton.
    pub fn num_transitions(&self) -> usize {
        self.transitions.len()
    }

    /// Whether the automaton has no states.
    pub fn is_empty(&self) -> bool {
        self.states.is_empty()
    }
}

impl<W: Semiring, const K: usize> Default for WeightedMultiTapeAutomaton<W, K> {
    fn default() -> Self {
        Self::new()
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// pair() — Combine two single-tape automata into a 2-tape automaton
// ══════════════════════════════════════════════════════════════════════════════

/// Combine two single-tape automata into a 2-tape automaton via product
/// construction (Kempe 2004, Definition 3).
///
/// The resulting automaton has:
/// - States: `|Q1| x |Q2|` (all pairs of states from `a1` and `a2`).
/// - Transitions: for each pair `(t1, t2)` of transitions from `a1` and `a2`,
///   create a transition `(q1, q2) --[label1, label2]--> (q1', q2')` with
///   weight `w1 * w2`.
/// - Also includes epsilon-extended transitions: a transition in `a1` paired
///   with an epsilon-stay in `a2`, and vice versa. This ensures the two tapes
///   can advance independently.
/// - Initial states: pairs `(i1, i2)` with weight `w_i1 * w_i2`.
/// - Accepting states: pairs `(f1, f2)` with weight `w_f1 * w_f2`.
pub fn pair<W: Semiring>(
    a1: &WeightedMultiTapeAutomaton<W, 1>,
    a2: &WeightedMultiTapeAutomaton<W, 1>,
) -> WeightedMultiTapeAutomaton<W, 2> {
    let n1 = a1.num_states();
    let n2 = a2.num_states();

    let mut result = WeightedMultiTapeAutomaton::<W, 2>::new();

    // Create product states: (q1, q2) -> id = q1 * n2 + q2
    // Preallocate for the full product.
    result.states.reserve(n1 * n2);
    for s1 in &a1.states {
        for s2 in &a2.states {
            let label = match (&s1.label, &s2.label) {
                (Some(l1), Some(l2)) => Some(format!("({l1},{l2})")),
                (Some(l1), None) => Some(format!("({l1},_)")),
                (None, Some(l2)) => Some(format!("(_,{l2})")),
                (None, None) => None,
            };
            result.add_state(label);
        }
    }

    let product_id = |q1: usize, q2: usize| -> usize { q1 * n2 + q2 };

    // Initial states: (i1, i2) with combined weight.
    for (&i1, &w1) in &a1.initial {
        for (&i2, &w2) in &a2.initial {
            result.set_initial(product_id(i1, i2), w1.times(&w2));
        }
    }

    // Accepting states: (f1, f2) with combined weight.
    for (&f1, &w1) in &a1.accepting {
        for (&f2, &w2) in &a2.accepting {
            result.set_accepting(product_id(f1, f2), w1.times(&w2));
        }
    }

    // Synchronized transitions: both tapes advance simultaneously.
    for t1 in &a1.transitions {
        for t2 in &a2.transitions {
            result.add_transition(
                product_id(t1.from, t2.from),
                product_id(t1.to, t2.to),
                [t1.labels[0].clone(), t2.labels[0].clone()],
                t1.weight.times(&t2.weight),
            );
        }
    }

    // Epsilon-extended: a1 advances, a2 stays (epsilon on tape 2).
    for t1 in &a1.transitions {
        for q2 in 0..n2 {
            result.add_transition(
                product_id(t1.from, q2),
                product_id(t1.to, q2),
                [t1.labels[0].clone(), None],
                t1.weight,
            );
        }
    }

    // Epsilon-extended: a2 advances, a1 stays (epsilon on tape 1).
    for t2 in &a2.transitions {
        for q1 in 0..n1 {
            result.add_transition(
                product_id(q1, t2.from),
                product_id(q1, t2.to),
                [None, t2.labels[0].clone()],
                t2.weight,
            );
        }
    }

    result
}

// ══════════════════════════════════════════════════════════════════════════════
// project() — Extract single-tape behavior
// ══════════════════════════════════════════════════════════════════════════════

impl<W: Semiring, const K: usize> WeightedMultiTapeAutomaton<W, K> {
    /// Project the automaton onto a single tape, discarding all other tape labels.
    ///
    /// The result is a 1-tape automaton that retains only the symbols on
    /// `tape_idx`. Labels on all other tapes become epsilon (and are discarded
    /// in the output). The state structure and weights are preserved; epsilon
    /// removal is left to downstream consumers.
    ///
    /// # Panics
    ///
    /// Panics if `tape_idx >= K`.
    pub fn project(&self, tape_idx: usize) -> WeightedMultiTapeAutomaton<W, 1> {
        assert!(
            tape_idx < K,
            "multi_tape::project: tape_idx {tape_idx} out of range (K = {K})"
        );

        let mut result = WeightedMultiTapeAutomaton::<W, 1>::new();

        // Copy states.
        for s in &self.states {
            result.add_state(s.label.clone());
        }

        // Copy initial and accepting weights.
        for (&state, &weight) in &self.initial {
            result.set_initial(state, weight);
        }
        for (&state, &weight) in &self.accepting {
            result.set_accepting(state, weight);
        }

        // Project transitions: keep only the label on tape_idx.
        for t in &self.transitions {
            result.add_transition(t.from, t.to, [t.labels[tape_idx].clone()], t.weight);
        }

        result
    }

    /// Constrain tapes `tape_i` and `tape_j` to share identical labels
    /// (Kempe 2004, auto-intersection).
    ///
    /// Retains only transitions where `labels[tape_i] == labels[tape_j]`:
    /// - Both `None` (both tapes consume epsilon) — kept.
    /// - Both `Some(s)` with the same string `s` — kept.
    /// - All other combinations — removed.
    ///
    /// States that become unreachable after filtering are NOT pruned (the
    /// caller can run dead-state elimination if desired).
    ///
    /// # Panics
    ///
    /// Panics if `tape_i >= K`, `tape_j >= K`, or `tape_i == tape_j`.
    pub fn auto_intersect(&self, tape_i: usize, tape_j: usize) -> Self {
        assert!(
            tape_i < K,
            "multi_tape::auto_intersect: tape_i {tape_i} out of range (K = {K})"
        );
        assert!(
            tape_j < K,
            "multi_tape::auto_intersect: tape_j {tape_j} out of range (K = {K})"
        );
        assert!(
            tape_i != tape_j,
            "multi_tape::auto_intersect: tape_i and tape_j must differ (both = {tape_i})"
        );

        let mut result = Self::new();

        // Copy states.
        for s in &self.states {
            result.add_state(s.label.clone());
        }

        // Copy initial and accepting weights.
        for (&state, &weight) in &self.initial {
            result.set_initial(state, weight);
        }
        for (&state, &weight) in &self.accepting {
            result.set_accepting(state, weight);
        }

        // Filter transitions: keep only those where labels[i] == labels[j].
        for t in &self.transitions {
            if t.labels[tape_i] == t.labels[tape_j] {
                result.add_transition(t.from, t.to, t.labels.clone(), t.weight);
            }
        }

        result
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// multi_tape_intersect() — K-tape product construction
// ══════════════════════════════════════════════════════════════════════════════

/// Compute the K-tape product (intersection) of two multi-tape automata.
///
/// Product construction with synchronized tape labels on all K tapes:
/// - States: `|Q_a| x |Q_b|` (all pairs).
/// - Transitions: a transition from `a` and a transition from `b` are combined
///   if and only if their labels match on ALL K tapes (both `None`, or both
///   `Some(s)` with the same string).
/// - Weight: `w_a * w_b` (semiring multiplication).
/// - Initial: `(i_a, i_b)` with weight `w_ia * w_ib`.
/// - Accepting: `(f_a, f_b)` with weight `w_fa * w_fb`.
pub fn multi_tape_intersect<W: Semiring, const K: usize>(
    a: &WeightedMultiTapeAutomaton<W, K>,
    b: &WeightedMultiTapeAutomaton<W, K>,
) -> WeightedMultiTapeAutomaton<W, K> {
    let na = a.num_states();
    let nb = b.num_states();

    let mut result = WeightedMultiTapeAutomaton::<W, K>::new();

    // Product states.
    result.states.reserve(na * nb);
    for sa in &a.states {
        for sb in &b.states {
            let label = match (&sa.label, &sb.label) {
                (Some(la), Some(lb)) => Some(format!("({la},{lb})")),
                (Some(la), None) => Some(format!("({la},_)")),
                (None, Some(lb)) => Some(format!("(_,{lb})")),
                (None, None) => None,
            };
            result.add_state(label);
        }
    }

    let product_id = |qa: usize, qb: usize| -> usize { qa * nb + qb };

    // Initial states.
    for (&ia, &wa) in &a.initial {
        for (&ib, &wb) in &b.initial {
            result.set_initial(product_id(ia, ib), wa.times(&wb));
        }
    }

    // Accepting states.
    for (&fa, &wa) in &a.accepting {
        for (&fb, &wb) in &b.accepting {
            result.set_accepting(product_id(fa, fb), wa.times(&wb));
        }
    }

    // Synchronized transitions: labels must match on ALL K tapes.
    for ta in &a.transitions {
        for tb in &b.transitions {
            let all_match = (0..K).all(|k| ta.labels[k] == tb.labels[k]);
            if all_match {
                // Use labels from either side (they are equal).
                result.add_transition(
                    product_id(ta.from, tb.from),
                    product_id(ta.to, tb.to),
                    ta.labels.clone(),
                    ta.weight.times(&tb.weight),
                );
            }
        }
    }

    result
}

// ══════════════════════════════════════════════════════════════════════════════
// evaluate() — Evaluate on K input streams
// ══════════════════════════════════════════════════════════════════════════════

impl<W: Semiring, const K: usize> WeightedMultiTapeAutomaton<W, K> {
    /// Evaluate the automaton on K concrete input streams.
    ///
    /// Performs a BFS over `(state, positions_per_tape)` configurations. Each
    /// configuration tracks the current state and how far each tape has been
    /// consumed. The evaluation terminates when no more configurations can
    /// advance. The result is the semiring sum of `initial_weight * path_weight
    /// * accepting_weight` over all accepting configurations where every tape
    /// has been fully consumed.
    ///
    /// # Time Complexity
    ///
    /// O(|Q| * prod_k |input_k| * |transitions|) in the worst case. For
    /// deterministic automata this reduces to O(max_k |input_k|).
    pub fn evaluate(&self, inputs: &[Vec<String>; K]) -> W {
        if self.initial.is_empty() {
            return W::zero();
        }

        // Configuration: (state_id, [position_per_tape]) -> accumulated weight.
        // Positions are how many symbols have been consumed on each tape.
        let mut active: HashMap<(usize, [usize; K]), W> = HashMap::new();

        // Seed with initial states at position [0, 0, ..., 0].
        let start_positions = [0_usize; K];
        for (&state, &weight) in &self.initial {
            active
                .entry((state, start_positions))
                .and_modify(|w| *w = w.plus(&weight))
                .or_insert(weight);
        }

        // BFS: process configurations level by level.
        // We iterate until no new configurations are discovered.
        let mut result = W::zero();
        let mut queue: VecDeque<(usize, [usize; K], W)> = VecDeque::new();
        let mut visited: HashSet<(usize, [usize; K])> = HashSet::new();

        for (&(state, positions), &weight) in &active {
            queue.push_back((state, positions, weight));
            visited.insert((state, positions));
        }

        while let Some((state, positions, path_weight)) = queue.pop_front() {
            // Check if this is an accepting configuration (all tapes consumed).
            let all_consumed = (0..K).all(|k| positions[k] == inputs[k].len());
            if all_consumed {
                if let Some(&accept_weight) = self.accepting.get(&state) {
                    result = result.plus(&path_weight.times(&accept_weight));
                }
            }

            // Try all transitions from this state.
            for t in &self.transitions {
                if t.from != state {
                    continue;
                }

                // Check if we can consume the required labels.
                let mut new_positions = positions;
                let mut can_take = true;

                for k in 0..K {
                    match &t.labels[k] {
                        None => {
                            // Epsilon on tape k: no symbol consumed.
                        }
                        Some(sym) => {
                            if positions[k] < inputs[k].len()
                                && inputs[k][positions[k]] == *sym
                            {
                                new_positions[k] = positions[k] + 1;
                            } else {
                                can_take = false;
                                break;
                            }
                        }
                    }
                }

                if can_take {
                    let new_weight = path_weight.times(&t.weight);
                    let key = (t.to, new_positions);

                    if visited.insert(key) {
                        queue.push_back((t.to, new_positions, new_weight));
                    }
                    // Note: if already visited via a different path, the first
                    // visit's weight is used. For exact semiring evaluation,
                    // a more sophisticated algorithm (e.g., Dijkstra for
                    // tropical) would be needed. This BFS suffices for
                    // correctness testing.
                }
            }
        }

        result
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// MultiTapeAnalysis — Static analysis results
// ══════════════════════════════════════════════════════════════════════════════

/// Analysis results for a multi-tape automaton.
///
/// Captures structural properties useful for diagnostics and optimization:
/// - Disconnected tapes (no auto-intersection constraints).
/// - Overlapping tapes (identical label sets on all transitions).
#[derive(Debug, Clone)]
pub struct MultiTapeAnalysis {
    /// Number of states in the analyzed automaton.
    pub num_states: usize,
    /// Number of tapes (K).
    pub num_tapes: usize,
    /// Tapes that have no label constraints shared with any other tape.
    ///
    /// A tape is "disconnected" if it could be removed and analyzed
    /// independently without affecting the other tapes' behavior.
    pub disconnected_tapes: Vec<usize>,
    /// Pairs of tapes whose label sets are identical on every transition.
    ///
    /// When `(i, j)` appears here, tapes `i` and `j` always read the same
    /// symbol (or both epsilon) on every transition. This suggests they could
    /// be merged into a single tape.
    pub overlapping_tapes: Vec<(usize, usize)>,
}

impl<W: Semiring, const K: usize> WeightedMultiTapeAutomaton<W, K> {
    /// Analyze the multi-tape automaton for structural properties.
    ///
    /// Detects disconnected tapes (those whose labels are always `None` or
    /// never constrained by `auto_intersect`) and overlapping tape pairs
    /// (those with identical labels on every transition).
    pub fn analyze(&self) -> MultiTapeAnalysis {
        // A tape is "disconnected" if it never appears with a non-epsilon label
        // on any transition.
        let mut tape_has_label = vec![false; K];
        for t in &self.transitions {
            for k in 0..K {
                if t.labels[k].is_some() {
                    tape_has_label[k] = true;
                }
            }
        }

        let disconnected_tapes: Vec<usize> = (0..K)
            .filter(|&k| !tape_has_label[k])
            .collect();

        // Overlapping tapes: tapes i,j are overlapping if labels[i] == labels[j]
        // on every transition.
        let mut overlapping_tapes: Vec<(usize, usize)> = Vec::new();
        for i in 0..K {
            for j in (i + 1)..K {
                let all_match = self
                    .transitions
                    .iter()
                    .all(|t| t.labels[i] == t.labels[j]);
                // Only report overlapping if there are transitions to compare.
                if all_match && !self.transitions.is_empty() {
                    overlapping_tapes.push((i, j));
                }
            }
        }

        MultiTapeAnalysis {
            num_states: self.num_states(),
            num_tapes: K,
            disconnected_tapes,
            overlapping_tapes,
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Display
// ══════════════════════════════════════════════════════════════════════════════

impl<W: Semiring, const K: usize> fmt::Display for WeightedMultiTapeAutomaton<W, K> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "WeightedMultiTapeAutomaton<K={K}> {{",)?;
        writeln!(f, "  states: {} | transitions: {}", self.num_states(), self.num_transitions())?;

        // Initial states.
        if !self.initial.is_empty() {
            write!(f, "  initial: [")?;
            let mut first = true;
            for (&state, &weight) in &self.initial {
                if !first {
                    write!(f, ", ")?;
                }
                first = false;
                let label = self.states[state]
                    .label
                    .as_deref()
                    .unwrap_or("_");
                write!(f, "{label}/{weight:?}")?;
            }
            writeln!(f, "]")?;
        }

        // Accepting states.
        if !self.accepting.is_empty() {
            write!(f, "  accepting: [")?;
            let mut first = true;
            for (&state, &weight) in &self.accepting {
                if !first {
                    write!(f, ", ")?;
                }
                first = false;
                let label = self.states[state]
                    .label
                    .as_deref()
                    .unwrap_or("_");
                write!(f, "{label}/{weight:?}")?;
            }
            writeln!(f, "]")?;
        }

        // Transitions.
        for t in &self.transitions {
            let from_label = self.states[t.from]
                .label
                .as_deref()
                .unwrap_or("_");
            let to_label = self.states[t.to]
                .label
                .as_deref()
                .unwrap_or("_");
            let labels: Vec<String> = t
                .labels
                .iter()
                .map(|l| l.as_deref().unwrap_or("eps").to_string())
                .collect();
            writeln!(
                f,
                "  {from_label} --[{}]--> {to_label} / {:?}",
                labels.join(", "),
                t.weight
            )?;
        }

        writeln!(f, "}}")
    }
}

impl fmt::Display for MultiTapeAnalysis {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(
            f,
            "MultiTapeAnalysis {{ states: {}, tapes: {} }}",
            self.num_states, self.num_tapes
        )?;
        if !self.disconnected_tapes.is_empty() {
            writeln!(f, "  disconnected tapes: {:?}", self.disconnected_tapes)?;
        }
        if !self.overlapping_tapes.is_empty() {
            writeln!(f, "  overlapping tape pairs: {:?}", self.overlapping_tapes)?;
        }
        Ok(())
    }
}

/// Analyze grammar multi-stream structure using multi-tape automata.
///
/// Builds a category dependency graph and finds:
/// - Disconnected tapes: categories with no cross-category references (singleton components)
/// - Overlapping tapes: categories that share identical rule structures
pub fn analyze_from_bundle(
    all_syntax: &[(String, String, Vec<crate::SyntaxItemSpec>)],
    categories: &[crate::pipeline::CategoryInfo],
) -> MultiTapeAnalysis {
    let num_cats = categories.len();
    let num_rules = all_syntax.len();

    if num_cats == 0 {
        return MultiTapeAnalysis {
            num_states: num_rules.max(1),
            num_tapes: 0,
            disconnected_tapes: Vec::new(),
            overlapping_tapes: Vec::new(),
        };
    }

    // Map category → index
    let cat_to_idx: HashMap<String, usize> = categories
        .iter()
        .enumerate()
        .map(|(i, c)| (c.name.clone(), i))
        .collect();

    // Build adjacency: category A connects to B when A has a rule referencing B
    let mut connected_to: Vec<HashSet<usize>> = vec![HashSet::new(); num_cats];

    for (_label, cat, items) in all_syntax {
        let src = match cat_to_idx.get(cat) {
            Some(&idx) => idx,
            None => continue,
        };
        for item in items {
            collect_category_refs(item, cat, &cat_to_idx, src, &mut connected_to);
        }
    }

    // Union-Find for connected components
    let mut parent: Vec<usize> = (0..num_cats).collect();

    fn find(parent: &mut [usize], x: usize) -> usize {
        if parent[x] != x {
            parent[x] = find(parent, parent[x]);
        }
        parent[x]
    }

    fn union(parent: &mut [usize], a: usize, b: usize) {
        let ra = find(parent, a);
        let rb = find(parent, b);
        if ra != rb {
            parent[ra] = rb;
        }
    }

    for src in 0..num_cats {
        for &dst in &connected_to[src] {
            union(&mut parent, src, dst);
        }
    }

    // Find disconnected tapes: categories in singleton components
    // (no cross-category references at all)
    let mut component_members: HashMap<usize, Vec<usize>> = HashMap::new();
    for i in 0..num_cats {
        let root = find(&mut parent, i);
        component_members.entry(root).or_default().push(i);
    }

    let mut disconnected_tapes: Vec<usize> = component_members
        .values()
        .filter(|members| members.len() == 1)
        .map(|members| members[0])
        .collect();
    disconnected_tapes.sort_unstable();

    // Overlapping tapes: categories with identical rule structures.
    // Group by sorted list of rule item discriminant signatures.
    let mut cat_signatures: HashMap<usize, Vec<Vec<String>>> = HashMap::new();
    for (_label, cat, items) in all_syntax {
        if let Some(&idx) = cat_to_idx.get(cat) {
            let mut sig: Vec<String> = items
                .iter()
                .map(|item| format!("{:?}", std::mem::discriminant(item)))
                .collect();
            sig.sort();
            cat_signatures.entry(idx).or_default().push(sig);
        }
    }

    // Normalize: sort rule signatures per category for stable comparison
    for sigs in cat_signatures.values_mut() {
        sigs.sort();
    }

    let mut overlapping_tapes: Vec<(usize, usize)> = Vec::new();
    let mut cat_indices: Vec<usize> = cat_signatures.keys().copied().collect();
    cat_indices.sort_unstable();
    for i in 0..cat_indices.len() {
        for j in (i + 1)..cat_indices.len() {
            let idx_a = cat_indices[i];
            let idx_b = cat_indices[j];
            if let (Some(sigs_a), Some(sigs_b)) =
                (cat_signatures.get(&idx_a), cat_signatures.get(&idx_b))
            {
                if sigs_a == sigs_b && !sigs_a.is_empty() {
                    overlapping_tapes.push((idx_a, idx_b));
                }
            }
        }
    }

    MultiTapeAnalysis {
        num_states: num_rules.max(1),
        num_tapes: num_cats,
        disconnected_tapes,
        overlapping_tapes,
    }
}

/// Recursively collect cross-category references from syntax items.
fn collect_category_refs(
    item: &crate::SyntaxItemSpec,
    rule_cat: &str,
    cat_to_idx: &HashMap<String, usize>,
    src: usize,
    connected_to: &mut [HashSet<usize>],
) {
    match item {
        crate::SyntaxItemSpec::NonTerminal { category, .. } => {
            if category != rule_cat {
                if let Some(&dst) = cat_to_idx.get(category.as_str()) {
                    connected_to[src].insert(dst);
                    connected_to[dst].insert(src);
                }
            }
        }
        crate::SyntaxItemSpec::Binder { category, .. } => {
            if category != rule_cat {
                if let Some(&dst) = cat_to_idx.get(category.as_str()) {
                    connected_to[src].insert(dst);
                    connected_to[dst].insert(src);
                }
            }
        }
        crate::SyntaxItemSpec::Collection {
            element_category, ..
        } => {
            if element_category != rule_cat {
                if let Some(&dst) = cat_to_idx.get(element_category.as_str()) {
                    connected_to[src].insert(dst);
                    connected_to[dst].insert(src);
                }
            }
        }
        crate::SyntaxItemSpec::Sep { body, .. } => {
            collect_category_refs(body, rule_cat, cat_to_idx, src, connected_to);
        }
        crate::SyntaxItemSpec::Map { body_items } => {
            for sub in body_items {
                collect_category_refs(sub, rule_cat, cat_to_idx, src, connected_to);
            }
        }
        crate::SyntaxItemSpec::Zip {
            left_category,
            right_category,
            body,
            ..
        } => {
            for ref_cat in [left_category.as_str(), right_category.as_str()] {
                if ref_cat != rule_cat {
                    if let Some(&dst) = cat_to_idx.get(ref_cat) {
                        connected_to[src].insert(dst);
                        connected_to[dst].insert(src);
                    }
                }
            }
            collect_category_refs(body, rule_cat, cat_to_idx, src, connected_to);
        }
        crate::SyntaxItemSpec::Optional { inner } => {
            for sub in inner {
                collect_category_refs(sub, rule_cat, cat_to_idx, src, connected_to);
            }
        }
        _ => {}
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Predicate Dispatch — PredicateCompiler integration
// ══════════════════════════════════════════════════════════════════════════════

/// Compiler adapter for the Multi-Tape Automata module (M8).
///
/// Activated by ≥2 channels in a join receive (k-tape regular relation variety).
#[cfg(feature = "predicate-dispatch")]
pub struct MultiTapeCompiler;

#[cfg(feature = "predicate-dispatch")]
impl crate::predicate_dispatch::PredicateCompiler for MultiTapeCompiler {
    type Output = MultiTapeAnalysis;

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
    use crate::automata::semiring::{LogWeight, TropicalWeight};

    // ── Helper: build a simple 1-tape automaton ──────────────────────────────

    /// Build a 1-tape automaton that accepts the sequence of symbols in `words`.
    /// Each transition has weight TropicalWeight::one() (cost 0).
    fn linear_1tape(words: &[&str]) -> WeightedMultiTapeAutomaton<TropicalWeight, 1> {
        let mut a = WeightedMultiTapeAutomaton::<TropicalWeight, 1>::new();
        // n+1 states for n words: q0 --w0--> q1 --w1--> q2 ... --w(n-1)--> qn
        let n = words.len();
        for i in 0..=n {
            a.add_state(Some(format!("q{i}")));
        }
        a.set_initial(0, TropicalWeight::one());
        a.set_accepting(n, TropicalWeight::one());
        for (i, word) in words.iter().enumerate() {
            a.add_transition(i, i + 1, [Some(word.to_string())], TropicalWeight::one());
        }
        a
    }

    // ── Construction tests ──────────────────────────────────────────────────

    #[test]
    fn construct_1_tape() {
        let a = linear_1tape(&["a", "b"]);
        assert_eq!(a.num_states(), 3);
        assert_eq!(a.num_transitions(), 2);
        assert_eq!(a.initial.len(), 1);
        assert_eq!(a.accepting.len(), 1);
    }

    #[test]
    fn construct_2_tape() {
        let mut a = WeightedMultiTapeAutomaton::<TropicalWeight, 2>::new();
        let q0 = a.add_state(Some("q0".into()));
        let q1 = a.add_state(Some("q1".into()));
        a.set_initial(q0, TropicalWeight::one());
        a.set_accepting(q1, TropicalWeight::one());
        a.add_transition(
            q0,
            q1,
            [Some("x".into()), Some("y".into())],
            TropicalWeight::one(),
        );
        assert_eq!(a.num_states(), 2);
        assert_eq!(a.num_transitions(), 1);
    }

    #[test]
    fn construct_3_tape() {
        let mut a = WeightedMultiTapeAutomaton::<TropicalWeight, 3>::new();
        let q0 = a.add_state(Some("q0".into()));
        let q1 = a.add_state(Some("q1".into()));
        a.set_initial(q0, TropicalWeight::one());
        a.set_accepting(q1, TropicalWeight::one());
        a.add_transition(
            q0,
            q1,
            [Some("a".into()), Some("b".into()), Some("c".into())],
            TropicalWeight::one(),
        );
        assert_eq!(a.num_states(), 2);
        assert_eq!(a.num_transitions(), 1);
    }

    // ── pair() tests ────────────────────────────────────────────────────────

    #[test]
    fn pair_combines_two_single_tape() {
        let a1 = linear_1tape(&["a"]);
        let a2 = linear_1tape(&["x"]);

        let paired = pair(&a1, &a2);

        // Product: 2 states * 2 states = 4 states.
        assert_eq!(paired.num_states(), 4);
        // 1 initial state (product of single initials).
        assert_eq!(paired.initial.len(), 1);
        // 1 accepting state (product of single acceptings).
        assert_eq!(paired.accepting.len(), 1);
        // Transitions: 1*1 synchronized + 1*2 eps-extended(a1) + 1*2 eps-extended(a2) = 5.
        assert_eq!(paired.num_transitions(), 5);
    }

    #[test]
    fn pair_evaluate_independent_tapes() {
        // a1 accepts ["hello"], a2 accepts ["world"].
        let a1 = linear_1tape(&["hello"]);
        let a2 = linear_1tape(&["world"]);
        let paired = pair(&a1, &a2);

        // Evaluate with matching inputs on each tape via epsilon-extended transitions.
        let result = paired.evaluate(&[
            vec!["hello".into()],
            vec!["world".into()],
        ]);
        // Should accept (via epsilon-extended paths).
        assert!(
            !result.is_zero(),
            "pair should accept independent tape inputs"
        );
    }

    // ── project() tests ─────────────────────────────────────────────────────

    #[test]
    fn project_tape_0_from_2_tape() {
        let mut a = WeightedMultiTapeAutomaton::<TropicalWeight, 2>::new();
        let q0 = a.add_state(Some("q0".into()));
        let q1 = a.add_state(Some("q1".into()));
        a.set_initial(q0, TropicalWeight::one());
        a.set_accepting(q1, TropicalWeight::one());
        a.add_transition(
            q0,
            q1,
            [Some("alpha".into()), Some("beta".into())],
            TropicalWeight::new(1.5),
        );

        let projected = a.project(0);
        assert_eq!(projected.num_states(), 2);
        assert_eq!(projected.num_transitions(), 1);
        // The single transition should have label "alpha" on tape 0.
        assert_eq!(
            projected.transitions[0].labels[0].as_deref(),
            Some("alpha")
        );
        assert_eq!(projected.transitions[0].weight, TropicalWeight::new(1.5));
    }

    #[test]
    fn project_tape_1_from_2_tape() {
        let mut a = WeightedMultiTapeAutomaton::<TropicalWeight, 2>::new();
        let q0 = a.add_state(Some("q0".into()));
        let q1 = a.add_state(Some("q1".into()));
        a.set_initial(q0, TropicalWeight::one());
        a.set_accepting(q1, TropicalWeight::one());
        a.add_transition(
            q0,
            q1,
            [Some("alpha".into()), Some("beta".into())],
            TropicalWeight::new(2.0),
        );

        let projected = a.project(1);
        assert_eq!(projected.num_states(), 2);
        assert_eq!(projected.num_transitions(), 1);
        // The single transition should have label "beta" on tape 1.
        assert_eq!(
            projected.transitions[0].labels[0].as_deref(),
            Some("beta")
        );
        assert_eq!(projected.transitions[0].weight, TropicalWeight::new(2.0));
    }

    // ── auto_intersect() tests ──────────────────────────────────────────────

    #[test]
    fn auto_intersect_filters_mismatched_labels() {
        let mut a = WeightedMultiTapeAutomaton::<TropicalWeight, 2>::new();
        let q0 = a.add_state(Some("q0".into()));
        let q1 = a.add_state(Some("q1".into()));
        let q2 = a.add_state(Some("q2".into()));
        a.set_initial(q0, TropicalWeight::one());
        a.set_accepting(q1, TropicalWeight::one());
        a.set_accepting(q2, TropicalWeight::one());

        // Matching labels on tapes 0 and 1.
        a.add_transition(
            q0,
            q1,
            [Some("x".into()), Some("x".into())],
            TropicalWeight::one(),
        );
        // Mismatched labels.
        a.add_transition(
            q0,
            q2,
            [Some("a".into()), Some("b".into())],
            TropicalWeight::one(),
        );

        let constrained = a.auto_intersect(0, 1);
        assert_eq!(constrained.num_states(), 3);
        // Only the matching transition survives.
        assert_eq!(constrained.num_transitions(), 1);
        assert_eq!(
            constrained.transitions[0].labels[0].as_deref(),
            Some("x")
        );
        assert_eq!(
            constrained.transitions[0].labels[1].as_deref(),
            Some("x")
        );
    }

    #[test]
    fn auto_intersect_keeps_both_epsilon() {
        let mut a = WeightedMultiTapeAutomaton::<TropicalWeight, 2>::new();
        let q0 = a.add_state(None);
        let q1 = a.add_state(None);
        a.set_initial(q0, TropicalWeight::one());
        a.set_accepting(q1, TropicalWeight::one());

        // Both tapes epsilon — should be kept.
        a.add_transition(q0, q1, [None, None], TropicalWeight::one());

        let constrained = a.auto_intersect(0, 1);
        assert_eq!(constrained.num_transitions(), 1);
    }

    // ── multi_tape_intersect() tests ────────────────────────────────────────

    #[test]
    fn multi_tape_intersect_product() {
        // Two 2-tape automata, each with 2 states.
        let mut a = WeightedMultiTapeAutomaton::<TropicalWeight, 2>::new();
        let a0 = a.add_state(Some("a0".into()));
        let a1 = a.add_state(Some("a1".into()));
        a.set_initial(a0, TropicalWeight::one());
        a.set_accepting(a1, TropicalWeight::one());
        a.add_transition(
            a0,
            a1,
            [Some("x".into()), Some("y".into())],
            TropicalWeight::new(1.0),
        );

        let mut b = WeightedMultiTapeAutomaton::<TropicalWeight, 2>::new();
        let b0 = b.add_state(Some("b0".into()));
        let b1 = b.add_state(Some("b1".into()));
        b.set_initial(b0, TropicalWeight::one());
        b.set_accepting(b1, TropicalWeight::one());
        b.add_transition(
            b0,
            b1,
            [Some("x".into()), Some("y".into())],
            TropicalWeight::new(2.0),
        );

        let product = multi_tape_intersect(&a, &b);

        // Product: 2 * 2 = 4 states.
        assert_eq!(product.num_states(), 4);
        // One synchronized transition (labels match on both tapes).
        assert_eq!(product.num_transitions(), 1);
        // Weight: 1.0 + 2.0 = 3.0 (tropical times = float addition).
        assert_eq!(product.transitions[0].weight, TropicalWeight::new(3.0));
    }

    #[test]
    fn multi_tape_intersect_no_matching_labels() {
        let mut a = WeightedMultiTapeAutomaton::<TropicalWeight, 2>::new();
        let a0 = a.add_state(None);
        let a1 = a.add_state(None);
        a.set_initial(a0, TropicalWeight::one());
        a.set_accepting(a1, TropicalWeight::one());
        a.add_transition(
            a0,
            a1,
            [Some("x".into()), Some("y".into())],
            TropicalWeight::one(),
        );

        let mut b = WeightedMultiTapeAutomaton::<TropicalWeight, 2>::new();
        let b0 = b.add_state(None);
        let b1 = b.add_state(None);
        b.set_initial(b0, TropicalWeight::one());
        b.set_accepting(b1, TropicalWeight::one());
        // Labels differ on tape 0: "z" vs "x".
        b.add_transition(
            b0,
            b1,
            [Some("z".into()), Some("y".into())],
            TropicalWeight::one(),
        );

        let product = multi_tape_intersect(&a, &b);
        // No matching transitions.
        assert_eq!(product.num_transitions(), 0);
    }

    // ── evaluate() tests ────────────────────────────────────────────────────

    #[test]
    fn evaluate_2_tape_matching_input() {
        let mut a = WeightedMultiTapeAutomaton::<TropicalWeight, 2>::new();
        let q0 = a.add_state(Some("q0".into()));
        let q1 = a.add_state(Some("q1".into()));
        a.set_initial(q0, TropicalWeight::one());
        a.set_accepting(q1, TropicalWeight::one());
        a.add_transition(
            q0,
            q1,
            [Some("a".into()), Some("b".into())],
            TropicalWeight::new(1.0),
        );

        let result = a.evaluate(&[vec!["a".into()], vec!["b".into()]]);
        // Path weight: one() * 1.0 * one() = TropicalWeight(0.0 + 1.0 + 0.0) = 1.0.
        assert_eq!(result, TropicalWeight::new(1.0));
    }

    #[test]
    fn evaluate_2_tape_no_match() {
        let mut a = WeightedMultiTapeAutomaton::<TropicalWeight, 2>::new();
        let q0 = a.add_state(None);
        let q1 = a.add_state(None);
        a.set_initial(q0, TropicalWeight::one());
        a.set_accepting(q1, TropicalWeight::one());
        a.add_transition(
            q0,
            q1,
            [Some("a".into()), Some("b".into())],
            TropicalWeight::one(),
        );

        // Wrong input on tape 1.
        let result = a.evaluate(&[vec!["a".into()], vec!["WRONG".into()]]);
        assert!(result.is_zero(), "should reject mismatched input");
    }

    #[test]
    fn evaluate_with_epsilon_transitions() {
        let mut a = WeightedMultiTapeAutomaton::<TropicalWeight, 2>::new();
        let q0 = a.add_state(Some("q0".into()));
        let q1 = a.add_state(Some("q1".into()));
        let q2 = a.add_state(Some("q2".into()));
        a.set_initial(q0, TropicalWeight::one());
        a.set_accepting(q2, TropicalWeight::one());

        // q0 --[a, eps]--> q1 (consume "a" on tape 0, epsilon on tape 1).
        a.add_transition(
            q0,
            q1,
            [Some("a".into()), None],
            TropicalWeight::new(1.0),
        );
        // q1 --[eps, b]--> q2 (epsilon on tape 0, consume "b" on tape 1).
        a.add_transition(
            q1,
            q2,
            [None, Some("b".into())],
            TropicalWeight::new(2.0),
        );

        let result = a.evaluate(&[vec!["a".into()], vec!["b".into()]]);
        // Path: q0 --1.0--> q1 --2.0--> q2.
        // Weight: one() * 1.0 * 2.0 * one() = TropicalWeight(0.0 + 1.0 + 2.0 + 0.0) = 3.0.
        assert_eq!(result, TropicalWeight::new(3.0));
    }

    #[test]
    fn evaluate_empty_automaton() {
        let a = WeightedMultiTapeAutomaton::<TropicalWeight, 2>::new();
        let result = a.evaluate(&[vec![], vec![]]);
        assert!(result.is_zero(), "empty automaton should yield zero weight");
    }

    #[test]
    fn evaluate_single_transition() {
        let mut a = WeightedMultiTapeAutomaton::<TropicalWeight, 1>::new();
        let q0 = a.add_state(Some("q0".into()));
        let q1 = a.add_state(Some("q1".into()));
        a.set_initial(q0, TropicalWeight::one());
        a.set_accepting(q1, TropicalWeight::one());
        a.add_transition(
            q0,
            q1,
            [Some("hello".into())],
            TropicalWeight::new(0.5),
        );

        let result = a.evaluate(&[vec!["hello".into()]]);
        assert_eq!(result, TropicalWeight::new(0.5));
    }

    // ── Analysis tests ──────────────────────────────────────────────────────

    #[test]
    fn disconnected_tape_detection() {
        let mut a = WeightedMultiTapeAutomaton::<TropicalWeight, 3>::new();
        let q0 = a.add_state(None);
        let q1 = a.add_state(None);
        a.set_initial(q0, TropicalWeight::one());
        a.set_accepting(q1, TropicalWeight::one());

        // Tape 0 and 2 have labels; tape 1 is always epsilon.
        a.add_transition(
            q0,
            q1,
            [Some("a".into()), None, Some("c".into())],
            TropicalWeight::one(),
        );

        let analysis = a.analyze();
        assert_eq!(analysis.num_tapes, 3);
        assert_eq!(analysis.disconnected_tapes, vec![1]);
    }

    #[test]
    fn overlapping_tape_detection() {
        let mut a = WeightedMultiTapeAutomaton::<TropicalWeight, 2>::new();
        let q0 = a.add_state(None);
        let q1 = a.add_state(None);
        a.set_initial(q0, TropicalWeight::one());
        a.set_accepting(q1, TropicalWeight::one());

        // Both tapes always have the same label.
        a.add_transition(
            q0,
            q1,
            [Some("x".into()), Some("x".into())],
            TropicalWeight::one(),
        );

        let analysis = a.analyze();
        assert_eq!(analysis.overlapping_tapes, vec![(0, 1)]);
    }

    #[test]
    fn no_overlapping_when_labels_differ() {
        let mut a = WeightedMultiTapeAutomaton::<TropicalWeight, 2>::new();
        let q0 = a.add_state(None);
        let q1 = a.add_state(None);
        a.set_initial(q0, TropicalWeight::one());
        a.set_accepting(q1, TropicalWeight::one());

        a.add_transition(
            q0,
            q1,
            [Some("x".into()), Some("y".into())],
            TropicalWeight::one(),
        );

        let analysis = a.analyze();
        assert!(analysis.overlapping_tapes.is_empty());
    }

    // ── Display test ────────────────────────────────────────────────────────

    #[test]
    fn display_does_not_panic() {
        let mut a = WeightedMultiTapeAutomaton::<TropicalWeight, 2>::new();
        let q0 = a.add_state(Some("start".into()));
        let q1 = a.add_state(Some("end".into()));
        a.set_initial(q0, TropicalWeight::one());
        a.set_accepting(q1, TropicalWeight::one());
        a.add_transition(
            q0,
            q1,
            [Some("a".into()), None],
            TropicalWeight::new(1.5),
        );

        let display = format!("{a}");
        assert!(display.contains("WeightedMultiTapeAutomaton<K=2>"));
        assert!(display.contains("start"));
        assert!(display.contains("end"));
        assert!(display.contains("eps"));
    }

    #[test]
    fn display_analysis_does_not_panic() {
        let mut a = WeightedMultiTapeAutomaton::<TropicalWeight, 3>::new();
        let q0 = a.add_state(None);
        let q1 = a.add_state(None);
        a.set_initial(q0, TropicalWeight::one());
        a.set_accepting(q1, TropicalWeight::one());
        a.add_transition(
            q0,
            q1,
            [Some("a".into()), None, Some("a".into())],
            TropicalWeight::one(),
        );

        let analysis = a.analyze();
        let display = format!("{analysis}");
        assert!(display.contains("MultiTapeAnalysis"));
        assert!(display.contains("tapes: 3"));
    }

    // ── Default / empty tests ───────────────────────────────────────────────

    #[test]
    fn default_is_empty() {
        let a = WeightedMultiTapeAutomaton::<TropicalWeight, 2>::default();
        assert!(a.is_empty());
        assert_eq!(a.num_states(), 0);
        assert_eq!(a.num_transitions(), 0);
    }

    // ── LogWeight test (feature-gated) ──────────────────────────────────────

    #[test]
    fn evaluate_with_log_weight() {
        let mut a = WeightedMultiTapeAutomaton::<LogWeight, 1>::new();
        let q0 = a.add_state(Some("q0".into()));
        let q1 = a.add_state(Some("q1".into()));
        a.set_initial(q0, LogWeight::one());
        a.set_accepting(q1, LogWeight::one());
        a.add_transition(
            q0,
            q1,
            [Some("tok".into())],
            LogWeight::new(0.5),
        );

        let result = a.evaluate(&[vec!["tok".into()]]);
        // LogWeight::one() = 0.0, times = +, so path = 0.0 + 0.5 + 0.0 = 0.5.
        assert!(result.approx_eq(&LogWeight::new(0.5), 1e-9));
    }

    // ── analyze_from_bundle() tape independence tests ─────────────────────

    #[test]
    fn analyze_bundle_isolated_category() {
        use crate::pipeline::CategoryInfo;

        let categories = vec![
            CategoryInfo {
                name: "Expr".to_string(),
                is_primary: true,
                native_type: None,
            },
            CategoryInfo {
                name: "Decl".to_string(),
                is_primary: false,
                native_type: None,
            },
        ];

        // Expr has only terminals, Decl has only terminals → both isolated
        let all_syntax = vec![
            (
                "Lit".to_string(),
                "Expr".to_string(),
                vec![crate::SyntaxItemSpec::Terminal("42".to_string())],
            ),
            (
                "Let".to_string(),
                "Decl".to_string(),
                vec![crate::SyntaxItemSpec::Terminal("let".to_string())],
            ),
        ];

        let result = analyze_from_bundle(&all_syntax, &categories);
        assert_eq!(
            result.disconnected_tapes.len(),
            2,
            "both categories should be disconnected"
        );
    }

    #[test]
    fn analyze_bundle_connected_categories() {
        use crate::pipeline::CategoryInfo;

        let categories = vec![
            CategoryInfo {
                name: "Expr".to_string(),
                is_primary: true,
                native_type: None,
            },
            CategoryInfo {
                name: "Stmt".to_string(),
                is_primary: false,
                native_type: None,
            },
        ];

        // Expr references Stmt → connected
        let all_syntax = vec![
            (
                "Block".to_string(),
                "Expr".to_string(),
                vec![crate::SyntaxItemSpec::NonTerminal {
                    category: "Stmt".to_string(),
                    param_name: "s".to_string(),
                }],
            ),
            (
                "Ret".to_string(),
                "Stmt".to_string(),
                vec![crate::SyntaxItemSpec::Terminal("return".to_string())],
            ),
        ];

        let result = analyze_from_bundle(&all_syntax, &categories);
        assert!(
            result.disconnected_tapes.is_empty(),
            "connected categories should not be disconnected"
        );
    }

    #[test]
    fn analyze_bundle_overlapping_tapes() {
        use crate::pipeline::CategoryInfo;

        let categories = vec![
            CategoryInfo {
                name: "Expr".to_string(),
                is_primary: true,
                native_type: None,
            },
            CategoryInfo {
                name: "Pat".to_string(),
                is_primary: false,
                native_type: None,
            },
        ];

        // Both categories have identical rule structures (single terminal rule)
        let all_syntax = vec![
            (
                "Lit".to_string(),
                "Expr".to_string(),
                vec![crate::SyntaxItemSpec::Terminal("42".to_string())],
            ),
            (
                "Lit".to_string(),
                "Pat".to_string(),
                vec![crate::SyntaxItemSpec::Terminal("42".to_string())],
            ),
        ];

        let result = analyze_from_bundle(&all_syntax, &categories);
        assert!(
            !result.overlapping_tapes.is_empty(),
            "identical rule structures should overlap"
        );
    }

    #[test]
    fn analyze_bundle_empty_categories() {
        let result = analyze_from_bundle(&[], &[]);
        assert_eq!(result.num_tapes, 0);
        assert!(result.disconnected_tapes.is_empty());
        assert!(result.overlapping_tapes.is_empty());
    }

    #[test]
    fn analyze_bundle_binder_cross_ref() {
        use crate::pipeline::CategoryInfo;

        let categories = vec![
            CategoryInfo {
                name: "Expr".to_string(),
                is_primary: true,
                native_type: None,
            },
            CategoryInfo {
                name: "Name".to_string(),
                is_primary: false,
                native_type: None,
            },
        ];

        // Expr has a binder referencing Name → connected
        let all_syntax = vec![
            (
                "Lambda".to_string(),
                "Expr".to_string(),
                vec![crate::SyntaxItemSpec::Binder {
                    param_name: "x".to_string(),
                    category: "Name".to_string(),
                    is_multi: false,
                }],
            ),
            (
                "Id".to_string(),
                "Name".to_string(),
                vec![crate::SyntaxItemSpec::Terminal("id".to_string())],
            ),
        ];

        let result = analyze_from_bundle(&all_syntax, &categories);
        assert!(
            result.disconnected_tapes.is_empty(),
            "binder cross-reference should connect categories"
        );
    }

    #[test]
    fn analyze_bundle_collection_cross_ref() {
        use crate::pipeline::CategoryInfo;
        use crate::recursive::CollectionKind;

        let categories = vec![
            CategoryInfo {
                name: "Prog".to_string(),
                is_primary: true,
                native_type: None,
            },
            CategoryInfo {
                name: "Stmt".to_string(),
                is_primary: false,
                native_type: None,
            },
        ];

        // Prog has a collection of Stmt → connected
        let all_syntax = vec![
            (
                "Program".to_string(),
                "Prog".to_string(),
                vec![crate::SyntaxItemSpec::Collection {
                    param_name: "stmts".to_string(),
                    element_category: "Stmt".to_string(),
                    separator: ";".to_string(),
                    kind: CollectionKind::Vec,
                }],
            ),
            (
                "Nop".to_string(),
                "Stmt".to_string(),
                vec![crate::SyntaxItemSpec::Terminal("nop".to_string())],
            ),
        ];

        let result = analyze_from_bundle(&all_syntax, &categories);
        assert!(
            result.disconnected_tapes.is_empty(),
            "collection cross-reference should connect categories"
        );
    }

    #[test]
    fn analyze_bundle_three_categories_partial_connection() {
        use crate::pipeline::CategoryInfo;

        let categories = vec![
            CategoryInfo {
                name: "A".to_string(),
                is_primary: true,
                native_type: None,
            },
            CategoryInfo {
                name: "B".to_string(),
                is_primary: false,
                native_type: None,
            },
            CategoryInfo {
                name: "C".to_string(),
                is_primary: false,
                native_type: None,
            },
        ];

        // A references B (connected), C is isolated
        let all_syntax = vec![
            (
                "AB".to_string(),
                "A".to_string(),
                vec![crate::SyntaxItemSpec::NonTerminal {
                    category: "B".to_string(),
                    param_name: "b".to_string(),
                }],
            ),
            (
                "BLit".to_string(),
                "B".to_string(),
                vec![crate::SyntaxItemSpec::Terminal("b".to_string())],
            ),
            (
                "CLit".to_string(),
                "C".to_string(),
                vec![crate::SyntaxItemSpec::Terminal("c".to_string())],
            ),
        ];

        let result = analyze_from_bundle(&all_syntax, &categories);
        // Only C (index 2) should be disconnected
        assert_eq!(result.disconnected_tapes, vec![2]);
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Property-based tests
// ══════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod proptest_tests {
    use super::*;
    use proptest::prelude::*;
    use crate::test_generators::*;
    use crate::SyntaxItemSpec;

    /// Collect all cross-category references (outbound and inbound).
    ///
    /// Returns a map from category name to a set of other category names it
    /// is connected to (bidirectionally: if A references B, both A→B and B→A
    /// are recorded).
    fn build_connectivity(
        all_syntax: &[(String, String, Vec<SyntaxItemSpec>)],
    ) -> std::collections::HashMap<String, std::collections::HashSet<String>> {
        let mut connections: std::collections::HashMap<String, std::collections::HashSet<String>> =
            std::collections::HashMap::new();
        for (_label, rule_cat, items) in all_syntax {
            for item in items {
                collect_cross_refs(item, rule_cat, &mut connections);
            }
        }
        connections
    }

    fn collect_cross_refs(
        item: &SyntaxItemSpec,
        rule_cat: &str,
        connections: &mut std::collections::HashMap<String, std::collections::HashSet<String>>,
    ) {
        match item {
            SyntaxItemSpec::NonTerminal { category, .. } => {
                if category != rule_cat {
                    connections.entry(rule_cat.to_string()).or_default().insert(category.clone());
                    connections.entry(category.clone()).or_default().insert(rule_cat.to_string());
                }
            }
            SyntaxItemSpec::Binder { category, .. } => {
                if category != rule_cat {
                    connections.entry(rule_cat.to_string()).or_default().insert(category.clone());
                    connections.entry(category.clone()).or_default().insert(rule_cat.to_string());
                }
            }
            SyntaxItemSpec::Collection { element_category, .. } => {
                if element_category != rule_cat {
                    connections.entry(rule_cat.to_string()).or_default().insert(element_category.clone());
                    connections.entry(element_category.clone()).or_default().insert(rule_cat.to_string());
                }
            }
            SyntaxItemSpec::Sep { body, .. } => {
                collect_cross_refs(body, rule_cat, connections);
            }
            SyntaxItemSpec::Map { body_items } => {
                for sub in body_items {
                    collect_cross_refs(sub, rule_cat, connections);
                }
            }
            SyntaxItemSpec::Zip { left_category, right_category, body, .. } => {
                for ref_cat in [left_category.as_str(), right_category.as_str()] {
                    if ref_cat != rule_cat {
                        connections.entry(rule_cat.to_string()).or_default().insert(ref_cat.to_string());
                        connections.entry(ref_cat.to_string()).or_default().insert(rule_cat.to_string());
                    }
                }
                collect_cross_refs(body, rule_cat, connections);
            }
            SyntaxItemSpec::Optional { inner } => {
                for sub in inner {
                    collect_cross_refs(sub, rule_cat, connections);
                }
            }
            _ => {}
        }
    }

    /// Strip all non-Terminal items from a grammar, leaving only Terminal items.
    fn terminalize(
        all_syntax: &[(String, String, Vec<SyntaxItemSpec>)],
    ) -> Vec<(String, String, Vec<SyntaxItemSpec>)> {
        all_syntax
            .iter()
            .map(|(label, cat, items)| {
                let terminal_items: Vec<SyntaxItemSpec> = items
                    .iter()
                    .filter_map(|item| match item {
                        SyntaxItemSpec::Terminal(t) => Some(SyntaxItemSpec::Terminal(t.clone())),
                        _ => None,
                    })
                    .collect();
                let items = if terminal_items.is_empty() {
                    vec![SyntaxItemSpec::Terminal("fallback".to_string())]
                } else {
                    terminal_items
                };
                (label.clone(), cat.clone(), items)
            })
            .collect()
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(30))]

        // ── Property 1: disconnected ↔ no cross-category references ────────
        /// A disconnected tape index `i` means category `categories[i]` has
        /// no inbound NonTerminal references from other categories AND no
        /// outbound NonTerminal references to other categories.
        #[test]
        fn prop_disconnected_no_cross_references(
            (categories, all_syntax) in arb_small_grammar(),
        ) {
            let result = analyze_from_bundle(&all_syntax, &categories);
            let connectivity = build_connectivity(&all_syntax);

            for &tape_idx in &result.disconnected_tapes {
                let cat_name = &categories[tape_idx].name;
                // A disconnected tape should have no cross-category connections.
                let has_connections = connectivity
                    .get(cat_name)
                    .map_or(false, |conns| {
                        // Only count connections to categories that actually
                        // exist in this grammar.
                        let cat_set: std::collections::HashSet<&str> =
                            categories.iter().map(|c| c.name.as_str()).collect();
                        conns.iter().any(|c| cat_set.contains(c.as_str()))
                    });
                prop_assert!(
                    !has_connections,
                    "disconnected tape {} ({}) has cross-category connections",
                    tape_idx,
                    cat_name,
                );
            }
        }

        // ── Property 2: connected categories not disconnected ───────────────
        /// If category A references category B via NonTerminal (and both are
        /// in the grammar), neither A nor B should be in `disconnected_tapes`.
        #[test]
        fn prop_connected_not_disconnected(
            (categories, all_syntax) in arb_small_grammar(),
        ) {
            let result = analyze_from_bundle(&all_syntax, &categories);
            let connectivity = build_connectivity(&all_syntax);
            let cat_to_idx: std::collections::HashMap<&str, usize> = categories
                .iter()
                .enumerate()
                .map(|(i, c)| (c.name.as_str(), i))
                .collect();

            for (cat_a, connections) in &connectivity {
                if let Some(&idx_a) = cat_to_idx.get(cat_a.as_str()) {
                    for cat_b in connections {
                        if let Some(&idx_b) = cat_to_idx.get(cat_b.as_str()) {
                            prop_assert!(
                                !result.disconnected_tapes.contains(&idx_a),
                                "category {} (idx {}) references {} but is disconnected",
                                cat_a,
                                idx_a,
                                cat_b,
                            );
                            prop_assert!(
                                !result.disconnected_tapes.contains(&idx_b),
                                "category {} (idx {}) is referenced by {} but is disconnected",
                                cat_b,
                                idx_b,
                                cat_a,
                            );
                        }
                    }
                }
            }
        }

        // ── Property 3: disconnected indices are valid ──────────────────────
        /// Every index in `disconnected_tapes` satisfies `i < categories.len()`.
        #[test]
        fn prop_disconnected_subset_all_tapes(
            (categories, all_syntax) in arb_small_grammar(),
        ) {
            let result = analyze_from_bundle(&all_syntax, &categories);
            for &tape_idx in &result.disconnected_tapes {
                prop_assert!(
                    tape_idx < categories.len(),
                    "disconnected tape {} >= categories.len() {}",
                    tape_idx,
                    categories.len(),
                );
            }
        }

        // ── Property 4: all-terminal → all disconnected ─────────────────────
        /// A grammar with only Terminal items should have every category index
        /// in `disconnected_tapes` (no cross-category references exist).
        #[test]
        fn prop_all_terminal_all_disconnected(
            (categories, all_syntax) in arb_small_grammar(),
        ) {
            let terminal_only = terminalize(&all_syntax);
            let result = analyze_from_bundle(&terminal_only, &categories);

            for i in 0..categories.len() {
                prop_assert!(
                    result.disconnected_tapes.contains(&i),
                    "terminal-only grammar: category {} ({}) should be disconnected",
                    i,
                    categories[i].name,
                );
            }
        }

        // ── Property 5: overlapping tape indices are valid ──────────────────
        /// Every index in `overlapping_tapes` pairs satisfies `i < categories.len()`.
        #[test]
        fn prop_overlapping_tapes_subset_all(
            (categories, all_syntax) in arb_grammar(2..6, 1..5),
        ) {
            let result = analyze_from_bundle(&all_syntax, &categories);
            for &(idx_a, idx_b) in &result.overlapping_tapes {
                prop_assert!(
                    idx_a < categories.len(),
                    "overlapping tape idx {} >= categories.len() {}",
                    idx_a,
                    categories.len(),
                );
                prop_assert!(
                    idx_b < categories.len(),
                    "overlapping tape idx {} >= categories.len() {}",
                    idx_b,
                    categories.len(),
                );
            }
        }

        // ── Property 6: disconnected count bounded ──────────────────────────
        /// The number of disconnected tapes cannot exceed the total number
        /// of categories.
        #[test]
        fn prop_disconnected_count_le_categories(
            (categories, all_syntax) in arb_small_grammar(),
        ) {
            let result = analyze_from_bundle(&all_syntax, &categories);
            prop_assert!(
                result.disconnected_tapes.len() <= categories.len(),
                "disconnected_tapes.len() {} > categories.len() {}",
                result.disconnected_tapes.len(),
                categories.len(),
            );
        }
    }
}
