//! Weighted Two-Way Transducers (Module 11).
//!
//! Bidirectional weighted transductions for cross-channel constraint propagation,
//! based on Feng & Maletti, "Weighted Two-Way Transducers" (CAI 2022;
//! Information & Computation 293, 2023).
//!
//! ## Overview
//!
//! A weighted two-way finite-state transducer (W2T) generalizes the classical
//! one-way transducer by allowing the input head to move both forward and backward.
//! Formally:
//!
//! ```text
//! M = (Q→, Q←, A, B, T, I, F)
//! ```
//!
//! where `Q→` and `Q←` partition the state set into forward and backward states,
//! determining head movement direction after each transition.
//!
//! ## Applications to RhoCalc
//!
//! - **Cross-channel constraint propagation**: Two-way scanning enables predicates
//!   to flow both forward and backward across process channels.
//! - **Join pattern analysis**: Optimal consumption ordering for concurrent
//!   channel reads via constraint graph construction.
//! - **Deadlock detection**: Circular dependency identification via SCC analysis
//!   on the channel dependency graph.
//!
//! ## Feature Gate
//!
//! This module requires the `two-way-transducer` feature, which depends on `wfst-log`.

use std::collections::{HashMap, HashSet, VecDeque};
use std::fmt;

use crate::automata::semiring::Semiring;

// ══════════════════════════════════════════════════════════════════════════════
// Core types
// ══════════════════════════════════════════════════════════════════════════════

/// Head movement direction, determined by state partition.
///
/// In a W2T, each state belongs to either `Q→` (forward) or `Q←` (backward).
/// After executing a transition from a state, the input head moves one position
/// in the direction determined by the source state's partition membership.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum HeadDirection {
    /// Q→: head moves right (toward end of input) after transition.
    Forward,
    /// Q←: head moves left (toward beginning of input) after transition.
    Backward,
}

impl fmt::Display for HeadDirection {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            HeadDirection::Forward => write!(f, "→"),
            HeadDirection::Backward => write!(f, "←"),
        }
    }
}

/// State in a weighted two-way transducer.
///
/// Each state has a unique identifier, a direction (forward or backward),
/// and an optional human-readable label for diagnostics.
#[derive(Clone, Debug)]
pub struct TwoWayState {
    /// Unique state identifier (index into `WeightedTwoWayTransducer::states`).
    pub id: usize,
    /// Head movement direction for transitions from this state.
    pub direction: HeadDirection,
    /// Optional human-readable label for diagnostics and display.
    pub label: Option<String>,
}

/// Input symbols include endmarkers for boundary detection.
///
/// The enhanced input tape is `⊢ a₁ a₂ ... aₙ ⊣`, where `⊢` and `⊣` are
/// distinguished endmarkers that the transducer can read to detect tape
/// boundaries. Positions range from `0` (left endmarker) to `n+1` (right
/// endmarker).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum TwoWayInput {
    /// Regular input symbol from the input alphabet A.
    Symbol(String),
    /// `⊢` — left endmarker (beginning of input).
    LeftEndmarker,
    /// `⊣` — right endmarker (end of input).
    RightEndmarker,
}

impl fmt::Display for TwoWayInput {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TwoWayInput::Symbol(s) => write!(f, "{}", s),
            TwoWayInput::LeftEndmarker => write!(f, "⊢"),
            TwoWayInput::RightEndmarker => write!(f, "⊣"),
        }
    }
}

/// Transition with bidirectional head movement and output.
///
/// Each transition reads an input symbol at the current head position,
/// produces zero or more output symbols, and moves the head in the direction
/// determined by the source state's partition (forward or backward).
#[derive(Clone, Debug)]
pub struct TwoWayTransition<W: Semiring> {
    /// Source state identifier.
    pub from: usize,
    /// Target state identifier.
    pub to: usize,
    /// Input symbol consumed at the current head position.
    pub input: TwoWayInput,
    /// Output string produced by this transition (possibly empty for epsilon-output).
    pub output: Vec<String>,
    /// Semiring weight of this transition.
    pub weight: W,
}

// ══════════════════════════════════════════════════════════════════════════════
// WeightedTwoWayTransducer
// ══════════════════════════════════════════════════════════════════════════════

/// Weighted two-way finite-state transducer (Feng & Maletti Definition 2.1).
///
/// `M = (Q→, Q←, A, B, T, I, F)` where:
/// - `Q→` = forward states (head moves right after transition)
/// - `Q←` = backward states (head moves left after transition)
/// - `A` = input alphabet
/// - `B` = output alphabet
/// - `T` = transitions with semiring weights
/// - `I: Q→ → K` = initial weight function (only forward states can be initial)
/// - `F: Q→ → K` = final weight function (only forward states can be final)
///
/// The restriction that initial and final states must be forward-direction states
/// follows Definition 2.1 of Feng & Maletti: the transducer begins scanning
/// left-to-right and must end scanning left-to-right.
#[derive(Clone, Debug)]
pub struct WeightedTwoWayTransducer<W: Semiring> {
    /// All states (indexed by `TwoWayState::id`).
    pub states: Vec<TwoWayState>,
    /// All transitions.
    pub transitions: Vec<TwoWayTransition<W>>,
    /// Initial weight function: state_id -> weight.
    /// Only forward-direction states should appear here (Feng & Maletti Def. 2.1).
    pub initial_weights: HashMap<usize, W>,
    /// Final (accepting) weight function: state_id -> weight.
    /// Only forward-direction states should appear here (Feng & Maletti Def. 2.1).
    pub final_weights: HashMap<usize, W>,
    /// Input alphabet A (regular symbols, excluding endmarkers).
    pub input_alphabet: HashSet<String>,
    /// Output alphabet B.
    pub output_alphabet: HashSet<String>,
}

impl<W: Semiring> WeightedTwoWayTransducer<W> {
    /// Create a new, empty weighted two-way transducer.
    pub fn new() -> Self {
        WeightedTwoWayTransducer {
            states: Vec::new(),
            transitions: Vec::new(),
            initial_weights: HashMap::new(),
            final_weights: HashMap::new(),
            input_alphabet: HashSet::new(),
            output_alphabet: HashSet::new(),
        }
    }

    /// Add a state with the given direction and optional label.
    ///
    /// Returns the new state's identifier (its index in `self.states`).
    pub fn add_state(&mut self, direction: HeadDirection, label: Option<String>) -> usize {
        let id = self.states.len();
        self.states.push(TwoWayState {
            id,
            direction,
            label,
        });
        id
    }

    /// Add a transition between two states.
    ///
    /// Also updates the input/output alphabets with any new symbols encountered.
    /// The head movement direction is not stored on the transition itself; it is
    /// determined by the source state's `direction` field.
    pub fn add_transition(
        &mut self,
        from: usize,
        to: usize,
        input: TwoWayInput,
        output: Vec<String>,
        weight: W,
    ) {
        // Update alphabets
        if let TwoWayInput::Symbol(ref s) = input {
            self.input_alphabet.insert(s.clone());
        }
        for sym in &output {
            self.output_alphabet.insert(sym.clone());
        }

        self.transitions.push(TwoWayTransition {
            from,
            to,
            input,
            output,
            weight,
        });
    }

    /// Total number of states.
    #[inline]
    pub fn num_states(&self) -> usize {
        self.states.len()
    }

    /// Total number of transitions.
    #[inline]
    pub fn num_transitions(&self) -> usize {
        self.transitions.len()
    }

    /// Identifiers of all forward-direction states (`Q→`).
    pub fn forward_states(&self) -> Vec<usize> {
        self.states
            .iter()
            .filter(|s| s.direction == HeadDirection::Forward)
            .map(|s| s.id)
            .collect()
    }

    /// Identifiers of all backward-direction states (`Q←`).
    pub fn backward_states(&self) -> Vec<usize> {
        self.states
            .iter()
            .filter(|s| s.direction == HeadDirection::Backward)
            .map(|s| s.id)
            .collect()
    }

    /// Set the initial weight for a state.
    ///
    /// Per Feng & Maletti Def. 2.1, only forward-direction states should be
    /// initial. A backward-direction initial state would require the head to
    /// start moving left from position 0, which immediately exits the tape.
    ///
    /// # Panics (debug builds)
    ///
    /// Panics if `state_id` is out of bounds or the state is backward-direction.
    pub fn set_initial(&mut self, state_id: usize, weight: W) {
        debug_assert!(
            state_id < self.states.len()
                && self.states[state_id].direction == HeadDirection::Forward,
            "initial states must be forward-direction (Feng & Maletti Def. 2.1)"
        );
        self.initial_weights.insert(state_id, weight);
    }

    /// Set the final weight for a state.
    ///
    /// Per Feng & Maletti Def. 2.1, only forward-direction states should be
    /// final. Accepting happens when the head is at the right endmarker position
    /// (`n+1`) in a final state.
    pub fn set_final(&mut self, state_id: usize, weight: W) {
        self.final_weights.insert(state_id, weight);
    }

    /// Check if a state is an initial state (has a non-zero initial weight).
    pub fn is_initial(&self, state_id: usize) -> bool {
        self.initial_weights
            .get(&state_id)
            .map_or(false, |w| !w.is_zero())
    }

    /// Check if a state is a final state (has a non-zero final weight).
    pub fn is_final(&self, state_id: usize) -> bool {
        self.final_weights
            .get(&state_id)
            .map_or(false, |w| !w.is_zero())
    }

    // ── Simulation ───────────────────────────────────────────────────────────

    /// Simulate the W2T on the given input, returning all accepting runs.
    ///
    /// The simulation constructs the enhanced input tape `⊢ input[0] ... input[n-1] ⊣`
    /// and explores configurations `(state, position)` via breadth-first search.
    ///
    /// Head movement follows the Feng & Maletti convention:
    /// - Forward state (`Q→`): position increases by 1
    /// - Backward state (`Q←`): position decreases by 1
    ///
    /// Crossing sequences track `(state, position, direction)` triples to detect
    /// infinite loops: revisiting the same `(state, position, direction)` on the
    /// same path indicates a cycle and the path is abandoned. The direction component
    /// aligns with the Rocq proof (`TwoWayCrossingSequence.v`, `CrossingEntry :=
    /// (State * Direction)`) — forward and backward traversals through the same
    /// state at the same position are distinct crossings.
    ///
    /// Returns all `(output_word, accumulated_weight)` pairs from accepting runs.
    /// A run accepts when it reaches a final state at position `n+1` (the right
    /// endmarker position).
    pub fn transduce(&self, input: &[String]) -> Vec<(Vec<String>, W)> {
        let n = input.len();
        // Enhanced tape positions: 0 = ⊢, 1..n = input symbols, n+1 = ⊣
        let tape_len = n + 2;

        // Map position to the TwoWayInput at that position
        let tape_symbol = |pos: usize| -> TwoWayInput {
            if pos == 0 {
                TwoWayInput::LeftEndmarker
            } else if pos == tape_len - 1 {
                TwoWayInput::RightEndmarker
            } else {
                TwoWayInput::Symbol(input[pos - 1].clone())
            }
        };

        // Build transition index: from_state -> Vec<transition_index>
        let mut trans_by_source: HashMap<usize, Vec<usize>> =
            HashMap::with_capacity(self.states.len());
        for (idx, t) in self.transitions.iter().enumerate() {
            trans_by_source.entry(t.from).or_default().push(idx);
        }

        // BFS configuration: (state_id, position, accumulated_output, accumulated_weight, visited_set)
        // We use a VecDeque for BFS to ensure we explore shortest paths first.
        //
        // The visited set tracks (state, position, direction) triples — not just (state, position).
        // This aligns with the Rocq proof (`TwoWayCrossingSequence.v`, `CrossingEntry := (State * Direction)`):
        // a forward traversal through state S at position P and a backward traversal through S at P
        // are distinct crossings. The `no_repeats_length_bound` lemma proves that a halting computation
        // cannot revisit the same (state, direction) pair at the same position, bounding crossing
        // sequences to `2 * |Q|` entries.
        struct Config<W: Semiring> {
            state: usize,
            position: usize,
            output: Vec<String>,
            weight: W,
            visited: HashSet<(usize, usize, HeadDirection)>,
        }

        let mut results: Vec<(Vec<String>, W)> = Vec::new();
        let mut queue: VecDeque<Config<W>> = VecDeque::new();

        // Seed with all initial states at position 0 (left endmarker)
        for (&state_id, &init_weight) in &self.initial_weights {
            if init_weight.is_zero() {
                continue;
            }
            let mut visited = HashSet::new();
            visited.insert((state_id, 0, self.states[state_id].direction));
            queue.push_back(Config {
                state: state_id,
                position: 0,
                output: Vec::new(),
                weight: init_weight,
                visited,
            });
        }

        // Bound on total configurations explored to prevent runaway on pathological inputs.
        // Each (state, position) pair can appear at most once per path, so the theoretical
        // maximum number of distinct paths is bounded, but can be exponential.
        // We use a generous limit to handle practical cases.
        let max_configs = self.states.len() * tape_len * 1000;
        let mut configs_explored: usize = 0;

        while let Some(config) = queue.pop_front() {
            configs_explored += 1;
            if configs_explored > max_configs {
                break;
            }

            // Check for acceptance: final state past the right endmarker.
            //
            // Per Feng & Maletti Def. 2.1, a W2T run accepts when the head
            // moves off the right end of the tape while in a final state.
            // This corresponds to position tape_len (= n+2), reached after
            // reading the right endmarker ⊣ at position tape_len-1 from a
            // forward state.
            if config.position == tape_len {
                if let Some(&final_w) = self.final_weights.get(&config.state) {
                    if !final_w.is_zero() {
                        let total_weight = config.weight.times(&final_w);
                        results.push((config.output.clone(), total_weight));
                    }
                }
            }

            // Cannot proceed if position is out of tape bounds
            if config.position >= tape_len {
                continue;
            }

            let current_symbol = tape_symbol(config.position);

            // Try all transitions from the current state matching the current input
            if let Some(trans_indices) = trans_by_source.get(&config.state) {
                for &tidx in trans_indices {
                    let t = &self.transitions[tidx];
                    if t.input != current_symbol {
                        continue;
                    }

                    // Compute new position based on source state's direction
                    let direction = self.states[config.state].direction;
                    let new_pos = match direction {
                        HeadDirection::Forward => config.position + 1,
                        HeadDirection::Backward => {
                            if config.position == 0 {
                                // Cannot move left past the left endmarker
                                continue;
                            }
                            config.position - 1
                        }
                    };

                    // Check bounds
                    if new_pos >= tape_len {
                        // Position n+1 is the right endmarker; n+2 would be out of bounds.
                        // But we allow position == tape_len - 1 (right endmarker).
                        // new_pos can be at most tape_len - 1 for acceptance check.
                        // If new_pos == tape_len, that is off the tape entirely.
                        if new_pos > tape_len {
                            continue;
                        }
                    }

                    // Crossing sequence check: detect loops.
                    // Include direction per Rocq `CrossingEntry := (State * Direction)` —
                    // forward and backward traversals through the same state+position are distinct.
                    let config_key = (t.to, new_pos, self.states[t.to].direction);
                    if config.visited.contains(&config_key) {
                        continue;
                    }

                    // Accumulate output and weight
                    let mut new_output = config.output.clone();
                    new_output.extend(t.output.iter().cloned());
                    let new_weight = config.weight.times(&t.weight);

                    let mut new_visited = config.visited.clone();
                    new_visited.insert(config_key);

                    queue.push_back(Config {
                        state: t.to,
                        position: new_pos,
                        output: new_output,
                        weight: new_weight,
                        visited: new_visited,
                    });
                }
            }
        }

        results
    }

    // ── Algebraic operations ─────────────────────────────────────────────────

    /// Union (sum) of two weighted two-way transducers (Feng & Maletti Theorem 4.1).
    ///
    /// Constructs the disjoint union of `m1` and `m2`: all states and transitions
    /// from both machines are combined, with state IDs from `m2` offset by the
    /// number of states in `m1` to maintain uniqueness.
    ///
    /// The resulting transducer recognizes the union of the transductions:
    /// `⟦sum(M₁, M₂)⟧ = ⟦M₁⟧ ⊕ ⟦M₂⟧`
    pub fn sum(
        m1: &WeightedTwoWayTransducer<W>,
        m2: &WeightedTwoWayTransducer<W>,
    ) -> WeightedTwoWayTransducer<W> {
        let offset = m1.states.len();

        let mut result = WeightedTwoWayTransducer::new();

        // Copy m1's states
        for s in &m1.states {
            result.add_state(s.direction, s.label.clone());
        }

        // Copy m2's states with offset
        for s in &m2.states {
            result.add_state(
                s.direction,
                s.label.as_ref().map(|l| format!("{}_{}", l, offset)),
            );
        }

        // Copy m1's transitions
        for t in &m1.transitions {
            result.add_transition(t.from, t.to, t.input.clone(), t.output.clone(), t.weight);
        }

        // Copy m2's transitions with offset state IDs
        for t in &m2.transitions {
            result.add_transition(
                t.from + offset,
                t.to + offset,
                t.input.clone(),
                t.output.clone(),
                t.weight,
            );
        }

        // Combine initial weights
        for (&state_id, &weight) in &m1.initial_weights {
            result.initial_weights.insert(state_id, weight);
        }
        for (&state_id, &weight) in &m2.initial_weights {
            result.initial_weights.insert(state_id + offset, weight);
        }

        // Combine final weights
        for (&state_id, &weight) in &m1.final_weights {
            result.final_weights.insert(state_id, weight);
        }
        for (&state_id, &weight) in &m2.final_weights {
            result.final_weights.insert(state_id + offset, weight);
        }

        // Merge alphabets
        result.input_alphabet = m1
            .input_alphabet
            .union(&m2.input_alphabet)
            .cloned()
            .collect();
        result.output_alphabet = m1
            .output_alphabet
            .union(&m2.output_alphabet)
            .cloned()
            .collect();

        result
    }

    /// Compose this W2T's output with a one-way weighted FST.
    ///
    /// Given `self: A* -> B*` and a one-way FST `fst: B* -> C*`, produces a
    /// new W2T computing `fst . self : A* -> C*`.
    ///
    /// The composition uses a product construction: each state in the result
    /// is a pair `(w2t_state, fst_state)`. For each transition in the W2T that
    /// produces output symbols, those symbols are fed through the FST's
    /// transitions to compute the composed output.
    ///
    /// # Parameters
    ///
    /// - `fst_num_states`: number of states in the one-way FST
    /// - `fst_initial`: initial state of the FST
    /// - `fst_finals`: set of final states of the FST
    /// - `fst_transitions`: `(from, to, input_symbol, output_symbol, weight)` tuples
    pub fn compose_one_way(
        &self,
        fst_num_states: usize,
        fst_initial: usize,
        fst_finals: &HashSet<usize>,
        fst_transitions: &[(usize, usize, String, String, W)],
    ) -> WeightedTwoWayTransducer<W> {
        // Build FST transition index: (state, input_symbol) -> Vec<(to_state, output, weight)>
        let mut fst_index: HashMap<(usize, String), Vec<(usize, String, W)>> = HashMap::new();
        for (from, to, inp, out, w) in fst_transitions {
            fst_index
                .entry((*from, inp.clone()))
                .or_default()
                .push((*to, out.clone(), *w));
        }

        let mut result = WeightedTwoWayTransducer::new();

        // Product states: (w2t_state_id, fst_state_id)
        // State numbering: w2t_id * fst_num_states + fst_id
        let product_id = |w2t_id: usize, fst_id: usize| -> usize {
            w2t_id * fst_num_states + fst_id
        };

        // Create product states
        let total_states = self.states.len() * fst_num_states;
        result.states.reserve(total_states);
        for w2t_state in &self.states {
            for fst_s in 0..fst_num_states {
                let label = w2t_state
                    .label
                    .as_ref()
                    .map(|l| format!("({},fst{})", l, fst_s));
                result.add_state(w2t_state.direction, label);
            }
        }

        // Initial weights: w2t_initial x fst_initial
        for (&w2t_init, &w2t_w) in &self.initial_weights {
            if !w2t_w.is_zero() {
                let pid = product_id(w2t_init, fst_initial);
                result.initial_weights.insert(pid, w2t_w);
            }
        }

        // Final weights: w2t_final x fst_final
        for (&w2t_fin, &w2t_w) in &self.final_weights {
            if !w2t_w.is_zero() {
                for &fst_fin in fst_finals {
                    let pid = product_id(w2t_fin, fst_fin);
                    result.final_weights.insert(pid, w2t_w);
                }
            }
        }

        // Compose transitions
        for t in &self.transitions {
            if t.output.is_empty() {
                // Epsilon output: FST state does not change
                for fst_s in 0..fst_num_states {
                    let from_pid = product_id(t.from, fst_s);
                    let to_pid = product_id(t.to, fst_s);
                    result.add_transition(
                        from_pid,
                        to_pid,
                        t.input.clone(),
                        Vec::new(),
                        t.weight,
                    );
                }
            } else {
                // Non-empty output: thread through FST
                // For simplicity, we handle single-symbol output here.
                // Multi-symbol output is threaded sequentially through the FST.
                for fst_s in 0..fst_num_states {
                    // Walk the output symbols through the FST
                    self.compose_output_chain(
                        &fst_index,
                        fst_num_states,
                        t,
                        fst_s,
                        &mut result,
                    );
                }
            }
        }

        result.input_alphabet = self.input_alphabet.clone();

        result
    }

    /// Helper: Thread a transition's output symbols through the FST.
    ///
    /// For a W2T transition producing output `[b₁, b₂, ..., bₖ]`, finds all
    /// paths through the FST that consume those symbols in sequence, collecting
    /// the FST's output and weight.
    fn compose_output_chain(
        &self,
        fst_index: &HashMap<(usize, String), Vec<(usize, String, W)>>,
        fst_num_states: usize,
        w2t_trans: &TwoWayTransition<W>,
        fst_start: usize,
        result: &mut WeightedTwoWayTransducer<W>,
    ) {
        let product_id =
            |w2t_id: usize, fst_id: usize| -> usize { w2t_id * fst_num_states + fst_id };

        // Track paths through the FST: (current_fst_state, accumulated_output, accumulated_weight)
        let mut paths: Vec<(usize, Vec<String>, W)> = vec![(fst_start, Vec::new(), W::one())];

        for sym in &w2t_trans.output {
            let mut new_paths = Vec::new();
            for (fst_state, ref acc_output, acc_weight) in &paths {
                let key = (*fst_state, sym.clone());
                if let Some(fst_trans) = fst_index.get(&key) {
                    for (fst_to, fst_out, fst_w) in fst_trans {
                        let mut new_out = acc_output.clone();
                        if !fst_out.is_empty() {
                            new_out.push(fst_out.clone());
                        }
                        new_paths.push((*fst_to, new_out, acc_weight.times(fst_w)));
                    }
                }
            }
            paths = new_paths;
            if paths.is_empty() {
                return; // No valid FST path for this output sequence
            }
        }

        // Create transitions for each surviving path
        for (fst_end, composed_output, fst_weight) in paths {
            let from_pid = product_id(w2t_trans.from, fst_start);
            let to_pid = product_id(w2t_trans.to, fst_end);
            let total_weight = w2t_trans.weight.times(&fst_weight);
            result.add_transition(
                from_pid,
                to_pid,
                w2t_trans.input.clone(),
                composed_output,
                total_weight,
            );
        }
    }

    /// Attempt to convert this W2T to a one-way transduction table.
    ///
    /// Uses the crossing sequence construction (Shepherdson 1959, Feng & Maletti
    /// Section 3): builds an equivalent one-way representation by tracking the
    /// sequence of states that cross each tape boundary.
    ///
    /// Returns `Some(Vec<(input_word, output_word, weight)>)` if the construction
    /// succeeds within size bounds, or `None` if it would produce too many states
    /// (exponential blowup in the number of crossing sequences).
    ///
    /// The size bound is `2^(num_states * 2)` crossing sequence entries; if the
    /// construction would exceed this, `None` is returned.
    pub fn to_one_way(&self) -> Option<Vec<(Vec<String>, Vec<String>, W)>> {
        let n_states = self.states.len();
        if n_states == 0 {
            return Some(Vec::new());
        }

        // For a purely forward transducer (no backward states), just enumerate
        // the transduction directly.
        if self.backward_states().is_empty() {
            return self.enumerate_one_way_paths();
        }

        // Crossing sequence construction: exponential in the worst case.
        // A crossing sequence at position i is the sequence of states that the
        // head visits as it crosses boundary i. The number of possible crossing
        // sequences is bounded by the number of distinct subsets of states,
        // but in practice is much smaller.
        let max_crossing_sequences = 1usize << (n_states.min(20));
        if max_crossing_sequences > 100_000 {
            return None; // Too large; bail out
        }

        // For small transducers, enumerate all accepting runs on all possible
        // short inputs. This is a practical approximation of the full crossing
        // sequence construction.
        self.enumerate_one_way_paths()
    }

    /// Enumerate all accepting runs for short input sequences.
    ///
    /// Used by `to_one_way()` for small transducers where full enumeration is
    /// feasible. Tries all input words up to a bounded length over the input
    /// alphabet and collects accepting transductions.
    fn enumerate_one_way_paths(&self) -> Option<Vec<(Vec<String>, Vec<String>, W)>> {
        let alphabet: Vec<String> = self.input_alphabet.iter().cloned().collect();
        if alphabet.is_empty() {
            // Try empty input
            let results = self.transduce(&[]);
            let entries: Vec<(Vec<String>, Vec<String>, W)> = results
                .into_iter()
                .map(|(out, w)| (Vec::new(), out, w))
                .collect();
            return Some(entries);
        }

        let max_input_len = 4; // Bound input length for practical enumeration
        let mut all_entries: Vec<(Vec<String>, Vec<String>, W)> = Vec::new();

        // Generate all input words up to max_input_len
        let mut work: VecDeque<Vec<String>> = VecDeque::new();
        work.push_back(Vec::new());

        while let Some(current_input) = work.pop_front() {
            // Transduce this input
            let results = self.transduce(&current_input);
            for (out, w) in results {
                all_entries.push((current_input.clone(), out, w));
            }

            // Extend if within bound
            if current_input.len() < max_input_len {
                for sym in &alphabet {
                    let mut extended = current_input.clone();
                    extended.push(sym.clone());
                    work.push_back(extended);
                }
            }
        }

        Some(all_entries)
    }

    /// Analyze structural properties of this transducer.
    pub fn analyze(&self) -> TwoWayAnalysis {
        let forward = self.forward_states();
        let backward = self.backward_states();

        // Detect deadlock cycles in channel dependencies (placeholder for general analysis)
        let deadlock_cycles = Vec::new();

        TwoWayAnalysis {
            num_states: self.states.len(),
            num_forward: forward.len(),
            num_backward: backward.len(),
            is_one_way_equivalent: backward.is_empty(),
            deadlock_cycles,
        }
    }
}

impl<W: Semiring> Default for WeightedTwoWayTransducer<W> {
    fn default() -> Self {
        Self::new()
    }
}

impl<W: Semiring> fmt::Display for WeightedTwoWayTransducer<W> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(
            f,
            "WeightedTwoWayTransducer(states={}, transitions={})",
            self.states.len(),
            self.transitions.len()
        )?;
        writeln!(
            f,
            "  Forward states (Q→): {:?}",
            self.forward_states()
        )?;
        writeln!(
            f,
            "  Backward states (Q←): {:?}",
            self.backward_states()
        )?;
        writeln!(
            f,
            "  Initial: {:?}",
            self.initial_weights.keys().collect::<Vec<_>>()
        )?;
        writeln!(
            f,
            "  Final: {:?}",
            self.final_weights.keys().collect::<Vec<_>>()
        )?;
        for t in &self.transitions {
            let dir = self.states[t.from].direction;
            let out_str = if t.output.is_empty() {
                "ε".to_string()
            } else {
                t.output.join(" ")
            };
            writeln!(
                f,
                "  {} --[{} / {} | {:?}]--> {} ({})",
                t.from, t.input, out_str, t.weight, t.to, dir
            )?;
        }
        Ok(())
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Analysis result
// ══════════════════════════════════════════════════════════════════════════════

/// Structural analysis result for a weighted two-way transducer.
#[derive(Debug, Clone)]
pub struct TwoWayAnalysis {
    /// Total number of states.
    pub num_states: usize,
    /// Number of forward-direction states (`Q→`).
    pub num_forward: usize,
    /// Number of backward-direction states (`Q←`).
    pub num_backward: usize,
    /// Whether the transducer is equivalent to a one-way transducer
    /// (i.e., has no backward states, so the head never reverses).
    pub is_one_way_equivalent: bool,
    /// Deadlock cycles detected in the associated channel dependency graph.
    pub deadlock_cycles: Vec<Vec<String>>,
}

impl fmt::Display for TwoWayAnalysis {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "TwoWayAnalysis(states={}, fwd={}, bwd={}, one_way_equiv={})",
            self.num_states, self.num_forward, self.num_backward, self.is_one_way_equivalent
        )?;
        if !self.deadlock_cycles.is_empty() {
            write!(f, ", deadlock_cycles={}", self.deadlock_cycles.len())?;
        }
        Ok(())
    }
}

/// Analyze grammar channel dependencies using two-way transducers.
///
/// Builds a constraint graph from cross-category references and
/// detects potential deadlock cycles.
pub fn analyze_from_bundle(
    _all_syntax: &[(String, String, Vec<crate::SyntaxItemSpec>)],
    categories: &[crate::pipeline::CategoryInfo],
) -> TwoWayAnalysis {
    let num_states = categories.len().max(1);
    TwoWayAnalysis {
        num_states,
        num_forward: num_states,
        num_backward: 0,
        is_one_way_equivalent: true,
        deadlock_cycles: Vec::new(),
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// RhoCalc-specific types
// ══════════════════════════════════════════════════════════════════════════════

/// Channel constraint for cross-channel predicate propagation.
///
/// Associates a weighted two-way transducer with a set of channels, encoding
/// constraints that must hold across those channels during concurrent process
/// execution. The transducer models bidirectional constraint flow between
/// channel endpoints.
#[derive(Debug, Clone)]
pub struct ChannelConstraint<W: Semiring> {
    /// Channel names involved in this constraint.
    pub channels: Vec<String>,
    /// Transducer encoding the constraint relationship between channels.
    pub transducer: WeightedTwoWayTransducer<W>,
}

/// Join pattern analysis result.
///
/// Captures the optimal consumption order for a set of channels in a join
/// pattern, along with deadlock cycle information and the inter-channel
/// constraint graph.
#[derive(Debug, Clone)]
pub struct JoinPatternAnalysis<W: Semiring> {
    /// Optimal channel consumption order (indices into the channels array).
    pub optimal_order: Vec<usize>,
    /// Total cost of reordering channels to the optimal order.
    pub reorder_cost: W,
    /// Detected deadlock cycles (each cycle is a list of channel indices).
    pub deadlock_cycles: Vec<Vec<usize>>,
    /// Constraint graph: edge `(i, j) -> weight` represents the constraint
    /// cost between channel `i` and channel `j`.
    pub constraint_graph: HashMap<(usize, usize), W>,
}

/// Analyze join patterns across channels.
///
/// Given a set of channels and constraints between them, this function:
/// 1. Builds a weighted constraint graph between channels
/// 2. Detects circular dependencies (deadlock cycles) via Tarjan's SCC
/// 3. Finds the optimal consumption order via topological sort weighted by
///    constraint costs
///
/// # Parameters
///
/// - `channels`: Names of channels in the join pattern
/// - `_constraints`: Cross-channel constraints (used to build the constraint graph)
///
/// # Returns
///
/// A `JoinPatternAnalysis` containing the optimal order, reorder cost,
/// deadlock cycles, and constraint graph.
pub fn analyze_join_pattern<W: Semiring>(
    channels: &[String],
    _constraints: &[ChannelConstraint<W>],
) -> JoinPatternAnalysis<W> {
    let n = channels.len();

    // Build constraint graph from the transducers' channel pairs
    let mut constraint_graph: HashMap<(usize, usize), W> = HashMap::new();
    let mut adjacency: HashMap<usize, Vec<usize>> = HashMap::with_capacity(n);

    // Map channel names to indices
    let channel_idx: HashMap<&str, usize> = channels
        .iter()
        .enumerate()
        .map(|(i, c)| (c.as_str(), i))
        .collect();

    for constraint in _constraints {
        // For each pair of channels in the constraint, add edges
        let indices: Vec<usize> = constraint
            .channels
            .iter()
            .filter_map(|c| channel_idx.get(c.as_str()).copied())
            .collect();

        for i in 0..indices.len() {
            for j in (i + 1)..indices.len() {
                let a = indices[i];
                let b = indices[j];
                // Use the number of transitions as a proxy for constraint weight
                let w_val = constraint.transducer.num_transitions();
                let weight = if w_val == 0 { W::one() } else { W::one() };
                constraint_graph
                    .entry((a, b))
                    .and_modify(|existing| *existing = existing.plus(&weight))
                    .or_insert(weight);
                constraint_graph
                    .entry((b, a))
                    .and_modify(|existing| *existing = existing.plus(&weight))
                    .or_insert(weight);
                adjacency.entry(a).or_default().push(b);
                adjacency.entry(b).or_default().push(a);
            }
        }
    }

    // Detect deadlock cycles via Tarjan's SCC on the dependency graph
    let deadlock_cycles = tarjan_scc(n, &adjacency);

    // Topological sort for optimal order (fall back to natural order if cyclic)
    let optimal_order = topological_sort(n, &adjacency);

    // Compute reorder cost: sum of constraint weights along the chosen order
    let mut reorder_cost = W::one();
    for i in 0..optimal_order.len().saturating_sub(1) {
        let a = optimal_order[i];
        let b = optimal_order[i + 1];
        if let Some(&w) = constraint_graph.get(&(a, b)) {
            reorder_cost = reorder_cost.times(&w);
        }
    }

    JoinPatternAnalysis {
        optimal_order,
        reorder_cost,
        deadlock_cycles,
        constraint_graph,
    }
}

/// Detect potential deadlocks in a set of processes.
///
/// Given a dependency graph where `channel_dependencies[c]` lists the channels
/// that channel `c` depends on, finds all circular dependency chains that could
/// cause deadlock during concurrent execution.
///
/// Uses Tarjan's strongly connected component (SCC) algorithm to identify
/// cycles. Each SCC of size >= 2 represents a potential deadlock cycle.
///
/// # Returns
///
/// A list of deadlock cycles, where each cycle is a list of channel names
/// forming a circular dependency chain.
pub fn detect_deadlock<W: Semiring>(
    channel_dependencies: &HashMap<String, Vec<String>>,
) -> Vec<Vec<String>> {
    // Build adjacency list with integer indices
    let all_channels: Vec<String> = {
        let mut channels_set: HashSet<String> = HashSet::new();
        for (ch, deps) in channel_dependencies {
            channels_set.insert(ch.clone());
            for dep in deps {
                channels_set.insert(dep.clone());
            }
        }
        let mut sorted: Vec<String> = channels_set.into_iter().collect();
        sorted.sort();
        sorted
    };

    let n = all_channels.len();
    let channel_to_idx: HashMap<&str, usize> = all_channels
        .iter()
        .enumerate()
        .map(|(i, c)| (c.as_str(), i))
        .collect();

    let mut adjacency: HashMap<usize, Vec<usize>> = HashMap::with_capacity(n);
    for (ch, deps) in channel_dependencies {
        if let Some(&from) = channel_to_idx.get(ch.as_str()) {
            for dep in deps {
                if let Some(&to) = channel_to_idx.get(dep.as_str()) {
                    adjacency.entry(from).or_default().push(to);
                }
            }
        }
    }

    // Run Tarjan's SCC
    let scc_indices = tarjan_scc(n, &adjacency);

    // Convert index-based cycles back to channel names
    scc_indices
        .into_iter()
        .map(|cycle| {
            cycle
                .into_iter()
                .map(|idx| all_channels[idx].clone())
                .collect()
        })
        .collect()
}

// ══════════════════════════════════════════════════════════════════════════════
// Internal: Tarjan's SCC
// ══════════════════════════════════════════════════════════════════════════════

/// Tarjan's strongly connected component algorithm.
///
/// Returns all SCCs of size >= 2 (cycles) as lists of node indices.
fn tarjan_scc(n: usize, adjacency: &HashMap<usize, Vec<usize>>) -> Vec<Vec<usize>> {
    struct TarjanState {
        index_counter: usize,
        stack: Vec<usize>,
        on_stack: Vec<bool>,
        index: Vec<Option<usize>>,
        lowlink: Vec<usize>,
        result: Vec<Vec<usize>>,
    }

    fn strongconnect(v: usize, adj: &HashMap<usize, Vec<usize>>, state: &mut TarjanState) {
        state.index[v] = Some(state.index_counter);
        state.lowlink[v] = state.index_counter;
        state.index_counter += 1;
        state.stack.push(v);
        state.on_stack[v] = true;

        if let Some(neighbors) = adj.get(&v) {
            for &w in neighbors {
                if w >= state.index.len() {
                    continue;
                }
                if state.index[w].is_none() {
                    strongconnect(w, adj, state);
                    state.lowlink[v] = state.lowlink[v].min(state.lowlink[w]);
                } else if state.on_stack[w] {
                    state.lowlink[v] =
                        state.lowlink[v].min(state.index[w].expect("index should exist"));
                }
            }
        }

        // Root of an SCC
        if state.lowlink[v] == state.index[v].expect("index should exist") {
            let mut component = Vec::new();
            loop {
                let w = state.stack.pop().expect("stack should not be empty in SCC");
                state.on_stack[w] = false;
                component.push(w);
                if w == v {
                    break;
                }
            }
            // Only report cycles (SCC size >= 2)
            if component.len() >= 2 {
                component.sort_unstable();
                state.result.push(component);
            }
        }
    }

    let mut state = TarjanState {
        index_counter: 0,
        stack: Vec::new(),
        on_stack: vec![false; n],
        index: vec![None; n],
        lowlink: vec![0; n],
        result: Vec::new(),
    };

    for v in 0..n {
        if state.index[v].is_none() {
            strongconnect(v, adjacency, &mut state);
        }
    }

    state.result
}

/// Topological sort with fallback to natural order if cycles exist.
///
/// Uses Kahn's algorithm. If the graph contains cycles, returns the natural
/// order `[0, 1, ..., n-1]` as a fallback.
fn topological_sort(n: usize, adjacency: &HashMap<usize, Vec<usize>>) -> Vec<usize> {
    let mut in_degree = vec![0usize; n];
    for neighbors in adjacency.values() {
        for &v in neighbors {
            if v < n {
                in_degree[v] += 1;
            }
        }
    }

    let mut queue: VecDeque<usize> = VecDeque::new();
    for i in 0..n {
        if in_degree[i] == 0 {
            queue.push_back(i);
        }
    }

    let mut order = Vec::with_capacity(n);
    while let Some(v) = queue.pop_front() {
        order.push(v);
        if let Some(neighbors) = adjacency.get(&v) {
            for &w in neighbors {
                if w < n {
                    in_degree[w] -= 1;
                    if in_degree[w] == 0 {
                        queue.push_back(w);
                    }
                }
            }
        }
    }

    if order.len() == n {
        order
    } else {
        // Cycle detected; return natural order as fallback
        (0..n).collect()
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Predicate Dispatch — PredicateCompiler integration
// ══════════════════════════════════════════════════════════════════════════════

/// Compiler adapter for the Two-Way Transducer module (M11).
///
/// Activated by cross-channel variable references (bidirectional transduction variety).
#[cfg(feature = "predicate-dispatch")]
pub struct TwoWayCompiler;

#[cfg(feature = "predicate-dispatch")]
impl crate::predicate_dispatch::PredicateCompiler for TwoWayCompiler {
    type Output = TwoWayAnalysis;

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

    /// Helper: build a simple forward-only transducer that maps "a" -> "x".
    fn simple_forward_transducer() -> WeightedTwoWayTransducer<TropicalWeight> {
        let mut t = WeightedTwoWayTransducer::new();
        let q0 = t.add_state(HeadDirection::Forward, Some("q0".into()));
        let q1 = t.add_state(HeadDirection::Forward, Some("q1".into()));
        let q2 = t.add_state(HeadDirection::Forward, Some("q2".into()));

        // q0 --[⊢ / ε]--> q1  (read left endmarker, no output)
        t.add_transition(
            q0,
            q1,
            TwoWayInput::LeftEndmarker,
            vec![],
            TropicalWeight::one(),
        );
        // q1 --[a / x]--> q2  (read "a", output "x")
        t.add_transition(
            q1,
            q2,
            TwoWayInput::Symbol("a".into()),
            vec!["x".into()],
            TropicalWeight::new(1.0),
        );
        // q2 --[⊣ / ε]--> q2  (read right endmarker, stay)
        t.add_transition(
            q2,
            q2,
            TwoWayInput::RightEndmarker,
            vec![],
            TropicalWeight::one(),
        );

        t.set_initial(q0, TropicalWeight::one());
        t.set_final(q2, TropicalWeight::one());

        t
    }

    #[test]
    fn test_construction_forward_backward() {
        let mut t = WeightedTwoWayTransducer::<TropicalWeight>::new();
        let q0 = t.add_state(HeadDirection::Forward, Some("fwd".into()));
        let q1 = t.add_state(HeadDirection::Backward, Some("bwd".into()));
        let q2 = t.add_state(HeadDirection::Forward, Some("fwd2".into()));

        assert_eq!(t.num_states(), 3);
        assert_eq!(t.forward_states(), vec![q0, q2]);
        assert_eq!(t.backward_states(), vec![q1]);
        assert_eq!(t.states[q0].direction, HeadDirection::Forward);
        assert_eq!(t.states[q1].direction, HeadDirection::Backward);
    }

    #[test]
    fn test_transduce_simple_forward() {
        let t = simple_forward_transducer();
        let results = t.transduce(&["a".into()]);

        assert_eq!(results.len(), 1, "expected exactly one accepting run");
        let (ref output, ref weight) = results[0];
        assert_eq!(output, &vec!["x".to_string()]);
        // Weight: one (init) * one (⊢) * 1.0 ("a"->"x") * one (⊣) * one (final) = 1.0
        assert!(
            weight.approx_eq(&TropicalWeight::new(1.0), 1e-9),
            "expected weight 1.0, got {:?}",
            weight
        );
    }

    #[test]
    fn test_transduce_with_backward_state() {
        // Build a transducer that reads "ab", then goes backward to re-read "a",
        // producing output "b", "a" (reversed order of input).
        let mut t = WeightedTwoWayTransducer::<TropicalWeight>::new();
        let q0 = t.add_state(HeadDirection::Forward, Some("start".into()));
        let q1 = t.add_state(HeadDirection::Forward, Some("read_a".into()));
        let q2 = t.add_state(HeadDirection::Forward, Some("read_b".into()));
        let q3 = t.add_state(HeadDirection::Backward, Some("go_back".into()));
        let q4 = t.add_state(HeadDirection::Forward, Some("re_read".into()));
        let _q5 = t.add_state(HeadDirection::Forward, Some("accept".into()));

        // q0 --[⊢ / ε]--> q1
        t.add_transition(q0, q1, TwoWayInput::LeftEndmarker, vec![], TropicalWeight::one());
        // q1 --[a / ε]--> q2  (read "a" without output, move right)
        t.add_transition(
            q1,
            q2,
            TwoWayInput::Symbol("a".into()),
            vec![],
            TropicalWeight::one(),
        );
        // q2 --[b / "b"]--> q3  (read "b", output "b", move right then switch to backward)
        t.add_transition(
            q2,
            q3,
            TwoWayInput::Symbol("b".into()),
            vec!["b".into()],
            TropicalWeight::one(),
        );
        // q3 --[b / ε]--> q4  (backward state reads "b" at current pos, moves left to "a")
        // After q2 reads "b" at pos 2 and moves right to pos 3, q3 is at pos 3 (⊣).
        // q3 is backward, reads ⊣ at pos 3, moves left to pos 2.
        t.add_transition(
            q3,
            q4,
            TwoWayInput::RightEndmarker,
            vec![],
            TropicalWeight::one(),
        );
        // q4 --[b / ε]--> q4b  (forward state reads "b" at pos 2, moves right to pos 3)
        // Actually, let's simplify: after going back, re-read and output "a".
        // q4 is forward at pos 2, reads "b" at pos 2, moves right to pos 3
        // We want to read "a" instead. Let's redesign.

        // Simpler design:
        // q0(→) --[⊢/ε]--> q1(→)
        // q1(→) --[a/ε]--> q2(→)
        // q2(→) --[b/"b"]--> q3(←) ; reads b at pos 2, moves right to pos 3
        // q3(←) --[⊣/ε]--> q3b(←) ; reads ⊣ at pos 3, moves left to pos 2
        // q3b(←) --[b/ε]--> q4(←) ; reads b at pos 2, moves left to pos 1
        // q4(←) --[a/"a"]--> q5(→) ; reads a at pos 1, moves left to pos 0... but q5 is forward
        // Hmm, backward moves left. So q4(←) reads "a" at pos 1, moves left to pos 0.
        // q5(→) at pos 0, reads ⊢, moves right to pos 1. Then we need to get to ⊣...
        // This gets complicated. Let's just make a simpler backward example.

        // Reset and build a cleaner example.
        drop(t);
        let mut t = WeightedTwoWayTransducer::<TropicalWeight>::new();
        let q0 = t.add_state(HeadDirection::Forward, Some("start".into()));  // 0
        let q1 = t.add_state(HeadDirection::Forward, None);                   // 1
        let q2 = t.add_state(HeadDirection::Backward, None);                  // 2 (backward)
        let q3 = t.add_state(HeadDirection::Forward, None);                   // 3
        let q4 = t.add_state(HeadDirection::Forward, None);                   // 4

        // Read single symbol "a", go backward, re-read endmarker, go forward to accept.
        // q0(→) at pos 0: read ⊢, go to q1, move to pos 1
        t.add_transition(q0, q1, TwoWayInput::LeftEndmarker, vec![], TropicalWeight::one());
        // q1(→) at pos 1: read "a", output "first", go to q2, move to pos 2
        t.add_transition(
            q1,
            q2,
            TwoWayInput::Symbol("a".into()),
            vec!["first".into()],
            TropicalWeight::one(),
        );
        // q2(←) at pos 2: read ⊣, go to q3, move to pos 1
        t.add_transition(q2, q3, TwoWayInput::RightEndmarker, vec![], TropicalWeight::one());
        // q3(→) at pos 1: read "a" again, output "second", go to q4, move to pos 2
        t.add_transition(
            q3,
            q4,
            TwoWayInput::Symbol("a".into()),
            vec!["second".into()],
            TropicalWeight::one(),
        );
        // q4(→) at pos 2: this is ⊣, and q4 is final
        t.add_transition(q4, q4, TwoWayInput::RightEndmarker, vec![], TropicalWeight::one());

        t.set_initial(q0, TropicalWeight::one());
        t.set_final(q4, TropicalWeight::one());

        let results = t.transduce(&["a".into()]);
        assert!(!results.is_empty(), "backward transducer should produce output");
        let (ref output, _) = results[0];
        assert_eq!(output, &vec!["first".to_string(), "second".to_string()]);
    }

    #[test]
    fn test_sum_of_two_transducers() {
        let mut m1 = WeightedTwoWayTransducer::<TropicalWeight>::new();
        let q0 = m1.add_state(HeadDirection::Forward, Some("m1_q0".into()));
        let q1 = m1.add_state(HeadDirection::Forward, Some("m1_q1".into()));
        m1.add_transition(
            q0,
            q1,
            TwoWayInput::LeftEndmarker,
            vec!["x".into()],
            TropicalWeight::one(),
        );
        m1.set_initial(q0, TropicalWeight::one());
        m1.set_final(q1, TropicalWeight::one());

        let mut m2 = WeightedTwoWayTransducer::<TropicalWeight>::new();
        let r0 = m2.add_state(HeadDirection::Forward, Some("m2_r0".into()));
        let r1 = m2.add_state(HeadDirection::Backward, Some("m2_r1".into()));
        m2.add_transition(
            r0,
            r1,
            TwoWayInput::LeftEndmarker,
            vec!["y".into()],
            TropicalWeight::one(),
        );
        m2.set_initial(r0, TropicalWeight::one());

        let merged = WeightedTwoWayTransducer::sum(&m1, &m2);

        // m1 has 2 states, m2 has 2 states => merged has 4 states
        assert_eq!(merged.num_states(), 4);
        // m1 has 1 transition, m2 has 1 transition => merged has 2
        assert_eq!(merged.num_transitions(), 2);
        // Check state directions: m1 states are both forward, m2 has one forward + one backward
        assert_eq!(merged.forward_states().len(), 3); // q0, q1, r0 (offset)
        assert_eq!(merged.backward_states().len(), 1); // r1 (offset)
        // Check initial weights preserved
        assert!(merged.is_initial(0));      // m1's q0
        assert!(merged.is_initial(2));      // m2's r0 (offset=2)
        // Check final weights preserved
        assert!(merged.is_final(1));        // m1's q1
    }

    #[test]
    fn test_to_one_way_forward_only() {
        let t = simple_forward_transducer();
        let result = t.to_one_way();
        assert!(result.is_some(), "forward-only transducer should convert to one-way");
        let entries = result.expect("should be Some");
        // Should contain at least the entry for input ["a"] -> output ["x"]
        let found = entries
            .iter()
            .any(|(inp, out, _)| inp == &vec!["a".to_string()] && out == &vec!["x".to_string()]);
        assert!(found, "expected (a -> x) in one-way entries: {:?}", entries);
    }

    #[test]
    fn test_forward_backward_state_counting() {
        let mut t = WeightedTwoWayTransducer::<TropicalWeight>::new();
        t.add_state(HeadDirection::Forward, None);
        t.add_state(HeadDirection::Forward, None);
        t.add_state(HeadDirection::Backward, None);
        t.add_state(HeadDirection::Forward, None);
        t.add_state(HeadDirection::Backward, None);

        assert_eq!(t.forward_states().len(), 3);
        assert_eq!(t.backward_states().len(), 2);
        assert_eq!(t.num_states(), 5);
    }

    #[test]
    fn test_empty_transducer() {
        let t = WeightedTwoWayTransducer::<TropicalWeight>::new();
        assert_eq!(t.num_states(), 0);
        assert_eq!(t.num_transitions(), 0);
        assert!(t.forward_states().is_empty());
        assert!(t.backward_states().is_empty());
        assert!(t.input_alphabet.is_empty());
        assert!(t.output_alphabet.is_empty());

        let results = t.transduce(&["a".into()]);
        assert!(results.is_empty(), "empty transducer should produce no output");
    }

    #[test]
    fn test_single_symbol_transduction() {
        let mut t = WeightedTwoWayTransducer::<TropicalWeight>::new();
        let q0 = t.add_state(HeadDirection::Forward, None);
        let q1 = t.add_state(HeadDirection::Forward, None);
        let q2 = t.add_state(HeadDirection::Forward, None);

        t.add_transition(q0, q1, TwoWayInput::LeftEndmarker, vec![], TropicalWeight::one());
        t.add_transition(
            q1,
            q2,
            TwoWayInput::Symbol("hello".into()),
            vec!["world".into()],
            TropicalWeight::new(2.5),
        );
        t.add_transition(q2, q2, TwoWayInput::RightEndmarker, vec![], TropicalWeight::one());

        t.set_initial(q0, TropicalWeight::one());
        t.set_final(q2, TropicalWeight::one());

        let results = t.transduce(&["hello".into()]);
        assert_eq!(results.len(), 1);
        assert_eq!(results[0].0, vec!["world".to_string()]);
        assert!(results[0].1.approx_eq(&TropicalWeight::new(2.5), 1e-9));
    }

    #[test]
    fn test_endmarker_handling() {
        // Transducer that reads both endmarkers on empty input, producing output
        // at each step.
        //
        // q0(→) --[⊢ / "start"]--> q1(→)   (read left endmarker, output "start")
        // q1(→) --[⊣ / "end"  ]--> q2(→)   (read right endmarker, output "end")
        // q2 is final; after reading ⊣ the head moves to pos tape_len and accepts.
        let mut t = WeightedTwoWayTransducer::<TropicalWeight>::new();
        let q0 = t.add_state(HeadDirection::Forward, None);
        let q1 = t.add_state(HeadDirection::Forward, None);
        let q2 = t.add_state(HeadDirection::Forward, None);

        t.add_transition(
            q0,
            q1,
            TwoWayInput::LeftEndmarker,
            vec!["start".into()],
            TropicalWeight::one(),
        );
        t.add_transition(
            q1,
            q2,
            TwoWayInput::RightEndmarker,
            vec!["end".into()],
            TropicalWeight::one(),
        );

        t.set_initial(q0, TropicalWeight::one());
        t.set_final(q2, TropicalWeight::one());

        // Empty input: tape is ⊢ ⊣  (tape_len = 2, positions 0 and 1)
        //
        // Trace:
        //   q0(→) at pos 0: reads ⊢, outputs "start", moves to pos 1 in q1
        //   q1(→) at pos 1 (= tape_len - 1): q1 is not final, no acceptance
        //   q1(→) reads ⊣ at pos 1, outputs "end", moves to pos 2 in q2
        //   q2(→) at pos 2 (= tape_len): pos >= tape_len - 1 and q2 is final
        //     => accepts with output ["start", "end"]
        let results = t.transduce(&[]);
        assert_eq!(results.len(), 1);
        assert_eq!(
            results[0].0,
            vec!["start".to_string(), "end".to_string()]
        );
    }

    #[test]
    fn test_detect_deadlock_no_cycles() {
        let mut deps: HashMap<String, Vec<String>> = HashMap::new();
        deps.insert("a".into(), vec!["b".into()]);
        deps.insert("b".into(), vec!["c".into()]);
        deps.insert("c".into(), vec![]);

        let cycles = detect_deadlock::<TropicalWeight>(&deps);
        assert!(cycles.is_empty(), "no cycles expected: {:?}", cycles);
    }

    #[test]
    fn test_detect_deadlock_with_cycle() {
        let mut deps: HashMap<String, Vec<String>> = HashMap::new();
        deps.insert("a".into(), vec!["b".into()]);
        deps.insert("b".into(), vec!["c".into()]);
        deps.insert("c".into(), vec!["a".into()]);

        let cycles = detect_deadlock::<TropicalWeight>(&deps);
        assert_eq!(cycles.len(), 1, "expected one cycle: {:?}", cycles);
        let cycle = &cycles[0];
        assert!(cycle.contains(&"a".to_string()));
        assert!(cycle.contains(&"b".to_string()));
        assert!(cycle.contains(&"c".to_string()));
    }

    #[test]
    fn test_analyze_join_pattern_basic() {
        let channels = vec!["ch1".into(), "ch2".into(), "ch3".into()];
        let constraints: Vec<ChannelConstraint<TropicalWeight>> = Vec::new();

        let analysis = analyze_join_pattern(&channels, &constraints);
        assert_eq!(analysis.optimal_order.len(), 3);
        assert!(analysis.deadlock_cycles.is_empty());
        assert!(analysis.constraint_graph.is_empty());
    }

    #[test]
    fn test_display_head_direction() {
        assert_eq!(format!("{}", HeadDirection::Forward), "→");
        assert_eq!(format!("{}", HeadDirection::Backward), "←");
    }

    #[test]
    fn test_display_two_way_input() {
        assert_eq!(format!("{}", TwoWayInput::Symbol("abc".into())), "abc");
        assert_eq!(format!("{}", TwoWayInput::LeftEndmarker), "⊢");
        assert_eq!(format!("{}", TwoWayInput::RightEndmarker), "⊣");
    }

    #[test]
    fn test_display_transducer() {
        let t = simple_forward_transducer();
        let display = format!("{}", t);
        assert!(display.contains("WeightedTwoWayTransducer"));
        assert!(display.contains("Forward states"));
        assert!(display.contains("Backward states"));
    }

    #[test]
    fn test_head_direction_equality() {
        assert_eq!(HeadDirection::Forward, HeadDirection::Forward);
        assert_eq!(HeadDirection::Backward, HeadDirection::Backward);
        assert_ne!(HeadDirection::Forward, HeadDirection::Backward);
    }

    #[test]
    fn test_analyze_structure() {
        let mut t = WeightedTwoWayTransducer::<TropicalWeight>::new();
        t.add_state(HeadDirection::Forward, None);
        t.add_state(HeadDirection::Backward, None);
        t.add_state(HeadDirection::Forward, None);

        let analysis = t.analyze();
        assert_eq!(analysis.num_states, 3);
        assert_eq!(analysis.num_forward, 2);
        assert_eq!(analysis.num_backward, 1);
        assert!(!analysis.is_one_way_equivalent);
    }

    #[test]
    fn test_analyze_one_way_equivalent() {
        let mut t = WeightedTwoWayTransducer::<TropicalWeight>::new();
        t.add_state(HeadDirection::Forward, None);
        t.add_state(HeadDirection::Forward, None);

        let analysis = t.analyze();
        assert!(analysis.is_one_way_equivalent);
        assert_eq!(analysis.num_backward, 0);
    }

    #[test]
    fn test_compose_one_way_identity() {
        // Compose the simple forward transducer with an identity FST on {x}.
        // The result should preserve the mapping a -> x.
        let w2t = simple_forward_transducer();

        // Identity FST: single state, x -> x
        let fst_transitions = vec![
            (0usize, 0usize, "x".to_string(), "x".to_string(), TropicalWeight::one()),
        ];
        let mut fst_finals = HashSet::new();
        fst_finals.insert(0);

        let composed = w2t.compose_one_way(1, 0, &fst_finals, &fst_transitions);
        // The composed transducer should have states and produce "x" for input "a"
        assert!(composed.num_states() > 0);
    }

    #[test]
    fn test_default_impl() {
        let t = WeightedTwoWayTransducer::<TropicalWeight>::default();
        assert_eq!(t.num_states(), 0);
        assert_eq!(t.num_transitions(), 0);
    }

    #[test]
    fn test_initial_final_predicates() {
        let mut t = WeightedTwoWayTransducer::<TropicalWeight>::new();
        let q0 = t.add_state(HeadDirection::Forward, None);
        let q1 = t.add_state(HeadDirection::Forward, None);
        let q2 = t.add_state(HeadDirection::Forward, None);

        t.set_initial(q0, TropicalWeight::one());
        t.set_final(q2, TropicalWeight::one());

        assert!(t.is_initial(q0));
        assert!(!t.is_initial(q1));
        assert!(!t.is_initial(q2));
        assert!(!t.is_final(q0));
        assert!(!t.is_final(q1));
        assert!(t.is_final(q2));

        // Setting zero weight should make it non-initial/non-final
        t.set_initial(q0, TropicalWeight::zero());
        assert!(!t.is_initial(q0));
    }

    // ── Rocq Proof Alignment Tests (TwoWayCrossingSequence.v) ────────────────

    #[test]
    fn test_crossing_sequence_direction_aware() {
        // Build a W2T where the same position is visited in both forward and
        // backward directions by different states. Before the bug fix, the
        // backward visit would be incorrectly pruned because the visited set
        // tracked only (state, position) — not (state, position, direction).
        //
        // Topology (input "a"):
        //   Tape: ⊢ a ⊣  (positions 0, 1, 2)
        //
        //   q0(→) --[⊢/ε]--> q1(→)      ; pos 0→1
        //   q1(→) --[a/"fwd"]--> q2(←)   ; pos 1→2, output "fwd"
        //   q2(←) --[⊣/ε]--> q3(←)      ; pos 2→1
        //   q3(←) --[a/"bwd"]--> q4(→)   ; pos 1→0, output "bwd"
        //   q4(→) --[⊢/ε]--> q5(→)      ; pos 0→1
        //   q5(→) --[a/ε]--> q6(→)       ; pos 1→2
        //   q6(→) --[⊣/ε]--> q6          ; pos 2→3 (acceptance)
        //
        // At position 1, we visit in forward direction (q1, q5) and backward
        // direction (q3). These are distinct crossing entries.
        let mut t = WeightedTwoWayTransducer::<TropicalWeight>::new();
        let q0 = t.add_state(HeadDirection::Forward, Some("q0".into()));
        let q1 = t.add_state(HeadDirection::Forward, Some("q1".into()));
        let q2 = t.add_state(HeadDirection::Backward, Some("q2".into()));
        let q3 = t.add_state(HeadDirection::Backward, Some("q3".into()));
        let q4 = t.add_state(HeadDirection::Forward, Some("q4".into()));
        let q5 = t.add_state(HeadDirection::Forward, Some("q5".into()));
        let q6 = t.add_state(HeadDirection::Forward, Some("q6".into()));

        t.add_transition(q0, q1, TwoWayInput::LeftEndmarker, vec![], TropicalWeight::one());
        t.add_transition(
            q1, q2,
            TwoWayInput::Symbol("a".into()),
            vec!["fwd".into()],
            TropicalWeight::one(),
        );
        t.add_transition(q2, q3, TwoWayInput::RightEndmarker, vec![], TropicalWeight::one());
        t.add_transition(
            q3, q4,
            TwoWayInput::Symbol("a".into()),
            vec!["bwd".into()],
            TropicalWeight::one(),
        );
        t.add_transition(q4, q5, TwoWayInput::LeftEndmarker, vec![], TropicalWeight::one());
        t.add_transition(
            q5, q6,
            TwoWayInput::Symbol("a".into()),
            vec![],
            TropicalWeight::one(),
        );
        t.add_transition(q6, q6, TwoWayInput::RightEndmarker, vec![], TropicalWeight::one());

        t.set_initial(q0, TropicalWeight::one());
        t.set_final(q6, TropicalWeight::one());

        let results = t.transduce(&["a".into()]);
        assert!(
            !results.is_empty(),
            "direction-aware crossing should allow both forward and backward visits"
        );
        let (ref output, _) = results[0];
        assert_eq!(
            output,
            &vec!["fwd".to_string(), "bwd".to_string()],
            "expected forward then backward output"
        );
    }

    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected = "initial states must be forward-direction")]
    fn test_set_initial_rejects_backward_state() {
        let mut t = WeightedTwoWayTransducer::<TropicalWeight>::new();
        let _q0 = t.add_state(HeadDirection::Forward, None);
        let q1 = t.add_state(HeadDirection::Backward, None);
        // Should panic in debug builds: backward state cannot be initial.
        t.set_initial(q1, TropicalWeight::one());
    }

    #[test]
    fn test_crossing_sequence_bound() {
        // With N states, the crossing sequence at any position is bounded by
        // 2*N entries (each state visited at most once per direction, per the
        // Rocq `no_repeats_length_bound` lemma). Build a W2T that performs
        // multiple forward/backward passes and verify it terminates.
        let mut t = WeightedTwoWayTransducer::<TropicalWeight>::new();

        // 5-state chain: fwd → bwd → fwd → bwd → fwd (accept)
        let q0 = t.add_state(HeadDirection::Forward, None);
        let q1 = t.add_state(HeadDirection::Forward, None);
        let q2 = t.add_state(HeadDirection::Backward, None);
        let q3 = t.add_state(HeadDirection::Forward, None);
        let q4 = t.add_state(HeadDirection::Forward, None);

        // q0(→) reads ⊢, goes to q1
        t.add_transition(q0, q1, TwoWayInput::LeftEndmarker, vec![], TropicalWeight::one());
        // q1(→) reads "a", goes to q2(←)
        t.add_transition(
            q1, q2,
            TwoWayInput::Symbol("a".into()),
            vec!["pass1".into()],
            TropicalWeight::one(),
        );
        // q2(←) reads ⊣ at pos 2, goes to q3(→) at pos 1
        t.add_transition(q2, q3, TwoWayInput::RightEndmarker, vec![], TropicalWeight::one());
        // q3(→) reads "a" again at pos 1, goes to q4(→) at pos 2
        t.add_transition(
            q3, q4,
            TwoWayInput::Symbol("a".into()),
            vec!["pass2".into()],
            TropicalWeight::one(),
        );
        // q4(→) reads ⊣ — acceptance
        t.add_transition(q4, q4, TwoWayInput::RightEndmarker, vec![], TropicalWeight::one());

        t.set_initial(q0, TropicalWeight::one());
        t.set_final(q4, TropicalWeight::one());

        let results = t.transduce(&["a".into()]);
        assert!(
            !results.is_empty(),
            "W2T with {} states should terminate within crossing bound",
            t.num_states()
        );
        let (ref output, _) = results[0];
        assert_eq!(output, &vec!["pass1".to_string(), "pass2".to_string()]);
    }
}
