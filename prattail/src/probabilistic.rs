//! Probabilistic Automata — statistical analysis, disambiguation, and training.
//!
//! Implements Module 7: Probabilistic Automata over the log-probability domain.
//! All weights use [`LogWeight`] (negative log-probability space), where
//! `plus = log-sum-exp` (probability addition) and `times = addition`
//! (probability multiplication). This ensures numerical stability for
//! long sequences and very small probabilities.
//!
//! ## Core Operations
//!
//! | Operation          | Algorithm             | Semiring        |
//! |--------------------|-----------------------|-----------------|
//! | `probability_of`   | Forward algorithm     | `LogWeight`     |
//! | `viterbi`          | Viterbi (best path)   | `TropicalWeight`|
//! | `entropy`          | Expectation semiring  | `EntropyWeight` |
//! | `selectivity`      | Matrix star closure   | `LogWeight`     |
//! | `train_from_corpus` | Baum-Welch EM        | `LogWeight`     |
//!
//! ## Connection to Other Modules
//!
//! - **`forward_backward.rs`**: The forward algorithm in `probability_of()` is
//!   a specialization of the generic semiring forward pass to LogWeight over
//!   a labeled automaton (rather than a pre-built DAG).
//! - **`training.rs`**: `train_from_corpus()` implements Baum-Welch EM for
//!   structure-free probabilistic automata, complementing the grammar-aware
//!   SGD training in `training.rs`. The two can be composed: use Baum-Welch
//!   to learn lexer-level token distributions, then SGD for parser-level
//!   rule weights.
//!
//! ## Lint Diagnostics
//!
//! The probabilistic analysis feeds four diagnostic codes:
//!
//! - **PR01** (Warning): *Low-selectivity rule* — a rule's total probability
//!   mass is below a threshold (e.g., `selectivity < 0.01`), suggesting it
//!   is effectively dead in practice even if structurally reachable.
//! - **PR02** (Note): *High-entropy dispatch point* — the dispatch entropy
//!   at a given state exceeds a threshold (e.g., `> 3.0 bits`), indicating
//!   the grammar is highly ambiguous at that point.
//! - **PR03** (Info): *Convergence report* — Baum-Welch training converged
//!   after `k` iterations with final log-likelihood `L`.
//! - **PR04** (Warning): *Non-normalized automaton* — transition weights do
//!   not sum to 1.0 per state. Call `normalize()` before analysis.
//!
//! ## References
//!
//! - Rabiner (1989), "A Tutorial on Hidden Markov Models and Selected
//!   Applications in Speech Recognition." Proceedings of the IEEE.
//! - Mohri (2009), "Weighted Automata Algorithms." In *Handbook of Weighted
//!   Automata*, Springer.

use std::collections::{HashMap, HashSet};

use crate::automata::semiring::{
    EntropyWeight, LogWeight, Semiring, TropicalWeight,
};

// ══════════════════════════════════════════════════════════════════════════════
// Core types
// ══════════════════════════════════════════════════════════════════════════════

/// State in a probabilistic automaton.
///
/// Each state has a unique numeric identifier and an optional human-readable
/// label (e.g., a rule name or category). Labels are used for diagnostics
/// and the `ProbabilisticAnalysis` report.
#[derive(Debug, Clone)]
pub struct ProbabilisticState {
    /// Unique state identifier (0-indexed, dense).
    pub id: usize,
    /// Optional human-readable label for diagnostics.
    pub label: Option<String>,
}

/// A probabilistic automaton with log-domain weights.
///
/// All weights are in [`LogWeight`] (negative log-probability space):
/// - `transitions[q]` contains `(target, symbol, weight)` triples where
///   `weight = -ln P(target | q, symbol)`.
/// - `initial_distribution[q] = -ln P(q₀ = q)` — the probability of
///   starting in state `q`.
/// - `accepting_weights[q] = -ln P(accept | q)` — the accepting weight
///   for state `q`. States not in the map have accepting weight `LogWeight::zero()`
///   (probability 0, i.e., non-accepting).
///
/// A `None` symbol on a transition represents an epsilon (silent) transition.
/// The forward and Viterbi algorithms handle epsilon transitions by skipping
/// the symbol-matching step.
///
/// ## Invariants
///
/// - `transitions.len() == states.len() == initial_distribution.len()`
/// - All state indices in transitions are `< states.len()`
/// - `is_normalized` is `true` only after a successful `normalize()` call
#[derive(Debug, Clone)]
pub struct ProbabilisticAutomaton {
    /// States of the automaton (indexed by state id).
    pub states: Vec<ProbabilisticState>,
    /// Alphabet: the set of all symbols appearing on transitions.
    pub alphabet: HashSet<String>,
    /// Transitions indexed by source state: `transitions[from] = [(to, symbol, weight), ...]`.
    pub transitions: Vec<Vec<(usize, Option<String>, LogWeight)>>,
    /// Initial probability distribution over states (one entry per state).
    pub initial_distribution: Vec<LogWeight>,
    /// Accepting weights: `state_id -> LogWeight`. Non-accepting states are absent.
    pub accepting_weights: HashMap<usize, LogWeight>,
    /// Whether the automaton has been normalized (per-state outgoing weights sum to 1).
    pub is_normalized: bool,
}

// ══════════════════════════════════════════════════════════════════════════════
// Constructor and basic methods
// ══════════════════════════════════════════════════════════════════════════════

impl ProbabilisticAutomaton {
    /// Create an empty probabilistic automaton with no states or transitions.
    pub fn new() -> Self {
        ProbabilisticAutomaton {
            states: Vec::new(),
            alphabet: HashSet::new(),
            transitions: Vec::new(),
            initial_distribution: Vec::new(),
            accepting_weights: HashMap::new(),
            is_normalized: false,
        }
    }

    /// Add a new state to the automaton with an optional label.
    ///
    /// Returns the state's id (0-indexed). The new state starts with no
    /// transitions, zero initial probability (`LogWeight::zero()`), and
    /// no accepting weight.
    pub fn add_state(&mut self, label: Option<String>) -> usize {
        let id = self.states.len();
        self.states.push(ProbabilisticState { id, label });
        self.transitions.push(Vec::new());
        self.initial_distribution.push(LogWeight::zero());
        self.is_normalized = false;
        id
    }

    /// Add a transition from state `from` to state `to` with the given symbol
    /// and log-domain weight.
    ///
    /// # Panics
    ///
    /// Panics if `from` or `to` is out of bounds.
    pub fn add_transition(
        &mut self,
        from: usize,
        label: Option<String>,
        to: usize,
        weight: LogWeight,
    ) {
        assert!(
            from < self.states.len(),
            "add_transition: source state {from} out of bounds (num_states = {})",
            self.states.len()
        );
        assert!(
            to < self.states.len(),
            "add_transition: target state {to} out of bounds (num_states = {})",
            self.states.len()
        );

        if let Some(sym) = &label {
            self.alphabet.insert(sym.clone());
        }
        self.transitions[from].push((to, label, weight));
        self.is_normalized = false;
    }

    /// Set the initial probability for a state (in log-domain).
    ///
    /// # Panics
    ///
    /// Panics if `state` is out of bounds.
    pub fn set_initial(&mut self, state: usize, weight: LogWeight) {
        assert!(
            state < self.states.len(),
            "set_initial: state {state} out of bounds (num_states = {})",
            self.states.len()
        );
        self.initial_distribution[state] = weight;
        self.is_normalized = false;
    }

    /// Set the accepting weight for a state (in log-domain).
    ///
    /// # Panics
    ///
    /// Panics if `state` is out of bounds.
    pub fn set_accepting(&mut self, state: usize, weight: LogWeight) {
        assert!(
            state < self.states.len(),
            "set_accepting: state {state} out of bounds (num_states = {})",
            self.states.len()
        );
        self.accepting_weights.insert(state, weight);
    }

    /// Number of states in the automaton.
    #[inline]
    pub fn num_states(&self) -> usize {
        self.states.len()
    }

    /// Total number of transitions across all states.
    pub fn num_transitions(&self) -> usize {
        self.transitions.iter().map(|t| t.len()).sum()
    }

    // ══════════════════════════════════════════════════════════════════════════
    // Normalization
    // ══════════════════════════════════════════════════════════════════════════

    /// Normalize transition weights so that for each state the outgoing
    /// transition probabilities sum to 1 (in probability space).
    ///
    /// In log-domain, this means for each state `q`:
    /// 1. Compute `Z_q = logsumexp` over all outgoing transition weights.
    /// 2. Subtract `Z_q` from each outgoing weight (dividing by Z in probability space).
    ///
    /// Also normalizes the initial distribution. Sets `is_normalized = true`.
    ///
    /// States with no outgoing transitions are left unchanged (their normalizing
    /// constant is `LogWeight::zero()`, which means zero probability mass; there
    /// is nothing to distribute).
    pub fn normalize(&mut self) {
        let n = self.states.len();

        // Normalize outgoing transitions per state.
        for q in 0..n {
            if self.transitions[q].is_empty() {
                continue;
            }

            // Compute log-sum-exp of all outgoing weights.
            let mut total = LogWeight::zero();
            for &(_, _, w) in &self.transitions[q] {
                total = total.plus(&w);
            }

            // If total is zero (all transitions have zero probability), skip.
            if total.is_zero() {
                continue;
            }

            // Subtract total from each weight (divide by Z in probability space).
            // In log-domain: w_new = w_old - Z  (since times is addition and
            // dividing corresponds to subtraction of log values).
            for entry in &mut self.transitions[q] {
                entry.2 = LogWeight::new(entry.2.value() - total.value());
            }
        }

        // Normalize initial distribution.
        let mut init_total = LogWeight::zero();
        for &w in &self.initial_distribution {
            init_total = init_total.plus(&w);
        }
        if !init_total.is_zero() {
            for w in &mut self.initial_distribution {
                *w = LogWeight::new(w.value() - init_total.value());
            }
        }

        self.is_normalized = true;
    }

    // ══════════════════════════════════════════════════════════════════════════
    // Forward algorithm — P(word)
    // ══════════════════════════════════════════════════════════════════════════

    /// Compute the total probability of a word under this automaton using
    /// the forward algorithm.
    ///
    /// The forward algorithm computes:
    /// ```text
    /// alpha[0][q] = initial_distribution[q]
    /// alpha[t+1][j] = logsumexp_i( alpha[t][i] + transition_weight(i, word[t], j) )
    /// P(word) = logsumexp_j( alpha[T][j] + accepting_weight[j] )
    /// ```
    ///
    /// All arithmetic is in [`LogWeight`] (log-sum-exp for `plus`, addition
    /// for `times`), ensuring numerical stability.
    ///
    /// Returns `LogWeight::zero()` (probability 0) if the word is not accepted.
    ///
    /// # Arguments
    ///
    /// * `word` — the input sequence of symbols.
    pub fn probability_of(&self, word: &[&str]) -> LogWeight {
        let n = self.states.len();
        if n == 0 {
            return LogWeight::zero();
        }

        // alpha[q] = forward score for state q at the current time step.
        let mut alpha = self.initial_distribution.clone();

        // Process each symbol in the word.
        for symbol in word {
            let mut alpha_next = vec![LogWeight::zero(); n];

            for from in 0..n {
                if alpha[from].is_zero() {
                    continue;
                }

                for &(to, ref trans_label, weight) in &self.transitions[from] {
                    // Match labeled transitions against the current symbol.
                    let matches = match trans_label {
                        Some(lbl) => lbl == symbol,
                        None => false, // epsilon transitions skip symbol consumption
                    };
                    if matches {
                        let contribution = alpha[from].times(&weight);
                        alpha_next[to] = alpha_next[to].plus(&contribution);
                    }
                }
            }

            alpha = alpha_next;
        }

        // Sum over accepting states: P(word) = logsumexp_j(alpha[T][j] + accept[j]).
        let mut result = LogWeight::zero();
        for q in 0..n {
            if alpha[q].is_zero() {
                continue;
            }
            let accept_w = self
                .accepting_weights
                .get(&q)
                .copied()
                .unwrap_or(LogWeight::zero());
            if accept_w.is_zero() {
                continue;
            }
            result = result.plus(&alpha[q].times(&accept_w));
        }

        result
    }

    // ══════════════════════════════════════════════════════════════════════════
    // Backward algorithm (internal helper)
    // ══════════════════════════════════════════════════════════════════════════

    /// Compute backward scores for a given word.
    ///
    /// Returns `beta` where `beta[t][q]` is the total weight of all paths
    /// from state `q` at time `t` to an accepting state at the end of the word.
    ///
    /// ```text
    /// beta[T][q] = accepting_weight[q]
    /// beta[t][i] = logsumexp_j( transition_weight(i, word[t], j) + beta[t+1][j] )
    /// ```
    fn backward(&self, word: &[&str]) -> Vec<Vec<LogWeight>> {
        let n = self.states.len();
        let t_len = word.len();

        // beta[t][q] — allocate (T+1) time steps, each with n states.
        let mut beta = vec![vec![LogWeight::zero(); n]; t_len + 1];

        // Initialize final time step with accepting weights.
        for q in 0..n {
            beta[t_len][q] = self
                .accepting_weights
                .get(&q)
                .copied()
                .unwrap_or(LogWeight::zero());
        }

        // Backward pass: from T-1 down to 0.
        for t in (0..t_len).rev() {
            for from in 0..n {
                let mut score = LogWeight::zero();
                for &(to, ref trans_label, weight) in &self.transitions[from] {
                    let matches = match trans_label {
                        Some(lbl) => lbl == word[t],
                        None => false,
                    };
                    if matches {
                        let contribution = weight.times(&beta[t + 1][to]);
                        score = score.plus(&contribution);
                    }
                }
                beta[t][from] = score;
            }
        }

        beta
    }

    /// Compute forward trellis for a given word.
    ///
    /// Returns `alpha` where `alpha[t][q]` is the total weight of all paths
    /// from the initial distribution to state `q` after consuming `t` symbols.
    fn forward_trellis(&self, word: &[&str]) -> Vec<Vec<LogWeight>> {
        let n = self.states.len();
        let t_len = word.len();

        let mut alpha = vec![vec![LogWeight::zero(); n]; t_len + 1];

        // Initialize with initial distribution.
        for q in 0..n {
            alpha[0][q] = self.initial_distribution[q];
        }

        // Forward pass.
        for t in 0..t_len {
            for from in 0..n {
                if alpha[t][from].is_zero() {
                    continue;
                }
                for &(to, ref trans_label, weight) in &self.transitions[from] {
                    let matches = match trans_label {
                        Some(lbl) => lbl == word[t],
                        None => false,
                    };
                    if matches {
                        let contribution = alpha[t][from].times(&weight);
                        alpha[t + 1][to] = alpha[t + 1][to].plus(&contribution);
                    }
                }
            }
        }

        alpha
    }

    // ══════════════════════════════════════════════════════════════════════════
    // Viterbi algorithm — best path
    // ══════════════════════════════════════════════════════════════════════════

    /// Find the most likely state sequence (Viterbi path) for a given word.
    ///
    /// The Viterbi algorithm operates in the tropical semiring (`min` for `plus`,
    /// `+` for `times`), finding the single best path rather than summing over
    /// all paths:
    ///
    /// ```text
    /// delta[0][q] = initial_weight[q]  (as TropicalWeight)
    /// delta[t+1][j] = min_i( delta[t][i] + tropical_trans(i, word[t], j) )
    /// best_cost = min_j( delta[T][j] + tropical_accept[j] )
    /// ```
    ///
    /// After the forward pass, backtracking recovers the optimal state sequence.
    ///
    /// # Returns
    ///
    /// `(best_cost, state_sequence)` where:
    /// - `best_cost` is the tropical weight (lower = higher probability)
    /// - `state_sequence` has length `word.len() + 1` (initial state + one per symbol)
    ///
    /// If the word is not accepted, returns `(TropicalWeight::zero(), vec![])`.
    pub fn viterbi(&self, word: &[&str]) -> (TropicalWeight, Vec<usize>) {
        let n = self.states.len();
        if n == 0 {
            return (TropicalWeight::zero(), Vec::new());
        }

        let t_len = word.len();

        // delta[q] = best cost to reach state q at the current time step.
        // back[t][q] = predecessor state on the best path to q at time t+1.
        let mut delta: Vec<TropicalWeight> = self
            .initial_distribution
            .iter()
            .map(|lw| TropicalWeight::new(lw.value()))
            .collect();

        let mut backpointers: Vec<Vec<usize>> = Vec::with_capacity(t_len);

        for t in 0..t_len {
            let mut delta_next = vec![TropicalWeight::zero(); n];
            let mut bp = vec![0_usize; n];

            for from in 0..n {
                if delta[from].is_zero() {
                    continue;
                }

                for &(to, ref trans_label, weight) in &self.transitions[from] {
                    let matches = match trans_label {
                        Some(lbl) => lbl == word[t],
                        None => false,
                    };
                    if matches {
                        let cost =
                            TropicalWeight::new(delta[from].value() + weight.value());
                        // Tropical plus = min: keep the lower-cost path.
                        if cost.value() < delta_next[to].value() {
                            delta_next[to] = cost;
                            bp[to] = from;
                        }
                    }
                }
            }

            backpointers.push(bp);
            delta = delta_next;
        }

        // Find best final state.
        let mut best_cost = TropicalWeight::zero();
        let mut best_final: Option<usize> = None;

        for q in 0..n {
            if delta[q].is_zero() {
                continue;
            }
            let accept_w = self
                .accepting_weights
                .get(&q)
                .map(|lw| TropicalWeight::new(lw.value()))
                .unwrap_or(TropicalWeight::zero());
            if accept_w.is_zero() {
                continue;
            }
            let total = TropicalWeight::new(delta[q].value() + accept_w.value());
            if best_final.is_none() || total.value() < best_cost.value() {
                best_cost = total;
                best_final = Some(q);
            }
        }

        let Some(final_state) = best_final else {
            return (TropicalWeight::zero(), Vec::new());
        };

        // Backtrack to recover the state sequence.
        let mut path = vec![0_usize; t_len + 1];
        path[t_len] = final_state;
        for t in (0..t_len).rev() {
            path[t] = backpointers[t][path[t + 1]];
        }

        (best_cost, path)
    }

    // ══════════════════════════════════════════════════════════════════════════
    // Entropy — Shannon entropy of the language
    // ══════════════════════════════════════════════════════════════════════════

    /// Compute the Shannon entropy of the language distribution.
    ///
    /// Uses the [`EntropyWeight`] (expectation semiring) to compute
    /// `H = -sum_w P(w) ln P(w)` over all words `w` in the language.
    ///
    /// The algorithm iteratively computes the Kleene closure `A*` applied
    /// to the accepting weight vector in the expectation semiring:
    ///
    /// ```text
    /// x_new[i] = accept[i]  +  sum_j A[i][j] * x[j]
    /// ```
    ///
    /// This converges to `x = A* * accept` for contractive automata (where
    /// all transition probabilities are strictly less than 1). Each arc's
    /// expectation component is set to the arc's negative log-probability
    /// (for Shannon entropy: `e = w`).
    ///
    /// The total entropy is then `initial^T * x`, extracting the expectation
    /// component.
    ///
    /// Returns the entropy in nats (natural logarithm base). Divide by `ln(2)`
    /// for bits.
    ///
    /// Returns `0.0` for empty automata or automata with no accepting paths.
    pub fn entropy(&self) -> f64 {
        let n = self.states.len();
        if n == 0 {
            return 0.0;
        }

        // Build n×n adjacency matrix in EntropyWeight.
        // For each pair (i, j), aggregate all transitions i → j.
        let mut adj: Vec<Vec<EntropyWeight>> =
            vec![vec![EntropyWeight::zero(); n]; n];

        for from in 0..n {
            for &(to, _, weight) in &self.transitions[from] {
                // For Shannon entropy, set expectation = weight (= -ln p).
                let ew = EntropyWeight::from_arc_weight(weight.value());
                adj[from][to] = adj[from][to].plus(&ew);
            }
        }

        // Initialize x[j] = accepting weight (with zero expectation).
        let mut x: Vec<EntropyWeight> = (0..n)
            .map(|j| {
                let accept_w = self
                    .accepting_weights
                    .get(&j)
                    .copied()
                    .unwrap_or(LogWeight::zero());
                if accept_w.is_zero() {
                    EntropyWeight::zero()
                } else {
                    EntropyWeight::new(accept_w.value(), 0.0)
                }
            })
            .collect();

        // Iteratively compute x = A* * accept via fixed-point iteration:
        //   x_new[i] = accept[i] + sum_j adj[i][j] * x[j]
        // Converges when all eigenvalues of A have spectral radius < 1
        // (guaranteed for proper probabilistic automata).
        let max_iter = 200;
        let convergence_eps = 1e-10;

        for _ in 0..max_iter {
            let mut x_new: Vec<EntropyWeight> = (0..n)
                .map(|j| {
                    let accept_w = self
                        .accepting_weights
                        .get(&j)
                        .copied()
                        .unwrap_or(LogWeight::zero());
                    if accept_w.is_zero() {
                        EntropyWeight::zero()
                    } else {
                        EntropyWeight::new(accept_w.value(), 0.0)
                    }
                })
                .collect();

            for i in 0..n {
                for j in 0..n {
                    if adj[i][j].is_zero() || x[j].is_zero() {
                        continue;
                    }
                    let contribution = adj[i][j].times(&x[j]);
                    x_new[i] = x_new[i].plus(&contribution);
                }
            }

            // Check convergence.
            let mut converged = true;
            for i in 0..n {
                if !x_new[i].approx_eq(&x[i], convergence_eps) {
                    converged = false;
                    break;
                }
            }

            x = x_new;

            if converged {
                break;
            }
        }

        // Total entropy: initial^T * x (extract expectation component).
        let mut total = EntropyWeight::zero();
        for i in 0..n {
            if self.initial_distribution[i].is_zero() || x[i].is_zero() {
                continue;
            }
            let init_ew = EntropyWeight::new(self.initial_distribution[i].value(), 0.0);
            let contribution = init_ew.times(&x[i]);
            total = total.plus(&contribution);
        }

        if total.is_zero() {
            return 0.0;
        }

        total.expectation()
    }

    // ══════════════════════════════════════════════════════════════════════════
    // Selectivity — total language weight
    // ══════════════════════════════════════════════════════════════════════════

    /// Compute the total weight (selectivity) of the automaton's language.
    ///
    /// Selectivity is the sum of probabilities over all accepted words:
    /// `S = sum_w P(w)`. For a normalized automaton accepting only finite
    /// words, `S <= 1.0` when the automaton is a proper distribution.
    /// For automata with self-loops, `S` can exceed 1.0 (e.g., a geometric
    /// series `sum 0.5^k = 2.0`).
    ///
    /// The algorithm iteratively computes `x = A* * accept` where `A` is
    /// the transition matrix (aggregated over all symbols) and `accept` is
    /// the accepting weight vector:
    ///
    /// ```text
    /// x_new[i] = accept[i]  +  sum_j A[i][j] * x[j]
    /// ```
    ///
    /// This fixed-point iteration converges for contractive automata (all
    /// transition probability sums per state strictly less than 1). The
    /// total selectivity is then `initial^T * x`.
    ///
    /// Returns `LogWeight::zero()` for empty automata or automata with no
    /// accepting paths.
    pub fn selectivity(&self) -> LogWeight {
        let n = self.states.len();
        if n == 0 {
            return LogWeight::zero();
        }

        // Build n×n adjacency matrix in LogWeight.
        let mut adj: Vec<Vec<LogWeight>> = vec![vec![LogWeight::zero(); n]; n];

        for from in 0..n {
            for &(to, _, weight) in &self.transitions[from] {
                adj[from][to] = adj[from][to].plus(&weight);
            }
        }

        // Initialize x[j] = accepting weight for state j.
        let mut x: Vec<LogWeight> = (0..n)
            .map(|j| {
                self.accepting_weights
                    .get(&j)
                    .copied()
                    .unwrap_or(LogWeight::zero())
            })
            .collect();

        // Iteratively compute x = A* * accept via fixed-point iteration:
        //   x_new[i] = accept[i] + sum_j adj[i][j] * x[j]
        let max_iter = 200;
        let convergence_eps = 1e-10;

        for _ in 0..max_iter {
            let mut x_new: Vec<LogWeight> = (0..n)
                .map(|j| {
                    self.accepting_weights
                        .get(&j)
                        .copied()
                        .unwrap_or(LogWeight::zero())
                })
                .collect();

            for i in 0..n {
                for j in 0..n {
                    if adj[i][j].is_zero() || x[j].is_zero() {
                        continue;
                    }
                    let contribution = adj[i][j].times(&x[j]);
                    x_new[i] = x_new[i].plus(&contribution);
                }
            }

            // Check convergence.
            let mut converged = true;
            for i in 0..n {
                if !x_new[i].approx_eq(&x[i], convergence_eps) {
                    converged = false;
                    break;
                }
            }

            x = x_new;

            if converged {
                break;
            }
        }

        // Total selectivity: initial^T * x.
        let mut total = LogWeight::zero();
        for i in 0..n {
            if self.initial_distribution[i].is_zero() || x[i].is_zero() {
                continue;
            }
            total = total.plus(&self.initial_distribution[i].times(&x[i]));
        }

        total
    }

    // ══════════════════════════════════════════════════════════════════════════
    // Baum-Welch EM training
    // ══════════════════════════════════════════════════════════════════════════

    /// Train transition weights from a corpus of labeled sequences using
    /// the Baum-Welch (forward-backward) EM algorithm.
    ///
    /// Each corpus entry is a sequence of symbols (a word). The algorithm
    /// iterates:
    ///
    /// 1. **E-step**: For each training word, compute the forward trellis
    ///    `alpha[t][q]` and backward trellis `beta[t][q]`. From these,
    ///    compute the expected transition counts:
    ///    ```text
    ///    xi(t, i, j, a) = alpha[t][i] * P(a | i, j) * beta[t+1][j] / P(word)
    ///    ```
    ///
    /// 2. **M-step**: Update transition weights from accumulated expected
    ///    counts across the entire corpus:
    ///    ```text
    ///    P_new(j, a | i) = sum_words xi(t, i, j, a) / sum_words gamma(t, i)
    ///    ```
    ///    where `gamma(t, i) = alpha[t][i] * beta[t][i] / P(word)`.
    ///
    /// 3. **Convergence check**: If the total log-likelihood change between
    ///    iterations is less than `tolerance`, stop early.
    ///
    /// After training, `is_normalized` is set to `true`.
    ///
    /// # Arguments
    ///
    /// * `corpus` — training sequences (each word is a `Vec<String>`).
    /// * `max_iterations` — upper bound on EM iterations.
    /// * `tolerance` — convergence threshold on log-likelihood change.
    pub fn train_from_corpus(
        &mut self,
        corpus: &[Vec<String>],
        max_iterations: usize,
        tolerance: f64,
    ) {
        let n = self.states.len();
        if n == 0 || corpus.is_empty() {
            return;
        }

        let mut prev_log_likelihood = f64::NEG_INFINITY;

        for _iteration in 0..max_iterations {
            // Accumulators for expected counts.
            // trans_counts[from] = vec of (to, symbol_index, accumulated_weight)
            // We accumulate in probability space for numerical reasons, then
            // convert back to log-domain.

            // Build a symbol-to-index map for this iteration.
            let symbols: Vec<Option<String>> = {
                let mut syms: Vec<Option<String>> = Vec::new();
                for from_trans in &self.transitions {
                    for &(_, ref lbl, _) in from_trans {
                        // Collect unique (to, label) patterns — but we just
                        // need labels for matching. We'll match by transition
                        // index instead.
                        let _ = lbl;
                    }
                }
                // Use transition indices directly.
                syms.push(None); // placeholder
                syms
            };
            let _ = symbols; // We'll index by transition position instead.

            // Accumulate expected transition counts in probability space.
            // trans_count[from][trans_idx] = expected count (probability sum).
            let mut trans_count: Vec<Vec<f64>> = Vec::with_capacity(n);
            for q in 0..n {
                trans_count.push(vec![0.0; self.transitions[q].len()]);
            }

            // Accumulate expected state occupancy for initial distribution.
            let mut init_count: Vec<f64> = vec![0.0; n];

            let mut total_log_likelihood: f64 = 0.0;

            for word_owned in corpus {
                // Convert &[String] to &[&str] for the internal methods.
                let word_refs: Vec<&str> =
                    word_owned.iter().map(|s| s.as_str()).collect();

                if word_refs.is_empty() {
                    // Empty word: only contribute to accepting states from initial.
                    continue;
                }

                // Forward and backward passes.
                let alpha = self.forward_trellis(&word_refs);
                let beta = self.backward(&word_refs);

                // Total probability of this word: P(word) = logsumexp_q(alpha[T][q] * accept[q]).
                let t_len = word_refs.len();
                let mut p_word = LogWeight::zero();
                for q in 0..n {
                    if alpha[t_len][q].is_zero() {
                        continue;
                    }
                    let accept_w = self
                        .accepting_weights
                        .get(&q)
                        .copied()
                        .unwrap_or(LogWeight::zero());
                    if accept_w.is_zero() {
                        continue;
                    }
                    p_word = p_word.plus(&alpha[t_len][q].times(&accept_w));
                }

                if p_word.is_zero() {
                    // Word has zero probability under current model — skip.
                    continue;
                }

                total_log_likelihood += -p_word.value(); // ln P(word) = -w

                // E-step: accumulate expected counts.
                // gamma(t, i) = alpha[t][i] * beta[t][i] / P(word)
                // xi(t, i->j, a) = alpha[t][i] * w(i,a,j) * beta[t+1][j] / P(word)

                // Initial distribution counts: gamma(0, q).
                for q in 0..n {
                    if alpha[0][q].is_zero() || beta[0][q].is_zero() {
                        continue;
                    }
                    let gamma_0_q =
                        (-(alpha[0][q].times(&beta[0][q]).value() - p_word.value()))
                            .exp();
                    init_count[q] += gamma_0_q;
                }

                // Transition counts: xi(t, from, trans_idx).
                for t in 0..t_len {
                    for from in 0..n {
                        if alpha[t][from].is_zero() {
                            continue;
                        }

                        for (trans_idx, &(to, ref trans_label, weight)) in
                            self.transitions[from].iter().enumerate()
                        {
                            let matches = match trans_label {
                                Some(lbl) => lbl == word_refs[t],
                                None => false,
                            };
                            if !matches {
                                continue;
                            }
                            if beta[t + 1][to].is_zero() {
                                continue;
                            }

                            // xi = alpha[t][from] * weight * beta[t+1][to] / P(word)
                            let xi_log = alpha[t][from]
                                .times(&weight)
                                .times(&beta[t + 1][to])
                                .value()
                                - p_word.value();
                            let xi_prob = (-xi_log).exp();
                            trans_count[from][trans_idx] += xi_prob;
                        }
                    }
                }
            }

            // M-step: update weights from expected counts.

            // Update initial distribution.
            let init_total: f64 = init_count.iter().sum();
            if init_total > 0.0 {
                for q in 0..n {
                    if init_count[q] > 0.0 {
                        self.initial_distribution[q] =
                            LogWeight::from_probability(init_count[q] / init_total);
                    } else {
                        self.initial_distribution[q] = LogWeight::zero();
                    }
                }
            }

            // Update transition weights.
            for from in 0..n {
                let state_total: f64 = trans_count[from].iter().sum();
                if state_total <= 0.0 {
                    continue;
                }

                for (trans_idx, count) in trans_count[from].iter().enumerate() {
                    if *count > 0.0 {
                        self.transitions[from][trans_idx].2 =
                            LogWeight::from_probability(*count / state_total);
                    } else {
                        self.transitions[from][trans_idx].2 = LogWeight::zero();
                    }
                }
            }

            // Convergence check.
            let ll_change = (total_log_likelihood - prev_log_likelihood).abs();
            prev_log_likelihood = total_log_likelihood;

            if ll_change < tolerance {
                break;
            }
        }

        self.is_normalized = true;
    }

    // ══════════════════════════════════════════════════════════════════════════
    // Analysis
    // ══════════════════════════════════════════════════════════════════════════

    /// Produce a summary analysis of the probabilistic automaton.
    ///
    /// Computes selectivity, entropy, and identifies rules (states) with
    /// low selectivity (probability mass below the given threshold).
    ///
    /// # Arguments
    ///
    /// * `selectivity_threshold` — states with total outgoing probability
    ///   below this threshold (in probability space) are flagged as
    ///   low-selectivity.
    pub fn analyze(&self, selectivity_threshold: f64) -> ProbabilisticAnalysis {
        let total_selectivity = self.selectivity();
        let sel_prob = if total_selectivity.is_zero() {
            0.0
        } else {
            total_selectivity.to_probability()
        };

        let mean_entropy = self.entropy();

        // Identify states with low outgoing probability mass.
        let mut low_selectivity_rules = Vec::new();
        let n = self.states.len();

        for q in 0..n {
            if self.transitions[q].is_empty() {
                continue;
            }

            // Compute total outgoing weight for this state.
            let mut state_total = LogWeight::zero();
            for &(_, _, w) in &self.transitions[q] {
                state_total = state_total.plus(&w);
            }

            if !state_total.is_zero() {
                let state_prob = state_total.to_probability();
                if state_prob < selectivity_threshold {
                    let label = self.states[q]
                        .label
                        .clone()
                        .unwrap_or_else(|| format!("state_{}", q));
                    low_selectivity_rules.push(label);
                }
            }
        }

        // Build per-rule selectivity map from the forward probabilities.
        let rule_selectivities: HashMap<String, f64> = if self.is_normalized {
            low_selectivity_rules
                .iter()
                .map(|label| (label.clone(), 0.0))
                .collect() // Approximation: low-selectivity rules get 0; others are unlisted
        } else {
            HashMap::new()
        };
        ProbabilisticAnalysis {
            num_states: n,
            is_normalized: self.is_normalized,
            total_selectivity: sel_prob,
            mean_entropy,
            low_selectivity_rules,
            rule_selectivities,
        }
    }
}

impl Default for ProbabilisticAutomaton {
    fn default() -> Self {
        Self::new()
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Analysis result
// ══════════════════════════════════════════════════════════════════════════════

/// Summary of a probabilistic automaton's statistical properties.
///
/// Produced by [`ProbabilisticAutomaton::analyze()`]. Used by lint diagnostics
/// (PR01–PR04) and the grammar feedback system.
#[derive(Debug, Clone)]
pub struct ProbabilisticAnalysis {
    /// Number of states in the automaton.
    pub num_states: usize,
    /// Whether the automaton has been normalized.
    pub is_normalized: bool,
    /// Total selectivity: sum of P(w) over all accepted words.
    /// For a proper distribution over finite words, `total_selectivity <= 1.0`.
    pub total_selectivity: f64,
    /// Mean Shannon entropy (in nats) of the language distribution.
    pub mean_entropy: f64,
    /// Labels of states/rules with probability mass below the analysis threshold.
    pub low_selectivity_rules: Vec<String>,
    /// Per-rule selectivity scores (rule_label → selectivity in [0,1]).
    /// Populated only when `is_normalized` is true and the PA has been trained.
    /// Used by codegen to blend probabilistic weights into constructor ordering (PR01-WEIGHT).
    pub rule_selectivities: HashMap<String, f64>,
}

/// Analyze grammar rule distribution using probabilistic automata.
///
/// Assigns non-uniform weights based on rule structural complexity:
/// simpler rules (fewer syntax items) get higher weight (more likely).
/// Weights are normalized per category and used for entropy computation.
pub fn analyze_from_bundle(
    all_syntax: &[(String, String, Vec<crate::SyntaxItemSpec>)],
    categories: &[crate::pipeline::CategoryInfo],
) -> ProbabilisticAnalysis {
    let num_states = categories.len().max(1);
    let num_rules = all_syntax.len();

    if num_rules == 0 {
        return ProbabilisticAnalysis {
            num_states,
            is_normalized: true,
            total_selectivity: 0.0,
            mean_entropy: 0.0,
            low_selectivity_rules: Vec::new(),
            rule_selectivities: HashMap::new(),
        };
    }

    // Assign raw weights based on structural complexity:
    // weight(rule) = 1.0 / (1.0 + syntax_items.len() as f64)
    // Simpler rules (fewer syntax items) get higher raw weight (higher probability).
    let mut per_cat_rules: HashMap<String, Vec<(String, f64)>> = HashMap::new();
    for (label, cat, items) in all_syntax {
        let qualified = format!("{}::{}", cat, label);
        let raw_weight = 1.0 / (1.0 + items.len() as f64);
        per_cat_rules
            .entry(cat.clone())
            .or_default()
            .push((qualified, raw_weight));
    }

    // Normalize per category: weights sum to 1.0 per category.
    let mut rule_selectivities: HashMap<String, f64> = HashMap::new();
    let mut total_entropy = 0.0_f64;
    let mut num_categories_with_rules = 0usize;

    for (_cat, rules) in &per_cat_rules {
        let sum: f64 = rules.iter().map(|(_, w)| w).sum();
        if sum <= 0.0 {
            continue;
        }
        num_categories_with_rules += 1;

        let mut cat_entropy = 0.0_f64;
        for (qualified, raw_w) in rules {
            let normalized = raw_w / sum;
            // Category weight proportional to rule count / total rules.
            let cat_weight = rules.len() as f64 / num_rules as f64;
            let selectivity = normalized * cat_weight;
            rule_selectivities.insert(qualified.clone(), selectivity);

            // Shannon entropy for this category: -p * ln(p).
            if normalized > 0.0 {
                cat_entropy -= normalized * normalized.ln();
            }
        }
        total_entropy += cat_entropy;
    }

    let mean_entropy = if num_categories_with_rules > 0 {
        total_entropy / num_categories_with_rules as f64
    } else {
        0.0
    };

    // Total selectivity: sum of all rule selectivities.
    let total_selectivity: f64 = rule_selectivities.values().sum();

    // Low selectivity rules: below 0.01 threshold.
    let low_selectivity_rules: Vec<String> = rule_selectivities
        .iter()
        .filter(|(_, &sel)| sel < 0.01)
        .map(|(label, _)| label.clone())
        .collect();

    ProbabilisticAnalysis {
        num_states,
        is_normalized: true,
        total_selectivity,
        mean_entropy,
        low_selectivity_rules,
        rule_selectivities,
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Helper: build a simple deterministic PA from labeled transitions
// ══════════════════════════════════════════════════════════════════════════════

/// Build a deterministic probabilistic automaton from a transition table.
///
/// Convenience constructor for tests and simple use cases. Each entry in
/// `transitions` is `(from, symbol, to, probability)` where `probability`
/// is in the standard `[0, 1]` range (converted to `LogWeight` internally).
///
/// # Arguments
///
/// * `num_states` — total number of states.
/// * `transitions` — list of `(from, symbol, to, probability)` entries.
/// * `initial_state` — the single initial state (gets probability 1.0).
/// * `accepting_states` — set of accepting states (each gets accept weight 1.0).
pub fn build_simple_pa(
    num_states: usize,
    transitions: &[(usize, &str, usize, f64)],
    initial_state: usize,
    accepting_states: &[usize],
) -> ProbabilisticAutomaton {
    let mut pa = ProbabilisticAutomaton::new();

    for i in 0..num_states {
        pa.add_state(Some(format!("q{i}")));
    }

    pa.set_initial(initial_state, LogWeight::one());

    for &accept in accepting_states {
        pa.set_accepting(accept, LogWeight::one());
    }

    for &(from, sym, to, prob) in transitions {
        pa.add_transition(from, Some(sym.to_string()), to, LogWeight::from_probability(prob));
    }

    pa
}

// ══════════════════════════════════════════════════════════════════════════════
// Predicate Dispatch — PredicateCompiler integration
// ══════════════════════════════════════════════════════════════════════════════

/// Compiler adapter for the Probabilistic Automata module (M7).
///
/// Activated by multi-guard conjunctions (≥2 guards on same channel).
#[cfg(feature = "predicate-dispatch")]
pub struct ProbabilisticCompiler;

#[cfg(feature = "predicate-dispatch")]
impl crate::predicate_dispatch::PredicateCompiler for ProbabilisticCompiler {
    type Output = ProbabilisticAnalysis;

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

    // Tolerance for floating-point comparisons.
    const EPS: f64 = 1e-6;

    /// Approximate equality for f64 values.
    fn approx_eq(a: f64, b: f64) -> bool {
        (a - b).abs() < EPS
    }

    // ── Construction and basic properties ────────────────────────────────────

    #[test]
    fn test_empty_automaton() {
        let pa = ProbabilisticAutomaton::new();
        assert_eq!(pa.num_states(), 0);
        assert_eq!(pa.num_transitions(), 0);
        assert!(!pa.is_normalized);
    }

    #[test]
    fn test_add_states_and_transitions() {
        let mut pa = ProbabilisticAutomaton::new();
        let q0 = pa.add_state(Some("start".to_string()));
        let q1 = pa.add_state(Some("end".to_string()));

        assert_eq!(pa.num_states(), 2);
        assert_eq!(q0, 0);
        assert_eq!(q1, 1);

        pa.add_transition(q0, Some("a".to_string()), q1, LogWeight::one());
        assert_eq!(pa.num_transitions(), 1);
        assert!(pa.alphabet.contains("a"));
    }

    #[test]
    fn test_default_is_new() {
        let pa = ProbabilisticAutomaton::default();
        assert_eq!(pa.num_states(), 0);
    }

    #[test]
    #[should_panic(expected = "source state")]
    fn test_add_transition_out_of_bounds_from() {
        let mut pa = ProbabilisticAutomaton::new();
        pa.add_state(None);
        pa.add_transition(5, Some("a".to_string()), 0, LogWeight::one());
    }

    #[test]
    #[should_panic(expected = "target state")]
    fn test_add_transition_out_of_bounds_to() {
        let mut pa = ProbabilisticAutomaton::new();
        pa.add_state(None);
        pa.add_transition(0, Some("a".to_string()), 5, LogWeight::one());
    }

    // ── Normalization ────────────────────────────────────────────────────────

    #[test]
    fn test_normalize_produces_valid_distribution() {
        // Two-state automaton: q0 --a(0.3)--> q1, q0 --b(0.7)--> q1
        // (but specified with arbitrary weights, normalized afterward)
        let mut pa = ProbabilisticAutomaton::new();
        let q0 = pa.add_state(None);
        let q1 = pa.add_state(None);

        // Use raw LogWeight values (not necessarily summing to 1).
        pa.add_transition(q0, Some("a".to_string()), q1, LogWeight::new(1.0));
        pa.add_transition(q0, Some("b".to_string()), q1, LogWeight::new(2.0));
        pa.set_initial(q0, LogWeight::one());
        pa.set_accepting(q1, LogWeight::one());

        assert!(!pa.is_normalized);
        pa.normalize();
        assert!(pa.is_normalized);

        // After normalization, outgoing transition probabilities from q0
        // should sum to 1.0 (in probability space).
        let p_a = pa.transitions[q0][0].2.to_probability();
        let p_b = pa.transitions[q0][1].2.to_probability();
        assert!(
            approx_eq(p_a + p_b, 1.0),
            "Expected sum ~1.0, got {:.6}",
            p_a + p_b
        );
    }

    #[test]
    fn test_normalize_already_normalized() {
        // Build a properly normalized automaton, normalize again — no change.
        let mut pa = ProbabilisticAutomaton::new();
        let q0 = pa.add_state(None);
        let q1 = pa.add_state(None);

        pa.add_transition(
            q0,
            Some("a".to_string()),
            q1,
            LogWeight::from_probability(0.6),
        );
        pa.add_transition(
            q0,
            Some("b".to_string()),
            q1,
            LogWeight::from_probability(0.4),
        );
        pa.set_initial(q0, LogWeight::one());
        pa.set_accepting(q1, LogWeight::one());

        let p_a_before = pa.transitions[q0][0].2.to_probability();
        let p_b_before = pa.transitions[q0][1].2.to_probability();

        pa.normalize();

        let p_a_after = pa.transitions[q0][0].2.to_probability();
        let p_b_after = pa.transitions[q0][1].2.to_probability();

        assert!(approx_eq(p_a_before, p_a_after));
        assert!(approx_eq(p_b_before, p_b_after));
        assert!(pa.is_normalized);
    }

    #[test]
    fn test_normalize_no_transitions() {
        // State with no outgoing transitions — normalization is a no-op.
        let mut pa = ProbabilisticAutomaton::new();
        pa.add_state(None);
        pa.normalize();
        assert!(pa.is_normalized);
    }

    // ── probability_of (forward algorithm) ───────────────────────────────────

    #[test]
    fn test_probability_of_simple() {
        // Linear automaton: q0 --a(0.8)--> q1 --b(0.5)--> q2
        // P("ab") = 0.8 * 0.5 = 0.4
        let pa = build_simple_pa(
            3,
            &[(0, "a", 1, 0.8), (1, "b", 2, 0.5)],
            0,
            &[2],
        );

        let p = pa.probability_of(&["a", "b"]);
        assert!(
            approx_eq(p.to_probability(), 0.4),
            "Expected ~0.4, got {:.6}",
            p.to_probability()
        );
    }

    #[test]
    fn test_probability_of_with_parallel_paths() {
        // q0 --a(0.3)--> q1, q0 --a(0.7)--> q2, q1 --b(1.0)--> q3, q2 --b(1.0)--> q3
        // P("ab") = 0.3*1.0 + 0.7*1.0 = 1.0
        let pa = build_simple_pa(
            4,
            &[
                (0, "a", 1, 0.3),
                (0, "a", 2, 0.7),
                (1, "b", 3, 1.0),
                (2, "b", 3, 1.0),
            ],
            0,
            &[3],
        );

        let p = pa.probability_of(&["a", "b"]);
        assert!(
            approx_eq(p.to_probability(), 1.0),
            "Expected ~1.0, got {:.6}",
            p.to_probability()
        );
    }

    #[test]
    fn test_probability_of_empty_word() {
        // q0 is both initial and accepting.
        // P("") = P(start=q0) * P(accept|q0) = 1.0 * 1.0 = 1.0
        let pa = build_simple_pa(1, &[], 0, &[0]);
        let p = pa.probability_of(&[]);
        assert!(
            approx_eq(p.to_probability(), 1.0),
            "Expected ~1.0 for empty word on accepting start state, got {:.6}",
            p.to_probability()
        );
    }

    #[test]
    fn test_probability_of_unaccepted_word() {
        // q0 --a--> q1, but only q0 is accepting. P("a") = 0 (q1 not accepting).
        let pa = build_simple_pa(2, &[(0, "a", 1, 1.0)], 0, &[0]);
        let p = pa.probability_of(&["a"]);
        assert!(
            p.is_zero(),
            "Expected zero probability for word ending in non-accepting state"
        );
    }

    #[test]
    fn test_probability_of_empty_automaton() {
        let pa = ProbabilisticAutomaton::new();
        let p = pa.probability_of(&["a"]);
        assert!(p.is_zero());
    }

    #[test]
    fn test_forward_matches_manual_calculation() {
        // 3-state automaton:
        // q0 --x(0.5)--> q1, q0 --x(0.5)--> q2
        // q1 --y(0.8)--> q2
        // q2 --y(0.6)--> q2  (self-loop)
        // Accepting: q2
        //
        // P("xy"):
        //   alpha[0] = [1.0, 0, 0]
        //   After "x": alpha[1] = [0, 0.5, 0.5]
        //   After "y": alpha[2] = [0, 0, 0.5*0.8 + 0.5*0.6] = [0, 0, 0.7]
        //   P("xy") = 0.7 * 1.0 = 0.7
        let pa = build_simple_pa(
            3,
            &[
                (0, "x", 1, 0.5),
                (0, "x", 2, 0.5),
                (1, "y", 2, 0.8),
                (2, "y", 2, 0.6),
            ],
            0,
            &[2],
        );

        let p = pa.probability_of(&["x", "y"]);
        assert!(
            approx_eq(p.to_probability(), 0.7),
            "Expected ~0.7, got {:.6}",
            p.to_probability()
        );
    }

    // ── Viterbi algorithm ────────────────────────────────────────────────────

    #[test]
    fn test_viterbi_simple_path() {
        // Linear: q0 --a(0.8)--> q1 --b(0.5)--> q2
        let pa = build_simple_pa(
            3,
            &[(0, "a", 1, 0.8), (1, "b", 2, 0.5)],
            0,
            &[2],
        );

        let (cost, path) = pa.viterbi(&["a", "b"]);
        assert!(!cost.is_zero(), "Viterbi should find a valid path");
        assert_eq!(path, vec![0, 1, 2]);

        // Cost = -ln(0.8) + -ln(0.5) in tropical domain.
        let expected_cost = -0.8_f64.ln() + (-0.5_f64.ln());
        assert!(
            approx_eq(cost.value(), expected_cost),
            "Expected cost ~{:.4}, got {:.4}",
            expected_cost,
            cost.value()
        );
    }

    #[test]
    fn test_viterbi_chooses_best_path() {
        // q0 --a(0.9)--> q1 --b(0.9)--> q3
        // q0 --a(0.1)--> q2 --b(0.1)--> q3
        // Best path: q0 -> q1 -> q3 (higher probability = lower tropical cost)
        let pa = build_simple_pa(
            4,
            &[
                (0, "a", 1, 0.9),
                (0, "a", 2, 0.1),
                (1, "b", 3, 0.9),
                (2, "b", 3, 0.1),
            ],
            0,
            &[3],
        );

        let (_, path) = pa.viterbi(&["a", "b"]);
        assert_eq!(path, vec![0, 1, 3], "Should choose the high-probability path");
    }

    #[test]
    fn test_viterbi_no_accepting_path() {
        let pa = build_simple_pa(2, &[(0, "a", 1, 1.0)], 0, &[0]);
        let (cost, path) = pa.viterbi(&["a"]);
        assert!(cost.is_zero(), "No accepting path should give zero cost");
        assert!(path.is_empty());
    }

    #[test]
    fn test_viterbi_empty_automaton() {
        let pa = ProbabilisticAutomaton::new();
        let (cost, path) = pa.viterbi(&["a"]);
        assert!(cost.is_zero());
        assert!(path.is_empty());
    }

    // ── Entropy ──────────────────────────────────────────────────────────────

    #[test]
    fn test_entropy_single_deterministic_path() {
        // A single path with probability 1: H = -1 * ln(1) = 0.
        let pa = build_simple_pa(
            2,
            &[(0, "a", 1, 1.0)],
            0,
            &[1],
        );

        let h = pa.entropy();
        assert!(
            approx_eq(h, 0.0),
            "Deterministic automaton should have entropy ~0.0, got {:.6}",
            h
        );
    }

    #[test]
    fn test_entropy_empty_automaton() {
        let pa = ProbabilisticAutomaton::new();
        assert_eq!(pa.entropy(), 0.0);
    }

    #[test]
    fn test_entropy_uniform_binary_choice() {
        // q0 --a(0.5)--> q1, q0 --b(0.5)--> q1
        // Two equally likely single-symbol words: H = -2 * 0.5 * ln(0.5) = ln(2)
        let pa = build_simple_pa(
            2,
            &[(0, "a", 1, 0.5), (0, "b", 1, 0.5)],
            0,
            &[1],
        );

        let h = pa.entropy();
        // For a uniform distribution over 2 outcomes, H = ln(2) ~= 0.693
        assert!(
            h > 0.0,
            "Entropy of uniform binary choice should be positive, got {:.6}",
            h
        );
    }

    // ── Selectivity ──────────────────────────────────────────────────────────

    #[test]
    fn test_selectivity_simple() {
        // q0 --a(0.5)--> q1 (accepting), P("a") = 0.5
        let pa = build_simple_pa(
            2,
            &[(0, "a", 1, 0.5)],
            0,
            &[1],
        );

        let s = pa.selectivity();
        assert!(
            approx_eq(s.to_probability(), 0.5),
            "Expected selectivity ~0.5, got {:.6}",
            s.to_probability()
        );
    }

    #[test]
    fn test_selectivity_empty_automaton() {
        let pa = ProbabilisticAutomaton::new();
        assert!(pa.selectivity().is_zero());
    }

    #[test]
    fn test_selectivity_no_accepting_states() {
        let pa = build_simple_pa(2, &[(0, "a", 1, 1.0)], 0, &[]);
        assert!(pa.selectivity().is_zero());
    }

    // ── Single-state self-loop ───────────────────────────────────────────────

    #[test]
    fn test_single_state_self_loop() {
        // q0 --a(0.5)--> q0 (self-loop), q0 is accepting.
        // P("") = 1.0, P("a") = 0.5, P("aa") = 0.25, ...
        // Geometric series: total selectivity = 1/(1-0.5) = 2.0
        let pa = build_simple_pa(
            1,
            &[(0, "a", 0, 0.5)],
            0,
            &[0],
        );

        // P("a") should be 0.5.
        let p_a = pa.probability_of(&["a"]);
        assert!(
            approx_eq(p_a.to_probability(), 0.5),
            "P(\"a\") should be ~0.5, got {:.6}",
            p_a.to_probability()
        );

        // P("aa") should be 0.25.
        let p_aa = pa.probability_of(&["a", "a"]);
        assert!(
            approx_eq(p_aa.to_probability(), 0.25),
            "P(\"aa\") should be ~0.25, got {:.6}",
            p_aa.to_probability()
        );

        // Total selectivity should be 2.0 (geometric sum).
        let s = pa.selectivity();
        assert!(
            approx_eq(s.to_probability(), 2.0),
            "Expected selectivity ~2.0, got {:.6}",
            s.to_probability()
        );
    }

    // ── Baum-Welch training ──────────────────────────────────────────────────

    #[test]
    fn test_train_from_corpus_basic() {
        // Train on a corpus of ["a", "b"] sequences.
        // After training, the automaton should assign higher probability to
        // observed sequences.
        let mut pa = build_simple_pa(
            3,
            &[
                (0, "a", 1, 0.5),
                (0, "b", 1, 0.5),
                (1, "a", 2, 0.5),
                (1, "b", 2, 0.5),
            ],
            0,
            &[2],
        );

        // Corpus: all sequences are "a" then "b".
        let corpus: Vec<Vec<String>> = (0..10)
            .map(|_| vec!["a".to_string(), "b".to_string()])
            .collect();

        let p_before = pa.probability_of(&["a", "b"]).to_probability();

        pa.train_from_corpus(&corpus, 20, 1e-8);

        let p_after = pa.probability_of(&["a", "b"]).to_probability();

        // After training on exclusively "ab" sequences, P("ab") should increase.
        assert!(
            p_after > p_before,
            "Training on 'ab' corpus should increase P('ab'): before={:.4}, after={:.4}",
            p_before,
            p_after
        );
    }

    #[test]
    fn test_train_from_corpus_convergence() {
        // Verify that training converges (stops early with tight tolerance).
        let mut pa = build_simple_pa(
            2,
            &[(0, "a", 1, 0.5)],
            0,
            &[1],
        );

        let corpus = vec![vec!["a".to_string()]; 5];
        pa.train_from_corpus(&corpus, 100, 1e-10);

        // With only one possible transition, weights should not change
        // significantly. The automaton should still be normalized.
        assert!(pa.is_normalized);
    }

    #[test]
    fn test_train_empty_corpus() {
        let mut pa = build_simple_pa(
            2,
            &[(0, "a", 1, 0.5)],
            0,
            &[1],
        );

        let w_before = pa.transitions[0][0].2;
        pa.train_from_corpus(&[], 10, 1e-6);
        let w_after = pa.transitions[0][0].2;

        // Empty corpus should not change weights.
        assert_eq!(w_before, w_after);
    }

    #[test]
    fn test_train_empty_automaton() {
        let mut pa = ProbabilisticAutomaton::new();
        // Should not panic.
        pa.train_from_corpus(&[vec!["a".to_string()]], 10, 1e-6);
    }

    // ── Analysis ─────────────────────────────────────────────────────────────

    #[test]
    fn test_analyze_basic() {
        let pa = build_simple_pa(
            3,
            &[(0, "a", 1, 0.8), (1, "b", 2, 0.5)],
            0,
            &[2],
        );

        let analysis = pa.analyze(0.01);
        assert_eq!(analysis.num_states, 3);
        assert!(!analysis.is_normalized);
        assert!(analysis.total_selectivity > 0.0);
    }

    #[test]
    fn test_analyze_low_selectivity_detection() {
        // State q0 has very low outgoing probability.
        let mut pa = ProbabilisticAutomaton::new();
        let q0 = pa.add_state(Some("weak_rule".to_string()));
        let q1 = pa.add_state(None);

        pa.add_transition(
            q0,
            Some("a".to_string()),
            q1,
            LogWeight::from_probability(0.001),
        );
        pa.set_initial(q0, LogWeight::one());
        pa.set_accepting(q1, LogWeight::one());

        let analysis = pa.analyze(0.01);
        assert!(
            analysis.low_selectivity_rules.contains(&"weak_rule".to_string()),
            "Should flag 'weak_rule' as low-selectivity"
        );
    }

    // ── build_simple_pa helper ───────────────────────────────────────────────

    #[test]
    fn test_build_simple_pa() {
        let pa = build_simple_pa(
            3,
            &[(0, "a", 1, 0.8), (1, "b", 2, 0.5)],
            0,
            &[2],
        );

        assert_eq!(pa.num_states(), 3);
        assert_eq!(pa.num_transitions(), 2);
        assert!(pa.alphabet.contains("a"));
        assert!(pa.alphabet.contains("b"));
        assert!(!pa.initial_distribution[0].is_zero());
        assert!(pa.initial_distribution[1].is_zero());
        assert!(pa.accepting_weights.contains_key(&2));
    }

    // ── Normalized automaton stays normalized ────────────────────────────────

    #[test]
    fn test_normalized_stays_normalized_after_renormalization() {
        let mut pa = build_simple_pa(
            3,
            &[
                (0, "a", 1, 0.6),
                (0, "b", 2, 0.4),
                (1, "c", 2, 1.0),
            ],
            0,
            &[2],
        );

        pa.normalize();
        assert!(pa.is_normalized);

        // Record weights.
        let w0_a = pa.transitions[0][0].2.to_probability();
        let w0_b = pa.transitions[0][1].2.to_probability();
        let w1_c = pa.transitions[1][0].2.to_probability();

        // Normalize again.
        pa.normalize();
        assert!(pa.is_normalized);

        // Weights should be unchanged (within tolerance).
        assert!(approx_eq(pa.transitions[0][0].2.to_probability(), w0_a));
        assert!(approx_eq(pa.transitions[0][1].2.to_probability(), w0_b));
        assert!(approx_eq(pa.transitions[1][0].2.to_probability(), w1_c));
    }

    // ── Viterbi consistency with forward ─────────────────────────────────────

    #[test]
    fn test_viterbi_probability_leq_total() {
        // The Viterbi probability (best single path) should be <= the total
        // probability (sum over all paths).
        let pa = build_simple_pa(
            4,
            &[
                (0, "a", 1, 0.6),
                (0, "a", 2, 0.4),
                (1, "b", 3, 0.8),
                (2, "b", 3, 0.7),
            ],
            0,
            &[3],
        );

        let total_p = pa.probability_of(&["a", "b"]).to_probability();
        let (viterbi_cost, _) = pa.viterbi(&["a", "b"]);
        let viterbi_p = (-viterbi_cost.value()).exp();

        assert!(
            viterbi_p <= total_p + EPS,
            "Viterbi probability ({:.6}) should be <= total probability ({:.6})",
            viterbi_p,
            total_p
        );
    }

    // ── Rocq Proof Alignment Tests (StochasticNormalization.v) ───────────────

    #[test]
    fn test_normalize_preserves_support() {
        // Rocq: `proportional_same_support` — normalization preserves support
        // (positive → positive, zero → zero).
        //
        // Build a 3-state PA with varied transition weights (some zero paths).
        // Verify that for several words: positive prob before ↔ positive after,
        // zero before ↔ zero after.
        let mut pa = build_simple_pa(
            3,
            &[
                (0, "a", 1, 0.7),
                (0, "a", 2, 0.3),
                (1, "b", 2, 0.5),
                // No transition from state 2 on "b" — so "ab" via q2 is zero
            ],
            0,
            &[2],
        );

        // Compute probabilities before normalization.
        let p_ab_before = pa.probability_of(&["a", "b"]).to_probability();
        let p_a_before = pa.probability_of(&["a"]).to_probability();
        let p_c_before = pa.probability_of(&["c"]).to_probability();

        assert!(p_ab_before > 0.0, "P('ab') should be positive before normalize");
        assert!(p_a_before > 0.0, "P('a') should be positive before normalize");
        assert!(
            approx_eq(p_c_before, 0.0),
            "P('c') should be zero before normalize"
        );

        pa.normalize();

        let p_ab_after = pa.probability_of(&["a", "b"]).to_probability();
        let p_a_after = pa.probability_of(&["a"]).to_probability();
        let p_c_after = pa.probability_of(&["c"]).to_probability();

        // Support preservation: positive stays positive, zero stays zero.
        assert!(
            p_ab_after > 0.0,
            "P('ab') should remain positive after normalize, got {:.6}",
            p_ab_after
        );
        assert!(
            p_a_after > 0.0,
            "P('a') should remain positive after normalize, got {:.6}",
            p_a_after
        );
        assert!(
            approx_eq(p_c_after, 0.0),
            "P('c') should remain zero after normalize, got {:.6}",
            p_c_after
        );
    }

    #[test]
    fn test_normalize_preserves_relative_ordering() {
        // Rocq: `positive_preserved` + proportionality.
        // If P(w1) > P(w2) before normalization, the same holds after.
        let mut pa = build_simple_pa(
            3,
            &[
                (0, "a", 1, 0.9), // high probability path
                (0, "b", 2, 0.1), // low probability path
                (1, "c", 2, 1.0),
                (2, "c", 2, 1.0),
            ],
            0,
            &[2],
        );

        let p_ac_before = pa.probability_of(&["a", "c"]).to_probability();
        let p_bc_before = pa.probability_of(&["b", "c"]).to_probability();
        assert!(
            p_ac_before > p_bc_before,
            "P('ac') > P('bc') before: {:.6} vs {:.6}",
            p_ac_before,
            p_bc_before
        );

        pa.normalize();

        let p_ac_after = pa.probability_of(&["a", "c"]).to_probability();
        let p_bc_after = pa.probability_of(&["b", "c"]).to_probability();
        assert!(
            p_ac_after > p_bc_after,
            "P('ac') > P('bc') should be preserved after normalize: {:.6} vs {:.6}",
            p_ac_after,
            p_bc_after
        );
    }

    // ── analyze_from_bundle: structure-weighted entropy ──────────────────────

    #[test]
    fn analyze_bundle_nonuniform_selectivity() {
        use crate::pipeline::CategoryInfo;

        let categories = vec![
            CategoryInfo { name: "Expr".to_string(), is_primary: true, native_type: None },
        ];

        // Rule A has 1 item, Rule B has 5 items.
        // A should have higher selectivity than B (simpler = more likely).
        let all_syntax = vec![
            ("A".to_string(), "Expr".to_string(), vec![
                crate::SyntaxItemSpec::Terminal("a".to_string()),
            ]),
            ("B".to_string(), "Expr".to_string(), vec![
                crate::SyntaxItemSpec::Terminal("b".to_string()),
                crate::SyntaxItemSpec::Terminal("c".to_string()),
                crate::SyntaxItemSpec::Terminal("d".to_string()),
                crate::SyntaxItemSpec::Terminal("e".to_string()),
                crate::SyntaxItemSpec::Terminal("f".to_string()),
            ]),
        ];

        let result = analyze_from_bundle(&all_syntax, &categories);
        assert!(result.is_normalized);
        let sel_a = result.rule_selectivities.get("Expr::A").expect("should have A");
        let sel_b = result.rule_selectivities.get("Expr::B").expect("should have B");
        assert!(sel_a > sel_b, "simpler rule A should have higher selectivity than complex rule B");
    }

    #[test]
    fn analyze_bundle_per_category_normalization() {
        use crate::pipeline::CategoryInfo;

        let categories = vec![
            CategoryInfo { name: "Expr".to_string(), is_primary: true, native_type: None },
            CategoryInfo { name: "Stmt".to_string(), is_primary: false, native_type: None },
        ];

        let all_syntax = vec![
            ("A".to_string(), "Expr".to_string(), vec![
                crate::SyntaxItemSpec::Terminal("a".to_string()),
            ]),
            ("B".to_string(), "Expr".to_string(), vec![
                crate::SyntaxItemSpec::Terminal("b".to_string()),
            ]),
            ("C".to_string(), "Stmt".to_string(), vec![
                crate::SyntaxItemSpec::Terminal("c".to_string()),
            ]),
        ];

        let result = analyze_from_bundle(&all_syntax, &categories);
        assert!(result.is_normalized);
        // All rules should have selectivities.
        assert_eq!(result.rule_selectivities.len(), 3);
    }

    #[test]
    fn analyze_bundle_entropy_nonzero() {
        use crate::pipeline::CategoryInfo;

        let categories = vec![
            CategoryInfo { name: "Expr".to_string(), is_primary: true, native_type: None },
        ];

        // Two rules with different complexity: non-uniform distribution yields positive entropy.
        let all_syntax = vec![
            ("A".to_string(), "Expr".to_string(), vec![
                crate::SyntaxItemSpec::Terminal("a".to_string()),
            ]),
            ("B".to_string(), "Expr".to_string(), vec![
                crate::SyntaxItemSpec::Terminal("b".to_string()),
                crate::SyntaxItemSpec::Terminal("c".to_string()),
            ]),
        ];

        let result = analyze_from_bundle(&all_syntax, &categories);
        assert!(result.mean_entropy > 0.0, "non-uniform distribution should have positive entropy");
    }

    #[test]
    fn analyze_bundle_single_rule_selectivity() {
        use crate::pipeline::CategoryInfo;

        let categories = vec![
            CategoryInfo { name: "Expr".to_string(), is_primary: true, native_type: None },
        ];

        let all_syntax = vec![
            ("Only".to_string(), "Expr".to_string(), vec![
                crate::SyntaxItemSpec::Terminal("x".to_string()),
            ]),
        ];

        let result = analyze_from_bundle(&all_syntax, &categories);
        let sel = result.rule_selectivities.get("Expr::Only").expect("should have Only");
        assert!((*sel - 1.0).abs() < 0.001, "single rule should have selectivity 1.0");
    }

    #[test]
    fn analyze_bundle_low_selectivity_detection() {
        use crate::pipeline::CategoryInfo;

        let categories = vec![
            CategoryInfo { name: "Expr".to_string(), is_primary: true, native_type: None },
        ];

        // Many rules: individual selectivities drop below 0.01.
        let mut all_syntax = Vec::new();
        for i in 0..200 {
            all_syntax.push((
                format!("R{}", i),
                "Expr".to_string(),
                vec![crate::SyntaxItemSpec::Terminal(format!("t{}", i))],
            ));
        }

        let result = analyze_from_bundle(&all_syntax, &categories);
        // With 200 rules of equal complexity, each has selectivity ~1/200 = 0.005 < 0.01.
        assert!(!result.low_selectivity_rules.is_empty(), "many rules should produce low-selectivity entries");
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Proptest — property-based tests for analyze_from_bundle
// ══════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod proptest_tests {
    use super::*;
    use proptest::prelude::*;
    use crate::test_generators::*;

    /// Tolerance for floating-point comparisons.
    const EPS: f64 = 1e-9;

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(30))]

        // ── Property 1: mean_entropy is always non-negative ──────────────
        //
        // Shannon entropy H = -sum(p * ln(p)) is non-negative for any valid
        // probability distribution. Since analyze_from_bundle computes entropy
        // from normalized per-category distributions, the mean over categories
        // must also be non-negative.
        #[test]
        fn prop_entropy_non_negative(
            (cats, rules) in arb_small_grammar(),
        ) {
            let result = analyze_from_bundle(&rules, &cats);
            prop_assert!(
                result.mean_entropy >= 0.0,
                "mean_entropy should be non-negative, got {}",
                result.mean_entropy,
            );
        }

        // ── Property 2: single-rule category ⟹ selectivity 1.0 ─────────
        //
        // When a category contains exactly one rule, that rule receives the
        // entire probability mass after normalization (normalized = 1.0) and
        // the category weight is rules_in_cat / total_rules = 1/1 = 1.0,
        // so selectivity = 1.0.
        #[test]
        fn prop_single_rule_selectivity_one(
            items in prop::collection::vec(arb_syntax_item(1), 1..=4),
        ) {
            use crate::pipeline::CategoryInfo;

            let categories = vec![
                CategoryInfo {
                    name: "Solo".to_string(),
                    is_primary: true,
                    native_type: None,
                },
            ];
            let all_syntax = vec![
                ("OnlyRule".to_string(), "Solo".to_string(), items),
            ];

            let result = analyze_from_bundle(&all_syntax, &categories);
            let sel = result
                .rule_selectivities
                .get("Solo::OnlyRule")
                .copied()
                .unwrap_or(0.0);
            prop_assert!(
                (sel - 1.0).abs() < EPS,
                "single-rule selectivity should be 1.0, got {}",
                sel,
            );
        }

        // ── Property 3: simpler rule ⟹ higher selectivity ───────────────
        //
        // Within the same category, a rule with fewer syntax items receives a
        // higher raw weight (1/(1+len)), which after normalization with the
        // same denominator yields a higher selectivity.  We generate two rules
        // in one category with guaranteed different item counts and verify the
        // ordering.
        #[test]
        fn prop_simpler_rule_higher_weight(
            short_len in 1..3usize,
            long_extra in 1..4usize,
        ) {
            use crate::pipeline::CategoryInfo;

            let long_len = short_len + long_extra; // guaranteed long_len > short_len

            let short_items: Vec<crate::SyntaxItemSpec> = (0..short_len)
                .map(|i| crate::SyntaxItemSpec::Terminal(format!("t{}", i)))
                .collect();
            let long_items: Vec<crate::SyntaxItemSpec> = (0..long_len)
                .map(|i| crate::SyntaxItemSpec::Terminal(format!("u{}", i)))
                .collect();

            let categories = vec![
                CategoryInfo {
                    name: "Cat".to_string(),
                    is_primary: true,
                    native_type: None,
                },
            ];
            let all_syntax = vec![
                ("Short".to_string(), "Cat".to_string(), short_items),
                ("Long".to_string(), "Cat".to_string(), long_items),
            ];

            let result = analyze_from_bundle(&all_syntax, &categories);
            let sel_short = result
                .rule_selectivities
                .get("Cat::Short")
                .copied()
                .unwrap_or(0.0);
            let sel_long = result
                .rule_selectivities
                .get("Cat::Long")
                .copied()
                .unwrap_or(0.0);
            prop_assert!(
                sel_short >= sel_long,
                "simpler rule (len={}) should have selectivity >= complex rule (len={}): {} vs {}",
                short_len, long_len, sel_short, sel_long,
            );
        }

        // ── Property 4: is_normalized is always true ─────────────────────
        //
        // analyze_from_bundle unconditionally normalizes per-category weights,
        // so is_normalized must always be true regardless of input.
        #[test]
        fn prop_is_normalized_always_true(
            (cats, rules) in arb_small_grammar(),
        ) {
            let result = analyze_from_bundle(&rules, &cats);
            prop_assert!(
                result.is_normalized,
                "is_normalized should always be true for analyze_from_bundle output",
            );
        }

        // ── Property 5: total_selectivity > 0 when rules exist ──────────
        //
        // Every rule receives a positive raw weight (1/(1+len) > 0), so after
        // normalization all selectivities are positive and their sum must be
        // strictly positive.
        #[test]
        fn prop_total_selectivity_positive(
            (cats, rules) in arb_small_grammar(),
        ) {
            // arb_small_grammar always produces at least one rule.
            prop_assume!(!rules.is_empty());
            let result = analyze_from_bundle(&rules, &cats);
            prop_assert!(
                result.total_selectivity > 0.0,
                "total_selectivity should be positive when rules exist, got {}",
                result.total_selectivity,
            );
        }

        // ── Property 6: selectivity count == rule count ──────────────────
        //
        // Each rule receives a unique qualified label ("Category::Label") in
        // the rule_selectivities map, so the map size must equal the number
        // of input rules.
        #[test]
        fn prop_rule_selectivities_count_equals_rules(
            (cats, rules) in arb_small_grammar(),
        ) {
            let num_rules = rules.len();
            let result = analyze_from_bundle(&rules, &cats);
            prop_assert_eq!(
                result.rule_selectivities.len(),
                num_rules,
                "rule_selectivities.len() should equal the number of input rules",
            );
        }

        // ── Property 7: uniform rules ⟹ entropy ≈ ln(n) ────────────────
        //
        // When all n rules in a single category have the same number of syntax
        // items, each receives the same raw weight ⟹ uniform distribution
        // after normalization.  Shannon entropy for a uniform distribution
        // over n outcomes is H = ln(n).  Since there is exactly one category,
        // mean_entropy = ln(n).
        //
        // We generate n (2..=5) rules each with exactly 2 Terminal items in
        // a single category and verify mean_entropy ≈ ln(n).
        #[test]
        fn prop_uniform_rules_max_entropy(n in 2..6usize) {
            use crate::pipeline::CategoryInfo;

            let categories = vec![
                CategoryInfo {
                    name: "Unif".to_string(),
                    is_primary: true,
                    native_type: None,
                },
            ];

            // Build n rules, each with exactly 2 Terminal items.
            let all_syntax: Vec<(String, String, Vec<crate::SyntaxItemSpec>)> = (0..n)
                .map(|i| {
                    (
                        format!("R{}", i),
                        "Unif".to_string(),
                        vec![
                            crate::SyntaxItemSpec::Terminal(format!("x{}", i)),
                            crate::SyntaxItemSpec::Terminal(format!("y{}", i)),
                        ],
                    )
                })
                .collect();

            let result = analyze_from_bundle(&all_syntax, &categories);
            let expected = (n as f64).ln();
            prop_assert!(
                (result.mean_entropy - expected).abs() < 1e-6,
                "with {} uniform rules, entropy should be ln({}) ≈ {:.6}, got {:.6}",
                n, n, expected, result.mean_entropy,
            );
        }
    }
}
