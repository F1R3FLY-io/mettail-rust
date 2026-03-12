//! Visibly Pushdown Automata (VPA) with decidable equivalence and inclusion.
//!
//! Visibly pushdown automata are a subclass of pushdown automata where the
//! input alphabet is partitioned into call, return, and internal symbols.
//! The stack discipline is determined entirely by the input — call symbols
//! push, return symbols pop, and internal symbols leave the stack unchanged.
//! This restriction yields a class that is closed under all Boolean operations
//! and has decidable equivalence and inclusion, making VPAs ideal for verifying
//! structured parsing properties.
//!
//! ## Weighted VPA Extension
//!
//! The `WeightedVpa<W>` struct generalizes the classic Boolean-weighted VPA to
//! arbitrary semirings. Each transition carries a weight `W`, enabling:
//! - **BooleanWeight** (default): standard reachability / language membership
//! - **TropicalWeight**: shortest-path / lowest-cost parsing
//! - **CountingWeight**: derivation counting
//! - **LogWeight**: log-space probabilistic parsing
//!
//! The type alias `Vpa = WeightedVpa<BooleanWeight>` preserves full backward
//! compatibility — all existing code works unchanged.
//!
//! ## Theoretical Foundations
//!
//! - **Alur & Madhusudan (2004)** — "Visibly pushdown languages." Introduces
//!   the VPA model and proves closure under union, intersection, complement,
//!   and determinization. Equivalence and inclusion are decidable in polynomial
//!   time (via product construction + emptiness).
//! - **Alur & Madhusudan (2009)** — "Adding nesting structure to words."
//!   Extended journal version with applications to XML validation and software
//!   model checking.
//! - **Alur, Kumar, Madhusudan & Viswanathan (2005)** — "Congruences for
//!   visibly pushdown languages." Myhill-Nerode theorem for VPLs, enabling
//!   minimization.
//!
//! ## PraTTaIL Integration
//!
//! VPAs model the bracket/delimiter structure of PraTTaIL grammars. Each
//! structural delimiter (parentheses, braces, brackets) is a call/return
//! symbol, and keywords/operators are internal symbols. VPA equivalence
//! checking verifies that grammar transformations preserve the nested
//! structure, and VPA inclusion checks that error recovery does not accept
//! inputs rejected by the original grammar.
//!
//! ## Diagnostic Lints
//!
//! ### V05 — Weighted Transition Anomaly
//!
//! **Severity**: Warning
//!
//! Fires when a weighted VPA has transitions with anomalous weight values
//! (e.g., all-zero weights on outgoing transitions from a non-dead state,
//! or multiplicative-identity weights that render the weighting vacuous).
//! Indicates that the weighted VPA is effectively unweighted or has dead
//! weighted paths that will never contribute to acceptance.
//!
//! ### V06 — Weighted Inclusion Violation
//!
//! **Severity**: Error
//!
//! Fires when `weighted_inclusion(A, B)` detects that the weighted language
//! of `A` is not contained in that of `B` — i.e., there exists a word `w`
//! such that `A.weighted_run(w) > B.weighted_run(w)` in the semiring's
//! natural order. For idempotent semirings, this is decidable via the
//! product construction and weighted emptiness. This lint guards grammar
//! transformations that must preserve or reduce weights (e.g., error recovery
//! must not increase parse priority beyond the original grammar).

use std::collections::{BTreeSet, HashMap, HashSet, VecDeque};
use std::fmt;
use std::marker::PhantomData;

use crate::automata::semiring::{BooleanWeight, IdempotentSemiring, Semiring};

// ══════════════════════════════════════════════════════════════════════════════
// Core types
// ══════════════════════════════════════════════════════════════════════════════

/// Partitioned alphabet for a VPA.
///
/// The input alphabet `Σ` is partitioned into three disjoint sets:
/// - `Σ_c` (call): symbols that push onto the stack
/// - `Σ_r` (return): symbols that pop from the stack
/// - `Σ_int` (internal): symbols that do not affect the stack
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VpaAlphabet {
    /// Call symbols (e.g., `(`, `{`, `[`).
    pub call_symbols: HashSet<String>,
    /// Return symbols (e.g., `)`, `}`, `]`).
    pub return_symbols: HashSet<String>,
    /// Internal symbols (e.g., `+`, `if`, identifiers).
    pub internal_symbols: HashSet<String>,
}

impl VpaAlphabet {
    /// Create a new VPA alphabet from the three symbol sets.
    pub fn new(
        call_symbols: HashSet<String>,
        return_symbols: HashSet<String>,
        internal_symbols: HashSet<String>,
    ) -> Self {
        VpaAlphabet {
            call_symbols,
            return_symbols,
            internal_symbols,
        }
    }

    /// Classify a symbol into its alphabet partition.
    pub fn classify(&self, symbol: &str) -> Option<SymbolKind> {
        if self.call_symbols.contains(symbol) {
            Some(SymbolKind::Call)
        } else if self.return_symbols.contains(symbol) {
            Some(SymbolKind::Return)
        } else if self.internal_symbols.contains(symbol) {
            Some(SymbolKind::Internal)
        } else {
            None
        }
    }
}

impl fmt::Display for VpaAlphabet {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "VpaAlphabet {{ call: {}, return: {}, internal: {} }}",
            self.call_symbols.len(),
            self.return_symbols.len(),
            self.internal_symbols.len(),
        )
    }
}

/// Classification of a symbol in the VPA alphabet.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SymbolKind {
    /// Call symbol: pushes onto the stack.
    Call,
    /// Return symbol: pops from the stack.
    Return,
    /// Internal symbol: stack-neutral.
    Internal,
}

/// A state in a VPA.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct VpaState {
    /// Unique state identifier.
    pub id: usize,
    /// Optional label for diagnostics.
    pub label: Option<String>,
}

impl VpaState {
    /// Create a new state with the given ID.
    pub fn new(id: usize) -> Self {
        VpaState { id, label: None }
    }

    /// Create a labeled state.
    pub fn labeled(id: usize, label: impl Into<String>) -> Self {
        VpaState {
            id,
            label: Some(label.into()),
        }
    }
}

impl fmt::Display for VpaState {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(ref label) = self.label {
            write!(f, "q{}({})", self.id, label)
        } else {
            write!(f, "q{}", self.id)
        }
    }
}

/// A Weighted Visibly Pushdown Automaton parameterized over semiring `W`.
///
/// The VPA `M = (Q, Σ, Γ, δ, Q₀, Z₀, F)` where:
/// - `Q` is the finite set of states
/// - `Σ = Σ_c ∪ Σ_r ∪ Σ_int` is the partitioned alphabet
/// - `Γ` is the stack alphabet
/// - `δ` consists of weighted call, return, and internal transition functions
/// - `Q₀ ⊆ Q` are initial states
/// - `Z₀ ∈ Γ` is the initial stack symbol
/// - `F ⊆ Q` are accepting states
///
/// When `W = BooleanWeight`, this is equivalent to the classical unweighted VPA.
/// Weights are carried on transitions: each target state is paired with a weight
/// value from the semiring. For `BooleanWeight`, the weight is always
/// `BooleanWeight(true)` (= `W::one()`), so the weighted structure degenerates
/// to the standard Boolean case.
///
/// Additional fields `initial_weights` and `accepting_weights` allow weighted
/// initial and accepting valuations for algorithms like `weighted_run()`. For
/// the `BooleanWeight` case, these are derived from `initial_states` and
/// `accepting_states` respectively.
#[derive(Debug, Clone)]
pub struct WeightedVpa<W: Semiring> {
    /// Set of states.
    pub states: Vec<VpaState>,
    /// Partitioned input alphabet.
    pub alphabet: VpaAlphabet,
    /// Call transitions: `(state, call_symbol) → [(state', stack_push_symbol, weight)]`.
    pub call_transitions: HashMap<(usize, String), Vec<(usize, String, W)>>,
    /// Return transitions: `(state, return_symbol, stack_top) → [(state', weight)]`.
    pub return_transitions: HashMap<(usize, String, String), Vec<(usize, W)>>,
    /// Internal transitions: `(state, internal_symbol) → [(state', weight)]`.
    pub internal_transitions: HashMap<(usize, String), Vec<(usize, W)>>,
    /// Initial state IDs (Boolean membership).
    pub initial_states: HashSet<usize>,
    /// Accepting state IDs (Boolean membership).
    pub accepting_states: HashSet<usize>,
    /// Initial stack symbol.
    pub initial_stack_symbol: String,
    /// Weighted initial state valuations. For weighted algorithms, the weight
    /// contributed by starting in state `q` is `initial_weights[q]`.
    /// For `BooleanWeight`, derived as `W::one()` for states in `initial_states`.
    pub initial_weights: HashMap<usize, W>,
    /// Weighted accepting state valuations. For weighted algorithms, the weight
    /// contributed by accepting in state `q` is `accepting_weights[q]`.
    /// For `BooleanWeight`, derived as `W::one()` for states in `accepting_states`.
    pub accepting_weights: HashMap<usize, W>,
    /// Phantom marker for the weight type (not stored, used for type inference).
    _weight: PhantomData<W>,
}

/// Backward-compatible type alias: the classical unweighted VPA is a
/// `WeightedVpa` over the Boolean semiring.
pub type Vpa = WeightedVpa<BooleanWeight>;

impl<W: Semiring> WeightedVpa<W> {
    /// Create an empty weighted VPA with the given alphabet.
    pub fn new(alphabet: VpaAlphabet) -> Self {
        WeightedVpa {
            states: Vec::new(),
            alphabet,
            call_transitions: HashMap::new(),
            return_transitions: HashMap::new(),
            internal_transitions: HashMap::new(),
            initial_states: HashSet::new(),
            accepting_states: HashSet::new(),
            initial_stack_symbol: "Z0".to_string(),
            initial_weights: HashMap::new(),
            accepting_weights: HashMap::new(),
            _weight: PhantomData,
        }
    }

    /// Add a state and return its ID.
    pub fn add_state(&mut self, label: Option<String>) -> usize {
        let id = self.states.len();
        let state = match label {
            Some(l) => VpaState::labeled(id, l),
            None => VpaState::new(id),
        };
        self.states.push(state);
        id
    }

    /// Number of states.
    pub fn num_states(&self) -> usize {
        self.states.len()
    }

    // ══════════════════════════════════════════════════════════════════════
    // Determinization, reachability, and trimming (Phase 5B.1)
    // ══════════════════════════════════════════════════════════════════════

    /// Determinize this VPA using the subset construction adapted for visibly
    /// pushdown automata (Alur & Madhusudan, 2004).
    ///
    /// Each macro-state in the determinized VPA corresponds to a set of
    /// micro-states from the original NFA. The visible stack discipline
    /// ensures that the stack height is determined solely by the input word,
    /// so we track sets-of-states without exponential stack blow-up.
    ///
    /// ## Algorithm
    ///
    /// - **Internal transitions**: standard powerset/subset NFA construction.
    ///   For each symbol, collect all NFA successors from each micro-state
    ///   in the current macro-state.
    /// - **Call transitions**: push the current macro-state ID onto a virtual
    ///   stack (encoded as the stack symbol `M{id}`), then compute the
    ///   successor macro-state from all NFA call-transition targets.
    /// - **Return transitions**: pop the virtual stack to recover the caller
    ///   macro-state. For each (micro-state, return-symbol, stack-symbol)
    ///   triple consistent with the caller macro-state's call transitions,
    ///   collect all NFA return-transition targets.
    /// - **Acceptance**: a macro-state is accepting iff it contains at least
    ///   one original accepting state.
    /// - **Totality**: the resulting VPA is total — every (macro-state, symbol)
    ///   pair has exactly one successor. Missing transitions route to a
    ///   non-accepting dead/sink state (macro-state `{}`).
    ///
    /// # Returns
    ///
    /// A new deterministic (and total) VPA accepting the same language.
    pub fn determinize(&self) -> WeightedVpa<W> {
        determinize_impl(self)
    }

    /// Check whether this VPA is deterministic.
    ///
    /// A VPA is deterministic iff:
    /// 1. It has exactly one initial state.
    /// 2. For each state and each internal symbol, there is at most one target.
    /// 3. For each state and each call symbol, there is at most one (target, push) pair.
    /// 4. For each state, return symbol, and stack-top symbol, there is at most
    ///    one target.
    ///
    /// # Returns
    ///
    /// `true` if the VPA is deterministic, `false` otherwise.
    pub fn is_deterministic(&self) -> bool {
        // Condition 1: exactly one initial state.
        if self.initial_states.len() != 1 {
            return false;
        }

        // Condition 2: internal transitions — at most one target per (state, symbol).
        for targets in self.internal_transitions.values() {
            if targets.len() > 1 {
                return false;
            }
        }

        // Condition 3: call transitions — at most one (target, push) per (state, symbol).
        for targets in self.call_transitions.values() {
            if targets.len() > 1 {
                return false;
            }
        }

        // Condition 4: return transitions — at most one target per (state, symbol, stack_top).
        for targets in self.return_transitions.values() {
            if targets.len() > 1 {
                return false;
            }
        }

        true
    }

    /// Compute the set of states reachable from the initial states via BFS.
    ///
    /// A state is reachable if there exists some input word and stack
    /// configuration that leads to it from an initial state. This analysis
    /// is conservative (over-approximates): it considers all transitions
    /// regardless of stack contents, since tracking full stack configurations
    /// would be unbounded.
    ///
    /// # Returns
    ///
    /// The set of all reachable `VpaState`s (cloned from `self.states`).
    pub fn reachable_states(&self) -> HashSet<VpaState> {
        let reachable_ids = self.reachable_state_ids();
        reachable_ids
            .into_iter()
            .filter_map(|id| self.states.get(id).cloned())
            .collect()
    }

    /// Compute the set of reachable state IDs from initial states via BFS.
    ///
    /// This is the internal helper that returns IDs rather than `VpaState`
    /// values, used by both `reachable_states()` and `trim()`.
    fn reachable_state_ids(&self) -> HashSet<usize> {
        let mut visited: HashSet<usize> = HashSet::new();
        let mut queue: VecDeque<usize> = VecDeque::new();

        for &q0 in &self.initial_states {
            if visited.insert(q0) {
                queue.push_back(q0);
            }
        }

        while let Some(state) = queue.pop_front() {
            // Follow internal transitions.
            for targets in self.internal_transitions.iter().filter_map(|((s, _), t)| {
                if *s == state {
                    Some(t)
                } else {
                    None
                }
            }) {
                for &(t, _) in targets {
                    if visited.insert(t) {
                        queue.push_back(t);
                    }
                }
            }

            // Follow call transitions.
            for targets in self.call_transitions.iter().filter_map(|((s, _), t)| {
                if *s == state {
                    Some(t)
                } else {
                    None
                }
            }) {
                for &(t, _, _) in targets {
                    if visited.insert(t) {
                        queue.push_back(t);
                    }
                }
            }

            // Follow return transitions.
            for targets in
                self.return_transitions
                    .iter()
                    .filter_map(|((s, _, _), t)| {
                        if *s == state {
                            Some(t)
                        } else {
                            None
                        }
                    })
            {
                for &(t, _) in targets {
                    if visited.insert(t) {
                        queue.push_back(t);
                    }
                }
            }
        }

        visited
    }

    /// Remove unreachable states and their transitions, producing a trimmed VPA.
    ///
    /// States not reachable from the initial states (via `reachable_state_ids()`)
    /// are removed, and all transitions involving unreachable states are dropped.
    /// State IDs are compacted (renumbered from 0).
    ///
    /// # Returns
    ///
    /// A new VPA containing only the reachable fragment.
    pub fn trim(&self) -> WeightedVpa<W> {
        let reachable = self.reachable_state_ids();

        // Build old-ID → new-ID mapping (compaction).
        let mut old_to_new: HashMap<usize, usize> = HashMap::with_capacity(reachable.len());
        let mut new_states: Vec<VpaState> = Vec::with_capacity(reachable.len());
        // Sort reachable IDs to ensure deterministic ordering.
        let mut sorted_reachable: Vec<usize> = reachable.iter().copied().collect();
        sorted_reachable.sort_unstable();
        for old_id in &sorted_reachable {
            let new_id = new_states.len();
            old_to_new.insert(*old_id, new_id);
            let mut new_state = self.states[*old_id].clone();
            new_state.id = new_id;
            new_states.push(new_state);
        }

        let mut trimmed = WeightedVpa::new(self.alphabet.clone());
        trimmed.states = new_states;
        trimmed.initial_stack_symbol = self.initial_stack_symbol.clone();

        // Remap initial states.
        for &q0 in &self.initial_states {
            if let Some(&new_id) = old_to_new.get(&q0) {
                trimmed.initial_states.insert(new_id);
            }
        }

        // Remap accepting states.
        for &qf in &self.accepting_states {
            if let Some(&new_id) = old_to_new.get(&qf) {
                trimmed.accepting_states.insert(new_id);
            }
        }

        // Remap initial weights.
        for (&q, w) in &self.initial_weights {
            if let Some(&new_id) = old_to_new.get(&q) {
                trimmed.initial_weights.insert(new_id, *w);
            }
        }

        // Remap accepting weights.
        for (&q, w) in &self.accepting_weights {
            if let Some(&new_id) = old_to_new.get(&q) {
                trimmed.accepting_weights.insert(new_id, *w);
            }
        }

        // Remap internal transitions.
        for ((src, sym), targets) in &self.internal_transitions {
            if let Some(&new_src) = old_to_new.get(src) {
                let remapped: Vec<(usize, W)> = targets
                    .iter()
                    .filter_map(|&(t, w)| old_to_new.get(&t).map(|&new_t| (new_t, w)))
                    .collect();
                if !remapped.is_empty() {
                    trimmed
                        .internal_transitions
                        .insert((new_src, sym.clone()), remapped);
                }
            }
        }

        // Remap call transitions.
        for ((src, sym), targets) in &self.call_transitions {
            if let Some(&new_src) = old_to_new.get(src) {
                let remapped: Vec<(usize, String, W)> = targets
                    .iter()
                    .filter_map(|&(t, ref gamma, w)| {
                        old_to_new
                            .get(&t)
                            .map(|&new_t| (new_t, gamma.clone(), w))
                    })
                    .collect();
                if !remapped.is_empty() {
                    trimmed
                        .call_transitions
                        .insert((new_src, sym.clone()), remapped);
                }
            }
        }

        // Remap return transitions.
        for ((src, sym, gamma), targets) in &self.return_transitions {
            if let Some(&new_src) = old_to_new.get(src) {
                let remapped: Vec<(usize, W)> = targets
                    .iter()
                    .filter_map(|&(t, w)| old_to_new.get(&t).map(|&new_t| (new_t, w)))
                    .collect();
                if !remapped.is_empty() {
                    trimmed
                        .return_transitions
                        .insert((new_src, sym.clone(), gamma.clone()), remapped);
                }
            }
        }

        trimmed
    }

    // ══════════════════════════════════════════════════════════════════════
    // Weighted operations
    // ══════════════════════════════════════════════════════════════════════

    /// Simulate a weighted VPA on a word and return the total acceptance weight.
    ///
    /// For each initial state `q₀`, the run begins with weight
    /// `initial_weights[q₀]` (or `W::one()` if `q₀` is in `initial_states`
    /// but has no explicit weight). Each transition multiplies (⊗) the
    /// accumulated weight by the transition weight. At the end, each accepting
    /// configuration's weight is multiplied by `accepting_weights[q]` (or
    /// `W::one()` if in `accepting_states` without explicit weight). All
    /// accepting run weights are combined via semiring addition (⊕).
    ///
    /// For `BooleanWeight`, this reduces to standard reachability: the result
    /// is `BooleanWeight(true)` iff the word is accepted.
    ///
    /// # Arguments
    ///
    /// * `word` — the input symbols to consume.
    ///
    /// # Returns
    ///
    /// The total acceptance weight (semiring sum over all accepting runs).
    pub fn weighted_run(&self, word: &[&str]) -> W {
        // Configuration: (state, stack) → accumulated weight.
        // We use a HashMap to combine weights (⊕) for configurations that
        // merge at the same (state, stack) pair.
        let mut configs: HashMap<(usize, Vec<String>), W> = HashMap::new();

        // Seed with initial configurations.
        for &q0 in &self.initial_states {
            let w0 = self
                .initial_weights
                .get(&q0)
                .copied()
                .unwrap_or_else(W::one);
            let init_stack = vec![self.initial_stack_symbol.clone()];
            let key = (q0, init_stack);
            let entry = configs.entry(key).or_insert_with(W::zero);
            *entry = entry.plus(&w0);
        }

        for sym in word {
            let sym_str = sym.to_string();
            let mut next_configs: HashMap<(usize, Vec<String>), W> = HashMap::new();

            match self.alphabet.classify(sym) {
                Some(SymbolKind::Internal) => {
                    for ((state, stack), weight) in &configs {
                        if let Some(targets) =
                            self.internal_transitions.get(&(*state, sym_str.clone()))
                        {
                            for &(t, tw) in targets {
                                let run_w = weight.times(&tw);
                                let key = (t, stack.clone());
                                let entry =
                                    next_configs.entry(key).or_insert_with(W::zero);
                                *entry = entry.plus(&run_w);
                            }
                        }
                    }
                }
                Some(SymbolKind::Call) => {
                    for ((state, stack), weight) in &configs {
                        if let Some(targets) =
                            self.call_transitions.get(&(*state, sym_str.clone()))
                        {
                            for &(t, ref gamma, tw) in targets {
                                let run_w = weight.times(&tw);
                                let mut new_stack = stack.clone();
                                new_stack.push(gamma.clone());
                                let key = (t, new_stack);
                                let entry =
                                    next_configs.entry(key).or_insert_with(W::zero);
                                *entry = entry.plus(&run_w);
                            }
                        }
                    }
                }
                Some(SymbolKind::Return) => {
                    for ((state, stack), weight) in &configs {
                        if stack.len() > 1 {
                            let top = &stack[stack.len() - 1];
                            if let Some(targets) = self.return_transitions.get(&(
                                *state,
                                sym_str.clone(),
                                top.clone(),
                            )) {
                                for &(t, tw) in targets {
                                    let run_w = weight.times(&tw);
                                    let mut new_stack = stack.clone();
                                    new_stack.pop();
                                    let key = (t, new_stack);
                                    let entry =
                                        next_configs.entry(key).or_insert_with(W::zero);
                                    *entry = entry.plus(&run_w);
                                }
                            }
                        }
                    }
                }
                None => {
                    // Unknown symbol — all configurations die.
                }
            }

            configs = next_configs;
        }

        // Collect acceptance weight: ⊕ over all configs in accepting states.
        let mut total = W::zero();
        for ((state, _stack), weight) in &configs {
            if self.accepting_states.contains(state) {
                let accept_w = self
                    .accepting_weights
                    .get(state)
                    .copied()
                    .unwrap_or_else(W::one);
                let run_w = weight.times(&accept_w);
                total = total.plus(&run_w);
            }
        }

        total
    }

    /// Weighted subset construction: determinize with weight aggregation.
    ///
    /// Each macro-state tracks a mapping from micro-states to accumulated
    /// weights (`HashMap<usize, W>`). On internal/call/return transitions,
    /// weights are propagated via semiring multiplication (⊗) and merged
    /// via semiring addition (⊕) when micro-states coincide.
    ///
    /// The resulting deterministic VPA has one initial state (the macro-state
    /// corresponding to the original initial states) and acceptance is determined
    /// by whether any micro-state in the macro-state is an original accepting
    /// state.
    ///
    /// # Returns
    ///
    /// A new deterministic `WeightedVpa<W>` accepting the same weighted language.
    pub fn weighted_determinize(&self) -> WeightedVpa<W> {
        // Macro-state: BTreeMap<usize, ()> for deterministic ordering (we track
        // weights separately since BTreeSet is used as the key).
        let mut macro_to_id: HashMap<BTreeSet<usize>, usize> = HashMap::new();
        let mut det = WeightedVpa::new(self.alphabet.clone());

        // Dead/sink state (ID 0).
        let dead_macro: BTreeSet<usize> = BTreeSet::new();
        let dead_id = det.add_state(Some("dead".to_string()));
        macro_to_id.insert(dead_macro.clone(), dead_id);

        // Initial macro-state.
        let initial_macro: BTreeSet<usize> = self.initial_states.iter().copied().collect();
        let initial_id = det.add_state(None);
        macro_to_id.insert(initial_macro.clone(), initial_id);
        det.initial_states.insert(initial_id);

        // Compute initial weight for the initial macro-state.
        let mut initial_w = W::zero();
        for &q in &initial_macro {
            let w = self
                .initial_weights
                .get(&q)
                .copied()
                .unwrap_or_else(W::one);
            initial_w = initial_w.plus(&w);
        }
        det.initial_weights.insert(initial_id, initial_w);

        if initial_macro
            .iter()
            .any(|s| self.accepting_states.contains(s))
        {
            det.accepting_states.insert(initial_id);
            // Compute accepting weight for the initial macro-state.
            let mut accept_w = W::zero();
            for &q in &initial_macro {
                if self.accepting_states.contains(&q) {
                    let w = self
                        .accepting_weights
                        .get(&q)
                        .copied()
                        .unwrap_or_else(W::one);
                    accept_w = accept_w.plus(&w);
                }
            }
            det.accepting_weights.insert(initial_id, accept_w);
        }

        let mut worklist: VecDeque<BTreeSet<usize>> = VecDeque::new();
        worklist.push_back(initial_macro);
        worklist.push_back(dead_macro);

        let call_syms: Vec<String> = self.alphabet.call_symbols.iter().cloned().collect();
        let ret_syms: Vec<String> = self.alphabet.return_symbols.iter().cloned().collect();
        let int_syms: Vec<String> = self.alphabet.internal_symbols.iter().cloned().collect();

        while let Some(current_macro) = worklist.pop_front() {
            let current_id = macro_to_id[&current_macro];

            // Internal transitions.
            for sym in &int_syms {
                let mut next_macro = BTreeSet::new();
                let mut combined_weight = W::zero();
                for &q in &current_macro {
                    if let Some(targets) =
                        self.internal_transitions.get(&(q, sym.clone()))
                    {
                        for &(t, tw) in targets {
                            next_macro.insert(t);
                            combined_weight = combined_weight.plus(&tw);
                        }
                    }
                }
                let next_id =
                    *macro_to_id
                        .entry(next_macro.clone())
                        .or_insert_with(|| {
                            let id = det.add_state(None);
                            if next_macro
                                .iter()
                                .any(|s| self.accepting_states.contains(s))
                            {
                                det.accepting_states.insert(id);
                                let mut aw = W::zero();
                                for &q in &next_macro {
                                    if self.accepting_states.contains(&q) {
                                        let w = self
                                            .accepting_weights
                                            .get(&q)
                                            .copied()
                                            .unwrap_or_else(W::one);
                                        aw = aw.plus(&w);
                                    }
                                }
                                det.accepting_weights.insert(id, aw);
                            }
                            worklist.push_back(next_macro.clone());
                            id
                        });
                det.internal_transitions
                    .entry((current_id, sym.clone()))
                    .or_insert_with(Vec::new)
                    .push((next_id, combined_weight));
            }

            // Call transitions.
            for sym in &call_syms {
                let mut next_macro = BTreeSet::new();
                let mut combined_weight = W::zero();
                for &q in &current_macro {
                    if let Some(targets) =
                        self.call_transitions.get(&(q, sym.clone()))
                    {
                        for &(t, _, tw) in targets {
                            next_macro.insert(t);
                            combined_weight = combined_weight.plus(&tw);
                        }
                    }
                }
                let next_id =
                    *macro_to_id
                        .entry(next_macro.clone())
                        .or_insert_with(|| {
                            let id = det.add_state(None);
                            if next_macro
                                .iter()
                                .any(|s| self.accepting_states.contains(s))
                            {
                                det.accepting_states.insert(id);
                                let mut aw = W::zero();
                                for &q in &next_macro {
                                    if self.accepting_states.contains(&q) {
                                        let w = self
                                            .accepting_weights
                                            .get(&q)
                                            .copied()
                                            .unwrap_or_else(W::one);
                                        aw = aw.plus(&w);
                                    }
                                }
                                det.accepting_weights.insert(id, aw);
                            }
                            worklist.push_back(next_macro.clone());
                            id
                        });
                let stack_sym = format!("M{}", current_id);
                det.call_transitions
                    .entry((current_id, sym.clone()))
                    .or_insert_with(Vec::new)
                    .push((next_id, stack_sym, combined_weight));
            }

            // Return transitions.
            for sym in &ret_syms {
                let mut all_stack_syms: Vec<String> = macro_to_id
                    .values()
                    .map(|id| format!("M{}", id))
                    .collect();
                all_stack_syms.push(self.initial_stack_symbol.clone());
                all_stack_syms.sort();
                all_stack_syms.dedup();

                for stack_sym in &all_stack_syms {
                    if det
                        .return_transitions
                        .contains_key(&(current_id, sym.clone(), stack_sym.clone()))
                    {
                        continue;
                    }

                    let caller_macro_opt: Option<&BTreeSet<usize>> =
                        if stack_sym.starts_with('M') {
                            if let Ok(caller_id) = stack_sym[1..].parse::<usize>() {
                                macro_to_id
                                    .iter()
                                    .find(|(_, &id)| id == caller_id)
                                    .map(|(m, _)| m)
                            } else {
                                None
                            }
                        } else {
                            None
                        };

                    let mut next_macro = BTreeSet::new();
                    let mut combined_weight = W::zero();
                    if let Some(caller_macro) = caller_macro_opt {
                        for &q in &current_macro {
                            for &caller_q in caller_macro {
                                for csym in &call_syms {
                                    if let Some(call_targets) =
                                        self.call_transitions.get(&(caller_q, csym.clone()))
                                    {
                                        for &(_, ref pushed_gamma, _cw) in call_targets {
                                            if let Some(ret_targets) =
                                                self.return_transitions.get(&(
                                                    q,
                                                    sym.clone(),
                                                    pushed_gamma.clone(),
                                                ))
                                            {
                                                for &(t, tw) in ret_targets {
                                                    next_macro.insert(t);
                                                    combined_weight =
                                                        combined_weight.plus(&tw);
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }

                    let next_id =
                        *macro_to_id
                            .entry(next_macro.clone())
                            .or_insert_with(|| {
                                let id = det.add_state(None);
                                if next_macro
                                    .iter()
                                    .any(|s| self.accepting_states.contains(s))
                                {
                                    det.accepting_states.insert(id);
                                    let mut aw = W::zero();
                                    for &q in &next_macro {
                                        if self.accepting_states.contains(&q) {
                                            let w = self
                                                .accepting_weights
                                                .get(&q)
                                                .copied()
                                                .unwrap_or_else(W::one);
                                            aw = aw.plus(&w);
                                        }
                                    }
                                    det.accepting_weights.insert(id, aw);
                                }
                                worklist.push_back(next_macro.clone());
                                id
                            });
                    det.return_transitions
                        .entry((current_id, sym.clone(), stack_sym.clone()))
                        .or_insert_with(Vec::new)
                        .push((next_id, combined_weight));
                }
            }
        }

        det
    }

    /// Weighted inclusion check: `L_w(self) ⊆ L_w(other)`.
    ///
    /// For idempotent semirings, weighted inclusion holds iff for every word `w`,
    /// `self.weighted_run(w) ⊕ other.weighted_run(w) = other.weighted_run(w)`.
    /// This is decidable via a product construction and weighted emptiness check.
    ///
    /// The algorithm:
    /// 1. BFS over product configurations `(state_a, Option<state_b>, stack_a, stack_b)`.
    /// 2. `other`'s state is `Option<usize>` — `None` represents a dead state
    ///    (reached when `other` has no matching transition). Dead states are
    ///    non-accepting with weight zero.
    /// 3. At each configuration, if `self` is in an accepting state, check
    ///    whether `other`'s weight absorbs `self`'s weight under ⊕. If not,
    ///    inclusion fails.
    ///
    /// For `BooleanWeight`, this reduces to standard language inclusion:
    /// `L(A) ⊆ L(B)` iff there is no word accepted by A but not by B.
    ///
    /// # Returns
    ///
    /// `true` if the weighted language of `self` is included in that of `other`.
    pub fn weighted_inclusion(&self, other: &WeightedVpa<W>) -> bool
    where
        W: IdempotentSemiring,
    {
        let max_stack_depth = (self.states.len() + other.states.len()) * 4 + 2;

        // Configuration: (state_a, Option<state_b>, stack_a, stack_b).
        // Option<state_b> = None means `other` is in a dead/sink state with
        // no transitions and zero acceptance weight.
        type Config = (usize, Option<usize>, Vec<String>, Vec<String>);
        let mut visited: HashSet<Config> = HashSet::new();
        let mut queue: VecDeque<(Config, W, W)> = VecDeque::new();

        // Helper: check acceptance at a configuration and return false if
        // inclusion is violated.
        let check_acceptance = |qa: usize,
                                qb: Option<usize>,
                                wa: &W,
                                wb: &W,
                                self_ref: &WeightedVpa<W>,
                                other_ref: &WeightedVpa<W>|
         -> bool {
            // Only check when self is in an accepting state.
            if !self_ref.accepting_states.contains(&qa) {
                return true; // No violation at this config.
            }
            let fa = self_ref
                .accepting_weights
                .get(&qa)
                .copied()
                .unwrap_or_else(W::one);
            let total_a = wa.times(&fa);
            if total_a.is_zero() {
                return true; // Self has zero weight, no violation.
            }
            match qb {
                Some(qb_id) if other_ref.accepting_states.contains(&qb_id) => {
                    let fb = other_ref
                        .accepting_weights
                        .get(&qb_id)
                        .copied()
                        .unwrap_or_else(W::one);
                    let total_b = wb.times(&fb);
                    let sum = total_a.plus(&total_b);
                    // Inclusion holds iff a ⊕ b = b.
                    sum.approx_eq(&total_b, 1e-10)
                }
                _ => {
                    // other is dead or not accepting → other's weight is zero.
                    // self has non-zero weight → inclusion violated.
                    false
                }
            }
        };

        // Seed with initial configurations.
        for &qa in &self.initial_states {
            let wa = self
                .initial_weights
                .get(&qa)
                .copied()
                .unwrap_or_else(W::one);

            if other.initial_states.is_empty() {
                // other has no initial states → always dead.
                let stack_a = vec![self.initial_stack_symbol.clone()];
                let stack_b = vec![other.initial_stack_symbol.clone()];
                let config = (qa, None, stack_a, stack_b);
                if visited.insert(config.clone()) {
                    if !check_acceptance(qa, None, &wa, &W::zero(), self, other) {
                        return false;
                    }
                    queue.push_back((config, wa, W::zero()));
                }
            } else {
                for &qb in &other.initial_states {
                    let wb = other
                        .initial_weights
                        .get(&qb)
                        .copied()
                        .unwrap_or_else(W::one);
                    let stack_a = vec![self.initial_stack_symbol.clone()];
                    let stack_b = vec![other.initial_stack_symbol.clone()];
                    let config = (qa, Some(qb), stack_a, stack_b);
                    if visited.insert(config.clone()) {
                        if !check_acceptance(qa, Some(qb), &wa, &wb, self, other) {
                            return false;
                        }
                        queue.push_back((config, wa, wb));
                    }
                }
            }
        }

        while let Some((config, wa, wb)) = queue.pop_front() {
            let (qa, qb_opt, ref stack_a, ref stack_b) = config;

            // Internal transitions.
            for sym in &self.alphabet.internal_symbols {
                let a_targets = self
                    .internal_transitions
                    .get(&(qa, sym.clone()))
                    .cloned()
                    .unwrap_or_default();
                if a_targets.is_empty() {
                    continue; // self has no transition, so this path dies in self.
                }

                let b_targets: Vec<(usize, W)> = match qb_opt {
                    Some(qb) => other
                        .internal_transitions
                        .get(&(qb, sym.clone()))
                        .cloned()
                        .unwrap_or_default(),
                    None => Vec::new(), // Dead state has no transitions.
                };

                for &(ta, twa) in &a_targets {
                    let new_wa = wa.times(&twa);

                    if b_targets.is_empty() {
                        // other is dead or has no transition → other stays dead.
                        let next = (ta, None, stack_a.clone(), stack_b.clone());
                        if visited.insert(next.clone()) {
                            if !check_acceptance(ta, None, &new_wa, &W::zero(), self, other) {
                                return false;
                            }
                            queue.push_back((next, new_wa, W::zero()));
                        }
                    } else {
                        for &(tb, twb) in &b_targets {
                            let new_wb = wb.times(&twb);
                            let next = (ta, Some(tb), stack_a.clone(), stack_b.clone());
                            if visited.insert(next.clone()) {
                                if !check_acceptance(
                                    ta,
                                    Some(tb),
                                    &new_wa,
                                    &new_wb,
                                    self,
                                    other,
                                ) {
                                    return false;
                                }
                                queue.push_back((next, new_wa, new_wb));
                            }
                        }
                    }
                }
            }

            // Call transitions.
            if stack_a.len() < max_stack_depth {
                for sym in &self.alphabet.call_symbols {
                    let a_targets = self
                        .call_transitions
                        .get(&(qa, sym.clone()))
                        .cloned()
                        .unwrap_or_default();
                    if a_targets.is_empty() {
                        continue;
                    }

                    let b_targets: Vec<(usize, String, W)> = match qb_opt {
                        Some(qb) => other
                            .call_transitions
                            .get(&(qb, sym.clone()))
                            .cloned()
                            .unwrap_or_default(),
                        None => Vec::new(),
                    };

                    for &(ta, ref gamma_a, twa) in &a_targets {
                        let new_wa = wa.times(&twa);
                        let mut sa = stack_a.clone();
                        sa.push(gamma_a.clone());

                        if b_targets.is_empty() {
                            // other dead.
                            let next = (ta, None, sa, stack_b.clone());
                            if visited.insert(next.clone()) {
                                if !check_acceptance(
                                    ta,
                                    None,
                                    &new_wa,
                                    &W::zero(),
                                    self,
                                    other,
                                ) {
                                    return false;
                                }
                                queue.push_back((next, new_wa, W::zero()));
                            }
                        } else {
                            for &(tb, ref gamma_b, twb) in &b_targets {
                                let new_wb = wb.times(&twb);
                                let mut sb = stack_b.clone();
                                sb.push(gamma_b.clone());
                                let next = (ta, Some(tb), sa.clone(), sb);
                                if visited.insert(next.clone()) {
                                    if !check_acceptance(
                                        ta,
                                        Some(tb),
                                        &new_wa,
                                        &new_wb,
                                        self,
                                        other,
                                    ) {
                                        return false;
                                    }
                                    queue.push_back((next, new_wa, new_wb));
                                }
                            }
                        }
                    }
                }
            }

            // Return transitions.
            if stack_a.len() > 1 {
                let top_a = &stack_a[stack_a.len() - 1];
                for sym in &self.alphabet.return_symbols {
                    let a_targets = self
                        .return_transitions
                        .get(&(qa, sym.clone(), top_a.clone()))
                        .cloned()
                        .unwrap_or_default();
                    if a_targets.is_empty() {
                        continue;
                    }

                    let b_targets: Vec<(usize, W)> = match qb_opt {
                        Some(qb) if stack_b.len() > 1 => {
                            let top_b = &stack_b[stack_b.len() - 1];
                            other
                                .return_transitions
                                .get(&(qb, sym.clone(), top_b.clone()))
                                .cloned()
                                .unwrap_or_default()
                        }
                        _ => Vec::new(), // Dead or stack empty.
                    };

                    for &(ta, twa) in &a_targets {
                        let new_wa = wa.times(&twa);
                        let mut sa = stack_a.clone();
                        sa.pop();

                        if b_targets.is_empty() {
                            let next = (ta, None, sa, stack_b.clone());
                            if visited.insert(next.clone()) {
                                if !check_acceptance(
                                    ta,
                                    None,
                                    &new_wa,
                                    &W::zero(),
                                    self,
                                    other,
                                ) {
                                    return false;
                                }
                                queue.push_back((next, new_wa, W::zero()));
                            }
                        } else {
                            for &(tb, twb) in &b_targets {
                                let new_wb = wb.times(&twb);
                                let mut sb = stack_b.clone();
                                sb.pop();
                                let next = (ta, Some(tb), sa.clone(), sb);
                                if visited.insert(next.clone()) {
                                    if !check_acceptance(
                                        ta,
                                        Some(tb),
                                        &new_wa,
                                        &new_wb,
                                        self,
                                        other,
                                    ) {
                                        return false;
                                    }
                                    queue.push_back((next, new_wa, new_wb));
                                }
                            }
                        }
                    }
                }
            }
        }

        true
    }
}

impl<W: Semiring> fmt::Display for WeightedVpa<W> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "VPA {{ states: {}, initial: {}, accepting: {}, alphabet: {} }}",
            self.states.len(),
            self.initial_states.len(),
            self.accepting_states.len(),
            self.alphabet,
        )
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Core functions
// ══════════════════════════════════════════════════════════════════════════════

/// Construct a VPA from a PraTTaIL grammar's structural delimiters.
///
/// Extracts call/return pairs from the grammar's structural delimiters
/// (parentheses, braces, brackets) and classifies remaining terminal
/// symbols as internal.
///
/// # Arguments
///
/// * `call_return_pairs` - Pairs of (call_symbol, return_symbol) for matched delimiters.
/// * `internal_symbols` - All other terminal symbols.
///
/// # Returns
///
/// A new `Vpa` with the appropriate alphabet partition.
pub fn construct_vpa(
    call_return_pairs: &[(String, String)],
    internal_symbols: &[String],
) -> Vpa {
    // Build the partitioned alphabet from the call/return pairs and internal symbols.
    let mut call_symbols = HashSet::with_capacity(call_return_pairs.len());
    let mut return_symbols = HashSet::with_capacity(call_return_pairs.len());
    for (c, r) in call_return_pairs {
        call_symbols.insert(c.clone());
        return_symbols.insert(r.clone());
    }
    let internal_set: HashSet<String> = internal_symbols.iter().cloned().collect();

    // Validate that the three partitions are disjoint.
    for sym in &call_symbols {
        assert!(
            !return_symbols.contains(sym),
            "Symbol {:?} appears in both call and return sets",
            sym
        );
        assert!(
            !internal_set.contains(sym),
            "Symbol {:?} appears in both call and internal sets",
            sym
        );
    }
    for sym in &return_symbols {
        assert!(
            !internal_set.contains(sym),
            "Symbol {:?} appears in both return and internal sets",
            sym
        );
    }

    let alphabet = VpaAlphabet::new(call_symbols, return_symbols, internal_set);

    // Build a VPA that accepts well-matched sequences of the given delimiters
    // with arbitrary internal symbols. This is the "universal well-matched"
    // language for the given alphabet partition.
    //
    // Acceptance is purely state-based (state in F after reading all input).
    // To enforce that only well-matched words are accepted, we encode the
    // stack-depth parity into the state:
    //
    //   q_ground (ID 0, accepting):  stack at initial depth (well-matched)
    //   q_nested (ID 1, non-accepting): inside unmatched calls
    //   q_dead   (ID 2, non-accepting): sink for unmatched returns at ground
    //
    // To distinguish "returning to ground" from "still nested", call
    // transitions from q_ground push "G_<sym>" and from q_nested push "N_<sym>".
    // Return transitions popping "G_..." go to q_ground; popping "N_..." stay
    // in q_nested.
    let mut vpa = Vpa::new(alphabet);
    let q_ground = vpa.add_state(Some("ground".to_string()));
    let q_nested = vpa.add_state(Some("nested".to_string()));
    let q_dead = vpa.add_state(Some("dead".to_string()));
    vpa.initial_states.insert(q_ground);
    vpa.accepting_states.insert(q_ground);

    let w_one = BooleanWeight::one();

    // Call transitions.
    for (call_sym, _) in call_return_pairs {
        // From ground: push ground-marker, go to nested.
        let g_gamma = format!("G_{}", call_sym);
        vpa.call_transitions
            .entry((q_ground, call_sym.clone()))
            .or_insert_with(Vec::new)
            .push((q_nested, g_gamma, w_one));

        // From nested: push nested-marker, stay nested.
        let n_gamma = format!("N_{}", call_sym);
        vpa.call_transitions
            .entry((q_nested, call_sym.clone()))
            .or_insert_with(Vec::new)
            .push((q_nested, n_gamma, w_one));

        // From dead: absorb into dead.
        vpa.call_transitions
            .entry((q_dead, call_sym.clone()))
            .or_insert_with(Vec::new)
            .push((q_dead, "DEAD".to_string(), w_one));
    }

    // Return transitions.
    for (call_sym, ret_sym) in call_return_pairs {
        let g_gamma = format!("G_{}", call_sym);
        let n_gamma = format!("N_{}", call_sym);

        // From nested, pop ground-marker → return to ground.
        vpa.return_transitions
            .entry((q_nested, ret_sym.clone(), g_gamma))
            .or_insert_with(Vec::new)
            .push((q_ground, w_one));

        // From nested, pop nested-marker → stay nested.
        vpa.return_transitions
            .entry((q_nested, ret_sym.clone(), n_gamma))
            .or_insert_with(Vec::new)
            .push((q_nested, w_one));

        // From ground, return is unmatched → dead sink.
        // At ground level, the only thing on the stack is Z0.
        vpa.return_transitions
            .entry((q_ground, ret_sym.clone(), vpa.initial_stack_symbol.clone()))
            .or_insert_with(Vec::new)
            .push((q_dead, w_one));

        // From dead, any return stays dead (for all known stack tops).
        for gamma in ["DEAD", "Z0"] {
            vpa.return_transitions
                .entry((q_dead, ret_sym.clone(), gamma.to_string()))
                .or_insert_with(Vec::new)
                .push((q_dead, w_one));
        }
        for (call_sym2, _) in call_return_pairs.iter() {
            for prefix in ["G_", "N_"] {
                let gamma = format!("{}{}", prefix, call_sym2);
                vpa.return_transitions
                    .entry((q_dead, ret_sym.clone(), gamma))
                    .or_insert_with(Vec::new)
                    .push((q_dead, w_one));
            }
        }
    }

    // Internal transitions: stay in current state.
    for sym in internal_symbols {
        vpa.internal_transitions
            .entry((q_ground, sym.clone()))
            .or_insert_with(Vec::new)
            .push((q_ground, w_one));
        vpa.internal_transitions
            .entry((q_nested, sym.clone()))
            .or_insert_with(Vec::new)
            .push((q_nested, w_one));
        vpa.internal_transitions
            .entry((q_dead, sym.clone()))
            .or_insert_with(Vec::new)
            .push((q_dead, w_one));
    }

    vpa
}

/// Check language equivalence of two VPAs.
///
/// Two VPAs are equivalent iff they accept the same set of words.
/// This is decidable for VPAs (unlike general PDAs) via the product
/// construction: `L(A) = L(B)` iff `L(A) ∩ L(B̄) = ∅` and `L(Ā) ∩ L(B) = ∅`.
///
/// # Arguments
///
/// * `a` - First VPA.
/// * `b` - Second VPA.
///
/// # Returns
///
/// `true` if the two VPAs accept exactly the same language.
pub fn check_equivalence(a: &Vpa, b: &Vpa) -> bool {
    // L(A) = L(B) iff L(A) ∩ L(B̄) = ∅ AND L(Ā) ∩ L(B) = ∅.
    //
    // Step 1: Check L(A) ⊆ L(B): complement B, intersect with A, check emptiness.
    let b_complement = complement(b);
    let a_minus_b = intersect(a, &b_complement);
    if !is_language_empty(&a_minus_b) {
        return false;
    }

    // Step 2: Check L(B) ⊆ L(A): complement A, intersect with B, check emptiness.
    let a_complement = complement(a);
    let b_minus_a = intersect(b, &a_complement);
    is_language_empty(&b_minus_a)
}

/// Check whether a VPA accepts the empty language (no word is accepted).
///
/// Uses BFS over configurations `(state, stack)`. Acceptance is purely
/// state-based: a configuration is accepting if its state is in `F`.
///
/// We bound exploration by tracking visited `(state, stack)` pairs and
/// capping the maximum stack depth at `|Q| * 4 + 2`. Any accepting run
/// on a longer word must revisit a `(state, stack_top)` pair and can be
/// shortened, so this bound suffices for emptiness detection.
pub fn is_language_empty(vpa: &Vpa) -> bool {
    let max_stack_depth = vpa.states.len() * 4 + 2;

    let mut visited: HashSet<(usize, Vec<String>)> = HashSet::new();
    let mut queue: VecDeque<(usize, Vec<String>)> = VecDeque::new();

    // Seed with initial configurations.
    for &q0 in &vpa.initial_states {
        let init_stack = vec![vpa.initial_stack_symbol.clone()];
        let config = (q0, init_stack);
        if visited.insert(config.clone()) {
            if vpa.accepting_states.contains(&q0) {
                return false; // The empty word is accepted.
            }
            queue.push_back(config);
        }
    }

    while let Some((state, stack)) = queue.pop_front() {
        // Internal transitions: stack unchanged.
        for sym in &vpa.alphabet.internal_symbols {
            if let Some(targets) = vpa.internal_transitions.get(&(state, sym.clone())) {
                for &(t, _) in targets {
                    let config = (t, stack.clone());
                    if visited.insert(config.clone()) {
                        if vpa.accepting_states.contains(&t) {
                            return false;
                        }
                        queue.push_back(config);
                    }
                }
            }
        }

        // Call transitions: push onto the stack.
        if stack.len() < max_stack_depth {
            for sym in &vpa.alphabet.call_symbols {
                if let Some(targets) = vpa.call_transitions.get(&(state, sym.clone())) {
                    for &(t, ref gamma, _) in targets {
                        let mut new_stack = stack.clone();
                        new_stack.push(gamma.clone());
                        let config = (t, new_stack);
                        if visited.insert(config.clone()) {
                            if vpa.accepting_states.contains(&t) {
                                return false;
                            }
                            queue.push_back(config);
                        }
                    }
                }
            }
        }

        // Return transitions: pop from the stack (if not at bottom-of-stack).
        if stack.len() > 1 {
            let top = &stack[stack.len() - 1];
            for sym in &vpa.alphabet.return_symbols {
                if let Some(targets) =
                    vpa.return_transitions
                        .get(&(state, sym.clone(), top.clone()))
                {
                    for &(t, _) in targets {
                        let mut new_stack = stack.clone();
                        new_stack.pop();
                        let config = (t, new_stack.clone());
                        if visited.insert(config.clone()) {
                            if vpa.accepting_states.contains(&t) {
                                return false;
                            }
                            queue.push_back(config);
                        }
                    }
                }
            }
        }
    }

    // No accepting configuration was reached.
    true
}

/// Complement a VPA (deterministic VPAs only).
///
/// Produces a VPA accepting `Σ* \ L(M)`. Requires determinization first
/// if the input VPA is nondeterministic.
///
/// # Arguments
///
/// * `vpa` - The VPA to complement.
///
/// # Returns
///
/// A new VPA accepting the complement language.
pub fn complement(vpa: &Vpa) -> Vpa {
    // Step 1: Determinize the VPA.
    let det = vpa.determinize();
    // Step 2: Swap accepting and non-accepting states.
    let all_state_ids: HashSet<usize> = (0..det.states.len()).collect();
    let new_accepting: HashSet<usize> = all_state_ids
        .difference(&det.accepting_states)
        .copied()
        .collect();
    Vpa {
        states: det.states,
        alphabet: det.alphabet,
        call_transitions: det.call_transitions,
        return_transitions: det.return_transitions,
        internal_transitions: det.internal_transitions,
        initial_states: det.initial_states,
        accepting_states: new_accepting,
        initial_stack_symbol: det.initial_stack_symbol,
        initial_weights: det.initial_weights,
        accepting_weights: HashMap::new(), // Recomputed from new accepting set.
        _weight: PhantomData,
    }
}

/// Determinize a VPA using the subset construction adapted for visibly
/// pushdown automata.
///
/// Each macro-state is a set of micro-states from the original NFA.
/// For call transitions, we push the current macro-state onto a "stack summary"
/// so that return transitions can restore it. This exploits the visible stack
/// discipline: the stack height is determined solely by the input word, so
/// we can track sets-of-states without exponential stack blow-up.
///
/// The resulting VPA is deterministic and **total**: every (macro-state, symbol)
/// pair has exactly one successor. Transitions that would lead to no NFA states
/// are directed to a non-accepting "dead" sink state.
fn determinize_impl<W: Semiring>(vpa: &WeightedVpa<W>) -> WeightedVpa<W> {
    let mut macro_to_id: HashMap<BTreeSet<usize>, usize> = HashMap::new();
    let mut det = WeightedVpa::new(vpa.alphabet.clone());

    let w_one = W::one();

    // Create the dead/sink state first (ID 0). It is non-accepting and all
    // of its transitions loop back to itself.
    let dead_macro: BTreeSet<usize> = BTreeSet::new();
    let dead_id = det.add_state(Some("dead".to_string()));
    macro_to_id.insert(dead_macro.clone(), dead_id);
    // dead_id is NOT added to accepting_states.

    let initial_macro: BTreeSet<usize> = vpa.initial_states.iter().copied().collect();
    let initial_id = det.add_state(None);
    macro_to_id.insert(initial_macro.clone(), initial_id);
    det.initial_states.insert(initial_id);

    if initial_macro.iter().any(|s| vpa.accepting_states.contains(s)) {
        det.accepting_states.insert(initial_id);
    }

    let mut worklist: VecDeque<BTreeSet<usize>> = VecDeque::new();
    worklist.push_back(initial_macro);
    // Also process the dead state to install self-loops.
    worklist.push_back(dead_macro);

    let call_syms: Vec<String> = vpa.alphabet.call_symbols.iter().cloned().collect();
    let ret_syms: Vec<String> = vpa.alphabet.return_symbols.iter().cloned().collect();
    let int_syms: Vec<String> = vpa.alphabet.internal_symbols.iter().cloned().collect();

    // Helper closure to get-or-create a macro-state ID.
    // We cannot use a closure that borrows `det` mutably, so we inline it.

    while let Some(current_macro) = worklist.pop_front() {
        let current_id = macro_to_id[&current_macro];

        // Internal transitions: straightforward subset construction.
        for sym in &int_syms {
            let mut next_macro = BTreeSet::new();
            for &q in &current_macro {
                if let Some(targets) = vpa.internal_transitions.get(&(q, sym.clone())) {
                    for &(t, _) in targets {
                        next_macro.insert(t);
                    }
                }
            }
            // If next_macro is empty, it maps to the dead state.
            let next_id = *macro_to_id.entry(next_macro.clone()).or_insert_with(|| {
                let id = det.add_state(None);
                if next_macro.iter().any(|s| vpa.accepting_states.contains(s)) {
                    det.accepting_states.insert(id);
                }
                worklist.push_back(next_macro.clone());
                id
            });
            det.internal_transitions
                .entry((current_id, sym.clone()))
                .or_insert_with(Vec::new)
                .push((next_id, w_one));
        }

        // Call transitions: push the current macro-state ID as the stack symbol.
        for sym in &call_syms {
            let mut next_macro = BTreeSet::new();
            for &q in &current_macro {
                if let Some(targets) = vpa.call_transitions.get(&(q, sym.clone())) {
                    for &(t, _, _) in targets {
                        next_macro.insert(t);
                    }
                }
            }
            let next_id = *macro_to_id.entry(next_macro.clone()).or_insert_with(|| {
                let id = det.add_state(None);
                if next_macro.iter().any(|s| vpa.accepting_states.contains(s)) {
                    det.accepting_states.insert(id);
                }
                worklist.push_back(next_macro.clone());
                id
            });
            let stack_sym = format!("M{}", current_id);
            det.call_transitions
                .entry((current_id, sym.clone()))
                .or_insert_with(Vec::new)
                .push((next_id, stack_sym, w_one));
        }

        // Return transitions: for each (return_symbol, stack_top) pair,
        // compute the set of successor states. We must handle every possible
        // stack symbol that could appear, including the initial stack symbol.
        for sym in &ret_syms {
            // Collect all determinized stack symbols we have seen so far
            // (M{id} for each macro-state, plus the initial stack symbol).
            let mut all_stack_syms: Vec<String> = macro_to_id
                .values()
                .map(|id| format!("M{}", id))
                .collect();
            all_stack_syms.push(vpa.initial_stack_symbol.clone());
            all_stack_syms.sort();
            all_stack_syms.dedup();

            for stack_sym in &all_stack_syms {
                // Already have a transition for this (current_id, sym, stack_sym)?
                if det
                    .return_transitions
                    .contains_key(&(current_id, sym.clone(), stack_sym.clone()))
                {
                    continue;
                }

                // If the stack symbol is "M{caller_id}", find the caller macro-state.
                let caller_macro_opt: Option<&BTreeSet<usize>> = if stack_sym.starts_with('M') {
                    if let Ok(caller_id) = stack_sym[1..].parse::<usize>() {
                        macro_to_id
                            .iter()
                            .find(|(_, &id)| id == caller_id)
                            .map(|(m, _)| m)
                    } else {
                        None
                    }
                } else {
                    None
                };

                let mut next_macro = BTreeSet::new();
                if let Some(caller_macro) = caller_macro_opt {
                    for &q in &current_macro {
                        for &caller_q in caller_macro {
                            for csym in &call_syms {
                                if let Some(call_targets) =
                                    vpa.call_transitions.get(&(caller_q, csym.clone()))
                                {
                                    for (_, pushed_gamma, _) in call_targets {
                                        if let Some(ret_targets) =
                                            vpa.return_transitions.get(&(
                                                q,
                                                sym.clone(),
                                                pushed_gamma.clone(),
                                            ))
                                        {
                                            for &(t, _) in ret_targets {
                                                next_macro.insert(t);
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
                // If the stack_sym is the initial stack symbol (Z0) and a return
                // is read at the bottom of the stack, we go to dead.
                // (next_macro stays empty → maps to dead state.)

                let next_id =
                    *macro_to_id
                        .entry(next_macro.clone())
                        .or_insert_with(|| {
                            let id = det.add_state(None);
                            if next_macro.iter().any(|s| vpa.accepting_states.contains(s)) {
                                det.accepting_states.insert(id);
                            }
                            worklist.push_back(next_macro.clone());
                            id
                        });
                det.return_transitions
                    .entry((current_id, sym.clone(), stack_sym.clone()))
                    .or_insert_with(Vec::new)
                    .push((next_id, w_one));
            }
        }
    }

    det
}

/// Intersect two VPAs via the product construction.
///
/// The product VPA accepts `L(A) ∩ L(B)`. State space is `Q_A × Q_B × Γ_A × Γ_B`
/// (using synchronized stacks).
///
/// # Arguments
///
/// * `a` - First VPA.
/// * `b` - Second VPA.
///
/// # Returns
///
/// A new VPA accepting the intersection of both languages.
pub fn intersect(a: &Vpa, b: &Vpa) -> Vpa {
    // Product construction with synchronized stack operations.
    //
    // Product state: (q_a, q_b) from VPA `a` and VPA `b`.
    // Product stack symbol: (gamma_a, gamma_b) — both automata push/pop in sync.
    //
    // The alphabet must be compatible (same partition). We use `a`'s alphabet
    // and assert that `b` classifies symbols the same way.

    let w_one = BooleanWeight::one();

    // Build the merged alphabet (union of both; classification must agree).
    let merged_alphabet = merge_alphabets(&a.alphabet, &b.alphabet);

    let mut product = Vpa::new(merged_alphabet);
    // Map (state_a, state_b) → product state ID.
    let mut pair_to_id: HashMap<(usize, usize), usize> = HashMap::new();
    let mut worklist: VecDeque<(usize, usize)> = VecDeque::new();

    // Initial states: all pairs of initial states.
    for &qa in &a.initial_states {
        for &qb in &b.initial_states {
            let pid = product.add_state(None);
            pair_to_id.insert((qa, qb), pid);
            product.initial_states.insert(pid);
            if a.accepting_states.contains(&qa) && b.accepting_states.contains(&qb) {
                product.accepting_states.insert(pid);
            }
            worklist.push_back((qa, qb));
        }
    }

    let call_syms: Vec<String> = product.alphabet.call_symbols.iter().cloned().collect();
    let ret_syms: Vec<String> = product.alphabet.return_symbols.iter().cloned().collect();
    let int_syms: Vec<String> = product.alphabet.internal_symbols.iter().cloned().collect();

    while let Some((qa, qb)) = worklist.pop_front() {
        let current_pid = pair_to_id[&(qa, qb)];

        // Internal transitions: both automata step, stack untouched.
        for sym in &int_syms {
            let a_targets = a
                .internal_transitions
                .get(&(qa, sym.clone()))
                .cloned()
                .unwrap_or_default();
            let b_targets = b
                .internal_transitions
                .get(&(qb, sym.clone()))
                .cloned()
                .unwrap_or_default();
            for &(ta, _) in &a_targets {
                for &(tb, _) in &b_targets {
                    let next_pid = get_or_create_product_state(
                        ta,
                        tb,
                        a,
                        b,
                        &mut product,
                        &mut pair_to_id,
                        &mut worklist,
                    );
                    product
                        .internal_transitions
                        .entry((current_pid, sym.clone()))
                        .or_insert_with(Vec::new)
                        .push((next_pid, w_one));
                }
            }
        }

        // Call transitions: both push. Product stack symbol encodes both.
        for sym in &call_syms {
            let a_targets = a
                .call_transitions
                .get(&(qa, sym.clone()))
                .cloned()
                .unwrap_or_default();
            let b_targets = b
                .call_transitions
                .get(&(qb, sym.clone()))
                .cloned()
                .unwrap_or_default();
            for &(ta, ref gamma_a, _) in &a_targets {
                for &(tb, ref gamma_b, _) in &b_targets {
                    let next_pid = get_or_create_product_state(
                        ta,
                        tb,
                        a,
                        b,
                        &mut product,
                        &mut pair_to_id,
                        &mut worklist,
                    );
                    // Encode both stack symbols as a single product stack symbol.
                    let product_gamma = format!("({},{})", gamma_a, gamma_b);
                    product
                        .call_transitions
                        .entry((current_pid, sym.clone()))
                        .or_insert_with(Vec::new)
                        .push((next_pid, product_gamma, w_one));
                }
            }
        }

        // Return transitions: both pop. Must match on the product stack symbol.
        for sym in &ret_syms {
            // Collect all (gamma_a, gamma_b) pairs that could be on the stack.
            // We look at all call transitions that could have pushed symbols.
            let mut a_gammas: HashSet<String> = HashSet::new();
            let mut b_gammas: HashSet<String> = HashSet::new();
            for ((s, _, gamma), _) in &a.return_transitions {
                if *s == qa {
                    a_gammas.insert(gamma.clone());
                }
            }
            for ((s, _, gamma), _) in &b.return_transitions {
                if *s == qb {
                    b_gammas.insert(gamma.clone());
                }
            }

            for ga in &a_gammas {
                let a_targets = a
                    .return_transitions
                    .get(&(qa, sym.clone(), ga.clone()))
                    .cloned()
                    .unwrap_or_default();
                for gb in &b_gammas {
                    let b_targets = b
                        .return_transitions
                        .get(&(qb, sym.clone(), gb.clone()))
                        .cloned()
                        .unwrap_or_default();
                    if a_targets.is_empty() || b_targets.is_empty() {
                        continue;
                    }
                    let product_gamma = format!("({},{})", ga, gb);
                    for &(ta, _) in &a_targets {
                        for &(tb, _) in &b_targets {
                            let next_pid = get_or_create_product_state(
                                ta,
                                tb,
                                a,
                                b,
                                &mut product,
                                &mut pair_to_id,
                                &mut worklist,
                            );
                            product
                                .return_transitions
                                .entry((current_pid, sym.clone(), product_gamma.clone()))
                                .or_insert_with(Vec::new)
                                .push((next_pid, w_one));
                        }
                    }
                }
            }
        }
    }

    product
}

/// Get or create a product state for the pair `(qa, qb)`.
fn get_or_create_product_state(
    qa: usize,
    qb: usize,
    a: &Vpa,
    b: &Vpa,
    product: &mut Vpa,
    pair_to_id: &mut HashMap<(usize, usize), usize>,
    worklist: &mut VecDeque<(usize, usize)>,
) -> usize {
    *pair_to_id.entry((qa, qb)).or_insert_with(|| {
        let pid = product.add_state(None);
        if a.accepting_states.contains(&qa) && b.accepting_states.contains(&qb) {
            product.accepting_states.insert(pid);
        }
        worklist.push_back((qa, qb));
        pid
    })
}

/// Merge two VPA alphabets, asserting classification consistency.
///
/// If a symbol appears in both alphabets, it must be classified the same way.
/// The result is the union of both alphabets.
fn merge_alphabets(a: &VpaAlphabet, b: &VpaAlphabet) -> VpaAlphabet {
    let mut call = a.call_symbols.clone();
    let mut ret = a.return_symbols.clone();
    let mut int = a.internal_symbols.clone();

    // Add symbols from `b`, checking consistency.
    for sym in &b.call_symbols {
        if let Some(kind) = a.classify(sym) {
            assert_eq!(
                kind,
                SymbolKind::Call,
                "Symbol {:?} classified as {:?} in `a` but Call in `b`",
                sym,
                kind
            );
        }
        call.insert(sym.clone());
    }
    for sym in &b.return_symbols {
        if let Some(kind) = a.classify(sym) {
            assert_eq!(
                kind,
                SymbolKind::Return,
                "Symbol {:?} classified as {:?} in `a` but Return in `b`",
                sym,
                kind
            );
        }
        ret.insert(sym.clone());
    }
    for sym in &b.internal_symbols {
        if let Some(kind) = a.classify(sym) {
            assert_eq!(
                kind,
                SymbolKind::Internal,
                "Symbol {:?} classified as {:?} in `a` but Internal in `b`",
                sym,
                kind
            );
        }
        int.insert(sym.clone());
    }

    VpaAlphabet::new(call, ret, int)
}

// ══════════════════════════════════════════════════════════════════════════════
// Pipeline bridge
// ══════════════════════════════════════════════════════════════════════════════

/// Pipeline-level VPA analysis result.
#[derive(Debug, Clone)]
pub struct VpaAnalysis {
    /// Whether the grammar's structured sublanguage admits a deterministic VPA.
    pub is_determinizable: bool,
    /// Alphabet classification mismatches (tokens used as both call and return).
    pub alphabet_mismatches: Vec<String>,
    /// Number of VPA states.
    pub state_count: usize,
    /// Upper bound on valid nesting depth (derived from VPA state count).
    /// Input exceeding this bound is structurally beyond the grammar's capacity.
    pub max_nesting_bound: usize,
}

/// Classify terminal tokens from a grammar's syntax items into a [`VpaAlphabet`].
///
/// Tokens `(`, `{`, `[` are classified as **Call** symbols; `)`, `}`, `]` as
/// **Return** symbols; every other terminal is classified as **Internal**.
///
/// # Arguments
///
/// * `all_syntax` — flattened grammar rules as `(label, category, syntax_items)` triples.
///
/// # Returns
///
/// A `VpaAlphabet` with the three partitions populated from the grammar terminals.
pub fn build_alphabet_from_syntax(
    all_syntax: &[(String, String, Vec<crate::SyntaxItemSpec>)],
) -> VpaAlphabet {
    let mut call_symbols: HashSet<String> = HashSet::new();
    let mut return_symbols: HashSet<String> = HashSet::new();
    let mut internal_symbols: HashSet<String> = HashSet::new();

    // Recursively collect all terminals from a syntax item tree.
    fn collect_terminals(item: &crate::SyntaxItemSpec, out: &mut Vec<String>) {
        match item {
            crate::SyntaxItemSpec::Terminal(t) => {
                out.push(t.clone());
            }
            crate::SyntaxItemSpec::Collection { separator, .. } => {
                out.push(separator.clone());
            }
            crate::SyntaxItemSpec::Sep { body, separator, .. } => {
                out.push(separator.clone());
                collect_terminals(body, out);
            }
            crate::SyntaxItemSpec::Map { body_items } => {
                for sub in body_items {
                    collect_terminals(sub, out);
                }
            }
            crate::SyntaxItemSpec::Zip { body, .. } => {
                collect_terminals(body, out);
            }
            crate::SyntaxItemSpec::Optional { inner } => {
                for sub in inner {
                    collect_terminals(sub, out);
                }
            }
            crate::SyntaxItemSpec::BinderCollection { separator, .. } => {
                out.push(separator.clone());
            }
            // NonTerminal, IdentCapture, Binder — no terminals to extract.
            _ => {}
        }
    }

    for (_label, _category, items) in all_syntax {
        let mut terminals = Vec::new();
        for item in items {
            collect_terminals(item, &mut terminals);
        }
        for tok in terminals {
            match tok.as_str() {
                "(" | "{" | "[" => {
                    call_symbols.insert(tok);
                }
                ")" | "}" | "]" => {
                    return_symbols.insert(tok);
                }
                _ => {
                    internal_symbols.insert(tok);
                }
            }
        }
    }

    VpaAlphabet::new(call_symbols, return_symbols, internal_symbols)
}

/// Construct a VPA from pipeline data and analyse determinizability.
///
/// This bridge function connects the compile-time grammar representation
/// (`CategoryInfo` + flattened syntax triples) to the VPA analysis engine.
///
/// # Algorithm
///
/// 1. Classifies all terminal tokens via [`build_alphabet_from_syntax`].
/// 2. Detects **alphabet mismatches** — tokens that appear in both the call and
///    return partitions, which would violate the VPA input-alphabet disjointness
///    requirement.
/// 3. Builds a VPA for the grammar's structured sublanguage using
///    [`construct_vpa`] with the standard delimiter pairs `()`/`{}`/`[]`.
/// 4. Checks determinizability: a grammar is determinizable iff there are no
///    alphabet mismatches and the constructed VPA can be determinized (i.e. the
///    VPA after calling [`Vpa::determinize`] is deterministic).
///
/// # Arguments
///
/// * `categories` — category metadata from the parser pipeline.
/// * `all_syntax` — flattened grammar rules as `(label, category, syntax_items)` triples.
///
/// # Returns
///
/// `Some(VpaAnalysis)` with the analysis results, or `None` if the alphabet
/// is completely empty (no terminals at all in the grammar).
pub fn analyze_from_bundle(
    _categories: &[crate::pipeline::CategoryInfo],
    all_syntax: &[(String, String, Vec<crate::SyntaxItemSpec>)],
) -> Option<VpaAnalysis> {
    let alphabet = build_alphabet_from_syntax(all_syntax);

    // If the grammar has zero terminals there is nothing to analyse.
    if alphabet.call_symbols.is_empty()
        && alphabet.return_symbols.is_empty()
        && alphabet.internal_symbols.is_empty()
    {
        return None;
    }

    // Detect alphabet mismatches: tokens classified as *both* call and return.
    let mut alphabet_mismatches: Vec<String> = alphabet
        .call_symbols
        .intersection(&alphabet.return_symbols)
        .cloned()
        .collect();
    alphabet_mismatches.sort();

    // Build the canonical call/return pairs from the alphabet.
    // Only pairs whose call AND return halves are present are included.
    let delimiter_pairs: &[(&str, &str)] = &[("(", ")"), ("{", "}"), ("[", "]")];
    let call_return_pairs: Vec<(String, String)> = delimiter_pairs
        .iter()
        .filter(|(c, r)| {
            alphabet.call_symbols.contains(*c) && alphabet.return_symbols.contains(*r)
        })
        .map(|(c, r)| (c.to_string(), r.to_string()))
        .collect();

    // Gather internal symbols (excluding any that are in the mismatch set).
    let internal: Vec<String> = alphabet.internal_symbols.iter().cloned().collect();

    // Construct the VPA for the structured sublanguage.
    let vpa = construct_vpa(&call_return_pairs, &internal);
    let state_count = vpa.num_states();

    // Determinizability: no mismatches AND the determinized VPA is deterministic.
    let is_determinizable = if alphabet_mismatches.is_empty() {
        let det = vpa.determinize();
        det.is_deterministic()
    } else {
        // Mismatches violate the VPA alphabet disjointness invariant,
        // so the structured sublanguage cannot be modelled as a VPA at all.
        false
    };

    Some(VpaAnalysis {
        is_determinizable,
        alphabet_mismatches,
        state_count,
        max_nesting_bound: state_count,
    })
}

// ══════════════════════════════════════════════════════════════════════════════
// Predicate Dispatch — PredicateCompiler integration
// ══════════════════════════════════════════════════════════════════════════════

/// Compiler adapter for the Visibly Pushdown Automata module (M4).
///
/// Activated by nested `letprop` scopes with balanced open/close (VPL variety).
#[cfg(feature = "predicate-dispatch")]
pub struct VpaCompiler;

#[cfg(feature = "predicate-dispatch")]
impl crate::predicate_dispatch::PredicateCompiler for VpaCompiler {
    type Output = Option<VpaAnalysis>;

    fn compile_predicate(
        &self,
        _pred: &crate::symbolic::PredicateExpr,
        _profile: &crate::predicate_dispatch::PredicateProfile,
        all_syntax: &[(String, String, Vec<crate::SyntaxItemSpec>)],
        categories: &[crate::pipeline::CategoryInfo],
    ) -> Self::Output {
        analyze_from_bundle(categories, all_syntax)
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Sprint 6B — VPA Delimiter Verification
// ══════════════════════════════════════════════════════════════════════════════

/// Build a VPA alphabet from custom token push/pop annotations.
///
/// Tokens with `push_mode` become call symbols, tokens with `is_pop` become
/// return symbols, and all others become internal symbols.  This classifies
/// tokens from *both* the default-mode token list and every named mode's
/// token list, producing a single unified alphabet.
///
/// # Arguments
///
/// * `default_tokens` — token specs from the default (top-level) lexer mode.
/// * `modes` — named lexer modes, each containing its own token specs.
///
/// # Examples
///
/// ```rust,ignore
/// let alphabet = build_vpa_alphabet_from_modes(&default_tokens, &modes);
/// assert!(alphabet.call_symbols.contains("("));
/// assert!(alphabet.return_symbols.contains(")"));
/// ```
pub fn build_vpa_alphabet_from_modes(
    default_tokens: &[crate::CustomTokenSpec],
    modes: &[crate::LexerModeSpec],
) -> VpaAlphabet {
    let mut call_symbols: HashSet<String> = HashSet::new();
    let mut return_symbols: HashSet<String> = HashSet::new();
    let mut internal_symbols: HashSet<String> = HashSet::new();

    // Classify a single token spec by its push/pop annotations.
    let mut classify_token = |spec: &crate::CustomTokenSpec| {
        if spec.push_mode.is_some() {
            call_symbols.insert(spec.name.clone());
        } else if spec.is_pop {
            return_symbols.insert(spec.name.clone());
        } else {
            internal_symbols.insert(spec.name.clone());
        }
    };

    for spec in default_tokens {
        classify_token(spec);
    }
    for mode in modes {
        for spec in &mode.token_specs {
            classify_token(spec);
        }
    }

    VpaAlphabet::new(call_symbols, return_symbols, internal_symbols)
}

/// Build a delimiter skip table from a flat token stream.
///
/// For each opening delimiter at index `i`, `skip_table[i] = Some(j)` where `j`
/// is the index of the matching closer.  For non-delimiters and unmatched
/// openers, `skip_table[i] = None`.
///
/// Built in O(n) via a single stack pass using the VPA alphabet classification.
///
/// # Arguments
///
/// * `tokens` — flat token stream of `(token, range)` pairs.
/// * `classify` — closure that maps a token reference to a [`SymbolKind`].
///
/// # Examples
///
/// ```rust,ignore
/// let table = build_skip_table(&tokens, |tok| alphabet.classify(tok).unwrap_or(SymbolKind::Internal));
/// // table[0] == Some(3) means the opener at 0 matches the closer at 3.
/// ```
pub fn build_skip_table<T>(
    tokens: &[(T, crate::runtime_types::Range)],
    classify: impl Fn(&T) -> SymbolKind,
) -> Vec<Option<usize>> {
    let mut table = vec![None; tokens.len()];
    let mut stack: Vec<usize> = Vec::new();
    for (i, (tok, _)) in tokens.iter().enumerate() {
        match classify(tok) {
            SymbolKind::Call => stack.push(i),
            SymbolKind::Return => {
                if let Some(opener) = stack.pop() {
                    table[opener] = Some(i);
                }
            }
            SymbolKind::Internal => {}
        }
    }
    table
}

/// A token tree: either a leaf token or a delimited group.
///
/// Constructed from a flat token stream and its [`build_skip_table`] output
/// in O(n) time.  Groups nest recursively — a `Group`'s `children` may
/// themselves contain further `Group` nodes.
///
/// # Type Parameter
///
/// * `T` — the token type (e.g., a generated `Token` enum).
#[derive(Debug, Clone)]
pub enum TokenTree<T> {
    /// A leaf token (non-delimiter or unmatched delimiter).
    Token(T, crate::runtime_types::Range),
    /// A delimited group: opener, contents, closer.
    Group {
        /// The opening delimiter token and its source range.
        open: (T, crate::runtime_types::Range),
        /// The closing delimiter token and its source range.
        close: (T, crate::runtime_types::Range),
        /// Child nodes between the delimiters.
        children: Vec<TokenTree<T>>,
    },
}

/// Build a token tree from a flat token stream and skip table.
///
/// Uses the skip table produced by [`build_skip_table`] to group matching
/// delimiters into nested [`TokenTree::Group`] nodes.  Unmatched openers
/// (where `skip_table[i] == None` despite the token being a `Call` symbol)
/// are demoted to leaf [`TokenTree::Token`] nodes.
///
/// Runs in O(n) time (each token is visited exactly once).
///
/// # Arguments
///
/// * `tokens` — flat token stream of `(token, range)` pairs.
/// * `skip_table` — the skip table built by [`build_skip_table`].
/// * `classify` — closure mapping a token reference to a [`SymbolKind`].
pub fn build_token_tree<T: Clone>(
    tokens: &[(T, crate::runtime_types::Range)],
    skip_table: &[Option<usize>],
    classify: impl Fn(&T) -> SymbolKind,
) -> Vec<TokenTree<T>> {
    /// Recursive helper that builds children within the half-open range
    /// `[start, end)` of the token stream.
    fn build_range<T: Clone>(
        tokens: &[(T, crate::runtime_types::Range)],
        skip_table: &[Option<usize>],
        classify: &dyn Fn(&T) -> SymbolKind,
        start: usize,
        end: usize,
    ) -> Vec<TokenTree<T>> {
        let mut result = Vec::new();
        let mut i = start;
        while i < end {
            match classify(&tokens[i].0) {
                SymbolKind::Call => {
                    if let Some(closer) = skip_table[i] {
                        let children =
                            build_range(tokens, skip_table, classify, i + 1, closer);
                        result.push(TokenTree::Group {
                            open: tokens[i].clone(),
                            close: tokens[closer].clone(),
                            children,
                        });
                        i = closer + 1;
                    } else {
                        // Unmatched opener — demote to leaf.
                        result.push(TokenTree::Token(
                            tokens[i].0.clone(),
                            tokens[i].1,
                        ));
                        i += 1;
                    }
                }
                _ => {
                    result.push(TokenTree::Token(tokens[i].0.clone(), tokens[i].1));
                    i += 1;
                }
            }
        }
        result
    }
    build_range(tokens, skip_table, &classify, 0, tokens.len())
}

// ══════════════════════════════════════════════════════════════════════════════
// Tests
// ══════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;
    use crate::automata::semiring::TropicalWeight;

    fn sample_alphabet() -> VpaAlphabet {
        VpaAlphabet::new(
            ["(".to_string(), "{".to_string()].into_iter().collect(),
            [")".to_string(), "}".to_string()].into_iter().collect(),
            ["+".to_string(), "id".to_string()].into_iter().collect(),
        )
    }

    #[test]
    fn alphabet_classification() {
        let alpha = sample_alphabet();
        assert_eq!(alpha.classify("("), Some(SymbolKind::Call));
        assert_eq!(alpha.classify(")"), Some(SymbolKind::Return));
        assert_eq!(alpha.classify("+"), Some(SymbolKind::Internal));
        assert_eq!(alpha.classify("unknown"), None);
    }

    #[test]
    fn vpa_construction_and_display() {
        let alpha = sample_alphabet();
        let mut vpa = Vpa::new(alpha);
        let q0 = vpa.add_state(Some("start".to_string()));
        let q1 = vpa.add_state(None);
        vpa.initial_states.insert(q0);
        vpa.accepting_states.insert(q1);
        assert_eq!(vpa.num_states(), 2);
        assert!(vpa.to_string().contains("states: 2"));
    }

    #[test]
    fn vpa_state_display() {
        let labeled = VpaState::labeled(0, "init");
        assert_eq!(labeled.to_string(), "q0(init)");
        let unlabeled = VpaState::new(3);
        assert_eq!(unlabeled.to_string(), "q3");
    }

    // ══════════════════════════════════════════════════════════════════════
    // Tests for construct_vpa, complement, intersect, check_equivalence
    // ══════════════════════════════════════════════════════════════════════

    /// Helper: build a VPA that accepts well-matched parentheses with internal
    /// symbols via `construct_vpa`.
    fn build_paren_vpa() -> Vpa {
        construct_vpa(
            &[("(".to_string(), ")".to_string())],
            &["+".to_string(), "id".to_string()],
        )
    }

    /// Helper: manually build a VPA that accepts ONLY the empty word.
    fn build_epsilon_only_vpa() -> Vpa {
        let alpha = VpaAlphabet::new(
            ["(".to_string()].into_iter().collect(),
            [")".to_string()].into_iter().collect(),
            ["+".to_string(), "id".to_string()].into_iter().collect(),
        );
        let mut vpa = Vpa::new(alpha);
        let q0 = vpa.add_state(Some("start".to_string()));
        vpa.initial_states.insert(q0);
        vpa.accepting_states.insert(q0);
        // No transitions at all — only the empty word is accepted.
        vpa
    }

    /// Helper: simulate a VPA on a given input word. Returns true iff the VPA
    /// accepts the word (reaches an accepting state after consuming all input).
    /// Acceptance is purely state-based (state in F); stack contents do not
    /// affect acceptance. The VPA design must encode stack-depth constraints
    /// into the state space if needed (e.g., ground vs. nested states).
    fn simulate(vpa: &Vpa, input: &[&str]) -> bool {
        // BFS over (state, stack) configurations.
        let mut configs: HashSet<(usize, Vec<String>)> = HashSet::new();
        for &q0 in &vpa.initial_states {
            configs.insert((q0, vec![vpa.initial_stack_symbol.clone()]));
        }

        for sym in input {
            let sym_str = sym.to_string();
            let mut next_configs: HashSet<(usize, Vec<String>)> = HashSet::new();

            match vpa.alphabet.classify(sym) {
                Some(SymbolKind::Internal) => {
                    for (state, stack) in &configs {
                        if let Some(targets) =
                            vpa.internal_transitions.get(&(*state, sym_str.clone()))
                        {
                            for &(t, _) in targets {
                                next_configs.insert((t, stack.clone()));
                            }
                        }
                    }
                }
                Some(SymbolKind::Call) => {
                    for (state, stack) in &configs {
                        if let Some(targets) =
                            vpa.call_transitions.get(&(*state, sym_str.clone()))
                        {
                            for (t, gamma, _) in targets {
                                let mut new_stack = stack.clone();
                                new_stack.push(gamma.clone());
                                next_configs.insert((*t, new_stack));
                            }
                        }
                    }
                }
                Some(SymbolKind::Return) => {
                    for (state, stack) in &configs {
                        if stack.len() > 1 {
                            let top = &stack[stack.len() - 1];
                            if let Some(targets) = vpa.return_transitions.get(&(
                                *state,
                                sym_str.clone(),
                                top.clone(),
                            )) {
                                for &(t, _) in targets {
                                    let mut new_stack = stack.clone();
                                    new_stack.pop();
                                    next_configs.insert((t, new_stack));
                                }
                            }
                        }
                    }
                }
                None => {
                    // Unknown symbol — no transitions possible.
                }
            }

            configs = next_configs;
        }

        // Acceptance is purely state-based: state in F after consuming all input.
        configs
            .iter()
            .any(|(state, _stack)| vpa.accepting_states.contains(state))
    }

    #[test]
    fn construct_vpa_accepts_well_matched() {
        let vpa = build_paren_vpa();

        // Empty string should be accepted (q0 is initial and accepting).
        assert!(simulate(&vpa, &[]), "empty string should be accepted");

        // Well-matched: "()"
        assert!(simulate(&vpa, &["(", ")"]), "() should be accepted");

        // Well-matched: "(())"
        assert!(
            simulate(&vpa, &["(", "(", ")", ")"]),
            "(()) should be accepted"
        );

        // Well-matched: "( id + id )"
        assert!(
            simulate(&vpa, &["(", "id", "+", "id", ")"]),
            "(id+id) should be accepted"
        );

        // Internal symbols only: "id + id"
        assert!(
            simulate(&vpa, &["id", "+", "id"]),
            "id+id should be accepted"
        );

        // Mismatched: "(" alone — stack not at initial height.
        assert!(!simulate(&vpa, &["("]), "( alone should be rejected");

        // Mismatched: ")" alone — no return transition from empty stack.
        assert!(!simulate(&vpa, &[")"]), ") alone should be rejected");

        // Mismatched: "((" — unmatched opens.
        assert!(!simulate(&vpa, &["(", "("]), "(( should be rejected");

        // Mismatched: ")(" — wrong order.
        assert!(!simulate(&vpa, &[")", "("]), ")( should be rejected");
    }

    #[test]
    fn equivalence_of_identical_vpas() {
        // Two independently constructed VPAs with the same language should be equivalent.
        let vpa1 = build_paren_vpa();
        let vpa2 = build_paren_vpa();
        assert!(
            check_equivalence(&vpa1, &vpa2),
            "identical VPAs should be equivalent"
        );
    }

    #[test]
    fn non_equivalence_of_different_vpas() {
        // The well-matched VPA accepts "()" but the epsilon-only VPA does not.
        let well_matched = build_paren_vpa();
        let eps_only = build_epsilon_only_vpa();
        assert!(
            !check_equivalence(&well_matched, &eps_only),
            "well-matched VPA and epsilon-only VPA should NOT be equivalent"
        );
    }

    #[test]
    fn complement_swaps_acceptance() {
        let vpa = build_paren_vpa();
        let comp = complement(&vpa);

        // The original accepts the empty string; the complement should reject it.
        assert!(
            simulate(&vpa, &[]),
            "original should accept empty string"
        );
        // After complement, the complement should reject the empty string.
        assert!(
            !simulate(&comp, &[]),
            "complement should reject empty string"
        );

        // The original accepts "()"; the complement should reject it.
        assert!(simulate(&vpa, &["(", ")"]), "original should accept ()");
        assert!(
            !simulate(&comp, &["(", ")"]),
            "complement should reject ()"
        );

        // The original accepts "id"; the complement should reject it.
        assert!(simulate(&vpa, &["id"]), "original should accept id");
        assert!(
            !simulate(&comp, &["id"]),
            "complement should reject id"
        );
    }

    #[test]
    fn intersect_restricts_language() {
        // Intersect the well-matched VPA with the epsilon-only VPA.
        // The result should accept only the empty string (the only word in both).
        let well_matched = build_paren_vpa();
        let eps_only = build_epsilon_only_vpa();
        let inter = intersect(&well_matched, &eps_only);

        // Empty string is in both languages.
        assert!(
            simulate(&inter, &[]),
            "intersection should accept empty string"
        );

        // "()" is in well_matched but not in eps_only.
        assert!(
            !simulate(&inter, &["(", ")"]),
            "intersection should reject () since epsilon-only doesn't accept it"
        );
    }

    // ══════════════════════════════════════════════════════════════════════
    // Tests for determinize, is_deterministic, reachable_states, trim
    // (Phase 5B.1)
    // ══════════════════════════════════════════════════════════════════════

    #[test]
    fn determinize_preserves_language() {
        // The construct_vpa-built VPA is already deterministic, but
        // determinize() should still produce an equivalent VPA.
        let vpa = build_paren_vpa();
        let det = vpa.determinize();

        // The determinized VPA should accept the same words.
        assert!(simulate(&det, &[]), "det should accept empty string");
        assert!(simulate(&det, &["(", ")"]), "det should accept ()");
        assert!(
            simulate(&det, &["(", "(", ")", ")"]),
            "det should accept (())"
        );
        assert!(
            simulate(&det, &["(", "id", "+", "id", ")"]),
            "det should accept (id+id)"
        );
        assert!(
            simulate(&det, &["id", "+", "id"]),
            "det should accept id+id"
        );

        // And reject the same words.
        assert!(!simulate(&det, &["("]), "det should reject (");
        assert!(!simulate(&det, &[")"]), "det should reject )");
        assert!(!simulate(&det, &["(", "("]), "det should reject ((");
        assert!(!simulate(&det, &[")", "("]), "det should reject )(");
    }

    #[test]
    fn determinize_nondeterministic_vpa() {
        // Build a nondeterministic VPA: two initial states with overlapping
        // transitions. One path accepts "()", the other accepts "id".
        let alpha = VpaAlphabet::new(
            ["(".to_string()].into_iter().collect(),
            [")".to_string()].into_iter().collect(),
            ["id".to_string()].into_iter().collect(),
        );
        let mut nfa_vpa = Vpa::new(alpha);
        let q0 = nfa_vpa.add_state(Some("init0".to_string()));
        let q1 = nfa_vpa.add_state(Some("init1".to_string()));
        let q2 = nfa_vpa.add_state(Some("after_call".to_string()));
        let q3 = nfa_vpa.add_state(Some("accept_paren".to_string()));
        let q4 = nfa_vpa.add_state(Some("accept_id".to_string()));

        let w_one = BooleanWeight::one();

        nfa_vpa.initial_states.insert(q0);
        nfa_vpa.initial_states.insert(q1); // Two initial states => nondeterministic.
        nfa_vpa.accepting_states.insert(q3);
        nfa_vpa.accepting_states.insert(q4);

        // Path 1: q0 --(-->  q2 --)-- q3 (accepts "()")
        nfa_vpa
            .call_transitions
            .entry((q0, "(".to_string()))
            .or_insert_with(Vec::new)
            .push((q2, "G_(".to_string(), w_one));
        nfa_vpa
            .return_transitions
            .entry((q2, ")".to_string(), "G_(".to_string()))
            .or_insert_with(Vec::new)
            .push((q3, w_one));

        // Path 2: q1 --id--> q4 (accepts "id")
        nfa_vpa
            .internal_transitions
            .entry((q1, "id".to_string()))
            .or_insert_with(Vec::new)
            .push((q4, w_one));

        assert!(
            !nfa_vpa.is_deterministic(),
            "NFA VPA with 2 initial states should not be deterministic"
        );

        let det = nfa_vpa.determinize();
        assert!(
            det.is_deterministic(),
            "determinized VPA should be deterministic"
        );

        // Both words should still be accepted.
        assert!(
            simulate(&det, &["(", ")"]),
            "det should accept () from path 1"
        );
        assert!(
            simulate(&det, &["id"]),
            "det should accept id from path 2"
        );
        // And words not in either path should be rejected.
        assert!(
            !simulate(&det, &["("]),
            "det should reject unmatched ("
        );
        assert!(
            !simulate(&det, &[")"]),
            "det should reject unmatched )"
        );
    }

    #[test]
    fn is_deterministic_on_constructed_vpa() {
        // construct_vpa produces a deterministic VPA (one initial state,
        // at most one target per transition key).
        let vpa = build_paren_vpa();
        assert!(
            vpa.is_deterministic(),
            "construct_vpa should produce a deterministic VPA"
        );
    }

    #[test]
    fn is_deterministic_false_multiple_initials() {
        let alpha = VpaAlphabet::new(
            HashSet::new(),
            HashSet::new(),
            ["a".to_string()].into_iter().collect(),
        );
        let mut vpa = Vpa::new(alpha);
        let q0 = vpa.add_state(None);
        let q1 = vpa.add_state(None);
        vpa.initial_states.insert(q0);
        vpa.initial_states.insert(q1);
        assert!(
            !vpa.is_deterministic(),
            "VPA with two initial states should not be deterministic"
        );
    }

    #[test]
    fn is_deterministic_false_nondeterministic_internal() {
        let alpha = VpaAlphabet::new(
            HashSet::new(),
            HashSet::new(),
            ["a".to_string()].into_iter().collect(),
        );
        let mut vpa = Vpa::new(alpha);
        let q0 = vpa.add_state(None);
        let q1 = vpa.add_state(None);
        let q2 = vpa.add_state(None);
        let w_one = BooleanWeight::one();
        vpa.initial_states.insert(q0);
        // q0 --a--> {q1, q2}: nondeterministic internal transition.
        vpa.internal_transitions
            .insert((q0, "a".to_string()), vec![(q1, w_one), (q2, w_one)]);
        assert!(
            !vpa.is_deterministic(),
            "VPA with nondeterministic internal transition should not be deterministic"
        );
    }

    #[test]
    fn reachable_states_basic() {
        let vpa = build_paren_vpa();
        let reachable = vpa.reachable_states();

        // All states in the constructed VPA should be reachable (ground,
        // nested, dead are all reachable via transitions from ground).
        assert_eq!(
            reachable.len(),
            vpa.states.len(),
            "all states in construct_vpa result should be reachable"
        );
    }

    #[test]
    fn reachable_states_excludes_isolated() {
        // Add an unreachable state and verify it is excluded.
        let alpha = VpaAlphabet::new(
            HashSet::new(),
            HashSet::new(),
            ["a".to_string()].into_iter().collect(),
        );
        let mut vpa = Vpa::new(alpha);
        let q0 = vpa.add_state(Some("start".to_string()));
        let q1 = vpa.add_state(Some("reachable".to_string()));
        let _q_isolated = vpa.add_state(Some("isolated".to_string()));
        let w_one = BooleanWeight::one();
        vpa.initial_states.insert(q0);
        vpa.internal_transitions
            .insert((q0, "a".to_string()), vec![(q1, w_one)]);

        let reachable = vpa.reachable_states();
        let reachable_ids: HashSet<usize> = reachable.iter().map(|s| s.id).collect();

        // q0 and q1 should be reachable, but NOT the isolated state.
        // Note: reachable_states returns states with compacted IDs from the
        // original, so we check by label.
        assert!(
            reachable_ids.contains(&q0),
            "q0 (start) should be reachable"
        );
        assert!(
            reachable_ids.contains(&q1),
            "q1 (reachable) should be reachable"
        );
        assert_eq!(reachable.len(), 2, "only 2 states should be reachable");
    }

    #[test]
    fn trim_removes_unreachable() {
        // Build a VPA with an unreachable state and verify trim removes it.
        let alpha = VpaAlphabet::new(
            ["(".to_string()].into_iter().collect(),
            [")".to_string()].into_iter().collect(),
            ["id".to_string()].into_iter().collect(),
        );
        let mut vpa = Vpa::new(alpha);
        let q0 = vpa.add_state(Some("start".to_string()));
        let q1 = vpa.add_state(Some("after_id".to_string()));
        let _q_unreachable = vpa.add_state(Some("unreachable".to_string()));
        let w_one = BooleanWeight::one();
        vpa.initial_states.insert(q0);
        vpa.accepting_states.insert(q1);
        vpa.internal_transitions
            .insert((q0, "id".to_string()), vec![(q1, w_one)]);

        assert_eq!(vpa.num_states(), 3, "original VPA has 3 states");

        let trimmed = vpa.trim();
        assert_eq!(
            trimmed.num_states(),
            2,
            "trimmed VPA should have 2 states (unreachable removed)"
        );

        // The trimmed VPA should still accept "id".
        assert!(simulate(&trimmed, &["id"]), "trimmed should accept id");
        // And still reject empty string (q0 is not accepting).
        assert!(
            !simulate(&trimmed, &[]),
            "trimmed should reject empty string"
        );
    }

    #[test]
    fn trim_preserves_language() {
        // Trimming a VPA with no unreachable states should preserve it exactly.
        let vpa = build_paren_vpa();
        let trimmed = vpa.trim();

        // Same number of states (all are reachable in construct_vpa output).
        assert_eq!(trimmed.num_states(), vpa.num_states());

        // Language preservation: check the same set of words.
        for input in &[
            vec![],
            vec!["(", ")"],
            vec!["(", "(", ")", ")"],
            vec!["id", "+", "id"],
            vec!["(", "id", "+", "id", ")"],
        ] {
            assert_eq!(
                simulate(&vpa, input),
                simulate(&trimmed, input),
                "trim should preserve acceptance of {:?}",
                input
            );
        }
        for input in &[
            vec!["("],
            vec![")"],
            vec!["(", "("],
            vec![")", "("],
        ] {
            assert_eq!(
                simulate(&vpa, input),
                simulate(&trimmed, input),
                "trim should preserve rejection of {:?}",
                input
            );
        }
    }

    #[test]
    fn determinize_then_trim_roundtrip() {
        // determinize + trim should produce a compact, deterministic VPA
        // with the same language as the original.
        let vpa = build_paren_vpa();
        let det = vpa.determinize();
        let trimmed = det.trim();

        assert!(
            trimmed.is_deterministic(),
            "determinize + trim should remain deterministic"
        );

        // Language equivalence via simulation on representative words.
        for input in &[
            vec![],
            vec!["(", ")"],
            vec!["(", "(", ")", ")"],
            vec!["id"],
            vec!["(", "id", ")"],
        ] {
            assert_eq!(
                simulate(&vpa, input),
                simulate(&trimmed, input),
                "determinize+trim should preserve acceptance of {:?}",
                input
            );
        }
    }

    #[test]
    fn determinize_epsilon_only_vpa() {
        // The epsilon-only VPA should determinize to a VPA that still accepts
        // only the empty string.
        let eps = build_epsilon_only_vpa();
        let det = eps.determinize();

        assert!(
            det.is_deterministic(),
            "determinized epsilon-only VPA should be deterministic"
        );
        assert!(
            simulate(&det, &[]),
            "det of epsilon-only should accept empty string"
        );
        // It should reject any non-empty input (even symbols in the alphabet).
        // Note: the epsilon-only VPA has no transitions, so determinize produces
        // a dead sink for all symbols, which is non-accepting.
        assert!(
            !simulate(&det, &["("]),
            "det of epsilon-only should reject ("
        );
        assert!(
            !simulate(&det, &["+"]),
            "det of epsilon-only should reject +"
        );
    }

    #[test]
    fn trim_empty_vpa() {
        // A VPA with no initial states has no reachable states.
        let alpha = VpaAlphabet::new(HashSet::new(), HashSet::new(), HashSet::new());
        let mut vpa = Vpa::new(alpha);
        let _q0 = vpa.add_state(None);
        // No initial states set.
        let trimmed = vpa.trim();
        assert_eq!(
            trimmed.num_states(),
            0,
            "VPA with no initial states should trim to 0 states"
        );
    }

    #[test]
    fn test_analyze_from_bundle_basic() {
        let cats = vec![crate::pipeline::CategoryInfo {
            name: "Expr".to_string(),
            native_type: None,
            is_primary: true,
        }];
        let syntax: Vec<(String, String, Vec<crate::SyntaxItemSpec>)> = vec![(
            "Group".to_string(),
            "Expr".to_string(),
            vec![
                crate::SyntaxItemSpec::Terminal("(".to_string()),
                crate::SyntaxItemSpec::NonTerminal {
                    category: "Expr".to_string(),
                    param_name: "inner".to_string(),
                },
                crate::SyntaxItemSpec::Terminal(")".to_string()),
            ],
        )];
        let result = analyze_from_bundle(&cats, &syntax);
        assert!(result.is_some(), "should produce VPA analysis for delimited syntax");
    }

    #[test]
    fn test_build_alphabet() {
        let syntax: Vec<(String, String, Vec<crate::SyntaxItemSpec>)> = vec![(
            "Group".to_string(),
            "Expr".to_string(),
            vec![
                crate::SyntaxItemSpec::Terminal("(".to_string()),
                crate::SyntaxItemSpec::NonTerminal {
                    category: "Expr".to_string(),
                    param_name: "inner".to_string(),
                },
                crate::SyntaxItemSpec::Terminal("+".to_string()),
                crate::SyntaxItemSpec::Terminal(")".to_string()),
            ],
        )];
        let alphabet = build_alphabet_from_syntax(&syntax);
        assert!(
            alphabet.call_symbols.contains("("),
            "( should be classified as call"
        );
        assert!(
            alphabet.return_symbols.contains(")"),
            ") should be classified as return"
        );
        assert!(
            alphabet.internal_symbols.contains("+"),
            "+ should be classified as internal"
        );
    }

    // ══════════════════════════════════════════════════════════════════════
    // Weighted VPA tests
    // ══════════════════════════════════════════════════════════════════════

    #[test]
    fn weighted_run_boolean_matches_simulate() {
        // For BooleanWeight, weighted_run should agree with simulate.
        let vpa = build_paren_vpa();

        // Accepted words: weighted_run should return BooleanWeight(true) = W::one().
        assert!(
            vpa.weighted_run(&[]).is_one(),
            "weighted_run on empty string should be one (accepted)"
        );
        assert!(
            vpa.weighted_run(&["(", ")"]).is_one(),
            "weighted_run on () should be one (accepted)"
        );
        assert!(
            vpa.weighted_run(&["id", "+", "id"]).is_one(),
            "weighted_run on id+id should be one (accepted)"
        );

        // Rejected words: weighted_run should return BooleanWeight(false) = W::zero().
        assert!(
            vpa.weighted_run(&["("]).is_zero(),
            "weighted_run on ( alone should be zero (rejected)"
        );
        assert!(
            vpa.weighted_run(&[")"]).is_zero(),
            "weighted_run on ) alone should be zero (rejected)"
        );
    }

    #[test]
    fn weighted_run_tropical_accumulates_cost() {
        // Build a simple weighted VPA with TropicalWeight.
        // q0 --id(cost=3.0)--> q1 (accepting)
        let alpha = VpaAlphabet::new(
            HashSet::new(),
            HashSet::new(),
            ["id".to_string()].into_iter().collect(),
        );
        let mut wvpa: WeightedVpa<TropicalWeight> = WeightedVpa::new(alpha);
        let q0 = wvpa.add_state(Some("start".to_string()));
        let q1 = wvpa.add_state(Some("accept".to_string()));
        wvpa.initial_states.insert(q0);
        wvpa.accepting_states.insert(q1);
        wvpa.initial_weights.insert(q0, TropicalWeight::one());
        wvpa.accepting_weights.insert(q1, TropicalWeight::one());

        // Transition with weight 3.0.
        wvpa.internal_transitions
            .insert((q0, "id".to_string()), vec![(q1, TropicalWeight::new(3.0))]);

        let result = wvpa.weighted_run(&["id"]);
        // Tropical: init_w(0.0) ⊗ trans_w(3.0) ⊗ accept_w(0.0) = 0.0 + 3.0 + 0.0 = 3.0
        assert!(
            result.approx_eq(&TropicalWeight::new(3.0), 1e-10),
            "weighted_run should accumulate tropical cost: expected 3.0, got {:?}",
            result
        );

        // Empty string: q0 is not accepting, should be zero (infinity).
        let empty_result = wvpa.weighted_run(&[]);
        assert!(
            empty_result.is_zero(),
            "weighted_run on empty string should be zero (q0 not accepting)"
        );

        // Unknown symbol: should be zero.
        let unknown_result = wvpa.weighted_run(&["unknown"]);
        assert!(
            unknown_result.is_zero(),
            "weighted_run on unknown symbol should be zero"
        );
    }

    #[test]
    fn weighted_run_tropical_call_return() {
        // Build a weighted VPA with call/return transitions carrying tropical weights.
        // q0 --(, push G, cost=1.0)--> q1 --), pop G, cost=2.0--> q2 (accepting)
        let alpha = VpaAlphabet::new(
            ["(".to_string()].into_iter().collect(),
            [")".to_string()].into_iter().collect(),
            HashSet::new(),
        );
        let mut wvpa: WeightedVpa<TropicalWeight> = WeightedVpa::new(alpha);
        let q0 = wvpa.add_state(Some("start".to_string()));
        let q1 = wvpa.add_state(Some("called".to_string()));
        let q2 = wvpa.add_state(Some("accept".to_string()));
        wvpa.initial_states.insert(q0);
        wvpa.accepting_states.insert(q2);
        wvpa.initial_weights.insert(q0, TropicalWeight::one());
        wvpa.accepting_weights.insert(q2, TropicalWeight::one());

        wvpa.call_transitions.insert(
            (q0, "(".to_string()),
            vec![(q1, "G".to_string(), TropicalWeight::new(1.0))],
        );
        wvpa.return_transitions.insert(
            (q1, ")".to_string(), "G".to_string()),
            vec![(q2, TropicalWeight::new(2.0))],
        );

        let result = wvpa.weighted_run(&["(", ")"]);
        // 0.0 + 1.0 + 2.0 + 0.0 = 3.0
        assert!(
            result.approx_eq(&TropicalWeight::new(3.0), 1e-10),
            "weighted_run on () should be 3.0 (tropical), got {:?}",
            result
        );
    }

    #[test]
    fn weighted_determinize_tropical() {
        // Build a nondeterministic weighted VPA and determinize it.
        let alpha = VpaAlphabet::new(
            HashSet::new(),
            HashSet::new(),
            ["a".to_string()].into_iter().collect(),
        );
        let mut wvpa: WeightedVpa<TropicalWeight> = WeightedVpa::new(alpha);
        let q0 = wvpa.add_state(Some("init0".to_string()));
        let q1 = wvpa.add_state(Some("init1".to_string()));
        let q2 = wvpa.add_state(Some("accept0".to_string()));
        let q3 = wvpa.add_state(Some("accept1".to_string()));

        wvpa.initial_states.insert(q0);
        wvpa.initial_states.insert(q1);
        wvpa.accepting_states.insert(q2);
        wvpa.accepting_states.insert(q3);
        wvpa.initial_weights.insert(q0, TropicalWeight::one());
        wvpa.initial_weights.insert(q1, TropicalWeight::one());
        wvpa.accepting_weights.insert(q2, TropicalWeight::one());
        wvpa.accepting_weights.insert(q3, TropicalWeight::one());

        // q0 --a(cost=5.0)--> q2
        wvpa.internal_transitions.insert(
            (q0, "a".to_string()),
            vec![(q2, TropicalWeight::new(5.0))],
        );
        // q1 --a(cost=3.0)--> q3
        wvpa.internal_transitions.insert(
            (q1, "a".to_string()),
            vec![(q3, TropicalWeight::new(3.0))],
        );

        assert!(
            !wvpa.is_deterministic(),
            "nondeterministic weighted VPA should not be deterministic"
        );

        let det = wvpa.weighted_determinize();
        assert!(
            det.is_deterministic(),
            "weighted_determinize should produce a deterministic VPA"
        );

        // The determinized VPA should still recognize "a".
        let result = det.weighted_run(&["a"]);
        // Both paths contribute: min(5.0, 3.0) = 3.0 (tropical plus = min).
        assert!(
            !result.is_zero(),
            "determinized weighted VPA should accept 'a'"
        );
    }

    #[test]
    fn weighted_inclusion_boolean() {
        // For BooleanWeight, weighted_inclusion reduces to language inclusion.
        let well_matched = build_paren_vpa();
        let eps_only = build_epsilon_only_vpa();

        // eps_only ⊆ well_matched (epsilon is accepted by both).
        assert!(
            eps_only.weighted_inclusion(&well_matched),
            "epsilon-only language should be included in well-matched language"
        );

        // well_matched ⊄ eps_only (well_matched accepts "()" but eps_only does not).
        assert!(
            !well_matched.weighted_inclusion(&eps_only),
            "well-matched language should NOT be included in epsilon-only language"
        );
    }

    // ── Sprint A1: VPA nesting bound tests ──────────────────────────────────

    #[test]
    fn vpa_nesting_bound_equals_state_count() {
        // VPA with 3 call/return pairs → state_count states (start + nesting levels)
        let pairs = vec![
            ("(".to_string(), ")".to_string()),
            ("{".to_string(), "}".to_string()),
            ("[".to_string(), "]".to_string()),
        ];
        let internal = vec!["+".to_string(), "id".to_string()];
        let vpa = construct_vpa(&pairs, &internal);
        let state_count = vpa.num_states();

        let analysis = VpaAnalysis {
            is_determinizable: true,
            alphabet_mismatches: Vec::new(),
            state_count,
            max_nesting_bound: state_count,
        };
        assert_eq!(analysis.max_nesting_bound, state_count);
    }

    // ── VPA token grouping tests ─────────────────────────────────────────────

    fn test_range(byte_offset: usize) -> crate::runtime_types::Range {
        let pos = crate::runtime_types::Position {
            byte_offset,
            line: 1,
            column: byte_offset,
        };
        crate::runtime_types::Range {
            start: pos,
            end: pos,
            file_id: None,
        }
    }

    fn classify_test_token(tok: &str) -> SymbolKind {
        match tok {
            "(" | "{" | "[" => SymbolKind::Call,
            ")" | "}" | "]" => SymbolKind::Return,
            _ => SymbolKind::Internal,
        }
    }

    #[test]
    fn test_build_vpa_alphabet_from_modes() {
        use crate::{CustomTokenSpec, LexerModeSpec};

        let default_tokens = vec![
            CustomTokenSpec {
                name: "LParen".into(),
                pattern: "\\(".into(),
                category: None,
                payload_type: None,
                constructor_code: None,
                is_builtin_override: false,
                priority: 2,
                push_mode: Some("inner".into()),
                is_pop: false,
                stream: None,
            },
            CustomTokenSpec {
                name: "Plus".into(),
                pattern: "\\+".into(),
                category: None,
                payload_type: None,
                constructor_code: None,
                is_builtin_override: false,
                priority: 2,
                push_mode: None,
                is_pop: false,
                stream: None,
            },
        ];
        let modes = vec![LexerModeSpec {
            name: "inner".into(),
            token_specs: vec![CustomTokenSpec {
                name: "RParen".into(),
                pattern: "\\)".into(),
                category: None,
                payload_type: None,
                constructor_code: None,
                is_builtin_override: false,
                priority: 2,
                push_mode: None,
                is_pop: true,
                stream: None,
            }],
        }];

        let alphabet = build_vpa_alphabet_from_modes(&default_tokens, &modes);
        assert!(
            alphabet.call_symbols.contains("LParen"),
            "LParen with push_mode should be a call symbol"
        );
        assert!(
            alphabet.return_symbols.contains("RParen"),
            "RParen with is_pop should be a return symbol"
        );
        assert!(
            alphabet.internal_symbols.contains("Plus"),
            "Plus (no push/pop) should be an internal symbol"
        );
        assert!(
            !alphabet.call_symbols.contains("Plus"),
            "Plus should not appear in call symbols"
        );
        assert!(
            !alphabet.return_symbols.contains("Plus"),
            "Plus should not appear in return symbols"
        );
    }

    #[test]
    fn test_skip_table_simple() {
        // Token stream: ( a + b )
        let tokens: Vec<(&str, _)> = vec![
            ("(", test_range(0)),
            ("a", test_range(1)),
            ("+", test_range(2)),
            ("b", test_range(3)),
            (")", test_range(4)),
        ];

        let table = build_skip_table(&tokens, |tok| classify_test_token(tok));

        assert_eq!(
            table[0],
            Some(4),
            "opener at 0 should match closer at 4"
        );
        assert_eq!(table[1], None, "leaf 'a' should have no skip");
        assert_eq!(table[2], None, "leaf '+' should have no skip");
        assert_eq!(table[3], None, "leaf 'b' should have no skip");
        assert_eq!(table[4], None, "closer ')' should have no skip entry");
    }

    #[test]
    fn test_skip_table_nested() {
        // Token stream: ( ( a ) )
        let tokens: Vec<(&str, _)> = vec![
            ("(", test_range(0)),
            ("(", test_range(1)),
            ("a", test_range(2)),
            (")", test_range(3)),
            (")", test_range(4)),
        ];

        let table = build_skip_table(&tokens, |tok| classify_test_token(tok));

        assert_eq!(
            table[0],
            Some(4),
            "outer opener at 0 should match outer closer at 4"
        );
        assert_eq!(
            table[1],
            Some(3),
            "inner opener at 1 should match inner closer at 3"
        );
        assert_eq!(table[2], None, "leaf 'a' should have no skip");
        assert_eq!(table[3], None, "closer at 3 should have no skip entry");
        assert_eq!(table[4], None, "closer at 4 should have no skip entry");
    }

    #[test]
    fn test_skip_table_unbalanced() {
        // Token stream: ( a ( b — two unmatched openers
        let tokens: Vec<(&str, _)> = vec![
            ("(", test_range(0)),
            ("a", test_range(1)),
            ("(", test_range(2)),
            ("b", test_range(3)),
        ];

        let table = build_skip_table(&tokens, |tok| classify_test_token(tok));

        assert_eq!(
            table[0], None,
            "unmatched opener at 0 should be None"
        );
        assert_eq!(table[1], None, "leaf 'a' should have no skip");
        assert_eq!(
            table[2], None,
            "unmatched opener at 2 should be None"
        );
        assert_eq!(table[3], None, "leaf 'b' should have no skip");
    }

    #[test]
    fn test_token_tree_simple() {
        // Token stream: ( a + b )
        let tokens: Vec<(&str, _)> = vec![
            ("(", test_range(0)),
            ("a", test_range(1)),
            ("+", test_range(2)),
            ("b", test_range(3)),
            (")", test_range(4)),
        ];
        let table = build_skip_table(&tokens, |tok| classify_test_token(tok));
        let tree = build_token_tree(&tokens, &table, |tok| classify_test_token(tok));

        assert_eq!(tree.len(), 1, "should produce exactly 1 top-level Group");
        match &tree[0] {
            TokenTree::Group {
                open,
                close,
                children,
            } => {
                assert_eq!(open.0, "(", "group opener should be '('");
                assert_eq!(close.0, ")", "group closer should be ')'");
                assert_eq!(children.len(), 3, "group should contain 3 children: a, +, b");
                // Verify all children are leaf tokens
                for (i, child) in children.iter().enumerate() {
                    match child {
                        TokenTree::Token(tok, _) => {
                            let expected = ["a", "+", "b"][i];
                            assert_eq!(
                                *tok, expected,
                                "child {i} should be '{expected}'"
                            );
                        }
                        TokenTree::Group { .. } => {
                            panic!("child {i} should be a Token, not a Group");
                        }
                    }
                }
            }
            TokenTree::Token(_, _) => panic!("expected a Group, got a Token"),
        }
    }

    #[test]
    fn test_token_tree_nested() {
        // Token stream: ( ( a ) b )
        let tokens: Vec<(&str, _)> = vec![
            ("(", test_range(0)),
            ("(", test_range(1)),
            ("a", test_range(2)),
            (")", test_range(3)),
            ("b", test_range(4)),
            (")", test_range(5)),
        ];
        let table = build_skip_table(&tokens, |tok| classify_test_token(tok));
        let tree = build_token_tree(&tokens, &table, |tok| classify_test_token(tok));

        assert_eq!(tree.len(), 1, "should produce exactly 1 top-level Group");
        match &tree[0] {
            TokenTree::Group {
                open,
                close,
                children,
            } => {
                assert_eq!(open.0, "(");
                assert_eq!(close.0, ")");
                assert_eq!(
                    children.len(),
                    2,
                    "outer group should contain 2 children: inner Group and leaf 'b'"
                );

                // First child: nested Group([a])
                match &children[0] {
                    TokenTree::Group {
                        open: inner_open,
                        close: inner_close,
                        children: inner_children,
                    } => {
                        assert_eq!(inner_open.0, "(");
                        assert_eq!(inner_close.0, ")");
                        assert_eq!(
                            inner_children.len(),
                            1,
                            "inner group should contain 1 child: 'a'"
                        );
                        match &inner_children[0] {
                            TokenTree::Token(tok, _) => assert_eq!(*tok, "a"),
                            TokenTree::Group { .. } => {
                                panic!("inner child should be Token 'a'");
                            }
                        }
                    }
                    TokenTree::Token(_, _) => {
                        panic!("first child of outer group should be a nested Group");
                    }
                }

                // Second child: leaf "b"
                match &children[1] {
                    TokenTree::Token(tok, _) => assert_eq!(*tok, "b"),
                    TokenTree::Group { .. } => {
                        panic!("second child of outer group should be leaf 'b'");
                    }
                }
            }
            TokenTree::Token(_, _) => panic!("expected a Group, got a Token"),
        }
    }

    #[test]
    fn test_token_tree_unmatched_opener() {
        // Token stream: ( a b — unmatched opener is demoted to leaf Token
        let tokens: Vec<(&str, _)> = vec![
            ("(", test_range(0)),
            ("a", test_range(1)),
            ("b", test_range(2)),
        ];
        let table = build_skip_table(&tokens, |tok| classify_test_token(tok));
        let tree = build_token_tree(&tokens, &table, |tok| classify_test_token(tok));

        assert_eq!(
            tree.len(),
            3,
            "unmatched opener should produce 3 leaf tokens"
        );
        // All nodes should be leaf tokens since the opener is unmatched
        for (i, node) in tree.iter().enumerate() {
            match node {
                TokenTree::Token(tok, _) => {
                    let expected = ["(", "a", "b"][i];
                    assert_eq!(
                        *tok, expected,
                        "leaf {i} should be '{expected}'"
                    );
                }
                TokenTree::Group { .. } => {
                    panic!("node {i} should be a demoted leaf Token, not a Group");
                }
            }
        }
    }
}
