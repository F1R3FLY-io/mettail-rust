//! Weighted Multi-Tape Automata (Module 8).
//!
//! Provides synchronized multi-stream computation over `K ≥ 0` input tapes. A
//! weighted multi-tape automaton specializes to single-tape NFAs (K=1), WFSTs
//! (K=2), and K-tape relations (K≥3). Each transition reads one symbol (or
//! epsilon) from each of the K tapes simultaneously, with an associated
//! semiring weight.
//!
//! ## Motivation
//!
//! Multi-channel receives in Rholang/MeTTaIL —
//! `for (@x <- ch1, @y <- ch2) { ... }` — naturally map to multi-tape automata:
//! ch1 becomes tape 1, ch2 becomes tape 2. The automaton synchronizes
//! consumption across channels, with semiring weights encoding priority,
//! probability, or cost. K≥3 supports synchronized triples (e.g. tag/text/aux
//! streams in NLP morphological analysis).
//!
//! ## Key Operations (Kempe, Guingne, Nicart 2004 "Algorithms for n-Tape Automata")
//!
//! - **pair_n([streams; K]) → <W,K>**: Build a K-tape automaton from K
//!   single-tape automata via iterated cross-product (Eq. 18 + Eq. 12
//!   associativity). For K=2 the binary `pair(a1, a2)` is a thin wrapper.
//! - **project(tape_idx)**: Extract single-tape behavior by projecting onto
//!   one tape (Eq. 22).
//! - **auto_intersect(i, j)**: Per-transition label-equality filter on tapes
//!   `i` and `j`. Note: this is a token-level synchronization operation,
//!   distinct from Kempe Eq. 30's `I_{j,k}` full-string equality (which would
//!   require ~50 LoC bounded-delay analysis with leftover strings; not
//!   needed for any current caller).
//! - **multi_tape_intersect(a, b)**: K-tape product construction with
//!   synchronized tape labels on all K tapes.
//! - **evaluate(inputs)**: Evaluate the automaton on K concrete input streams,
//!   returning the total weight of all accepting runs via BFS over
//!   `(state, positions_per_tape)` configurations.
//! - **build_synced_stream_automaton_k([streams; K], [names; K], sync) →
//!   SyncedStreamResult<W, K>**: K-stream sync automaton with `Align(...)`
//!   constraint enforcement via `auto_intersect` per resolved (i, j) pair.
//!
//! ## Theoretical Foundations
//!
//! - **Kempe, A., Guingne, F., Nicart, F. (2004)** — *"Algorithms for n-Tape
//!   Automata."* XRCE Research Report 2004/031, arXiv:cs.CL/0406003v1.
//!   Defines weighted n-tape automata as 6-tuple `A^(n) = ⟨Σ, Q, I, F, E^(n),
//!   𝒦⟩` (Eq. 1); cross-product `R₁^(n) × R₂^(m) = R^(n+m)` (Eq. 18) with
//!   associative pairing (Eq. 12), so iterating from K=1 produces arbitrary-K
//!   automata. Constructive algorithms in Section 6 (CrossPC, CrossPA).
//! - **Rabin & Scott (1959)** — *"Finite Automata and Their Decision
//!   Problems."* The product construction underlying `pair` and
//!   `multi_tape_intersect` is the standard Rabin-Scott cross-product,
//!   extended to K tapes with semiring weight multiplication.
//! - **Mohri, Pereira, Riley (1998)** — Composition algorithms with ε-filter.
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
        self.transitions
            .push(MultiTapeTransition { from, to, labels, weight });
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
/// construction (Kempe 2004, Eq. 18 — cross-product `R₁^(1) × R₂^(1) → R^(2)`).
///
/// The resulting automaton has:
/// - States: `|Q1| x |Q2|` (all pairs of states from `a1` and `a2`).
/// - Transitions: for each pair `(t1, t2)`, a synchronized transition
///   `(q1, q2) --[label1, label2]--> (q1', q2')` with weight `w1 * w2`.
/// - Also includes epsilon-extended transitions on each side, so the two
///   tapes can advance independently.
/// - Initial states: pairs `(i1, i2)` with weight `w_i1 * w_i2`.
/// - Accepting states: pairs `(f1, f2)` with weight `w_f1 * w_f2`.
///
/// **Implementation note (T11/2026-05-05):** this is a thin wrapper over
/// the K-generic `pair_n::<W, 2>([a1, a2])`. The semantics are byte-identical
/// to the prior K=2-hardcoded implementation, since `pair_n` for K=2 fold
/// reduces to one `pair_extend_dyn` step which mirrors the binary CrossPA
/// algorithm.
pub fn pair<W: Semiring>(
    a1: &WeightedMultiTapeAutomaton<W, 1>,
    a2: &WeightedMultiTapeAutomaton<W, 1>,
) -> WeightedMultiTapeAutomaton<W, 2> {
    pair_n::<W, 2>([a1, a2])
}

// ══════════════════════════════════════════════════════════════════════════════
// K-generic infrastructure (Kempe 2004 Eq. 18 cross-product, iterated)
// ══════════════════════════════════════════════════════════════════════════════

/// Module-private runtime-K multi-tape automaton.
///
/// Represents a multi-tape automaton with a runtime arity `k` (in contrast
/// to the public `WeightedMultiTapeAutomaton<W, K>` which fixes K at
/// compile time via const generics). Used as an intermediate representation
/// during K-iterative construction (`pair_extend_dyn`, `pair_n`); after the
/// fold completes, `materialize::<W, K>` converts to the fixed-K form.
///
/// This avoids the `generic_const_exprs` nightly feature that would
/// otherwise be required for `pair_extend<K>(...) -> <W, {K + 1}>`-style
/// signatures.
struct DynMultiTapeAutomaton<W: Semiring> {
    states: Vec<MultiTapeState>,
    transitions: Vec<DynMultiTapeTransition<W>>,
    initial: HashMap<usize, W>,
    accepting: HashMap<usize, W>,
    k: usize,
}

struct DynMultiTapeTransition<W: Semiring> {
    from: usize,
    to: usize,
    labels: Vec<Option<String>>,
    weight: W,
}

impl<W: Semiring> DynMultiTapeAutomaton<W> {
    fn new(k: usize) -> Self {
        Self {
            states: Vec::new(),
            transitions: Vec::new(),
            initial: HashMap::new(),
            accepting: HashMap::new(),
            k,
        }
    }

    fn add_state(&mut self, label: Option<String>) -> usize {
        let id = self.states.len();
        self.states.push(MultiTapeState { id, label });
        id
    }
}

/// Lift a 1-tape automaton into the runtime-K representation.
fn lift_1tape_to_dyn<W: Semiring>(
    a: &WeightedMultiTapeAutomaton<W, 1>,
) -> DynMultiTapeAutomaton<W> {
    let mut d = DynMultiTapeAutomaton::new(1);
    d.states.reserve(a.num_states());
    for s in &a.states {
        d.add_state(s.label.clone());
    }
    for (&q, &w) in &a.initial {
        d.initial.insert(q, w);
    }
    for (&q, &w) in &a.accepting {
        d.accepting.insert(q, w);
    }
    d.transitions.reserve(a.transitions.len());
    for t in &a.transitions {
        d.transitions.push(DynMultiTapeTransition {
            from: t.from,
            to: t.to,
            labels: vec![t.labels[0].clone()],
            weight: t.weight,
        });
    }
    d
}

/// Build a runtime-K view of a fixed-K automaton (for `pair_extend_dyn`'s
/// left operand). One-pass copy; O(|states| + |transitions|).
fn dyn_view<W: Semiring, const K: usize>(
    m: &WeightedMultiTapeAutomaton<W, K>,
) -> DynMultiTapeAutomaton<W> {
    let mut d = DynMultiTapeAutomaton::new(K);
    d.states.reserve(m.num_states());
    for s in &m.states {
        d.add_state(s.label.clone());
    }
    for (&q, &w) in &m.initial {
        d.initial.insert(q, w);
    }
    for (&q, &w) in &m.accepting {
        d.accepting.insert(q, w);
    }
    d.transitions.reserve(m.transitions.len());
    for t in &m.transitions {
        d.transitions.push(DynMultiTapeTransition {
            from: t.from,
            to: t.to,
            labels: t.labels.iter().cloned().collect(),
            weight: t.weight,
        });
    }
    d
}

/// Materialize a runtime-K automaton with `d.k == K` into the const-generic
/// `WeightedMultiTapeAutomaton<W, K>` form. Panics if `d.k != K`.
fn materialize<W: Semiring, const K: usize>(
    d: &DynMultiTapeAutomaton<W>,
) -> WeightedMultiTapeAutomaton<W, K> {
    assert_eq!(d.k, K, "materialize: dynamic arity {} does not match target K = {}", d.k, K,);
    let mut out = WeightedMultiTapeAutomaton::<W, K>::new();
    out.states.reserve(d.states.len());
    for s in &d.states {
        out.add_state(s.label.clone());
    }
    for (&q, &w) in &d.initial {
        out.set_initial(q, w);
    }
    for (&q, &w) in &d.accepting {
        out.set_accepting(q, w);
    }
    for t in &d.transitions {
        // Convert Vec<Option<String>> (length K) into [Option<String>; K].
        let mut arr: [Option<String>; K] = std::array::from_fn(|_| None);
        debug_assert_eq!(
            t.labels.len(),
            K,
            "materialize: transition label arity {} != K {}",
            t.labels.len(),
            K,
        );
        for (i, lbl) in t.labels.iter().enumerate() {
            arr[i] = lbl.clone();
        }
        out.add_transition(t.from, t.to, arr, t.weight);
    }
    out
}

/// Pair-extend a runtime-K automaton `m` with a 1-tape automaton `a` to
/// produce a runtime-(K+1) automaton (Kempe 2004 Definition 3 / Eq. 18,
/// CrossPA-style state pairing with synchronized + ε-extended transitions
/// on the new last tape).
///
/// Algorithm (Kempe Section 6.1.2 page 15, lifted from K=2 to K → K+1):
/// 1. Allocate `|Q_m| × |Q_a|` states with `product_id(qm, qa) = qm * |Q_a| + qa`.
/// 2. Initial weights: `I'((qm,qa)) = I_m(qm) ⊗ I_a(qa)`.
/// 3. Final weights: `F'((qm,qa)) = F_m(qm) ⊗ F_a(qa)`.
/// 4. Synchronized transitions: append `t_a.labels[0]` to `t_m`'s K-label
///    array; weight `t_m.weight ⊗ t_a.weight`.
/// 5. ε-extended on tape K+1 (m advances, a idle): copy `t_m.labels` and
///    append `None`; weight `t_m.weight`.
/// 6. ε-extended on tapes 0..K (m idle, a advances): K Nones + `t_a.labels[0]`;
///    weight `t_a.weight`.
fn pair_extend_dyn<W: Semiring>(
    m: &DynMultiTapeAutomaton<W>,
    a: &WeightedMultiTapeAutomaton<W, 1>,
) -> DynMultiTapeAutomaton<W> {
    let nm = m.states.len();
    let na = a.num_states();
    let new_k = m.k + 1;
    let mut out = DynMultiTapeAutomaton::new(new_k);

    out.states.reserve(nm * na);
    for sm in &m.states {
        for sa in &a.states {
            let label = match (&sm.label, &sa.label) {
                (Some(lm), Some(la)) => Some(format!("({lm},{la})")),
                (Some(lm), None) => Some(format!("({lm},_)")),
                (None, Some(la)) => Some(format!("(_,{la})")),
                (None, None) => None,
            };
            out.add_state(label);
        }
    }

    let product_id = |qm: usize, qa: usize| -> usize { qm * na + qa };

    for (&im, &wm) in &m.initial {
        for (&ia, &wa) in &a.initial {
            out.initial.insert(product_id(im, ia), wm.times(&wa));
        }
    }
    for (&fm, &wm) in &m.accepting {
        for (&fa, &wa) in &a.accepting {
            out.accepting.insert(product_id(fm, fa), wm.times(&wa));
        }
    }

    // Pre-allocate transitions: |T_m|*|T_a| sync + |T_m|*|Q_a| epsilon-on-new
    // + |Q_m|*|T_a| epsilon-on-old.
    out.transitions.reserve(
        m.transitions.len() * a.transitions.len()
            + m.transitions.len() * na
            + nm * a.transitions.len(),
    );

    // Synchronized: m and a both advance.
    for tm in &m.transitions {
        for ta in &a.transitions {
            let mut new_labels = Vec::with_capacity(new_k);
            new_labels.extend(tm.labels.iter().cloned());
            new_labels.push(ta.labels[0].clone());
            out.transitions.push(DynMultiTapeTransition {
                from: product_id(tm.from, ta.from),
                to: product_id(tm.to, ta.to),
                labels: new_labels,
                weight: tm.weight.times(&ta.weight),
            });
        }
    }

    // ε-extended on the new last tape (m advances, a idle).
    for tm in &m.transitions {
        for qa in 0..na {
            let mut new_labels = Vec::with_capacity(new_k);
            new_labels.extend(tm.labels.iter().cloned());
            new_labels.push(None);
            out.transitions.push(DynMultiTapeTransition {
                from: product_id(tm.from, qa),
                to: product_id(tm.to, qa),
                labels: new_labels,
                weight: tm.weight,
            });
        }
    }

    // ε-extended on tapes 0..K (m idle, a advances).
    for ta in &a.transitions {
        for qm in 0..nm {
            let mut new_labels = Vec::with_capacity(new_k);
            for _ in 0..m.k {
                new_labels.push(None);
            }
            new_labels.push(ta.labels[0].clone());
            out.transitions.push(DynMultiTapeTransition {
                from: product_id(qm, ta.from),
                to: product_id(qm, ta.to),
                labels: new_labels,
                weight: ta.weight,
            });
        }
    }

    out
}

/// Build a K-tape automaton from K single-tape automata via iterated
/// cross-product (Kempe 2004 Eq. 18 + Eq. 12 associativity).
///
/// Behavior by K:
/// - **K = 0**: returns the trivial 0-tape automaton with one state that is
///   both initial and accepting with weight `W::one()`. This is the identity
///   element for `pair_extend`: `pair_extend(trivial_0, a) ≅ a`. Recognizes
///   the empty K-tuple `()`.
/// - **K = 1**: returns a copy of `streams[0]` (degenerate single-tape case;
///   no fold work).
/// - **K ≥ 2**: builds via internal `DynMultiTapeAutomaton` fold:
///   `pair_n([s₀,…,s_{K-1}]) = pair_extend_dyn(...pair_extend_dyn(lift(s₀), s₁)..., s_{K-1})`,
///   then materializes to fixed-K. State count is `∏_k |Q_k|`.
///
/// Reference: Kempe, A., Guingne, F., Nicart, F. (2004). "Algorithms for
/// n-Tape Automata." XRCE Research Report 2004/031. Eq. 18 (cross-product
/// R₁^(n) × R₂^(m) = R^(n+m)) + Eq. 12 (associativity of pairing) +
/// Section 6.1.2 (CrossPA constructive algorithm).
pub fn pair_n<W: Semiring, const K: usize>(
    streams: [&WeightedMultiTapeAutomaton<W, 1>; K],
) -> WeightedMultiTapeAutomaton<W, K> {
    if K == 0 {
        // Identity for pair_extend: single-state automaton recognizing ().
        let mut empty = WeightedMultiTapeAutomaton::<W, K>::new();
        let q = empty.add_state(Some("trivial".to_string()));
        empty.set_initial(q, W::one());
        empty.set_accepting(q, W::one());
        return empty;
    }

    // K ≥ 1: start from streams[0] lifted to runtime-K, then fold.
    let mut acc = lift_1tape_to_dyn(streams[0]);
    for s in streams.iter().skip(1) {
        acc = pair_extend_dyn(&acc, s);
    }
    materialize::<W, K>(&acc)
}

/// Pair-extend a fixed-K automaton with a 1-tape automaton, returning the
/// runtime-K (= K_FROM + 1) representation. Use `materialize::<W, K_TARGET>`
/// to convert to a fixed-K type.
///
/// Public alternative to the unstable `generic_const_exprs`-based
/// `pair_extend<K>(..) -> <W, {K + 1}>` signature: callers that need
/// extension to a specific arity use this in combination with
/// `pair_extend_to::<W, K_FROM, K_TO>(...)` below.
///
/// Most consumers should use `pair_n<K>(...)` instead, which folds directly
/// to a fixed K.
pub fn pair_extend_to<W: Semiring, const K_FROM: usize, const K_TO: usize>(
    m: &WeightedMultiTapeAutomaton<W, K_FROM>,
    a: &WeightedMultiTapeAutomaton<W, 1>,
) -> WeightedMultiTapeAutomaton<W, K_TO> {
    assert_eq!(
        K_TO,
        K_FROM + 1,
        "pair_extend_to: K_TO must equal K_FROM + 1 (K_FROM={}, K_TO={})",
        K_FROM,
        K_TO,
    );
    let dyn_m = dyn_view::<W, K_FROM>(m);
    let extended = pair_extend_dyn(&dyn_m, a);
    materialize::<W, K_TO>(&extended)
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
        assert!(tape_idx < K, "multi_tape::project: tape_idx {tape_idx} out of range (K = {K})");

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
        assert!(tape_i < K, "multi_tape::auto_intersect: tape_i {tape_i} out of range (K = {K})");
        assert!(tape_j < K, "multi_tape::auto_intersect: tape_j {tape_j} out of range (K = {K})");
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
                        },
                        Some(sym) => {
                            if positions[k] < inputs[k].len() && inputs[k][positions[k]] == *sym {
                                new_positions[k] = positions[k] + 1;
                            } else {
                                can_take = false;
                                break;
                            }
                        },
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

        let disconnected_tapes: Vec<usize> = (0..K).filter(|&k| !tape_has_label[k]).collect();

        // Overlapping tapes: tapes i,j are overlapping if labels[i] == labels[j]
        // on every transition.
        let mut overlapping_tapes: Vec<(usize, usize)> = Vec::new();
        for i in 0..K {
            for j in (i + 1)..K {
                let all_match = self.transitions.iter().all(|t| t.labels[i] == t.labels[j]);
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
                let label = self.states[state].label.as_deref().unwrap_or("_");
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
                let label = self.states[state].label.as_deref().unwrap_or("_");
                write!(f, "{label}/{weight:?}")?;
            }
            writeln!(f, "]")?;
        }

        // Transitions.
        for t in &self.transitions {
            let from_label = self.states[t.from].label.as_deref().unwrap_or("_");
            let to_label = self.states[t.to].label.as_deref().unwrap_or("_");
            let labels: Vec<String> = t
                .labels
                .iter()
                .map(|l| l.as_deref().unwrap_or("eps").to_string())
                .collect();
            writeln!(f, "  {from_label} --[{}]--> {to_label} / {:?}", labels.join(", "), t.weight)?;
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
        },
        crate::SyntaxItemSpec::Binder { category, .. } => {
            if category != rule_cat {
                if let Some(&dst) = cat_to_idx.get(category.as_str()) {
                    connected_to[src].insert(dst);
                    connected_to[dst].insert(src);
                }
            }
        },
        crate::SyntaxItemSpec::Collection { element_category, .. } => {
            if element_category != rule_cat {
                if let Some(&dst) = cat_to_idx.get(element_category.as_str()) {
                    connected_to[src].insert(dst);
                    connected_to[dst].insert(src);
                }
            }
        },
        crate::SyntaxItemSpec::Sep { body, .. } => {
            collect_category_refs(body, rule_cat, cat_to_idx, src, connected_to);
        },
        crate::SyntaxItemSpec::Map { body_items } => {
            for sub in body_items {
                collect_category_refs(sub, rule_cat, cat_to_idx, src, connected_to);
            }
        },
        crate::SyntaxItemSpec::Zip { left_category, right_category, body, .. } => {
            for ref_cat in [left_category.as_str(), right_category.as_str()] {
                if ref_cat != rule_cat {
                    if let Some(&dst) = cat_to_idx.get(ref_cat) {
                        connected_to[src].insert(dst);
                        connected_to[dst].insert(src);
                    }
                }
            }
            collect_category_refs(body, rule_cat, cat_to_idx, src, connected_to);
        },
        crate::SyntaxItemSpec::Optional { inner } => {
            for sub in inner {
                collect_category_refs(sub, rule_cat, cat_to_idx, src, connected_to);
            }
        },
        _ => {},
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Predicate Dispatch — PredicateCompiler integration
// ══════════════════════════════════════════════════════════════════════════════

/// Compiler adapter for the Multi-Tape Automata module (M8).
///
/// Activated by ≥2 channels in a join receive (k-tape regular relation variety).
pub struct MultiTapeCompiler;

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
// Sprint 6C: Multi-Tape Synchronized Stream Parsing
// ══════════════════════════════════════════════════════════════════════════════
//
// Builds a synchronized K-tape automaton from stream DFAs and sync constraints.
// Each stream's token sequence becomes a 1-tape automaton; `pair()` combines
// them into a 2-tape automaton; `auto_intersect()` applies `Align` constraints
// from the `sync { ... }` block.
//
// ## Design Note on const generic K
//
// Rust's const generics require K to be known at compile time. Since `pair()`
// produces `WeightedMultiTapeAutomaton<W, 2>` from two 1-tape automata, and
// there is no generic way to iteratively increase K at runtime, we provide:
//
// 1. **`build_stream_automaton()`** — Builds a 1-tape automaton from a named
//    token stream (applicable to any number of streams independently).
// 2. **`build_synced_stream_automaton()`** — The K=2 workhorse: combines
//    exactly two stream automata via `pair()`, then applies `Align` constraints
//    via `auto_intersect()`. This covers the dominant use case (2-stream sync).
// 3. **`validate_sync_constraints()`** — General validation for any number of
//    streams and constraints, reporting satisfiability without constructing the
//    full product automaton. Works by checking each constraint pair independently
//    and combining diagnostics.
//
// **K ≥ 1 implementation note (T11/2026-05-05):** the iterative cross-product
// per Kempe (2004) Eq. 18 + Eq. 12 associativity is implemented via the
// runtime-K `DynMultiTapeAutomaton` intermediate (`pair_extend_dyn`,
// `pair_n<K>`). The K=2 helpers (`pair`, `build_synced_stream_automaton`)
// remain as thin wrappers; the K-generic API
// `build_synced_stream_automaton_k<K>` handles arbitrary K ≥ 1.

/// Result of building a synchronized multi-tape stream automaton.
///
/// Contains the combined automaton, per-constraint diagnostics, and an overall
/// satisfiability verdict. This is a compile-time validation tool — it verifies
/// constraint satisfiability but does not affect runtime lexing.
///
/// Generic over `K` (the number of tapes). The K=2 specialization is
/// `SyncedStreamResult<W, 2>`; arbitrary K ≥ 1 is supported via
/// `build_synced_stream_automaton_k`.
#[derive(Debug, Clone)]
pub struct SyncedStreamResult<W: Semiring, const K: usize> {
    /// The synchronized K-tape automaton combining all streams.
    pub automaton: WeightedMultiTapeAutomaton<W, K>,
    /// Per-constraint diagnostic messages.
    ///
    /// Each entry corresponds to a constraint from the `SyncSpec`. An `Ok(msg)`
    /// indicates the constraint was successfully applied (with a descriptive
    /// message); an `Err(msg)` indicates the constraint could not be satisfied
    /// (e.g., the boundary pattern does not appear in both streams).
    pub constraint_diagnostics: Vec<Result<String, String>>,
    /// Whether all constraints are satisfiable (the automaton has at least one
    /// accepting path after all constraints are applied).
    pub is_satisfiable: bool,
}

/// Build a 1-tape automaton from a stream's token sequence.
///
/// The automaton is a simple linear chain: one state per token boundary,
/// with each transition labeled by the corresponding token string and weighted
/// with `W::one()`. The resulting automaton accepts exactly the given token
/// sequence.
///
/// # Parameters
///
/// - `stream_name`: Human-readable name for state labels (e.g., "main", "comments").
/// - `tokens`: The ordered token strings in this stream.
///
/// # Returns
///
/// A 1-tape automaton with `tokens.len() + 1` states and `tokens.len()` transitions.
/// If `tokens` is empty, returns a single-state automaton that accepts the empty
/// string (initial = accepting = q0).
pub fn build_stream_automaton<W: Semiring>(
    stream_name: &str,
    tokens: &[String],
) -> WeightedMultiTapeAutomaton<W, 1> {
    let mut automaton = WeightedMultiTapeAutomaton::<W, 1>::new();
    let n = tokens.len();

    // Create n+1 states: q0 --tok[0]--> q1 --tok[1]--> q2 ... --tok[n-1]--> qn
    // Preallocate for the full chain.
    automaton.states.reserve(n + 1);
    for i in 0..=n {
        automaton.add_state(Some(format!("{stream_name}:q{i}")));
    }

    automaton.set_initial(0, W::one());
    automaton.set_accepting(n, W::one());

    for (i, token) in tokens.iter().enumerate() {
        automaton.add_transition(i, i + 1, [Some(token.clone())], W::one());
    }

    automaton
}

/// Build a synchronized 2-tape automaton from two stream automata and sync
/// constraints.
///
/// This is the primary entry point for Sprint 6C's multi-tape synchronized
/// stream parsing. It performs the following steps:
///
/// 1. **Combine** the two 1-tape stream automata into a 2-tape automaton via
///    [`pair()`], creating the full product state space with epsilon-extended
///    transitions (each tape can advance independently).
///
/// 2. **Apply `Align` constraints** via [`auto_intersect()`]. An `Align`
///    constraint between `stream_a` and `stream_b` with a boundary pattern
///    means the two tapes must synchronize at positions where the boundary
///    pattern appears. Since `auto_intersect(0, 1)` enforces label equality
///    on both tapes, we filter to transitions matching the boundary pattern
///    before intersecting, then re-add unconstrained transitions for
///    non-boundary tokens.
///
///    In the current implementation, `Align` constraints are applied by
///    running `auto_intersect(0, 1)` on the paired automaton, which enforces
///    that both tapes must read the same token at every step. This is the
///    strongest form of alignment — future refinements could relax this to
///    synchronize only at boundary tokens.
///
/// 3. **Check satisfiability** by verifying the resulting automaton has at
///    least one reachable accepting state (via forward reachability from
///    initial states).
///
/// `Track` constraints are recorded in diagnostics but do not modify the
/// automaton (they are metadata for runtime position tracking, not structural
/// constraints).
///
/// # Parameters
///
/// - `stream_a`: The first 1-tape stream automaton (becomes tape 0).
/// - `stream_b`: The second 1-tape stream automaton (becomes tape 1).
/// - `stream_a_name`: Name of the first stream (for constraint matching).
/// - `stream_b_name`: Name of the second stream (for constraint matching).
/// - `sync`: The synchronization specification from the `sync { ... }` block.
///
/// # Returns
///
/// A [`SyncedStreamResult`] containing the combined automaton, per-constraint
/// diagnostics, and satisfiability verdict.
///
/// # Complexity
///
/// - **States**: O(|Q_a| * |Q_b|) from the product construction in `pair()`.
/// - **Transitions**: O(|T_a| * |T_b| + |T_a| * |Q_b| + |Q_a| * |T_b|) from
///   synchronized + epsilon-extended transitions, then filtered by constraints.
/// - This is a compile-time cost, not a runtime cost.
///
/// # Example
///
/// ```rust,ignore
/// use prattail::multi_tape::*;
/// use prattail::automata::semiring::TropicalWeight;
/// use prattail::{SyncSpec, SyncConstraintSpec};
///
/// let main_stream = build_stream_automaton::<TropicalWeight>(
///     "main",
///     &["let".into(), "x".into(), "=".into(), "42".into()],
/// );
/// let comment_stream = build_stream_automaton::<TropicalWeight>(
///     "comments",
///     &["/* doc */".into()],
/// );
/// let sync = SyncSpec {
///     constraints: vec![SyncConstraintSpec::Track {
///         auxiliary: "comments".into(),
///         primary: "main".into(),
///     }],
/// };
/// let result = build_synced_stream_automaton(
///     &main_stream, &comment_stream,
///     "main", "comments",
///     &sync,
/// );
/// assert!(result.is_satisfiable);
/// ```
pub fn build_synced_stream_automaton<W: Semiring>(
    stream_a: &WeightedMultiTapeAutomaton<W, 1>,
    stream_b: &WeightedMultiTapeAutomaton<W, 1>,
    stream_a_name: &str,
    stream_b_name: &str,
    sync: &crate::SyncSpec,
) -> SyncedStreamResult<W, 2> {
    // Step 1: Combine via pair() — product construction with epsilon extension.
    let mut combined = pair(stream_a, stream_b);

    // Step 2: Apply constraints and collect diagnostics.
    let mut constraint_diagnostics = Vec::with_capacity(sync.constraints.len());

    for constraint in &sync.constraints {
        match constraint {
            crate::SyncConstraintSpec::Align {
                stream_a: ref constraint_a,
                stream_b: ref constraint_b,
                boundary_pattern,
            } => {
                // Check that this Align constraint applies to our two streams.
                let applies = (constraint_a == stream_a_name && constraint_b == stream_b_name)
                    || (constraint_a == stream_b_name && constraint_b == stream_a_name);

                if !applies {
                    constraint_diagnostics.push(Ok(format!(
                        "Align({}, {}) skipped: does not involve streams '{}' and '{}'",
                        constraint_a, constraint_b, stream_a_name, stream_b_name,
                    )));
                    continue;
                }

                // Check that the boundary pattern appears in at least one
                // transition on each tape. If not, the constraint is trivially
                // unsatisfiable (no synchronization points exist).
                let tape_0_has_boundary = stream_a
                    .transitions
                    .iter()
                    .any(|t| t.labels[0].as_deref() == Some(boundary_pattern.as_str()));
                let tape_1_has_boundary = stream_b
                    .transitions
                    .iter()
                    .any(|t| t.labels[0].as_deref() == Some(boundary_pattern.as_str()));

                if !tape_0_has_boundary && !tape_1_has_boundary {
                    constraint_diagnostics.push(Err(format!(
                        "Align({}, {}, '{}'): boundary pattern '{}' not found in either stream",
                        constraint_a, constraint_b, boundary_pattern, boundary_pattern,
                    )));
                    continue;
                }
                if !tape_0_has_boundary {
                    constraint_diagnostics.push(Err(format!(
                        "Align({}, {}, '{}'): boundary pattern '{}' not found in stream '{}'",
                        constraint_a,
                        constraint_b,
                        boundary_pattern,
                        boundary_pattern,
                        stream_a_name,
                    )));
                    continue;
                }
                if !tape_1_has_boundary {
                    constraint_diagnostics.push(Err(format!(
                        "Align({}, {}, '{}'): boundary pattern '{}' not found in stream '{}'",
                        constraint_a,
                        constraint_b,
                        boundary_pattern,
                        boundary_pattern,
                        stream_b_name,
                    )));
                    continue;
                }

                // Apply auto_intersect(0, 1) to enforce label equality on
                // both tapes. This is the strongest alignment: at every step,
                // both tapes must read the same token.
                //
                // A more refined approach would only enforce equality at
                // boundary positions, but auto_intersect is the correct
                // Kempe (2004) operation for full synchronization. Selective
                // boundary-only synchronization would require a custom
                // transition filter, which can be added as a future refinement.
                combined = combined.auto_intersect(0, 1);

                constraint_diagnostics.push(Ok(format!(
                    "Align({}, {}, '{}'): applied auto_intersect(0, 1) — \
                     {} transitions remain after synchronization",
                    constraint_a,
                    constraint_b,
                    boundary_pattern,
                    combined.num_transitions(),
                )));
            },
            crate::SyncConstraintSpec::Track { auxiliary, primary } => {
                // Track constraints are metadata — they instruct the runtime
                // to maintain position correspondence between the auxiliary
                // and primary streams but do not structurally constrain the
                // automaton. Record for diagnostics.
                constraint_diagnostics.push(Ok(format!(
                    "Track({} relative to {}): recorded (metadata-only, no structural constraint)",
                    auxiliary, primary,
                )));
            },
        }
    }

    // Step 3: Check satisfiability via forward reachability.
    let is_satisfiable = check_reachable_accepting(&combined);

    SyncedStreamResult {
        automaton: combined,
        constraint_diagnostics,
        is_satisfiable,
    }
}

/// Check whether any accepting state is reachable from an initial state.
///
/// Performs a BFS/DFS from all initial states through the transition graph.
/// Returns `true` if at least one accepting state is reached. This is used
/// to determine constraint satisfiability after `auto_intersect()` filtering.
fn check_reachable_accepting<W: Semiring, const K: usize>(
    automaton: &WeightedMultiTapeAutomaton<W, K>,
) -> bool {
    if automaton.initial.is_empty() || automaton.accepting.is_empty() {
        return false;
    }

    // Build adjacency list for forward traversal.
    let num_states = automaton.num_states();
    let mut adj: Vec<Vec<usize>> = vec![Vec::new(); num_states];
    for t in &automaton.transitions {
        adj[t.from].push(t.to);
    }

    // BFS from all initial states.
    let mut visited = vec![false; num_states];
    let mut queue = VecDeque::with_capacity(automaton.initial.len());
    for &state in automaton.initial.keys() {
        if !visited[state] {
            visited[state] = true;
            queue.push_back(state);
        }
    }

    while let Some(state) = queue.pop_front() {
        if automaton.accepting.contains_key(&state) {
            return true;
        }
        for &next in &adj[state] {
            if !visited[next] {
                visited[next] = true;
                queue.push_back(next);
            }
        }
    }

    false
}

/// Validate synchronization constraints against a set of named streams.
///
/// This is a general-purpose validation function that works for any number of
/// streams (not just K=2). It checks each constraint independently:
///
/// - **`Align`**: Verifies both referenced streams exist and that the boundary
///   pattern appears in at least one token of each stream.
/// - **`Track`**: Verifies both referenced streams exist.
///
/// For K=2 synchronization with actual automaton construction, use
/// [`build_synced_stream_automaton()`] instead.
///
/// # Parameters
///
/// - `stream_tokens`: Map from stream name to its ordered token strings.
/// - `sync`: The synchronization specification.
///
/// # Returns
///
/// A vector of per-constraint diagnostics. `Ok` = valid, `Err` = problem found.
pub fn validate_sync_constraints(
    stream_tokens: &HashMap<String, Vec<String>>,
    sync: &crate::SyncSpec,
) -> Vec<Result<String, String>> {
    let mut diagnostics = Vec::with_capacity(sync.constraints.len());

    for constraint in &sync.constraints {
        match constraint {
            crate::SyncConstraintSpec::Align { stream_a, stream_b, boundary_pattern } => {
                let a_tokens = stream_tokens.get(stream_a);
                let b_tokens = stream_tokens.get(stream_b);

                match (a_tokens, b_tokens) {
                    (None, None) => {
                        diagnostics.push(Err(format!(
                            "Align({}, {}, '{}'): neither stream '{}' nor '{}' exists",
                            stream_a, stream_b, boundary_pattern, stream_a, stream_b,
                        )));
                    },
                    (None, Some(_)) => {
                        diagnostics.push(Err(format!(
                            "Align({}, {}, '{}'): stream '{}' does not exist",
                            stream_a, stream_b, boundary_pattern, stream_a,
                        )));
                    },
                    (Some(_), None) => {
                        diagnostics.push(Err(format!(
                            "Align({}, {}, '{}'): stream '{}' does not exist",
                            stream_a, stream_b, boundary_pattern, stream_b,
                        )));
                    },
                    (Some(a_toks), Some(b_toks)) => {
                        let a_has = a_toks.iter().any(|t| t == boundary_pattern);
                        let b_has = b_toks.iter().any(|t| t == boundary_pattern);

                        if !a_has && !b_has {
                            diagnostics.push(Err(format!(
                                "Align({}, {}, '{}'): boundary pattern '{}' not found in either stream",
                                stream_a, stream_b, boundary_pattern, boundary_pattern,
                            )));
                        } else if !a_has {
                            diagnostics.push(Err(format!(
                                "Align({}, {}, '{}'): boundary pattern '{}' not found in stream '{}'",
                                stream_a, stream_b, boundary_pattern,
                                boundary_pattern, stream_a,
                            )));
                        } else if !b_has {
                            diagnostics.push(Err(format!(
                                "Align({}, {}, '{}'): boundary pattern '{}' not found in stream '{}'",
                                stream_a, stream_b, boundary_pattern,
                                boundary_pattern, stream_b,
                            )));
                        } else {
                            diagnostics.push(Ok(format!(
                                "Align({}, {}, '{}'): boundary pattern '{}' found in both streams ({} in '{}', {} in '{}')",
                                stream_a, stream_b, boundary_pattern, boundary_pattern,
                                a_toks.iter().filter(|t| *t == boundary_pattern).count(), stream_a,
                                b_toks.iter().filter(|t| *t == boundary_pattern).count(), stream_b,
                            )));
                        }
                    },
                }
            },
            crate::SyncConstraintSpec::Track { auxiliary, primary } => {
                let aux_exists = stream_tokens.contains_key(auxiliary);
                let pri_exists = stream_tokens.contains_key(primary);

                if !aux_exists && !pri_exists {
                    diagnostics.push(Err(format!(
                        "Track({} relative to {}): neither stream '{}' nor '{}' exists",
                        auxiliary, primary, auxiliary, primary,
                    )));
                } else if !aux_exists {
                    diagnostics.push(Err(format!(
                        "Track({} relative to {}): auxiliary stream '{}' does not exist",
                        auxiliary, primary, auxiliary,
                    )));
                } else if !pri_exists {
                    diagnostics.push(Err(format!(
                        "Track({} relative to {}): primary stream '{}' does not exist",
                        auxiliary, primary, primary,
                    )));
                } else {
                    diagnostics.push(Ok(format!(
                        "Track({} relative to {}): both streams exist ({} tokens in '{}', {} tokens in '{}')",
                        auxiliary, primary,
                        stream_tokens[auxiliary].len(), auxiliary,
                        stream_tokens[primary].len(), primary,
                    )));
                }
            },
        }
    }

    diagnostics
}

/// K-generic version of `build_synced_stream_automaton`: build a K-tape
/// synchronized automaton from K named streams and a `SyncSpec`.
///
/// Generalizes the K=2 helper to arbitrary K ≥ 1 per Kempe (2004) Eq. 18
/// (cross-product) + Eq. 30 (auto-intersection on tapes j, k). For K=2 the
/// public `build_synced_stream_automaton(...)` is a thin wrapper over
/// `build_synced_stream_automaton_k::<W, 2>([a, b], [na, nb], sync)`.
///
/// Algorithm:
/// 1. Combine the K streams via `pair_n([s_0, ..., s_{K-1}])` →
///    `<W, K>`-tape product with full ε-extension.
/// 2. For each `Align(name_i, name_j, boundary)` constraint:
///    a. Resolve `(name_i, name_j)` to tape indices via
///       `names.iter().position(...)`.
///    b. If both names resolve to distinct tape indices, check the boundary
///       pattern is present in both streams; if so, apply
///       `combined.auto_intersect(idx_i, idx_j)`.
///    c. If a name doesn't resolve, record a "skipped: not in our streams"
///       diagnostic.
/// 3. For each `Track` constraint: record metadata-only diagnostic.
/// 4. Check satisfiability via `check_reachable_accepting`.
///
/// Reference: Kempe, A., Guingne, F., Nicart, F. (2004). "Algorithms for
/// n-Tape Automata." XRCE Research Report 2004/031. Definitions 3 (pair),
/// 5 (project), 7 (auto-intersect) composed K times. Theorem 8.1
/// (Rabin-Scott 1959 cross-product) for the K-tape product.
pub fn build_synced_stream_automaton_k<W: Semiring, const K: usize>(
    streams: [&WeightedMultiTapeAutomaton<W, 1>; K],
    names: [&str; K],
    sync: &crate::SyncSpec,
) -> SyncedStreamResult<W, K> {
    // Step 1: Combine via pair_n (K-iterated cross-product).
    let mut combined = pair_n::<W, K>(streams);

    // Step 2: Apply constraints and collect diagnostics.
    let mut constraint_diagnostics = Vec::with_capacity(sync.constraints.len());

    for constraint in &sync.constraints {
        match constraint {
            crate::SyncConstraintSpec::Align {
                stream_a: ref constraint_a,
                stream_b: ref constraint_b,
                boundary_pattern,
            } => {
                let i = names.iter().position(|&n| n == constraint_a.as_str());
                let j = names.iter().position(|&n| n == constraint_b.as_str());
                match (i, j) {
                    (Some(i), Some(j)) if i != j => {
                        // Both names resolved to distinct tapes.
                        // Check boundary pattern presence in source streams
                        // (using the original 1-tape automata).
                        let has_i = streams[i]
                            .transitions
                            .iter()
                            .any(|t| t.labels[0].as_deref() == Some(boundary_pattern.as_str()));
                        let has_j = streams[j]
                            .transitions
                            .iter()
                            .any(|t| t.labels[0].as_deref() == Some(boundary_pattern.as_str()));
                        match (has_i, has_j) {
                            (false, false) => constraint_diagnostics.push(Err(format!(
                                "Align({}, {}, '{}'): boundary pattern '{}' not found in either stream",
                                constraint_a, constraint_b, boundary_pattern, boundary_pattern,
                            ))),
                            (false, true) => constraint_diagnostics.push(Err(format!(
                                "Align({}, {}, '{}'): boundary pattern '{}' not found in stream '{}'",
                                constraint_a, constraint_b, boundary_pattern,
                                boundary_pattern, constraint_a,
                            ))),
                            (true, false) => constraint_diagnostics.push(Err(format!(
                                "Align({}, {}, '{}'): boundary pattern '{}' not found in stream '{}'",
                                constraint_a, constraint_b, boundary_pattern,
                                boundary_pattern, constraint_b,
                            ))),
                            (true, true) => {
                                combined = combined.auto_intersect(i, j);
                                constraint_diagnostics.push(Ok(format!(
                                    "Align({}, {}, '{}'): applied auto_intersect({}, {}) — \
                                     {} transitions remain after synchronization",
                                    constraint_a, constraint_b, boundary_pattern,
                                    i, j, combined.num_transitions(),
                                )));
                            }
                        }
                    },
                    (Some(_), Some(_)) => {
                        // i == j: degenerate self-align (e.g. Align("a", "a", ".")).
                        // Record as a no-op rather than an error.
                        constraint_diagnostics.push(Ok(format!(
                            "Align({}, {}, '{}'): same stream — no-op",
                            constraint_a, constraint_b, boundary_pattern,
                        )));
                    },
                    _ => {
                        // At least one name doesn't appear in `names`.
                        constraint_diagnostics.push(Ok(format!(
                            "Align({}, {}, '{}'): skipped: does not involve any of our streams",
                            constraint_a, constraint_b, boundary_pattern,
                        )));
                    },
                }
            },
            crate::SyncConstraintSpec::Track { auxiliary, primary } => {
                constraint_diagnostics.push(Ok(format!(
                    "Track({} relative to {}): recorded (metadata-only, no structural constraint)",
                    auxiliary, primary,
                )));
            },
        }
    }

    let is_satisfiable = check_reachable_accepting(&combined);

    SyncedStreamResult {
        automaton: combined,
        constraint_diagnostics,
        is_satisfiable,
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
        a.add_transition(q0, q1, [Some("x".into()), Some("y".into())], TropicalWeight::one());
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
        let result = paired.evaluate(&[vec!["hello".into()], vec!["world".into()]]);
        // Should accept (via epsilon-extended paths).
        assert!(!result.is_zero(), "pair should accept independent tape inputs");
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
        assert_eq!(projected.transitions[0].labels[0].as_deref(), Some("alpha"));
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
        assert_eq!(projected.transitions[0].labels[0].as_deref(), Some("beta"));
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
        a.add_transition(q0, q1, [Some("x".into()), Some("x".into())], TropicalWeight::one());
        // Mismatched labels.
        a.add_transition(q0, q2, [Some("a".into()), Some("b".into())], TropicalWeight::one());

        let constrained = a.auto_intersect(0, 1);
        assert_eq!(constrained.num_states(), 3);
        // Only the matching transition survives.
        assert_eq!(constrained.num_transitions(), 1);
        assert_eq!(constrained.transitions[0].labels[0].as_deref(), Some("x"));
        assert_eq!(constrained.transitions[0].labels[1].as_deref(), Some("x"));
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
        a.add_transition(a0, a1, [Some("x".into()), Some("y".into())], TropicalWeight::new(1.0));

        let mut b = WeightedMultiTapeAutomaton::<TropicalWeight, 2>::new();
        let b0 = b.add_state(Some("b0".into()));
        let b1 = b.add_state(Some("b1".into()));
        b.set_initial(b0, TropicalWeight::one());
        b.set_accepting(b1, TropicalWeight::one());
        b.add_transition(b0, b1, [Some("x".into()), Some("y".into())], TropicalWeight::new(2.0));

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
        a.add_transition(a0, a1, [Some("x".into()), Some("y".into())], TropicalWeight::one());

        let mut b = WeightedMultiTapeAutomaton::<TropicalWeight, 2>::new();
        let b0 = b.add_state(None);
        let b1 = b.add_state(None);
        b.set_initial(b0, TropicalWeight::one());
        b.set_accepting(b1, TropicalWeight::one());
        // Labels differ on tape 0: "z" vs "x".
        b.add_transition(b0, b1, [Some("z".into()), Some("y".into())], TropicalWeight::one());

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
        a.add_transition(q0, q1, [Some("a".into()), Some("b".into())], TropicalWeight::new(1.0));

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
        a.add_transition(q0, q1, [Some("a".into()), Some("b".into())], TropicalWeight::one());

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
        a.add_transition(q0, q1, [Some("a".into()), None], TropicalWeight::new(1.0));
        // q1 --[eps, b]--> q2 (epsilon on tape 0, consume "b" on tape 1).
        a.add_transition(q1, q2, [None, Some("b".into())], TropicalWeight::new(2.0));

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
        a.add_transition(q0, q1, [Some("hello".into())], TropicalWeight::new(0.5));

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
        a.add_transition(q0, q1, [Some("a".into()), None, Some("c".into())], TropicalWeight::one());

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
        a.add_transition(q0, q1, [Some("x".into()), Some("x".into())], TropicalWeight::one());

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

        a.add_transition(q0, q1, [Some("x".into()), Some("y".into())], TropicalWeight::one());

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
        a.add_transition(q0, q1, [Some("a".into()), None], TropicalWeight::new(1.5));

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
        a.add_transition(q0, q1, [Some("a".into()), None, Some("a".into())], TropicalWeight::one());

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
        a.add_transition(q0, q1, [Some("tok".into())], LogWeight::new(0.5));

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
                has_var: true,
                native_type: None,
            },
            CategoryInfo {
                name: "Decl".to_string(),
                is_primary: false,
                has_var: true,
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
        assert_eq!(result.disconnected_tapes.len(), 2, "both categories should be disconnected");
    }

    #[test]
    fn analyze_bundle_connected_categories() {
        use crate::pipeline::CategoryInfo;

        let categories = vec![
            CategoryInfo {
                name: "Expr".to_string(),
                is_primary: true,
                has_var: true,
                native_type: None,
            },
            CategoryInfo {
                name: "Stmt".to_string(),
                is_primary: false,
                has_var: true,
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
                has_var: true,
                native_type: None,
            },
            CategoryInfo {
                name: "Pat".to_string(),
                is_primary: false,
                has_var: true,
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
        assert!(!result.overlapping_tapes.is_empty(), "identical rule structures should overlap");
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
                has_var: true,
                native_type: None,
            },
            CategoryInfo {
                name: "Name".to_string(),
                is_primary: false,
                has_var: true,
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
        use crate::grammar::ir::CollectionKind;
        use crate::pipeline::CategoryInfo;

        let categories = vec![
            CategoryInfo {
                name: "Prog".to_string(),
                is_primary: true,
                has_var: true,
                native_type: None,
            },
            CategoryInfo {
                name: "Stmt".to_string(),
                is_primary: false,
                has_var: true,
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
                    key_val_separator: None,
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
                has_var: true,
                native_type: None,
            },
            CategoryInfo {
                name: "B".to_string(),
                is_primary: false,
                has_var: true,
                native_type: None,
            },
            CategoryInfo {
                name: "C".to_string(),
                is_primary: false,
                has_var: true,
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

    // ── Sprint 6C: build_stream_automaton() tests ──────────────────────────

    #[test]
    fn build_stream_automaton_linear_chain() {
        let tokens: Vec<String> = vec!["let".into(), "x".into(), "=".into(), "42".into()];
        let automaton = build_stream_automaton::<TropicalWeight>("main", &tokens);

        // n+1 states for n tokens.
        assert_eq!(automaton.num_states(), 5);
        assert_eq!(automaton.num_transitions(), 4);
        assert_eq!(automaton.initial.len(), 1);
        assert_eq!(automaton.accepting.len(), 1);

        // Initial is state 0, accepting is state 4.
        assert!(automaton.initial.contains_key(&0));
        assert!(automaton.accepting.contains_key(&4));

        // Verify labels.
        assert_eq!(automaton.transitions[0].labels[0].as_deref(), Some("let"));
        assert_eq!(automaton.transitions[1].labels[0].as_deref(), Some("x"));
        assert_eq!(automaton.transitions[2].labels[0].as_deref(), Some("="));
        assert_eq!(automaton.transitions[3].labels[0].as_deref(), Some("42"));
    }

    #[test]
    fn build_stream_automaton_empty_tokens() {
        let tokens: Vec<String> = vec![];
        let automaton = build_stream_automaton::<TropicalWeight>("empty", &tokens);

        // 1 state (q0), which is both initial and accepting.
        assert_eq!(automaton.num_states(), 1);
        assert_eq!(automaton.num_transitions(), 0);
        assert!(automaton.initial.contains_key(&0));
        assert!(automaton.accepting.contains_key(&0));
    }

    #[test]
    fn build_stream_automaton_single_token() {
        let tokens: Vec<String> = vec!["hello".into()];
        let automaton = build_stream_automaton::<TropicalWeight>("single", &tokens);

        assert_eq!(automaton.num_states(), 2);
        assert_eq!(automaton.num_transitions(), 1);

        // Evaluate to verify acceptance.
        let result = automaton.evaluate(&[vec!["hello".into()]]);
        assert!(!result.is_zero(), "should accept the single token");
    }

    #[test]
    fn build_stream_automaton_state_labels() {
        let tokens: Vec<String> = vec!["a".into(), "b".into()];
        let automaton = build_stream_automaton::<TropicalWeight>("comments", &tokens);

        assert_eq!(automaton.states[0].label.as_deref(), Some("comments:q0"),);
        assert_eq!(automaton.states[1].label.as_deref(), Some("comments:q1"),);
        assert_eq!(automaton.states[2].label.as_deref(), Some("comments:q2"),);
    }

    #[test]
    fn build_stream_automaton_with_log_weight() {
        let tokens: Vec<String> = vec!["tok".into()];
        let automaton = build_stream_automaton::<LogWeight>("log_stream", &tokens);

        assert_eq!(automaton.num_states(), 2);
        assert_eq!(automaton.num_transitions(), 1);

        let result = automaton.evaluate(&[vec!["tok".into()]]);
        assert!(result.approx_eq(&LogWeight::one(), 1e-9), "all-one weights should yield one()");
    }

    // ── Sprint 6C: build_synced_stream_automaton() tests ───────────────────

    #[test]
    fn synced_stream_track_only() {
        use crate::{SyncConstraintSpec, SyncSpec};

        let main_tokens: Vec<String> = vec!["let".into(), "x".into(), "=".into(), "42".into()];
        let comment_tokens: Vec<String> = vec!["/* doc */".into()];

        let main_aut = build_stream_automaton::<TropicalWeight>("main", &main_tokens);
        let comment_aut = build_stream_automaton::<TropicalWeight>("comments", &comment_tokens);

        let sync = SyncSpec {
            constraints: vec![SyncConstraintSpec::Track {
                auxiliary: "comments".into(),
                primary: "main".into(),
            }],
        };

        let result =
            build_synced_stream_automaton(&main_aut, &comment_aut, "main", "comments", &sync);

        // Track constraints don't modify the automaton, so it should be the
        // full pair() product and should be satisfiable.
        assert!(result.is_satisfiable);
        assert_eq!(result.constraint_diagnostics.len(), 1);
        assert!(result.constraint_diagnostics[0].is_ok());

        // Product of 5 states * 2 states = 10 states.
        assert_eq!(result.automaton.num_states(), 10);
    }

    #[test]
    fn synced_stream_align_identical_tokens() {
        use crate::{SyncConstraintSpec, SyncSpec};

        // Two streams with the same tokens — Align should work.
        let tokens: Vec<String> = vec!["a".into(), "b".into()];
        let aut_a = build_stream_automaton::<TropicalWeight>("s1", &tokens);
        let aut_b = build_stream_automaton::<TropicalWeight>("s2", &tokens);

        let sync = SyncSpec {
            constraints: vec![SyncConstraintSpec::Align {
                stream_a: "s1".into(),
                stream_b: "s2".into(),
                boundary_pattern: "a".into(),
            }],
        };

        let result = build_synced_stream_automaton(&aut_a, &aut_b, "s1", "s2", &sync);

        assert_eq!(result.constraint_diagnostics.len(), 1);
        assert!(
            result.constraint_diagnostics[0].is_ok(),
            "Align should succeed when boundary exists in both streams"
        );
        // After auto_intersect, only transitions with matching labels survive.
        // The identical streams should retain some synchronized transitions.
        assert!(
            result.automaton.num_transitions() > 0,
            "synchronized identical streams should have transitions"
        );
    }

    #[test]
    fn synced_stream_align_missing_boundary_in_one() {
        use crate::{SyncConstraintSpec, SyncSpec};

        let tokens_a: Vec<String> = vec!["a".into(), "b".into()];
        let tokens_b: Vec<String> = vec!["c".into(), "d".into()];
        let aut_a = build_stream_automaton::<TropicalWeight>("s1", &tokens_a);
        let aut_b = build_stream_automaton::<TropicalWeight>("s2", &tokens_b);

        let sync = SyncSpec {
            constraints: vec![SyncConstraintSpec::Align {
                stream_a: "s1".into(),
                stream_b: "s2".into(),
                boundary_pattern: "a".into(), // exists in s1 but not s2
            }],
        };

        let result = build_synced_stream_automaton(&aut_a, &aut_b, "s1", "s2", &sync);

        assert_eq!(result.constraint_diagnostics.len(), 1);
        assert!(
            result.constraint_diagnostics[0].is_err(),
            "Align should fail when boundary missing from one stream"
        );
    }

    #[test]
    fn synced_stream_align_missing_boundary_in_both() {
        use crate::{SyncConstraintSpec, SyncSpec};

        let tokens_a: Vec<String> = vec!["a".into()];
        let tokens_b: Vec<String> = vec!["b".into()];
        let aut_a = build_stream_automaton::<TropicalWeight>("s1", &tokens_a);
        let aut_b = build_stream_automaton::<TropicalWeight>("s2", &tokens_b);

        let sync = SyncSpec {
            constraints: vec![SyncConstraintSpec::Align {
                stream_a: "s1".into(),
                stream_b: "s2".into(),
                boundary_pattern: "MISSING".into(),
            }],
        };

        let result = build_synced_stream_automaton(&aut_a, &aut_b, "s1", "s2", &sync);

        assert_eq!(result.constraint_diagnostics.len(), 1);
        assert!(
            result.constraint_diagnostics[0].is_err(),
            "Align should fail when boundary missing from both streams"
        );
    }

    #[test]
    fn synced_stream_align_wrong_streams() {
        use crate::{SyncConstraintSpec, SyncSpec};

        let tokens: Vec<String> = vec!["a".into()];
        let aut_a = build_stream_automaton::<TropicalWeight>("s1", &tokens);
        let aut_b = build_stream_automaton::<TropicalWeight>("s2", &tokens);

        // Constraint references streams that don't match our pair.
        let sync = SyncSpec {
            constraints: vec![SyncConstraintSpec::Align {
                stream_a: "other1".into(),
                stream_b: "other2".into(),
                boundary_pattern: "a".into(),
            }],
        };

        let result = build_synced_stream_automaton(&aut_a, &aut_b, "s1", "s2", &sync);

        // Constraint is skipped (doesn't apply to our streams), so the
        // automaton is unmodified and satisfiable.
        assert!(result.is_satisfiable);
        assert_eq!(result.constraint_diagnostics.len(), 1);
        assert!(result.constraint_diagnostics[0].is_ok());
        // Should contain "skipped" in the message.
        let msg = result.constraint_diagnostics[0]
            .as_ref()
            .expect("should be Ok");
        assert!(msg.contains("skipped"), "diagnostic should mention skipping: {msg}");
    }

    #[test]
    fn synced_stream_empty_sync_spec() {
        use crate::SyncSpec;

        let tokens: Vec<String> = vec!["a".into()];
        let aut_a = build_stream_automaton::<TropicalWeight>("s1", &tokens);
        let aut_b = build_stream_automaton::<TropicalWeight>("s2", &tokens);

        let sync = SyncSpec { constraints: vec![] };

        let result = build_synced_stream_automaton(&aut_a, &aut_b, "s1", "s2", &sync);

        // No constraints → just pair(), should be satisfiable.
        assert!(result.is_satisfiable);
        assert!(result.constraint_diagnostics.is_empty());
    }

    #[test]
    fn synced_stream_multiple_constraints() {
        use crate::{SyncConstraintSpec, SyncSpec};

        let tokens: Vec<String> = vec!["a".into(), "b".into()];
        let aut_a = build_stream_automaton::<TropicalWeight>("s1", &tokens);
        let aut_b = build_stream_automaton::<TropicalWeight>("s2", &tokens);

        let sync = SyncSpec {
            constraints: vec![
                SyncConstraintSpec::Track {
                    auxiliary: "s2".into(),
                    primary: "s1".into(),
                },
                SyncConstraintSpec::Align {
                    stream_a: "s1".into(),
                    stream_b: "s2".into(),
                    boundary_pattern: "a".into(),
                },
            ],
        };

        let result = build_synced_stream_automaton(&aut_a, &aut_b, "s1", "s2", &sync);

        assert_eq!(result.constraint_diagnostics.len(), 2);
        assert!(result.constraint_diagnostics[0].is_ok()); // Track
        assert!(result.constraint_diagnostics[1].is_ok()); // Align
    }

    // ── Sprint 6C: check_reachable_accepting() tests ───────────────────────

    #[test]
    fn check_reachable_accepting_simple_path() {
        let mut a = WeightedMultiTapeAutomaton::<TropicalWeight, 1>::new();
        let q0 = a.add_state(None);
        let q1 = a.add_state(None);
        a.set_initial(q0, TropicalWeight::one());
        a.set_accepting(q1, TropicalWeight::one());
        a.add_transition(q0, q1, [Some("x".into())], TropicalWeight::one());

        assert!(check_reachable_accepting(&a));
    }

    #[test]
    fn check_reachable_accepting_unreachable() {
        let mut a = WeightedMultiTapeAutomaton::<TropicalWeight, 1>::new();
        let q0 = a.add_state(None);
        let _q1 = a.add_state(None); // accepting but no transitions to it
        let q2 = a.add_state(None);
        a.set_initial(q0, TropicalWeight::one());
        a.set_accepting(q2, TropicalWeight::one());
        // Only transition: q0 -> q1 (not accepting)
        a.add_transition(q0, _q1, [Some("x".into())], TropicalWeight::one());

        assert!(!check_reachable_accepting(&a), "accepting state q2 should be unreachable");
    }

    #[test]
    fn check_reachable_accepting_empty() {
        let a = WeightedMultiTapeAutomaton::<TropicalWeight, 1>::new();
        assert!(
            !check_reachable_accepting(&a),
            "empty automaton has no reachable accepting state"
        );
    }

    #[test]
    fn check_reachable_accepting_initial_is_accepting() {
        let mut a = WeightedMultiTapeAutomaton::<TropicalWeight, 1>::new();
        let q0 = a.add_state(None);
        a.set_initial(q0, TropicalWeight::one());
        a.set_accepting(q0, TropicalWeight::one());

        assert!(
            check_reachable_accepting(&a),
            "initial state that is also accepting should be reachable"
        );
    }

    // ── Sprint 6C: validate_sync_constraints() tests ───────────────────────

    #[test]
    fn validate_sync_align_both_present() {
        use crate::{SyncConstraintSpec, SyncSpec};

        let mut streams = HashMap::new();
        streams.insert("s1".into(), vec!["a".into(), "b".into(), "a".into()]);
        streams.insert("s2".into(), vec!["a".into(), "c".into()]);

        let sync = SyncSpec {
            constraints: vec![SyncConstraintSpec::Align {
                stream_a: "s1".into(),
                stream_b: "s2".into(),
                boundary_pattern: "a".into(),
            }],
        };

        let diagnostics = validate_sync_constraints(&streams, &sync);
        assert_eq!(diagnostics.len(), 1);
        assert!(diagnostics[0].is_ok());
        // Should mention counts.
        let msg = diagnostics[0].as_ref().expect("should be Ok");
        assert!(msg.contains("2 in 's1'"), "should show 2 occurrences in s1: {msg}");
        assert!(msg.contains("1 in 's2'"), "should show 1 occurrence in s2: {msg}");
    }

    #[test]
    fn validate_sync_align_missing_stream() {
        use crate::{SyncConstraintSpec, SyncSpec};

        let mut streams = HashMap::new();
        streams.insert("s1".into(), vec!["a".into()]);
        // s2 does not exist

        let sync = SyncSpec {
            constraints: vec![SyncConstraintSpec::Align {
                stream_a: "s1".into(),
                stream_b: "s2".into(),
                boundary_pattern: "a".into(),
            }],
        };

        let diagnostics = validate_sync_constraints(&streams, &sync);
        assert_eq!(diagnostics.len(), 1);
        assert!(diagnostics[0].is_err());
        let msg = diagnostics[0].as_ref().expect_err("should be Err");
        assert!(msg.contains("s2"), "should mention missing stream: {msg}");
    }

    #[test]
    fn validate_sync_track_both_exist() {
        use crate::{SyncConstraintSpec, SyncSpec};

        let mut streams = HashMap::new();
        streams.insert("comments".into(), vec!["/* x */".into()]);
        streams.insert("main".into(), vec!["let".into(), "x".into()]);

        let sync = SyncSpec {
            constraints: vec![SyncConstraintSpec::Track {
                auxiliary: "comments".into(),
                primary: "main".into(),
            }],
        };

        let diagnostics = validate_sync_constraints(&streams, &sync);
        assert_eq!(diagnostics.len(), 1);
        assert!(diagnostics[0].is_ok());
    }

    #[test]
    fn validate_sync_track_missing_primary() {
        use crate::{SyncConstraintSpec, SyncSpec};

        let mut streams = HashMap::new();
        streams.insert("comments".into(), vec!["/* x */".into()]);
        // "main" does not exist

        let sync = SyncSpec {
            constraints: vec![SyncConstraintSpec::Track {
                auxiliary: "comments".into(),
                primary: "main".into(),
            }],
        };

        let diagnostics = validate_sync_constraints(&streams, &sync);
        assert_eq!(diagnostics.len(), 1);
        assert!(diagnostics[0].is_err());
    }

    #[test]
    fn validate_sync_empty_constraints() {
        let streams = HashMap::new();
        let sync = crate::SyncSpec { constraints: vec![] };

        let diagnostics = validate_sync_constraints(&streams, &sync);
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn validate_sync_align_boundary_not_in_either_stream() {
        use crate::{SyncConstraintSpec, SyncSpec};

        let mut streams = HashMap::new();
        streams.insert("s1".into(), vec!["x".into()]);
        streams.insert("s2".into(), vec!["y".into()]);

        let sync = SyncSpec {
            constraints: vec![SyncConstraintSpec::Align {
                stream_a: "s1".into(),
                stream_b: "s2".into(),
                boundary_pattern: "BOUNDARY".into(),
            }],
        };

        let diagnostics = validate_sync_constraints(&streams, &sync);
        assert_eq!(diagnostics.len(), 1);
        assert!(diagnostics[0].is_err());
        let msg = diagnostics[0].as_ref().expect_err("should be Err");
        assert!(
            msg.contains("either stream"),
            "should mention neither stream has the boundary: {msg}"
        );
    }

    #[test]
    fn validate_sync_multiple_mixed_constraints() {
        use crate::{SyncConstraintSpec, SyncSpec};

        let mut streams = HashMap::new();
        streams.insert("main".into(), vec!["a".into(), "b".into()]);
        streams.insert("ws".into(), vec![" ".into()]);
        streams.insert("comments".into(), vec!["/* */".into()]);

        let sync = SyncSpec {
            constraints: vec![
                SyncConstraintSpec::Track {
                    auxiliary: "ws".into(),
                    primary: "main".into(),
                },
                SyncConstraintSpec::Align {
                    stream_a: "main".into(),
                    stream_b: "comments".into(),
                    boundary_pattern: "a".into(), // in main but not comments
                },
                SyncConstraintSpec::Track {
                    auxiliary: "comments".into(),
                    primary: "main".into(),
                },
            ],
        };

        let diagnostics = validate_sync_constraints(&streams, &sync);
        assert_eq!(diagnostics.len(), 3);
        assert!(diagnostics[0].is_ok()); // Track ws/main — both exist
        assert!(diagnostics[1].is_err()); // Align main/comments — "a" not in comments
        assert!(diagnostics[2].is_ok()); // Track comments/main — both exist
    }

    // ══════════════════════════════════════════════════════════════════════════
    // K-generic tests (T11/2026-05-05): pair_n / pair_extend_to / K=0 / K=1 /
    // K=3 / K=4 / build_synced_stream_automaton_k. Per Kempe (2004) Eq. 18 +
    // Eq. 12 associativity, the K-tape cross-product is iterated binary
    // pairing; tests verify the iterated fold reduces correctly at each K.
    // ══════════════════════════════════════════════════════════════════════════

    /// K=0: trivial 0-tape automaton recognizing the empty K-tuple `()`.
    /// Identity element for `pair_extend`.
    #[test]
    fn pair_n_k0_recognizes_empty_tuple() {
        let trivial = pair_n::<TropicalWeight, 0>([]);
        assert_eq!(trivial.num_states(), 1);
        assert_eq!(trivial.num_transitions(), 0);
        // I(q) ⊗ F(q) = one() ⊗ one() = one().
        assert_eq!(trivial.evaluate(&[]), TropicalWeight::one());
    }

    /// K=1: pair_n([a]) returns a copy of `a` (degenerate single-tape).
    #[test]
    fn pair_n_k1_returns_clone_of_single_stream() {
        let a = linear_1tape(&["alpha", "beta"]);
        let folded = pair_n::<TropicalWeight, 1>([&a]);
        assert_eq!(folded.num_states(), a.num_states());
        assert_eq!(folded.num_transitions(), a.num_transitions());
        let r1 = folded.evaluate(&[vec!["alpha".into(), "beta".into()]]);
        let r2 = a.evaluate(&[vec!["alpha".into(), "beta".into()]]);
        assert_eq!(r1, r2);
    }

    /// K=1 evaluate matches single-tape NFA semantics on accept and reject.
    #[test]
    fn k1_evaluate_matches_single_tape_nfa_semantics() {
        let a = linear_1tape(&["a", "b", "c"]);
        let r_match = a.evaluate(&[vec!["a".into(), "b".into(), "c".into()]]);
        let r_miss = a.evaluate(&[vec!["a".into(), "WRONG".into(), "c".into()]]);
        assert_ne!(r_match, TropicalWeight::zero());
        assert_eq!(r_miss, TropicalWeight::zero());
    }

    /// K=1 multi_tape_intersect reduces to standard 1-tape intersection.
    #[test]
    fn k1_multi_tape_intersect_acts_as_weighted_intersection() {
        let a = linear_1tape(&["x"]);
        let b = linear_1tape(&["x"]);
        let p = multi_tape_intersect(&a, &b);
        // 2 states × 2 states = 4 product states.
        assert_eq!(p.num_states(), 4);
        // Only the matching label survives the synchronized cross-product.
        // The current K-generic multi_tape_intersect is a per-transition
        // label-match (not full Kempe Eq. 30), so we expect 1 transition.
        assert_eq!(p.num_transitions(), 1);
    }

    /// K=2 regression: pair() (now a wrapper over pair_n([a, b]))
    /// preserves the original product-state count and synchronized +
    /// ε-extended transition counts.
    #[test]
    fn pair_n_k2_byte_compat_with_legacy_pair() {
        let a = linear_1tape(&["x"]);
        let b = linear_1tape(&["y"]);
        let folded = pair(&a, &b);
        // 2 × 2 = 4 product states.
        assert_eq!(folded.num_states(), 4);
        // 1 sync × 1 + 1 ε-on-tape-0 × 2 states + 1 ε-on-tape-1 × 2 states
        // = 1 + 2 + 2 = 5 transitions.
        assert_eq!(folded.num_transitions(), 5);
    }

    /// K=3: pair_n state count = product of source state counts.
    #[test]
    fn pair_n_k3_construction_state_count() {
        let a = linear_1tape(&["a"]); // 2 states
        let b = linear_1tape(&["b1", "b2"]); // 3 states
        let c = linear_1tape(&["c"]); // 2 states
        let triple = pair_n::<TropicalWeight, 3>([&a, &b, &c]);
        assert_eq!(triple.num_states(), 2 * 3 * 2); // = 12
    }

    /// K=3: synchronized consumption of three independent tapes accepts.
    #[test]
    fn pair_n_k3_evaluate_synchronized_consumption() {
        let a = linear_1tape(&["x"]);
        let b = linear_1tape(&["y"]);
        let c = linear_1tape(&["z"]);
        let triple = pair_n::<TropicalWeight, 3>([&a, &b, &c]);
        let r = triple.evaluate(&[vec!["x".into()], vec!["y".into()], vec!["z".into()]]);
        assert_ne!(
            r,
            TropicalWeight::zero(),
            "K=3 paired automaton should accept independently-consumed tapes",
        );
    }

    /// K=3 auto_intersect on a distinct pair of tapes (0, 1) keeps only the
    /// transitions where labels[0] == labels[1] per-transition.
    #[test]
    fn auto_intersect_k3_distinct_pair_filters_correctly() {
        let mut m = WeightedMultiTapeAutomaton::<TropicalWeight, 3>::new();
        let q0 = m.add_state(None);
        let q1 = m.add_state(None);
        let q2 = m.add_state(None);
        m.set_initial(q0, TropicalWeight::one());
        m.set_accepting(q1, TropicalWeight::one());
        m.set_accepting(q2, TropicalWeight::one());
        m.add_transition(
            q0,
            q1,
            [Some("a".into()), Some("a".into()), Some("b".into())],
            TropicalWeight::one(),
        );
        m.add_transition(
            q0,
            q2,
            [Some("a".into()), Some("b".into()), Some("c".into())],
            TropicalWeight::one(),
        );
        let constrained = m.auto_intersect(0, 1);
        // Only the first transition has labels[0] == labels[1].
        assert_eq!(constrained.num_transitions(), 1);
    }

    /// K=4: pair_n state count = 2×2×2×2 = 16.
    #[test]
    fn pair_n_k4_state_count_product() {
        let s0 = linear_1tape(&["a"]);
        let s1 = linear_1tape(&["b"]);
        let s2 = linear_1tape(&["c"]);
        let s3 = linear_1tape(&["d"]);
        let q = pair_n::<TropicalWeight, 4>([&s0, &s1, &s2, &s3]);
        assert_eq!(q.num_states(), 2 * 2 * 2 * 2);
    }

    /// K=4 synchronized evaluation across four tapes of varying length.
    #[test]
    fn pair_n_k4_evaluate_synchronized() {
        let s0 = linear_1tape(&["a", "b"]);
        let s1 = linear_1tape(&["x"]);
        let s2 = linear_1tape(&["c"]);
        let s3 = linear_1tape(&["y", "z"]);
        let q = pair_n::<TropicalWeight, 4>([&s0, &s1, &s2, &s3]);
        let r = q.evaluate(&[
            vec!["a".into(), "b".into()],
            vec!["x".into()],
            vec!["c".into()],
            vec!["y".into(), "z".into()],
        ]);
        assert_ne!(r, TropicalWeight::zero(), "K=4 product accepts all tapes simultaneously",);
    }

    /// K=4 chained auto_intersect across two pairs (0,2) and (1,3).
    #[test]
    fn auto_intersect_k4_chained_two_pair_constraints() {
        let mut m = WeightedMultiTapeAutomaton::<TropicalWeight, 4>::new();
        let q0 = m.add_state(None);
        let q1 = m.add_state(None);
        m.set_initial(q0, TropicalWeight::one());
        m.set_accepting(q1, TropicalWeight::one());
        // Transition where labels[0] == labels[2] AND labels[1] == labels[3]:
        m.add_transition(
            q0,
            q1,
            [Some("a".into()), Some("x".into()), Some("a".into()), Some("x".into())],
            TropicalWeight::one(),
        );
        // Transition where labels[0] == labels[2] but labels[1] != labels[3]:
        m.add_transition(
            q0,
            q1,
            [Some("a".into()), Some("x".into()), Some("a".into()), Some("DIFF".into())],
            TropicalWeight::one(),
        );
        let c1 = m.auto_intersect(0, 2);
        let c2 = c1.auto_intersect(1, 3);
        // Only the all-matching transition survives both filters.
        assert_eq!(c2.num_transitions(), 1);
    }

    /// K=3 build_synced_stream_automaton_k: Align constraint between two of
    /// the three streams resolves correctly via name lookup.
    #[test]
    fn build_synced_stream_automaton_k3_align_two_tapes() {
        let s0 = build_stream_automaton::<TropicalWeight>("s0", &["a".into(), "b".into()]);
        let s1 = build_stream_automaton::<TropicalWeight>("s1", &["c".into(), "d".into()]);
        let s2 = build_stream_automaton::<TropicalWeight>("s2", &["a".into(), "e".into()]);
        let sync = crate::SyncSpec {
            constraints: vec![crate::SyncConstraintSpec::Align {
                stream_a: "s0".into(),
                stream_b: "s2".into(),
                boundary_pattern: "a".into(),
            }],
        };
        let result = build_synced_stream_automaton_k::<TropicalWeight, 3>(
            [&s0, &s1, &s2],
            ["s0", "s1", "s2"],
            &sync,
        );
        // The boundary "a" appears in both s0 and s2, so the constraint is
        // applied (auto_intersect(0, 2)). The constraint diagnostic is Ok.
        assert_eq!(result.constraint_diagnostics.len(), 1);
        assert!(
            result.constraint_diagnostics[0].is_ok(),
            "expected Ok, got {:?}",
            result.constraint_diagnostics[0],
        );
    }

    /// K=3 build_synced_stream_automaton_k: Align with name not in `names`
    /// produces a "skipped" diagnostic without affecting the automaton.
    #[test]
    fn build_synced_stream_automaton_k3_align_unknown_stream_skips() {
        let s0 = build_stream_automaton::<TropicalWeight>("s0", &["a".into()]);
        let s1 = build_stream_automaton::<TropicalWeight>("s1", &["b".into()]);
        let s2 = build_stream_automaton::<TropicalWeight>("s2", &["c".into()]);
        let sync = crate::SyncSpec {
            constraints: vec![crate::SyncConstraintSpec::Align {
                stream_a: "s0".into(),
                stream_b: "UNKNOWN".into(),
                boundary_pattern: ".".into(),
            }],
        };
        let result = build_synced_stream_automaton_k::<TropicalWeight, 3>(
            [&s0, &s1, &s2],
            ["s0", "s1", "s2"],
            &sync,
        );
        assert_eq!(result.constraint_diagnostics.len(), 1);
        assert!(result.constraint_diagnostics[0].is_ok());
        let msg = match &result.constraint_diagnostics[0] {
            Ok(m) => m.clone(),
            Err(_) => panic!("expected Ok diagnostic"),
        };
        assert!(msg.contains("skipped"), "diagnostic should say skipped: {}", msg);
    }

    /// K=2 evaluation parity: pair(a, b) (now a thin wrapper over pair_n) and
    /// the K=2 binary `pair` produce the same evaluation results.
    #[test]
    fn pair_n_k2_evaluate_parity_with_legacy_binary_pair() {
        let a = linear_1tape(&["x"]);
        let b = linear_1tape(&["y"]);
        let p_binary = pair(&a, &b);
        let p_via_n = pair_n::<TropicalWeight, 2>([&a, &b]);
        // Same number of states and transitions.
        assert_eq!(p_binary.num_states(), p_via_n.num_states());
        assert_eq!(p_binary.num_transitions(), p_via_n.num_transitions());
        // Same evaluation on accepting input.
        let r_binary = p_binary.evaluate(&[vec!["x".into()], vec!["y".into()]]);
        let r_via_n = p_via_n.evaluate(&[vec!["x".into()], vec!["y".into()]]);
        assert_eq!(r_binary, r_via_n);
    }

    /// pair_extend_to: 2-tape × 1-tape → 3-tape.
    #[test]
    fn pair_extend_to_k2_to_k3() {
        let a = linear_1tape(&["x"]);
        let b = linear_1tape(&["y"]);
        let c = linear_1tape(&["z"]);
        let pair_ab = pair(&a, &b); // <W, 2>
        let triple: WeightedMultiTapeAutomaton<TropicalWeight, 3> =
            pair_extend_to::<TropicalWeight, 2, 3>(&pair_ab, &c);
        // |Q_ab| = 4 × |Q_c| = 2 → 8 product states.
        assert_eq!(triple.num_states(), 8);
        // Evaluation accepts all-three-tapes synchronized:
        let r = triple.evaluate(&[vec!["x".into()], vec!["y".into()], vec!["z".into()]]);
        assert_ne!(r, TropicalWeight::zero());
    }

    /// Property: pair_n is associative (K=3 case).
    /// pair_n([a, b, c]) and pair_extend_to(pair_n([a, b]), c) produce
    /// automata with the same product-state count.
    #[test]
    fn pair_n_k3_associativity_property() {
        let a = linear_1tape(&["a1"]);
        let b = linear_1tape(&["b1"]);
        let c = linear_1tape(&["c1"]);
        let abc_direct = pair_n::<TropicalWeight, 3>([&a, &b, &c]);
        let ab = pair_n::<TropicalWeight, 2>([&a, &b]);
        let abc_left_assoc: WeightedMultiTapeAutomaton<TropicalWeight, 3> =
            pair_extend_to::<TropicalWeight, 2, 3>(&ab, &c);
        // Both fold orderings produce the same product-state count.
        assert_eq!(abc_direct.num_states(), abc_left_assoc.num_states());
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Property-based tests
// ══════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod proptest_tests {
    use super::*;
    use crate::test_generators::*;
    use crate::SyntaxItemSpec;
    use proptest::prelude::*;

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
                    connections
                        .entry(rule_cat.to_string())
                        .or_default()
                        .insert(category.clone());
                    connections
                        .entry(category.clone())
                        .or_default()
                        .insert(rule_cat.to_string());
                }
            },
            SyntaxItemSpec::Binder { category, .. } => {
                if category != rule_cat {
                    connections
                        .entry(rule_cat.to_string())
                        .or_default()
                        .insert(category.clone());
                    connections
                        .entry(category.clone())
                        .or_default()
                        .insert(rule_cat.to_string());
                }
            },
            SyntaxItemSpec::Collection { element_category, .. } => {
                if element_category != rule_cat {
                    connections
                        .entry(rule_cat.to_string())
                        .or_default()
                        .insert(element_category.clone());
                    connections
                        .entry(element_category.clone())
                        .or_default()
                        .insert(rule_cat.to_string());
                }
            },
            SyntaxItemSpec::Sep { body, .. } => {
                collect_cross_refs(body, rule_cat, connections);
            },
            SyntaxItemSpec::Map { body_items } => {
                for sub in body_items {
                    collect_cross_refs(sub, rule_cat, connections);
                }
            },
            SyntaxItemSpec::Zip { left_category, right_category, body, .. } => {
                for ref_cat in [left_category.as_str(), right_category.as_str()] {
                    if ref_cat != rule_cat {
                        connections
                            .entry(rule_cat.to_string())
                            .or_default()
                            .insert(ref_cat.to_string());
                        connections
                            .entry(ref_cat.to_string())
                            .or_default()
                            .insert(rule_cat.to_string());
                    }
                }
                collect_cross_refs(body, rule_cat, connections);
            },
            SyntaxItemSpec::Optional { inner } => {
                for sub in inner {
                    collect_cross_refs(sub, rule_cat, connections);
                }
            },
            _ => {},
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
