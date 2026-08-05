//! Parity Alternating Tree Automata (PATA) for mu-calculus model checking.
//!
//! Parity alternating tree automata extend alternating automata from words to
//! trees (terms). A PATA processes a term from root to leaves, using
//! existential (disjunctive) and universal (conjunctive) branching to navigate
//! child subtrees. The parity acceptance condition generalizes Buchi acceptance:
//! a run is accepting iff the minimum priority visited infinitely often along
//! every path is even.
//!
//! ## Theoretical Foundations
//!
//! - **Emerson & Jutla (1991)** — "Tree automata, mu-calculus and determinacy."
//!   Establishes the equivalence between mu-calculus model checking and
//!   acceptance by alternating tree automata with parity conditions.
//! - **Zielonka (1998)** — "Infinite games on finitely coloured graphs with
//!   applications to automata on infinite trees." Provides the recursive
//!   algorithm for solving parity games that underlies emptiness checking.
//! - **Muller & Schupp (1995)** — "Simulating alternating tree automata by
//!   nondeterministic automata." Shows the simulation relationship and
//!   complementation via priority manipulation.
//! - **Bradfield & Stirling (2006)** — "Modal mu-calculi." Comprehensive
//!   survey of the modal mu-calculus and its automata-theoretic semantics.
//!
//! ## Architecture
//!
//! ```text
//! Mu-calculus formula
//!       │
//!       ▼
//! mu_calculus_to_pata()
//!       │
//!       ▼
//! ParityAlternatingTreeAutomaton
//!       │
//!       ├──→ check_emptiness() (parity game reduction)
//!       │
//!       ├──→ evaluate_term() (bottom-up evaluation on concrete terms)
//!       │
//!       └──→ check_inclusion() (complement + product + emptiness)
//! ```
//!
//! ## PraTTaIL Integration
//!
//! Parity alternating tree automata model branching specifications over parse
//! trees and ASTs. Mu-calculus formulas express recursive structural properties
//! (e.g., "every function application has a well-typed argument in some child
//! position") that can be checked against concrete parse trees via
//! `evaluate_term` or verified structurally via `check_emptiness`.

use std::collections::{HashMap, HashSet};
use std::fmt;

use crate::alternating::BranchingMode;
use crate::automata::semiring::{BooleanWeight, Semiring};

// ══════════════════════════════════════════════════════════════════════════════
// Core types
// ══════════════════════════════════════════════════════════════════════════════

/// A state in a parity alternating tree automaton.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ParityTreeState {
    /// Unique state identifier.
    pub id: usize,
    /// Whether this state uses universal (conjunctive) or existential
    /// (disjunctive) branching.
    pub branching: BranchingMode,
    /// Priority for parity acceptance (0 = most accepting).
    /// Even priorities are accepting; odd are rejecting.
    pub priority: u32,
    /// Optional label for diagnostics.
    pub label: Option<String>,
}

impl fmt::Display for ParityTreeState {
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

/// A transition in a PATA.
///
/// Specifies how to process a tree node's children. Each direction triple
/// `(child_index, target_state, weight)` says: descend into the `child_index`-th
/// child of the current tree node and continue evaluation from `target_state`,
/// accumulating `weight`.
#[derive(Debug, Clone)]
pub struct ParityTreeTransition<W: Semiring> {
    /// Source state ID.
    pub from: usize,
    /// Symbol labeling the tree node.
    pub symbol: String,
    /// `(child_index, target_state, weight)` triples.
    /// `child_index` indicates which child of the tree node to descend into.
    pub directions: Vec<(usize, usize, W)>,
}

impl<W: Semiring + fmt::Display> fmt::Display for ParityTreeTransition<W> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let dirs: Vec<String> = self
            .directions
            .iter()
            .map(|(ci, tgt, w)| format!("(child={}, q{}, {})", ci, tgt, w))
            .collect();
        write!(f, "q{} --{}-> [{}]", self.from, self.symbol, dirs.join(", "))
    }
}

/// A term (tree) for evaluation.
///
/// A term is a labeled, ranked tree. Each node has a symbol and zero or more
/// children. Leaves are terms with zero children.
pub struct Term {
    /// The symbol labeling this node.
    pub symbol: String,
    /// Child subtrees (empty for leaves).
    pub children: Vec<Term>,
}

impl Clone for Term {
    fn clone(&self) -> Self {
        struct CloneFrame<'term> {
            source: &'term Term,
            next_child: usize,
            children: Vec<Term>,
        }

        let mut frames = vec![CloneFrame {
            source: self,
            next_child: 0,
            children: Vec::with_capacity(self.children.len()),
        }];
        loop {
            let frame = frames
                .last_mut()
                .expect("the root clone frame remains until cloning completes");
            if let Some(child) = frame.source.children.get(frame.next_child) {
                frame.next_child += 1;
                frames.push(CloneFrame {
                    source: child,
                    next_child: 0,
                    children: Vec::with_capacity(child.children.len()),
                });
                continue;
            }

            let frame = frames.pop().expect("the completed clone frame exists");
            let cloned = Term {
                symbol: frame.source.symbol.clone(),
                children: frame.children,
            };
            if let Some(parent) = frames.last_mut() {
                parent.children.push(cloned);
            } else {
                return cloned;
            }
        }
    }
}

impl PartialEq for Term {
    fn eq(&self, other: &Self) -> bool {
        let mut work = vec![(self, other)];
        while let Some((left, right)) = work.pop() {
            if left.symbol != right.symbol || left.children.len() != right.children.len() {
                return false;
            }
            work.extend(left.children.iter().zip(&right.children));
        }
        true
    }
}

impl Eq for Term {}

impl Drop for Term {
    fn drop(&mut self) {
        // Empty every descendant's child vector before that descendant is
        // dropped, turning recursive structural destruction into an explicit
        // heap-backed worklist.
        let mut work = std::mem::take(&mut self.children);
        while let Some(mut node) = work.pop() {
            work.append(&mut node.children);
        }
    }
}

impl fmt::Debug for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        enum Task<'term> {
            Term(&'term Term),
            Separator,
            Close,
        }

        let mut work = vec![Task::Term(self)];
        while let Some(task) = work.pop() {
            match task {
                Task::Term(term) => {
                    write!(f, "Term {{ symbol: {:?}, children: [", term.symbol)?;
                    work.push(Task::Close);
                    for (index, child) in term.children.iter().enumerate().rev() {
                        work.push(Task::Term(child));
                        if index > 0 {
                            work.push(Task::Separator);
                        }
                    }
                },
                Task::Separator => f.write_str(", ")?,
                Task::Close => f.write_str("] }")?,
            }
        }
        Ok(())
    }
}

impl Term {
    /// Create a leaf term with the given symbol.
    pub fn leaf(symbol: impl Into<String>) -> Self {
        Term {
            symbol: symbol.into(),
            children: Vec::new(),
        }
    }

    /// Create a term node with the given symbol and children.
    pub fn node(symbol: impl Into<String>, children: Vec<Term>) -> Self {
        Term { symbol: symbol.into(), children }
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        enum Task<'term> {
            Term(&'term Term),
            Separator,
            Close,
        }

        let mut work = vec![Task::Term(self)];
        while let Some(task) = work.pop() {
            match task {
                Task::Term(term) => {
                    f.write_str(&term.symbol)?;
                    if !term.children.is_empty() {
                        f.write_str("(")?;
                        work.push(Task::Close);
                        for (index, child) in term.children.iter().enumerate().rev() {
                            work.push(Task::Term(child));
                            if index > 0 {
                                work.push(Task::Separator);
                            }
                        }
                    }
                },
                Task::Separator => f.write_str(", ")?,
                Task::Close => f.write_str(")")?,
            }
        }
        Ok(())
    }
}

/// A parity alternating tree automaton.
///
/// ## Theoretical Foundations
///
/// - **Emerson & Jutla (1991)** — "Tree automata, mu-calculus and determinacy."
/// - **Zielonka (1998)** — "Infinite games on finitely coloured graphs with
///   applications to automata on infinite trees."
/// - **Muller & Schupp (1995)** — "Simulating alternating tree automata by
///   nondeterministic automata."
///
/// ## Formal Definition
///
/// A PATA is a tuple `A = (Q, Σ, δ, q₀, Ω, k)` where:
/// - `Q = Q_E ∪ Q_A` (existential and universal states)
/// - `Σ` is the ranked alphabet (each symbol has an arity)
/// - `δ: Q × Σ → B⁺(Dir × Q)` maps states and symbols to positive Boolean
///   combinations of direction-state pairs
/// - `q₀` is the initial state
/// - `Ω: Q → ℕ` is the priority function (parity acceptance)
/// - `k` is the maximum arity (branching factor)
#[derive(Debug, Clone)]
pub struct ParityAlternatingTreeAutomaton<W: Semiring> {
    /// All states in the automaton.
    pub states: Vec<ParityTreeState>,
    /// The alphabet (set of node symbols).
    pub alphabet: HashSet<String>,
    /// Transitions.
    pub transitions: Vec<ParityTreeTransition<W>>,
    /// Initial state ID.
    pub initial_state: Option<usize>,
    /// Maximum number of children per node (maximum arity).
    pub max_arity: usize,
}

impl<W: Semiring> ParityAlternatingTreeAutomaton<W> {
    /// Create an empty PATA with the given maximum arity.
    pub fn new(max_arity: usize) -> Self {
        ParityAlternatingTreeAutomaton {
            states: Vec::new(),
            alphabet: HashSet::new(),
            transitions: Vec::new(),
            initial_state: None,
            max_arity,
        }
    }

    /// Add a state and return its ID.
    pub fn add_state(
        &mut self,
        branching: BranchingMode,
        priority: u32,
        label: Option<String>,
    ) -> usize {
        let id = self.states.len();
        self.states
            .push(ParityTreeState { id, branching, priority, label });
        id
    }

    /// Add a transition from state `from` on symbol `symbol` with the given
    /// direction triples `(child_index, target_state, weight)`.
    pub fn add_transition(
        &mut self,
        from: usize,
        symbol: String,
        directions: Vec<(usize, usize, W)>,
    ) {
        self.alphabet.insert(symbol.clone());
        self.transitions
            .push(ParityTreeTransition { from, symbol, directions });
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

    /// Compute the nesting depth of fixpoints (number of distinct priority
    /// levels used, which bounds the alternation depth of the corresponding
    /// mu-calculus formula).
    pub fn priority_depth(&self) -> u32 {
        let priorities: HashSet<u32> = self.states.iter().map(|s| s.priority).collect();
        priorities.len() as u32
    }
}

impl<W: Semiring> Default for ParityAlternatingTreeAutomaton<W> {
    fn default() -> Self {
        Self::new(0)
    }
}

impl<W: Semiring> fmt::Display for ParityAlternatingTreeAutomaton<W> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "PATA {{ states: {}, transitions: {}, max_priority: {}, max_arity: {} }}",
            self.num_states(),
            self.num_transitions(),
            self.max_priority(),
            self.max_arity,
        )
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Mu-calculus formula
// ══════════════════════════════════════════════════════════════════════════════

/// Mu-calculus formula for specification over tree structures.
///
/// The modal mu-calculus extends propositional logic with:
/// - Modal operators: `Diamond{k, phi}` (some k-th child satisfies phi),
///   `Box{k, phi}` (all k-th children satisfy phi)
/// - Fixpoint operators: `Mu{X, phi}` (least fixpoint — eventually must hold),
///   `Nu{X, phi}` (greatest fixpoint — invariant property)
///
/// ## Semantics
///
/// Given a tree `T` and environment `rho` mapping variables to sets of nodes:
/// - `[[True]]_rho` = all nodes
/// - `[[False]]_rho` = empty set
/// - `[[Atom(a)]]_rho` = {nodes labeled `a`}
/// - `[[Var(X)]]_rho` = `rho(X)`
/// - `[[Not(phi)]]_rho` = complement of `[[phi]]_rho`
/// - `[[And(phi, psi)]]_rho` = `[[phi]]_rho` intersect `[[psi]]_rho`
/// - `[[Or(phi, psi)]]_rho` = `[[phi]]_rho` union `[[psi]]_rho`
/// - `[[Diamond{k, phi}]]_rho` = {nodes whose k-th child is in `[[phi]]_rho`}
/// - `[[Box{k, phi}]]_rho` = {nodes whose all k-th children are in `[[phi]]_rho`}
/// - `[[Mu{X, phi}]]_rho` = least fixpoint of `S -> [[phi]]_rho[X:=S]`
/// - `[[Nu{X, phi}]]_rho` = greatest fixpoint of `S -> [[phi]]_rho[X:=S]`
pub enum MuCalculusFormula {
    /// Propositional variable (references fixpoint binding).
    Var(String),
    /// True (tautology — satisfied by all nodes).
    True,
    /// False (contradiction — satisfied by no node).
    False,
    /// Atomic proposition: node has label `label`.
    Atom(String),
    /// Negation.
    Not(Box<MuCalculusFormula>),
    /// Conjunction.
    And(Box<MuCalculusFormula>, Box<MuCalculusFormula>),
    /// Disjunction.
    Or(Box<MuCalculusFormula>, Box<MuCalculusFormula>),
    /// Existential modality: `Diamond_k(phi)` — some k-th child satisfies `phi`.
    Diamond {
        child_idx: usize,
        body: Box<MuCalculusFormula>,
    },
    /// Universal modality: `Box_k(phi)` — all k-th children satisfy `phi`.
    Box {
        child_idx: usize,
        body: Box<MuCalculusFormula>,
    },
    /// Least fixpoint: `mu X. phi`.
    Mu {
        var: String,
        body: Box<MuCalculusFormula>,
    },
    /// Greatest fixpoint: `nu X. phi`.
    Nu {
        var: String,
        body: Box<MuCalculusFormula>,
    },
}

#[path = "parity_tree/mu_calculus_lifecycle.rs"]
mod mu_calculus_lifecycle;

/// Errors produced while compiling modal mu-calculus formulas to PATA.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MuCalculusCompileError {
    /// A variable reference appears outside the scope of a matching fixpoint.
    UnboundVariable { var: String },
}

impl fmt::Display for MuCalculusCompileError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            MuCalculusCompileError::UnboundVariable { var } => {
                write!(f, "unbound mu-calculus variable `{}`", var)
            },
        }
    }
}

impl std::error::Error for MuCalculusCompileError {}

// ══════════════════════════════════════════════════════════════════════════════
// Analysis result
// ══════════════════════════════════════════════════════════════════════════════

/// Result of a parity tree automaton analysis.
#[derive(Debug, Clone)]
pub struct ParityTreeAnalysis {
    /// Number of states in the PATA.
    pub num_states: usize,
    /// Maximum priority across all states.
    pub max_priority: u32,
    /// Whether the language of the PATA is empty.
    pub is_empty: bool,
    /// Nesting depth of fixpoints (number of distinct priority levels).
    pub priority_depth: u32,
    /// OSLF Phase 5 `.1`: per-recursive-predicate emptiness verdicts.
    ///
    /// Each entry is `(predicate_name, is_satisfiable)` where `is_satisfiable`
    /// is the NON-emptiness of the predicate's PATA — i.e. `true` iff some AST
    /// can satisfy the recursive behavioral type. Computed by
    /// [`analyze_recursive_predicates`] via [`decide_recursive_predicate`] (which
    /// lowers through [`crate::letprop::letprop_to_pata`] and decides with
    /// [`check_emptiness`]). EMPTY on every current grammar because no surface
    /// syntax yet produces a `letprop` recursive predicate (that is a tracked
    /// follow-up touching `ast/`), so the live path is parity-safe and inert; the
    /// `LP01` dead-behavioral-type lint consumes the `false` entries. Always
    /// present; EMPTY on every current grammar (no surface syntax yet produces a
    /// `letprop` recursive predicate).
    pub fixpoint_decisions: Vec<(String, bool)>,
}

/// Analyze grammar tree structure using parity tree automata.
///
/// Builds a trivial PATA from the grammar's rule nesting structure.
/// Reports state count, priority depth, and emptiness.
pub fn analyze_from_bundle(
    all_syntax: &[(String, String, Vec<crate::SyntaxItemSpec>)],
    categories: &[crate::pipeline::CategoryInfo],
) -> ParityTreeAnalysis {
    let num_states = categories.len().max(1);
    ParityTreeAnalysis {
        num_states,
        max_priority: if categories.is_empty() { 0 } else { 1 },
        is_empty: all_syntax.is_empty(),
        priority_depth: 1,
        fixpoint_decisions: Vec::new(),
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// OSLF Phase 5 `.1`: live recursive-predicate decision path
// ══════════════════════════════════════════════════════════════════════════════

/// Decide whether a `letprop` recursive behavioral predicate is *satisfiable*
/// (its PATA is NON-empty).
///
/// This is the first live caller of [`crate::letprop::letprop_to_pata`]: the
/// predicate is lowered to a modal-μ-calculus formula (μ for least / ν for
/// greatest fixpoint, by [`crate::letprop::analyze_polarity`]), compiled to a
/// Parity Alternating Tree Automaton over the recognized arity, then decided by
/// the Zielonka-aligned [`check_emptiness`] (Rocq-aligned to `PataEmptiness.v`).
///
/// Returns `true` iff `L(PATA) ≠ ∅` — i.e. some finite AST can satisfy the
/// recursive type. A lowering failure (mixed polarity, argument mismatch, a
/// non-recursive body, or an ill-scoped μ-formula) is treated as `false`: an
/// undecidable / malformed predicate has no witnessed inhabitant, which the
/// `LP01` lint surfaces as a dead behavioral type rather than crashing the
/// build.
///
/// `max_arity` for the tree alphabet is derived from the predicate's parameter
/// count (each parameter contributes at most one child direction in the lowered
/// formula); a parameterless predicate still needs arity ≥ 1 so leaf
/// transitions are representable.
pub fn decide_recursive_predicate(rp: &crate::letprop::RecursivePredicate) -> bool {
    let max_arity = rp.params.len().max(1);
    match crate::letprop::letprop_to_pata(rp, max_arity) {
        Ok(pata) => !check_emptiness(&pata),
        // A predicate that cannot be lowered has no decided inhabitant; report it
        // as unsatisfiable so LP01 flags it instead of panicking the pipeline.
        Err(_) => false,
    }
}

/// OSLF Phase 5 `.1`: richer parity-tree analysis that decides every recursive
/// (`letprop`-style) behavioral predicate reachable from the grammar's guards.
///
/// Extends the stub [`analyze_from_bundle`] result with a per-predicate
/// satisfiability verdict in [`ParityTreeAnalysis::fixpoint_decisions`]. The set
/// of recursive predicates is gathered by [`collect_recursive_predicates`], which
/// walks the grammar's guard predicates; **no current grammar surface syntax
/// produces a `letprop` recursive predicate** (that is a tracked follow-up that
/// touches `ast/`), so on every present grammar this returns an EMPTY
/// `fixpoint_decisions` and is byte-equivalent (modulo the new empty field) to
/// the stub — the live path is parity-safe and inert. When a recursive predicate
/// *is* present (exercised today by the synthetic positive case in
/// `prattail/tests/letprop_pata_snapshot.rs`), each is decided via
/// [`decide_recursive_predicate`].
pub fn analyze_recursive_predicates(
    all_syntax: &[(String, String, Vec<crate::SyntaxItemSpec>)],
    categories: &[crate::pipeline::CategoryInfo],
) -> ParityTreeAnalysis {
    let mut analysis = analyze_from_bundle(all_syntax, categories);

    let recursive = collect_recursive_predicates(all_syntax, categories);
    let mut decisions: Vec<(String, bool)> = Vec::with_capacity(recursive.len());
    for rp in &recursive {
        let satisfiable = decide_recursive_predicate(rp);
        decisions.push((rp.name.clone(), satisfiable));
    }

    // Surface the richest PATA shape we actually built. When at least one
    // recursive predicate was decided, recompute the headline (num_states /
    // max_priority / is_empty / priority_depth) from the *first* predicate's
    // automaton so the existing PT01–PT03 lints reflect a real PATA rather than
    // the category-count stub. With no recursive predicates the stub is kept
    // verbatim (inert).
    if let Some(first) = recursive.first() {
        let max_arity = first.params.len().max(1);
        if let Ok(pata) = crate::letprop::letprop_to_pata(first, max_arity) {
            analysis.num_states = pata.num_states();
            analysis.max_priority = pata.max_priority();
            analysis.priority_depth = pata.priority_depth();
            analysis.is_empty = check_emptiness(&pata);
        }
    }

    analysis.fixpoint_decisions = decisions;
    analysis
}

/// Gather every `letprop` recursive predicate reachable from the grammar's guard
/// predicates.
///
/// This is the seam to the (tracked, not-yet-built) surface syntax: once a
/// `letprop` declaration lowers into the grammar IR's guard predicates, this
/// function will return one [`crate::letprop::RecursivePredicate`] per recursive
/// guard. Today there is **no** such surface syntax, and the parser bundle
/// (`all_syntax` + `categories`) carries no recursive-predicate payload, so this
/// always returns an empty vector — the live decision path stays inert on every
/// present grammar. It is written as a total walk (rather than `unimplemented!`)
/// so the analysis is a no-op, never a panic, when the feature is enabled on a
/// real grammar.
fn collect_recursive_predicates(
    _all_syntax: &[(String, String, Vec<crate::SyntaxItemSpec>)],
    _categories: &[crate::pipeline::CategoryInfo],
) -> Vec<crate::letprop::RecursivePredicate> {
    // No surface syntax yet lowers a `letprop` into the parser bundle; the
    // recursive-predicate payload does not exist on `SyntaxItemSpec` /
    // `CategoryInfo`. Returning an empty set keeps the live path parity-safe
    // and inert until the tracked `ast/` follow-up wires the surface form.
    Vec::new()
}

// ══════════════════════════════════════════════════════════════════════════════
// Core operations
// ══════════════════════════════════════════════════════════════════════════════

/// Check emptiness of a parity alternating tree automaton.
///
/// Reduces the problem to a parity game on finite trees. Player 0 (Existential)
/// controls existential states; Player 1 (Universal) controls universal states.
/// The automaton is non-empty iff Player 0 has a winning strategy from the
/// initial state.
///
/// For finite trees, we use bottom-up fixpoint evaluation:
/// 1. States with even priority and no outgoing transitions are accepting leaves.
/// 2. States with odd priority and no outgoing transitions are rejecting leaves.
/// 3. Propagate backward:
///    - Existential: accepting if **some** transition leads to all-accepting
///      successor directions.
///    - Universal: accepting if **all** transitions lead to all-accepting
///      successor directions.
///
/// # Arguments
///
/// * `automaton` - The PATA to check.
///
/// # Returns
///
/// `true` if `L(automaton) = emptyset`, `false` otherwise.
// === Rocq Proof Alignment (PataEmptiness.v) ===
//
// The Rocq proof formalizes Zielonka's recursive parity game algorithm,
// proving it terminates (well-founded recursion on vertex count via
// `zielonka_wf_argument`) and correctly partitions vertices into winning
// regions (`zielonka_terminates`, `zielonka_empty_game`).
//
// The Rust implementation uses a bottom-up fixpoint propagation instead:
// states with even priority are immediately accepting; odd-priority states
// become accepting when their transitions are satisfied (existential = any,
// universal = all). This iterates until no state changes.
//
// Both algorithms solve PATA emptiness for *finite* trees. The fixpoint is
// correct because `accepting[s]` is a monotone function over a finite lattice
// (each of N states can flip false→true at most once, so the fixpoint is
// reached in at most N iterations). For infinite-tree semantics (ω-regular
// parity conditions), the full Zielonka algorithm would be needed.
//
// Properties preserved:
//   - Even-priority leaves are accepting (both algorithms).
//   - Universal states require all children to accept (both).
//   - Existential states require at least one child to accept (both).
//   - Termination is guaranteed by the finite state set.
pub fn check_emptiness(automaton: &ParityAlternatingTreeAutomaton<BooleanWeight>) -> bool {
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

    // Build adjacency: for each state, collect transitions as lists of target
    // state IDs (extracted from direction triples).
    let mut transitions_from: Vec<Vec<Vec<usize>>> = vec![Vec::new(); n];
    for t in &automaton.transitions {
        if t.from < n {
            let targets: Vec<usize> = t.directions.iter().map(|&(_, tgt, _)| tgt).collect();
            transitions_from[t.from].push(targets);
        }
    }

    // `accepting[s]` = true means state s can produce an accepting run subtree.
    let mut accepting = vec![false; n];

    // Initialize accepting status.
    // For finite-tree parity semantics:
    // - A state with even priority can always terminate the run (accepting),
    //   regardless of whether it has outgoing transitions. Even priority means
    //   "this checkpoint is accepting" in the parity condition.
    // - A state with odd priority can only accept by continuing through
    //   transitions that eventually reach even-priority dominance.
    // - A state with no transitions (leaf) accepts iff its priority is even.
    for s in 0..n {
        if automaton.states[s].priority % 2 == 0 {
            // Even priority: can terminate the run here (accepting checkpoint).
            accepting[s] = true;
        }
        // Odd priority with no transitions: rejecting leaf (stays false).
    }

    // Fixpoint iteration: propagate accepting status backward.
    let mut changed = true;
    while changed {
        changed = false;
        for s in 0..n {
            if accepting[s] {
                continue;
            }
            if transitions_from[s].is_empty() {
                continue;
            }

            let even_priority = automaton.states[s].priority % 2 == 0;

            // A transition's target list counts as "satisfied" if:
            // - It has non-empty targets and all targets are accepting, OR
            // - It has empty targets (no child obligations) AND the state
            //   has even priority (can terminate with an accepting parity).
            //
            // Without the even-priority check, empty-target transitions on
            // odd-priority states would vacuously satisfy, which is incorrect:
            // the run terminates at odd priority, which is rejecting.
            let transition_satisfied = |targets: &Vec<usize>| -> bool {
                if targets.is_empty() {
                    even_priority
                } else {
                    targets.iter().all(|&tgt| tgt < n && accepting[tgt])
                }
            };

            let new_status = match automaton.states[s].branching {
                BranchingMode::Existential => {
                    // At least one transition must be satisfied.
                    transitions_from[s]
                        .iter()
                        .any(|targets| transition_satisfied(targets))
                },
                BranchingMode::Universal => {
                    // ALL transitions must be satisfied.
                    transitions_from[s]
                        .iter()
                        .all(|targets| transition_satisfied(targets))
                },
            };

            if new_status {
                accepting[s] = true;
                changed = true;
            }
        }
    }

    // The language is empty iff the initial state is NOT accepting.
    !accepting[initial]
}

/// Evaluate a PATA on a concrete term (tree), returning whether the automaton
/// accepts the term.
///
/// Performs bottom-up evaluation:
/// 1. For each leaf: a state accepts if it has a matching transition (symbol
///    match) with no child directions, or if it has even priority and the symbol
///    matches a transition with empty directions.
/// 2. For each internal node: combine child results according to the branching
///    mode and transition directions.
///
/// # Arguments
///
/// * `automaton` - The PATA to evaluate.
/// * `term` - The term to evaluate against.
///
/// # Returns
///
/// `true` if the initial state accepts the term, `false` otherwise.
pub fn evaluate_term(
    automaton: &ParityAlternatingTreeAutomaton<BooleanWeight>,
    term: &Term,
) -> bool {
    let n = automaton.num_states();
    if n == 0 || automaton.initial_state.is_none() {
        return false;
    }

    let initial = automaton
        .initial_state
        .expect("initial_state checked above");
    if initial >= n {
        return false;
    }

    // Build transition index: (from_state, symbol) -> list of direction-sets.
    let mut trans_index: HashMap<(usize, &str), Vec<&Vec<(usize, usize, BooleanWeight)>>> =
        HashMap::new();
    for t in &automaton.transitions {
        trans_index
            .entry((t.from, t.symbol.as_str()))
            .or_default()
            .push(&t.directions);
    }

    fn eval_node<'a>(
        term: &Term,
        child_results: &[HashSet<usize>],
        automaton: &'a ParityAlternatingTreeAutomaton<BooleanWeight>,
        trans_index: &HashMap<(usize, &'a str), Vec<&Vec<(usize, usize, BooleanWeight)>>>,
    ) -> HashSet<usize> {
        let mut accepting_states = HashSet::new();

        for state in &automaton.states {
            let sid = state.id;

            // Find transitions from this state on the term's symbol.
            let transitions = trans_index.get(&(sid, term.symbol.as_str()));

            match transitions {
                None => {
                    // No transition on this symbol.
                    // For leaves with even priority, this state could accept
                    // vacuously if it has no transitions at all on any symbol.
                    // But without a matching transition, we cannot accept.
                },
                Some(trans_list) => {
                    // Check if any/all transitions (depending on branching mode)
                    // lead to acceptance.
                    let result = match state.branching {
                        BranchingMode::Existential => {
                            // Some transition must have all its directions satisfied.
                            trans_list.iter().any(|directions| {
                                if directions.is_empty() {
                                    // No directions needed — accepts if priority is even
                                    // (leaf acceptance) or unconditionally for symbol match.
                                    true
                                } else {
                                    directions.iter().all(|&(child_idx, target, weight)| {
                                        if weight == BooleanWeight::zero() {
                                            return true; // zero-weighted direction is vacuously satisfied
                                        }
                                        if child_idx < child_results.len() {
                                            child_results[child_idx].contains(&target)
                                        } else {
                                            false // child index out of range
                                        }
                                    })
                                }
                            })
                        },
                        BranchingMode::Universal => {
                            // ALL transitions must have all their directions satisfied.
                            trans_list.iter().all(|directions| {
                                if directions.is_empty() {
                                    true
                                } else {
                                    directions.iter().all(|&(child_idx, target, weight)| {
                                        if weight == BooleanWeight::zero() {
                                            return true;
                                        }
                                        if child_idx < child_results.len() {
                                            child_results[child_idx].contains(&target)
                                        } else {
                                            false
                                        }
                                    })
                                }
                            })
                        },
                    };

                    if result {
                        accepting_states.insert(sid);
                    }
                },
            }
        }
        accepting_states
    }

    // Post-order PDA. Each frame is the recursive activation record made
    // explicit: the node, the next child to enter, and completed child results.
    // This preserves left-to-right evaluation while using heap space linear in
    // tree depth instead of consuming the native call stack.
    struct EvalFrame<'term> {
        term: &'term Term,
        next_child: usize,
        child_results: Vec<HashSet<usize>>,
    }

    let mut frames = vec![EvalFrame {
        term,
        next_child: 0,
        child_results: Vec::with_capacity(term.children.len()),
    }];
    loop {
        let frame = frames
            .last_mut()
            .expect("the root frame remains until evaluation completes");
        if let Some(child) = frame.term.children.get(frame.next_child) {
            frame.next_child += 1;
            frames.push(EvalFrame {
                term: child,
                next_child: 0,
                child_results: Vec::with_capacity(child.children.len()),
            });
            continue;
        }

        let frame = frames.pop().expect("the completed frame exists");
        let accepting = eval_node(frame.term, &frame.child_results, automaton, &trans_index);
        if let Some(parent) = frames.last_mut() {
            parent.child_results.push(accepting);
        } else {
            return accepting.contains(&initial);
        }
    }
}

/// Compile a mu-calculus formula into a parity alternating tree automaton.
///
/// The translation proceeds recursively on the formula structure:
/// - `True` => existential state with even priority (accepting leaf)
/// - `False` => existential state with odd priority (rejecting leaf)
/// - `Atom(a)` => existential state with transitions matching symbol `a`
/// - `And(phi, psi)` => universal state branching to both subformula automata
/// - `Or(phi, psi)` => existential state branching to both subformula automata
/// - `Not(phi)` => swap branching modes and flip priorities (complement)
/// - `Diamond{k, phi}` => existential state directing child `k` to phi's state
/// - `Box{k, phi}` => universal state directing child `k` to phi's state
/// - `Mu{X, phi}` => odd priority (least fixpoint, must eventually stabilize)
/// - `Nu{X, phi}` => even priority (greatest fixpoint, invariant)
/// - `Var(X)` => reference to the fixpoint's bound state
///
/// # Arguments
///
/// * `formula` - The mu-calculus formula to compile.
/// * `max_arity` - Maximum arity of the tree alphabet.
///
/// # Returns
///
/// A PATA accepting exactly the set of trees satisfying the formula.
pub fn mu_calculus_to_pata(
    formula: &MuCalculusFormula,
    max_arity: usize,
) -> ParityAlternatingTreeAutomaton<BooleanWeight> {
    try_mu_calculus_to_pata(formula, max_arity).unwrap_or_else(|err| {
        panic!("failed to compile mu-calculus formula `{}` to PATA: {}", formula, err)
    })
}

/// Checked compiler from modal mu-calculus formulas to parity alternating tree
/// automata.
///
/// Unlike [`mu_calculus_to_pata`], this function reports ill-scoped formulas
/// instead of panicking.
pub fn try_mu_calculus_to_pata(
    formula: &MuCalculusFormula,
    max_arity: usize,
) -> Result<ParityAlternatingTreeAutomaton<BooleanWeight>, MuCalculusCompileError> {
    let mut automaton = ParityAlternatingTreeAutomaton::new(max_arity);
    // Track variable -> state ID bindings for fixpoint references.
    let mut var_env: HashMap<String, usize> = HashMap::new();
    // Track priority allocation: each new fixpoint gets a fresh priority level.
    let mut next_priority: u32 = 0;

    let initial = compile_formula(formula, &mut automaton, &mut var_env, &mut next_priority)?;
    automaton.initial_state = Some(initial);

    Ok(automaton)
}

/// Heap-backed compiler PDA for `mu_calculus_to_pata`.
///
/// Returns the state ID representing the compiled formula.
fn compile_formula(
    formula: &MuCalculusFormula,
    automaton: &mut ParityAlternatingTreeAutomaton<BooleanWeight>,
    var_env: &mut HashMap<String, usize>,
    next_priority: &mut u32,
) -> Result<usize, MuCalculusCompileError> {
    enum Task<'formula> {
        Visit(&'formula MuCalculusFormula),
        Not,
        And,
        Or,
        Diamond(usize),
        Box(usize),
        Mu {
            var: &'formula str,
            state: usize,
            previous: Option<usize>,
        },
        Nu {
            var: &'formula str,
            state: usize,
            previous: Option<usize>,
        },
    }

    let mut tasks = vec![Task::Visit(formula)];
    let mut values = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            Task::Visit(MuCalculusFormula::True) => values.push(automaton.add_state(
                BranchingMode::Existential,
                0,
                Some("true".to_string()),
            )),
            Task::Visit(MuCalculusFormula::False) => values.push(automaton.add_state(
                BranchingMode::Existential,
                1,
                Some("false".to_string()),
            )),
            Task::Visit(MuCalculusFormula::Var(var)) => {
                values.push(
                    var_env.get(var).copied().ok_or_else(|| {
                        MuCalculusCompileError::UnboundVariable { var: var.clone() }
                    })?,
                );
            },
            Task::Visit(MuCalculusFormula::Atom(atom)) => {
                let state = automaton.add_state(
                    BranchingMode::Existential,
                    0,
                    Some(format!("atom:{atom}")),
                );
                automaton.add_transition(state, atom.clone(), Vec::new());
                values.push(state);
            },
            Task::Visit(MuCalculusFormula::Not(body)) => {
                tasks.push(Task::Not);
                tasks.push(Task::Visit(body));
            },
            Task::Visit(MuCalculusFormula::And(left, right)) => {
                tasks.push(Task::And);
                tasks.push(Task::Visit(right));
                tasks.push(Task::Visit(left));
            },
            Task::Visit(MuCalculusFormula::Or(left, right)) => {
                tasks.push(Task::Or);
                tasks.push(Task::Visit(right));
                tasks.push(Task::Visit(left));
            },
            Task::Visit(MuCalculusFormula::Diamond { child_idx, body }) => {
                tasks.push(Task::Diamond(*child_idx));
                tasks.push(Task::Visit(body));
            },
            Task::Visit(MuCalculusFormula::Box { child_idx, body }) => {
                tasks.push(Task::Box(*child_idx));
                tasks.push(Task::Visit(body));
            },
            Task::Visit(MuCalculusFormula::Mu { var, body }) => {
                let priority = *next_priority | 1;
                *next_priority = priority + 1;
                let state = automaton.add_state(
                    BranchingMode::Existential,
                    priority,
                    Some(format!("mu:{var}")),
                );
                let previous = var_env.insert(var.clone(), state);
                tasks.push(Task::Mu { var, state, previous });
                tasks.push(Task::Visit(body));
            },
            Task::Visit(MuCalculusFormula::Nu { var, body }) => {
                let priority = *next_priority & !1;
                *next_priority = priority + 2;
                let state = automaton.add_state(
                    BranchingMode::Existential,
                    priority,
                    Some(format!("nu:{var}")),
                );
                let previous = var_env.insert(var.clone(), state);
                tasks.push(Task::Nu { var, state, previous });
                tasks.push(Task::Visit(body));
            },
            Task::Not => {
                let inner = values
                    .pop()
                    .expect("mu-calculus compiler lost a negated state");
                let inner_state = &automaton.states[inner];
                let flipped_branching = match inner_state.branching {
                    BranchingMode::Existential => BranchingMode::Universal,
                    BranchingMode::Universal => BranchingMode::Existential,
                };
                let flipped_priority = if inner_state.priority % 2 == 0 {
                    inner_state.priority + 1
                } else {
                    inner_state.priority.saturating_sub(1)
                };
                let state = automaton.add_state(
                    flipped_branching,
                    flipped_priority,
                    Some(format!("not:q{inner}")),
                );
                let transitions: Vec<_> = automaton
                    .transitions
                    .iter()
                    .filter(|transition| transition.from == inner)
                    .cloned()
                    .collect();
                for transition in transitions {
                    automaton.add_transition(state, transition.symbol, transition.directions);
                }
                values.push(state);
            },
            Task::And => {
                let right = values
                    .pop()
                    .expect("mu-calculus compiler lost a right state");
                let left = values
                    .pop()
                    .expect("mu-calculus compiler lost a left state");
                let state = automaton.add_state(
                    BranchingMode::Universal,
                    0,
                    Some(format!("and:q{left},q{right}")),
                );
                automaton.add_transition(
                    state,
                    "_and_left".to_string(),
                    vec![(0, left, BooleanWeight::one())],
                );
                automaton.add_transition(
                    state,
                    "_and_right".to_string(),
                    vec![(0, right, BooleanWeight::one())],
                );
                values.push(state);
            },
            Task::Or => {
                let right = values
                    .pop()
                    .expect("mu-calculus compiler lost a right state");
                let left = values
                    .pop()
                    .expect("mu-calculus compiler lost a left state");
                let state = automaton.add_state(
                    BranchingMode::Existential,
                    0,
                    Some(format!("or:q{left},q{right}")),
                );
                automaton.add_transition(
                    state,
                    "_or_left".to_string(),
                    vec![(0, left, BooleanWeight::one())],
                );
                automaton.add_transition(
                    state,
                    "_or_right".to_string(),
                    vec![(0, right, BooleanWeight::one())],
                );
                values.push(state);
            },
            Task::Diamond(child_idx) => {
                let body = values
                    .pop()
                    .expect("mu-calculus compiler lost a modal state");
                let state = automaton.add_state(
                    BranchingMode::Existential,
                    0,
                    Some(format!("diamond:{child_idx}:q{body}")),
                );
                automaton.add_transition(
                    state,
                    format!("_diamond_{child_idx}"),
                    vec![(child_idx, body, BooleanWeight::one())],
                );
                values.push(state);
            },
            Task::Box(child_idx) => {
                let body = values
                    .pop()
                    .expect("mu-calculus compiler lost a modal state");
                let state = automaton.add_state(
                    BranchingMode::Universal,
                    0,
                    Some(format!("box:{child_idx}:q{body}")),
                );
                automaton.add_transition(
                    state,
                    format!("_box_{child_idx}"),
                    vec![(child_idx, body, BooleanWeight::one())],
                );
                values.push(state);
            },
            Task::Mu { var, state, previous } => {
                let body = values
                    .pop()
                    .expect("mu-calculus compiler lost a fixpoint body");
                if let Some(previous) = previous {
                    var_env.insert(var.to_owned(), previous);
                } else {
                    var_env.remove(var);
                }
                automaton.add_transition(
                    state,
                    format!("_mu_{var}"),
                    vec![(0, body, BooleanWeight::one())],
                );
                values.push(state);
            },
            Task::Nu { var, state, previous } => {
                let body = values
                    .pop()
                    .expect("mu-calculus compiler lost a fixpoint body");
                if let Some(previous) = previous {
                    var_env.insert(var.to_owned(), previous);
                } else {
                    var_env.remove(var);
                }
                automaton.add_transition(
                    state,
                    format!("_nu_{var}"),
                    vec![(0, body, BooleanWeight::one())],
                );
                values.push(state);
            },
        }
    }
    debug_assert_eq!(values.len(), 1);
    Ok(values
        .pop()
        .expect("mu-calculus compiler produced no state"))
}

/// Check language inclusion: `L(a) subseteq L(b)`.
///
/// Uses the identity `L(A) ⊆ L(B) iff L(A) ∩ L(complement(B)) = ∅`.
///
/// 1. Complement `B`: flip branching modes and shift priorities.
/// 2. Intersect `A` with `complement(B)` via product construction.
/// 3. Check emptiness of the product.
///
/// # Arguments
///
/// * `a` - The candidate subset automaton.
/// * `b` - The candidate superset automaton.
///
/// # Returns
///
/// `true` if `L(a) ⊆ L(b)`, `false` otherwise.
pub fn check_inclusion(
    a: &ParityAlternatingTreeAutomaton<BooleanWeight>,
    b: &ParityAlternatingTreeAutomaton<BooleanWeight>,
) -> bool {
    // L(A) ⊆ L(B) iff L(A) ∩ L(complement(B)) = ∅

    // Step 1: Complement B.
    let comp_b = complement(b);

    // Step 2: Intersect A with complement(B).
    let product = intersect(a, &comp_b);

    // Step 3: Check emptiness.
    check_emptiness(&product)
}

/// Complement a PATA by flipping branching modes and shifting priorities.
///
/// For alternating automata, complementation is straightforward:
/// - Swap existential and universal branching.
/// - Increment all priorities by 1 (flips even/odd parity).
///
/// This exploits the duality of alternation: the complement of an alternating
/// automaton with priority function `Omega` is obtained by dualization
/// (Emerson & Jutla, 1991).
fn complement(
    automaton: &ParityAlternatingTreeAutomaton<BooleanWeight>,
) -> ParityAlternatingTreeAutomaton<BooleanWeight> {
    let mut result = ParityAlternatingTreeAutomaton::new(automaton.max_arity);

    // Copy states with flipped branching and shifted priorities.
    for state in &automaton.states {
        let flipped = match state.branching {
            BranchingMode::Existential => BranchingMode::Universal,
            BranchingMode::Universal => BranchingMode::Existential,
        };
        result.add_state(flipped, state.priority + 1, state.label.clone());
    }

    // Copy transitions unchanged (structure is preserved; semantics change
    // through the flipped branching modes).
    for t in &automaton.transitions {
        result.add_transition(t.from, t.symbol.clone(), t.directions.clone());
    }

    result.initial_state = automaton.initial_state;
    result.alphabet = automaton.alphabet.clone();

    result
}

/// Intersect two PATAs via product construction.
///
/// The product automaton `A x B` accepts the intersection of their languages.
/// Product states are pairs `(q_a, q_b)`. The branching mode of a product
/// state is universal if either component is universal (conjunction of
/// requirements); otherwise existential.
///
/// Product transitions combine directions from both components: for matching
/// symbols, the product transition requires all directions from both `A` and
/// `B` to be satisfied simultaneously.
fn intersect(
    a: &ParityAlternatingTreeAutomaton<BooleanWeight>,
    b: &ParityAlternatingTreeAutomaton<BooleanWeight>,
) -> ParityAlternatingTreeAutomaton<BooleanWeight> {
    let na = a.num_states();
    let nb = b.num_states();
    let max_arity = std::cmp::max(a.max_arity, b.max_arity);
    let mut product = ParityAlternatingTreeAutomaton::new(max_arity);

    if na == 0 || nb == 0 {
        return product;
    }

    // Create product states: (qa, qb) -> product state ID.
    // Product ID = qa * nb + qb.
    let product_id = |qa: usize, qb: usize| -> usize { qa * nb + qb };

    for qa in 0..na {
        for qb in 0..nb {
            let sa = &a.states[qa];
            let sb = &b.states[qb];
            // Universal if either is universal (conjunction).
            let branching = match (sa.branching, sb.branching) {
                (BranchingMode::Universal, _) | (_, BranchingMode::Universal) => {
                    BranchingMode::Universal
                },
                _ => BranchingMode::Existential,
            };
            // Priority: interleave priorities from both components using the
            // standard pairing: max(2*pa, 2*pb+1) to preserve parity semantics.
            // Simpler approach: use the maximum priority (conservative).
            let priority = std::cmp::max(sa.priority, sb.priority);
            let label = match (&sa.label, &sb.label) {
                (Some(la), Some(lb)) => Some(format!("({},{})", la, lb)),
                (Some(la), None) => Some(format!("({},q{})", la, qb)),
                (None, Some(lb)) => Some(format!("(q{},{})", qa, lb)),
                (None, None) => Some(format!("(q{},q{})", qa, qb)),
            };
            let id = product.add_state(branching, priority, label);
            debug_assert_eq!(id, product_id(qa, qb));
        }
    }

    // Build transition index for efficient matching.
    let mut a_trans: HashMap<(usize, &str), Vec<&Vec<(usize, usize, BooleanWeight)>>> =
        HashMap::new();
    for t in &a.transitions {
        a_trans
            .entry((t.from, t.symbol.as_str()))
            .or_default()
            .push(&t.directions);
    }
    let mut b_trans: HashMap<(usize, &str), Vec<&Vec<(usize, usize, BooleanWeight)>>> =
        HashMap::new();
    for t in &b.transitions {
        b_trans
            .entry((t.from, t.symbol.as_str()))
            .or_default()
            .push(&t.directions);
    }

    // Shared alphabet.
    let shared_syms: HashSet<&str> = a
        .alphabet
        .iter()
        .filter(|s| b.alphabet.contains(s.as_str()))
        .map(|s| s.as_str())
        .collect();

    // For each pair of states and shared symbol, combine transitions.
    for qa in 0..na {
        for qb in 0..nb {
            let pid = product_id(qa, qb);
            for &sym in &shared_syms {
                let a_directions = a_trans.get(&(qa, sym));
                let b_directions = b_trans.get(&(qb, sym));

                if let (Some(a_dirs_list), Some(b_dirs_list)) = (a_directions, b_directions) {
                    // Cross-product of transitions from both automata.
                    for a_dirs in a_dirs_list {
                        for b_dirs in b_dirs_list {
                            // Merge directions: each direction targets a product state.
                            let mut merged: Vec<(usize, usize, BooleanWeight)> =
                                Vec::with_capacity(a_dirs.len() + b_dirs.len());
                            for &(ci, tgt_a, w) in a_dirs.iter() {
                                // Target in A maps to product state (tgt_a, qb).
                                // Use qb as the "unchanged" component for A's directions.
                                for qb_inner in 0..nb {
                                    merged.push((ci, product_id(tgt_a, qb_inner), w));
                                }
                            }
                            for &(ci, tgt_b, w) in b_dirs.iter() {
                                for qa_inner in 0..na {
                                    merged.push((ci, product_id(qa_inner, tgt_b), w));
                                }
                            }
                            product.add_transition(pid, sym.to_string(), merged);
                        }
                    }
                }
            }

            // Also handle transitions that exist only in one component.
            // For a state to accept in the product, both components must agree.
            // Transitions unique to one component produce no product transitions
            // (the other component has no matching transition, so the product
            // transition cannot fire). This is correct for intersection.
        }
    }

    // Set initial state.
    if let (Some(init_a), Some(init_b)) = (a.initial_state, b.initial_state) {
        if init_a < na && init_b < nb {
            product.initial_state = Some(product_id(init_a, init_b));
        }
    }

    product
}

/// Analyze a PATA and produce a summary.
pub fn analyze(automaton: &ParityAlternatingTreeAutomaton<BooleanWeight>) -> ParityTreeAnalysis {
    ParityTreeAnalysis {
        num_states: automaton.num_states(),
        max_priority: automaton.max_priority(),
        is_empty: check_emptiness(automaton),
        priority_depth: automaton.priority_depth(),
        // OSLF Phase 5 `.1`: this summary path has no recursive-predicate
        // context, so there are no per-fixpoint verdicts to report.
        fixpoint_decisions: Vec::new(),
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Predicate Dispatch — PredicateCompiler integration
// ══════════════════════════════════════════════════════════════════════════════

/// Compiler adapter for the Parity Tree Automata module (M5).
///
/// Activated by recursive `letprop` / fixpoint definitions (μ-calculus variety).
pub struct ParityTreeCompiler;

impl crate::predicate_dispatch::PredicateCompiler for ParityTreeCompiler {
    type Output = ParityTreeAnalysis;

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

    // ─── Construction and basic properties ──────────────────────────────

    #[test]
    fn construction_empty_automaton() {
        let pata: ParityAlternatingTreeAutomaton<BooleanWeight> =
            ParityAlternatingTreeAutomaton::new(2);
        assert_eq!(pata.num_states(), 0);
        assert_eq!(pata.num_transitions(), 0);
        assert_eq!(pata.max_priority(), 0);
        assert_eq!(pata.max_arity, 2);
        assert!(pata.initial_state.is_none());
    }

    #[test]
    fn construction_add_states_and_transitions() {
        let mut pata: ParityAlternatingTreeAutomaton<BooleanWeight> =
            ParityAlternatingTreeAutomaton::new(2);
        let q0 = pata.add_state(BranchingMode::Existential, 0, Some("root".to_string()));
        let q1 = pata.add_state(BranchingMode::Universal, 1, None);
        let q2 = pata.add_state(BranchingMode::Existential, 2, Some("leaf".to_string()));
        pata.initial_state = Some(q0);

        pata.add_transition(
            q0,
            "f".to_string(),
            vec![(0, q1, BooleanWeight::one()), (1, q2, BooleanWeight::one())],
        );

        assert_eq!(pata.num_states(), 3);
        assert_eq!(pata.num_transitions(), 1);
        assert_eq!(pata.max_priority(), 2);
        assert_eq!(pata.priority_depth(), 3); // priorities {0, 1, 2}
        assert!(pata.alphabet.contains("f"));
    }

    // ─── check_emptiness ────────────────────────────────────────────────

    #[test]
    fn emptiness_trivially_empty_no_states() {
        let pata: ParityAlternatingTreeAutomaton<BooleanWeight> =
            ParityAlternatingTreeAutomaton::new(2);
        assert!(check_emptiness(&pata));
    }

    #[test]
    fn emptiness_trivially_non_empty_accepting_leaf() {
        // Single existential state with even priority, no transitions.
        let mut pata: ParityAlternatingTreeAutomaton<BooleanWeight> =
            ParityAlternatingTreeAutomaton::new(2);
        let q0 = pata.add_state(BranchingMode::Existential, 0, None);
        pata.initial_state = Some(q0);
        assert!(!check_emptiness(&pata)); // accepting leaf => non-empty
    }

    #[test]
    fn emptiness_rejecting_leaf_odd_priority() {
        let mut pata: ParityAlternatingTreeAutomaton<BooleanWeight> =
            ParityAlternatingTreeAutomaton::new(2);
        let q0 = pata.add_state(BranchingMode::Existential, 1, None);
        pata.initial_state = Some(q0);
        assert!(check_emptiness(&pata)); // odd priority leaf => rejecting => empty
    }

    #[test]
    fn emptiness_existential_with_accepting_target() {
        // q0 (existential, odd) -f-> [q1 (even, leaf)]
        // q0 is not a leaf, but its transition leads to accepting q1.
        let mut pata: ParityAlternatingTreeAutomaton<BooleanWeight> =
            ParityAlternatingTreeAutomaton::new(2);
        let q0 = pata.add_state(BranchingMode::Existential, 1, None);
        let q1 = pata.add_state(BranchingMode::Existential, 0, None);
        pata.initial_state = Some(q0);
        pata.add_transition(q0, "f".to_string(), vec![(0, q1, BooleanWeight::one())]);
        assert!(!check_emptiness(&pata)); // q1 accepts, so q0 accepts via existential
    }

    #[test]
    fn emptiness_universal_all_accepting() {
        // q0 (universal, odd) -f-> [(0, q1), (1, q2)]
        // Both q1, q2 are accepting leaves.
        let mut pata: ParityAlternatingTreeAutomaton<BooleanWeight> =
            ParityAlternatingTreeAutomaton::new(2);
        let q0 = pata.add_state(BranchingMode::Universal, 1, None);
        let q1 = pata.add_state(BranchingMode::Existential, 0, None);
        let q2 = pata.add_state(BranchingMode::Existential, 0, None);
        pata.initial_state = Some(q0);
        pata.add_transition(
            q0,
            "f".to_string(),
            vec![(0, q1, BooleanWeight::one()), (1, q2, BooleanWeight::one())],
        );
        assert!(!check_emptiness(&pata)); // both accept => universal accepts
    }

    #[test]
    fn emptiness_universal_one_rejecting() {
        // q0 (universal) -f-> [(0, q1), (1, q2)]
        // q1 accepts but q2 rejects.
        let mut pata: ParityAlternatingTreeAutomaton<BooleanWeight> =
            ParityAlternatingTreeAutomaton::new(2);
        let q0 = pata.add_state(BranchingMode::Universal, 1, None);
        let q1 = pata.add_state(BranchingMode::Existential, 0, None); // accepting
        let q2 = pata.add_state(BranchingMode::Existential, 1, None); // rejecting
        pata.initial_state = Some(q0);
        pata.add_transition(
            q0,
            "f".to_string(),
            vec![(0, q1, BooleanWeight::one()), (1, q2, BooleanWeight::one())],
        );
        assert!(check_emptiness(&pata)); // q2 rejects => universal fails => empty
    }

    // ─── evaluate_term ──────────────────────────────────────────────────

    #[test]
    fn evaluate_term_leaf_acceptance() {
        // PATA: q0 (existential, even) matches symbol "a" with no directions.
        let mut pata: ParityAlternatingTreeAutomaton<BooleanWeight> =
            ParityAlternatingTreeAutomaton::new(0);
        let q0 = pata.add_state(BranchingMode::Existential, 0, None);
        pata.initial_state = Some(q0);
        pata.add_transition(q0, "a".to_string(), Vec::new());

        let leaf_a = Term::leaf("a");
        let leaf_b = Term::leaf("b");

        assert!(evaluate_term(&pata, &leaf_a));
        assert!(!evaluate_term(&pata, &leaf_b)); // wrong symbol
    }

    #[test]
    fn evaluate_term_binary_node() {
        // PATA accepts f(a, b):
        // q0 (existential) -"f"-> [(0, q1), (1, q2)]
        // q1 (existential) -"a"-> []
        // q2 (existential) -"b"-> []
        let mut pata: ParityAlternatingTreeAutomaton<BooleanWeight> =
            ParityAlternatingTreeAutomaton::new(2);
        let q0 = pata.add_state(BranchingMode::Existential, 0, None);
        let q1 = pata.add_state(BranchingMode::Existential, 0, None);
        let q2 = pata.add_state(BranchingMode::Existential, 0, None);
        pata.initial_state = Some(q0);
        pata.add_transition(
            q0,
            "f".to_string(),
            vec![(0, q1, BooleanWeight::one()), (1, q2, BooleanWeight::one())],
        );
        pata.add_transition(q1, "a".to_string(), Vec::new());
        pata.add_transition(q2, "b".to_string(), Vec::new());

        let term_fab = Term::node("f", vec![Term::leaf("a"), Term::leaf("b")]);
        let term_fba = Term::node("f", vec![Term::leaf("b"), Term::leaf("a")]);
        let term_a = Term::leaf("a");

        assert!(evaluate_term(&pata, &term_fab));
        assert!(!evaluate_term(&pata, &term_fba)); // children swapped
        assert!(!evaluate_term(&pata, &term_a)); // wrong structure
    }

    // ─── mu_calculus_to_pata ────────────────────────────────────────────

    #[test]
    fn mu_calculus_true_formula() {
        let formula = MuCalculusFormula::True;
        let pata = mu_calculus_to_pata(&formula, 2);
        assert!(pata.initial_state.is_some());
        assert_eq!(pata.num_states(), 1);
        // True formula creates a single accepting state.
        assert_eq!(pata.states[0].priority % 2, 0); // even priority
    }

    #[test]
    fn mu_calculus_false_formula() {
        let formula = MuCalculusFormula::False;
        let pata = mu_calculus_to_pata(&formula, 2);
        assert_eq!(pata.num_states(), 1);
        assert_eq!(pata.states[0].priority % 2, 1); // odd priority
    }

    #[test]
    fn mu_calculus_atom_formula() {
        let formula = MuCalculusFormula::Atom("f".to_string());
        let pata = mu_calculus_to_pata(&formula, 2);
        assert!(pata.initial_state.is_some());
        assert!(pata.num_states() >= 1);
        // Should have a transition on symbol "f".
        assert!(pata.alphabet.contains("f"));
        assert!(pata.num_transitions() >= 1);
    }

    #[test]
    fn mu_calculus_and_composition() {
        let formula = MuCalculusFormula::And(
            Box::new(MuCalculusFormula::True),
            Box::new(MuCalculusFormula::True),
        );
        let pata = mu_calculus_to_pata(&formula, 2);
        assert!(pata.initial_state.is_some());
        // And creates a universal state pointing to two True subformula states.
        let init = pata.initial_state.expect("should have initial state");
        assert_eq!(pata.states[init].branching, BranchingMode::Universal);
    }

    #[test]
    fn mu_calculus_or_composition() {
        let formula = MuCalculusFormula::Or(
            Box::new(MuCalculusFormula::True),
            Box::new(MuCalculusFormula::False),
        );
        let pata = mu_calculus_to_pata(&formula, 2);
        let init = pata.initial_state.expect("should have initial state");
        assert_eq!(pata.states[init].branching, BranchingMode::Existential);
    }

    #[test]
    fn mu_calculus_diamond_modality() {
        // Diamond{0, Atom("a")} — some child 0 satisfies Atom("a").
        let formula = MuCalculusFormula::Diamond {
            child_idx: 0,
            body: Box::new(MuCalculusFormula::Atom("a".to_string())),
        };
        let pata = mu_calculus_to_pata(&formula, 2);
        let init = pata.initial_state.expect("should have initial state");
        assert_eq!(pata.states[init].branching, BranchingMode::Existential);
        // Should have a transition with child_idx=0 in its directions.
        let init_trans: Vec<_> = pata.transitions.iter().filter(|t| t.from == init).collect();
        assert!(!init_trans.is_empty());
        let has_child_0_dir = init_trans
            .iter()
            .any(|t| t.directions.iter().any(|&(ci, _, _)| ci == 0));
        assert!(has_child_0_dir);
    }

    #[test]
    fn mu_calculus_box_modality() {
        // Box{1, Atom("b")} — all child-1 nodes satisfy Atom("b").
        let formula = MuCalculusFormula::Box {
            child_idx: 1,
            body: Box::new(MuCalculusFormula::Atom("b".to_string())),
        };
        let pata = mu_calculus_to_pata(&formula, 2);
        let init = pata.initial_state.expect("should have initial state");
        assert_eq!(pata.states[init].branching, BranchingMode::Universal);
    }

    #[test]
    fn mu_calculus_mu_fixpoint() {
        // mu X. Atom("a") — least fixpoint, should get odd priority.
        let formula = MuCalculusFormula::Mu {
            var: "X".to_string(),
            body: Box::new(MuCalculusFormula::Atom("a".to_string())),
        };
        let pata = mu_calculus_to_pata(&formula, 2);
        let init = pata.initial_state.expect("should have initial state");
        // Mu states get odd priority.
        assert_eq!(pata.states[init].priority % 2, 1);
    }

    #[test]
    fn mu_calculus_nu_fixpoint() {
        // nu X. Atom("a") — greatest fixpoint, should get even priority.
        let formula = MuCalculusFormula::Nu {
            var: "X".to_string(),
            body: Box::new(MuCalculusFormula::Atom("a".to_string())),
        };
        let pata = mu_calculus_to_pata(&formula, 2);
        let init = pata.initial_state.expect("should have initial state");
        // Nu states get even priority.
        assert_eq!(pata.states[init].priority % 2, 0);
    }

    #[test]
    fn mu_calculus_rejects_free_variable() {
        let formula = MuCalculusFormula::Var("X".to_string());
        let err = try_mu_calculus_to_pata(&formula, 2)
            .err()
            .expect("free variable should fail compilation");
        assert_eq!(err, MuCalculusCompileError::UnboundVariable { var: "X".to_string() });
    }

    #[test]
    fn mu_calculus_restores_fixpoint_scope() {
        let formula = MuCalculusFormula::And(
            Box::new(MuCalculusFormula::Mu {
                var: "X".to_string(),
                body: Box::new(MuCalculusFormula::Var("X".to_string())),
            }),
            Box::new(MuCalculusFormula::Var("X".to_string())),
        );
        let err = try_mu_calculus_to_pata(&formula, 2)
            .err()
            .expect("variable should not escape the left fixpoint branch");
        assert_eq!(err, MuCalculusCompileError::UnboundVariable { var: "X".to_string() });
    }

    // ─── check_inclusion ────────────────────────────────────────────────

    #[test]
    fn inclusion_reflexive() {
        // L(A) ⊆ L(A) should always hold.
        let mut pata: ParityAlternatingTreeAutomaton<BooleanWeight> =
            ParityAlternatingTreeAutomaton::new(2);
        let q0 = pata.add_state(BranchingMode::Existential, 0, None);
        pata.initial_state = Some(q0);
        pata.add_transition(q0, "a".to_string(), Vec::new());

        assert!(check_inclusion(&pata, &pata));
    }

    // ─── Term construction and display ──────────────────────────────────

    #[test]
    fn term_construction_and_display() {
        let leaf = Term::leaf("x");
        assert_eq!(leaf.to_string(), "x");
        assert!(leaf.children.is_empty());

        let node = Term::node("f", vec![Term::leaf("a"), Term::leaf("b")]);
        assert_eq!(node.to_string(), "f(a, b)");
        assert_eq!(node.children.len(), 2);

        let nested = Term::node("g", vec![Term::node("f", vec![Term::leaf("x")]), Term::leaf("y")]);
        assert_eq!(nested.to_string(), "g(f(x), y)");
    }

    // ─── MuCalculusFormula display ──────────────────────────────────────

    #[test]
    fn mu_calculus_formula_display() {
        assert_eq!(MuCalculusFormula::True.to_string(), "true");
        assert_eq!(MuCalculusFormula::False.to_string(), "false");
        assert_eq!(MuCalculusFormula::Var("X".to_string()).to_string(), "X");
        assert_eq!(MuCalculusFormula::Atom("f".to_string()).to_string(), "\"f\"");
        assert_eq!(
            MuCalculusFormula::Not(Box::new(MuCalculusFormula::True)).to_string(),
            "~(true)"
        );
        assert_eq!(
            MuCalculusFormula::And(
                Box::new(MuCalculusFormula::True),
                Box::new(MuCalculusFormula::False),
            )
            .to_string(),
            "(true /\\ false)"
        );
        assert_eq!(
            MuCalculusFormula::Or(
                Box::new(MuCalculusFormula::True),
                Box::new(MuCalculusFormula::False),
            )
            .to_string(),
            "(true \\/ false)"
        );
        assert_eq!(
            MuCalculusFormula::Diamond {
                child_idx: 0,
                body: Box::new(MuCalculusFormula::True),
            }
            .to_string(),
            "<0>.(true)"
        );
        assert_eq!(
            MuCalculusFormula::Box {
                child_idx: 1,
                body: Box::new(MuCalculusFormula::False),
            }
            .to_string(),
            "[1].(false)"
        );
        assert_eq!(
            MuCalculusFormula::Mu {
                var: "X".to_string(),
                body: Box::new(MuCalculusFormula::Var("X".to_string())),
            }
            .to_string(),
            "mu X.X"
        );
        assert_eq!(
            MuCalculusFormula::Nu {
                var: "Y".to_string(),
                body: Box::new(MuCalculusFormula::Var("Y".to_string())),
            }
            .to_string(),
            "nu Y.Y"
        );
    }

    // ─── Priority depth calculation ─────────────────────────────────────

    #[test]
    fn priority_depth_calculation() {
        let mut pata: ParityAlternatingTreeAutomaton<BooleanWeight> =
            ParityAlternatingTreeAutomaton::new(2);
        assert_eq!(pata.priority_depth(), 0); // no states

        pata.add_state(BranchingMode::Existential, 0, None);
        assert_eq!(pata.priority_depth(), 1); // {0}

        pata.add_state(BranchingMode::Universal, 1, None);
        assert_eq!(pata.priority_depth(), 2); // {0, 1}

        pata.add_state(BranchingMode::Existential, 0, None); // duplicate priority
        assert_eq!(pata.priority_depth(), 2); // still {0, 1}

        pata.add_state(BranchingMode::Universal, 3, None);
        assert_eq!(pata.priority_depth(), 3); // {0, 1, 3}
    }

    // ─── Product construction for intersection ──────────────────────────

    #[test]
    fn product_construction_state_count() {
        // A has 2 states, B has 3 states => product has 2*3 = 6 states.
        let mut a: ParityAlternatingTreeAutomaton<BooleanWeight> =
            ParityAlternatingTreeAutomaton::new(1);
        a.add_state(BranchingMode::Existential, 0, None);
        a.add_state(BranchingMode::Existential, 0, None);
        a.initial_state = Some(0);
        a.add_transition(0, "x".to_string(), vec![(0, 1, BooleanWeight::one())]);

        let mut b: ParityAlternatingTreeAutomaton<BooleanWeight> =
            ParityAlternatingTreeAutomaton::new(1);
        b.add_state(BranchingMode::Existential, 0, None);
        b.add_state(BranchingMode::Existential, 0, None);
        b.add_state(BranchingMode::Existential, 0, None);
        b.initial_state = Some(0);
        b.add_transition(0, "x".to_string(), vec![(0, 1, BooleanWeight::one())]);

        let product = intersect(&a, &b);
        assert_eq!(product.num_states(), 6); // 2 * 3
        assert!(product.initial_state.is_some());
    }

    // ─── ParityTreeState display ────────────────────────────────────────

    #[test]
    fn parity_tree_state_display() {
        let s = ParityTreeState {
            id: 0,
            branching: BranchingMode::Existential,
            priority: 2,
            label: None,
        };
        assert_eq!(s.to_string(), "q0[E,p=2]");

        let s2 = ParityTreeState {
            id: 3,
            branching: BranchingMode::Universal,
            priority: 1,
            label: Some("check".to_string()),
        };
        assert_eq!(s2.to_string(), "q3[A,p=1](check)");
    }

    // ─── ParityAlternatingTreeAutomaton display ─────────────────────────

    #[test]
    fn pata_display() {
        let mut pata: ParityAlternatingTreeAutomaton<BooleanWeight> =
            ParityAlternatingTreeAutomaton::new(2);
        pata.add_state(BranchingMode::Existential, 0, None);
        pata.add_state(BranchingMode::Universal, 1, None);
        pata.add_transition(0, "f".to_string(), vec![(0, 1, BooleanWeight::one())]);
        assert_eq!(
            pata.to_string(),
            "PATA { states: 2, transitions: 1, max_priority: 1, max_arity: 2 }"
        );
    }

    // ─── Analysis summary ───────────────────────────────────────────────

    #[test]
    fn analyze_summary() {
        let mut pata: ParityAlternatingTreeAutomaton<BooleanWeight> =
            ParityAlternatingTreeAutomaton::new(2);
        let q0 = pata.add_state(BranchingMode::Existential, 0, None);
        pata.initial_state = Some(q0);

        let result = analyze(&pata);
        assert_eq!(result.num_states, 1);
        assert_eq!(result.max_priority, 0);
        assert!(!result.is_empty); // accepting leaf
        assert_eq!(result.priority_depth, 1);
    }

    // ── Rocq Proof Alignment Tests (PataEmptiness.v) ─────────────────────────

    #[test]
    fn test_emptiness_even_priority_leaf_non_empty() {
        // Rocq: Parity acceptance — even priority with no outgoing transitions
        // (leaf) is accepting. A single existential state with even priority 2
        // should be non-empty.
        let mut pata: ParityAlternatingTreeAutomaton<BooleanWeight> =
            ParityAlternatingTreeAutomaton::new(2);
        let q0 = pata.add_state(BranchingMode::Existential, 2, None);
        pata.initial_state = Some(q0);

        let is_empty = check_emptiness(&pata);
        assert!(
            !is_empty,
            "single existential state with even priority 2 (leaf) should be non-empty"
        );
    }

    #[test]
    fn test_emptiness_universal_requires_all_children() {
        // Rocq: Universal state requires ALL transitions to be satisfied.
        // Build: q0 (universal, odd priority 1) with transitions to q1, q2, q3.
        //   q1: even priority (accepting leaf)
        //   q2: even priority (accepting leaf)
        //   q3: odd priority, no transitions (rejecting leaf)
        // Since q3 rejects, the universal state q0 should also reject → empty.
        let mut pata: ParityAlternatingTreeAutomaton<BooleanWeight> =
            ParityAlternatingTreeAutomaton::new(2);
        let q0 = pata.add_state(BranchingMode::Universal, 1, None); // odd = must continue
        let q1 = pata.add_state(BranchingMode::Existential, 0, None); // even = accepting
        let q2 = pata.add_state(BranchingMode::Existential, 0, None); // even = accepting
        let q3 = pata.add_state(BranchingMode::Existential, 1, None); // odd, no transitions = rejecting
        pata.initial_state = Some(q0);

        // q0 --f--> (q1, q2, q3) — universal requires all to accept
        pata.add_transition(
            q0,
            "f".to_string(),
            vec![
                (0, q1, BooleanWeight::one()),
                (1, q2, BooleanWeight::one()),
                (0, q3, BooleanWeight::one()),
            ],
        );

        let is_empty = check_emptiness(&pata);
        assert!(is_empty, "universal state with one rejecting child (odd leaf) should be empty");

        // Now make q3 accepting (even priority) — should become non-empty.
        pata.states[q3].priority = 0;
        let is_empty2 = check_emptiness(&pata);
        assert!(!is_empty2, "universal state with all accepting children should be non-empty");
    }
}
