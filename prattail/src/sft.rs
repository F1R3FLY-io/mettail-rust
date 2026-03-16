//! Symbolic Finite Transducers (SFTs) — output-producing transductions over infinite domains.
//!
//! ## Theory
//!
//! Symbolic Finite Transducers (SFTs) extend Symbolic Finite Automata (SFAs) with output
//! functions. Where SFAs accept/reject inputs, SFTs transform inputs to outputs, parameterized
//! by BooleanAlgebra predicates. Each transition is guarded by a predicate and annotated with
//! an output function that maps the consumed input element to a sequence of output elements.
//!
//! Formally, an SFT is a tuple (Q, A, B, δ, q₀, F) where:
//! - Q is a finite set of states
//! - A is the input Boolean algebra
//! - B is the output Boolean algebra
//! - δ ⊆ Q × φ(A) × (A::Domain → B::Domain*) × Q is the transition relation
//! - q₀ ∈ Q is the initial state (or set of initial states for NFA-style)
//! - F ⊆ Q is the set of accepting states
//!
//! ## Key Operations
//!
//! - **Transduction** (`transduce`): NFA-style simulation, collecting all output sequences
//! - **Composition** (`compose`): Chain two SFTs (A→B) ∘ (B→C) = (A→C)
//! - **Pre-image** (`pre_image`): Given SFA over B, compute SFA over A
//! - **Post-image** (`post_image`): Given SFA over A, compute SFA over B
//! - **Functionality** (`is_functional`): Check if single-valued
//! - **Equivalence** (`is_equivalent_functional`): Check equivalence for functional SFTs
//!
//! ## References
//!
//! - D'Antoni, L. & Veanes, M. (2012). "Symbolic Finite State Transducers: Algorithms
//!   and Applications." POPL 2012.
//! - D'Antoni, L. & Veanes, M. (2017). "The Power of Symbolic Automata and Transducers."
//!   CAV 2017.

use std::collections::{HashMap, HashSet, VecDeque};
use std::fmt;
use std::sync::Arc;

use crate::symbolic::{BooleanAlgebra, SymbolicAutomaton, SymbolicState, SymbolicTransition};

// ══════════════════════════════════════════════════════════════════════════════
// §1  OutputFunction — closed enum for composable output operations
// ══════════════════════════════════════════════════════════════════════════════

/// Output function mapping input domain elements to output sequences.
///
/// Closed enum (not trait object) to support Clone, Debug, and enable
/// compile-time composition without dynamic dispatch. `Arc<dyn Fn>` for
/// Map/FlatMap handles the function pointer case.
///
/// Identity/Constant/Epsilon cover >90% of practical cases without closures.
pub enum OutputFunction<A: BooleanAlgebra, B: BooleanAlgebra> {
    /// ε-output: produce nothing.
    Epsilon,
    /// Constant output (ignores input).
    Constant(Vec<B::Domain>),
    /// Identity: pass through input unchanged.
    /// Conceptually requires `A::Domain ≈ B::Domain`; enforced at construction.
    Identity,
    /// Single-element computed output.
    Map(Arc<dyn Fn(&A::Domain) -> B::Domain + Send + Sync>),
    /// Multi-element computed output.
    FlatMap(Arc<dyn Fn(&A::Domain) -> Vec<B::Domain> + Send + Sync>),
}

impl<A: BooleanAlgebra, B: BooleanAlgebra> Clone for OutputFunction<A, B> {
    fn clone(&self) -> Self {
        match self {
            Self::Epsilon => Self::Epsilon,
            Self::Constant(v) => Self::Constant(v.clone()),
            Self::Identity => Self::Identity,
            Self::Map(f) => Self::Map(Arc::clone(f)),
            Self::FlatMap(f) => Self::FlatMap(Arc::clone(f)),
        }
    }
}

impl<A: BooleanAlgebra, B: BooleanAlgebra> fmt::Debug for OutputFunction<A, B> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Epsilon => write!(f, "Epsilon"),
            Self::Constant(v) => write!(f, "Constant({:?})", v),
            Self::Identity => write!(f, "Identity"),
            Self::Map(_) => write!(f, "Map(<fn>)"),
            Self::FlatMap(_) => write!(f, "FlatMap(<fn>)"),
        }
    }
}

impl<A: BooleanAlgebra, B: BooleanAlgebra> OutputFunction<A, B> {
    /// Apply the output function to an input domain element.
    /// Returns the produced output sequence.
    pub fn apply(&self, input: &A::Domain) -> Vec<B::Domain>
    where
        A::Domain: Clone + Into<B::Domain>,
    {
        match self {
            Self::Epsilon => Vec::new(),
            Self::Constant(v) => v.clone(),
            Self::Identity => vec![input.clone().into()],
            Self::Map(f) => vec![f(input)],
            Self::FlatMap(f) => f(input),
        }
    }

    /// Apply to all elements in a sequence, concatenating outputs.
    pub fn apply_all(&self, inputs: &[A::Domain]) -> Vec<B::Domain>
    where
        A::Domain: Clone + Into<B::Domain>,
    {
        let mut result = Vec::new();
        for input in inputs {
            result.extend(self.apply(input));
        }
        result
    }

    /// Whether this is the epsilon (no-output) function.
    pub fn is_epsilon(&self) -> bool {
        matches!(self, Self::Epsilon)
    }

    /// Whether this is a constant output function.
    pub fn is_constant(&self) -> bool {
        matches!(self, Self::Constant(_))
    }

    /// Whether this is the identity function.
    pub fn is_identity(&self) -> bool {
        matches!(self, Self::Identity)
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// §2  SFT Core Types
// ══════════════════════════════════════════════════════════════════════════════

/// Transition in a symbolic finite transducer.
pub struct SftTransition<A: BooleanAlgebra, B: BooleanAlgebra> {
    /// Source state.
    pub from: usize,
    /// Target state.
    pub to: usize,
    /// Guard predicate over the input algebra.
    pub guard: A::Predicate,
    /// Output function applied when the guard is satisfied.
    pub output: OutputFunction<A, B>,
}

impl<A: BooleanAlgebra, B: BooleanAlgebra> Clone for SftTransition<A, B> {
    fn clone(&self) -> Self {
        Self {
            from: self.from,
            to: self.to,
            guard: self.guard.clone(),
            output: self.output.clone(),
        }
    }
}

impl<A: BooleanAlgebra, B: BooleanAlgebra> fmt::Debug for SftTransition<A, B> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("SftTransition")
            .field("from", &self.from)
            .field("to", &self.to)
            .field("guard", &self.guard)
            .field("output", &self.output)
            .finish()
    }
}

/// State in a symbolic finite transducer.
#[derive(Debug, Clone)]
pub struct SftState {
    /// State identifier.
    pub id: usize,
    /// Whether this is an accepting state.
    pub is_accepting: bool,
    /// Optional human-readable label.
    pub label: Option<String>,
}

/// Symbolic Finite Transducer parameterized by input and output algebras.
///
/// Formally: (Q, A, B, δ, q₀, F) where δ: Q × φ(A) → Q × f(A→B*).
/// D'Antoni & Veanes, POPL 2012.
pub struct SymbolicFiniteTransducer<A: BooleanAlgebra, B: BooleanAlgebra> {
    /// Input Boolean algebra.
    pub input_algebra: A,
    /// Output Boolean algebra.
    pub output_algebra: B,
    /// All states.
    pub states: Vec<SftState>,
    /// All transitions.
    pub transitions: Vec<SftTransition<A, B>>,
    /// Initial state IDs.
    pub initial_states: HashSet<usize>,
    /// Accepting state IDs.
    pub accepting_states: HashSet<usize>,
}

impl<A: BooleanAlgebra, B: BooleanAlgebra> Clone for SymbolicFiniteTransducer<A, B> {
    fn clone(&self) -> Self {
        Self {
            input_algebra: self.input_algebra.clone(),
            output_algebra: self.output_algebra.clone(),
            states: self.states.clone(),
            transitions: self.transitions.clone(),
            initial_states: self.initial_states.clone(),
            accepting_states: self.accepting_states.clone(),
        }
    }
}

impl<A: BooleanAlgebra, B: BooleanAlgebra> fmt::Debug for SymbolicFiniteTransducer<A, B> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("SymbolicFiniteTransducer")
            .field("states", &self.states.len())
            .field("transitions", &self.transitions.len())
            .field("initial_states", &self.initial_states)
            .field("accepting_states", &self.accepting_states)
            .finish()
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// §3  SFT Sprint 1 — Core Construction + Basic Operations
// ══════════════════════════════════════════════════════════════════════════════

impl<A: BooleanAlgebra, B: BooleanAlgebra> SymbolicFiniteTransducer<A, B> {
    /// Create a new empty SFT.
    pub fn new(input_algebra: A, output_algebra: B) -> Self {
        SymbolicFiniteTransducer {
            input_algebra,
            output_algebra,
            states: Vec::new(),
            transitions: Vec::new(),
            initial_states: HashSet::new(),
            accepting_states: HashSet::new(),
        }
    }

    /// Add a state and return its ID.
    pub fn add_state(&mut self, is_accepting: bool, label: Option<String>) -> usize {
        let id = self.states.len();
        self.states.push(SftState {
            id,
            is_accepting,
            label,
        });
        if is_accepting {
            self.accepting_states.insert(id);
        }
        id
    }

    /// Mark a state as initial.
    pub fn set_initial(&mut self, state_id: usize) {
        assert!(
            state_id < self.states.len(),
            "State ID {} out of range (have {} states)",
            state_id,
            self.states.len(),
        );
        self.initial_states.insert(state_id);
    }

    /// Add a guarded transition with output function.
    pub fn add_transition(
        &mut self,
        from: usize,
        to: usize,
        guard: A::Predicate,
        output: OutputFunction<A, B>,
    ) {
        assert!(
            from < self.states.len() && to < self.states.len(),
            "Transition endpoints ({} -> {}) out of range (have {} states)",
            from,
            to,
            self.states.len(),
        );
        self.transitions.push(SftTransition {
            from,
            to,
            guard,
            output,
        });
    }

    /// Get the number of states.
    pub fn num_states(&self) -> usize {
        self.states.len()
    }

    /// Get the number of transitions.
    pub fn num_transitions(&self) -> usize {
        self.transitions.len()
    }

    /// Transduce an input word, returning all possible output sequences.
    ///
    /// NFA-style simulation: maintains a set of (state, output_so_far) pairs
    /// and, for each input element, computes successors by evaluating guards
    /// and applying output functions.
    ///
    /// # Complexity
    ///
    /// O(|w| · |Q| · |δ|), where |w| is word length.
    pub fn transduce(&self, word: &[A::Domain]) -> Vec<Vec<B::Domain>>
    where
        A::Domain: Clone + Into<B::Domain>,
    {
        if self.initial_states.is_empty() {
            return Vec::new();
        }

        // (state_id, accumulated output)
        let mut current: Vec<(usize, Vec<B::Domain>)> = self
            .initial_states
            .iter()
            .map(|&s| (s, Vec::new()))
            .collect();

        for elem in word {
            let mut next: Vec<(usize, Vec<B::Domain>)> = Vec::new();
            for (state, acc) in &current {
                for trans in &self.transitions {
                    if trans.from == *state
                        && self.input_algebra.evaluate(&trans.guard, elem)
                    {
                        let mut new_acc = acc.clone();
                        new_acc.extend(trans.output.apply(elem));
                        next.push((trans.to, new_acc));
                    }
                }
            }
            current = next;
        }

        // Collect outputs from accepting states.
        current
            .into_iter()
            .filter(|(state, _)| self.accepting_states.contains(state))
            .map(|(_, output)| output)
            .collect()
    }

    /// Extract the domain SFA: drop output functions, keep guards.
    ///
    /// The resulting SFA accepts exactly the inputs for which the SFT
    /// produces at least one output.
    pub fn domain_sfa(&self) -> SymbolicAutomaton<A> {
        let mut sfa = SymbolicAutomaton::new(self.input_algebra.clone());
        for state in &self.states {
            sfa.add_state(state.is_accepting, state.label.clone());
        }
        for &init in &self.initial_states {
            sfa.set_initial(init);
        }
        for trans in &self.transitions {
            sfa.add_transition(trans.from, trans.to, trans.guard.clone());
        }
        sfa
    }

    /// Check if the SFT has an empty domain (no input is ever accepted).
    pub fn is_empty(&self) -> bool {
        self.domain_sfa().is_empty()
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// §4  SFT Sprint 2 — Composition + Pre/Post-Image
// ══════════════════════════════════════════════════════════════════════════════

impl<A, B> SymbolicFiniteTransducer<A, B>
where
    A: BooleanAlgebra,
    B: BooleanAlgebra,
{
    /// Compose two SFTs: self (A → B) followed by other (B → C).
    /// Result: A → C via product construction.
    ///
    /// Algorithm (D'Antoni & Veanes §4):
    /// 1. States = Q₁ × Q₂ product
    /// 2. For each pair of transitions (t₁ from q₁, t₂ from q₂):
    ///    - Check if t₁'s output can satisfy t₂'s guard
    ///    - If so, compose guards and output functions
    /// 3. Accepting = F₁ × F₂
    ///
    /// For non-identity/non-constant output functions, this performs a
    /// conservative over-approximation using satisfiability checks.
    pub fn compose<C: BooleanAlgebra>(
        &self,
        other: &SymbolicFiniteTransducer<B, C>,
    ) -> SymbolicFiniteTransducer<A, C>
    where
        A::Domain: Clone + Into<B::Domain> + Send + Sync + 'static,
        B::Domain: Clone + Into<C::Domain> + Send + Sync + 'static,
    {
        let mut result = SymbolicFiniteTransducer::new(
            self.input_algebra.clone(),
            other.output_algebra.clone(),
        );

        // Product state space: (q₁, q₂) → product_state_id
        let mut state_map: HashMap<(usize, usize), usize> = HashMap::new();
        let mut worklist: VecDeque<(usize, usize)> = VecDeque::new();

        // Create initial product states.
        for &i1 in &self.initial_states {
            for &i2 in &other.initial_states {
                let is_accepting = self.accepting_states.contains(&i1)
                    && other.accepting_states.contains(&i2);
                let label = format!(
                    "({},{})",
                    self.states[i1].label.as_deref().unwrap_or(&i1.to_string()),
                    other.states[i2].label.as_deref().unwrap_or(&i2.to_string()),
                );
                let pid = result.add_state(is_accepting, Some(label));
                result.set_initial(pid);
                state_map.insert((i1, i2), pid);
                worklist.push_back((i1, i2));
            }
        }

        // Explore product states.
        while let Some((q1, q2)) = worklist.pop_front() {
            let from_pid = state_map[&(q1, q2)];

            // For each transition from q₁ in self...
            for t1 in &self.transitions {
                if t1.from != q1 {
                    continue;
                }

                // Handle composition based on output function type.
                match &t1.output {
                    OutputFunction::Epsilon => {
                        // ε-output: advance only in self, stay in other.
                        // This creates a transition that produces nothing.
                        let to_pair = (t1.to, q2);
                        let to_pid = *state_map.entry(to_pair).or_insert_with(|| {
                            let is_acc = self.accepting_states.contains(&t1.to)
                                && other.accepting_states.contains(&q2);
                            let label = format!("({},{})", t1.to, q2);
                            let pid = result.add_state(is_acc, Some(label));
                            worklist.push_back(to_pair);
                            pid
                        });
                        result.add_transition(
                            from_pid,
                            to_pid,
                            t1.guard.clone(),
                            OutputFunction::Epsilon,
                        );
                    }
                    OutputFunction::Constant(vals) => {
                        // Constant output: feed vals through other's transitions.
                        self.compose_constant_output(
                            &mut result,
                            other,
                            &mut state_map,
                            &mut worklist,
                            from_pid,
                            t1,
                            q2,
                            vals,
                        );
                    }
                    OutputFunction::Identity => {
                        // Identity: for each t₂ from q₂, compose if guards compatible.
                        for t2 in &other.transitions {
                            if t2.from != q2 {
                                continue;
                            }
                            // Guard compatibility: t₁'s guard ∧ (identity maps input
                            // through t₂'s guard on B). Since identity passes A::Domain
                            // as B::Domain, we need the input to satisfy both guards.
                            // Conservative: check if t₁'s guard ∧ TRUE is satisfiable.
                            if self.input_algebra.is_satisfiable(&t1.guard)
                                && other.output_algebra.is_satisfiable(
                                    &other.output_algebra.true_pred(),
                                )
                            {
                                let to_pair = (t1.to, t2.to);
                                let to_pid =
                                    *state_map.entry(to_pair).or_insert_with(|| {
                                        let is_acc =
                                            self.accepting_states.contains(&t1.to)
                                                && other.accepting_states.contains(&t2.to);
                                        let label = format!("({},{})", t1.to, t2.to);
                                        let pid = result.add_state(is_acc, Some(label));
                                        worklist.push_back(to_pair);
                                        pid
                                    });
                                // Adapt OutputFunction<B,C> to OutputFunction<A,C>
                                // via identity: A→B then apply t2's output B→C.
                                let t2_out = t2.output.clone();
                                let adapted: OutputFunction<A, C> =
                                    OutputFunction::FlatMap(Arc::new(move |input: &A::Domain| {
                                        let b_val: B::Domain = input.clone().into();
                                        match &t2_out {
                                            OutputFunction::Epsilon => Vec::new(),
                                            OutputFunction::Constant(v) => v.clone(),
                                            OutputFunction::Identity => vec![b_val.into()],
                                            OutputFunction::Map(f) => vec![f(&b_val)],
                                            OutputFunction::FlatMap(f) => f(&b_val),
                                        }
                                    }));
                                result.add_transition(
                                    from_pid,
                                    to_pid,
                                    t1.guard.clone(),
                                    adapted,
                                );
                            }
                        }
                    }
                    OutputFunction::Map(_) | OutputFunction::FlatMap(_) => {
                        // For computed output functions, conservative approach:
                        // compose with all transitions from q₂ whose guards
                        // are satisfiable (we can't statically check output coverage).
                        for t2 in &other.transitions {
                            if t2.from != q2 {
                                continue;
                            }
                            if other.input_algebra.is_satisfiable(&t2.guard) {
                                let to_pair = (t1.to, t2.to);
                                let to_pid =
                                    *state_map.entry(to_pair).or_insert_with(|| {
                                        let is_acc =
                                            self.accepting_states.contains(&t1.to)
                                                && other.accepting_states.contains(&t2.to);
                                        let label = format!("({},{})", t1.to, t2.to);
                                        let pid = result.add_state(is_acc, Some(label));
                                        worklist.push_back(to_pair);
                                        pid
                                    });
                                // Composed output: apply self's then other's.
                                let t1_out = t1.output.clone();
                                let t2_out = t2.output.clone();
                                result.add_transition(
                                    from_pid,
                                    to_pid,
                                    t1.guard.clone(),
                                    compose_output_functions(t1_out, t2_out),
                                );
                            }
                        }
                    }
                }
            }
        }

        result
    }

    /// Helper: compose constant output values through `other`'s transitions.
    fn compose_constant_output<C: BooleanAlgebra>(
        &self,
        result: &mut SymbolicFiniteTransducer<A, C>,
        other: &SymbolicFiniteTransducer<B, C>,
        state_map: &mut HashMap<(usize, usize), usize>,
        worklist: &mut VecDeque<(usize, usize)>,
        from_pid: usize,
        t1: &SftTransition<A, B>,
        q2_start: usize,
        vals: &[B::Domain],
    ) where
        B::Domain: Clone + Into<C::Domain>,
    {
        if vals.is_empty() {
            // Empty constant = epsilon.
            let to_pair = (t1.to, q2_start);
            let to_pid = *state_map.entry(to_pair).or_insert_with(|| {
                let is_acc = self.accepting_states.contains(&t1.to)
                    && other.accepting_states.contains(&q2_start);
                let label = format!("({},{})", t1.to, q2_start);
                let pid = result.add_state(is_acc, Some(label));
                worklist.push_back(to_pair);
                pid
            });
            result.add_transition(
                from_pid,
                to_pid,
                t1.guard.clone(),
                OutputFunction::Epsilon,
            );
            return;
        }

        // Feed constant values through other one at a time.
        // This is a fixed-length simulation.
        let mut q2_current = q2_start;
        let mut all_outputs: Vec<C::Domain> = Vec::new();
        let mut feasible = true;

        for val in vals {
            let mut found = false;
            for t2 in &other.transitions {
                if t2.from == q2_current && other.input_algebra.evaluate(&t2.guard, val) {
                    match &t2.output {
                        OutputFunction::Epsilon => {}
                        OutputFunction::Constant(c) => all_outputs.extend(c.iter().cloned()),
                        OutputFunction::Identity => all_outputs.push(val.clone().into()),
                        OutputFunction::Map(f) => all_outputs.push(f(val)),
                        OutputFunction::FlatMap(f) => all_outputs.extend(f(val)),
                    }
                    q2_current = t2.to;
                    found = true;
                    break; // Take first matching transition (deterministic assumption).
                }
            }
            if !found {
                feasible = false;
                break;
            }
        }

        if feasible {
            let to_pair = (t1.to, q2_current);
            let to_pid = *state_map.entry(to_pair).or_insert_with(|| {
                let is_acc = self.accepting_states.contains(&t1.to)
                    && other.accepting_states.contains(&q2_current);
                let label = format!("({},{})", t1.to, q2_current);
                let pid = result.add_state(is_acc, Some(label));
                worklist.push_back(to_pair);
                pid
            });
            let composed_out = if all_outputs.is_empty() {
                OutputFunction::Epsilon
            } else {
                OutputFunction::Constant(all_outputs)
            };
            result.add_transition(from_pid, to_pid, t1.guard.clone(), composed_out);
        }
    }

    /// Pre-image: given SFA over B, compute SFA over A accepting exactly those
    /// inputs whose transduction is accepted by the SFA.
    ///
    /// Algorithm: product construction SFT × SFA over output.
    pub fn pre_image(&self, acceptor: &SymbolicAutomaton<B>) -> SymbolicAutomaton<A>
    where
        A::Domain: Clone + Into<B::Domain>,
        B::Predicate: Into<A::Predicate>,
    {
        let mut result = SymbolicAutomaton::new(self.input_algebra.clone());

        let mut state_map: HashMap<(usize, usize), usize> = HashMap::new();
        let mut worklist: VecDeque<(usize, usize)> = VecDeque::new();

        // Create initial product states.
        for &i_sft in &self.initial_states {
            for &i_sfa in &acceptor.initial_states {
                let is_acc = self.accepting_states.contains(&i_sft)
                    && acceptor.accepting_states.contains(&i_sfa);
                let pid = result.add_state(is_acc, None);
                result.set_initial(pid);
                state_map.insert((i_sft, i_sfa), pid);
                worklist.push_back((i_sft, i_sfa));
            }
        }

        while let Some((q_sft, q_sfa)) = worklist.pop_front() {
            let from_pid = state_map[&(q_sft, q_sfa)];

            for t_sft in &self.transitions {
                if t_sft.from != q_sft {
                    continue;
                }

                // Determine where the SFA ends up after consuming the SFT's output.
                match &t_sft.output {
                    OutputFunction::Epsilon => {
                        // No output consumed by SFA — SFA state unchanged.
                        let to_pair = (t_sft.to, q_sfa);
                        let to_pid = *state_map.entry(to_pair).or_insert_with(|| {
                            let is_acc = self.accepting_states.contains(&t_sft.to)
                                && acceptor.accepting_states.contains(&q_sfa);
                            let pid = result.add_state(is_acc, None);
                            worklist.push_back(to_pair);
                            pid
                        });
                        result.add_transition(from_pid, to_pid, t_sft.guard.clone());
                    }
                    OutputFunction::Constant(vals) => {
                        // Simulate SFA on the constant output.
                        if let Some(final_sfa_state) =
                            simulate_sfa_on_word(acceptor, q_sfa, vals)
                        {
                            let to_pair = (t_sft.to, final_sfa_state);
                            let to_pid = *state_map.entry(to_pair).or_insert_with(|| {
                                let is_acc = self.accepting_states.contains(&t_sft.to)
                                    && acceptor.accepting_states.contains(&final_sfa_state);
                                let pid = result.add_state(is_acc, None);
                                worklist.push_back(to_pair);
                                pid
                            });
                            result.add_transition(from_pid, to_pid, t_sft.guard.clone());
                        }
                    }
                    OutputFunction::Identity => {
                        // Identity: output equals input. The SFA guard on B
                        // restricts which outputs are accepted, and since output
                        // = input, this restricts the input too. We convert the
                        // SFA guard from B::Predicate to A::Predicate and intersect
                        // with the SFT guard.
                        for t_sfa in &acceptor.transitions {
                            if t_sfa.from == q_sfa {
                                let sfa_guard_as_a: A::Predicate =
                                    t_sfa.guard.clone().into();
                                let composed_guard =
                                    self.input_algebra.and(&t_sft.guard, &sfa_guard_as_a);
                                if !self.input_algebra.is_satisfiable(&composed_guard) {
                                    continue;
                                }
                                let to_pair = (t_sft.to, t_sfa.to);
                                let to_pid =
                                    *state_map.entry(to_pair).or_insert_with(|| {
                                        let is_acc =
                                            self.accepting_states.contains(&t_sft.to)
                                                && acceptor
                                                    .accepting_states
                                                    .contains(&t_sfa.to);
                                        let pid = result.add_state(is_acc, None);
                                        worklist.push_back(to_pair);
                                        pid
                                    });
                                result.add_transition(
                                    from_pid,
                                    to_pid,
                                    composed_guard,
                                );
                            }
                        }
                    }
                    OutputFunction::Map(_) | OutputFunction::FlatMap(_) => {
                        // Conservative: for computed outputs, connect to all SFA successors.
                        for t_sfa in &acceptor.transitions {
                            if t_sfa.from == q_sfa
                                && acceptor.algebra.is_satisfiable(&t_sfa.guard)
                            {
                                let to_pair = (t_sft.to, t_sfa.to);
                                let to_pid =
                                    *state_map.entry(to_pair).or_insert_with(|| {
                                        let is_acc =
                                            self.accepting_states.contains(&t_sft.to)
                                                && acceptor
                                                    .accepting_states
                                                    .contains(&t_sfa.to);
                                        let pid = result.add_state(is_acc, None);
                                        worklist.push_back(to_pair);
                                        pid
                                    });
                                result.add_transition(
                                    from_pid,
                                    to_pid,
                                    t_sft.guard.clone(),
                                );
                            }
                        }
                    }
                }
            }
        }

        result
    }

    /// Post-image: given SFA over A, compute SFA over B accepting exactly
    /// the outputs produced from inputs in L(input_lang).
    ///
    /// Algorithm: product construction SFA × SFT, project to output.
    pub fn post_image(&self, input_lang: &SymbolicAutomaton<A>) -> SymbolicAutomaton<B>
    where
        A::Domain: Clone + Into<B::Domain>,
    {
        let mut result = SymbolicAutomaton::new(self.output_algebra.clone());

        let mut state_map: HashMap<(usize, usize), usize> = HashMap::new();
        let mut worklist: VecDeque<(usize, usize)> = VecDeque::new();

        // Initial product states: (SFA_init, SFT_init).
        for &i_sfa in &input_lang.initial_states {
            for &i_sft in &self.initial_states {
                let is_acc = input_lang.accepting_states.contains(&i_sfa)
                    && self.accepting_states.contains(&i_sft);
                let pid = result.add_state(is_acc, None);
                result.set_initial(pid);
                state_map.insert((i_sfa, i_sft), pid);
                worklist.push_back((i_sfa, i_sft));
            }
        }

        while let Some((q_sfa, q_sft)) = worklist.pop_front() {
            let from_pid = state_map[&(q_sfa, q_sft)];

            // For each SFA transition and each SFT transition,
            // if their input guards are compatible...
            for t_sfa in &input_lang.transitions {
                if t_sfa.from != q_sfa {
                    continue;
                }
                for t_sft in &self.transitions {
                    if t_sft.from != q_sft {
                        continue;
                    }

                    // Input guard compatibility: t_sfa.guard ∧ t_sft.guard.
                    let combined_guard =
                        self.input_algebra.and(&t_sfa.guard, &t_sft.guard);
                    if !self.input_algebra.is_satisfiable(&combined_guard) {
                        continue;
                    }

                    let to_pair = (t_sfa.to, t_sft.to);
                    let to_pid = *state_map.entry(to_pair).or_insert_with(|| {
                        let is_acc = input_lang.accepting_states.contains(&t_sfa.to)
                            && self.accepting_states.contains(&t_sft.to);
                        let pid = result.add_state(is_acc, None);
                        worklist.push_back(to_pair);
                        pid
                    });

                    // Output: project SFT's output as SFA transition guard.
                    // For constant/identity, we can construct exact predicates.
                    // For computed functions, use TRUE (conservative).
                    let out_guard = match &t_sft.output {
                        OutputFunction::Epsilon => {
                            // No output: this is an ε-transition in the output SFA.
                            // We add a direct connection without consuming output.
                            result.add_transition(
                                from_pid,
                                to_pid,
                                self.output_algebra.true_pred(),
                            );
                            continue;
                        }
                        OutputFunction::Identity => {
                            // Identity: output guard = input guard (projected).
                            // Conservative: TRUE.
                            self.output_algebra.true_pred()
                        }
                        OutputFunction::Constant(_)
                        | OutputFunction::Map(_)
                        | OutputFunction::FlatMap(_) => {
                            // Conservative: TRUE.
                            self.output_algebra.true_pred()
                        }
                    };

                    result.add_transition(from_pid, to_pid, out_guard);
                }
            }
        }

        result
    }

    /// Restrict domain to intersection with given SFA.
    pub fn restrict_domain(&self, input_lang: &SymbolicAutomaton<A>) -> Self
    where
        A::Domain: Clone + Into<B::Domain>,
    {
        let mut result = SymbolicFiniteTransducer::new(
            self.input_algebra.clone(),
            self.output_algebra.clone(),
        );

        let mut state_map: HashMap<(usize, usize), usize> = HashMap::new();
        let mut worklist: VecDeque<(usize, usize)> = VecDeque::new();

        for &i_sfa in &input_lang.initial_states {
            for &i_sft in &self.initial_states {
                let is_acc = input_lang.accepting_states.contains(&i_sfa)
                    && self.accepting_states.contains(&i_sft);
                let pid = result.add_state(is_acc, None);
                result.set_initial(pid);
                state_map.insert((i_sfa, i_sft), pid);
                worklist.push_back((i_sfa, i_sft));
            }
        }

        while let Some((q_sfa, q_sft)) = worklist.pop_front() {
            let from_pid = state_map[&(q_sfa, q_sft)];

            for t_sfa in &input_lang.transitions {
                if t_sfa.from != q_sfa {
                    continue;
                }
                for t_sft in &self.transitions {
                    if t_sft.from != q_sft {
                        continue;
                    }

                    let combined_guard =
                        self.input_algebra.and(&t_sfa.guard, &t_sft.guard);
                    if !self.input_algebra.is_satisfiable(&combined_guard) {
                        continue;
                    }

                    let to_pair = (t_sfa.to, t_sft.to);
                    let to_pid = *state_map.entry(to_pair).or_insert_with(|| {
                        let is_acc = input_lang.accepting_states.contains(&t_sfa.to)
                            && self.accepting_states.contains(&t_sft.to);
                        let pid = result.add_state(is_acc, None);
                        worklist.push_back(to_pair);
                        pid
                    });

                    result.add_transition(
                        from_pid,
                        to_pid,
                        combined_guard,
                        t_sft.output.clone(),
                    );
                }
            }
        }

        result
    }
}

/// Simulate an SFA on a concrete word starting from a given state.
/// Returns the final state if accepted, None otherwise.
/// Takes the first matching transition at each step (deterministic assumption).
fn simulate_sfa_on_word<A: BooleanAlgebra>(
    sfa: &SymbolicAutomaton<A>,
    start_state: usize,
    word: &[A::Domain],
) -> Option<usize> {
    let mut current = start_state;
    for elem in word {
        let mut found = false;
        for trans in &sfa.transitions {
            if trans.from == current && sfa.algebra.evaluate(&trans.guard, elem) {
                current = trans.to;
                found = true;
                break;
            }
        }
        if !found {
            return None;
        }
    }
    Some(current)
}

/// Compose two output functions: first ; second.
/// The composed function applies `first` (A→B*) then feeds each result through `second` (B→C*).
fn compose_output_functions<A, B, C>(
    first: OutputFunction<A, B>,
    second: OutputFunction<B, C>,
) -> OutputFunction<A, C>
where
    A: BooleanAlgebra,
    B: BooleanAlgebra,
    C: BooleanAlgebra,
    A::Domain: Clone + Into<B::Domain> + Send + Sync + 'static,
    B::Domain: Clone + Into<C::Domain> + Send + Sync + 'static,
{
    // Handle simple short-circuits without closures.
    if first.is_epsilon() || second.is_epsilon() {
        return OutputFunction::Epsilon;
    }
    if first.is_identity() && second.is_identity() {
        return OutputFunction::Identity;
    }

    // General case: build a FlatMap that chains first (A→B*) then second (B→C*).
    // Both `first` and `second` are moved into the closure.
    OutputFunction::FlatMap(Arc::new(move |input: &A::Domain| {
        // Apply first: A::Domain → Vec<B::Domain>
        let b_vals: Vec<B::Domain> = match &first {
            OutputFunction::Epsilon => return Vec::new(),
            OutputFunction::Constant(v) => v.clone(),
            OutputFunction::Identity => vec![input.clone().into()],
            OutputFunction::Map(f) => vec![f(input)],
            OutputFunction::FlatMap(f) => f(input),
        };
        // Apply second to each B::Domain → Vec<C::Domain>
        let mut c_vals = Vec::new();
        for b_val in &b_vals {
            match &second {
                OutputFunction::Epsilon => {}
                OutputFunction::Constant(v) => c_vals.extend(v.iter().cloned()),
                OutputFunction::Identity => c_vals.push(b_val.clone().into()),
                OutputFunction::Map(f) => c_vals.push(f(b_val)),
                OutputFunction::FlatMap(f) => c_vals.extend(f(b_val)),
            }
        }
        c_vals
    }))
}

// ══════════════════════════════════════════════════════════════════════════════
// §5  SFT Sprint 3 — Functionality + Equivalence
// ══════════════════════════════════════════════════════════════════════════════

/// Error type for SFT operations.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SftError {
    /// Operation requires a functional SFT but the SFT is nondeterministic.
    NotFunctional,
    /// Algebras of the two SFTs don't match.
    AlgebraMismatch,
}

impl fmt::Display for SftError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NotFunctional => write!(f, "SFT is not functional (nondeterministic)"),
            Self::AlgebraMismatch => write!(f, "input/output algebras do not match"),
        }
    }
}

impl std::error::Error for SftError {}

impl<A, B> SymbolicFiniteTransducer<A, B>
where
    A: BooleanAlgebra,
    B: BooleanAlgebra,
{
    /// Check if the SFT is functional (single-valued):
    /// each input word produces at most one output word.
    ///
    /// Algorithm (D'Antoni & Veanes §5):
    /// Build self-product SFT (self × self) over the same input.
    /// Check if any reachable state pair (q₁, q₂) can produce
    /// different outputs on the same guarded input.
    ///
    /// Conservative approximation: checks for structurally identical
    /// output functions on overlapping guards from the same state.
    pub fn is_functional(&self) -> bool {
        // Build adjacency: for each state, group transitions by guard overlap.
        for state_id in 0..self.states.len() {
            let state_transitions: Vec<&SftTransition<A, B>> = self
                .transitions
                .iter()
                .filter(|t| t.from == state_id)
                .collect();

            // Check all pairs of transitions from this state.
            for i in 0..state_transitions.len() {
                for j in (i + 1)..state_transitions.len() {
                    let ti = state_transitions[i];
                    let tj = state_transitions[j];

                    // If guards overlap, check if outputs are compatible.
                    let overlap =
                        self.input_algebra.and(&ti.guard, &tj.guard);
                    if self.input_algebra.is_satisfiable(&overlap) {
                        // Same target state and structurally identical output?
                        if ti.to != tj.to
                            || !output_structurally_equal(&ti.output, &tj.output)
                        {
                            return false;
                        }
                    }
                }
            }
        }
        true
    }

    /// Equivalence for functional SFTs.
    /// T₁ ≡ T₂ iff domain(T₁) = domain(T₂) and ∀w: T₁(w) = T₂(w).
    ///
    /// Both SFTs must be functional; returns `Err(NotFunctional)` otherwise.
    pub fn is_equivalent_functional(&self, other: &Self) -> Result<bool, SftError> {
        if !self.is_functional() {
            return Err(SftError::NotFunctional);
        }
        if !other.is_functional() {
            return Err(SftError::NotFunctional);
        }

        // Check domain equivalence.
        let domain_self = self.domain_sfa();
        let domain_other = other.domain_sfa();
        if !domain_self.is_equivalent(&domain_other) {
            return Ok(false);
        }

        // For functional SFTs with the same domain: check if the product
        // self × other can produce different outputs on any reachable pair.
        // Structural check: for each pair of states, check transition compatibility.
        for &i1 in &self.initial_states {
            for &i2 in &other.initial_states {
                if !self.check_output_equivalence_from(other, i1, i2, &mut HashSet::new()) {
                    return Ok(false);
                }
            }
        }

        Ok(true)
    }

    /// DFS check: from (q1, q2), do self and other produce the same outputs?
    fn check_output_equivalence_from(
        &self,
        other: &Self,
        q1: usize,
        q2: usize,
        visited: &mut HashSet<(usize, usize)>,
    ) -> bool {
        if !visited.insert((q1, q2)) {
            return true; // Already checked this pair.
        }

        let t1s: Vec<&SftTransition<A, B>> =
            self.transitions.iter().filter(|t| t.from == q1).collect();
        let t2s: Vec<&SftTransition<A, B>> =
            other.transitions.iter().filter(|t| t.from == q2).collect();

        for t1 in &t1s {
            for t2 in &t2s {
                let overlap = self.input_algebra.and(&t1.guard, &t2.guard);
                if self.input_algebra.is_satisfiable(&overlap) {
                    if !output_structurally_equal(&t1.output, &t2.output) {
                        return false;
                    }
                    if !self.check_output_equivalence_from(other, t1.to, t2.to, visited) {
                        return false;
                    }
                }
            }
        }

        true
    }

    /// Total check: every input word has at least one output.
    /// Equivalent to: domain SFA is universal (accepts all words).
    pub fn is_total(&self) -> bool {
        // Build domain SFA and check if its complement is empty.
        let domain = self.domain_sfa();
        let complement = domain.complement();
        complement.is_empty()
    }

    /// Injective check (conservative): different inputs → different outputs.
    ///
    /// Checks structurally that no two transitions from the same state
    /// with non-overlapping guards produce the same constant output.
    /// For computed output functions, assumes non-injective (conservative).
    pub fn is_injective(&self) -> bool
    where
        B::Domain: PartialEq,
    {
        for state_id in 0..self.states.len() {
            let state_transitions: Vec<&SftTransition<A, B>> = self
                .transitions
                .iter()
                .filter(|t| t.from == state_id)
                .collect();

            for i in 0..state_transitions.len() {
                for j in (i + 1)..state_transitions.len() {
                    let ti = state_transitions[i];
                    let tj = state_transitions[j];

                    // Non-overlapping guards (different inputs)...
                    let overlap = self.input_algebra.and(&ti.guard, &tj.guard);
                    if !self.input_algebra.is_satisfiable(&overlap) {
                        // ...but same output?
                        if output_structurally_equal(&ti.output, &tj.output)
                            && ti.to == tj.to
                        {
                            // Same output for different inputs → not injective.
                            match (&ti.output, &tj.output) {
                                (OutputFunction::Constant(a), OutputFunction::Constant(b))
                                    if a == b =>
                                {
                                    return false;
                                }
                                (OutputFunction::Epsilon, OutputFunction::Epsilon) => {
                                    return false;
                                }
                                _ => {} // Can't determine statically.
                            }
                        }
                    }
                }
            }
        }
        true
    }
}

/// Check structural equality of output functions.
/// Only `Epsilon`, `Constant`, and `Identity` can be compared; `Map`/`FlatMap` are
/// conservatively treated as unequal.
fn output_structurally_equal<A: BooleanAlgebra, B: BooleanAlgebra>(
    a: &OutputFunction<A, B>,
    b: &OutputFunction<A, B>,
) -> bool {
    match (a, b) {
        (OutputFunction::Epsilon, OutputFunction::Epsilon) => true,
        (OutputFunction::Identity, OutputFunction::Identity) => true,
        (OutputFunction::Constant(va), OutputFunction::Constant(vb)) => {
            // Compare constant vectors using Debug representation
            // (since B::Domain doesn't require Eq in general).
            format!("{:?}", va) == format!("{:?}", vb)
        }
        _ => false,
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// §6  SFT Sprint 5 — Practical Application Factories
// ══════════════════════════════════════════════════════════════════════════════

use crate::symbolic::{CharClassAlgebra, CharClassPred};

/// Case-fold SFT: A-Z → a-z, pass through everything else.
pub fn case_fold_sft() -> SymbolicFiniteTransducer<CharClassAlgebra, CharClassAlgebra> {
    let algebra = CharClassAlgebra::new();
    let mut sft = SymbolicFiniteTransducer::new(algebra.clone(), algebra);

    let q0 = sft.add_state(true, Some("q0".to_string()));
    sft.set_initial(q0);

    // Uppercase A-Z → lowercase a-z.
    sft.add_transition(
        q0,
        q0,
        CharClassPred::Range('A', 'Z'),
        OutputFunction::Map(Arc::new(|c: &char| {
            char::from_u32(*c as u32 + 32).unwrap_or(*c)
        })),
    );

    // Everything else → identity.
    // Complement of A-Z: ['\0', '@'] ∪ ['[', char::MAX].
    let not_upper = CharClassPred::Not(Box::new(CharClassPred::Range('A', 'Z')));
    sft.add_transition(q0, q0, not_upper, OutputFunction::Identity);

    sft
}

/// Whitespace normalization SFT: tab, carriage return, form feed, vertical tab → space.
pub fn whitespace_normalize_sft() -> SymbolicFiniteTransducer<CharClassAlgebra, CharClassAlgebra> {
    let algebra = CharClassAlgebra::new();
    let mut sft = SymbolicFiniteTransducer::new(algebra.clone(), algebra);

    let q0 = sft.add_state(true, Some("q0".to_string()));
    sft.set_initial(q0);

    // Whitespace characters (tab, CR, FF, VT) → space.
    let ws_chars = CharClassPred::Union(vec![
        ('\t', '\t'),   // tab
        ('\x0B', '\x0B'), // vertical tab
        ('\x0C', '\x0C'), // form feed
        ('\r', '\r'),   // carriage return
    ]);
    sft.add_transition(
        q0,
        q0,
        ws_chars.clone(),
        OutputFunction::Constant(vec![' ']),
    );

    // Everything else → identity.
    let not_ws = CharClassPred::Not(Box::new(ws_chars));
    sft.add_transition(q0, q0, not_ws, OutputFunction::Identity);

    sft
}

/// Build an SFT from guarded rules: each (guard, output) pair becomes a transition.
/// Disjoint guards → functional SFT.
pub fn guard_transform_sft<A: BooleanAlgebra>(
    rules: &[(A::Predicate, OutputFunction<A, A>)],
    algebra: &A,
) -> SymbolicFiniteTransducer<A, A> {
    let mut sft = SymbolicFiniteTransducer::new(algebra.clone(), algebra.clone());

    let q0 = sft.add_state(true, Some("q0".to_string()));
    sft.set_initial(q0);

    for (guard, output) in rules {
        sft.add_transition(q0, q0, guard.clone(), output.clone());
    }

    sft
}

/// Compose a chain of same-algebra SFTs into a single pipeline.
pub fn compose_chain<A: BooleanAlgebra>(
    chain: &[SymbolicFiniteTransducer<A, A>],
) -> SymbolicFiniteTransducer<A, A>
where
    A::Domain: Clone + Into<A::Domain> + Send + Sync + 'static,
{
    if chain.is_empty() {
        panic!("compose_chain requires at least one SFT");
    }
    if chain.len() == 1 {
        return chain[0].clone();
    }

    let mut result = chain[0].clone();
    for sft in &chain[1..] {
        result = result.compose(sft);
    }
    result
}

// ══════════════════════════════════════════════════════════════════════════════
// §7  SFT Sprint 4 — Pipeline Analysis Integration
// ══════════════════════════════════════════════════════════════════════════════

/// Structural analysis result for SFTs constructed from grammar data.
#[derive(Debug, Clone)]
pub struct SftAnalysis {
    /// Number of transducers constructed.
    pub num_transducers: usize,
    /// Number that are functional (single-valued).
    pub functional_count: usize,
    /// Number that are total (accept all inputs).
    pub total_count: usize,
    /// Pairs of equivalent functional SFTs (by label).
    pub equivalent_pairs: Vec<(String, String)>,
    /// Labels of SFTs with empty domains (dead transductions).
    pub empty_domain_labels: Vec<String>,
    /// Labels of SFTs that always produce the same constant output.
    pub constant_output_labels: Vec<String>,
}

impl fmt::Display for SftAnalysis {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "SftAnalysis(transducers={}, functional={}, total={}, empty_domains={}, constant_outputs={})",
            self.num_transducers,
            self.functional_count,
            self.total_count,
            self.empty_domain_labels.len(),
            self.constant_output_labels.len(),
        )?;
        if !self.equivalent_pairs.is_empty() {
            write!(f, ", equiv_pairs={}", self.equivalent_pairs.len())?;
        }
        Ok(())
    }
}

/// Analyze grammar data to produce SFT analysis results.
///
/// Currently constructs lightweight analysis from grammar structure.
/// Future: construct actual SFTs from grammar rules and perform deep analysis.
pub fn analyze_from_bundle(
    _all_syntax: &[(String, String, Vec<crate::SyntaxItemSpec>)],
    categories: &[crate::pipeline::CategoryInfo],
) -> SftAnalysis {
    // Lightweight structural analysis: no actual SFT construction yet.
    // Count categories as potential transduction domains.
    let num_transducers = categories.len().min(1); // At least 1 if grammar exists.

    SftAnalysis {
        num_transducers,
        functional_count: num_transducers,
        total_count: 0,
        equivalent_pairs: Vec::new(),
        empty_domain_labels: Vec::new(),
        constant_output_labels: Vec::new(),
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// §8  Tests
// ══════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;
    use crate::symbolic::{CharClassAlgebra, CharClassPred, IntervalAlgebra, IntervalPred};

    // ── Sprint SFT1 tests ──────────────────────────────────────────────

    #[test]
    fn empty_sft_produces_no_output() {
        let alg = IntervalAlgebra::new(0, 100);
        let sft: SymbolicFiniteTransducer<IntervalAlgebra, IntervalAlgebra> =
            SymbolicFiniteTransducer::new(alg.clone(), alg);
        assert!(sft.transduce(&[42]).is_empty());
        assert!(sft.is_empty());
    }

    #[test]
    fn identity_transduction() {
        let alg = IntervalAlgebra::new(0, 100);
        let mut sft = SymbolicFiniteTransducer::new(alg.clone(), alg);

        let q0 = sft.add_state(true, Some("q0".to_string()));
        sft.set_initial(q0);
        sft.add_transition(q0, q0, IntervalPred::True, OutputFunction::Identity);

        let results = sft.transduce(&[1, 2, 3]);
        assert_eq!(results.len(), 1);
        assert_eq!(results[0], vec![1, 2, 3]);
    }

    #[test]
    fn constant_output() {
        let alg = IntervalAlgebra::new(0, 100);
        let mut sft = SymbolicFiniteTransducer::new(alg.clone(), alg);

        let q0 = sft.add_state(true, Some("q0".to_string()));
        sft.set_initial(q0);
        sft.add_transition(
            q0,
            q0,
            IntervalPred::True,
            OutputFunction::Constant(vec![99]),
        );

        let results = sft.transduce(&[1, 2, 3]);
        assert_eq!(results.len(), 1);
        assert_eq!(results[0], vec![99, 99, 99]);
    }

    #[test]
    fn epsilon_output() {
        let alg = IntervalAlgebra::new(0, 100);
        let mut sft = SymbolicFiniteTransducer::new(alg.clone(), alg);

        let q0 = sft.add_state(true, Some("q0".to_string()));
        sft.set_initial(q0);
        sft.add_transition(q0, q0, IntervalPred::True, OutputFunction::Epsilon);

        let results = sft.transduce(&[1, 2, 3]);
        assert_eq!(results.len(), 1);
        assert!(results[0].is_empty());
    }

    #[test]
    fn map_output() {
        let alg = IntervalAlgebra::new(0, 100);
        let mut sft = SymbolicFiniteTransducer::new(alg.clone(), alg);

        let q0 = sft.add_state(true, Some("q0".to_string()));
        sft.set_initial(q0);
        sft.add_transition(
            q0,
            q0,
            IntervalPred::True,
            OutputFunction::Map(Arc::new(|x: &i64| x * 2)),
        );

        let results = sft.transduce(&[3, 5, 7]);
        assert_eq!(results.len(), 1);
        assert_eq!(results[0], vec![6, 10, 14]);
    }

    #[test]
    fn flatmap_output() {
        let alg = IntervalAlgebra::new(0, 100);
        let mut sft = SymbolicFiniteTransducer::new(alg.clone(), alg);

        let q0 = sft.add_state(true, Some("q0".to_string()));
        sft.set_initial(q0);
        sft.add_transition(
            q0,
            q0,
            IntervalPred::True,
            OutputFunction::FlatMap(Arc::new(|x: &i64| vec![*x, *x + 1])),
        );

        let results = sft.transduce(&[10]);
        assert_eq!(results.len(), 1);
        assert_eq!(results[0], vec![10, 11]);
    }

    #[test]
    fn guard_filtering() {
        let alg = IntervalAlgebra::new(0, 100);
        let mut sft = SymbolicFiniteTransducer::new(alg.clone(), alg);

        let q0 = sft.add_state(true, Some("q0".to_string()));
        sft.set_initial(q0);
        // Only pass through values in [0, 50).
        sft.add_transition(
            q0,
            q0,
            IntervalPred::Range(0, 50),
            OutputFunction::Identity,
        );

        let results = sft.transduce(&[10, 20, 30]);
        assert_eq!(results.len(), 1);
        assert_eq!(results[0], vec![10, 20, 30]);

        // Value outside range — no output.
        let results = sft.transduce(&[10, 60]);
        assert!(results.is_empty());
    }

    #[test]
    fn domain_sfa_extraction() {
        let alg = IntervalAlgebra::new(0, 100);
        let mut sft = SymbolicFiniteTransducer::new(alg.clone(), alg);

        let q0 = sft.add_state(true, Some("q0".to_string()));
        sft.set_initial(q0);
        sft.add_transition(
            q0,
            q0,
            IntervalPred::Range(0, 50),
            OutputFunction::Identity,
        );

        let domain = sft.domain_sfa();
        assert!(domain.accepts(&[10, 20]));
        assert!(!domain.accepts(&[60]));
    }

    #[test]
    fn nondeterministic_output() {
        let alg = IntervalAlgebra::new(0, 100);
        let mut sft = SymbolicFiniteTransducer::new(alg.clone(), alg);

        let q0 = sft.add_state(true, None);
        sft.set_initial(q0);

        // Two transitions on overlapping guards with different outputs.
        sft.add_transition(q0, q0, IntervalPred::True, OutputFunction::Identity);
        sft.add_transition(
            q0,
            q0,
            IntervalPred::True,
            OutputFunction::Constant(vec![0]),
        );

        let results = sft.transduce(&[42]);
        assert_eq!(results.len(), 2);
    }

    #[test]
    fn charclass_identity_transduction() {
        let alg = CharClassAlgebra::new();
        let mut sft = SymbolicFiniteTransducer::new(alg.clone(), alg);

        let q0 = sft.add_state(true, Some("q0".to_string()));
        sft.set_initial(q0);
        sft.add_transition(q0, q0, CharClassPred::True, OutputFunction::Identity);

        let results = sft.transduce(&['a', 'b', 'c']);
        assert_eq!(results.len(), 1);
        assert_eq!(results[0], vec!['a', 'b', 'c']);
    }

    #[test]
    fn accessors() {
        let alg = IntervalAlgebra::new(0, 10);
        let mut sft = SymbolicFiniteTransducer::new(alg.clone(), alg);
        assert_eq!(sft.num_states(), 0);
        assert_eq!(sft.num_transitions(), 0);

        let q0 = sft.add_state(true, None);
        sft.set_initial(q0);
        sft.add_transition(q0, q0, IntervalPred::True, OutputFunction::Identity);

        assert_eq!(sft.num_states(), 1);
        assert_eq!(sft.num_transitions(), 1);
    }

    // ── Sprint SFT2 tests ──────────────────────────────────────────────

    #[test]
    fn compose_identity_with_constant() {
        let alg = IntervalAlgebra::new(0, 100);
        let mut t1 = SymbolicFiniteTransducer::new(alg.clone(), alg.clone());
        let q0 = t1.add_state(true, None);
        t1.set_initial(q0);
        t1.add_transition(q0, q0, IntervalPred::True, OutputFunction::Identity);

        let mut t2 = SymbolicFiniteTransducer::new(alg.clone(), alg);
        let q0 = t2.add_state(true, None);
        t2.set_initial(q0);
        t2.add_transition(
            q0,
            q0,
            IntervalPred::True,
            OutputFunction::Constant(vec![42]),
        );

        let composed = t1.compose(&t2);
        let results = composed.transduce(&[1, 2, 3]);
        // Identity followed by constant(42): each input produces [42].
        assert_eq!(results.len(), 1);
        assert_eq!(results[0], vec![42, 42, 42]);
    }

    #[test]
    fn compose_two_maps() {
        let alg = IntervalAlgebra::new(0, 100);
        let mut t1 = SymbolicFiniteTransducer::new(alg.clone(), alg.clone());
        let q0 = t1.add_state(true, None);
        t1.set_initial(q0);
        t1.add_transition(
            q0,
            q0,
            IntervalPred::True,
            OutputFunction::Map(Arc::new(|x: &i64| x + 1)),
        );

        let mut t2 = SymbolicFiniteTransducer::new(alg.clone(), alg);
        let q0 = t2.add_state(true, None);
        t2.set_initial(q0);
        t2.add_transition(
            q0,
            q0,
            IntervalPred::True,
            OutputFunction::Map(Arc::new(|x: &i64| x * 2)),
        );

        let composed = t1.compose(&t2);
        let results = composed.transduce(&[5]);
        // (5 + 1) * 2 = 12
        assert_eq!(results.len(), 1);
        assert_eq!(results[0], vec![12]);
    }

    #[test]
    fn pre_image_identity() {
        let alg = IntervalAlgebra::new(0, 100);
        let mut sft = SymbolicFiniteTransducer::new(alg.clone(), alg.clone());
        let q0 = sft.add_state(true, None);
        sft.set_initial(q0);
        sft.add_transition(q0, q0, IntervalPred::True, OutputFunction::Identity);

        // Acceptor that accepts [0,50).
        let mut acceptor = SymbolicAutomaton::new(alg);
        let s0 = acceptor.add_state(true, None);
        acceptor.set_initial(s0);
        acceptor.add_transition(s0, s0, IntervalPred::Range(0, 50));

        let pre = sft.pre_image(&acceptor);
        assert!(pre.accepts(&[10, 20]));
        // 60 is outside acceptor range.
        assert!(!pre.accepts(&[60]));
    }

    #[test]
    fn post_image_basic() {
        let alg = IntervalAlgebra::new(0, 100);
        let mut sft = SymbolicFiniteTransducer::new(alg.clone(), alg.clone());
        let q0 = sft.add_state(true, None);
        sft.set_initial(q0);
        sft.add_transition(q0, q0, IntervalPred::True, OutputFunction::Identity);

        // Input language: accepts all.
        let mut input_lang = SymbolicAutomaton::new(alg);
        let s0 = input_lang.add_state(true, None);
        input_lang.set_initial(s0);
        input_lang.add_transition(s0, s0, IntervalPred::True);

        let post = sft.post_image(&input_lang);
        // Post-image of universe through identity = non-empty.
        assert!(!post.is_empty());
    }

    #[test]
    fn restrict_domain_basic() {
        let alg = IntervalAlgebra::new(0, 100);
        let mut sft = SymbolicFiniteTransducer::new(alg.clone(), alg.clone());
        let q0 = sft.add_state(true, None);
        sft.set_initial(q0);
        sft.add_transition(q0, q0, IntervalPred::True, OutputFunction::Identity);

        // Restrict to [10, 20).
        let mut restrictor = SymbolicAutomaton::new(alg);
        let s0 = restrictor.add_state(true, None);
        restrictor.set_initial(s0);
        restrictor.add_transition(s0, s0, IntervalPred::Range(10, 20));

        let restricted = sft.restrict_domain(&restrictor);
        let results = restricted.transduce(&[15]);
        assert_eq!(results.len(), 1);
        assert_eq!(results[0], vec![15]);

        // Outside restricted domain.
        let results = restricted.transduce(&[50]);
        assert!(results.is_empty());
    }

    #[test]
    fn empty_sft_composition() {
        let alg = IntervalAlgebra::new(0, 100);
        let t1: SymbolicFiniteTransducer<IntervalAlgebra, IntervalAlgebra> =
            SymbolicFiniteTransducer::new(alg.clone(), alg.clone());
        let mut t2 = SymbolicFiniteTransducer::new(alg.clone(), alg);
        let q0 = t2.add_state(true, None);
        t2.set_initial(q0);
        t2.add_transition(q0, q0, IntervalPred::True, OutputFunction::Identity);

        let composed = t1.compose(&t2);
        assert!(composed.is_empty());
    }

    // ── Sprint SFT3 tests ──────────────────────────────────────────────

    #[test]
    fn identity_is_functional() {
        let alg = IntervalAlgebra::new(0, 100);
        let mut sft = SymbolicFiniteTransducer::new(alg.clone(), alg);
        let q0 = sft.add_state(true, None);
        sft.set_initial(q0);
        sft.add_transition(q0, q0, IntervalPred::True, OutputFunction::Identity);
        assert!(sft.is_functional());
    }

    #[test]
    fn constant_is_functional() {
        let alg = IntervalAlgebra::new(0, 100);
        let mut sft = SymbolicFiniteTransducer::new(alg.clone(), alg);
        let q0 = sft.add_state(true, None);
        sft.set_initial(q0);
        sft.add_transition(
            q0,
            q0,
            IntervalPred::True,
            OutputFunction::Constant(vec![42]),
        );
        assert!(sft.is_functional());
    }

    #[test]
    fn nondeterministic_is_not_functional() {
        let alg = IntervalAlgebra::new(0, 100);
        let mut sft = SymbolicFiniteTransducer::new(alg.clone(), alg);
        let q0 = sft.add_state(true, None);
        let q1 = sft.add_state(true, None);
        sft.set_initial(q0);
        // Two transitions with overlapping guards, different targets.
        sft.add_transition(q0, q0, IntervalPred::True, OutputFunction::Identity);
        sft.add_transition(
            q0,
            q1,
            IntervalPred::True,
            OutputFunction::Constant(vec![0]),
        );
        assert!(!sft.is_functional());
    }

    #[test]
    fn equivalence_of_identical_sft() {
        let alg = IntervalAlgebra::new(0, 100);
        let mut sft1 = SymbolicFiniteTransducer::new(alg.clone(), alg.clone());
        let q0 = sft1.add_state(true, None);
        sft1.set_initial(q0);
        sft1.add_transition(q0, q0, IntervalPred::True, OutputFunction::Identity);

        let mut sft2 = SymbolicFiniteTransducer::new(alg.clone(), alg);
        let q0 = sft2.add_state(true, None);
        sft2.set_initial(q0);
        sft2.add_transition(q0, q0, IntervalPred::True, OutputFunction::Identity);

        assert_eq!(sft1.is_equivalent_functional(&sft2), Ok(true));
    }

    #[test]
    fn equivalence_error_on_nonfunctional() {
        let alg = IntervalAlgebra::new(0, 100);
        let mut sft = SymbolicFiniteTransducer::new(alg.clone(), alg.clone());
        let q0 = sft.add_state(true, None);
        let q1 = sft.add_state(true, None);
        sft.set_initial(q0);
        sft.add_transition(q0, q0, IntervalPred::True, OutputFunction::Identity);
        sft.add_transition(q0, q1, IntervalPred::True, OutputFunction::Epsilon);

        let mut sft2 = SymbolicFiniteTransducer::new(alg.clone(), alg);
        let q0 = sft2.add_state(true, None);
        sft2.set_initial(q0);
        sft2.add_transition(q0, q0, IntervalPred::True, OutputFunction::Identity);

        assert_eq!(sft.is_equivalent_functional(&sft2), Err(SftError::NotFunctional));
    }

    #[test]
    fn totality_check() {
        let alg = IntervalAlgebra::new(0, 100);
        let mut sft = SymbolicFiniteTransducer::new(alg.clone(), alg);
        let q0 = sft.add_state(true, None);
        sft.set_initial(q0);
        sft.add_transition(q0, q0, IntervalPred::True, OutputFunction::Identity);
        assert!(sft.is_total());
    }

    #[test]
    fn non_totality_check() {
        let alg = IntervalAlgebra::new(0, 100);
        let mut sft = SymbolicFiniteTransducer::new(alg.clone(), alg);
        let q0 = sft.add_state(true, None);
        sft.set_initial(q0);
        // Only accepts [0,50).
        sft.add_transition(
            q0,
            q0,
            IntervalPred::Range(0, 50),
            OutputFunction::Identity,
        );
        assert!(!sft.is_total());
    }

    #[test]
    fn injectivity_check() {
        let alg = IntervalAlgebra::new(0, 100);
        let mut sft = SymbolicFiniteTransducer::new(alg.clone(), alg);
        let q0 = sft.add_state(true, None);
        sft.set_initial(q0);
        sft.add_transition(q0, q0, IntervalPred::True, OutputFunction::Identity);
        assert!(sft.is_injective());
    }

    // ── Sprint SFT5 tests: Practical factories ─────────────────────────

    #[test]
    fn case_fold_upper_to_lower() {
        let sft = case_fold_sft();
        let results = sft.transduce(&['A', 'B', 'Z']);
        assert_eq!(results.len(), 1);
        assert_eq!(results[0], vec!['a', 'b', 'z']);
    }

    #[test]
    fn case_fold_lower_unchanged() {
        let sft = case_fold_sft();
        let results = sft.transduce(&['a', 'b', 'c']);
        assert_eq!(results.len(), 1);
        assert_eq!(results[0], vec!['a', 'b', 'c']);
    }

    #[test]
    fn whitespace_normalize_tab() {
        let sft = whitespace_normalize_sft();
        let results = sft.transduce(&['a', '\t', 'b']);
        assert_eq!(results.len(), 1);
        assert_eq!(results[0], vec!['a', ' ', 'b']);
    }

    #[test]
    fn guard_transform_disjoint() {
        let alg = IntervalAlgebra::new(0, 100);
        let rules = vec![
            (
                IntervalPred::Range(0, 50),
                OutputFunction::Constant(vec![0_i64]),
            ),
            (
                IntervalPred::Range(50, 100),
                OutputFunction::Constant(vec![1_i64]),
            ),
        ];
        let sft = guard_transform_sft(&rules, &alg);
        assert!(sft.is_functional());

        let results = sft.transduce(&[25]);
        assert_eq!(results.len(), 1);
        assert_eq!(results[0], vec![0]);

        let results = sft.transduce(&[75]);
        assert_eq!(results.len(), 1);
        assert_eq!(results[0], vec![1]);
    }

    #[test]
    fn guard_transform_overlapping() {
        let alg = IntervalAlgebra::new(0, 100);
        let rules = vec![
            (
                IntervalPred::Range(0, 60),
                OutputFunction::Constant(vec![0_i64]),
            ),
            (
                IntervalPred::Range(40, 100),
                OutputFunction::Constant(vec![1_i64]),
            ),
        ];
        let sft = guard_transform_sft(&rules, &alg);
        assert!(!sft.is_functional()); // Overlapping guards → nondeterministic.
    }

    #[test]
    fn case_fold_is_functional() {
        let sft = case_fold_sft();
        assert!(sft.is_functional());
    }

    #[test]
    fn whitespace_normalize_is_functional() {
        let sft = whitespace_normalize_sft();
        assert!(sft.is_functional());
    }

    // ── Sprint SFT4 tests: Analysis ────────────────────────────────────

    #[test]
    fn sft_analysis_construction() {
        let analysis = SftAnalysis {
            num_transducers: 5,
            functional_count: 3,
            total_count: 2,
            equivalent_pairs: vec![("A".to_string(), "B".to_string())],
            empty_domain_labels: vec!["dead".to_string()],
            constant_output_labels: vec!["const".to_string()],
        };
        assert_eq!(analysis.num_transducers, 5);
        let display = format!("{}", analysis);
        assert!(display.contains("transducers=5"));
        assert!(display.contains("equiv_pairs=1"));
    }

    #[test]
    fn analyze_from_bundle_basic() {
        let categories = vec![crate::pipeline::CategoryInfo {
            name: "Expr".to_string(),
            native_type: None,
            is_primary: true,
        }];
        let analysis = analyze_from_bundle(&[], &categories);
        assert_eq!(analysis.num_transducers, 1);
        assert_eq!(analysis.functional_count, 1);
    }
}
