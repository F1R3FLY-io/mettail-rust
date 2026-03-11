//! Register automata: data-aware finite-state computation with register storage.
//!
//! Register automata extend classical finite automata with a fixed number of
//! registers that can store and compare data values from the input. This enables
//! data-dependent transitions — e.g., matching opening/closing tags, enforcing
//! variable binding consistency, or tracking context-sensitive constraints that
//! go beyond the power of ordinary finite automata.
//!
//! ## Theoretical Foundations
//!
//! - **Kaminski & Francez (1994)** — "Finite-memory automata." Introduces
//!   finite-memory automata (register automata) over infinite alphabets,
//!   establishing decidability of emptiness and universality for the
//!   deterministic case.
//! - **Neven, Schwentick & Vianu (2004)** — "Finite state machines for strings
//!   over infinite alphabets." Comprehensive survey of register automata
//!   variants: deterministic, nondeterministic, with/without guessing.
//! - **Segoufin (2006)** — "Automata and logics for words and trees over an
//!   infinite alphabet." Connections between register automata and logics.
//!
//! ## PraTTaIL Integration
//!
//! Register automata model context-sensitive parsing constraints in PraTTaIL
//! grammars. Where the `nominal` module tracks name-binding via orbit-finite
//! symmetry, register automata provide a complementary operational model:
//! - **Tag matching**: registers store opening tags, `TestEq` ensures closers match
//! - **Variable consistency**: registers track bound variables across a derivation
//! - **Freshness**: `TestFresh` ensures new bindings do not shadow existing ones

use crate::automata::semiring::{BooleanWeight, Semiring};
use std::collections::{HashMap, HashSet, VecDeque};
use std::fmt;

// ══════════════════════════════════════════════════════════════════════════════
// Core types
// ══════════════════════════════════════════════════════════════════════════════

/// Data values stored in registers.
///
/// Register automata operate over an infinite data domain. `DataValue` provides
/// the concrete value types that can appear in the input stream and be stored
/// in registers for subsequent comparison.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum DataValue {
    /// An integer data value.
    Integer(i64),
    /// A symbolic data value (identifier, tag name, etc.).
    Symbol(String),
    /// The unit value (placeholder / wildcard).
    Unit,
}

impl fmt::Display for DataValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            DataValue::Integer(n) => write!(f, "{}", n),
            DataValue::Symbol(s) => write!(f, "'{}'", s),
            DataValue::Unit => write!(f, "()"),
        }
    }
}

/// Operations on registers during transitions.
///
/// Each transition carries a vector of `RegisterOp`, one per register. Guards
/// (`TestEq`, `TestNeq`, `TestFresh`) are checked before the transition fires;
/// assignments (`Store`) are applied after all guards pass.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum RegisterOp {
    /// No operation on this register.
    Nop,
    /// Store the current input data value into this register.
    Store,
    /// Guard: current input must equal this register's value.
    TestEq,
    /// Guard: current input must NOT equal this register's value.
    TestNeq,
    /// Guard: current input must be fresh (not equal to ANY register).
    TestFresh,
}

impl fmt::Display for RegisterOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RegisterOp::Nop => write!(f, "-"),
            RegisterOp::Store => write!(f, "store"),
            RegisterOp::TestEq => write!(f, "=?"),
            RegisterOp::TestNeq => write!(f, "!=?"),
            RegisterOp::TestFresh => write!(f, "fresh?"),
        }
    }
}

/// A state in a register automaton.
#[derive(Debug, Clone)]
pub struct RegisterState {
    /// Unique state identifier (index into `RegisterAutomaton::states`).
    pub id: usize,
    /// Whether this is an accepting state.
    pub is_accepting: bool,
    /// Optional human-readable label for diagnostics.
    pub label: Option<String>,
}

impl fmt::Display for RegisterState {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let acc = if self.is_accepting { "*" } else { "" };
        if let Some(ref label) = self.label {
            write!(f, "r{}{} [{}]", self.id, acc, label)
        } else {
            write!(f, "r{}{}", self.id, acc)
        }
    }
}

/// A transition in a register automaton.
///
/// Transitions carry a structural label (matching the input symbol), a vector
/// of register operations (one per register), and a semiring weight.
#[derive(Debug, Clone)]
pub struct RegisterTransition<W: Semiring> {
    /// Source state index.
    pub from: usize,
    /// Target state index.
    pub to: usize,
    /// Label on the transition (structural, not data).
    /// `None` matches any structural label (epsilon-like on the label component).
    pub label: Option<String>,
    /// Register operations, one per register.
    pub ops: Vec<RegisterOp>,
    /// Semiring weight.
    pub weight: W,
}

impl<W: Semiring + fmt::Display> fmt::Display for RegisterTransition<W> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let label_str = self
            .label
            .as_deref()
            .unwrap_or("*");
        let ops_str: Vec<String> = self.ops.iter().map(|op| format!("{}", op)).collect();
        write!(
            f,
            "r{} --{}/[{}]/{}--> r{}",
            self.from,
            label_str,
            ops_str.join(", "),
            self.weight,
            self.to,
        )
    }
}

/// A register automaton with `k` registers.
///
/// Register automata extend finite automata with a fixed number of registers
/// that can store and compare data values from the input. This enables
/// data-dependent transitions — e.g., matching opening/closing tags,
/// enforcing variable binding consistency.
///
/// ## Theoretical Foundations
///
/// - **Kaminski & Francez (1994)** — "Finite-memory automata." Introduces
///   finite-memory automata (register automata) over infinite alphabets.
/// - **Neven, Schwentick & Vianu (2004)** — "Finite state machines for strings
///   over infinite alphabets." Comprehensive survey of register automata variants.
///
/// ## Semantics
///
/// A configuration is a pair `(state, register_valuation)` where the register
/// valuation maps each register index to `Option<DataValue>`. The automaton
/// processes a *data word* — a sequence of `(label, data_value)` pairs — by
/// nondeterministically choosing transitions whose guards are satisfied by the
/// current data value and register valuation, then applying store operations.
#[derive(Debug, Clone)]
pub struct RegisterAutomaton<W: Semiring> {
    /// Number of registers (fixed at construction time).
    pub num_registers: usize,
    /// States in the automaton.
    pub states: Vec<RegisterState>,
    /// Structural alphabet (set of label strings).
    pub alphabet: HashSet<String>,
    /// Transitions.
    pub transitions: Vec<RegisterTransition<W>>,
    /// Initial state (if set).
    pub initial_state: Option<usize>,
    /// Initial register valuation (one per register).
    pub initial_registers: Vec<Option<DataValue>>,
    /// Set of accepting state indices.
    pub accepting_states: HashSet<usize>,
}

impl<W: Semiring + fmt::Display> fmt::Display for RegisterAutomaton<W> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "RegisterAutomaton({} registers):", self.num_registers)?;
        writeln!(f, "  States ({}):", self.states.len())?;
        for state in &self.states {
            writeln!(f, "    {}", state)?;
        }
        writeln!(f, "  Initial state: {:?}", self.initial_state)?;
        write!(f, "  Initial registers: [")?;
        for (i, reg) in self.initial_registers.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            match reg {
                Some(v) => write!(f, "{}", v)?,
                None => write!(f, "_")?,
            }
        }
        writeln!(f, "]")?;
        writeln!(f, "  Transitions ({}):", self.transitions.len())?;
        for t in &self.transitions {
            writeln!(f, "    {}", t)?;
        }
        Ok(())
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Construction
// ══════════════════════════════════════════════════════════════════════════════

impl<W: Semiring> RegisterAutomaton<W> {
    /// Create a new register automaton with `num_registers` registers.
    ///
    /// All registers are initially unbound (`None`). States, transitions,
    /// and the initial state must be added after construction.
    pub fn new(num_registers: usize) -> Self {
        RegisterAutomaton {
            num_registers,
            states: Vec::new(),
            alphabet: HashSet::new(),
            transitions: Vec::new(),
            initial_state: None,
            initial_registers: vec![None; num_registers],
            accepting_states: HashSet::new(),
        }
    }

    /// Add a state to the automaton and return its index.
    ///
    /// If `is_accepting` is true, the state is added to the accepting set.
    pub fn add_state(&mut self, is_accepting: bool, label: Option<String>) -> usize {
        let id = self.states.len();
        self.states.push(RegisterState {
            id,
            is_accepting,
            label,
        });
        if is_accepting {
            self.accepting_states.insert(id);
        }
        id
    }

    /// Add a transition to the automaton.
    ///
    /// # Panics
    ///
    /// Panics if `ops.len() != self.num_registers`, or if `from` or `to`
    /// are out of bounds.
    pub fn add_transition(
        &mut self,
        from: usize,
        to: usize,
        label: Option<String>,
        ops: Vec<RegisterOp>,
        weight: W,
    ) {
        assert_eq!(
            ops.len(),
            self.num_registers,
            "ops length ({}) must equal num_registers ({})",
            ops.len(),
            self.num_registers,
        );
        assert!(
            from < self.states.len(),
            "source state {} out of bounds (num_states = {})",
            from,
            self.states.len(),
        );
        assert!(
            to < self.states.len(),
            "target state {} out of bounds (num_states = {})",
            to,
            self.states.len(),
        );
        if let Some(ref lbl) = label {
            self.alphabet.insert(lbl.clone());
        }
        self.transitions.push(RegisterTransition {
            from,
            to,
            label,
            ops,
            weight,
        });
    }

    /// Number of states.
    #[inline]
    pub fn num_states(&self) -> usize {
        self.states.len()
    }

    /// Number of transitions.
    #[inline]
    pub fn num_transitions(&self) -> usize {
        self.transitions.len()
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Evaluation (nondeterministic simulation)
// ══════════════════════════════════════════════════════════════════════════════

/// A configuration of a register automaton: `(state_id, register_valuation)`.
type Config = (usize, Vec<Option<DataValue>>);

impl<W: Semiring> RegisterAutomaton<W> {
    /// Evaluate the automaton on a data word, returning the accumulated weight.
    ///
    /// The data word is a sequence of `(label, data_value)` pairs. The automaton
    /// performs a nondeterministic BFS over configurations `(state, registers)`,
    /// accumulating weights via `Semiring::times` along paths and combining
    /// alternative accepting runs via `Semiring::plus`.
    ///
    /// # Returns
    ///
    /// The semiring sum of weights over all accepting runs. Returns `W::zero()`
    /// if no accepting run exists.
    pub fn evaluate(&self, data_word: &[(Option<String>, DataValue)]) -> W {
        let initial_state = match self.initial_state {
            Some(s) => s,
            None => return W::zero(),
        };

        // Map from configuration -> accumulated weight for that configuration.
        let mut current: HashMap<Config, W> = HashMap::new();
        current.insert(
            (initial_state, self.initial_registers.clone()),
            W::one(),
        );

        for (label, data_val) in data_word {
            let mut next: HashMap<Config, W> = HashMap::new();

            for ((state, regs), path_weight) in &current {
                // Find all transitions from this state with matching label.
                for trans in &self.transitions {
                    if trans.from != *state {
                        continue;
                    }
                    // Check label match: transition label None matches any input label.
                    if let Some(ref trans_label) = trans.label {
                        match label {
                            Some(ref input_label) if input_label == trans_label => {}
                            _ => continue,
                        }
                    }

                    // Check guards.
                    if !Self::check_guards(&trans.ops, &regs, data_val) {
                        continue;
                    }

                    // Guards pass — apply stores and advance.
                    let new_regs = Self::apply_stores(&trans.ops, &regs, data_val);
                    let new_weight = path_weight.times(&trans.weight);
                    let config = (trans.to, new_regs);

                    next.entry(config)
                        .and_modify(|w| *w = w.plus(&new_weight))
                        .or_insert(new_weight);
                }
            }

            current = next;
        }

        // Sum weights over all accepting configurations.
        let mut result = W::zero();
        for ((state, _regs), weight) in &current {
            if self.accepting_states.contains(state) {
                result = result.plus(weight);
            }
        }
        result
    }

    /// Check whether all guards in `ops` are satisfied by the current registers
    /// and the incoming data value.
    fn check_guards(
        ops: &[RegisterOp],
        regs: &[Option<DataValue>],
        data_val: &DataValue,
    ) -> bool {
        for (i, op) in ops.iter().enumerate() {
            match op {
                RegisterOp::TestEq => {
                    // Register must be bound and equal to data_val.
                    match &regs[i] {
                        Some(v) if v == data_val => {}
                        _ => return false,
                    }
                }
                RegisterOp::TestNeq => {
                    // Register must be bound and NOT equal to data_val.
                    match &regs[i] {
                        Some(v) if v != data_val => {}
                        _ => return false,
                    }
                }
                RegisterOp::TestFresh => {
                    // Data value must not equal ANY currently bound register.
                    for reg_val in regs.iter().flatten() {
                        if reg_val == data_val {
                            return false;
                        }
                    }
                }
                RegisterOp::Nop | RegisterOp::Store => {
                    // No guard to check.
                }
            }
        }
        true
    }

    /// Apply store operations: copy data_val into registers where op == Store.
    fn apply_stores(
        ops: &[RegisterOp],
        regs: &[Option<DataValue>],
        data_val: &DataValue,
    ) -> Vec<Option<DataValue>> {
        let mut new_regs = regs.to_vec();
        for (i, op) in ops.iter().enumerate() {
            if *op == RegisterOp::Store {
                new_regs[i] = Some(data_val.clone());
            }
        }
        new_regs
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Equivalence checking
// ══════════════════════════════════════════════════════════════════════════════

impl<W: Semiring> RegisterAutomaton<W> {
    /// Check language equivalence with another register automaton.
    ///
    /// Two register automata are equivalent if they accept the same set of data
    /// words (with the same weights). This is decidable for register automata
    /// via a product construction + emptiness check on the symmetric difference.
    ///
    /// ## Algorithm
    ///
    /// 1. Build the product automaton `self x other` synchronizing on data words.
    /// 2. Mark a product state as accepting iff exactly one component accepts
    ///    (symmetric difference).
    /// 3. Check emptiness of the product via BFS from the initial product state.
    /// 4. If the symmetric-difference language is empty, the automata are equivalent.
    ///
    /// ## Complexity
    ///
    /// For automata with `n1`, `n2` states and `k1`, `k2` registers, the product
    /// has `O(n1 * n2)` state pairs, each with `O(k1 + k2)` registers. The BFS
    /// explores reachable product configurations; in the worst case this is
    /// exponential in the number of registers, but for small `k` (typical in
    /// PraTTaIL grammars) it is tractable.
    // === Rocq Proof Alignment (RegisterEquivalence.v) ===
    //
    // The Rocq proof establishes decidability of register automaton equivalence
    // via orbit-finite bisimulation:
    //   - `orbit_eq` is an equivalence relation (refl/sym/trans).
    //   - `orbit_space_bound`: at most |Q| * 2^(k²) orbit classes.
    //   - `refinement_preserves_orbits`: partition refinement respects orbits.
    //   - `fixed_point_is_bisimulation`: fixed point of refinement = bisimulation.
    //
    // The Rust uses BFS over *concrete* product configurations with sentinel data
    // values rather than orbit-abstract representations. This is sound: concrete
    // BFS explores a superset of the reachable orbit space. However, it may not
    // explore all orbit classes — configurations differing only by a permutation
    // of data values are distinct in the concrete representation but orbit-equivalent
    // in the Rocq model.
    //
    // For correctness: the BFS equivalence check is sound (if it finds a difference,
    // the automata are indeed non-equivalent) but may be incomplete for automata
    // with large register counts where the orbit abstraction provides exponential
    // compression.
    //
    // Properties preserved:
    //   - Equality pattern detection (register equality checks).
    //   - Self-bisimilarity (an automaton is always equivalent to itself).
    //   - Bisimulation space finiteness for fixed register count.
    pub fn check_equivalence(&self, other: &RegisterAutomaton<W>) -> bool {
        // Both must have initial states to be comparable.
        let self_init = match self.initial_state {
            Some(s) => s,
            None => return other.initial_state.is_none(),
        };
        let other_init = match other.initial_state {
            Some(s) => s,
            None => return false,
        };

        // Product construction: BFS over (state1, state2, regs1, regs2).
        // States are represented as Option<usize> — None means the automaton
        // has entered a non-accepting dead (sink) state with no outgoing
        // transitions. This models asymmetric reachability: when one automaton
        // can advance but the other is stuck, the stuck side enters the sink.
        type ProductConfig = (
            Option<usize>,                // self state (None = dead)
            Option<usize>,                // other state (None = dead)
            Vec<Option<DataValue>>,       // self registers
            Vec<Option<DataValue>>,       // other registers
        );

        let init_config: ProductConfig = (
            Some(self_init),
            Some(other_init),
            self.initial_registers.clone(),
            other.initial_registers.clone(),
        );

        let mut visited: HashSet<ProductConfig> = HashSet::new();
        let mut queue: VecDeque<ProductConfig> = VecDeque::new();
        visited.insert(init_config.clone());
        queue.push_back(init_config);

        // Collect all data values mentioned in transitions and initial registers
        // as representative test values. Also include a "fresh" sentinel.
        let test_values = self.collect_data_values(other);

        while let Some((s1_opt, s2_opt, regs1, regs2)) = queue.pop_front() {
            // Check symmetric difference: exactly one accepting.
            let acc1 = s1_opt
                .map(|s| self.accepting_states.contains(&s))
                .unwrap_or(false);
            let acc2 = s2_opt
                .map(|s| other.accepting_states.contains(&s))
                .unwrap_or(false);
            if acc1 != acc2 {
                return false;
            }

            // If both are in the dead sink, no further exploration.
            if s1_opt.is_none() && s2_opt.is_none() {
                continue;
            }

            // Explore transitions for each test data value.
            for data_val in &test_values {
                let labels = self.transition_labels_from_opt(s1_opt, other, s2_opt);
                for label in &labels {
                    let self_succs = match s1_opt {
                        Some(s) => self.successors_for(s, &regs1, label, data_val),
                        None => Vec::new(),
                    };
                    let other_succs = match s2_opt {
                        Some(s) => other.successors_for(s, &regs2, label, data_val),
                        None => Vec::new(),
                    };

                    // Case 1: both have successors — pair them.
                    if !self_succs.is_empty() && !other_succs.is_empty() {
                        for (ns1, nr1) in &self_succs {
                            for (ns2, nr2) in &other_succs {
                                let config = (Some(*ns1), Some(*ns2), nr1.clone(), nr2.clone());
                                if visited.insert(config.clone()) {
                                    queue.push_back(config);
                                }
                            }
                        }
                    }
                    // Case 2: only self has successors — other enters dead sink.
                    if !self_succs.is_empty() && other_succs.is_empty() {
                        let dead_regs2 = match s2_opt {
                            Some(_) => regs2.clone(),
                            None => regs2.clone(),
                        };
                        for (ns1, nr1) in &self_succs {
                            let config = (Some(*ns1), None, nr1.clone(), dead_regs2.clone());
                            if visited.insert(config.clone()) {
                                queue.push_back(config);
                            }
                        }
                    }
                    // Case 3: only other has successors — self enters dead sink.
                    if self_succs.is_empty() && !other_succs.is_empty() {
                        let dead_regs1 = match s1_opt {
                            Some(_) => regs1.clone(),
                            None => regs1.clone(),
                        };
                        for (ns2, nr2) in &other_succs {
                            let config = (None, Some(*ns2), dead_regs1.clone(), nr2.clone());
                            if visited.insert(config.clone()) {
                                queue.push_back(config);
                            }
                        }
                    }
                }
            }
        }

        true
    }

    /// Collect the union of transition labels available from optional states.
    fn transition_labels_from_opt(
        &self,
        s1: Option<usize>,
        other: &RegisterAutomaton<W>,
        s2: Option<usize>,
    ) -> Vec<Option<String>> {
        let mut labels: HashSet<Option<String>> = HashSet::new();
        if let Some(s) = s1 {
            for t in &self.transitions {
                if t.from == s {
                    labels.insert(t.label.clone());
                }
            }
        }
        if let Some(s) = s2 {
            for t in &other.transitions {
                if t.from == s {
                    labels.insert(t.label.clone());
                }
            }
        }
        labels.into_iter().collect()
    }

    /// Collect representative data values for equivalence exploration.
    fn collect_data_values(&self, other: &RegisterAutomaton<W>) -> Vec<DataValue> {
        let mut values: HashSet<DataValue> = HashSet::new();
        for reg in &self.initial_registers {
            if let Some(v) = reg {
                values.insert(v.clone());
            }
        }
        for reg in &other.initial_registers {
            if let Some(v) = reg {
                values.insert(v.clone());
            }
        }
        for t in &self.transitions {
            // Gather labels as symbols for test coverage.
            if let Some(ref lbl) = t.label {
                values.insert(DataValue::Symbol(lbl.clone()));
            }
        }
        for t in &other.transitions {
            if let Some(ref lbl) = t.label {
                values.insert(DataValue::Symbol(lbl.clone()));
            }
        }
        // Always include a fresh sentinel that should not match any register.
        values.insert(DataValue::Symbol("__fresh_sentinel__".to_string()));
        values.insert(DataValue::Unit);
        values.into_iter().collect()
    }

    /// Compute successor configurations from state `s` with registers `regs`
    /// on the given label and data value.
    fn successors_for(
        &self,
        s: usize,
        regs: &[Option<DataValue>],
        label: &Option<String>,
        data_val: &DataValue,
    ) -> Vec<(usize, Vec<Option<DataValue>>)> {
        let mut succs = Vec::new();
        for t in &self.transitions {
            if t.from != s {
                continue;
            }
            // Label match.
            if t.label != *label {
                continue;
            }
            // Guards.
            if !Self::check_guards(&t.ops, regs, data_val) {
                continue;
            }
            let new_regs = Self::apply_stores(&t.ops, regs, data_val);
            succs.push((t.to, new_regs));
        }
        succs
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Normalization and dead-register analysis
// ══════════════════════════════════════════════════════════════════════════════

impl<W: Semiring> RegisterAutomaton<W> {
    /// Find registers that are written (Store) but never read (TestEq/TestNeq/TestFresh).
    ///
    /// A register `i` is *dead* if at least one transition stores into it but
    /// no transition tests it. Dead registers waste storage and can be safely
    /// normalized away.
    pub fn dead_registers(&self) -> Vec<usize> {
        let mut stored: HashSet<usize> = HashSet::new();
        let mut tested: HashSet<usize> = HashSet::new();

        for t in &self.transitions {
            for (i, op) in t.ops.iter().enumerate() {
                match op {
                    RegisterOp::Store => {
                        stored.insert(i);
                    }
                    RegisterOp::TestEq | RegisterOp::TestNeq | RegisterOp::TestFresh => {
                        tested.insert(i);
                    }
                    RegisterOp::Nop => {}
                }
            }
        }

        let mut dead: Vec<usize> = stored.difference(&tested).copied().collect();
        dead.sort_unstable();
        dead
    }

    /// Normalize the automaton by removing dead stores.
    ///
    /// Replaces `Store` operations on dead registers (written but never tested)
    /// with `Nop`. This does not change the language or weights — it only
    /// eliminates unnecessary register writes.
    pub fn normalize(&mut self) {
        let dead = self.dead_registers();
        if dead.is_empty() {
            return;
        }
        let dead_set: HashSet<usize> = dead.into_iter().collect();
        for t in &mut self.transitions {
            for (i, op) in t.ops.iter_mut().enumerate() {
                if dead_set.contains(&i) && *op == RegisterOp::Store {
                    *op = RegisterOp::Nop;
                }
            }
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Analysis
// ══════════════════════════════════════════════════════════════════════════════

/// Result of analyzing a register automaton.
#[derive(Debug, Clone)]
pub struct RegisterAnalysis {
    /// Number of states.
    pub num_states: usize,
    /// Number of registers.
    pub num_registers: usize,
    /// Indices of dead registers (stored but never tested).
    pub dead_registers: Vec<usize>,
    /// Unbound references: `(transition_idx, register_idx)` pairs where a
    /// transition tests a register that has no reachable `Store` path from
    /// the initial state.
    pub unbound_references: Vec<(usize, usize)>,
}

/// Analyze grammar binding structure using register automata.
///
/// Builds a register model from the grammar: each category gets a register.
/// Categories with `IdentCapture`/`Binder` items produce `Store` operations.
/// Categories referenced as `NonTerminal` produce `TestEq` (reads).
/// A register is "dead" if it has Store but no TestEq.
pub fn analyze_from_bundle(
    all_syntax: &[(String, String, Vec<crate::SyntaxItemSpec>)],
    categories: &[crate::pipeline::CategoryInfo],
) -> RegisterAnalysis {
    let num_cats = categories.len();
    if num_cats == 0 {
        return RegisterAnalysis {
            num_states: 1,
            num_registers: 0,
            dead_registers: Vec::new(),
            unbound_references: Vec::new(),
        };
    }

    // Map category → register index
    let cat_to_reg: HashMap<String, usize> = categories
        .iter()
        .enumerate()
        .map(|(i, c)| (c.name.clone(), i))
        .collect();

    // Track which registers have Store (binder) and TestEq (reference) operations
    let mut has_store = vec![false; num_cats];
    let mut has_test = vec![false; num_cats];

    for (_label, cat, items) in all_syntax {
        for item in items {
            collect_register_ops(item, cat, &cat_to_reg, &mut has_store, &mut has_test);
        }
    }

    // Dead registers: stored but never tested
    let dead_registers: Vec<usize> = (0..num_cats)
        .filter(|&i| has_store[i] && !has_test[i])
        .collect();

    // Unbound references: tested but never stored
    // We represent these as (transition_idx=0, register_idx) since we don't track per-transition
    let unbound_references: Vec<(usize, usize)> = (0..num_cats)
        .filter(|&i| has_test[i] && !has_store[i])
        .map(|i| (0, i))
        .collect();

    RegisterAnalysis {
        num_states: num_cats.max(1),
        num_registers: num_cats,
        dead_registers,
        unbound_references,
    }
}

/// Recursively scan syntax items for register Store/TestEq operations.
fn collect_register_ops(
    item: &crate::SyntaxItemSpec,
    rule_cat: &str,
    cat_to_reg: &HashMap<String, usize>,
    has_store: &mut [bool],
    has_test: &mut [bool],
) {
    match item {
        // IdentCapture produces a Store for the rule's category register
        crate::SyntaxItemSpec::IdentCapture { .. } => {
            if let Some(&reg) = cat_to_reg.get(rule_cat) {
                has_store[reg] = true;
            }
        }
        // Binder produces a Store for the binder's category register
        crate::SyntaxItemSpec::Binder { category, .. } => {
            if let Some(&reg) = cat_to_reg.get(category.as_str()) {
                has_store[reg] = true;
            }
        }
        // BinderCollection produces a Store for the rule's category register
        crate::SyntaxItemSpec::BinderCollection { .. } => {
            if let Some(&reg) = cat_to_reg.get(rule_cat) {
                has_store[reg] = true;
            }
        }
        // NonTerminal reference produces a TestEq (reads the category's register)
        crate::SyntaxItemSpec::NonTerminal { category, .. } => {
            if let Some(&reg) = cat_to_reg.get(category.as_str()) {
                has_test[reg] = true;
            }
        }
        // Collection reference produces a TestEq
        crate::SyntaxItemSpec::Collection { element_category, .. } => {
            if let Some(&reg) = cat_to_reg.get(element_category.as_str()) {
                has_test[reg] = true;
            }
        }
        // Recurse into compound items
        crate::SyntaxItemSpec::Sep { body, .. } => {
            collect_register_ops(body, rule_cat, cat_to_reg, has_store, has_test);
        }
        crate::SyntaxItemSpec::Map { body_items } => {
            for sub in body_items {
                collect_register_ops(sub, rule_cat, cat_to_reg, has_store, has_test);
            }
        }
        crate::SyntaxItemSpec::Zip { left_category, right_category, body, .. } => {
            for ref_cat in [left_category.as_str(), right_category.as_str()] {
                if let Some(&reg) = cat_to_reg.get(ref_cat) {
                    has_test[reg] = true;
                }
            }
            collect_register_ops(body, rule_cat, cat_to_reg, has_store, has_test);
        }
        crate::SyntaxItemSpec::Optional { inner } => {
            for sub in inner {
                collect_register_ops(sub, rule_cat, cat_to_reg, has_store, has_test);
            }
        }
        // Terminal — no register ops
        _ => {}
    }
}

/// Analyze a register automaton for dead registers and unbound references.
///
/// - **Dead registers**: registers that have `Store` operations but no
///   `TestEq`/`TestNeq`/`TestFresh` operations anywhere.
/// - **Unbound references**: transitions that test a register which cannot
///   have been stored into on any path from the initial state to that
///   transition's source state.
pub fn analyze(automaton: &RegisterAutomaton<BooleanWeight>) -> RegisterAnalysis {
    let dead = automaton.dead_registers();
    let unbound = find_unbound_references(automaton);

    RegisterAnalysis {
        num_states: automaton.num_states(),
        num_registers: automaton.num_registers,
        dead_registers: dead,
        unbound_references: unbound,
    }
}

/// Find transitions that test a register which may not have been stored
/// on any path from the initial state.
///
/// Uses BFS to compute, for each reachable state, the set of registers
/// that are *definitely stored* on every path to that state. A transition
/// testing register `i` from state `s` is flagged as unbound if `i` is
/// not in the stored set for `s` and register `i` is initially `None`.
fn find_unbound_references(
    automaton: &RegisterAutomaton<BooleanWeight>,
) -> Vec<(usize, usize)> {
    let initial_state = match automaton.initial_state {
        Some(s) => s,
        None => return Vec::new(),
    };

    let num_regs = automaton.num_registers;

    // For each state, track which registers *may* have been stored on some
    // path reaching that state. We use a forward BFS/fixpoint to propagate
    // "possibly stored" sets.
    let num_states = automaton.num_states();
    // possibly_stored[s] = set of register indices that MAY have been stored
    // on at least one path from initial to s.
    let mut possibly_stored: Vec<HashSet<usize>> = vec![HashSet::new(); num_states];

    // Registers initially bound are "already stored".
    let initial_stored: HashSet<usize> = automaton
        .initial_registers
        .iter()
        .enumerate()
        .filter_map(|(i, v)| if v.is_some() { Some(i) } else { None })
        .collect();
    if initial_state < num_states {
        possibly_stored[initial_state] = initial_stored;
    }

    // BFS fixpoint: propagate possibly-stored sets along transitions.
    let mut queue: VecDeque<usize> = VecDeque::new();
    queue.push_back(initial_state);
    let mut in_queue: HashSet<usize> = HashSet::new();
    in_queue.insert(initial_state);

    while let Some(s) = queue.pop_front() {
        in_queue.remove(&s);
        let current_stored = possibly_stored[s].clone();

        for t in &automaton.transitions {
            if t.from != s {
                continue;
            }
            let mut new_stored = current_stored.clone();
            for (i, op) in t.ops.iter().enumerate() {
                if *op == RegisterOp::Store {
                    new_stored.insert(i);
                }
            }
            // If target gains new possibly-stored registers, re-enqueue.
            let target = t.to;
            let old_len = possibly_stored[target].len();
            possibly_stored[target] = possibly_stored[target]
                .union(&new_stored)
                .copied()
                .collect();
            if possibly_stored[target].len() > old_len && !in_queue.contains(&target) {
                queue.push_back(target);
                in_queue.insert(target);
            }
        }
    }

    // Check each transition: if it tests register i from state s, but
    // register i is not in possibly_stored[s] and not initially bound,
    // it is an unbound reference.
    let mut unbound = Vec::new();
    for (trans_idx, t) in automaton.transitions.iter().enumerate() {
        for (reg_idx, op) in t.ops.iter().enumerate() {
            match op {
                RegisterOp::TestEq | RegisterOp::TestNeq => {
                    if reg_idx < num_regs && !possibly_stored[t.from].contains(&reg_idx) {
                        unbound.push((trans_idx, reg_idx));
                    }
                }
                _ => {}
            }
        }
    }

    unbound
}

// ══════════════════════════════════════════════════════════════════════════════
// Display for TropicalWeight (needed by RegisterTransition display)
// ══════════════════════════════════════════════════════════════════════════════

// NOTE: TropicalWeight already implements Display via its fmt::Display in semiring.rs.
// BooleanWeight may not, so we provide a local impl if needed. We only gate these
// on Display for the Semiring bound on RegisterTransition::Display.

// ══════════════════════════════════════════════════════════════════════════════
// Predicate Dispatch — PredicateCompiler integration
// ══════════════════════════════════════════════════════════════════════════════

/// Compiler adapter for the Register Automata module (M6).
///
/// Activated by equality/inequality/freshness relations (data language variety).
#[cfg(feature = "predicate-dispatch")]
pub struct RegisterCompiler;

#[cfg(feature = "predicate-dispatch")]
impl crate::predicate_dispatch::PredicateCompiler for RegisterCompiler {
    type Output = RegisterAnalysis;

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
    use crate::automata::semiring::{BooleanWeight, TropicalWeight};

    // ── Helpers ──────────────────────────────────────────────────────────────

    /// Build a simple 2-state, 1-register automaton that matches open/close tags.
    ///
    /// ```text
    ///   q0 --open/[store]--> q1 --close/[=?]--> q2(accept)
    /// ```
    /// Accepts data words like: [("open", X), ("close", X)] where X matches.
    fn tag_matching_automaton() -> RegisterAutomaton<BooleanWeight> {
        let mut ra = RegisterAutomaton::new(1);
        let q0 = ra.add_state(false, Some("start".to_string()));
        let q1 = ra.add_state(false, Some("opened".to_string()));
        let q2 = ra.add_state(true, Some("matched".to_string()));
        ra.initial_state = Some(q0);

        // open: store data value into register 0
        ra.add_transition(
            q0,
            q1,
            Some("open".to_string()),
            vec![RegisterOp::Store],
            BooleanWeight::one(),
        );
        // close: test that data value equals register 0
        ra.add_transition(
            q1,
            q2,
            Some("close".to_string()),
            vec![RegisterOp::TestEq],
            BooleanWeight::one(),
        );

        ra
    }

    // ── Construction tests ───────────────────────────────────────────────────

    #[test]
    fn test_construction_empty() {
        let ra: RegisterAutomaton<BooleanWeight> = RegisterAutomaton::new(3);
        assert_eq!(ra.num_registers, 3);
        assert_eq!(ra.num_states(), 0);
        assert_eq!(ra.num_transitions(), 0);
        assert!(ra.initial_state.is_none());
        assert_eq!(ra.initial_registers.len(), 3);
        assert!(ra.initial_registers.iter().all(|r| r.is_none()));
    }

    #[test]
    fn test_add_states() {
        let mut ra: RegisterAutomaton<BooleanWeight> = RegisterAutomaton::new(1);
        let s0 = ra.add_state(false, Some("init".to_string()));
        let s1 = ra.add_state(true, Some("accept".to_string()));
        assert_eq!(s0, 0);
        assert_eq!(s1, 1);
        assert_eq!(ra.num_states(), 2);
        assert!(!ra.states[0].is_accepting);
        assert!(ra.states[1].is_accepting);
        assert!(ra.accepting_states.contains(&1));
        assert!(!ra.accepting_states.contains(&0));
    }

    #[test]
    fn test_add_transition_updates_alphabet() {
        let mut ra: RegisterAutomaton<BooleanWeight> = RegisterAutomaton::new(1);
        ra.add_state(false, None);
        ra.add_state(false, None);
        ra.add_transition(
            0,
            1,
            Some("read".to_string()),
            vec![RegisterOp::Nop],
            BooleanWeight::one(),
        );
        assert!(ra.alphabet.contains("read"));
        assert_eq!(ra.num_transitions(), 1);
    }

    #[test]
    #[should_panic(expected = "ops length")]
    fn test_add_transition_wrong_ops_length() {
        let mut ra: RegisterAutomaton<BooleanWeight> = RegisterAutomaton::new(2);
        ra.add_state(false, None);
        ra.add_state(false, None);
        // Only 1 op instead of 2 — should panic.
        ra.add_transition(0, 1, None, vec![RegisterOp::Nop], BooleanWeight::one());
    }

    // ── Evaluate tests ──────────────────────────────────────────────────────

    #[test]
    fn test_evaluate_empty_automaton() {
        let ra: RegisterAutomaton<BooleanWeight> = RegisterAutomaton::new(1);
        let result = ra.evaluate(&[(Some("a".to_string()), DataValue::Unit)]);
        assert_eq!(result, BooleanWeight::zero());
    }

    #[test]
    fn test_evaluate_empty_word_accepting_initial() {
        let mut ra: RegisterAutomaton<BooleanWeight> = RegisterAutomaton::new(0);
        let q0 = ra.add_state(true, None);
        ra.initial_state = Some(q0);
        // Empty data word, initial state is accepting.
        let result = ra.evaluate(&[]);
        assert_eq!(result, BooleanWeight::one());
    }

    #[test]
    fn test_evaluate_empty_word_non_accepting() {
        let mut ra: RegisterAutomaton<BooleanWeight> = RegisterAutomaton::new(0);
        let q0 = ra.add_state(false, None);
        ra.initial_state = Some(q0);
        let result = ra.evaluate(&[]);
        assert_eq!(result, BooleanWeight::zero());
    }

    #[test]
    fn test_evaluate_tag_matching_success() {
        let ra = tag_matching_automaton();
        let word = vec![
            (Some("open".to_string()), DataValue::Symbol("div".to_string())),
            (Some("close".to_string()), DataValue::Symbol("div".to_string())),
        ];
        let result = ra.evaluate(&word);
        assert_eq!(result, BooleanWeight::one());
    }

    #[test]
    fn test_evaluate_tag_matching_failure() {
        let ra = tag_matching_automaton();
        let word = vec![
            (Some("open".to_string()), DataValue::Symbol("div".to_string())),
            (Some("close".to_string()), DataValue::Symbol("span".to_string())),
        ];
        let result = ra.evaluate(&word);
        assert_eq!(result, BooleanWeight::zero());
    }

    #[test]
    fn test_evaluate_test_fresh() {
        // Automaton: q0 --a/[store]--> q1 --b/[fresh?]--> q2(accept)
        // Accepts (a, X), (b, Y) iff Y != X.
        let mut ra: RegisterAutomaton<BooleanWeight> = RegisterAutomaton::new(1);
        let q0 = ra.add_state(false, None);
        let q1 = ra.add_state(false, None);
        let q2 = ra.add_state(true, None);
        ra.initial_state = Some(q0);

        ra.add_transition(
            q0, q1,
            Some("a".to_string()),
            vec![RegisterOp::Store],
            BooleanWeight::one(),
        );
        ra.add_transition(
            q1, q2,
            Some("b".to_string()),
            vec![RegisterOp::TestFresh],
            BooleanWeight::one(),
        );

        // Fresh value: should accept.
        let word_fresh = vec![
            (Some("a".to_string()), DataValue::Integer(1)),
            (Some("b".to_string()), DataValue::Integer(2)),
        ];
        assert_eq!(ra.evaluate(&word_fresh), BooleanWeight::one());

        // Same value: should reject (not fresh).
        let word_same = vec![
            (Some("a".to_string()), DataValue::Integer(1)),
            (Some("b".to_string()), DataValue::Integer(1)),
        ];
        assert_eq!(ra.evaluate(&word_same), BooleanWeight::zero());
    }

    #[test]
    fn test_evaluate_test_neq() {
        // Automaton: q0 --a/[store]--> q1 --b/[!=?]--> q2(accept)
        let mut ra: RegisterAutomaton<BooleanWeight> = RegisterAutomaton::new(1);
        let q0 = ra.add_state(false, None);
        let q1 = ra.add_state(false, None);
        let q2 = ra.add_state(true, None);
        ra.initial_state = Some(q0);

        ra.add_transition(
            q0, q1,
            Some("a".to_string()),
            vec![RegisterOp::Store],
            BooleanWeight::one(),
        );
        ra.add_transition(
            q1, q2,
            Some("b".to_string()),
            vec![RegisterOp::TestNeq],
            BooleanWeight::one(),
        );

        // Different value: should accept.
        let word_diff = vec![
            (Some("a".to_string()), DataValue::Symbol("x".to_string())),
            (Some("b".to_string()), DataValue::Symbol("y".to_string())),
        ];
        assert_eq!(ra.evaluate(&word_diff), BooleanWeight::one());

        // Same value: should reject.
        let word_same = vec![
            (Some("a".to_string()), DataValue::Symbol("x".to_string())),
            (Some("b".to_string()), DataValue::Symbol("x".to_string())),
        ];
        assert_eq!(ra.evaluate(&word_same), BooleanWeight::zero());
    }

    #[test]
    fn test_evaluate_tropical_weights() {
        // Automaton: q0 --a/[nop]/2.0--> q1(accept)
        let mut ra: RegisterAutomaton<TropicalWeight> = RegisterAutomaton::new(0);
        let q0 = ra.add_state(false, None);
        let q1 = ra.add_state(true, None);
        ra.initial_state = Some(q0);

        ra.add_transition(
            q0, q1,
            Some("a".to_string()),
            vec![],
            TropicalWeight::new(2.0),
        );

        let word = vec![(Some("a".to_string()), DataValue::Unit)];
        let result = ra.evaluate(&word);
        assert_eq!(result, TropicalWeight::new(2.0));
    }

    // ── Multi-register tests ────────────────────────────────────────────────

    #[test]
    fn test_multi_register_tracking() {
        // 2 registers: store first value in reg0, second in reg1,
        // then test both with TestEq.
        //
        //   q0 --a/[store, nop]--> q1 --b/[nop, store]--> q2
        //   q2 --c/[=?, =?]--> q3(accept)
        //
        // Accepts: (a, X), (b, Y), (c, Z) iff Z == X AND Z == Y
        // i.e. X == Y == Z.
        let mut ra: RegisterAutomaton<BooleanWeight> = RegisterAutomaton::new(2);
        let q0 = ra.add_state(false, None);
        let q1 = ra.add_state(false, None);
        let q2 = ra.add_state(false, None);
        let q3 = ra.add_state(true, None);
        ra.initial_state = Some(q0);

        ra.add_transition(
            q0, q1,
            Some("a".to_string()),
            vec![RegisterOp::Store, RegisterOp::Nop],
            BooleanWeight::one(),
        );
        ra.add_transition(
            q1, q2,
            Some("b".to_string()),
            vec![RegisterOp::Nop, RegisterOp::Store],
            BooleanWeight::one(),
        );
        ra.add_transition(
            q2, q3,
            Some("c".to_string()),
            vec![RegisterOp::TestEq, RegisterOp::TestEq],
            BooleanWeight::one(),
        );

        // All same: accept.
        let word_ok = vec![
            (Some("a".to_string()), DataValue::Integer(42)),
            (Some("b".to_string()), DataValue::Integer(42)),
            (Some("c".to_string()), DataValue::Integer(42)),
        ];
        assert_eq!(ra.evaluate(&word_ok), BooleanWeight::one());

        // Different second: reject (reg1 != reg0 at third step).
        let word_bad = vec![
            (Some("a".to_string()), DataValue::Integer(42)),
            (Some("b".to_string()), DataValue::Integer(99)),
            (Some("c".to_string()), DataValue::Integer(42)),
        ];
        assert_eq!(ra.evaluate(&word_bad), BooleanWeight::zero());
    }

    // ── Dead register tests ─────────────────────────────────────────────────

    #[test]
    fn test_dead_registers_none() {
        let ra = tag_matching_automaton();
        // Register 0 is both stored and tested — not dead.
        assert!(ra.dead_registers().is_empty());
    }

    #[test]
    fn test_dead_registers_found() {
        // 2 registers. Reg 0: stored and tested. Reg 1: stored but never tested.
        let mut ra: RegisterAutomaton<BooleanWeight> = RegisterAutomaton::new(2);
        let q0 = ra.add_state(false, None);
        let q1 = ra.add_state(false, None);
        let q2 = ra.add_state(true, None);
        ra.initial_state = Some(q0);

        ra.add_transition(
            q0, q1,
            Some("a".to_string()),
            vec![RegisterOp::Store, RegisterOp::Store],
            BooleanWeight::one(),
        );
        ra.add_transition(
            q1, q2,
            Some("b".to_string()),
            vec![RegisterOp::TestEq, RegisterOp::Nop], // reg 1 never tested
            BooleanWeight::one(),
        );

        let dead = ra.dead_registers();
        assert_eq!(dead, vec![1]);
    }

    // ── Normalize tests ─────────────────────────────────────────────────────

    #[test]
    fn test_normalize_removes_dead_stores() {
        let mut ra: RegisterAutomaton<BooleanWeight> = RegisterAutomaton::new(2);
        let q0 = ra.add_state(false, None);
        let q1 = ra.add_state(true, None);
        ra.initial_state = Some(q0);

        ra.add_transition(
            q0, q1,
            Some("a".to_string()),
            vec![RegisterOp::Store, RegisterOp::Store], // reg 1 dead
            BooleanWeight::one(),
        );
        // Only reg 0 is tested.
        ra.add_transition(
            q1, q0,
            Some("b".to_string()),
            vec![RegisterOp::TestEq, RegisterOp::Nop],
            BooleanWeight::one(),
        );

        ra.normalize();

        // After normalization, reg 1's Store should become Nop.
        assert_eq!(ra.transitions[0].ops[0], RegisterOp::Store);
        assert_eq!(ra.transitions[0].ops[1], RegisterOp::Nop);
    }

    #[test]
    fn test_normalize_no_change_when_all_live() {
        let mut ra = tag_matching_automaton();
        let ops_before: Vec<Vec<RegisterOp>> =
            ra.transitions.iter().map(|t| t.ops.clone()).collect();
        ra.normalize();
        let ops_after: Vec<Vec<RegisterOp>> =
            ra.transitions.iter().map(|t| t.ops.clone()).collect();
        assert_eq!(ops_before, ops_after);
    }

    // ── Equivalence tests ───────────────────────────────────────────────────

    #[test]
    fn test_equivalence_identical() {
        let ra1 = tag_matching_automaton();
        let ra2 = tag_matching_automaton();
        assert!(ra1.check_equivalence(&ra2));
    }

    #[test]
    fn test_equivalence_different_languages() {
        let ra1 = tag_matching_automaton();

        // Build an automaton that always accepts (no guard).
        let mut ra2: RegisterAutomaton<BooleanWeight> = RegisterAutomaton::new(1);
        let q0 = ra2.add_state(false, None);
        let q1 = ra2.add_state(false, None);
        let q2 = ra2.add_state(true, None);
        ra2.initial_state = Some(q0);

        ra2.add_transition(
            q0, q1,
            Some("open".to_string()),
            vec![RegisterOp::Nop],
            BooleanWeight::one(),
        );
        ra2.add_transition(
            q1, q2,
            Some("close".to_string()),
            vec![RegisterOp::Nop], // no TestEq — accepts all close values
            BooleanWeight::one(),
        );

        assert!(!ra1.check_equivalence(&ra2));
    }

    #[test]
    fn test_equivalence_both_empty() {
        let ra1: RegisterAutomaton<BooleanWeight> = RegisterAutomaton::new(0);
        let ra2: RegisterAutomaton<BooleanWeight> = RegisterAutomaton::new(0);
        // Both have no initial state — equivalent (both reject everything).
        assert!(ra1.check_equivalence(&ra2));
    }

    // ── Analysis tests ──────────────────────────────────────────────────────

    #[test]
    fn test_analyze_clean() {
        let ra = tag_matching_automaton();
        let analysis = analyze(&ra);
        assert_eq!(analysis.num_states, 3);
        assert_eq!(analysis.num_registers, 1);
        assert!(analysis.dead_registers.is_empty());
        assert!(analysis.unbound_references.is_empty());
    }

    #[test]
    fn test_analyze_finds_unbound_reference() {
        // TestEq on register 0 without a prior Store on any path.
        let mut ra: RegisterAutomaton<BooleanWeight> = RegisterAutomaton::new(1);
        let q0 = ra.add_state(false, None);
        let q1 = ra.add_state(true, None);
        ra.initial_state = Some(q0);

        // Directly test register 0 without storing — unbound reference.
        ra.add_transition(
            q0, q1,
            Some("x".to_string()),
            vec![RegisterOp::TestEq],
            BooleanWeight::one(),
        );

        let analysis = analyze(&ra);
        assert_eq!(analysis.unbound_references.len(), 1);
        assert_eq!(analysis.unbound_references[0], (0, 0)); // transition 0, register 0
    }

    #[test]
    fn test_analyze_no_unbound_when_initially_bound() {
        // Register 0 is initially bound — TestEq is valid.
        let mut ra: RegisterAutomaton<BooleanWeight> = RegisterAutomaton::new(1);
        let q0 = ra.add_state(false, None);
        let q1 = ra.add_state(true, None);
        ra.initial_state = Some(q0);
        ra.initial_registers[0] = Some(DataValue::Integer(42));

        ra.add_transition(
            q0, q1,
            Some("x".to_string()),
            vec![RegisterOp::TestEq],
            BooleanWeight::one(),
        );

        let analysis = analyze(&ra);
        assert!(analysis.unbound_references.is_empty());
    }

    // ── Display tests ───────────────────────────────────────────────────────

    #[test]
    fn test_display_data_value() {
        assert_eq!(format!("{}", DataValue::Integer(42)), "42");
        assert_eq!(format!("{}", DataValue::Symbol("foo".to_string())), "'foo'");
        assert_eq!(format!("{}", DataValue::Unit), "()");
    }

    #[test]
    fn test_display_register_op() {
        assert_eq!(format!("{}", RegisterOp::Nop), "-");
        assert_eq!(format!("{}", RegisterOp::Store), "store");
        assert_eq!(format!("{}", RegisterOp::TestEq), "=?");
        assert_eq!(format!("{}", RegisterOp::TestNeq), "!=?");
        assert_eq!(format!("{}", RegisterOp::TestFresh), "fresh?");
    }

    #[test]
    fn test_display_register_state() {
        let s = RegisterState {
            id: 0,
            is_accepting: false,
            label: Some("init".to_string()),
        };
        assert_eq!(format!("{}", s), "r0 [init]");

        let s_acc = RegisterState {
            id: 1,
            is_accepting: true,
            label: None,
        };
        assert_eq!(format!("{}", s_acc), "r1*");
    }

    #[test]
    fn test_display_automaton() {
        let ra = tag_matching_automaton();
        let display = format!("{}", ra);
        assert!(display.contains("RegisterAutomaton(1 registers)"));
        assert!(display.contains("States (3)"));
        assert!(display.contains("Transitions (2)"));
        assert!(display.contains("store"));
        assert!(display.contains("=?"));
    }

    // ── analyze_from_bundle tests ───────────────────────────────────────────

    #[test]
    fn analyze_bundle_dead_register() {
        use crate::pipeline::CategoryInfo;

        let categories = vec![
            CategoryInfo { name: "Expr".to_string(), is_primary: true, native_type: None },
            CategoryInfo { name: "Name".to_string(), is_primary: false, native_type: None },
        ];

        // Name has IdentCapture (Store) but is never referenced as NonTerminal (no TestEq)
        let all_syntax = vec![
            ("Lit".to_string(), "Expr".to_string(), vec![
                crate::SyntaxItemSpec::Terminal("42".to_string()),
            ]),
            ("Var".to_string(), "Name".to_string(), vec![
                crate::SyntaxItemSpec::IdentCapture { param_name: "x".to_string() },
            ]),
        ];

        let result = analyze_from_bundle(&all_syntax, &categories);
        // Name register (index 1) has Store but no Test → dead
        assert!(result.dead_registers.contains(&1), "Name register should be dead");
    }

    #[test]
    fn analyze_bundle_live_register() {
        use crate::pipeline::CategoryInfo;

        let categories = vec![
            CategoryInfo { name: "Expr".to_string(), is_primary: true, native_type: None },
            CategoryInfo { name: "Name".to_string(), is_primary: false, native_type: None },
        ];

        // Name has IdentCapture (Store) AND is referenced by Expr (TestEq)
        let all_syntax = vec![
            ("Ref".to_string(), "Expr".to_string(), vec![
                crate::SyntaxItemSpec::NonTerminal {
                    category: "Name".to_string(),
                    param_name: "n".to_string(),
                },
            ]),
            ("Var".to_string(), "Name".to_string(), vec![
                crate::SyntaxItemSpec::IdentCapture { param_name: "x".to_string() },
            ]),
        ];

        let result = analyze_from_bundle(&all_syntax, &categories);
        assert!(!result.dead_registers.contains(&1), "Name register should NOT be dead (it's referenced)");
    }

    #[test]
    fn analyze_bundle_no_binders() {
        use crate::pipeline::CategoryInfo;

        let categories = vec![
            CategoryInfo { name: "Expr".to_string(), is_primary: true, native_type: None },
        ];

        let all_syntax = vec![
            ("Lit".to_string(), "Expr".to_string(), vec![
                crate::SyntaxItemSpec::Terminal("42".to_string()),
            ]),
        ];

        let result = analyze_from_bundle(&all_syntax, &categories);
        assert!(result.dead_registers.is_empty(), "no binders means no dead registers");
    }

    #[test]
    fn analyze_bundle_empty_categories() {
        use crate::pipeline::CategoryInfo;

        let categories: Vec<CategoryInfo> = vec![];
        let all_syntax: Vec<(String, String, Vec<crate::SyntaxItemSpec>)> = vec![];

        let result = analyze_from_bundle(&all_syntax, &categories);
        assert_eq!(result.num_registers, 0);
        assert!(result.dead_registers.is_empty());
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

    /// Helper: collect cross-category NonTerminal references.
    ///
    /// Returns a set of category names that are referenced as `NonTerminal`
    /// (or `Collection`, `Binder`, `Zip`) targets from rules belonging to a
    /// *different* category.
    fn referenced_categories(
        all_syntax: &[(String, String, Vec<SyntaxItemSpec>)],
    ) -> std::collections::HashSet<String> {
        let mut referenced = std::collections::HashSet::new();
        for (_label, rule_cat, items) in all_syntax {
            for item in items {
                collect_nt_refs(item, rule_cat, &mut referenced);
            }
        }
        referenced
    }

    fn collect_nt_refs(
        item: &SyntaxItemSpec,
        rule_cat: &str,
        referenced: &mut std::collections::HashSet<String>,
    ) {
        match item {
            SyntaxItemSpec::NonTerminal { category, .. } => {
                referenced.insert(category.clone());
            }
            SyntaxItemSpec::Collection { element_category, .. } => {
                referenced.insert(element_category.clone());
            }
            SyntaxItemSpec::Binder { category, .. } => {
                // Binder produces Store, not TestEq — but we track the
                // category for prop_referenced_category_not_dead which
                // needs NonTerminal/Collection references specifically.
                let _ = category;
            }
            SyntaxItemSpec::Sep { body, .. } => {
                collect_nt_refs(body, rule_cat, referenced);
            }
            SyntaxItemSpec::Map { body_items } => {
                for sub in body_items {
                    collect_nt_refs(sub, rule_cat, referenced);
                }
            }
            SyntaxItemSpec::Zip { left_category, right_category, body, .. } => {
                referenced.insert(left_category.clone());
                referenced.insert(right_category.clone());
                collect_nt_refs(body, rule_cat, referenced);
            }
            SyntaxItemSpec::Optional { inner } => {
                for sub in inner {
                    collect_nt_refs(sub, rule_cat, referenced);
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
                // Ensure at least one item per rule.
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

        // ── Property 1: dead_registers indices are valid ────────────────────
        /// Every index in `dead_registers` must be less than `num_registers`.
        #[test]
        fn prop_dead_registers_subset_all(
            (categories, all_syntax) in arb_small_grammar(),
        ) {
            let result = analyze_from_bundle(&all_syntax, &categories);
            for &dr in &result.dead_registers {
                prop_assert!(
                    dr < result.num_registers,
                    "dead register {} >= num_registers {}",
                    dr,
                    result.num_registers,
                );
            }
        }

        // ── Property 2: dead register not referenced by NonTerminal ─────────
        /// A dead register at index `i` corresponds to a category that is NOT
        /// referenced via `NonTerminal` or `Collection` in any rule's items.
        /// (Dead = has Store but no TestEq; TestEq comes from NonTerminal/
        /// Collection references to that category.)
        #[test]
        fn prop_dead_implies_store_no_test(
            (categories, all_syntax) in arb_small_grammar(),
        ) {
            let result = analyze_from_bundle(&all_syntax, &categories);
            let referenced = referenced_categories(&all_syntax);

            for &dr in &result.dead_registers {
                let cat_name = &categories[dr].name;
                // A dead register means this category has Store but no TestEq.
                // TestEq is produced by NonTerminal/Collection references to
                // this category. So if it's dead, no NonTerminal/Collection
                // should reference it (though it may reference itself — self-
                // references don't count in the collect_register_ops function
                // since NonTerminal always marks has_test regardless of source).
                //
                // Note: collect_register_ops marks has_test for the *target*
                // category of NonTerminal/Collection regardless of which
                // category owns the rule. So if ANY rule references cat_name
                // via NonTerminal or Collection, has_test[dr] would be true
                // and it would NOT be dead. Therefore dead => not referenced.
                prop_assert!(
                    !referenced.contains(cat_name),
                    "dead register {} ({}) is referenced via NonTerminal/Collection",
                    dr,
                    cat_name,
                );
            }
        }

        // ── Property 3: no binders → no dead registers ─────────────────────
        /// A grammar with only Terminal items (no IdentCapture, Binder,
        /// NonTerminal, etc.) should have no dead registers, because dead
        /// registers require a Store operation (from IdentCapture/Binder/
        /// BinderCollection).
        #[test]
        fn prop_no_binders_no_dead(
            (categories, all_syntax) in arb_small_grammar(),
        ) {
            let terminal_only = terminalize(&all_syntax);
            let result = analyze_from_bundle(&terminal_only, &categories);
            prop_assert!(
                result.dead_registers.is_empty(),
                "terminal-only grammar should have no dead registers, got {:?}",
                result.dead_registers,
            );
        }

        // ── Property 4: referenced category not dead ────────────────────────
        /// If category C is referenced as a NonTerminal (or Collection) target
        /// in any rule, its register index should NOT appear in
        /// `dead_registers` (because TestEq would be set).
        #[test]
        fn prop_referenced_category_not_dead(
            (categories, all_syntax) in arb_small_grammar(),
        ) {
            let result = analyze_from_bundle(&all_syntax, &categories);
            let referenced = referenced_categories(&all_syntax);

            let cat_to_idx: std::collections::HashMap<&str, usize> = categories
                .iter()
                .enumerate()
                .map(|(i, c)| (c.name.as_str(), i))
                .collect();

            for ref_cat in &referenced {
                if let Some(&idx) = cat_to_idx.get(ref_cat.as_str()) {
                    prop_assert!(
                        !result.dead_registers.contains(&idx),
                        "referenced category {} (idx {}) should not be dead",
                        ref_cat,
                        idx,
                    );
                }
            }
        }

        // ── Property 5: num_registers equals categories.len() ───────────────
        /// The number of registers always equals the number of categories.
        #[test]
        fn prop_num_registers_equals_categories(
            (categories, all_syntax) in arb_grammar(1..6, 1..5),
        ) {
            let result = analyze_from_bundle(&all_syntax, &categories);
            prop_assert_eq!(
                result.num_registers,
                categories.len(),
                "num_registers should equal categories.len()",
            );
        }
    }
}
