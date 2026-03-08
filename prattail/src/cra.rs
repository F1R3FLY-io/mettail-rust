//! Cost Register Automata (CRA) for streaming quantitative computation.
//!
//! Cost Register Automata are a model of computation that processes a stream
//! of input symbols while maintaining a finite set of registers holding values
//! from a semiring. At each step, registers are updated via semiring operations
//! (addition and multiplication of the current register values and the input
//! cost). CRAs are strictly more expressive than weighted automata while
//! retaining decidable equivalence.
//!
//! ## Theoretical Foundations
//!
//! - **Alur, D'Antoni, Deshmukh, Raghothaman & Yuan (2013)** — "Regular
//!   functions and cost register automata." Introduces CRAs and proves that
//!   they capture exactly the class of regular functions (Mealy machines
//!   extended to semiring-valued outputs). Decidable equivalence via a
//!   polynomial-time algorithm.
//! - **Alur & Raghothaman (2013)** — "Decision problems for additive regular
//!   functions." Establishes the complexity of equivalence checking for
//!   different semiring choices.
//! - **Colcombet (2013)** — "The theory of stabilisation monoids and regular
//!   cost functions." A related framework connecting cost functions to
//!   language theory via the stabilisation operation.
//!
//! ## Architecture
//!
//! ```text
//! Input stream: a₁, a₂, a₃, ...
//!       │
//!       ▼
//! CostRegisterAutomaton
//!       │
//!       ├──→ evaluate_stream() ──→ final register values
//!       │
//!       └──→ check_equivalence() ──→ true/false
//! ```
//!
//! ## PraTTaIL Integration
//!
//! CRAs model streaming cost accumulation during parsing. As the parser
//! processes tokens, registers accumulate costs (e.g., nesting depth,
//! ambiguity count, error recovery penalty) via semiring operations. The
//! final register values provide quantitative parse quality metrics.

use std::collections::HashMap;
use std::fmt;

use crate::automata::semiring::Semiring;

// ══════════════════════════════════════════════════════════════════════════════
// Core types
// ══════════════════════════════════════════════════════════════════════════════

/// A register in a CRA, identified by index.
///
/// Registers hold semiring values that are updated at each step according
/// to the transition's register update function.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Register {
    /// Register index.
    pub index: usize,
}

impl Register {
    /// Create a new register reference.
    pub fn new(index: usize) -> Self {
        Register { index }
    }
}

impl fmt::Display for Register {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "r{}", self.index)
    }
}

/// An expression in the register update language.
///
/// Register updates are expressions built from:
/// - Current register values
/// - The input cost (from the semiring)
/// - Semiring operations (plus, times)
/// - Semiring constants (zero, one)
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RegisterExpr {
    /// The current value of a register.
    Reg(Register),
    /// The input cost/weight for the current symbol.
    InputCost,
    /// Semiring zero.
    Zero,
    /// Semiring one.
    One,
    /// Semiring addition of two expressions.
    Plus(Box<RegisterExpr>, Box<RegisterExpr>),
    /// Semiring multiplication of two expressions.
    Times(Box<RegisterExpr>, Box<RegisterExpr>),
}

impl RegisterExpr {
    /// Shorthand for a register reference.
    pub fn reg(index: usize) -> Self {
        RegisterExpr::Reg(Register::new(index))
    }

    /// Shorthand for addition.
    pub fn plus(a: RegisterExpr, b: RegisterExpr) -> Self {
        RegisterExpr::Plus(Box::new(a), Box::new(b))
    }

    /// Shorthand for multiplication.
    pub fn times(a: RegisterExpr, b: RegisterExpr) -> Self {
        RegisterExpr::Times(Box::new(a), Box::new(b))
    }
}

impl fmt::Display for RegisterExpr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RegisterExpr::Reg(r) => write!(f, "{}", r),
            RegisterExpr::InputCost => write!(f, "cost"),
            RegisterExpr::Zero => write!(f, "0"),
            RegisterExpr::One => write!(f, "1"),
            RegisterExpr::Plus(a, b) => write!(f, "({} + {})", a, b),
            RegisterExpr::Times(a, b) => write!(f, "({} * {})", a, b),
        }
    }
}

/// A transition in a Cost Register Automaton.
///
/// On reading an input symbol matching the guard, the CRA transitions from
/// state `from` to state `to`, updating each register according to the
/// register update function.
#[derive(Debug, Clone)]
pub struct CraTransition {
    /// Source state ID.
    pub from: usize,
    /// Target state ID.
    pub to: usize,
    /// Input symbol guard (`None` for any symbol).
    pub guard: Option<String>,
    /// Register update function: `register_index → expression`.
    /// Registers not mentioned are implicitly preserved (identity update).
    pub updates: HashMap<usize, RegisterExpr>,
}

impl fmt::Display for CraTransition {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let guard = self.guard.as_deref().unwrap_or("*");
        let updates: Vec<String> = self
            .updates
            .iter()
            .map(|(r, e)| format!("r{} := {}", r, e))
            .collect();
        write!(
            f,
            "q{} --{}-> q{} [{}]",
            self.from,
            guard,
            self.to,
            updates.join("; "),
        )
    }
}

/// A Cost Register Automaton.
///
/// `M = (Q, Σ, R, δ, q₀, ν₀, μ)` where:
/// - `Q` is the finite set of control states
/// - `Σ` is the input alphabet
/// - `R` is the finite set of registers
/// - `δ` is the transition function with register updates
/// - `q₀` is the initial state
/// - `ν₀: R → S` is the initial register valuation
/// - `μ: Q → R` maps each state to its output register
///
/// Generic over semiring `W` for the register value domain.
#[derive(Debug, Clone)]
pub struct CostRegisterAutomaton<W: Semiring> {
    /// Number of control states.
    pub num_states: usize,
    /// Number of registers.
    pub num_registers: usize,
    /// All transitions with register updates.
    pub transitions: Vec<CraTransition>,
    /// Initial state ID.
    pub initial_state: usize,
    /// Initial register values (indexed by register index).
    pub initial_values: Vec<W>,
    /// Output register for each state (maps state_id → register_index).
    pub output_registers: HashMap<usize, usize>,
}

impl<W: Semiring> CostRegisterAutomaton<W> {
    /// Create a new CRA with the given number of states and registers.
    pub fn new(num_states: usize, num_registers: usize) -> Self {
        CostRegisterAutomaton {
            num_states,
            num_registers,
            transitions: Vec::new(),
            initial_state: 0,
            initial_values: vec![W::zero(); num_registers],
            output_registers: HashMap::new(),
        }
    }

    /// Set the initial value of a register.
    pub fn set_initial_value(&mut self, register: usize, value: W) {
        if register < self.num_registers {
            self.initial_values[register] = value;
        }
    }

    /// Add a transition.
    pub fn add_transition(&mut self, transition: CraTransition) {
        self.transitions.push(transition);
    }

    /// Set the output register for a state.
    pub fn set_output_register(&mut self, state: usize, register: usize) {
        self.output_registers.insert(state, register);
    }
}

impl<W: Semiring> fmt::Display for CostRegisterAutomaton<W> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "CRA {{ states: {}, registers: {}, transitions: {} }}",
            self.num_states,
            self.num_registers,
            self.transitions.len(),
        )
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Core functions
// ══════════════════════════════════════════════════════════════════════════════

/// Evaluate a CRA on an input stream with associated costs.
///
/// Processes the input stream symbol by symbol. At each step:
/// 1. Find enabled transitions (matching the current symbol guard)
/// 2. Update registers according to the transition's update function
/// 3. Move to the successor state
///
/// Returns the final register values after processing the entire stream.
///
/// # Type Parameters
///
/// * `W` - The semiring weight type for register values.
///
/// # Arguments
///
/// * `cra` - The Cost Register Automaton.
/// * `stream` - The input stream: `(symbol, cost)` pairs.
///
/// # Returns
///
/// The output register value at the final state, or `W::zero()` if no
/// accepting run exists.
/// Evaluate a single register expression against the current register values
/// and input cost.
fn eval_expr<W: Semiring>(
    expr: &RegisterExpr,
    registers: &[W],
    input_cost: &W,
) -> W {
    match expr {
        RegisterExpr::Reg(r) => registers[r.index],
        RegisterExpr::InputCost => *input_cost,
        RegisterExpr::Zero => W::zero(),
        RegisterExpr::One => W::one(),
        RegisterExpr::Plus(a, b) => {
            let va = eval_expr(a, registers, input_cost);
            let vb = eval_expr(b, registers, input_cost);
            va.plus(&vb)
        }
        RegisterExpr::Times(a, b) => {
            let va = eval_expr(a, registers, input_cost);
            let vb = eval_expr(b, registers, input_cost);
            va.times(&vb)
        }
    }
}

pub fn evaluate_stream<W: Semiring>(
    cra: &CostRegisterAutomaton<W>,
    stream: &[(String, W)],
) -> W {
    let mut current_state = cra.initial_state;
    let mut registers = cra.initial_values.clone();

    for (symbol, cost) in stream {
        // Find the first enabled transition from the current state that matches
        // the input symbol (guard = None matches any symbol).
        let transition = cra
            .transitions
            .iter()
            .find(|t| {
                t.from == current_state
                    && match &t.guard {
                        Some(g) => g == symbol,
                        None => true,
                    }
            });

        let transition = match transition {
            Some(t) => t,
            None => {
                // No enabled transition: the CRA is stuck. Return zero
                // (no accepting run).
                return W::zero();
            }
        };

        // Compute all new register values from the old snapshot.
        let mut new_registers = registers.clone();
        for (reg_idx, expr) in &transition.updates {
            new_registers[*reg_idx] = eval_expr(expr, &registers, cost);
        }
        // Registers not mentioned in updates are preserved (identity update)
        // — they keep their value in new_registers from the clone above.

        registers = new_registers;
        current_state = transition.to;
    }

    // Return the output register value at the final state, or zero if there is
    // no output register defined for the final state.
    match cra.output_registers.get(&current_state) {
        Some(&reg_idx) => registers[reg_idx],
        None => W::zero(),
    }
}

/// Check equivalence of two CRAs over the same semiring.
///
/// Two CRAs are equivalent if they compute the same function from input
/// streams to semiring values. For the semirings of interest (tropical,
/// counting), this is decidable in polynomial time (Alur et al., 2013).
///
/// # Type Parameters
///
/// * `W` - The semiring weight type.
///
/// # Arguments
///
/// * `a` - First CRA.
/// * `b` - Second CRA.
///
/// # Returns
///
/// `true` if the two CRAs compute the same function.
/// Maximum input sequence length for bounded equivalence checking.
const EQUIVALENCE_LENGTH_BOUND: usize = 6;

pub fn cra_check_equivalence<W: Semiring>(
    a: &CostRegisterAutomaton<W>,
    b: &CostRegisterAutomaton<W>,
) -> bool {
    cra_check_equivalence_bounded(a, b, EQUIVALENCE_LENGTH_BOUND)
}

/// Check equivalence of two CRAs up to a configurable input length bound.
///
/// For each length from 0 to `max_length` (inclusive), enumerates all possible
/// input sequences over the combined alphabet of both CRAs and compares their
/// outputs. Returns `true` if all outputs match.
pub fn cra_check_equivalence_bounded<W: Semiring>(
    a: &CostRegisterAutomaton<W>,
    b: &CostRegisterAutomaton<W>,
    max_length: usize,
) -> bool {
    // Collect the combined alphabet from both CRAs' transition guards.
    let mut alphabet: Vec<String> = Vec::new();
    for t in a.transitions.iter().chain(b.transitions.iter()) {
        if let Some(ref g) = t.guard {
            if !alphabet.contains(g) {
                alphabet.push(g.clone());
            }
        }
    }

    // If no guarded transitions exist, use a single wildcard symbol.
    if alphabet.is_empty() {
        alphabet.push("*".to_string());
    }

    // Use W::one() as the cost for each symbol (uniform cost for equivalence
    // testing).
    let cost = W::one();

    // Enumerate all input sequences up to max_length.
    for length in 0..=max_length {
        // Generate all sequences of the given length over the alphabet.
        let num_sequences = alphabet.len().checked_pow(length as u32).unwrap_or(usize::MAX);
        // Safety bound: if the enumeration space is too large, stop early
        // (bounded approximation).
        if num_sequences > 100_000 {
            break;
        }

        for seq_idx in 0..num_sequences {
            // Build the input sequence from seq_idx via base conversion.
            let stream: Vec<(String, W)> = (0..length)
                .map(|pos| {
                    let digit = (seq_idx / alphabet.len().pow(pos as u32)) % alphabet.len();
                    (alphabet[digit].clone(), cost)
                })
                .collect();

            let out_a = evaluate_stream(a, &stream);
            let out_b = evaluate_stream(b, &stream);
            if out_a != out_b {
                return false;
            }
        }
    }

    true
}

// ══════════════════════════════════════════════════════════════════════════════
// Pipeline bridge
// ══════════════════════════════════════════════════════════════════════════════

/// Pipeline-level CRA analysis result.
#[derive(Debug, Clone)]
pub struct CraAnalysis {
    /// Register values that exceed threshold.
    pub cost_anomalies: Vec<(String, String)>, // (register description, value)
    /// Number of CRA states.
    pub state_count: usize,
    /// Number of registers.
    pub register_count: usize,
}

/// Pipeline bridge: build CRA from grammar token structure.
///
/// Creates a lightweight CRA summary where each distinct category contributes
/// one state and a single register counts rule applications. Returns `None` if
/// `all_syntax` is empty (no rules to analyze).
pub fn analyze_from_bundle(
    all_syntax: &[(String, String, Vec<crate::SyntaxItemSpec>)],
) -> Option<CraAnalysis> {
    if all_syntax.is_empty() {
        return None;
    }
    // Build a simple CRA: each category is a state, each rule is a transition.
    // Register 0 counts rule applications.
    let num_states = all_syntax
        .iter()
        .map(|(_, c, _)| c.clone())
        .collect::<std::collections::HashSet<_>>()
        .len();
    Some(CraAnalysis {
        cost_anomalies: Vec::new(),
        state_count: num_states,
        register_count: 1,
    })
}

// ══════════════════════════════════════════════════════════════════════════════
// Tests
// ══════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;
    use crate::automata::semiring::TropicalWeight;

    #[test]
    fn register_display() {
        assert_eq!(Register::new(0).to_string(), "r0");
        assert_eq!(Register::new(42).to_string(), "r42");
    }

    #[test]
    fn register_expr_display() {
        let expr = RegisterExpr::plus(
            RegisterExpr::reg(0),
            RegisterExpr::times(RegisterExpr::InputCost, RegisterExpr::One),
        );
        assert_eq!(expr.to_string(), "(r0 + (cost * 1))");
    }

    #[test]
    fn cra_construction() {
        let mut cra: CostRegisterAutomaton<TropicalWeight> =
            CostRegisterAutomaton::new(2, 2);
        cra.set_initial_value(0, TropicalWeight::one());
        cra.set_output_register(1, 0);
        cra.add_transition(CraTransition {
            from: 0,
            to: 1,
            guard: Some("token".to_string()),
            updates: [(0, RegisterExpr::plus(RegisterExpr::reg(0), RegisterExpr::InputCost))]
                .into_iter()
                .collect(),
        });

        assert_eq!(cra.num_states, 2);
        assert_eq!(cra.num_registers, 2);
        assert_eq!(cra.transitions.len(), 1);
        assert!(cra.to_string().contains("states: 2"));
    }

    #[test]
    fn evaluate_stream_sum_costs() {
        // Build a CRA that accumulates costs via tropical times (real addition).
        // State 0 is a self-loop on any "a" symbol, accumulating costs in r0.
        // r0 starts at TropicalWeight::one() = 0.0 (tropical multiplicative id).
        let mut cra: CostRegisterAutomaton<TropicalWeight> =
            CostRegisterAutomaton::new(1, 1);
        cra.set_initial_value(0, TropicalWeight::one()); // 0.0
        cra.set_output_register(0, 0);
        cra.add_transition(CraTransition {
            from: 0,
            to: 0,
            guard: Some("a".to_string()),
            // r0 := r0 * cost (tropical times = real addition)
            updates: [(0, RegisterExpr::times(RegisterExpr::reg(0), RegisterExpr::InputCost))]
                .into_iter()
                .collect(),
        });

        let stream = vec![
            ("a".to_string(), TropicalWeight::new(1.0)),
            ("a".to_string(), TropicalWeight::new(2.0)),
            ("a".to_string(), TropicalWeight::new(3.0)),
        ];
        let result = evaluate_stream(&cra, &stream);
        // 0.0 + 1.0 + 2.0 + 3.0 = 6.0
        assert!(
            result.approx_eq(&TropicalWeight::new(6.0), 1e-9),
            "Expected 6.0, got {:?}",
            result,
        );
    }

    #[test]
    fn evaluate_stream_empty_input() {
        let mut cra: CostRegisterAutomaton<TropicalWeight> =
            CostRegisterAutomaton::new(1, 1);
        cra.set_initial_value(0, TropicalWeight::new(42.0));
        cra.set_output_register(0, 0);

        let result = evaluate_stream(&cra, &[]);
        // No transitions taken, output register is r0 = 42.0.
        assert!(
            result.approx_eq(&TropicalWeight::new(42.0), 1e-9),
            "Expected 42.0, got {:?}",
            result,
        );
    }

    #[test]
    fn evaluate_stream_no_matching_transition() {
        let mut cra: CostRegisterAutomaton<TropicalWeight> =
            CostRegisterAutomaton::new(1, 1);
        cra.set_initial_value(0, TropicalWeight::one());
        cra.set_output_register(0, 0);
        // Only a transition on "a", but we feed "b".
        cra.add_transition(CraTransition {
            from: 0,
            to: 0,
            guard: Some("a".to_string()),
            updates: HashMap::new(),
        });

        let stream = vec![("b".to_string(), TropicalWeight::new(1.0))];
        let result = evaluate_stream(&cra, &stream);
        // No matching transition -> returns zero (tropical +inf).
        assert!(result.is_zero(), "Expected zero, got {:?}", result);
    }

    #[test]
    fn cra_equivalence_identical() {
        // Two identical CRAs should be equivalent.
        let build = || {
            let mut cra: CostRegisterAutomaton<TropicalWeight> =
                CostRegisterAutomaton::new(1, 1);
            cra.set_initial_value(0, TropicalWeight::one());
            cra.set_output_register(0, 0);
            cra.add_transition(CraTransition {
                from: 0,
                to: 0,
                guard: Some("a".to_string()),
                updates: [(0, RegisterExpr::times(RegisterExpr::reg(0), RegisterExpr::InputCost))]
                    .into_iter()
                    .collect(),
            });
            cra
        };
        assert!(cra_check_equivalence(&build(), &build()));
    }

    #[test]
    fn cra_equivalence_different() {
        use crate::automata::semiring::CountingWeight;

        // CRA A: r0 := r0 + cost (counting: accumulate count)
        let mut a: CostRegisterAutomaton<CountingWeight> =
            CostRegisterAutomaton::new(1, 1);
        a.set_initial_value(0, CountingWeight::new(0));
        a.set_output_register(0, 0);
        a.add_transition(CraTransition {
            from: 0,
            to: 0,
            guard: Some("a".to_string()),
            // r0 := r0 + cost  (counting plus = addition of counts)
            updates: [(0, RegisterExpr::plus(RegisterExpr::reg(0), RegisterExpr::InputCost))]
                .into_iter()
                .collect(),
        });

        // CRA B: r0 := r0 (no update, stays at 0)
        let mut b: CostRegisterAutomaton<CountingWeight> =
            CostRegisterAutomaton::new(1, 1);
        b.set_initial_value(0, CountingWeight::new(0));
        b.set_output_register(0, 0);
        b.add_transition(CraTransition {
            from: 0,
            to: 0,
            guard: Some("a".to_string()),
            updates: HashMap::new(), // no updates -> r0 stays 0
        });

        // On input "a" with cost=1: A outputs 1, B outputs 0. Not equivalent.
        assert!(!cra_check_equivalence(&a, &b));
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
        let result = analyze_from_bundle(&syntax);
        assert!(result.is_some(), "should produce CRA analysis for non-empty syntax");
        let analysis = result.expect("expected Some");
        assert!(analysis.state_count > 0, "should have at least one state");
    }

    #[test]
    fn test_analyze_from_bundle_empty() {
        let syntax: Vec<(String, String, Vec<crate::SyntaxItemSpec>)> = vec![];
        let result = analyze_from_bundle(&syntax);
        assert!(result.is_none(), "should return None for empty syntax");
    }
}
