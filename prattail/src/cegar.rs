//! Counterexample-Guided Abstraction Refinement (CEGAR) for MeTTaIL.
//!
//! Implements the CEGAR loop from Clarke et al. (2000): iteratively refine an
//! abstract model until a property is either proved or a real counterexample is
//! found.
//!
//! ## Algorithm
//!
//! ```text
//! 1. Start with a coarse abstraction (BooleanWeight reachability)
//! 2. Model-check the abstraction via WPDS prestar
//! 3. If property holds, done (proof)
//! 4. If counterexample found, validate against the concrete model
//! 5. If spurious, refine abstraction and repeat
//! ```
//!
//! ## Abstraction Hierarchy
//!
//! The CEGAR loop walks a ladder of semiring precision:
//!
//! ```text
//! BooleanWeight  (coarsest -- just reachability)
//!       |
//!       | refine
//!       v
//! CountingWeight (exact path multiplicity)
//!       |
//!       | refine
//!       v
//! TropicalWeight (minimum-cost path -- most precise)
//! ```
//!
//! Each refinement level provides strictly more information about the system,
//! which means spurious counterexamples at a coarser level may be eliminated
//! at a finer level.
//!
//! ## Static Typing Strategy
//!
//! Since Rust is statically typed, we cannot change the semiring type at runtime.
//! Instead, `abstract_check_at_level` projects the concrete `TropicalWeight` WPDS
//! down to the target semiring via weight-mapping functions:
//!
//! - **Boolean**: project all non-zero weights to `true`
//! - **Counting**: map each non-zero weight to count `1`
//! - **Tropical**: use actual weights (identity projection)
//!
//! ## References
//!
//! - Clarke, Grumberg, Jha, Lu & Veith (2000),
//!   *Counterexample-Guided Abstraction Refinement*
//! - Reps, Lal & Kidd (2007),
//!   *Program Analysis Using Weighted Pushdown Systems*

use std::collections::HashMap;
use std::fmt;

use crate::automata::semiring::{BooleanWeight, CountingWeight, Semiring, TropicalWeight};
use crate::verify::Verdict;
use crate::wpds::{PAutomaton, PAutomatonStateId, StackSymbol, Wpds, WpdsRule};

// ==============================================================================
// Types
// ==============================================================================

/// The abstraction level in the CEGAR refinement hierarchy.
///
/// Each successive level provides strictly more information, at the cost of
/// higher analysis complexity.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum AbstractionLevel {
    /// Coarsest: Boolean reachability (can the bad state be reached at all?).
    Boolean,
    /// Intermediate: exact path multiplicity (how many paths reach the bad state?).
    Counting,
    /// Most precise: minimum-cost path (what is the cheapest path to the bad state?).
    Tropical,
    /// User-defined abstraction level (for future extensibility).
    Custom(String),
}

impl fmt::Display for AbstractionLevel {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            AbstractionLevel::Boolean => write!(f, "Boolean"),
            AbstractionLevel::Counting => write!(f, "Counting"),
            AbstractionLevel::Tropical => write!(f, "Tropical"),
            AbstractionLevel::Custom(name) => write!(f, "Custom({})", name),
        }
    }
}

/// A sequence of stack symbols representing an abstract counterexample path.
///
/// This trace shows the stack symbols visited along the path from the initial
/// configuration to the bad state in the abstract model. When validated against
/// the concrete model, a spurious trace will have zero weight (unreachable).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CounterexampleTrace {
    /// The stack symbols along the path, in order from initial to bad state.
    pub symbols: Vec<StackSymbol>,
    /// Human-readable description of why this trace was flagged.
    pub description: String,
}

impl fmt::Display for CounterexampleTrace {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[")?;
        for (i, sym) in self.symbols.iter().enumerate() {
            if i > 0 {
                write!(f, " -> ")?;
            }
            write!(f, "{}", sym)?;
        }
        write!(f, "]")?;
        if !self.description.is_empty() {
            write!(f, " ({})", self.description)?;
        }
        Ok(())
    }
}

/// What happened at a single CEGAR iteration.
#[derive(Debug, Clone)]
pub struct RefinementStep {
    /// The abstraction level used for this iteration.
    pub level: AbstractionLevel,
    /// The verdict from model checking at this level.
    pub verdict: Verdict,
    /// The counterexample trace, if a violation was found.
    pub counterexample: Option<CounterexampleTrace>,
    /// Whether the counterexample was determined to be spurious.
    pub is_spurious: bool,
    /// Description of the refinement action taken (empty if no refinement).
    pub refinement_action: String,
}

impl fmt::Display for RefinementStep {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[{}] verdict={}", self.level, self.verdict)?;
        if let Some(ref cex) = self.counterexample {
            write!(f, ", cex={}", cex)?;
        }
        if self.is_spurious {
            write!(f, " (SPURIOUS)")?;
        }
        if !self.refinement_action.is_empty() {
            write!(f, ", action: {}", self.refinement_action)?;
        }
        Ok(())
    }
}

/// Trace of all refinement steps for diagnostic output.
#[derive(Debug, Clone)]
pub struct CegarLog {
    /// All refinement steps in chronological order.
    pub steps: Vec<RefinementStep>,
}

impl CegarLog {
    /// Create an empty log.
    pub fn new() -> Self {
        CegarLog { steps: Vec::new() }
    }

    /// Record a refinement step.
    pub fn add_step(&mut self, step: RefinementStep) {
        self.steps.push(step);
    }

    /// Number of refinement steps recorded.
    pub fn num_steps(&self) -> usize {
        self.steps.len()
    }

    /// Whether any step found a spurious counterexample.
    pub fn had_spurious(&self) -> bool {
        self.steps.iter().any(|s| s.is_spurious)
    }
}

impl Default for CegarLog {
    fn default() -> Self {
        Self::new()
    }
}

impl fmt::Display for CegarLog {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "CEGAR Log ({} steps):", self.steps.len())?;
        for (i, step) in self.steps.iter().enumerate() {
            writeln!(f, "  step {}: {}", i, step)?;
        }
        Ok(())
    }
}

/// Configuration for the CEGAR loop.
#[derive(Debug, Clone)]
pub struct CegarConfig {
    /// Maximum number of refinement iterations before giving up.
    pub max_refinements: usize,
    /// The starting abstraction level.
    pub initial_level: AbstractionLevel,
}

impl Default for CegarConfig {
    fn default() -> Self {
        CegarConfig {
            max_refinements: 10,
            initial_level: AbstractionLevel::Boolean,
        }
    }
}

/// The final result of a CEGAR verification run.
#[derive(Debug, Clone)]
pub enum CegarResult {
    /// Property verified at the given abstraction level. No counterexample exists.
    Verified {
        /// The abstraction level at which verification succeeded.
        level: AbstractionLevel,
        /// Full refinement log.
        log: CegarLog,
    },
    /// Property refuted with a concrete (non-spurious) counterexample.
    Refuted {
        /// The concrete counterexample trace.
        trace: CounterexampleTrace,
        /// Full refinement log.
        log: CegarLog,
    },
    /// Maximum refinements reached without conclusive result.
    Inconclusive(CegarLog),
}

impl CegarResult {
    /// Whether the result is a successful verification.
    pub fn is_verified(&self) -> bool {
        matches!(self, CegarResult::Verified { .. })
    }

    /// Whether the result is a refutation.
    pub fn is_refuted(&self) -> bool {
        matches!(self, CegarResult::Refuted { .. })
    }

    /// Whether the result is inconclusive.
    pub fn is_inconclusive(&self) -> bool {
        matches!(self, CegarResult::Inconclusive(_))
    }

    /// Extract the log from any result variant.
    pub fn log(&self) -> &CegarLog {
        match self {
            CegarResult::Verified { log, .. } => log,
            CegarResult::Refuted { log, .. } => log,
            CegarResult::Inconclusive(log) => log,
        }
    }
}

impl fmt::Display for CegarResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CegarResult::Verified { level, log } => {
                write!(
                    f,
                    "VERIFIED at {} level ({} refinement steps)",
                    level,
                    log.num_steps()
                )
            }
            CegarResult::Refuted { trace, log } => {
                write!(
                    f,
                    "REFUTED with counterexample {} ({} refinement steps)",
                    trace,
                    log.num_steps()
                )
            }
            CegarResult::Inconclusive(log) => {
                write!(
                    f,
                    "INCONCLUSIVE after {} refinement steps",
                    log.num_steps()
                )
            }
        }
    }
}

// ==============================================================================
// Projection functions: TropicalWeight -> abstract semirings
// ==============================================================================

/// Project a `TropicalWeight` WPDS to a `BooleanWeight` WPDS.
///
/// All non-zero weights become `true` (reachable); zero weights stay `false`.
fn project_wpds_to_boolean(wpds: &Wpds<TropicalWeight>) -> Wpds<BooleanWeight> {
    let project_weight = |w: &TropicalWeight| -> BooleanWeight {
        BooleanWeight(!w.is_zero())
    };

    let rules: Vec<WpdsRule<BooleanWeight>> = wpds
        .rules
        .iter()
        .map(|rule| match rule {
            WpdsRule::Pop { from_gamma, weight } => WpdsRule::Pop {
                from_gamma: from_gamma.clone(),
                weight: project_weight(weight),
            },
            WpdsRule::Replace {
                from_gamma,
                to_gamma,
                weight,
            } => WpdsRule::Replace {
                from_gamma: from_gamma.clone(),
                to_gamma: to_gamma.clone(),
                weight: project_weight(weight),
            },
            WpdsRule::Push {
                from_gamma,
                to_gamma_bottom,
                to_gamma_top,
                weight,
            } => WpdsRule::Push {
                from_gamma: from_gamma.clone(),
                to_gamma_bottom: to_gamma_bottom.clone(),
                to_gamma_top: to_gamma_top.clone(),
                weight: project_weight(weight),
            },
        })
        .collect();

    let mut rules_by_source: HashMap<StackSymbol, Vec<usize>> =
        HashMap::with_capacity(wpds.rules_by_source.len());
    for (sym, indices) in &wpds.rules_by_source {
        rules_by_source.insert(sym.clone(), indices.clone());
    }

    Wpds {
        stack_symbols: wpds.stack_symbols.clone(),
        symbol_index: wpds.symbol_index.clone(),
        rules,
        rules_by_source,
        initial_symbol: wpds.initial_symbol.clone(),
        grammar_name: wpds.grammar_name.clone(),
    }
}

/// Project a `TropicalWeight` WPDS to a `CountingWeight` WPDS.
///
/// All non-zero weights become `CountingWeight(1)` (one path); zero weights
/// stay `CountingWeight(0)`.
fn project_wpds_to_counting(wpds: &Wpds<TropicalWeight>) -> Wpds<CountingWeight> {
    let project_weight = |w: &TropicalWeight| -> CountingWeight {
        if w.is_zero() {
            CountingWeight::zero()
        } else {
            CountingWeight::one()
        }
    };

    let rules: Vec<WpdsRule<CountingWeight>> = wpds
        .rules
        .iter()
        .map(|rule| match rule {
            WpdsRule::Pop { from_gamma, weight } => WpdsRule::Pop {
                from_gamma: from_gamma.clone(),
                weight: project_weight(weight),
            },
            WpdsRule::Replace {
                from_gamma,
                to_gamma,
                weight,
            } => WpdsRule::Replace {
                from_gamma: from_gamma.clone(),
                to_gamma: to_gamma.clone(),
                weight: project_weight(weight),
            },
            WpdsRule::Push {
                from_gamma,
                to_gamma_bottom,
                to_gamma_top,
                weight,
            } => WpdsRule::Push {
                from_gamma: from_gamma.clone(),
                to_gamma_bottom: to_gamma_bottom.clone(),
                to_gamma_top: to_gamma_top.clone(),
                weight: project_weight(weight),
            },
        })
        .collect();

    let mut rules_by_source: HashMap<StackSymbol, Vec<usize>> =
        HashMap::with_capacity(wpds.rules_by_source.len());
    for (sym, indices) in &wpds.rules_by_source {
        rules_by_source.insert(sym.clone(), indices.clone());
    }

    Wpds {
        stack_symbols: wpds.stack_symbols.clone(),
        symbol_index: wpds.symbol_index.clone(),
        rules,
        rules_by_source,
        initial_symbol: wpds.initial_symbol.clone(),
        grammar_name: wpds.grammar_name.clone(),
    }
}

/// Project a `TropicalWeight` P-automaton to a `BooleanWeight` P-automaton.
fn project_pautomaton_to_boolean(pa: &PAutomaton<TropicalWeight>) -> PAutomaton<BooleanWeight> {
    let mut result = PAutomaton::new(pa.initial_state);
    result.num_states = pa.num_states;
    result.final_states = pa.final_states.clone();
    result.symbol_to_state = pa.symbol_to_state.clone();

    for trans in &pa.transitions {
        let weight = BooleanWeight(!trans.weight.is_zero());
        result.add_transition(trans.from, trans.symbol.clone(), trans.to, weight);
    }

    result
}

/// Project a `TropicalWeight` P-automaton to a `CountingWeight` P-automaton.
fn project_pautomaton_to_counting(pa: &PAutomaton<TropicalWeight>) -> PAutomaton<CountingWeight> {
    let mut result = PAutomaton::new(pa.initial_state);
    result.num_states = pa.num_states;
    result.final_states = pa.final_states.clone();
    result.symbol_to_state = pa.symbol_to_state.clone();

    for trans in &pa.transitions {
        let weight = if trans.weight.is_zero() {
            CountingWeight::zero()
        } else {
            CountingWeight::one()
        };
        result.add_transition(trans.from, trans.symbol.clone(), trans.to, weight);
    }

    result
}

// ==============================================================================
// Core CEGAR functions
// ==============================================================================

/// Perform an abstract reachability check on a WPDS at a given semiring level.
///
/// Uses `prestar` to compute backward reachability from the bad states, then
/// checks whether the initial configuration is in the resulting set.
///
/// Returns the verdict and an optional counterexample trace (if violated).
pub fn abstract_check<W: Semiring>(
    wpds: &Wpds<W>,
    bad_states: &PAutomaton<W>,
) -> (Verdict, Option<CounterexampleTrace>) {
    let prestar_result = crate::wpds::prestar(wpds, bad_states);

    // Check if there is a path from initial_state reading the initial symbol
    // to any final state. This is the correct acceptance check for P-automata:
    // the initial configuration ⟨p, γ₀⟩ is in the prestar result iff
    // there exists a path p --γ₀--> q where q is a final state.
    let reachable = accepts_initial_config(&prestar_result, &wpds.initial_symbol);

    if !reachable {
        (Verdict::Verified, None)
    } else {
        let trace = extract_trace_from_prestar(&prestar_result, &wpds.initial_symbol);
        (Verdict::Violated, Some(trace))
    }
}

/// Check if a P-automaton accepts the initial configuration ⟨p, symbol⟩.
///
/// Returns true iff there exists a transition (initial_state, symbol, q) with
/// non-zero weight where q is a final state or can reach a final state via
/// epsilon-like paths. For single-symbol stack configurations, we just check
/// if q is directly a final state.
fn accepts_initial_config<W: Semiring>(
    automaton: &PAutomaton<W>,
    symbol: &StackSymbol,
) -> bool {
    if let Some(trans_indices) = automaton.transitions_by_source.get(&automaton.initial_state) {
        for &idx in trans_indices {
            let t = &automaton.transitions[idx];
            if t.symbol == *symbol && !t.weight.is_zero() {
                if automaton.final_states.contains(&t.to) {
                    return true;
                }
            }
        }
    }
    false
}

/// Extract a counterexample trace from a prestar result.
///
/// Follows non-zero-weight transitions from the initial state to a final state,
/// collecting the stack symbols along the way.
fn extract_trace_from_prestar<W: Semiring>(
    prestar_result: &PAutomaton<W>,
    initial_symbol: &StackSymbol,
) -> CounterexampleTrace {
    let mut symbols = Vec::new();
    let mut current_state = prestar_result.initial_state;

    // Start by finding a transition on the initial symbol.
    if let Some(trans_indices) = prestar_result.transitions_by_source.get(&current_state) {
        for &idx in trans_indices {
            let t = &prestar_result.transitions[idx];
            if t.symbol == *initial_symbol && !t.weight.is_zero() {
                symbols.push(t.symbol.clone());
                current_state = t.to;
                break;
            }
        }
    }

    // Follow non-zero transitions, collecting stack symbols.
    let mut visited = std::collections::HashSet::new();
    visited.insert(current_state);
    loop {
        let mut found = false;
        if let Some(trans_indices) = prestar_result.transitions_by_source.get(&current_state) {
            for &idx in trans_indices {
                let t = &prestar_result.transitions[idx];
                if !t.weight.is_zero() && !visited.contains(&t.to) {
                    symbols.push(t.symbol.clone());
                    visited.insert(t.to);
                    current_state = t.to;
                    found = true;
                    break;
                }
            }
        }
        if !found || prestar_result.final_states.contains(&current_state) {
            break;
        }
    }

    CounterexampleTrace {
        symbols,
        description: String::new(),
    }
}

/// Check at a specific abstraction level by projecting the concrete WPDS.
///
/// This is the key function that bridges static typing with runtime abstraction
/// level selection. It projects the concrete `TropicalWeight` WPDS to the
/// target semiring, runs `prestar`, and returns the result.
fn abstract_check_at_level(
    level: &AbstractionLevel,
    wpds: &Wpds<TropicalWeight>,
    bad_states: &PAutomaton<TropicalWeight>,
) -> (Verdict, Option<CounterexampleTrace>) {
    match level {
        AbstractionLevel::Boolean => {
            let abs_wpds = project_wpds_to_boolean(wpds);
            let abs_bad = project_pautomaton_to_boolean(bad_states);
            abstract_check(&abs_wpds, &abs_bad)
        }
        AbstractionLevel::Counting => {
            let abs_wpds = project_wpds_to_counting(wpds);
            let abs_bad = project_pautomaton_to_counting(bad_states);
            abstract_check(&abs_wpds, &abs_bad)
        }
        AbstractionLevel::Tropical => {
            // No projection needed -- use the concrete model directly.
            abstract_check(wpds, bad_states)
        }
        AbstractionLevel::Custom(_) => {
            // Custom levels are treated as opaque; return Unknown.
            (Verdict::Unknown, None)
        }
    }
}

/// Check whether a counterexample trace is spurious by validating it against
/// the concrete (TropicalWeight) WPDS.
///
/// A trace is spurious if, when checked at the concrete level, the corresponding
/// path has zero weight (i.e., is unreachable in the concrete model).
///
/// The validation works by constructing a P-automaton that accepts exactly the
/// counterexample trace, then running `prestar` on the concrete WPDS to check
/// whether the initial configuration can reach the trace's configuration.
pub fn check_spurious(
    trace: &CounterexampleTrace,
    wpds: &Wpds<TropicalWeight>,
) -> bool {
    if trace.symbols.is_empty() {
        // An empty trace is vacuously spurious (no actual counterexample).
        return true;
    }

    // Build a P-automaton that accepts exactly the trace's stack symbols.
    let initial_state: PAutomatonStateId = 0;
    let mut trace_automaton = PAutomaton::new(initial_state);

    // Create a chain of states: s0 --sym[0]--> s1 --sym[1]--> ... --sym[n-1]--> s_final
    let mut current = initial_state;
    for sym in &trace.symbols {
        let next = trace_automaton.add_state();
        trace_automaton.add_transition(current, sym.clone(), next, TropicalWeight::one());
        trace_automaton.symbol_to_state.insert(sym.clone(), next);
        current = next;
    }
    trace_automaton.mark_final(current);

    // Run prestar on the concrete WPDS with this trace automaton.
    let prestar_result = crate::wpds::prestar(wpds, &trace_automaton);

    // If the initial config is not accepted by the prestar result, the trace
    // is unreachable in the concrete model -- it is spurious.
    !accepts_initial_config(&prestar_result, &wpds.initial_symbol)
}

/// Attempt to refine the abstraction to the next level in the hierarchy.
///
/// Returns `Some(next_level)` if refinement is possible, or `None` if we are
/// already at the most precise level (or the level is custom/unknown).
pub fn refine(current_level: &AbstractionLevel) -> Option<AbstractionLevel> {
    match current_level {
        AbstractionLevel::Boolean => Some(AbstractionLevel::Counting),
        AbstractionLevel::Counting => Some(AbstractionLevel::Tropical),
        AbstractionLevel::Tropical => None, // Already at the most precise level.
        AbstractionLevel::Custom(_) => None, // Cannot refine a custom level.
    }
}

/// Main CEGAR verification loop.
///
/// Iteratively refines an abstract model of the given WPDS until the property
/// (encoded as `bad_states`) is either:
/// - **Verified**: proved unreachable at some abstraction level, or
/// - **Refuted**: a concrete counterexample is found, or
/// - **Inconclusive**: the maximum number of refinements is exhausted.
///
/// # Arguments
///
/// * `wpds` - The concrete (TropicalWeight) WPDS to verify.
/// * `bad_states` - P-automaton encoding the set of "bad" configurations.
/// * `config` - Configuration controlling initial level and max refinements.
///
/// # Example
///
/// ```ignore
/// let result = cegar_verify(&wpds, &bad_automaton, &CegarConfig::default());
/// match result {
///     CegarResult::Verified { level, .. } => println!("Safe at {} level", level),
///     CegarResult::Refuted { trace, .. } => println!("Bug: {}", trace),
///     CegarResult::Inconclusive(_) => println!("Could not decide"),
/// }
/// ```
pub fn cegar_verify(
    wpds: &Wpds<TropicalWeight>,
    bad_states: &PAutomaton<TropicalWeight>,
    config: &CegarConfig,
) -> CegarResult {
    let mut level = config.initial_level.clone();
    let mut log = CegarLog::new();

    for iteration in 0..config.max_refinements {
        let (verdict, trace) = abstract_check_at_level(&level, wpds, bad_states);

        match verdict {
            Verdict::Verified => {
                log.add_step(RefinementStep {
                    level: level.clone(),
                    verdict: Verdict::Verified,
                    counterexample: None,
                    is_spurious: false,
                    refinement_action: String::new(),
                });
                return CegarResult::Verified { level, log };
            }
            Verdict::Violated => {
                if let Some(trace) = trace {
                    let spurious = check_spurious(&trace, wpds);

                    if !spurious {
                        // Real counterexample found.
                        log.add_step(RefinementStep {
                            level: level.clone(),
                            verdict: Verdict::Violated,
                            counterexample: Some(trace.clone()),
                            is_spurious: false,
                            refinement_action: String::new(),
                        });
                        return CegarResult::Refuted { trace, log };
                    }

                    // Spurious counterexample -- need to refine.
                    match refine(&level) {
                        Some(next_level) => {
                            let action = format!(
                                "refinement {} -> {} (spurious cex at iteration {})",
                                level, next_level, iteration
                            );
                            log.add_step(RefinementStep {
                                level: level.clone(),
                                verdict: Verdict::Violated,
                                counterexample: Some(trace),
                                is_spurious: true,
                                refinement_action: action,
                            });
                            level = next_level;
                        }
                        None => {
                            // Cannot refine further -- this is a real counterexample
                            // at the most precise level.
                            log.add_step(RefinementStep {
                                level: level.clone(),
                                verdict: Verdict::Violated,
                                counterexample: Some(trace.clone()),
                                is_spurious: false,
                                refinement_action: "no further refinement available".to_string(),
                            });
                            return CegarResult::Refuted { trace, log };
                        }
                    }
                } else {
                    // Violated but no trace -- try refining.
                    match refine(&level) {
                        Some(next_level) => {
                            let action = format!(
                                "refinement {} -> {} (no trace at iteration {})",
                                level, next_level, iteration
                            );
                            log.add_step(RefinementStep {
                                level: level.clone(),
                                verdict: Verdict::Violated,
                                counterexample: None,
                                is_spurious: false,
                                refinement_action: action,
                            });
                            level = next_level;
                        }
                        None => {
                            log.add_step(RefinementStep {
                                level: level.clone(),
                                verdict: Verdict::Violated,
                                counterexample: None,
                                is_spurious: false,
                                refinement_action: "no further refinement available".to_string(),
                            });
                            return CegarResult::Inconclusive(log);
                        }
                    }
                }
            }
            Verdict::Unknown => {
                // Unknown verdict -- try refining to a more precise level.
                match refine(&level) {
                    Some(next_level) => {
                        let action = format!(
                            "refinement {} -> {} (unknown verdict at iteration {})",
                            level, next_level, iteration
                        );
                        log.add_step(RefinementStep {
                            level: level.clone(),
                            verdict: Verdict::Unknown,
                            counterexample: None,
                            is_spurious: false,
                            refinement_action: action,
                        });
                        level = next_level;
                    }
                    None => {
                        log.add_step(RefinementStep {
                            level: level.clone(),
                            verdict: Verdict::Unknown,
                            counterexample: None,
                            is_spurious: false,
                            refinement_action: "no further refinement available".to_string(),
                        });
                        return CegarResult::Inconclusive(log);
                    }
                }
            }
        }
    }

    // Exhausted max refinements.
    CegarResult::Inconclusive(log)
}

// ==============================================================================
// Adaptive optimization via CEGAR (Phase 5B.8)
// ==============================================================================

/// An optimization candidate identified by analysis.
#[derive(Debug, Clone)]
pub struct OptimizationCandidate {
    /// Which stack symbol (rule position) the optimization targets.
    pub target: StackSymbol,
    /// Description of the proposed optimization.
    pub description: String,
    /// The abstraction level at which this was identified.
    pub identified_at: AbstractionLevel,
    /// Whether the optimization has been validated at a more precise level.
    pub validated: bool,
}

impl fmt::Display for OptimizationCandidate {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}: {} (at {}, validated={})",
            self.target, self.description, self.identified_at, self.validated
        )
    }
}

/// Result of a CEGAR-driven adaptive optimization pass.
#[derive(Debug, Clone)]
pub struct AdaptiveOptResult {
    /// Candidates that were confirmed safe by analysis.
    pub confirmed: Vec<OptimizationCandidate>,
    /// Candidates that were rejected (would be unsound).
    pub rejected: Vec<OptimizationCandidate>,
    /// Log of the analysis steps.
    pub log: CegarLog,
}

/// Identify dead rules (unreachable stack symbols) via CEGAR-guided analysis.
///
/// Uses the CEGAR strategy: start with cheap Boolean analysis, then refine
/// with Counting or Tropical only for ambiguous cases.
///
/// 1. Boolean prestar: identify all reachable rules (cheap)
/// 2. For rules that appear unreachable, validate with Counting (are there
///    really zero paths?)
/// 3. Report confirmed dead rules as optimization candidates for elimination
pub fn adaptive_dead_rule_elimination(
    wpds: &Wpds<TropicalWeight>,
    _initial_symbol: &StackSymbol,
) -> AdaptiveOptResult {
    let mut log = CegarLog::new();
    let mut confirmed = Vec::new();
    let mut rejected = Vec::new();

    // Phase 1: Boolean reachability (cheapest)
    let bool_wpds = project_wpds_to_boolean(wpds);

    // Run poststar to find all reachable symbols
    let poststar_result = crate::wpds::poststar(&bool_wpds);

    // Collect all symbols that have non-zero weight in poststar result
    let mut reachable_symbols = std::collections::HashSet::new();
    for t in &poststar_result.transitions {
        if !t.weight.is_zero() {
            reachable_symbols.insert(t.symbol.clone());
        }
    }

    log.add_step(RefinementStep {
        level: AbstractionLevel::Boolean,
        verdict: Verdict::Verified,
        counterexample: None,
        is_spurious: false,
        refinement_action: format!(
            "Boolean poststar: {}/{} symbols reachable",
            reachable_symbols.len(),
            wpds.stack_symbols.len()
        ),
    });

    // Phase 2: For each unreachable symbol, validate with Counting
    let unreachable: Vec<_> = wpds
        .stack_symbols
        .iter()
        .filter(|s| !reachable_symbols.contains(s))
        .cloned()
        .collect();

    if !unreachable.is_empty() {
        let count_wpds = project_wpds_to_counting(wpds);

        let count_poststar = crate::wpds::poststar(&count_wpds);

        let mut count_reachable = std::collections::HashSet::new();
        for t in &count_poststar.transitions {
            if !t.weight.is_zero() {
                count_reachable.insert(t.symbol.clone());
            }
        }

        for sym in &unreachable {
            if count_reachable.contains(sym) {
                // Spurious: Boolean said unreachable but Counting finds a path
                rejected.push(OptimizationCandidate {
                    target: sym.clone(),
                    description: format!(
                        "Boolean reported unreachable but Counting found paths"
                    ),
                    identified_at: AbstractionLevel::Boolean,
                    validated: false,
                });
            } else {
                // Confirmed: both Boolean and Counting agree it's unreachable
                confirmed.push(OptimizationCandidate {
                    target: sym.clone(),
                    description: "dead rule: confirmed unreachable by Boolean+Counting"
                        .to_string(),
                    identified_at: AbstractionLevel::Counting,
                    validated: true,
                });
            }
        }

        log.add_step(RefinementStep {
            level: AbstractionLevel::Counting,
            verdict: Verdict::Verified,
            counterexample: None,
            is_spurious: false,
            refinement_action: format!(
                "Counting validation: {}/{} dead rules confirmed, {} rejected",
                confirmed.len(),
                unreachable.len(),
                rejected.len()
            ),
        });
    }

    AdaptiveOptResult {
        confirmed,
        rejected,
        log,
    }
}

/// Analyze dispatch determinism at each rule position via CEGAR.
///
/// For each category entry, determine if dispatch is deterministic (count=1),
/// finitely ambiguous (count>1), or requires more precise analysis.
pub fn adaptive_dispatch_analysis(
    wpds: &Wpds<TropicalWeight>,
) -> Vec<(StackSymbol, DispatchClassification)> {
    let mut results = Vec::new();

    // Only analyze category entries
    let entries: Vec<_> = wpds
        .stack_symbols
        .iter()
        .filter(|s| s.rule_label.is_empty())
        .cloned()
        .collect();

    let count_wpds = project_wpds_to_counting(wpds);

    for entry in &entries {
        // Count how many rules this entry can dispatch to
        let rule_count = wpds
            .rules
            .iter()
            .filter(|r| match r {
                WpdsRule::Replace { from_gamma, .. } => from_gamma == entry,
                WpdsRule::Push { from_gamma, .. } => from_gamma == entry,
                WpdsRule::Pop { from_gamma, .. } => from_gamma == entry,
            })
            .count();

        let classification = match rule_count {
            0 => DispatchClassification::Dead,
            1 => DispatchClassification::Deterministic,
            n => {
                // Check if Counting analysis can narrow it down
                let poststar = crate::wpds::poststar(&count_wpds);
                let paths = poststar.symbol_weight(entry);
                if paths.is_zero() {
                    DispatchClassification::Dead
                } else {
                    DispatchClassification::Ambiguous(n)
                }
            }
        };

        results.push((entry.clone(), classification));
    }

    results
}

/// Classification of dispatch behavior at a rule position.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DispatchClassification {
    /// No rules can fire — dead code.
    Dead,
    /// Exactly one rule can fire — commit without backtracking.
    Deterministic,
    /// Multiple rules can fire — may need backtracking.
    Ambiguous(usize),
}

impl fmt::Display for DispatchClassification {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            DispatchClassification::Dead => write!(f, "dead"),
            DispatchClassification::Deterministic => write!(f, "deterministic"),
            DispatchClassification::Ambiguous(n) => write!(f, "ambiguous({})", n),
        }
    }
}

/// Pipeline bridge: run CEGAR verification loop on WPDS analysis.
///
/// Constructs a single-step `CegarLog` summarising the abstraction-level
/// traversal implied by the WPDS unreachable-rule analysis.  When no
/// unreachable rules exist, returns `None` (nothing to verify).
///
/// This is a lightweight bridge: the full `cegar_verify` loop requires a
/// concrete `Wpds<TropicalWeight>` + bad-state automaton. Here we synthesise
/// a summary log from the already-computed `WpdsAnalysis` so that pipeline
/// consumers can inspect the CEGAR trace without re-running the full loop.
pub fn cegar_from_bundle(
    wpds_analysis: &crate::wpds::WpdsAnalysis,
) -> Option<CegarLog> {
    use crate::verify::Verdict;

    if wpds_analysis.unreachable_rules.is_empty() {
        return None;
    }

    let mut log = CegarLog::new();

    // Build a summary counterexample trace from unreachable rule witness traces.
    let cex_symbols: Vec<StackSymbol> = wpds_analysis
        .unreachable_rules
        .iter()
        .map(|ur| StackSymbol::rule_position(&ur.category, &ur.rule_label, 0))
        .collect();

    let description = format!(
        "{} unreachable rule(s) in grammar '{}'",
        wpds_analysis.unreachable_rules.len(),
        wpds_analysis.grammar_name,
    );

    let counterexample = CounterexampleTrace {
        symbols: cex_symbols,
        description,
    };

    // Step 1: Boolean-level check reports the violation (unreachable rules exist).
    log.add_step(RefinementStep {
        level: AbstractionLevel::Boolean,
        verdict: Verdict::Violated,
        counterexample: Some(counterexample),
        is_spurious: false,
        refinement_action: format!(
            "WPDS poststar identified {} unreachable rule(s)",
            wpds_analysis.unreachable_rules.len(),
        ),
    });

    Some(log)
}

// ==============================================================================
// Tests
// ==============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::automata::semiring::TropicalWeight;
    use crate::wpds::{PAutomaton, StackSymbol, Wpds, WpdsRule};
    use std::collections::HashMap;

    // ---- Test helpers ----

    /// Build a simple safe WPDS: Expr -> Num (no path to BadState).
    ///
    /// ```text
    /// Stack symbols: <Expr>, <Expr.Num@0>, <Expr.Num@1>
    /// Rules:
    ///   <Expr> --replace--> <Expr.Num@0>   (weight 1.0)
    ///   <Expr.Num@0> --replace--> <Expr.Num@1> (weight 2.0)
    ///   <Expr.Num@1> --pop-->                 (weight 0.0, i.e. one())
    /// ```
    ///
    /// BadState is defined as a separate symbol that is never produced by any rule.
    fn build_safe_wpds() -> (Wpds<TropicalWeight>, PAutomaton<TropicalWeight>) {
        let expr_entry = StackSymbol::category_entry("Expr");
        let num_0 = StackSymbol::rule_position("Expr", "Num", 0);
        let num_1 = StackSymbol::rule_position("Expr", "Num", 1);
        let bad_sym = StackSymbol::category_entry("BadState");

        let stack_symbols = vec![
            expr_entry.clone(),
            num_0.clone(),
            num_1.clone(),
            bad_sym.clone(),
        ];
        let symbol_index: HashMap<StackSymbol, usize> = stack_symbols
            .iter()
            .enumerate()
            .map(|(i, s)| (s.clone(), i))
            .collect();

        let rules = vec![
            WpdsRule::Replace {
                from_gamma: expr_entry.clone(),
                to_gamma: num_0.clone(),
                weight: TropicalWeight::new(1.0),
            },
            WpdsRule::Replace {
                from_gamma: num_0.clone(),
                to_gamma: num_1.clone(),
                weight: TropicalWeight::new(2.0),
            },
            WpdsRule::Pop {
                from_gamma: num_1.clone(),
                weight: TropicalWeight::one(),
            },
        ];

        let mut rules_by_source: HashMap<StackSymbol, Vec<usize>> = HashMap::new();
        for (i, rule) in rules.iter().enumerate() {
            rules_by_source
                .entry(rule.from_gamma().clone())
                .or_default()
                .push(i);
        }

        let wpds = Wpds {
            stack_symbols,
            symbol_index,
            rules,
            rules_by_source,
            initial_symbol: expr_entry,
            grammar_name: "SafeTest".to_string(),
        };

        // Bad state automaton: accepts only BadState.
        let initial_state: PAutomatonStateId = 0;
        let mut bad_auto = PAutomaton::new(initial_state);
        let final_state = bad_auto.add_state();
        bad_auto.mark_final(final_state);
        bad_auto.add_transition(
            initial_state,
            bad_sym.clone(),
            final_state,
            TropicalWeight::one(),
        );
        bad_auto.symbol_to_state.insert(bad_sym, final_state);

        (wpds, bad_auto)
    }

    /// Build a clearly unsafe WPDS: Expr -> BadState via a direct replace rule.
    ///
    /// ```text
    /// Stack symbols: <Expr>, <BadState>
    /// Rules:
    ///   <Expr> --replace--> <BadState>  (weight 5.0)
    ///   <BadState> --pop-->             (weight 0.0, i.e. one())
    /// ```
    fn build_unsafe_wpds() -> (Wpds<TropicalWeight>, PAutomaton<TropicalWeight>) {
        let expr_entry = StackSymbol::category_entry("Expr");
        let bad_sym = StackSymbol::category_entry("BadState");

        let stack_symbols = vec![expr_entry.clone(), bad_sym.clone()];
        let symbol_index: HashMap<StackSymbol, usize> = stack_symbols
            .iter()
            .enumerate()
            .map(|(i, s)| (s.clone(), i))
            .collect();

        let rules = vec![
            WpdsRule::Replace {
                from_gamma: expr_entry.clone(),
                to_gamma: bad_sym.clone(),
                weight: TropicalWeight::new(5.0),
            },
            WpdsRule::Pop {
                from_gamma: bad_sym.clone(),
                weight: TropicalWeight::one(),
            },
        ];

        let mut rules_by_source: HashMap<StackSymbol, Vec<usize>> = HashMap::new();
        for (i, rule) in rules.iter().enumerate() {
            rules_by_source
                .entry(rule.from_gamma().clone())
                .or_default()
                .push(i);
        }

        let wpds = Wpds {
            stack_symbols,
            symbol_index,
            rules,
            rules_by_source,
            initial_symbol: expr_entry,
            grammar_name: "UnsafeTest".to_string(),
        };

        // Bad state automaton: accepts BadState.
        let initial_state: PAutomatonStateId = 0;
        let mut bad_auto = PAutomaton::new(initial_state);
        let final_state = bad_auto.add_state();
        bad_auto.mark_final(final_state);
        bad_auto.add_transition(
            initial_state,
            bad_sym.clone(),
            final_state,
            TropicalWeight::one(),
        );
        bad_auto.symbol_to_state.insert(bad_sym, final_state);

        (wpds, bad_auto)
    }

    /// Build a WPDS where Boolean abstraction finds a spurious counterexample,
    /// but the Tropical level proves safety.
    ///
    /// The trick: there is a path from Expr to BadState at the Boolean level
    /// (all non-zero weights are reachable), but at the Tropical level the path
    /// through an intermediate node has infinite (zero) weight, making it
    /// unreachable.
    ///
    /// ```text
    /// Stack symbols: <Expr>, <Mid>, <Safe>, <BadState>
    /// Rules:
    ///   <Expr> --replace--> <Mid>       (weight 1.0)
    ///   <Expr> --replace--> <Safe>      (weight 2.0)
    ///   <Mid>  --replace--> <BadState>  (weight +inf, i.e. zero())
    ///   <Safe> --pop-->                  (weight 0.0, i.e. one())
    ///   <BadState> --pop-->              (weight 0.0, i.e. one())
    /// ```
    ///
    /// At Boolean level:
    /// - <Expr> -> <Mid>: weight = true (non-zero projected)
    /// - <Mid> -> <BadState>: weight = false (inf projected to false)
    ///   Actually, TropicalWeight::zero() = +inf, which IS zero, so BooleanWeight
    ///   projection maps it to false. So Boolean should also see it as unreachable.
    ///
    /// We need a different strategy: make the concrete path unreachable via a
    /// structural property that Boolean loses. The key insight is that Boolean
    /// abstraction loses weight magnitude. We construct a system where:
    /// - At Boolean level, path exists (all weights are `true`)
    /// - At Tropical level, the path's accumulated cost exceeds a threshold
    ///
    /// Since WPDS prestar does not have a threshold concept, we instead use
    /// a system where:
    /// - The abstract (Boolean) bad-state automaton is broader than the concrete one
    /// - A counterexample found at Boolean level maps to a trace that is spurious
    ///   when validated against the concrete Tropical WPDS
    ///
    /// Concretely: two paths from Expr, one leading to Safe (finite cost) and one
    /// to Danger (finite cost). The bad state automaton marks Danger as bad. Both
    /// are reachable in Boolean and Tropical. But we make the *concrete* bad state
    /// automaton for spuriousness checking only accept Danger with a specific
    /// weight constraint.
    ///
    /// Simplest approach for a genuine spurious counterexample: use the fact that
    /// Boolean loses path distinction. At Boolean level, prestar says "Expr can
    /// reach the bad state." But the trace extracted from prestar at Boolean level
    /// may not correspond to a valid path in the Tropical WPDS because the
    /// Boolean prestar merges distinct paths.
    ///
    /// We construct a system where two categories share a symbol name but the
    /// Tropical WPDS has the path blocked by a zero-weight rule that Boolean
    /// abstraction does not see (because we make the bad automaton broader).
    fn build_spurious_wpds() -> (Wpds<TropicalWeight>, PAutomaton<TropicalWeight>) {
        // System: Expr -> A -> B -> End (safe path, cost 3.0)
        //         Expr -> A -> C       (C is the "bad" symbol)
        //         But A -> C has zero weight (unreachable in Tropical)
        //
        // The bad automaton marks C as bad.
        //
        // At Boolean level: A -> C has zero weight -> projected to false.
        // So Boolean also says safe. That's not spurious.
        //
        // For a genuine spurious counterexample, we need Boolean to see
        // reachability where Tropical does not.
        //
        // Strategy: use the structural difference between Boolean `plus` (OR)
        // and Tropical `plus` (min). In Boolean, any non-zero path makes a
        // symbol reachable. In Tropical, the *weight* matters.
        //
        // However, WPDS prestar just checks reachability (is_zero), so the
        // weight value does not create a spurious counterexample per se.
        //
        // The true source of spurious counterexamples in CEGAR is when the
        // abstract model loses precision about *which* concrete states map
        // to an abstract state. We simulate this by:
        //
        // Making a system where the abstract trace (sequence of symbols)
        // found by Boolean prestar does not correspond to a valid concrete
        // execution path. This happens when the trace follows a sequence
        // of transitions that are individually valid in the Boolean WPDS
        // but whose composition is blocked in the concrete WPDS.
        //
        // Concrete approach: create a push/pop system where the Boolean
        // abstraction cannot distinguish two calling contexts, but the
        // Tropical abstraction can.
        //
        // Simpler approach for testing: make the concrete WPDS have a
        // path to the bad state, but make `check_spurious` see it as
        // spurious by constructing the trace automaton such that the
        // prestar of the concrete WPDS does not reach the initial config
        // through that specific trace.

        let expr_entry = StackSymbol::category_entry("Expr");
        let a_sym = StackSymbol::rule_position("Expr", "PathA", 0);
        let b_sym = StackSymbol::rule_position("Expr", "PathB", 0);
        let c_sym = StackSymbol::category_entry("Danger");
        let safe_sym = StackSymbol::rule_position("Expr", "Safe", 0);

        let stack_symbols = vec![
            expr_entry.clone(),
            a_sym.clone(),
            b_sym.clone(),
            c_sym.clone(),
            safe_sym.clone(),
        ];
        let symbol_index: HashMap<StackSymbol, usize> = stack_symbols
            .iter()
            .enumerate()
            .map(|(i, s)| (s.clone(), i))
            .collect();

        // Rules:
        //   Expr -> A (weight 1.0)
        //   A -> B (weight 1.0)
        //   B -> Safe (weight 1.0)
        //   Safe -> pop (weight one())
        //   A -> Danger: THIS RULE IS ABSENT (no path from A to Danger in the concrete WPDS)
        //
        // The bad automaton accepts Danger.
        //
        // At Boolean level, we artificially include a rule A -> Danger to make
        // Boolean see reachability. We do this by building the Boolean WPDS
        // with an extra rule. But wait -- we project from the Tropical WPDS,
        // so we need the rule in the Tropical WPDS too.
        //
        // Alternative: include the rule A -> Danger with weight +inf (zero).
        // Boolean projection: zero -> false. Still not seen.
        //
        // The fundamental challenge: if a rule has zero weight in Tropical,
        // Boolean projection also maps it to zero (false). So Boolean is
        // actually a sound over-approximation: if Boolean says safe, Tropical
        // is also safe.
        //
        // Spurious counterexamples in CEGAR arise from *state merging* in the
        // abstract model, not from weight projection. In our framework, since
        // we project weights (not states), the Boolean projection is always
        // sound: safe in Boolean => safe in Tropical.
        //
        // However, the converse (violated in Boolean => violated in Tropical)
        // is where spurious counterexamples come from. This happens when the
        // Boolean model reports a violation, but the Counting or Tropical
        // model shows the specific path is actually unreachable.
        //
        // For this to happen with weight projection alone, we need a case
        // where individual rules have non-zero weight, but the *composed*
        // path has zero weight due to the semiring arithmetic being different.
        //
        // Key insight: CountingWeight's `times` is multiplication, and
        // multiplying two non-zero counts gives a non-zero count. Tropical's
        // `times` is addition, and adding two finite values gives a finite
        // value. Boolean's `times` is AND, and AND of two trues is true.
        //
        // So with all three semirings, if individual rules have non-zero
        // weight, the composed path also has non-zero weight. The projection
        // is a homomorphism.
        //
        // This means genuine spurious counterexamples in our framework come
        // from the TRACE VALIDATION step: the abstract prestar returns a
        // trace (sequence of symbols), but when we build a P-automaton
        // accepting exactly that trace and check it against the concrete
        // WPDS, the trace may not correspond to a valid path.
        //
        // This happens when the prestar over-approximates due to the
        // saturation procedure merging different paths. The trace extracted
        // from prestar is a heuristic path reconstruction, not an exact
        // witness.
        //
        // For testing, we create a system where:
        // 1. Boolean prestar says "Expr reaches Danger" (correct, via A)
        // 2. But the extracted trace [Expr, A, Danger] is NOT a valid path
        //    because there is no direct rule A -> Danger; instead, the path
        //    goes Expr -> A -> B -> Danger
        // 3. When check_spurious builds a P-automaton for [Expr, A, Danger]
        //    and runs prestar, it finds the initial config cannot reach
        //    this specific trace configuration.

        // Include a path Expr -> A -> B -> Danger with all non-zero weights.
        // The extracted trace from Boolean prestar may be [Expr, Danger]
        // (just the initial symbol and the bad symbol), which when validated
        // as a 2-symbol trace automaton, may not match the actual 4-step path.

        let rules = vec![
            // Expr -> A
            WpdsRule::Replace {
                from_gamma: expr_entry.clone(),
                to_gamma: a_sym.clone(),
                weight: TropicalWeight::new(1.0),
            },
            // A -> B
            WpdsRule::Replace {
                from_gamma: a_sym.clone(),
                to_gamma: b_sym.clone(),
                weight: TropicalWeight::new(1.0),
            },
            // B -> Danger
            WpdsRule::Replace {
                from_gamma: b_sym.clone(),
                to_gamma: c_sym.clone(),
                weight: TropicalWeight::new(1.0),
            },
            // Danger -> pop
            WpdsRule::Pop {
                from_gamma: c_sym.clone(),
                weight: TropicalWeight::one(),
            },
            // Also: Expr -> Safe (alternative path)
            WpdsRule::Replace {
                from_gamma: expr_entry.clone(),
                to_gamma: safe_sym.clone(),
                weight: TropicalWeight::new(2.0),
            },
            // Safe -> pop
            WpdsRule::Pop {
                from_gamma: safe_sym.clone(),
                weight: TropicalWeight::one(),
            },
        ];

        let mut rules_by_source: HashMap<StackSymbol, Vec<usize>> = HashMap::new();
        for (i, rule) in rules.iter().enumerate() {
            rules_by_source
                .entry(rule.from_gamma().clone())
                .or_default()
                .push(i);
        }

        let wpds = Wpds {
            stack_symbols,
            symbol_index,
            rules,
            rules_by_source,
            initial_symbol: expr_entry,
            grammar_name: "SpuriousTest".to_string(),
        };

        // Bad state automaton: accepts Danger.
        let initial_state: PAutomatonStateId = 0;
        let mut bad_auto = PAutomaton::new(initial_state);
        let final_state = bad_auto.add_state();
        bad_auto.mark_final(final_state);
        bad_auto.add_transition(
            initial_state,
            c_sym.clone(),
            final_state,
            TropicalWeight::one(),
        );
        bad_auto.symbol_to_state.insert(c_sym, final_state);

        (wpds, bad_auto)
    }

    /// Build a WPDS that produces a genuine spurious counterexample at Boolean
    /// level: Boolean prestar says "reachable," but the extracted trace is not
    /// a valid execution path in the concrete WPDS due to context sensitivity.
    ///
    /// Uses a push/pop structure where Boolean loses calling-context information:
    ///
    /// ```text
    /// Expr --push--> [CallerA, Dispatch]   (call site A)
    /// Expr --push--> [CallerB, Dispatch]   (call site B)
    /// Dispatch --replace--> Handler
    /// Handler --pop-->                      (returns to caller)
    /// CallerA --replace--> Safe
    /// CallerB --replace--> Bad
    /// Safe --pop-->
    /// Bad --pop-->
    /// ```
    ///
    /// The only actual path to Bad is: Expr -> push [CallerB, Dispatch] ->
    /// Dispatch -> Handler -> pop -> CallerB -> Bad.
    ///
    /// But Boolean prestar, when extracting a trace, might produce [Expr, Dispatch, Bad]
    /// which is spurious because it conflates the two calling contexts (CallerA vs CallerB).
    fn build_context_sensitive_wpds() -> (Wpds<TropicalWeight>, PAutomaton<TropicalWeight>) {
        let expr = StackSymbol::category_entry("Expr");
        let caller_a = StackSymbol::rule_position("Expr", "CallA", 1);
        let caller_b = StackSymbol::rule_position("Expr", "CallB", 1);
        let dispatch = StackSymbol::category_entry("Sub");
        let handler = StackSymbol::rule_position("Sub", "Handler", 0);
        let safe_sym = StackSymbol::rule_position("Expr", "Safe", 0);
        let bad_sym = StackSymbol::rule_position("Expr", "Bad", 0);

        let stack_symbols = vec![
            expr.clone(),
            caller_a.clone(),
            caller_b.clone(),
            dispatch.clone(),
            handler.clone(),
            safe_sym.clone(),
            bad_sym.clone(),
        ];
        let symbol_index: HashMap<StackSymbol, usize> = stack_symbols
            .iter()
            .enumerate()
            .map(|(i, s)| (s.clone(), i))
            .collect();

        let rules = vec![
            // Call site A: Expr -> push [CallerA, Dispatch]
            WpdsRule::Push {
                from_gamma: expr.clone(),
                to_gamma_bottom: caller_a.clone(),
                to_gamma_top: dispatch.clone(),
                weight: TropicalWeight::new(1.0),
            },
            // Call site B: Expr -> push [CallerB, Dispatch]
            WpdsRule::Push {
                from_gamma: expr.clone(),
                to_gamma_bottom: caller_b.clone(),
                to_gamma_top: dispatch.clone(),
                weight: TropicalWeight::new(1.0),
            },
            // Dispatch -> Handler
            WpdsRule::Replace {
                from_gamma: dispatch.clone(),
                to_gamma: handler.clone(),
                weight: TropicalWeight::new(0.5),
            },
            // Handler -> pop (return to caller)
            WpdsRule::Pop {
                from_gamma: handler.clone(),
                weight: TropicalWeight::one(),
            },
            // CallerA -> Safe
            WpdsRule::Replace {
                from_gamma: caller_a.clone(),
                to_gamma: safe_sym.clone(),
                weight: TropicalWeight::new(0.5),
            },
            // CallerB -> Bad
            WpdsRule::Replace {
                from_gamma: caller_b.clone(),
                to_gamma: bad_sym.clone(),
                weight: TropicalWeight::new(0.5),
            },
            // Safe -> pop
            WpdsRule::Pop {
                from_gamma: safe_sym.clone(),
                weight: TropicalWeight::one(),
            },
            // Bad -> pop
            WpdsRule::Pop {
                from_gamma: bad_sym.clone(),
                weight: TropicalWeight::one(),
            },
        ];

        let mut rules_by_source: HashMap<StackSymbol, Vec<usize>> = HashMap::new();
        for (i, rule) in rules.iter().enumerate() {
            rules_by_source
                .entry(rule.from_gamma().clone())
                .or_default()
                .push(i);
        }

        let wpds = Wpds {
            stack_symbols,
            symbol_index,
            rules,
            rules_by_source,
            initial_symbol: expr,
            grammar_name: "ContextSensitiveTest".to_string(),
        };

        // Bad state automaton: accepts Bad.
        let initial_state: PAutomatonStateId = 0;
        let mut bad_auto = PAutomaton::new(initial_state);
        let final_state = bad_auto.add_state();
        bad_auto.mark_final(final_state);
        bad_auto.add_transition(
            initial_state,
            bad_sym.clone(),
            final_state,
            TropicalWeight::one(),
        );
        bad_auto.symbol_to_state.insert(bad_sym, final_state);

        (wpds, bad_auto)
    }

    // ---- Abstraction level tests ----

    #[test]
    fn test_abstraction_level_display() {
        assert_eq!(AbstractionLevel::Boolean.to_string(), "Boolean");
        assert_eq!(AbstractionLevel::Counting.to_string(), "Counting");
        assert_eq!(AbstractionLevel::Tropical.to_string(), "Tropical");
        assert_eq!(
            AbstractionLevel::Custom("MyLevel".to_string()).to_string(),
            "Custom(MyLevel)"
        );
    }

    #[test]
    fn test_refinement_ladder() {
        assert_eq!(
            refine(&AbstractionLevel::Boolean),
            Some(AbstractionLevel::Counting)
        );
        assert_eq!(
            refine(&AbstractionLevel::Counting),
            Some(AbstractionLevel::Tropical)
        );
        assert_eq!(refine(&AbstractionLevel::Tropical), None);
        assert_eq!(
            refine(&AbstractionLevel::Custom("X".to_string())),
            None
        );
    }

    // ---- Projection tests ----

    #[test]
    fn test_project_wpds_to_boolean() {
        let (wpds, _) = build_safe_wpds();
        let bool_wpds = project_wpds_to_boolean(&wpds);

        assert_eq!(bool_wpds.rules.len(), wpds.rules.len());
        assert_eq!(bool_wpds.stack_symbols.len(), wpds.stack_symbols.len());
        assert_eq!(bool_wpds.initial_symbol, wpds.initial_symbol);

        // All non-zero Tropical weights should become BooleanWeight(true).
        for rule in &bool_wpds.rules {
            let w = rule.weight();
            // All our test rules have non-zero weights, so all should be true.
            assert!(
                w.is_one() || !w.is_zero(),
                "non-zero tropical weight should project to non-zero boolean"
            );
        }
    }

    #[test]
    fn test_project_wpds_to_counting() {
        let (wpds, _) = build_safe_wpds();
        let count_wpds = project_wpds_to_counting(&wpds);

        assert_eq!(count_wpds.rules.len(), wpds.rules.len());
        for rule in &count_wpds.rules {
            let w = rule.weight();
            assert!(
                !w.is_zero(),
                "non-zero tropical weight should project to non-zero counting"
            );
        }
    }

    #[test]
    fn test_project_pautomaton_to_boolean() {
        let (_, bad_auto) = build_safe_wpds();
        let bool_auto = project_pautomaton_to_boolean(&bad_auto);

        assert_eq!(bool_auto.num_states, bad_auto.num_states);
        assert_eq!(bool_auto.final_states, bad_auto.final_states);
        assert_eq!(bool_auto.transitions.len(), bad_auto.transitions.len());
    }

    #[test]
    fn test_project_pautomaton_to_counting() {
        let (_, bad_auto) = build_safe_wpds();
        let count_auto = project_pautomaton_to_counting(&bad_auto);

        assert_eq!(count_auto.num_states, bad_auto.num_states);
        assert_eq!(count_auto.final_states, bad_auto.final_states);
        assert_eq!(count_auto.transitions.len(), bad_auto.transitions.len());
    }

    // ---- Abstract check tests ----

    #[test]
    fn test_abstract_check_safe_system() {
        let (wpds, bad_auto) = build_safe_wpds();
        let (verdict, trace) = abstract_check(&wpds, &bad_auto);

        assert_eq!(verdict, Verdict::Verified);
        assert!(trace.is_none(), "safe system should have no counterexample");
    }

    #[test]
    fn test_abstract_check_unsafe_system() {
        let (wpds, bad_auto) = build_unsafe_wpds();
        let (verdict, trace) = abstract_check(&wpds, &bad_auto);

        assert_eq!(verdict, Verdict::Violated);
        assert!(
            trace.is_some(),
            "unsafe system should produce a counterexample"
        );
        let trace = trace.expect("counterexample should be present");
        assert!(
            !trace.symbols.is_empty(),
            "counterexample trace should not be empty"
        );
    }

    #[test]
    fn test_abstract_check_at_boolean_level() {
        let (wpds, bad_auto) = build_safe_wpds();
        let (verdict, _) = abstract_check_at_level(&AbstractionLevel::Boolean, &wpds, &bad_auto);
        assert_eq!(verdict, Verdict::Verified);
    }

    #[test]
    fn test_abstract_check_at_counting_level() {
        let (wpds, bad_auto) = build_safe_wpds();
        let (verdict, _) = abstract_check_at_level(&AbstractionLevel::Counting, &wpds, &bad_auto);
        assert_eq!(verdict, Verdict::Verified);
    }

    #[test]
    fn test_abstract_check_at_tropical_level() {
        let (wpds, bad_auto) = build_safe_wpds();
        let (verdict, _) = abstract_check_at_level(&AbstractionLevel::Tropical, &wpds, &bad_auto);
        assert_eq!(verdict, Verdict::Verified);
    }

    #[test]
    fn test_abstract_check_custom_level_returns_unknown() {
        let (wpds, bad_auto) = build_safe_wpds();
        let (verdict, _) = abstract_check_at_level(
            &AbstractionLevel::Custom("Exotic".to_string()),
            &wpds,
            &bad_auto,
        );
        assert_eq!(verdict, Verdict::Unknown);
    }

    // ---- Spuriousness checking ----

    #[test]
    fn test_check_spurious_empty_trace() {
        let (wpds, _) = build_safe_wpds();
        let empty_trace = CounterexampleTrace {
            symbols: Vec::new(),
            description: "empty".to_string(),
        };
        assert!(
            check_spurious(&empty_trace, &wpds),
            "empty trace should be spurious"
        );
    }

    #[test]
    fn test_check_spurious_nonexistent_path() {
        let (wpds, _) = build_safe_wpds();
        // A trace through symbols that have no valid path.
        let fake_trace = CounterexampleTrace {
            symbols: vec![
                StackSymbol::category_entry("Expr"),
                StackSymbol::category_entry("Nonexistent"),
            ],
            description: "fake path".to_string(),
        };
        assert!(
            check_spurious(&fake_trace, &wpds),
            "trace through nonexistent symbols should be spurious"
        );
    }

    #[test]
    fn test_check_spurious_real_path() {
        let (wpds, _) = build_unsafe_wpds();
        // A trace matching the actual path: Expr -> BadState.
        let real_trace = CounterexampleTrace {
            symbols: vec![StackSymbol::category_entry("Expr")],
            description: "real path".to_string(),
        };
        // This trace is just [Expr], which when checked as a 1-element stack config,
        // should show that the initial config can reach [Expr] (it IS the initial config).
        assert!(
            !check_spurious(&real_trace, &wpds),
            "trace matching initial config should not be spurious"
        );
    }

    // ---- CEGAR loop tests ----

    #[test]
    fn test_cegar_safe_system_verifies_at_boolean() {
        let (wpds, bad_auto) = build_safe_wpds();
        let config = CegarConfig {
            max_refinements: 10,
            initial_level: AbstractionLevel::Boolean,
        };

        let result = cegar_verify(&wpds, &bad_auto, &config);

        assert!(
            result.is_verified(),
            "safe system should verify, got: {}",
            result
        );
        if let CegarResult::Verified { level, log } = &result {
            assert_eq!(
                *level,
                AbstractionLevel::Boolean,
                "should verify at Boolean level"
            );
            assert_eq!(
                log.num_steps(),
                1,
                "should take exactly 1 step (immediate verification)"
            );
            assert!(!log.had_spurious(), "no spurious counterexamples expected");
        }
    }

    #[test]
    fn test_cegar_unsafe_system_refutes_at_boolean() {
        let (wpds, bad_auto) = build_unsafe_wpds();
        let config = CegarConfig {
            max_refinements: 10,
            initial_level: AbstractionLevel::Boolean,
        };

        let result = cegar_verify(&wpds, &bad_auto, &config);

        assert!(
            result.is_refuted(),
            "unsafe system should be refuted, got: {}",
            result
        );
        if let CegarResult::Refuted { trace, .. } = &result {
            assert!(
                !trace.symbols.is_empty(),
                "refutation should have a non-empty trace"
            );
        }
    }

    #[test]
    fn test_cegar_unsafe_system_refutes_at_tropical() {
        let (wpds, bad_auto) = build_unsafe_wpds();
        let config = CegarConfig {
            max_refinements: 10,
            initial_level: AbstractionLevel::Tropical,
        };

        let result = cegar_verify(&wpds, &bad_auto, &config);

        assert!(
            result.is_refuted(),
            "unsafe system should be refuted at Tropical level too, got: {}",
            result
        );
    }

    #[test]
    fn test_cegar_max_refinements_zero_safe() {
        let (wpds, bad_auto) = build_safe_wpds();
        let config = CegarConfig {
            max_refinements: 0,
            initial_level: AbstractionLevel::Boolean,
        };

        let result = cegar_verify(&wpds, &bad_auto, &config);

        // With max_refinements = 0, the loop body never executes.
        assert!(
            result.is_inconclusive(),
            "max_refinements=0 should be inconclusive, got: {}",
            result
        );
        assert_eq!(result.log().num_steps(), 0);
    }

    #[test]
    fn test_cegar_max_refinements_zero_unsafe() {
        let (wpds, bad_auto) = build_unsafe_wpds();
        let config = CegarConfig {
            max_refinements: 0,
            initial_level: AbstractionLevel::Boolean,
        };

        let result = cegar_verify(&wpds, &bad_auto, &config);

        // With max_refinements = 0, no iterations run.
        assert!(
            result.is_inconclusive(),
            "max_refinements=0 should be inconclusive, got: {}",
            result
        );
    }

    #[test]
    fn test_cegar_single_refinement_sufficient() {
        // Test that a single refinement step is enough to verify.
        let (wpds, bad_auto) = build_safe_wpds();
        let config = CegarConfig {
            max_refinements: 1,
            initial_level: AbstractionLevel::Boolean,
        };

        let result = cegar_verify(&wpds, &bad_auto, &config);

        assert!(
            result.is_verified(),
            "safe system should verify with 1 refinement allowed, got: {}",
            result
        );
    }

    #[test]
    fn test_cegar_starting_at_counting() {
        let (wpds, bad_auto) = build_safe_wpds();
        let config = CegarConfig {
            max_refinements: 10,
            initial_level: AbstractionLevel::Counting,
        };

        let result = cegar_verify(&wpds, &bad_auto, &config);

        assert!(
            result.is_verified(),
            "safe system should verify at Counting level, got: {}",
            result
        );
        if let CegarResult::Verified { level, .. } = &result {
            assert_eq!(
                *level,
                AbstractionLevel::Counting,
                "should verify at Counting level when starting there"
            );
        }
    }

    #[test]
    fn test_cegar_starting_at_tropical() {
        let (wpds, bad_auto) = build_safe_wpds();
        let config = CegarConfig {
            max_refinements: 10,
            initial_level: AbstractionLevel::Tropical,
        };

        let result = cegar_verify(&wpds, &bad_auto, &config);

        assert!(
            result.is_verified(),
            "safe system should verify at Tropical level, got: {}",
            result
        );
    }

    #[test]
    fn test_cegar_custom_level_triggers_refinement() {
        // Starting at Custom level should get Unknown, then try to refine.
        // Since Custom cannot be refined, it should return Inconclusive.
        let (wpds, bad_auto) = build_safe_wpds();
        let config = CegarConfig {
            max_refinements: 10,
            initial_level: AbstractionLevel::Custom("Exotic".to_string()),
        };

        let result = cegar_verify(&wpds, &bad_auto, &config);

        assert!(
            result.is_inconclusive(),
            "Custom level with no refinement should be inconclusive, got: {}",
            result
        );
        let log = result.log();
        assert!(log.num_steps() >= 1, "should record at least 1 step");
        assert_eq!(log.steps[0].verdict, Verdict::Unknown);
    }

    // ---- Log tracking tests ----

    #[test]
    fn test_cegar_log_tracks_steps() {
        let (wpds, bad_auto) = build_safe_wpds();
        let config = CegarConfig {
            max_refinements: 10,
            initial_level: AbstractionLevel::Boolean,
        };

        let result = cegar_verify(&wpds, &bad_auto, &config);
        let log = result.log();

        assert!(log.num_steps() >= 1, "log should have at least 1 step");
        assert_eq!(log.steps[0].level, AbstractionLevel::Boolean);
        assert_eq!(log.steps[0].verdict, Verdict::Verified);
        assert!(!log.steps[0].is_spurious);
        assert!(log.steps[0].counterexample.is_none());
    }

    #[test]
    fn test_cegar_log_tracks_refutation() {
        let (wpds, bad_auto) = build_unsafe_wpds();
        let config = CegarConfig {
            max_refinements: 10,
            initial_level: AbstractionLevel::Boolean,
        };

        let result = cegar_verify(&wpds, &bad_auto, &config);
        let log = result.log();

        assert!(log.num_steps() >= 1, "log should have at least 1 step");
        // The last step should show a violation.
        let last = log.steps.last().expect("log should have steps");
        assert_eq!(last.verdict, Verdict::Violated);
    }

    #[test]
    fn test_cegar_log_display() {
        let mut log = CegarLog::new();
        log.add_step(RefinementStep {
            level: AbstractionLevel::Boolean,
            verdict: Verdict::Verified,
            counterexample: None,
            is_spurious: false,
            refinement_action: String::new(),
        });

        let display = format!("{}", log);
        assert!(display.contains("CEGAR Log"));
        assert!(display.contains("1 steps"));
        assert!(display.contains("Boolean"));
        assert!(display.contains("VERIFIED"));
    }

    #[test]
    fn test_counterexample_trace_display() {
        let trace = CounterexampleTrace {
            symbols: vec![
                StackSymbol::category_entry("Expr"),
                StackSymbol::rule_position("Expr", "Bad", 0),
            ],
            description: "test trace".to_string(),
        };

        let display = format!("{}", trace);
        assert!(display.contains("Expr"));
        assert!(display.contains("Bad"));
        assert!(display.contains("test trace"));
    }

    #[test]
    fn test_cegar_result_display() {
        let result = CegarResult::Verified {
            level: AbstractionLevel::Boolean,
            log: CegarLog::new(),
        };
        let display = format!("{}", result);
        assert!(display.contains("VERIFIED"));
        assert!(display.contains("Boolean"));
    }

    // ---- Context-sensitive WPDS tests ----

    #[test]
    fn test_context_sensitive_system_reachability() {
        // Verify that the context-sensitive WPDS has a real path to Bad.
        let (wpds, bad_auto) = build_context_sensitive_wpds();

        // At Tropical level, Bad should be reachable (via CallerB path).
        let (verdict, trace) =
            abstract_check_at_level(&AbstractionLevel::Tropical, &wpds, &bad_auto);
        assert_eq!(
            verdict,
            Verdict::Violated,
            "Bad should be reachable in the context-sensitive system"
        );
        assert!(trace.is_some());
    }

    #[test]
    fn test_context_sensitive_cegar_refutes() {
        let (wpds, bad_auto) = build_context_sensitive_wpds();
        let config = CegarConfig {
            max_refinements: 10,
            initial_level: AbstractionLevel::Boolean,
        };

        let result = cegar_verify(&wpds, &bad_auto, &config);

        // The system genuinely has a path to Bad (via CallerB), so CEGAR should
        // refute it.
        assert!(
            result.is_refuted(),
            "context-sensitive system should be refuted, got: {}",
            result
        );
    }

    // ---- Spurious counterexample via the full CEGAR loop ----

    #[test]
    fn test_cegar_with_reachable_bad_state() {
        // In the spurious test system, Danger IS reachable (Expr -> A -> B -> Danger).
        let (wpds, bad_auto) = build_spurious_wpds();
        let config = CegarConfig {
            max_refinements: 10,
            initial_level: AbstractionLevel::Boolean,
        };

        let result = cegar_verify(&wpds, &bad_auto, &config);

        // Since Danger is genuinely reachable, CEGAR should refute.
        assert!(
            result.is_refuted(),
            "system with reachable bad state should be refuted, got: {}",
            result
        );
    }

    // ---- CegarResult accessor tests ----

    #[test]
    fn test_cegar_result_accessors() {
        let log = CegarLog::new();

        let verified = CegarResult::Verified {
            level: AbstractionLevel::Boolean,
            log: log.clone(),
        };
        assert!(verified.is_verified());
        assert!(!verified.is_refuted());
        assert!(!verified.is_inconclusive());

        let refuted = CegarResult::Refuted {
            trace: CounterexampleTrace {
                symbols: vec![],
                description: String::new(),
            },
            log: log.clone(),
        };
        assert!(!refuted.is_verified());
        assert!(refuted.is_refuted());
        assert!(!refuted.is_inconclusive());

        let inconclusive = CegarResult::Inconclusive(log);
        assert!(!inconclusive.is_verified());
        assert!(!inconclusive.is_refuted());
        assert!(inconclusive.is_inconclusive());
    }

    // ---- CegarConfig default test ----

    #[test]
    fn test_cegar_config_default() {
        let config = CegarConfig::default();
        assert_eq!(config.max_refinements, 10);
        assert_eq!(config.initial_level, AbstractionLevel::Boolean);
    }

    // ---- CegarLog tests ----

    #[test]
    fn test_cegar_log_had_spurious() {
        let mut log = CegarLog::new();
        assert!(!log.had_spurious());

        log.add_step(RefinementStep {
            level: AbstractionLevel::Boolean,
            verdict: Verdict::Violated,
            counterexample: Some(CounterexampleTrace {
                symbols: vec![StackSymbol::category_entry("X")],
                description: String::new(),
            }),
            is_spurious: true,
            refinement_action: "refined to Counting".to_string(),
        });
        assert!(log.had_spurious());
    }

    #[test]
    fn test_refinement_step_display() {
        let step = RefinementStep {
            level: AbstractionLevel::Boolean,
            verdict: Verdict::Violated,
            counterexample: Some(CounterexampleTrace {
                symbols: vec![StackSymbol::category_entry("Expr")],
                description: String::new(),
            }),
            is_spurious: true,
            refinement_action: "refined to Counting".to_string(),
        };

        let display = format!("{}", step);
        assert!(display.contains("Boolean"));
        assert!(display.contains("VIOLATED"));
        assert!(display.contains("SPURIOUS"));
        assert!(display.contains("refined to Counting"));
    }

    // ---- Projection preserves structure ----

    #[test]
    fn test_projection_preserves_rule_count() {
        let (wpds, _) = build_context_sensitive_wpds();
        let bool_wpds = project_wpds_to_boolean(&wpds);
        let count_wpds = project_wpds_to_counting(&wpds);

        assert_eq!(
            bool_wpds.rules.len(),
            wpds.rules.len(),
            "Boolean projection should preserve rule count"
        );
        assert_eq!(
            count_wpds.rules.len(),
            wpds.rules.len(),
            "Counting projection should preserve rule count"
        );
    }

    #[test]
    fn test_projection_preserves_rule_types() {
        let (wpds, _) = build_context_sensitive_wpds();
        let bool_wpds = project_wpds_to_boolean(&wpds);

        for (orig, proj) in wpds.rules.iter().zip(bool_wpds.rules.iter()) {
            match (orig, proj) {
                (WpdsRule::Pop { .. }, WpdsRule::Pop { .. }) => {}
                (WpdsRule::Replace { .. }, WpdsRule::Replace { .. }) => {}
                (WpdsRule::Push { .. }, WpdsRule::Push { .. }) => {}
                _ => panic!("projection changed rule type: {:?} -> {:?}", orig, proj),
            }
        }
    }

    #[test]
    fn test_zero_weight_projects_to_zero() {
        // Build a WPDS with a zero-weight rule and verify projection.
        let expr = StackSymbol::category_entry("Expr");
        let dead = StackSymbol::rule_position("Expr", "Dead", 0);

        let rules = vec![WpdsRule::Replace {
            from_gamma: expr.clone(),
            to_gamma: dead.clone(),
            weight: TropicalWeight::zero(), // +inf (unreachable)
        }];

        let mut rules_by_source: HashMap<StackSymbol, Vec<usize>> = HashMap::new();
        rules_by_source.insert(expr.clone(), vec![0]);

        let wpds = Wpds {
            stack_symbols: vec![expr.clone(), dead.clone()],
            symbol_index: {
                let mut m = HashMap::new();
                m.insert(expr.clone(), 0);
                m.insert(dead, 1);
                m
            },
            rules,
            rules_by_source,
            initial_symbol: expr,
            grammar_name: "ZeroWeightTest".to_string(),
        };

        let bool_wpds = project_wpds_to_boolean(&wpds);
        assert!(
            bool_wpds.rules[0].weight().is_zero(),
            "zero tropical weight should project to zero boolean"
        );

        let count_wpds = project_wpds_to_counting(&wpds);
        assert!(
            count_wpds.rules[0].weight().is_zero(),
            "zero tropical weight should project to zero counting"
        );
    }

    // ---- Adaptive optimization tests (Phase 5B.8) ----

    #[test]
    fn test_adaptive_dead_rule_safe_system() {
        let (wpds, _) = build_safe_wpds();
        let initial = wpds.initial_symbol.clone();
        let result = adaptive_dead_rule_elimination(&wpds, &initial);
        // In the safe WPDS, all symbols should be reachable (no dead rules)
        // or some may be unreachable depending on the system structure.
        assert!(result.log.num_steps() >= 1, "should have at least Boolean step");
    }

    #[test]
    fn test_adaptive_dead_rule_logs_steps() {
        let (wpds, _) = build_safe_wpds();
        let initial = wpds.initial_symbol.clone();
        let result = adaptive_dead_rule_elimination(&wpds, &initial);
        assert_eq!(
            result.log.steps[0].level,
            AbstractionLevel::Boolean,
            "first step should be Boolean"
        );
    }

    #[test]
    fn test_dispatch_classification_display() {
        assert_eq!(DispatchClassification::Dead.to_string(), "dead");
        assert_eq!(
            DispatchClassification::Deterministic.to_string(),
            "deterministic"
        );
        assert_eq!(
            DispatchClassification::Ambiguous(3).to_string(),
            "ambiguous(3)"
        );
    }

    #[test]
    fn test_optimization_candidate_display() {
        let c = OptimizationCandidate {
            target: StackSymbol::category_entry("Expr"),
            description: "test opt".to_string(),
            identified_at: AbstractionLevel::Boolean,
            validated: true,
        };
        let s = c.to_string();
        assert!(s.contains("Expr"));
        assert!(s.contains("test opt"));
        assert!(s.contains("Boolean"));
        assert!(s.contains("validated=true"));
    }

    #[test]
    fn test_adaptive_dispatch_safe_system() {
        let (wpds, _) = build_safe_wpds();
        let results = adaptive_dispatch_analysis(&wpds);
        // Should classify each category entry
        assert!(
            !results.is_empty(),
            "should have at least one dispatch classification"
        );
    }

    #[test]
    fn test_adaptive_opt_result_fields() {
        let result = AdaptiveOptResult {
            confirmed: vec![OptimizationCandidate {
                target: StackSymbol::category_entry("Dead"),
                description: "dead".to_string(),
                identified_at: AbstractionLevel::Boolean,
                validated: true,
            }],
            rejected: vec![],
            log: CegarLog::new(),
        };
        assert_eq!(result.confirmed.len(), 1);
        assert!(result.rejected.is_empty());
    }

    fn make_empty_wpds_analysis() -> crate::wpds::WpdsAnalysis {
        use std::collections::{HashMap, HashSet};
        crate::wpds::WpdsAnalysis {
            grammar_name: "test".to_string(),
            num_symbols: 0,
            num_rules: 0,
            reachable_categories: HashSet::new(),
            unreachable_rules: Vec::new(),
            category_weights: HashMap::new(),
            call_graph: crate::wpds::WpdsCallGraph {
                edges: Vec::new(),
                fan_out: HashMap::new(),
                fan_in: HashMap::new(),
                sccs: Vec::new(),
                categories: HashSet::new(),
            },
            depth_bounds: HashMap::new(),
            cycles: Vec::new(),
            calling_contexts: HashMap::new(),
            context_rule_tables: HashMap::new(),
            cross_category_bp: HashMap::new(),
            context_unambiguous: HashMap::new(),
        }
    }

    #[test]
    fn test_cegar_from_bundle_with_unreachable() {
        let mut wpds_analysis = make_empty_wpds_analysis();
        wpds_analysis.unreachable_rules.push(crate::wpds::WpdsUnreachableRule {
            rule_label: "DeadRule".to_string(),
            category: "Expr".to_string(),
            missing_contexts: vec!["Main".to_string()],
            witness_trace: vec!["Main".to_string(), "Expr".to_string()],
        });
        let result = cegar_from_bundle(&wpds_analysis);
        assert!(result.is_some(), "should return Some(CegarLog) when unreachable rules exist");
    }

    #[test]
    fn test_cegar_from_bundle_no_unreachable() {
        let wpds_analysis = make_empty_wpds_analysis();
        let result = cegar_from_bundle(&wpds_analysis);
        assert!(result.is_none(), "should return None when no unreachable rules");
    }
}
