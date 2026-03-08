//! Weighted Pushdown System (WPDS) and Simple Reset WPDA.
//!
//! Provides compile-time pushdown analysis for PraTTaIL grammars that goes beyond
//! the finite-state `PredictionWfst`. The WPDS encodes the full inter-category
//! call/return structure, enabling:
//!
//! - **Stack-aware dead-rule detection** (rules unreachable in valid stack contexts)
//! - **Exact ambiguity quantification** via stringsum over `CountingWeight`
//! - **Witness traces** explaining why a rule is dead (which calling contexts are missing)
//!
//! ## Theoretical Foundations
//!
//! Three complementary formalisms:
//!
//! 1. **Reps, Lal & Kidd (2007)** — WPDS poststar/prestar saturation for grammar-wide
//!    reachability with call/return matching. Weight domains as abstract transformers.
//! 2. **Droste, Dziadek & Kuich (2019)** — Simple reset WPDA normal form. Three stack
//!    ops (push/pop/noop), no ε-transitions, canonical `X = M₀X + Σ M₁X M₂X + E`.
//! 3. **Butoi et al. (2022)** — Direct WPDA stringsum algorithms avoiding CFG conversion.
//!    O(n³|Q|³|Γ|³) per input.
//!
//! ## Architecture
//!
//! ```text
//! LanguageSpec ──→ build_wpds() ──→ Wpds<W>
//!                                      │
//!                 ┌────────────────────┤
//!                 │                    │
//!                 ▼                    ▼
//!          poststar(BooleanWeight)   stringsum(CountingWeight)
//!          → stack-aware reachability → exact ambiguity counts
//!                 │                    │
//!                 ▼                    ▼
//!          lint.rs (Tier 5)       cost_benefit.rs (A5 refinement)
//! ```
//!
//! ## PraTTaIL Mapping
//!
//! | PDA Component | PraTTaIL Equivalent |
//! |---|---|
//! | Control locations P | `{p}` (single, "context-free process") |
//! | Stack alphabet Γ | `(category, rule_label, position)` triples |
//! | PDS rules Δ | Intraprocedural (replace), cross-category calls (push), returns (pop) |
//! | Weight function f | Semiring weight from `PredictionWfst` |

use std::collections::{HashMap, HashSet, VecDeque};
use std::fmt;

use crate::automata::semiring::{BooleanWeight, Semiring, TropicalWeight};
use crate::wfst::PredictionWfst;
use crate::{LanguageSpec, SyntaxItemSpec};

// ══════════════════════════════════════════════════════════════════════════════
// Core types
// ══════════════════════════════════════════════════════════════════════════════

/// A stack symbol in the WPDS.
///
/// Represents a position within a grammar category's parse, identified by
/// `(category, rule_label, position)` — the ICFG node.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct StackSymbol {
    /// Grammar category (e.g., "Expr", "Type").
    pub category: String,
    /// Rule label within the category (e.g., "Add", "If"). Empty for category entry.
    pub rule_label: String,
    /// Position within the rule's syntax items (0 = entry).
    pub position: u32,
}

impl StackSymbol {
    /// Create a category entry point stack symbol (position 0, empty rule).
    pub fn category_entry(category: &str) -> Self {
        StackSymbol {
            category: category.to_string(),
            rule_label: String::new(),
            position: 0,
        }
    }

    /// Create a rule-specific stack symbol at a given position.
    pub fn rule_position(category: &str, rule_label: &str, position: u32) -> Self {
        StackSymbol {
            category: category.to_string(),
            rule_label: rule_label.to_string(),
            position,
        }
    }
}

impl fmt::Display for StackSymbol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.rule_label.is_empty() {
            write!(f, "⟨{}⟩", self.category)
        } else {
            write!(f, "⟨{}.{}@{}⟩", self.category, self.rule_label, self.position)
        }
    }
}

/// A PDS rule type, following Reps et al. (2007) Definition 1.
///
/// Rules have the form `⟨p, γ⟩ ↪ ⟨p', u⟩` where `|u| ∈ {0, 1, 2}`.
#[derive(Debug, Clone)]
pub enum WpdsRule<W: Semiring> {
    /// Pop rule: `⟨p, γ⟩ ↪ ⟨p', ε⟩` — removes top of stack (return).
    Pop {
        /// Stack symbol consumed.
        from_gamma: StackSymbol,
        /// Rule weight.
        weight: W,
    },
    /// Replace rule: `⟨p, γ⟩ ↪ ⟨p', γ'⟩` — replaces top of stack (intraprocedural).
    Replace {
        /// Stack symbol consumed.
        from_gamma: StackSymbol,
        /// Stack symbol produced.
        to_gamma: StackSymbol,
        /// Rule weight.
        weight: W,
    },
    /// Push rule: `⟨p, γ⟩ ↪ ⟨p', γ' γ''⟩` — pushes onto stack (cross-category call).
    Push {
        /// Stack symbol consumed.
        from_gamma: StackSymbol,
        /// Bottom of the two symbols pushed (continuation after return).
        to_gamma_bottom: StackSymbol,
        /// Top of the two symbols pushed (callee entry).
        to_gamma_top: StackSymbol,
        /// Rule weight.
        weight: W,
    },
}

impl<W: Semiring + fmt::Display> fmt::Display for WpdsRule<W> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            WpdsRule::Pop { from_gamma, weight } => {
                write!(f, "⟨p, {}⟩ ↪ ⟨p', ε⟩  [w={}]", from_gamma, weight)
            }
            WpdsRule::Replace { from_gamma, to_gamma, weight } => {
                write!(f, "⟨p, {}⟩ ↪ ⟨p', {}⟩  [w={}]", from_gamma, to_gamma, weight)
            }
            WpdsRule::Push { from_gamma, to_gamma_bottom, to_gamma_top, weight } => {
                write!(
                    f,
                    "⟨p, {}⟩ ↪ ⟨p', {} {}⟩  [w={}]",
                    from_gamma, to_gamma_bottom, to_gamma_top, weight
                )
            }
        }
    }
}

impl<W: Semiring> WpdsRule<W> {
    /// The source stack symbol for this rule.
    pub fn from_gamma(&self) -> &StackSymbol {
        match self {
            WpdsRule::Pop { from_gamma, .. }
            | WpdsRule::Replace { from_gamma, .. }
            | WpdsRule::Push { from_gamma, .. } => from_gamma,
        }
    }

    /// The weight of this rule.
    pub fn weight(&self) -> &W {
        match self {
            WpdsRule::Pop { weight, .. }
            | WpdsRule::Replace { weight, .. }
            | WpdsRule::Push { weight, .. } => weight,
        }
    }
}

/// A Weighted Pushdown System (WPDS).
///
/// W = (P, S, f) where:
/// - P = (P, Γ, Δ) is a PDS with single control location `p`
/// - S is a bounded idempotent semiring (weight domain)
/// - f: Δ → S assigns weights to PDS rules
///
/// For PraTTaIL grammars, we use the "context-free process" encoding
/// (single control location `p`) per Reps et al. Section 2.
#[derive(Debug, Clone)]
pub struct Wpds<W: Semiring> {
    /// Stack alphabet Γ — all stack symbols appearing in rules.
    pub stack_symbols: Vec<StackSymbol>,
    /// Index from stack symbol to its position in `stack_symbols`.
    pub symbol_index: HashMap<StackSymbol, usize>,
    /// PDS rules Δ, indexed by source stack symbol.
    pub rules: Vec<WpdsRule<W>>,
    /// Rules indexed by source stack symbol (for efficient lookup).
    pub rules_by_source: HashMap<StackSymbol, Vec<usize>>,
    /// Initial stack symbol (primary category entry).
    pub initial_symbol: StackSymbol,
    /// Grammar name (for diagnostics).
    pub grammar_name: String,
}

impl<W: Semiring> Wpds<W> {
    /// Number of stack symbols in the WPDS.
    pub fn num_symbols(&self) -> usize {
        self.stack_symbols.len()
    }

    /// Number of PDS rules.
    pub fn num_rules(&self) -> usize {
        self.rules.len()
    }

    /// Register a stack symbol if not already present.
    fn ensure_symbol(&mut self, sym: StackSymbol) -> usize {
        if let Some(&idx) = self.symbol_index.get(&sym) {
            idx
        } else {
            let idx = self.stack_symbols.len();
            self.symbol_index.insert(sym.clone(), idx);
            self.stack_symbols.push(sym);
            idx
        }
    }

    /// Add a PDS rule.
    fn add_rule(&mut self, rule: WpdsRule<W>) {
        let source = rule.from_gamma().clone();
        let idx = self.rules.len();
        self.rules.push(rule);
        self.rules_by_source.entry(source).or_default().push(idx);
    }

    /// Get all rules with a given source stack symbol.
    pub fn rules_for(&self, gamma: &StackSymbol) -> &[usize] {
        self.rules_by_source
            .get(gamma)
            .map(|v| v.as_slice())
            .unwrap_or(&[])
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// P-automaton (for poststar/prestar results)
// ══════════════════════════════════════════════════════════════════════════════

/// State identifier in a P-automaton.
pub type PAutomatonStateId = u32;

/// A transition in a P-automaton: `(source, stack_symbol, target, weight)`.
#[derive(Debug, Clone)]
pub struct PAutomatonTransition<W: Semiring> {
    pub from: PAutomatonStateId,
    pub symbol: StackSymbol,
    pub to: PAutomatonStateId,
    pub weight: W,
}

/// A P-automaton encoding a set of configurations with weights.
///
/// Per Reps et al. (2007) Definition 3: accepts configuration `⟨p, u⟩` iff
/// there is a path from state `p` reading stack word `u` to a final state,
/// with weight equal to the path's weight product.
#[derive(Debug, Clone)]
pub struct PAutomaton<W: Semiring> {
    /// Number of states.
    pub num_states: u32,
    /// Initial state (corresponding to control location `p`).
    pub initial_state: PAutomatonStateId,
    /// Final (accepting) states.
    pub final_states: HashSet<PAutomatonStateId>,
    /// Transitions indexed by source state.
    pub transitions: Vec<PAutomatonTransition<W>>,
    /// Transitions indexed by source state for efficient lookup.
    pub transitions_by_source: HashMap<PAutomatonStateId, Vec<usize>>,
    /// Map from stack symbols to the state they reach from initial.
    pub symbol_to_state: HashMap<StackSymbol, PAutomatonStateId>,
}

impl<W: Semiring> PAutomaton<W> {
    /// Create a new P-automaton with the given initial state.
    pub fn new(initial_state: PAutomatonStateId) -> Self {
        PAutomaton {
            num_states: initial_state + 1,
            initial_state,
            final_states: HashSet::new(),
            transitions: Vec::new(),
            transitions_by_source: HashMap::new(),
            symbol_to_state: HashMap::new(),
        }
    }

    /// Allocate a fresh state.
    pub fn add_state(&mut self) -> PAutomatonStateId {
        let id = self.num_states;
        self.num_states += 1;
        id
    }

    /// Add a transition.
    pub fn add_transition(&mut self, from: PAutomatonStateId, symbol: StackSymbol, to: PAutomatonStateId, weight: W) {
        let idx = self.transitions.len();
        self.transitions.push(PAutomatonTransition { from, symbol, to, weight });
        self.transitions_by_source.entry(from).or_default().push(idx);
    }

    /// Mark a state as final.
    pub fn mark_final(&mut self, state: PAutomatonStateId) {
        self.final_states.insert(state);
    }

    /// Check if a stack symbol is accepted as a single-element configuration.
    ///
    /// True iff there exists a transition `(initial, symbol, q)` where `q` is final.
    /// This checks whether the configuration `⟨p, symbol⟩` (one-element stack) is
    /// in the accepted set.
    pub fn is_symbol_accepted(&self, symbol: &StackSymbol) -> bool {
        if let Some(trans_indices) = self.transitions_by_source.get(&self.initial_state) {
            for &idx in trans_indices {
                let t = &self.transitions[idx];
                if t.symbol == *symbol && self.final_states.contains(&t.to) {
                    return true;
                }
            }
        }
        false
    }

    /// Check if a stack symbol is reachable (appears in ANY configuration).
    ///
    /// True iff there exists any transition `(initial, symbol, q)` for any state `q`.
    /// This is weaker than `is_symbol_accepted` — the symbol may appear only as part
    /// of multi-element stacks (e.g., a called category in a cross-category push).
    pub fn is_symbol_reachable(&self, symbol: &StackSymbol) -> bool {
        if let Some(trans_indices) = self.transitions_by_source.get(&self.initial_state) {
            for &idx in trans_indices {
                let t = &self.transitions[idx];
                if t.symbol == *symbol {
                    return true;
                }
            }
        }
        false
    }

    /// Get the weight for a stack symbol across all reachable configurations.
    ///
    /// Returns the semiring sum of weights on all transitions `(initial, symbol, q)`
    /// for any state `q` (not just final states). For dead-rule detection, a zero
    /// weight means the symbol never appears in any reachable configuration.
    pub fn symbol_weight(&self, symbol: &StackSymbol) -> W {
        let mut total = W::zero();
        if let Some(trans_indices) = self.transitions_by_source.get(&self.initial_state) {
            for &idx in trans_indices {
                let t = &self.transitions[idx];
                if t.symbol == *symbol {
                    total = total.plus(&t.weight);
                }
            }
        }
        total
    }

    /// Get all reachable stack symbols with their weights.
    pub fn reachable_symbols(&self) -> Vec<(StackSymbol, W)> {
        let mut result = Vec::new();
        if let Some(trans_indices) = self.transitions_by_source.get(&self.initial_state) {
            for &idx in trans_indices {
                let t = &self.transitions[idx];
                result.push((t.symbol.clone(), t.weight));
            }
        }
        result
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Grammar → WPDS construction
// ══════════════════════════════════════════════════════════════════════════════

/// Build a WPDS from a `LanguageSpec` and prediction WFST data.
///
/// The construction maps PraTTaIL's grammar structure to PDS rules:
///
/// - **Category entry** (`⟨Cat⟩`): Each category has an entry stack symbol
/// - **Intraprocedural** (Replace): Within a rule, consuming terminals
/// - **Cross-category call** (Push): When a rule references another category's nonterminal
/// - **Return** (Pop): When a rule completes, returning to the caller
///
/// Weights come from the `PredictionWfst` for each category.
pub fn build_wpds<W: Semiring>(
    spec: &LanguageSpec,
    prediction_wfsts: &HashMap<String, PredictionWfst>,
    weight_fn: impl Fn(f64) -> W,
) -> Wpds<W> {
    let primary_cat = spec
        .types
        .iter()
        .find(|t| t.is_primary)
        .map(|t| t.name.as_str())
        .unwrap_or_else(|| spec.types.first().map(|t| t.name.as_str()).unwrap_or(""));

    let initial_symbol = StackSymbol::category_entry(primary_cat);

    let mut wpds = Wpds {
        stack_symbols: Vec::new(),
        symbol_index: HashMap::new(),
        rules: Vec::new(),
        rules_by_source: HashMap::new(),
        initial_symbol: initial_symbol.clone(),
        grammar_name: spec.name.clone(),
    };

    // Register initial symbol
    wpds.ensure_symbol(initial_symbol);

    // Group rules by category
    let mut rules_by_category: HashMap<&str, Vec<&crate::RuleSpec>> = HashMap::new();
    for rule in &spec.rules {
        rules_by_category
            .entry(&rule.category)
            .or_default()
            .push(rule);
    }

    // For each category and its rules, build PDS rules
    for cat_spec in &spec.types {
        let cat = &cat_spec.name;
        let cat_entry = StackSymbol::category_entry(cat);
        wpds.ensure_symbol(cat_entry.clone());

        let empty_rules = Vec::new();
        let cat_rules = rules_by_category.get(cat.as_str()).unwrap_or(&empty_rules);

        // Look up WFST weights for rules in this category
        let wfst = prediction_wfsts.get(cat);

        for rule_spec in cat_rules {
            let label = &rule_spec.label;

            // Get weight from WFST or default to one()
            let rule_weight = wfst
                .and_then(|w| {
                    w.actions
                        .iter()
                        .find(|a| a.action.rule_label() == *label)
                        .map(|a| a.weight.value())
                })
                .unwrap_or(0.0);

            let w = weight_fn(rule_weight);

            // Create rule entry point
            let rule_entry = StackSymbol::rule_position(cat, label, 0);
            wpds.ensure_symbol(rule_entry.clone());

            // Category entry → rule entry (Replace): dispatching to this rule
            wpds.add_rule(WpdsRule::Replace {
                from_gamma: cat_entry.clone(),
                to_gamma: rule_entry.clone(),
                weight: w,
            });

            // Walk syntax items, creating transitions for each position
            let mut pos: u32 = 0;
            for (_idx, item) in rule_spec.syntax.iter().enumerate() {
                let current = StackSymbol::rule_position(cat, label, pos);
                wpds.ensure_symbol(current.clone());
                let next_pos = pos + 1;

                match item {
                    SyntaxItemSpec::Terminal(_) => {
                        // Intraprocedural: consume terminal (Replace)
                        let next = StackSymbol::rule_position(cat, label, next_pos);
                        wpds.ensure_symbol(next.clone());
                        wpds.add_rule(WpdsRule::Replace {
                            from_gamma: current,
                            to_gamma: next,
                            weight: W::one(),
                        });
                    }
                    SyntaxItemSpec::NonTerminal { category: ref nt_cat, .. } => {
                        if nt_cat == cat {
                            // Same-category recursion: Replace (handled by Pratt BP)
                            let next = StackSymbol::rule_position(cat, label, next_pos);
                            wpds.ensure_symbol(next.clone());
                            wpds.add_rule(WpdsRule::Replace {
                                from_gamma: current,
                                to_gamma: next,
                                weight: W::one(),
                            });
                        } else {
                            // Cross-category call: Push (callee entry on top, continuation on bottom)
                            let continuation = StackSymbol::rule_position(cat, label, next_pos);
                            let callee_entry = StackSymbol::category_entry(nt_cat);
                            wpds.ensure_symbol(continuation.clone());
                            wpds.ensure_symbol(callee_entry.clone());
                            wpds.add_rule(WpdsRule::Push {
                                from_gamma: current,
                                to_gamma_bottom: continuation,
                                to_gamma_top: callee_entry,
                                weight: W::one(),
                            });
                        }
                    }
                    SyntaxItemSpec::Binder { category: ref b_cat, .. } => {
                        if b_cat == cat {
                            let next = StackSymbol::rule_position(cat, label, next_pos);
                            wpds.ensure_symbol(next.clone());
                            wpds.add_rule(WpdsRule::Replace {
                                from_gamma: current,
                                to_gamma: next,
                                weight: W::one(),
                            });
                        } else {
                            let continuation = StackSymbol::rule_position(cat, label, next_pos);
                            let callee_entry = StackSymbol::category_entry(b_cat);
                            wpds.ensure_symbol(continuation.clone());
                            wpds.ensure_symbol(callee_entry.clone());
                            wpds.add_rule(WpdsRule::Push {
                                from_gamma: current,
                                to_gamma_bottom: continuation,
                                to_gamma_top: callee_entry,
                                weight: W::one(),
                            });
                        }
                    }
                    SyntaxItemSpec::Collection { element_category: ref e_cat, .. } => {
                        if e_cat == cat {
                            let next = StackSymbol::rule_position(cat, label, next_pos);
                            wpds.ensure_symbol(next.clone());
                            wpds.add_rule(WpdsRule::Replace {
                                from_gamma: current,
                                to_gamma: next,
                                weight: W::one(),
                            });
                        } else {
                            let continuation = StackSymbol::rule_position(cat, label, next_pos);
                            let callee_entry = StackSymbol::category_entry(e_cat);
                            wpds.ensure_symbol(continuation.clone());
                            wpds.ensure_symbol(callee_entry.clone());
                            wpds.add_rule(WpdsRule::Push {
                                from_gamma: current,
                                to_gamma_bottom: continuation,
                                to_gamma_top: callee_entry,
                                weight: W::one(),
                            });
                        }
                    }
                    SyntaxItemSpec::IdentCapture { .. }
                    | SyntaxItemSpec::BinderCollection { .. } => {
                        // These consume an identifier token — intraprocedural
                        let next = StackSymbol::rule_position(cat, label, next_pos);
                        wpds.ensure_symbol(next.clone());
                        wpds.add_rule(WpdsRule::Replace {
                            from_gamma: current,
                            to_gamma: next,
                            weight: W::one(),
                        });
                    }
                    SyntaxItemSpec::Sep { body, .. } => {
                        // Separated list: model as single cross-category or replace
                        build_syntax_item_rules(&mut wpds, cat, label, &current, pos, body);
                        // After Sep, continue to next position
                        let next = StackSymbol::rule_position(cat, label, next_pos);
                        wpds.ensure_symbol(next.clone());
                        // The Sep body may loop, but we model a single traversal
                        wpds.add_rule(WpdsRule::Replace {
                            from_gamma: current,
                            to_gamma: next,
                            weight: W::one(),
                        });
                    }
                    SyntaxItemSpec::Map { .. } => {
                        // Structured body: treat as sequence
                        let next = StackSymbol::rule_position(cat, label, next_pos);
                        wpds.ensure_symbol(next.clone());
                        wpds.add_rule(WpdsRule::Replace {
                            from_gamma: current,
                            to_gamma: next,
                            weight: W::one(),
                        });
                    }
                    SyntaxItemSpec::Zip { left_category, right_category, .. } => {
                        // Dual-accumulator: model cross-category calls for each category
                        let continuation = StackSymbol::rule_position(cat, label, next_pos);
                        wpds.ensure_symbol(continuation.clone());

                        for ref_cat in [left_category.as_str(), right_category.as_str()] {
                            if ref_cat != cat {
                                let callee_entry = StackSymbol::category_entry(ref_cat);
                                wpds.ensure_symbol(callee_entry.clone());
                                wpds.add_rule(WpdsRule::Push {
                                    from_gamma: current.clone(),
                                    to_gamma_bottom: continuation.clone(),
                                    to_gamma_top: callee_entry,
                                    weight: W::one(),
                                });
                            }
                        }
                        // Also allow intraprocedural transition (same-category or completed)
                        wpds.add_rule(WpdsRule::Replace {
                            from_gamma: current,
                            to_gamma: continuation,
                            weight: W::one(),
                        });
                    }
                    SyntaxItemSpec::Optional { inner } => {
                        // Optional group: both skip and enter paths
                        let next = StackSymbol::rule_position(cat, label, next_pos);
                        wpds.ensure_symbol(next.clone());
                        // Skip path
                        wpds.add_rule(WpdsRule::Replace {
                            from_gamma: current.clone(),
                            to_gamma: next.clone(),
                            weight: W::one(),
                        });
                        // Enter path: model cross-category references inside optional
                        for sub_item in inner {
                            if let Some(ref_cat) = cross_category_ref(sub_item, cat) {
                                let callee_entry = StackSymbol::category_entry(&ref_cat);
                                wpds.ensure_symbol(callee_entry.clone());
                                wpds.add_rule(WpdsRule::Push {
                                    from_gamma: current.clone(),
                                    to_gamma_bottom: next.clone(),
                                    to_gamma_top: callee_entry,
                                    weight: W::one(),
                                });
                            }
                        }
                    }
                }
                pos = next_pos;
            }

            // Rule completion: Pop (return to caller)
            let final_pos = StackSymbol::rule_position(cat, label, pos);
            wpds.ensure_symbol(final_pos.clone());
            wpds.add_rule(WpdsRule::Pop {
                from_gamma: final_pos,
                weight: W::one(),
            });
        }
    }

    wpds
}

/// Extract cross-category reference from a syntax item, if any.
fn cross_category_ref(item: &SyntaxItemSpec, current_cat: &str) -> Option<String> {
    match item {
        SyntaxItemSpec::NonTerminal { category, .. } if category != current_cat => {
            Some(category.clone())
        }
        SyntaxItemSpec::Binder { category, .. } if category != current_cat => {
            Some(category.clone())
        }
        SyntaxItemSpec::Collection { element_category, .. } if element_category != current_cat => {
            Some(element_category.clone())
        }
        _ => None,
    }
}

/// Build WPDS rules for a nested syntax item (e.g., Sep body).
fn build_syntax_item_rules<W: Semiring>(
    wpds: &mut Wpds<W>,
    cat: &str,
    label: &str,
    current: &StackSymbol,
    pos: u32,
    item: &SyntaxItemSpec,
) {
    if let Some(ref_cat) = cross_category_ref(item, cat) {
        let continuation = StackSymbol::rule_position(cat, label, pos + 1);
        let callee_entry = StackSymbol::category_entry(&ref_cat);
        wpds.ensure_symbol(continuation.clone());
        wpds.ensure_symbol(callee_entry.clone());
        wpds.add_rule(WpdsRule::Push {
            from_gamma: current.clone(),
            to_gamma_bottom: continuation,
            to_gamma_top: callee_entry,
            weight: W::one(),
        });
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// poststar: Forward reachability saturation (Reps et al. 2007)
// ══════════════════════════════════════════════════════════════════════════════

/// Compute poststar (forward reachability) for a WPDS.
///
/// Given an initial P-automaton `A₀` encoding the start configuration
/// `⟨p, γ₀⟩`, computes `A_post*` — the weighted P-automaton accepting
/// all configurations reachable from A₀ with MOVP weights.
///
/// **Algorithm** (Reps et al. 2007, Figure 3):
/// For each PDS rule `r: ⟨p, γ⟩ ↪ ⟨p', u⟩` with weight `f(r)`:
///
/// - Pop (`|u|=0`): If `(p, γ, q)` in A with weight w, add nothing (config accepted)
/// - Replace (`|u|=1`): If `(p, γ, q)` with w, add `(p', γ', q)` with `f(r) ⊗ w`
/// - Push (`|u|=2`): If `(p, γ, q)` with w, add fresh state `q_r`,
///   add `(p', γ', q_r)` with `f(r)` and `(q_r, γ'', q)` with `w`
///
/// Saturation terminates when no new transitions can be added. For bounded
/// idempotent semirings, this converges in finite steps.
///
/// **Complexity:** O_s(|P||Δ|(|Q₀|+|Δ|)H) where H = weight domain height.
pub fn poststar<W: Semiring>(wpds: &Wpds<W>) -> PAutomaton<W> {
    // Initial P-automaton: state p (=0), transition (p, γ₀, q_f) with weight one()
    let p_state: PAutomatonStateId = 0;
    let mut automaton = PAutomaton::new(p_state);
    let q_final = automaton.add_state();
    automaton.mark_final(q_final);

    // Initial transition: (p, initial_symbol, q_final) with weight one()
    automaton.add_transition(p_state, wpds.initial_symbol.clone(), q_final, W::one());
    automaton.symbol_to_state.insert(wpds.initial_symbol.clone(), q_final);

    // Worklist of transitions to process: (from, symbol, to, weight)
    let mut worklist: VecDeque<(PAutomatonStateId, StackSymbol, PAutomatonStateId, W)> =
        VecDeque::new();
    worklist.push_back((p_state, wpds.initial_symbol.clone(), q_final, W::one()));

    // Track existing transitions for convergence: (from, symbol, to) → weight
    let mut existing: HashMap<(PAutomatonStateId, StackSymbol, PAutomatonStateId), W> =
        HashMap::new();
    existing.insert(
        (p_state, wpds.initial_symbol.clone(), q_final),
        W::one(),
    );

    // Fresh state allocation for push rules: from_gamma → fresh_state
    let mut push_states: HashMap<StackSymbol, PAutomatonStateId> = HashMap::new();

    // Saturation loop
    while let Some((_from, gamma, to, w)) = worklist.pop_front() {
        // Find all rules with source gamma
        let rule_indices: Vec<usize> = wpds.rules_for(&gamma).to_vec();

        for rule_idx in rule_indices {
            let rule = &wpds.rules[rule_idx];

            match rule {
                WpdsRule::Pop { .. } => {
                    // Pop: configuration ⟨p, γ⟩ → ⟨p', ε⟩
                    // The automaton already accepts γ from state `from`; pop means
                    // the remaining stack below γ is now the active configuration.
                    // For single-control-location WPDS, this means we've returned.
                    // No new transition needed — the path already reaches q_final.
                }
                WpdsRule::Replace { to_gamma, weight, .. } => {
                    // Replace: ⟨p, γ⟩ → ⟨p', γ'⟩
                    // Add transition (p, γ', to) with weight f(r) ⊗ w
                    let new_weight = weight.times(&w);
                    let key = (p_state, to_gamma.clone(), to);

                    let should_add = match existing.get(&key) {
                        Some(old_w) => {
                            let combined = old_w.plus(&new_weight);
                            if !combined.approx_eq(old_w, 1e-10) {
                                existing.insert(key.clone(), combined);
                                true
                            } else {
                                false
                            }
                        }
                        None => {
                            existing.insert(key.clone(), new_weight);
                            true
                        }
                    };

                    if should_add {
                        let combined = existing.get(&key).expect("just inserted").clone();
                        automaton.add_transition(p_state, to_gamma.clone(), to, combined);
                        automaton.symbol_to_state.entry(to_gamma.clone()).or_insert(to);
                        worklist.push_back((p_state, to_gamma.clone(), to, combined));
                    }
                }
                WpdsRule::Push { to_gamma_bottom, to_gamma_top, weight, .. } => {
                    // Push: ⟨p, γ⟩ → ⟨p', γ_bottom γ_top⟩
                    // Need: (p, γ_top, q_r) and (q_r, γ_bottom, to)
                    // where q_r is a fresh state for this push rule's source
                    let q_r = *push_states.entry(gamma.clone()).or_insert_with(|| {
                        automaton.add_state()
                    });

                    // Add (q_r, γ_bottom, to) with weight w
                    let bottom_key = (q_r, to_gamma_bottom.clone(), to);
                    let bottom_new = match existing.get(&bottom_key) {
                        Some(old_w) => {
                            let combined = old_w.plus(&w);
                            if !combined.approx_eq(old_w, 1e-10) {
                                existing.insert(bottom_key.clone(), combined);
                                true
                            } else {
                                false
                            }
                        }
                        None => {
                            existing.insert(bottom_key.clone(), w.clone());
                            true
                        }
                    };

                    if bottom_new {
                        let bw = existing.get(&bottom_key).expect("just inserted").clone();
                        automaton.add_transition(q_r, to_gamma_bottom.clone(), to, bw);
                    }

                    // Add (p, γ_top, q_r) with weight f(r)
                    let top_key = (p_state, to_gamma_top.clone(), q_r);
                    let top_new = match existing.get(&top_key) {
                        Some(old_w) => {
                            let combined = old_w.plus(weight);
                            if !combined.approx_eq(old_w, 1e-10) {
                                existing.insert(top_key.clone(), combined);
                                true
                            } else {
                                false
                            }
                        }
                        None => {
                            existing.insert(top_key.clone(), *weight);
                            true
                        }
                    };

                    if top_new {
                        let tw = existing.get(&top_key).expect("just inserted").clone();
                        automaton.add_transition(p_state, to_gamma_top.clone(), q_r, tw);
                        automaton.symbol_to_state.entry(to_gamma_top.clone()).or_insert(q_r);
                        worklist.push_back((p_state, to_gamma_top.clone(), q_r, tw));
                    }
                }
            }
        }
    }

    automaton
}

/// Compute prestar (backward reachability) for a WPDS.
///
/// Given a target P-automaton encoding configurations we want to reach,
/// computes `A_pre*` — the weighted P-automaton accepting all configurations
/// from which the target is reachable.
///
/// **Algorithm** (Reps et al. 2007, Figure 2):
/// For each PDS rule `r: ⟨p, γ⟩ ↪ ⟨p', u⟩` with weight `f(r)`:
///
/// - Pop (`|u|=0`): Add `(p, γ, p')` with `f(r)`
/// - Replace (`|u|=1`): If `(p', γ', q)` with w, add `(p, γ, q)` with `f(r) ⊗ w`
/// - Push (`|u|=2`): If `(p', γ', q')` with w₁ and `(q', γ'', q)` with w₂,
///   add `(p, γ, q)` with `f(r) ⊗ w₁ ⊗ w₂`
pub fn prestar<W: Semiring>(wpds: &Wpds<W>, target: &PAutomaton<W>) -> PAutomaton<W> {
    let p_state: PAutomatonStateId = 0;
    let mut automaton = target.clone();

    // Worklist: process transitions until convergence
    let mut worklist: VecDeque<(PAutomatonStateId, StackSymbol, PAutomatonStateId, W)> =
        VecDeque::new();

    let mut existing: HashMap<(PAutomatonStateId, StackSymbol, PAutomatonStateId), W> =
        HashMap::new();
    for trans in &automaton.transitions {
        let key = (trans.from, trans.symbol.clone(), trans.to);
        let entry = existing.entry(key).or_insert(W::zero());
        *entry = entry.plus(&trans.weight);
    }

    // Phase 1: Initialize pop rules (processed once, not per-worklist-item).
    // Pop rule ⟨p, γ⟩ → ⟨p', ε⟩ means: if at state p with γ on stack, transition
    // to p' with empty stack. In prestar terms: add (p, γ, p') unconditionally.
    for rule in &wpds.rules {
        if let WpdsRule::Pop { from_gamma, weight } = rule {
            let key = (p_state, from_gamma.clone(), p_state);
            let new_weight = *weight;
            let changed = match existing.get(&key) {
                Some(old_w) => {
                    let combined = old_w.plus(&new_weight);
                    if !combined.approx_eq(old_w, 1e-10) {
                        existing.insert(key.clone(), combined);
                        true
                    } else {
                        false
                    }
                }
                None => {
                    existing.insert(key.clone(), new_weight);
                    true
                }
            };
            if changed {
                let cw = *existing.get(&key).expect("just inserted");
                automaton.add_transition(p_state, from_gamma.clone(), p_state, cw);
                worklist.push_back((p_state, from_gamma.clone(), p_state, cw));
            }
        }
    }

    // Also seed worklist with all existing target transitions (after pop init,
    // so replace/push rules can chain off both target and pop transitions).
    for trans in &target.transitions {
        worklist.push_back((trans.from, trans.symbol.clone(), trans.to, trans.weight));
    }

    // Phase 2: Worklist saturation for replace and push rules only.
    // When we dequeue transition (from, gamma, to), we check replace/push rules
    // whose RHS produces gamma.
    while let Some((_from, gamma, _to, _w)) = worklist.pop_front() {
        for rule in &wpds.rules {
            match rule {
                WpdsRule::Pop { .. } => {
                    // Pop rules are already handled in Phase 1.
                }
                WpdsRule::Replace { from_gamma, to_gamma, weight } => {
                    // Replace: ⟨p, from_gamma⟩ → ⟨p', to_gamma⟩
                    // If (p', to_gamma, q) exists, add (p, from_gamma, q) with f(r) ⊗ w
                    if *to_gamma == gamma {
                        // Find all transitions (p_state, to_gamma, q)
                        let targets: Vec<(PAutomatonStateId, W)> = existing
                            .iter()
                            .filter(|((f, s, _), _)| *f == p_state && *s == *to_gamma)
                            .map(|((_, _, t), w)| (*t, *w))
                            .collect();

                        for (q, w) in targets {
                            let new_weight = weight.times(&w);
                            let key = (p_state, from_gamma.clone(), q);
                            let should_add = match existing.get(&key) {
                                Some(old_w) => {
                                    let combined = old_w.plus(&new_weight);
                                    if !combined.approx_eq(old_w, 1e-10) {
                                        existing.insert(key.clone(), combined);
                                        true
                                    } else {
                                        false
                                    }
                                }
                                None => {
                                    existing.insert(key.clone(), new_weight);
                                    true
                                }
                            };
                            if should_add {
                                let cw = *existing.get(&key).expect("just inserted");
                                automaton.add_transition(p_state, from_gamma.clone(), q, cw);
                                worklist.push_back((p_state, from_gamma.clone(), q, cw));
                            }
                        }
                    }
                }
                WpdsRule::Push { from_gamma, to_gamma_bottom, to_gamma_top, weight } => {
                    // Push: ⟨p, from_gamma⟩ → ⟨p', γ_bottom γ_top⟩
                    // If (p', γ_top, q') and (q', γ_bottom, q) exist,
                    // add (p, from_gamma, q) with f(r) ⊗ w₁ ⊗ w₂
                    if *to_gamma_top == gamma || *to_gamma_bottom == gamma {
                        // Find (p_state, γ_top, q')
                        let top_targets: Vec<(PAutomatonStateId, W)> = existing
                            .iter()
                            .filter(|((f, s, _), _)| *f == p_state && *s == *to_gamma_top)
                            .map(|((_, _, t), w)| (*t, *w))
                            .collect();

                        for (q_prime, w1) in &top_targets {
                            // Find (q', γ_bottom, q)
                            let bottom_targets: Vec<(PAutomatonStateId, W)> = existing
                                .iter()
                                .filter(|((f, s, _), _)| *f == *q_prime && *s == *to_gamma_bottom)
                                .map(|((_, _, t), w)| (*t, *w))
                                .collect();

                            for (q, w2) in bottom_targets {
                                let new_weight = weight.times(w1).times(&w2);
                                let key = (p_state, from_gamma.clone(), q);
                                let should_add = match existing.get(&key) {
                                    Some(old_w) => {
                                        let combined = old_w.plus(&new_weight);
                                        if !combined.approx_eq(old_w, 1e-10) {
                                            existing.insert(key.clone(), combined);
                                            true
                                        } else {
                                            false
                                        }
                                    }
                                    None => {
                                        existing.insert(key.clone(), new_weight);
                                        true
                                    }
                                };
                                if should_add {
                                    let cw = *existing.get(&key).expect("just inserted");
                                    automaton.add_transition(p_state, from_gamma.clone(), q, cw);
                                    worklist.push_back((p_state, from_gamma.clone(), q, cw));
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    automaton
}

// ══════════════════════════════════════════════════════════════════════════════
// Stringsum: Butoi et al. (2022) per-input ambiguity analysis
// ══════════════════════════════════════════════════════════════════════════════

/// Token representation for stringsum computation.
///
/// Maps PraTTaIL terminal tokens to indices for the DP tables.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct StringsumInput {
    /// Token sequence as terminal strings.
    pub tokens: Vec<String>,
}

/// Result of stringsum computation for a single input.
#[derive(Debug, Clone)]
pub struct StringsumResult<W: Semiring> {
    /// The input that was analyzed.
    pub input: StringsumInput,
    /// Total weight of all accepting runs (parse derivations).
    pub total_weight: W,
    /// Per-position weights (weight of all runs at each input position).
    pub position_weights: Vec<W>,
}

/// Compute stringsum over a WPDS for a given input string.
///
/// This implements a simplified version of Butoi et al. (2022) stringsum
/// adapted for PraTTaIL's grammar structure. Rather than the full O(n³|Q|³|Γ|³)
/// algorithm, we exploit PraTTaIL's deterministic dispatch to reduce to
/// a poststar-based computation:
///
/// 1. Build poststar P-automaton from the WPDS
/// 2. For each token in the input, find matching rules and accumulate weights
/// 3. The total weight is the product of per-position weights
///
/// For ambiguity detection, use `CountingWeight`: if result > 1, the input
/// has multiple parse derivations.
pub fn stringsum<W: Semiring>(
    _wpds: &Wpds<W>,
    post_automaton: &PAutomaton<W>,
    input: &StringsumInput,
    spec: &LanguageSpec,
) -> StringsumResult<W> {
    // For each token in the input, find which rules can consume it
    // and accumulate the total weight across all possible parse paths.
    //
    // This is a simplified approach that leverages the poststar P-automaton
    // to determine reachable rules at each position.

    let mut position_weights = Vec::with_capacity(input.tokens.len());
    let mut total = W::one();

    // Group rules by their first terminal
    let mut rules_by_first_terminal: HashMap<&str, Vec<(&str, &str, W)>> = HashMap::new();
    for rule in &spec.rules {
        if let Some(SyntaxItemSpec::Terminal(ref tok)) = rule.syntax.first() {
            let sym = StackSymbol::category_entry(&rule.category);
            let sym_weight = post_automaton.symbol_weight(&sym);
            if !sym_weight.is_zero() {
                rules_by_first_terminal
                    .entry(tok.as_str())
                    .or_default()
                    .push((&rule.category, &rule.label, sym_weight));
            }
        }
    }

    for token in &input.tokens {
        let mut pos_weight = W::zero();

        // Find all rules that could consume this token
        if let Some(matching_rules) = rules_by_first_terminal.get(token.as_str()) {
            for (_cat, _label, w) in matching_rules {
                pos_weight = pos_weight.plus(w);
            }
        }

        // Also check non-terminal starts (ident, integer, etc.)
        for rule in &spec.rules {
            if rule.is_var || rule.is_literal {
                let sym = StackSymbol::category_entry(&rule.category);
                let sym_weight = post_automaton.symbol_weight(&sym);
                if !sym_weight.is_zero() {
                    // Check if this token could match a variable/literal pattern
                    let matches = match token.as_str() {
                        t if t.chars().all(|c| c.is_ascii_digit()) && rule.is_literal => true,
                        t if t.starts_with('"') && rule.is_literal => true,
                        t if t.chars().next().is_some_and(|c| c.is_ascii_alphabetic() || c == '_')
                            && rule.is_var =>
                        {
                            true
                        }
                        _ => false,
                    };
                    if matches {
                        pos_weight = pos_weight.plus(&sym_weight);
                    }
                }
            }
        }

        // If no rule matches, this position has zero weight (parse fails)
        if pos_weight.is_zero() {
            pos_weight = W::zero();
        }

        total = total.times(&pos_weight);
        position_weights.push(pos_weight);
    }

    StringsumResult {
        input: input.clone(),
        total_weight: total,
        position_weights,
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Analysis results (consumed by lint and cost_benefit)
// ══════════════════════════════════════════════════════════════════════════════

/// WPDS analysis results for a grammar.
///
// ══════════════════════════════════════════════════════════════════════════════
// G33: WPDS Call Graph
// ══════════════════════════════════════════════════════════════════════════════

/// A directed edge in the WPDS call graph representing a cross-category call.
#[derive(Debug, Clone)]
pub struct CallEdge {
    /// Category initiating the call.
    pub caller_cat: String,
    /// Category being called.
    pub callee_cat: String,
    /// Number of distinct call sites (Push rules) for this edge.
    pub call_sites: usize,
    /// Sum of weights across all call sites (TropicalWeight → min, Counting → sum).
    pub total_weight: f64,
}

/// Directed, weighted call graph extracted from WPDS Push rules.
///
/// Each edge `(caller → callee)` represents one or more cross-category Push
/// rules. The graph includes SCC decomposition (Tarjan) for recursion analysis.
#[derive(Debug, Clone)]
pub struct WpdsCallGraph {
    /// All directed edges.
    pub edges: Vec<CallEdge>,
    /// Fan-out: number of distinct callees per category.
    pub fan_out: HashMap<String, usize>,
    /// Fan-in: number of distinct callers per category.
    pub fan_in: HashMap<String, usize>,
    /// Strongly connected components (Tarjan). Each SCC is a set of category names.
    /// SCCs of size > 1 indicate mutual recursion; size 1 with self-edge = direct recursion.
    pub sccs: Vec<Vec<String>>,
    /// All category names present in the graph (as caller or callee).
    pub categories: HashSet<String>,
}

/// Extract a directed call graph from WPDS Push rules.
///
/// Linear scan of Push rules produces `CallEdge`s with call-site multiplicity
/// and weight aggregation. Tarjan SCC decomposition identifies recursion.
pub fn extract_call_graph<W: Semiring>(wpds: &Wpds<W>) -> WpdsCallGraph {
    // Aggregate Push rules into edges: (caller_cat, callee_cat) → (count, weight_sum)
    let mut edge_map: HashMap<(String, String), (usize, f64)> = HashMap::new();
    let mut categories: HashSet<String> = HashSet::new();

    for rule in &wpds.rules {
        if let WpdsRule::Push {
            from_gamma,
            to_gamma_top,
            ..
        } = rule
        {
            let caller = &from_gamma.category;
            let callee = &to_gamma_top.category;
            if !caller.is_empty() && !callee.is_empty() && caller != callee {
                categories.insert(caller.clone());
                categories.insert(callee.clone());
                let entry = edge_map
                    .entry((caller.clone(), callee.clone()))
                    .or_insert((0, 0.0));
                entry.0 += 1;
                // Use a simple numeric proxy for weight aggregation
                if !rule.weight().is_zero() {
                    entry.1 += 1.0;
                }
            }
        }
    }

    // Also include categories from Replace rules (for categories with no cross-category calls)
    for rule in &wpds.rules {
        let cat = &rule.from_gamma().category;
        if !cat.is_empty() {
            categories.insert(cat.clone());
        }
    }

    let edges: Vec<CallEdge> = edge_map
        .into_iter()
        .map(|((caller, callee), (count, weight))| CallEdge {
            caller_cat: caller,
            callee_cat: callee,
            call_sites: count,
            total_weight: weight,
        })
        .collect();

    // Compute fan-in and fan-out
    let mut fan_out: HashMap<String, usize> = HashMap::new();
    let mut fan_in: HashMap<String, usize> = HashMap::new();
    for edge in &edges {
        *fan_out.entry(edge.caller_cat.clone()).or_insert(0) += 1;
        *fan_in.entry(edge.callee_cat.clone()).or_insert(0) += 1;
    }

    // Tarjan SCC decomposition
    let sccs = tarjan_scc(&categories, &edges);

    WpdsCallGraph {
        edges,
        fan_out,
        fan_in,
        sccs,
        categories,
    }
}

/// Tarjan's strongly connected components algorithm on the call graph.
fn tarjan_scc(categories: &HashSet<String>, edges: &[CallEdge]) -> Vec<Vec<String>> {
    // Build adjacency list
    let cat_list: Vec<String> = categories.iter().cloned().collect();
    let cat_index: HashMap<&str, usize> = cat_list
        .iter()
        .enumerate()
        .map(|(i, c)| (c.as_str(), i))
        .collect();
    let n = cat_list.len();

    let mut adj: Vec<Vec<usize>> = vec![Vec::new(); n];
    for edge in edges {
        if let (Some(&from), Some(&to)) = (
            cat_index.get(edge.caller_cat.as_str()),
            cat_index.get(edge.callee_cat.as_str()),
        ) {
            adj[from].push(to);
        }
    }

    // Tarjan state
    let mut index_counter: usize = 0;
    let mut stack: Vec<usize> = Vec::new();
    let mut on_stack = vec![false; n];
    let mut indices = vec![usize::MAX; n]; // usize::MAX = undefined
    let mut lowlinks = vec![0usize; n];
    let mut result: Vec<Vec<String>> = Vec::new();

    fn strongconnect(
        v: usize,
        adj: &[Vec<usize>],
        index_counter: &mut usize,
        stack: &mut Vec<usize>,
        on_stack: &mut [bool],
        indices: &mut [usize],
        lowlinks: &mut [usize],
        result: &mut Vec<Vec<String>>,
        cat_list: &[String],
    ) {
        indices[v] = *index_counter;
        lowlinks[v] = *index_counter;
        *index_counter += 1;
        stack.push(v);
        on_stack[v] = true;

        for &w in &adj[v] {
            if indices[w] == usize::MAX {
                strongconnect(
                    w,
                    adj,
                    index_counter,
                    stack,
                    on_stack,
                    indices,
                    lowlinks,
                    result,
                    cat_list,
                );
                lowlinks[v] = lowlinks[v].min(lowlinks[w]);
            } else if on_stack[w] {
                lowlinks[v] = lowlinks[v].min(indices[w]);
            }
        }

        if lowlinks[v] == indices[v] {
            let mut component = Vec::new();
            loop {
                let w = stack.pop().expect("tarjan stack underflow");
                on_stack[w] = false;
                component.push(cat_list[w].clone());
                if w == v {
                    break;
                }
            }
            result.push(component);
        }
    }

    for v in 0..n {
        if indices[v] == usize::MAX {
            strongconnect(
                v,
                &adj,
                &mut index_counter,
                &mut stack,
                &mut on_stack,
                &mut indices,
                &mut lowlinks,
                &mut result,
                &cat_list,
            );
        }
    }

    result
}

/// Compute the shortest path from any reachable category to a target category
/// in the call graph. Returns a witness trace (list of steps) or empty vec
/// if no path exists.
pub fn shortest_path_witness(
    call_graph: &WpdsCallGraph,
    reachable: &HashSet<String>,
    target_cat: &str,
) -> Vec<String> {
    // BFS from all reachable categories to target
    // Build reverse adjacency: callee → callers
    let mut reverse_adj: HashMap<&str, Vec<&str>> = HashMap::new();
    for edge in &call_graph.edges {
        reverse_adj
            .entry(edge.callee_cat.as_str())
            .or_default()
            .push(edge.caller_cat.as_str());
    }

    // BFS backwards from target_cat to find a reachable category
    let mut visited: HashSet<&str> = HashSet::new();
    let mut parent: HashMap<&str, &str> = HashMap::new();
    let mut queue: VecDeque<&str> = VecDeque::new();

    visited.insert(target_cat);
    queue.push_back(target_cat);

    let mut found_source: Option<&str> = None;

    // If target itself is reachable, no path needed (shouldn't happen for dead rules)
    if reachable.contains(target_cat) {
        return vec![format!("{} (reachable)", target_cat)];
    }

    while let Some(current) = queue.pop_front() {
        if let Some(callers) = reverse_adj.get(current) {
            for &caller in callers {
                if !visited.contains(caller) {
                    visited.insert(caller);
                    parent.insert(caller, current);
                    if reachable.contains(caller) {
                        found_source = Some(caller);
                        break;
                    }
                    queue.push_back(caller);
                }
            }
        }
        if found_source.is_some() {
            break;
        }
    }

    match found_source {
        Some(source) => {
            // Reconstruct path from source to target
            let mut path = Vec::new();
            let mut current = source;
            path.push(format!("{} (reachable)", current));
            while current != target_cat {
                if let Some(&next) = parent.get(current) {
                    path.push(format!("  → Push to {} (missing)", next));
                    current = next;
                } else {
                    break;
                }
            }
            path
        }
        None => {
            // No path exists from any reachable category
            vec![format!(
                "{} has no path from any reachable category",
                target_cat
            )]
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// G34: Recursion Depth Bounds
// ══════════════════════════════════════════════════════════════════════════════

/// Per-category recursion depth bounds derived from WPDS analysis.
#[derive(Debug, Clone)]
pub struct DepthBounds {
    /// Minimum nesting depth at which this category appears (0 = top-level).
    pub min_depth: u32,
    /// Maximum nesting depth (`None` = unbounded, i.e. recursive).
    pub max_depth: Option<u32>,
    /// Whether this category participates in recursion (SCC member or self-loop).
    pub is_recursive: bool,
}

/// Compute per-category depth bounds from the call graph and P-automaton.
///
/// Uses BFS from the primary category on the call graph to determine min depth.
/// Categories in non-trivial SCCs (|SCC|>1 or self-loop) get `max_depth = None`.
/// Non-recursive categories get `max_depth = min_depth` (only reachable at a fixed depth).
pub fn compute_depth_bounds(
    call_graph: &WpdsCallGraph,
    primary_cat: &str,
) -> HashMap<String, DepthBounds> {
    let mut result = HashMap::new();

    // Build adjacency list for BFS
    let mut adj: HashMap<&str, Vec<&str>> = HashMap::new();
    for edge in &call_graph.edges {
        adj.entry(edge.caller_cat.as_str())
            .or_default()
            .push(edge.callee_cat.as_str());
    }

    // Identify recursive categories (in non-trivial SCCs)
    let mut recursive_cats: HashSet<&str> = HashSet::new();
    for scc in &call_graph.sccs {
        if scc.len() > 1 {
            // Mutual recursion
            for cat in scc {
                recursive_cats.insert(cat.as_str());
            }
        } else if scc.len() == 1 {
            // Check for self-loop
            let cat = &scc[0];
            if call_graph
                .edges
                .iter()
                .any(|e| e.caller_cat == *cat && e.callee_cat == *cat)
            {
                recursive_cats.insert(cat.as_str());
            }
        }
    }

    // BFS from primary to compute min_depth
    let mut visited: HashMap<&str, u32> = HashMap::new();
    let mut queue: VecDeque<(&str, u32)> = VecDeque::new();
    visited.insert(primary_cat, 0);
    queue.push_back((primary_cat, 0));

    while let Some((cat, depth)) = queue.pop_front() {
        if let Some(callees) = adj.get(cat) {
            for &callee in callees {
                if !visited.contains_key(callee) {
                    visited.insert(callee, depth + 1);
                    queue.push_back((callee, depth + 1));
                }
            }
        }
    }

    for cat in &call_graph.categories {
        let min_depth = visited.get(cat.as_str()).copied().unwrap_or(u32::MAX);
        let is_recursive = recursive_cats.contains(cat.as_str());
        let max_depth = if is_recursive || min_depth == u32::MAX {
            None
        } else {
            Some(min_depth)
        };
        result.insert(
            cat.clone(),
            DepthBounds {
                min_depth: if min_depth == u32::MAX { 0 } else { min_depth },
                max_depth,
                is_recursive,
            },
        );
    }

    result
}

// ══════════════════════════════════════════════════════════════════════════════
// G35: Cycle Classification
// ══════════════════════════════════════════════════════════════════════════════

/// Classification of a cycle in the call graph.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CycleKind {
    /// Single category with a self-loop (e.g., Expr calls itself cross-category).
    Direct,
    /// Multiple categories forming a cycle (e.g., Expr → Type → Expr).
    Mutual,
}

/// Information about a cycle in the WPDS call graph.
#[derive(Debug, Clone)]
pub struct CycleInfo {
    /// Categories involved in the cycle.
    pub categories: Vec<String>,
    /// Type of cycle.
    pub kind: CycleKind,
    /// Whether any cycle member has a left-recursive Replace from position-0
    /// reaching itself without consuming input.
    pub is_left_recursive: bool,
}

/// Classify all cycles from the call graph SCCs and WPDS rules.
///
/// Direct = |SCC|=1 with self-edge. Mutual = |SCC|>1.
/// Left-recursion check: a category is left-recursive if it has a Replace rule
/// from position-0 back to its own category entry.
pub fn classify_cycles<W: Semiring>(
    call_graph: &WpdsCallGraph,
    wpds: &Wpds<W>,
) -> Vec<CycleInfo> {
    let mut cycles = Vec::new();

    for scc in &call_graph.sccs {
        if scc.len() > 1 {
            // Mutual recursion
            let is_left_recursive = scc.iter().any(|cat| has_left_recursion(cat, wpds));
            cycles.push(CycleInfo {
                categories: scc.clone(),
                kind: CycleKind::Mutual,
                is_left_recursive,
            });
        } else if scc.len() == 1 {
            let cat = &scc[0];
            // Check for self-loop in call graph
            let has_self_edge = call_graph
                .edges
                .iter()
                .any(|e| e.caller_cat == *cat && e.callee_cat == *cat);
            if has_self_edge {
                let is_left_recursive = has_left_recursion(cat, wpds);
                cycles.push(CycleInfo {
                    categories: scc.clone(),
                    kind: CycleKind::Direct,
                    is_left_recursive,
                });
            }
        }
    }

    cycles
}

/// Check if a category has left-recursion in the WPDS: a Replace rule from
/// position-0 of any rule back to its own category entry without consuming input.
fn has_left_recursion<W: Semiring>(category: &str, wpds: &Wpds<W>) -> bool {
    let entry = StackSymbol::category_entry(category);
    // Check if any Replace from category entry goes to a rule@0,
    // and that rule@0 has a Replace back to category entry (or to another rule@0
    // that eventually reaches entry).
    // Simplified check: any Replace rule from entry symbol to a rule@0 that
    // then has a Replace back to entry or another position-0.
    for rule in &wpds.rules {
        if let WpdsRule::Replace {
            from_gamma,
            to_gamma,
            ..
        } = rule
        {
            if *from_gamma == entry && to_gamma.category == category && to_gamma.position == 0 {
                // Entry dispatches to rule@0; now check if rule@0 can reach entry
                // without consuming input (another Replace chain to entry)
                if has_replace_path_to_entry(wpds, to_gamma, &entry) {
                    return true;
                }
            }
        }
    }
    false
}

/// Check if there's a Replace-only path from `start` back to `target` (left-recursion).
fn has_replace_path_to_entry<W: Semiring>(
    wpds: &Wpds<W>,
    start: &StackSymbol,
    target: &StackSymbol,
) -> bool {
    let mut visited: HashSet<StackSymbol> = HashSet::new();
    let mut queue: VecDeque<StackSymbol> = VecDeque::new();
    queue.push_back(start.clone());
    visited.insert(start.clone());

    while let Some(current) = queue.pop_front() {
        for rule in &wpds.rules {
            if let WpdsRule::Replace {
                from_gamma,
                to_gamma,
                ..
            } = rule
            {
                if *from_gamma == current {
                    if *to_gamma == *target {
                        return true;
                    }
                    if !visited.contains(to_gamma) {
                        visited.insert(to_gamma.clone());
                        queue.push_back(to_gamma.clone());
                    }
                }
            }
        }
    }
    false
}

// ══════════════════════════════════════════════════════════════════════════════
// G36: Prestar "Who Calls Me?" Analysis
// ══════════════════════════════════════════════════════════════════════════════

/// A calling context for a category: who calls it, from which rule, at what position.
#[derive(Debug, Clone)]
pub struct CallingContext {
    /// Category that initiates the call.
    pub caller_category: String,
    /// Rule label in the caller that contains the cross-category reference.
    pub caller_rule: String,
    /// Position within the caller's rule where the call occurs.
    pub caller_position: u32,
    /// Weight on the Push rule.
    pub weight: f64,
}

/// Compute calling contexts for each category by scanning WPDS Push rules.
///
/// For each category, returns all `(caller, rule, position)` triples that
/// reference it via Push rules. This is the WPDS-precise version of
/// `find_missing_callers`.
pub fn compute_calling_contexts<W: Semiring>(
    wpds: &Wpds<W>,
) -> HashMap<String, Vec<CallingContext>> {
    let mut contexts: HashMap<String, Vec<CallingContext>> = HashMap::new();

    for rule in &wpds.rules {
        if let WpdsRule::Push {
            from_gamma,
            to_gamma_top,
            weight,
            ..
        } = rule
        {
            if !from_gamma.category.is_empty() && !to_gamma_top.category.is_empty() {
                contexts
                    .entry(to_gamma_top.category.clone())
                    .or_default()
                    .push(CallingContext {
                        caller_category: from_gamma.category.clone(),
                        caller_rule: from_gamma.rule_label.clone(),
                        caller_position: from_gamma.position,
                        weight: if weight.is_zero() { 0.0 } else { 1.0 },
                    });
            }
        }
    }

    contexts
}

/// Produced by `analyze_wpds()` and consumed by:
/// - `lint.rs`: Stack-aware dead-rule detection (W13), complexity report (D14)
/// - `cost_benefit.rs`: Ambiguity refinement (A5)
/// - Pipeline diagnostics (P05)
#[derive(Debug, Clone)]
pub struct WpdsAnalysis {
    /// Grammar name.
    pub grammar_name: String,
    /// Number of stack symbols.
    pub num_symbols: usize,
    /// Number of PDS rules.
    pub num_rules: usize,
    /// Stack-aware reachability: which category entry symbols are reachable from root.
    pub reachable_categories: HashSet<String>,
    /// Stack-aware unreachable rule labels with witness info.
    pub unreachable_rules: Vec<WpdsUnreachableRule>,
    /// Per-category weight from poststar (TropicalWeight).
    pub category_weights: HashMap<String, f64>,
    /// G33: Directed call graph extracted from Push rules.
    pub call_graph: WpdsCallGraph,
    /// G34: Per-category recursion depth bounds.
    pub depth_bounds: HashMap<String, DepthBounds>,
    /// G35: Classified cycles (direct, mutual, left-recursive).
    pub cycles: Vec<CycleInfo>,
    /// G36: Calling contexts per category (who calls each category and from where).
    pub calling_contexts: HashMap<String, Vec<CallingContext>>,
    /// CS-01: Context-sensitive rule tables per category.
    /// Maps `category → ContextRuleTable`.
    /// Empty if no category benefits from context narrowing.
    pub context_rule_tables: HashMap<String, ContextRuleTable>,
    /// CS-04: Per-call-site effective binding power.
    /// Maps `(caller_cat, callee_cat) → min_bp`.
    /// When different callers use different min_bp values, CS-04 threads
    /// the caller-specific BP through cross-category dispatch.
    pub cross_category_bp: HashMap<(String, String), Vec<u8>>,
    /// CS-05: Per-context ambiguity status for categories.
    /// Maps `category → is_unambiguous_in_all_contexts`.
    /// When true, NFA try-all can commit to the first success (skip save/restore).
    pub context_unambiguous: HashMap<String, bool>,
}

// ══════════════════════════════════════════════════════════════════════════════
// CS-01: Context-Sensitive Rule Tables
// ══════════════════════════════════════════════════════════════════════════════

/// A context entry mapping a calling context tag to a set of valid rule indices.
#[derive(Debug, Clone)]
pub struct ContextEntry {
    /// The calling context tag (caller category name or "top-level").
    pub context_tag: String,
    /// Indices of rules valid in this context (into the category's rule list).
    pub valid_rules: Vec<String>,
}

/// Per-category context-sensitive rule table.
///
/// Maps calling contexts to valid rule sets. When all contexts yield the same
/// rule set, the table is trivial (no benefit from context-sensitive dispatch).
#[derive(Debug, Clone)]
pub struct ContextRuleTable {
    /// Category this table serves.
    pub category: String,
    /// One entry per calling context.
    pub entries: Vec<ContextEntry>,
    /// Whether the table is non-trivial (at least one context has a reduced rule set).
    pub is_nontrivial: bool,
    /// Number of contexts where the rule set becomes a singleton (direct dispatch).
    pub singleton_contexts: usize,
}

/// Build context-sensitive rule tables from WPDS analysis.
///
/// For each category with calling contexts, determines which rules are reachable
/// from each calling context. If different contexts yield different rule sets,
/// the table is non-trivial and can be used for context-sensitive dispatch.
pub fn build_context_rule_tables(
    calling_contexts: &HashMap<String, Vec<CallingContext>>,
    reachable_categories: &HashSet<String>,
    all_rules: &[(String, String)], // (rule_label, category) pairs
) -> HashMap<String, ContextRuleTable> {
    let mut tables = HashMap::new();

    // Group rules by category
    let mut rules_by_cat: HashMap<&str, Vec<&str>> = HashMap::new();
    for (label, cat) in all_rules {
        rules_by_cat.entry(cat.as_str()).or_default().push(label.as_str());
    }

    for (cat, contexts) in calling_contexts {
        if !reachable_categories.contains(cat) || contexts.is_empty() {
            continue;
        }

        let all_rules_for_cat: Vec<String> = rules_by_cat
            .get(cat.as_str())
            .map(|v| v.iter().map(|s| s.to_string()).collect())
            .unwrap_or_default();

        if all_rules_for_cat.is_empty() {
            continue;
        }

        // Group calling contexts by caller category
        let mut contexts_by_caller: HashMap<&str, Vec<&CallingContext>> = HashMap::new();
        for ctx in contexts {
            contexts_by_caller
                .entry(ctx.caller_category.as_str())
                .or_default()
                .push(ctx);
        }

        let mut entries = Vec::new();
        let mut is_nontrivial = false;
        let mut singleton_count = 0usize;

        for (caller_cat, _caller_contexts) in &contexts_by_caller {
            // For now, all rules are valid from any calling context.
            // Full rule filtering requires poststar per-rule-per-context reachability,
            // which is expensive. Here we record the structure for downstream use.
            // The actual filtering happens when we have per-rule reachability data.
            let valid = all_rules_for_cat.clone();

            if valid.len() < all_rules_for_cat.len() {
                is_nontrivial = true;
            }
            if valid.len() == 1 {
                singleton_count += 1;
            }

            entries.push(ContextEntry {
                context_tag: caller_cat.to_string(),
                valid_rules: valid,
            });
        }

        // Also add a "top-level" entry if this is the primary category
        // (called directly, not via Push)
        entries.push(ContextEntry {
            context_tag: "top-level".to_string(),
            valid_rules: all_rules_for_cat,
        });

        tables.insert(
            cat.clone(),
            ContextRuleTable {
                category: cat.clone(),
                entries,
                is_nontrivial,
                singleton_contexts: singleton_count,
            },
        );
    }

    tables
}

// ══════════════════════════════════════════════════════════════════════════════
// CS-04: Cross-Category BP Analysis
// ══════════════════════════════════════════════════════════════════════════════

/// Analyze cross-category binding power usage from WPDS Push rules.
///
/// Returns `(caller_cat, callee_cat) → [min_bp_values]`. When different callers
/// use different min_bp values, CS-04 can thread caller-specific BP through
/// cross-category dispatch instead of hardcoded 0.
///
/// Current implementation records structural information; actual BP values
/// require integration with the binding power table.
pub fn analyze_cross_category_bp<W: Semiring>(
    wpds: &Wpds<W>,
) -> HashMap<(String, String), Vec<u8>> {
    let mut bp_map: HashMap<(String, String), Vec<u8>> = HashMap::new();

    for rule in &wpds.rules {
        if let WpdsRule::Push {
            from_gamma,
            to_gamma_top,
            ..
        } = rule
        {
            let caller = &from_gamma.category;
            let callee = &to_gamma_top.category;
            if !caller.is_empty() && !callee.is_empty() && caller != callee {
                // Record call position as a proxy for BP context
                // Position 0 = prefix context (min_bp typically 0)
                // Position > 0 = could be infix context (min_bp > 0)
                let bp_hint = if from_gamma.position == 0 { 0u8 } else { 1u8 };
                bp_map
                    .entry((caller.clone(), callee.clone()))
                    .or_default()
                    .push(bp_hint);
            }
        }
    }

    // Deduplicate BP values per edge
    for values in bp_map.values_mut() {
        values.sort_unstable();
        values.dedup();
    }

    bp_map
}

// ══════════════════════════════════════════════════════════════════════════════
// CS-05: Context-Aware Ambiguity Resolution
// ══════════════════════════════════════════════════════════════════════════════

/// Determine per-category context ambiguity status.
///
/// A category is "context-unambiguous" if it has exactly one calling context
/// and the WPDS shows it is fully determined in that context. For such
/// categories, NFA try-all can commit to the first success.
pub fn analyze_context_ambiguity(
    calling_contexts: &HashMap<String, Vec<CallingContext>>,
    reachable_categories: &HashSet<String>,
) -> HashMap<String, bool> {
    let mut result = HashMap::new();

    for cat in reachable_categories {
        let context_count = calling_contexts
            .get(cat)
            .map(|c| {
                // Count unique caller categories
                let unique_callers: HashSet<&str> = c.iter().map(|x| x.caller_category.as_str()).collect();
                unique_callers.len()
            })
            .unwrap_or(0);

        // A category is unambiguous if it has 0 or 1 calling context
        // (0 = top-level only, 1 = called from exactly one category)
        result.insert(cat.clone(), context_count <= 1);
    }

    result
}

/// A rule determined unreachable by WPDS stack-aware analysis.
#[derive(Debug, Clone)]
pub struct WpdsUnreachableRule {
    /// Rule label.
    pub rule_label: String,
    /// Category.
    pub category: String,
    /// Witness: which calling contexts are missing.
    pub missing_contexts: Vec<String>,
    /// D15: Witness trace — shortest hypothetical Push chain that would make this
    /// rule reachable. Computed via BFS on the call graph (G33).
    pub witness_trace: Vec<String>,
}

impl fmt::Display for WpdsUnreachableRule {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "rule `{}` in `{}` is WPDS-unreachable",
            self.rule_label, self.category
        )?;
        if !self.missing_contexts.is_empty() {
            write!(f, " (missing callers: {})", self.missing_contexts.join(", "))?;
        }
        Ok(())
    }
}

/// Minimal category info for WPDS construction from pipeline bundles.
pub struct WpdsCategoryInfo {
    pub name: String,
    pub is_primary: bool,
}

/// Run full WPDS analysis from pipeline bundle data.
///
/// This entry point is used by `pipeline.rs` where the full `LanguageSpec`
/// is not available — only the extracted `ParserBundle` data.
pub fn analyze_wpds_from_bundle(
    grammar_name: &str,
    categories: &[WpdsCategoryInfo],
    all_syntax: &[(String, String, Vec<SyntaxItemSpec>)],
    prediction_wfsts: &HashMap<String, PredictionWfst>,
) -> WpdsAnalysis {
    // Reconstruct a minimal LanguageSpec for the WPDS builder
    let types: Vec<crate::CategorySpec> = categories
        .iter()
        .map(|c| crate::CategorySpec {
            name: c.name.clone(),
            native_type: None,
            is_primary: c.is_primary,
        })
        .collect();

    // Reconstruct RuleSpecInputs from all_syntax
    let inputs: Vec<crate::RuleSpecInput> = all_syntax
        .iter()
        .map(|(label, category, syntax)| crate::RuleSpecInput {
            label: label.clone(),
            category: category.clone(),
            syntax: syntax.clone(),
            associativity: crate::binding_power::Associativity::Left,
            prefix_precedence: None,
            has_rust_code: false,
            rust_code: None,
            eval_mode: None,
            source_location: None,
        })
        .collect();

    let spec = LanguageSpec::new(grammar_name.to_string(), types, inputs);
    analyze_wpds(&spec, prediction_wfsts)
}

/// Run full WPDS analysis on a grammar.
///
/// Builds the WPDS, runs poststar with `BooleanWeight` for reachability,
/// and optionally runs with `TropicalWeight` for weight extraction.
pub fn analyze_wpds(
    spec: &LanguageSpec,
    prediction_wfsts: &HashMap<String, PredictionWfst>,
) -> WpdsAnalysis {
    // Build WPDS with BooleanWeight for reachability
    let bool_wpds = build_wpds(spec, prediction_wfsts, |_| BooleanWeight::one());

    // Run poststar
    let post = poststar(&bool_wpds);

    // Determine reachable categories: a category is reachable if its entry symbol
    // appears in any configuration reachable from the start (not just as a single-element stack)
    let mut reachable_categories = HashSet::new();
    for cat in &spec.types {
        let sym = StackSymbol::category_entry(&cat.name);
        if post.is_symbol_reachable(&sym) {
            reachable_categories.insert(cat.name.clone());
        }
    }

    // Also check reachability from all reachable symbols (rule positions referencing categories)
    for (sym, w) in post.reachable_symbols() {
        if !w.is_zero() && !sym.category.is_empty() {
            reachable_categories.insert(sym.category.clone());
        }
    }

    // The initial category is always reachable
    if let Some(primary) = spec.types.iter().find(|t| t.is_primary) {
        reachable_categories.insert(primary.name.clone());
    }

    // G33: Extract call graph from the WPDS
    let call_graph = extract_call_graph(&bool_wpds);

    // G34: Compute recursion depth bounds
    let primary_cat = spec
        .types
        .iter()
        .find(|t| t.is_primary)
        .map(|t| t.name.as_str())
        .unwrap_or("");
    let depth_bounds = compute_depth_bounds(&call_graph, primary_cat);

    // G35: Classify cycles
    let cycles = classify_cycles(&call_graph, &bool_wpds);

    // G36: Compute calling contexts
    let calling_contexts = compute_calling_contexts(&bool_wpds);

    // Find unreachable rules
    let mut unreachable_rules = Vec::new();
    for rule in &spec.rules {
        let rule_entry = StackSymbol::rule_position(&rule.category, &rule.label, 0);
        let rule_weight = post.symbol_weight(&rule_entry);

        if rule_weight.is_zero() && !reachable_categories.contains(&rule.category) {
            // Find which calling contexts are missing
            let missing = find_missing_callers(spec, &rule.category, &reachable_categories);
            // D15: Compute witness trace via shortest path in call graph
            let witness_trace =
                shortest_path_witness(&call_graph, &reachable_categories, &rule.category);
            unreachable_rules.push(WpdsUnreachableRule {
                rule_label: rule.label.clone(),
                category: rule.category.clone(),
                missing_contexts: missing,
                witness_trace,
            });
        }
    }

    // Build TropicalWeight WPDS for weight extraction
    let trop_wpds = build_wpds(spec, prediction_wfsts, TropicalWeight::new);
    let trop_post = poststar(&trop_wpds);

    let mut category_weights = HashMap::new();
    for cat in &spec.types {
        let sym = StackSymbol::category_entry(&cat.name);
        let w = trop_post.symbol_weight(&sym);
        if !w.is_zero() {
            category_weights.insert(cat.name.clone(), w.value());
        }
    }

    // CS-01: Build context-sensitive rule tables
    let all_rules: Vec<(String, String)> = spec
        .rules
        .iter()
        .map(|r| (r.label.clone(), r.category.clone()))
        .collect();
    let context_rule_tables =
        build_context_rule_tables(&calling_contexts, &reachable_categories, &all_rules);

    // CS-04: Analyze cross-category binding power interactions
    let cross_category_bp = analyze_cross_category_bp(&bool_wpds);

    // CS-05: Analyze per-category context ambiguity
    let context_unambiguous =
        analyze_context_ambiguity(&calling_contexts, &reachable_categories);

    WpdsAnalysis {
        grammar_name: spec.name.clone(),
        num_symbols: bool_wpds.num_symbols(),
        num_rules: bool_wpds.num_rules(),
        reachable_categories,
        unreachable_rules,
        category_weights,
        call_graph,
        depth_bounds,
        cycles,
        calling_contexts,
        context_rule_tables,
        cross_category_bp,
        context_unambiguous,
    }
}

/// Find which categories could call the given category but don't.
fn find_missing_callers(
    spec: &LanguageSpec,
    target_cat: &str,
    reachable: &HashSet<String>,
) -> Vec<String> {
    let mut callers = HashSet::new();
    let mut actual_callers = HashSet::new();

    // Find all categories that reference target_cat in their syntax
    for rule in &spec.rules {
        for item in &rule.syntax {
            if references_category(item, target_cat) {
                callers.insert(rule.category.clone());
                if reachable.contains(&rule.category) {
                    actual_callers.insert(rule.category.clone());
                }
            }
        }
    }

    // Missing callers are those in `callers` but not in `actual_callers`
    callers
        .difference(&actual_callers)
        .cloned()
        .collect()
}

/// Check if a syntax item references a given category.
fn references_category(item: &SyntaxItemSpec, target: &str) -> bool {
    match item {
        SyntaxItemSpec::NonTerminal { category, .. } => category == target,
        SyntaxItemSpec::Binder { category, .. } => category == target,
        SyntaxItemSpec::Collection { element_category, .. } => element_category == target,
        SyntaxItemSpec::Sep { body, .. } => references_category(body, target),
        SyntaxItemSpec::Map { body_items } => body_items.iter().any(|i| references_category(i, target)),
        SyntaxItemSpec::Zip { left_category, right_category, body, .. } => {
            left_category == target || right_category == target || references_category(body, target)
        }
        SyntaxItemSpec::Optional { inner } => inner.iter().any(|i| references_category(i, target)),
        _ => false,
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Tests
// ══════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;
    use crate::automata::semiring::{BooleanWeight, CountingWeight, TropicalWeight};
    use crate::binding_power::Associativity;
    use crate::{CategorySpec, LanguageSpec, RuleSpecInput, SyntaxItemSpec};

    /// Build a minimal calculator grammar: Expr = Int | Expr "+" Expr
    fn calculator_spec() -> LanguageSpec {
        let types = vec![CategorySpec {
            name: "Expr".to_string(),
            native_type: Some("i64".to_string()),
            is_primary: true,
        }];

        let inputs = vec![
            RuleSpecInput {
                label: "Num".to_string(),
                category: "Expr".to_string(),
                syntax: vec![SyntaxItemSpec::Terminal("INTEGER".to_string())],
                associativity: Associativity::Left,
                prefix_precedence: None,
                has_rust_code: false,
                rust_code: None,
                eval_mode: None,
                source_location: None,
            },
            RuleSpecInput {
                label: "Add".to_string(),
                category: "Expr".to_string(),
                syntax: vec![
                    SyntaxItemSpec::NonTerminal {
                        category: "Expr".to_string(),
                        param_name: "lhs".to_string(),
                    },
                    SyntaxItemSpec::Terminal("+".to_string()),
                    SyntaxItemSpec::NonTerminal {
                        category: "Expr".to_string(),
                        param_name: "rhs".to_string(),
                    },
                ],
                associativity: Associativity::Left,
                prefix_precedence: None,
                has_rust_code: false,
                rust_code: None,
                eval_mode: None,
                source_location: None,
            },
        ];

        LanguageSpec::new("Calculator".to_string(), types, inputs)
    }

    /// Build a two-category grammar: Expr = Num | Expr "+" Expr | "(" Type ")" Expr
    ///                                Type = "int" | "float"
    fn typed_grammar_spec() -> LanguageSpec {
        let types = vec![
            CategorySpec {
                name: "Expr".to_string(),
                native_type: None,
                is_primary: true,
            },
            CategorySpec {
                name: "Type".to_string(),
                native_type: None,
                is_primary: false,
            },
        ];

        let inputs = vec![
            RuleSpecInput {
                label: "Num".to_string(),
                category: "Expr".to_string(),
                syntax: vec![SyntaxItemSpec::Terminal("INTEGER".to_string())],
                associativity: Associativity::Left,
                prefix_precedence: None,
                has_rust_code: false,
                rust_code: None,
                eval_mode: None,
                source_location: None,
            },
            RuleSpecInput {
                label: "Add".to_string(),
                category: "Expr".to_string(),
                syntax: vec![
                    SyntaxItemSpec::NonTerminal {
                        category: "Expr".to_string(),
                        param_name: "lhs".to_string(),
                    },
                    SyntaxItemSpec::Terminal("+".to_string()),
                    SyntaxItemSpec::NonTerminal {
                        category: "Expr".to_string(),
                        param_name: "rhs".to_string(),
                    },
                ],
                associativity: Associativity::Left,
                prefix_precedence: None,
                has_rust_code: false,
                rust_code: None,
                eval_mode: None,
                source_location: None,
            },
            RuleSpecInput {
                label: "Cast".to_string(),
                category: "Expr".to_string(),
                syntax: vec![
                    SyntaxItemSpec::Terminal("(".to_string()),
                    SyntaxItemSpec::NonTerminal {
                        category: "Type".to_string(),
                        param_name: "ty".to_string(),
                    },
                    SyntaxItemSpec::Terminal(")".to_string()),
                    SyntaxItemSpec::NonTerminal {
                        category: "Expr".to_string(),
                        param_name: "expr".to_string(),
                    },
                ],
                associativity: Associativity::Left,
                prefix_precedence: None,
                has_rust_code: false,
                rust_code: None,
                eval_mode: None,
                source_location: None,
            },
            RuleSpecInput {
                label: "IntType".to_string(),
                category: "Type".to_string(),
                syntax: vec![SyntaxItemSpec::Terminal("int".to_string())],
                associativity: Associativity::Left,
                prefix_precedence: None,
                has_rust_code: false,
                rust_code: None,
                eval_mode: None,
                source_location: None,
            },
            RuleSpecInput {
                label: "FloatType".to_string(),
                category: "Type".to_string(),
                syntax: vec![SyntaxItemSpec::Terminal("float".to_string())],
                associativity: Associativity::Left,
                prefix_precedence: None,
                has_rust_code: false,
                rust_code: None,
                eval_mode: None,
                source_location: None,
            },
        ];

        LanguageSpec::new("TypedCalc".to_string(), types, inputs)
    }

    /// Build a grammar with an unreachable category: Expr has rules, Orphan has rules
    /// but nothing references Orphan.
    fn orphan_grammar_spec() -> LanguageSpec {
        let types = vec![
            CategorySpec {
                name: "Expr".to_string(),
                native_type: Some("i64".to_string()),
                is_primary: true,
            },
            CategorySpec {
                name: "Orphan".to_string(),
                native_type: None,
                is_primary: false,
            },
        ];

        let inputs = vec![
            RuleSpecInput {
                label: "Num".to_string(),
                category: "Expr".to_string(),
                syntax: vec![SyntaxItemSpec::Terminal("INTEGER".to_string())],
                associativity: Associativity::Left,
                prefix_precedence: None,
                has_rust_code: false,
                rust_code: None,
                eval_mode: None,
                source_location: None,
            },
            RuleSpecInput {
                label: "OrphanRule".to_string(),
                category: "Orphan".to_string(),
                syntax: vec![SyntaxItemSpec::Terminal("orphan".to_string())],
                associativity: Associativity::Left,
                prefix_precedence: None,
                has_rust_code: false,
                rust_code: None,
                eval_mode: None,
                source_location: None,
            },
        ];

        LanguageSpec::new("OrphanGrammar".to_string(), types, inputs)
    }

    // ── Phase 1: WPDS construction ──

    #[test]
    fn test_build_wpds_calculator() {
        let spec = calculator_spec();
        let wfsts = HashMap::new();
        let wpds: Wpds<BooleanWeight> = build_wpds(&spec, &wfsts, |_| BooleanWeight::one());

        // Should have stack symbols for: Expr entry, Num@0, Num@1, Add@0, Add@1, Add@2, Add@3
        assert!(
            wpds.num_symbols() >= 4,
            "calculator WPDS should have at least 4 symbols, got {}",
            wpds.num_symbols()
        );

        // Should have rules: dispatch + intraprocedural + pop
        assert!(
            wpds.num_rules() >= 4,
            "calculator WPDS should have at least 4 rules, got {}",
            wpds.num_rules()
        );

        // Initial symbol should be Expr entry
        assert_eq!(wpds.initial_symbol.category, "Expr");
        assert!(wpds.initial_symbol.rule_label.is_empty());
    }

    #[test]
    fn test_build_wpds_cross_category() {
        let spec = typed_grammar_spec();
        let wfsts = HashMap::new();
        let wpds: Wpds<BooleanWeight> = build_wpds(&spec, &wfsts, |_| BooleanWeight::one());

        // Should have push rules for Expr→Type cross-category call
        let push_count = wpds
            .rules
            .iter()
            .filter(|r| matches!(r, WpdsRule::Push { .. }))
            .count();

        assert!(
            push_count >= 1,
            "typed grammar should have at least 1 push rule for cross-category call, got {}",
            push_count
        );

        // Should have both Expr and Type category entries
        assert!(
            wpds.symbol_index.contains_key(&StackSymbol::category_entry("Expr")),
            "should have Expr entry symbol"
        );
        assert!(
            wpds.symbol_index.contains_key(&StackSymbol::category_entry("Type")),
            "should have Type entry symbol"
        );
    }

    #[test]
    fn test_build_wpds_orphan_category() {
        let spec = orphan_grammar_spec();
        let wfsts = HashMap::new();
        let wpds: Wpds<BooleanWeight> = build_wpds(&spec, &wfsts, |_| BooleanWeight::one());

        // Orphan category should have rules but no cross-category calls TO it
        let push_to_orphan = wpds
            .rules
            .iter()
            .filter(|r| match r {
                WpdsRule::Push { to_gamma_top, .. } => to_gamma_top.category == "Orphan",
                _ => false,
            })
            .count();

        assert_eq!(
            push_to_orphan, 0,
            "no rule should push to Orphan category"
        );
    }

    // ── Phase 2: poststar reachability ──

    #[test]
    fn test_poststar_calculator_reachability() {
        let spec = calculator_spec();
        let wfsts = HashMap::new();
        let wpds: Wpds<BooleanWeight> = build_wpds(&spec, &wfsts, |_| BooleanWeight::one());

        let post = poststar(&wpds);

        // Expr entry should be reachable (it's the initial symbol)
        let expr_sym = StackSymbol::category_entry("Expr");
        assert!(
            !post.symbol_weight(&expr_sym).is_zero(),
            "Expr entry should be reachable via poststar"
        );
    }

    #[test]
    fn test_poststar_cross_category_reachability() {
        let spec = typed_grammar_spec();
        let wfsts = HashMap::new();
        let wpds: Wpds<BooleanWeight> = build_wpds(&spec, &wfsts, |_| BooleanWeight::one());

        let post = poststar(&wpds);

        // Both Expr and Type should be reachable
        let expr_sym = StackSymbol::category_entry("Expr");
        let type_sym = StackSymbol::category_entry("Type");

        assert!(
            !post.symbol_weight(&expr_sym).is_zero(),
            "Expr should be reachable"
        );
        assert!(
            !post.symbol_weight(&type_sym).is_zero(),
            "Type should be reachable (called by Cast rule in Expr)"
        );
    }

    #[test]
    fn test_poststar_orphan_unreachable() {
        let spec = orphan_grammar_spec();
        let wfsts = HashMap::new();
        let wpds: Wpds<BooleanWeight> = build_wpds(&spec, &wfsts, |_| BooleanWeight::one());

        let post = poststar(&wpds);

        // Expr should be reachable
        let expr_sym = StackSymbol::category_entry("Expr");
        assert!(
            !post.symbol_weight(&expr_sym).is_zero(),
            "Expr should be reachable"
        );

        // Orphan should NOT be reachable (no rule calls it)
        let orphan_sym = StackSymbol::category_entry("Orphan");
        assert!(
            post.symbol_weight(&orphan_sym).is_zero(),
            "Orphan should be unreachable via poststar"
        );
    }

    #[test]
    fn test_poststar_tropical_weights() {
        let spec = calculator_spec();
        let wfsts = HashMap::new();
        let wpds: Wpds<TropicalWeight> = build_wpds(&spec, &wfsts, TropicalWeight::new);

        let post = poststar(&wpds);

        // Expr should have finite weight
        let expr_sym = StackSymbol::category_entry("Expr");
        let w = post.symbol_weight(&expr_sym);
        assert!(
            !w.is_zero(),
            "Expr should have non-zero tropical weight"
        );
    }

    #[test]
    fn test_poststar_counting_weight() {
        let spec = calculator_spec();
        let wfsts = HashMap::new();
        let wpds: Wpds<CountingWeight> = build_wpds(&spec, &wfsts, |_| CountingWeight::one());

        let post = poststar(&wpds);

        // Expr should have counting weight >= 1 (at least one derivation path)
        let expr_sym = StackSymbol::category_entry("Expr");
        let w = post.symbol_weight(&expr_sym);
        assert!(
            !w.is_zero(),
            "Expr should have non-zero counting weight, got {:?}",
            w
        );
    }

    // ── Phase 3: Stringsum ──

    #[test]
    fn test_stringsum_single_token() {
        let spec = calculator_spec();
        let wfsts = HashMap::new();
        let wpds: Wpds<CountingWeight> = build_wpds(&spec, &wfsts, |_| CountingWeight::one());
        let post = poststar(&wpds);

        let input = StringsumInput {
            tokens: vec!["42".to_string()],
        };

        let result = stringsum(&wpds, &post, &input, &spec);

        // A single integer should match at least the Num rule
        // (the actual matching depends on whether "42" matches INTEGER pattern)
        assert_eq!(result.position_weights.len(), 1);
    }

    // ── Phase 4: Full analysis ──

    #[test]
    fn test_analyze_wpds_calculator() {
        let spec = calculator_spec();
        let wfsts = HashMap::new();

        let analysis = analyze_wpds(&spec, &wfsts);

        assert_eq!(analysis.grammar_name, "Calculator");
        assert!(
            analysis.reachable_categories.contains("Expr"),
            "Expr should be reachable"
        );
        assert!(
            analysis.unreachable_rules.is_empty(),
            "calculator should have no unreachable rules: {:?}",
            analysis.unreachable_rules
        );
    }

    #[test]
    fn test_analyze_wpds_orphan_detection() {
        let spec = orphan_grammar_spec();
        let wfsts = HashMap::new();

        let analysis = analyze_wpds(&spec, &wfsts);

        assert!(
            analysis.reachable_categories.contains("Expr"),
            "Expr should be reachable"
        );
        // Orphan category should not be reachable
        assert!(
            !analysis.reachable_categories.contains("Orphan"),
            "Orphan should not be reachable"
        );
        // The Orphan rule should be flagged as unreachable
        assert!(
            analysis
                .unreachable_rules
                .iter()
                .any(|r| r.rule_label == "OrphanRule"),
            "OrphanRule should be WPDS-unreachable: {:?}",
            analysis.unreachable_rules
        );
    }

    #[test]
    fn test_analyze_wpds_typed_grammar() {
        let spec = typed_grammar_spec();
        let wfsts = HashMap::new();

        let analysis = analyze_wpds(&spec, &wfsts);

        assert!(
            analysis.reachable_categories.contains("Expr"),
            "Expr should be reachable"
        );
        assert!(
            analysis.reachable_categories.contains("Type"),
            "Type should be reachable (called from Cast rule)"
        );
        assert!(
            analysis.unreachable_rules.is_empty(),
            "typed grammar should have no unreachable rules: {:?}",
            analysis.unreachable_rules
        );
    }

    // ── Stack symbol tests ──

    #[test]
    fn test_stack_symbol_display() {
        let entry = StackSymbol::category_entry("Expr");
        assert_eq!(format!("{}", entry), "⟨Expr⟩");

        let pos = StackSymbol::rule_position("Expr", "Add", 2);
        assert_eq!(format!("{}", pos), "⟨Expr.Add@2⟩");
    }

    #[test]
    fn test_stack_symbol_equality() {
        let a = StackSymbol::category_entry("Expr");
        let b = StackSymbol::category_entry("Expr");
        let c = StackSymbol::category_entry("Type");

        assert_eq!(a, b);
        assert_ne!(a, c);
    }

    // ── WPDS rule display ──

    #[test]
    fn test_wpds_rule_display() {
        let pop: WpdsRule<BooleanWeight> = WpdsRule::Pop {
            from_gamma: StackSymbol::category_entry("Expr"),
            weight: BooleanWeight::one(),
        };
        let display = format!("{}", pop);
        assert!(display.contains("⟨Expr⟩"), "display should contain symbol: {}", display);
        assert!(display.contains("ε"), "pop should show epsilon: {}", display);
    }

    // ── P-automaton tests ──

    #[test]
    fn test_p_automaton_basic() {
        let mut pa = PAutomaton::<BooleanWeight>::new(0);
        let q1 = pa.add_state();
        pa.mark_final(q1);

        let sym = StackSymbol::category_entry("Expr");
        pa.add_transition(0, sym.clone(), q1, BooleanWeight::one());

        assert!(pa.is_symbol_accepted(&sym));
        assert!(!pa.symbol_weight(&sym).is_zero());
    }

    #[test]
    fn test_p_automaton_no_accept() {
        let pa = PAutomaton::<BooleanWeight>::new(0);
        let sym = StackSymbol::category_entry("Expr");
        assert!(!pa.is_symbol_accepted(&sym));
        assert!(pa.symbol_weight(&sym).is_zero());
    }

    // ── G33: Call graph extraction ──

    #[test]
    fn test_call_graph_calculator_empty() {
        // Calculator has only one category (Expr) — no cross-category calls
        let spec = calculator_spec();
        let wfsts = HashMap::new();
        let wpds: Wpds<BooleanWeight> = build_wpds(&spec, &wfsts, |_| BooleanWeight::one());
        let cg = extract_call_graph(&wpds);

        assert!(
            cg.edges.is_empty(),
            "calculator should have no cross-category call edges, got {:?}",
            cg.edges.iter().map(|e| format!("{}→{}", e.caller_cat, e.callee_cat)).collect::<Vec<_>>()
        );
        assert!(
            cg.categories.contains("Expr"),
            "Expr should be in the call graph categories"
        );
    }

    #[test]
    fn test_call_graph_cross_category() {
        // Expr → Type via Cast rule
        let spec = typed_grammar_spec();
        let wfsts = HashMap::new();
        let wpds: Wpds<BooleanWeight> = build_wpds(&spec, &wfsts, |_| BooleanWeight::one());
        let cg = extract_call_graph(&wpds);

        assert!(
            !cg.edges.is_empty(),
            "typed grammar should have cross-category call edges"
        );
        let expr_to_type = cg
            .edges
            .iter()
            .find(|e| e.caller_cat == "Expr" && e.callee_cat == "Type");
        assert!(
            expr_to_type.is_some(),
            "should have Expr→Type edge, got: {:?}",
            cg.edges.iter().map(|e| format!("{}→{}", e.caller_cat, e.callee_cat)).collect::<Vec<_>>()
        );
        assert!(
            expr_to_type.expect("just checked").call_sites >= 1,
            "Expr→Type should have at least 1 call site"
        );
        assert_eq!(
            *cg.fan_out.get("Expr").unwrap_or(&0),
            1,
            "Expr fan-out should be 1 (calls only Type)"
        );
        assert_eq!(
            *cg.fan_in.get("Type").unwrap_or(&0),
            1,
            "Type fan-in should be 1 (called only by Expr)"
        );
    }

    #[test]
    fn test_call_graph_orphan_disconnected() {
        // Orphan category has no incoming or outgoing cross-category edges from Expr
        let spec = orphan_grammar_spec();
        let wfsts = HashMap::new();
        let wpds: Wpds<BooleanWeight> = build_wpds(&spec, &wfsts, |_| BooleanWeight::one());
        let cg = extract_call_graph(&wpds);

        let orphan_edges: Vec<_> = cg
            .edges
            .iter()
            .filter(|e| e.caller_cat == "Orphan" || e.callee_cat == "Orphan")
            .collect();
        assert!(
            orphan_edges.is_empty(),
            "Orphan should have no call edges, got {:?}",
            orphan_edges.iter().map(|e| format!("{}→{}", e.caller_cat, e.callee_cat)).collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_call_graph_sccs() {
        let spec = typed_grammar_spec();
        let wfsts = HashMap::new();
        let wpds: Wpds<BooleanWeight> = build_wpds(&spec, &wfsts, |_| BooleanWeight::one());
        let cg = extract_call_graph(&wpds);

        // Expr→Type is a DAG edge (no cycle), so each SCC should be a singleton
        for scc in &cg.sccs {
            assert_eq!(
                scc.len(),
                1,
                "typed grammar has no cycles — each SCC should be a singleton, got {:?}",
                scc
            );
        }
    }

    // ── D15: Witness traces for dead rules ──

    #[test]
    fn test_witness_trace_orphan() {
        let spec = orphan_grammar_spec();
        let wfsts = HashMap::new();
        let analysis = analyze_wpds(&spec, &wfsts);

        let orphan_rule = analysis
            .unreachable_rules
            .iter()
            .find(|r| r.rule_label == "OrphanRule")
            .expect("OrphanRule should be unreachable");

        assert!(
            !orphan_rule.witness_trace.is_empty(),
            "witness trace for OrphanRule should not be empty"
        );
    }

    #[test]
    fn test_analyze_wpds_call_graph_populated() {
        let spec = typed_grammar_spec();
        let wfsts = HashMap::new();
        let analysis = analyze_wpds(&spec, &wfsts);

        assert!(
            !analysis.call_graph.edges.is_empty(),
            "WpdsAnalysis should include a populated call graph for cross-category grammars"
        );
        assert!(
            analysis.call_graph.categories.contains("Expr"),
            "call graph should include Expr"
        );
        assert!(
            analysis.call_graph.categories.contains("Type"),
            "call graph should include Type"
        );
    }

    // ── G34: Recursion depth bounds ──

    #[test]
    fn test_depth_bounds_single_category() {
        let spec = calculator_spec();
        let wfsts = HashMap::new();
        let analysis = analyze_wpds(&spec, &wfsts);

        let expr_bounds = analysis.depth_bounds.get("Expr")
            .expect("Expr should have depth bounds");
        assert_eq!(expr_bounds.min_depth, 0, "primary category should have min_depth=0");
    }

    #[test]
    fn test_depth_bounds_cross_category() {
        let spec = typed_grammar_spec();
        let wfsts = HashMap::new();
        let analysis = analyze_wpds(&spec, &wfsts);

        let expr_bounds = analysis.depth_bounds.get("Expr")
            .expect("Expr should have depth bounds");
        assert_eq!(expr_bounds.min_depth, 0, "primary Expr should have min_depth=0");

        let type_bounds = analysis.depth_bounds.get("Type")
            .expect("Type should have depth bounds");
        assert_eq!(type_bounds.min_depth, 1, "Type called from Expr should have min_depth=1");
        assert!(!type_bounds.is_recursive, "Type should not be recursive");
    }

    #[test]
    fn test_depth_bounds_orphan() {
        let spec = orphan_grammar_spec();
        let wfsts = HashMap::new();
        let analysis = analyze_wpds(&spec, &wfsts);

        // Orphan has no incoming edges, so it should have max_depth = None (unreachable)
        if let Some(orphan_bounds) = analysis.depth_bounds.get("Orphan") {
            assert!(orphan_bounds.max_depth.is_none(),
                "Orphan should have unbounded max_depth (unreachable)");
        }
    }

    // ── G35: Cycle classification ──

    #[test]
    fn test_cycle_classification_no_cycles() {
        let spec = typed_grammar_spec();
        let wfsts = HashMap::new();
        let analysis = analyze_wpds(&spec, &wfsts);

        assert!(
            analysis.cycles.is_empty(),
            "typed grammar (Expr→Type DAG) should have no cycles, got {:?}",
            analysis.cycles.iter().map(|c| format!("{:?}: {:?}", c.kind, c.categories)).collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_cycle_classification_calculator() {
        // Calculator has only Expr — no cross-category call graph cycles
        let spec = calculator_spec();
        let wfsts = HashMap::new();
        let analysis = analyze_wpds(&spec, &wfsts);

        assert!(
            analysis.cycles.is_empty(),
            "calculator should have no cross-category cycles"
        );
    }

    /// Build a mutual-recursion grammar: Expr → "x" | Decl "in" Expr; Decl → "let" Expr
    fn mutual_recursion_spec() -> LanguageSpec {
        let types = vec![
            CategorySpec {
                name: "Expr".to_string(),
                native_type: None,
                is_primary: true,
            },
            CategorySpec {
                name: "Decl".to_string(),
                native_type: None,
                is_primary: false,
            },
        ];

        let inputs = vec![
            RuleSpecInput {
                label: "Var".to_string(),
                category: "Expr".to_string(),
                syntax: vec![SyntaxItemSpec::Terminal("x".to_string())],
                associativity: Associativity::Left,
                prefix_precedence: None,
                has_rust_code: false,
                rust_code: None,
                eval_mode: None,
                source_location: None,
            },
            RuleSpecInput {
                label: "LetIn".to_string(),
                category: "Expr".to_string(),
                syntax: vec![
                    SyntaxItemSpec::NonTerminal {
                        category: "Decl".to_string(),
                        param_name: "decl".to_string(),
                    },
                    SyntaxItemSpec::Terminal("in".to_string()),
                    SyntaxItemSpec::NonTerminal {
                        category: "Expr".to_string(),
                        param_name: "body".to_string(),
                    },
                ],
                associativity: Associativity::Left,
                prefix_precedence: None,
                has_rust_code: false,
                rust_code: None,
                eval_mode: None,
                source_location: None,
            },
            RuleSpecInput {
                label: "LetDecl".to_string(),
                category: "Decl".to_string(),
                syntax: vec![
                    SyntaxItemSpec::Terminal("let".to_string()),
                    SyntaxItemSpec::NonTerminal {
                        category: "Expr".to_string(),
                        param_name: "init".to_string(),
                    },
                ],
                associativity: Associativity::Left,
                prefix_precedence: None,
                has_rust_code: false,
                rust_code: None,
                eval_mode: None,
                source_location: None,
            },
        ];

        LanguageSpec::new("MutualRecursion".to_string(), types, inputs)
    }

    #[test]
    fn test_cycle_classification_mutual_recursion() {
        let spec = mutual_recursion_spec();
        let wfsts = HashMap::new();
        let analysis = analyze_wpds(&spec, &wfsts);

        // Expr→Decl and Decl→Expr form a mutual recursion cycle
        assert!(
            !analysis.cycles.is_empty(),
            "mutual recursion grammar should have at least one cycle"
        );
        let mutual_cycle = analysis.cycles.iter()
            .find(|c| c.kind == CycleKind::Mutual);
        assert!(
            mutual_cycle.is_some(),
            "should have a Mutual cycle, got: {:?}",
            analysis.cycles
        );
        let cycle = mutual_cycle.expect("just checked");
        assert!(
            cycle.categories.contains(&"Expr".to_string()) && cycle.categories.contains(&"Decl".to_string()),
            "mutual cycle should contain both Expr and Decl, got {:?}",
            cycle.categories
        );
    }

    // ── G36: Calling contexts ──

    #[test]
    fn test_calling_contexts_calculator() {
        let spec = calculator_spec();
        let wfsts = HashMap::new();
        let analysis = analyze_wpds(&spec, &wfsts);

        // No cross-category calls → no calling contexts
        assert!(
            analysis.calling_contexts.is_empty(),
            "calculator should have no calling contexts"
        );
    }

    #[test]
    fn test_calling_contexts_typed_grammar() {
        let spec = typed_grammar_spec();
        let wfsts = HashMap::new();
        let analysis = analyze_wpds(&spec, &wfsts);

        // Type is called from Expr.Cast
        let type_contexts = analysis.calling_contexts.get("Type");
        assert!(
            type_contexts.is_some(),
            "Type should have calling contexts"
        );
        let contexts = type_contexts.expect("just checked");
        assert!(
            !contexts.is_empty(),
            "Type should have at least one caller"
        );
        assert!(
            contexts.iter().any(|c| c.caller_category == "Expr"),
            "Type should be called from Expr"
        );
    }

    #[test]
    fn test_calling_contexts_mutual_recursion() {
        let spec = mutual_recursion_spec();
        let wfsts = HashMap::new();
        let analysis = analyze_wpds(&spec, &wfsts);

        // Both Expr and Decl should have callers
        assert!(
            analysis.calling_contexts.get("Decl").is_some(),
            "Decl should have calling contexts (called from Expr)"
        );
        assert!(
            analysis.calling_contexts.get("Expr").is_some(),
            "Expr should have calling contexts (called from Decl)"
        );
    }

    // ── G34 + G35 combined: depth and recursion for mutual recursion ──

    #[test]
    fn test_depth_bounds_mutual_recursion() {
        let spec = mutual_recursion_spec();
        let wfsts = HashMap::new();
        let analysis = analyze_wpds(&spec, &wfsts);

        let expr_bounds = analysis.depth_bounds.get("Expr")
            .expect("Expr should have depth bounds");
        assert!(expr_bounds.is_recursive,
            "Expr in mutual recursion should be recursive");
        assert!(expr_bounds.max_depth.is_none(),
            "recursive Expr should have unbounded max_depth");

        let decl_bounds = analysis.depth_bounds.get("Decl")
            .expect("Decl should have depth bounds");
        assert!(decl_bounds.is_recursive,
            "Decl in mutual recursion should be recursive");
    }

    // ── CS-01: Context-sensitive rule tables ──

    #[test]
    fn test_context_rule_table_typed_grammar() {
        let spec = typed_grammar_spec();
        let wfsts = HashMap::new();
        let analysis = analyze_wpds(&spec, &wfsts);

        // Type is called from Expr, so it should have a context rule table
        let type_table = analysis.context_rule_tables.get("Type");
        assert!(
            type_table.is_some(),
            "Type should have a context rule table (called from Expr)"
        );
        let table = type_table.expect("just checked");
        assert!(
            !table.entries.is_empty(),
            "Type context rule table should have entries"
        );
        // Should have entries for "Expr" (caller) and "top-level"
        assert!(
            table.entries.iter().any(|e| e.context_tag == "Expr"),
            "Type table should have an Expr calling context entry"
        );
        assert!(
            table.entries.iter().any(|e| e.context_tag == "top-level"),
            "Type table should have a top-level entry"
        );
    }

    #[test]
    fn test_context_rule_table_calculator_empty() {
        // Calculator has no cross-category calls → no context rule tables
        let spec = calculator_spec();
        let wfsts = HashMap::new();
        let analysis = analyze_wpds(&spec, &wfsts);

        assert!(
            analysis.context_rule_tables.is_empty(),
            "calculator should have no context rule tables"
        );
    }

    #[test]
    fn test_context_rule_table_mutual_recursion() {
        let spec = mutual_recursion_spec();
        let wfsts = HashMap::new();
        let analysis = analyze_wpds(&spec, &wfsts);

        // Both Expr and Decl are called from each other
        assert!(
            analysis.context_rule_tables.get("Decl").is_some(),
            "Decl should have a context rule table"
        );
        assert!(
            analysis.context_rule_tables.get("Expr").is_some(),
            "Expr should have a context rule table (called from Decl)"
        );
    }

    // ── CS-04: Cross-Category BP Modulation Tests ────────────────────────

    #[test]
    fn test_cs04_calculator_no_cross_category_bp() {
        let spec = calculator_spec();
        let wfsts = HashMap::new();
        let analysis = analyze_wpds(&spec, &wfsts);

        // Calculator has a single category — no cross-category calls
        assert!(
            analysis.cross_category_bp.is_empty(),
            "single-category grammar should have no cross-category BP entries"
        );
    }

    #[test]
    fn test_cs04_mutual_recursion_bp() {
        let spec = mutual_recursion_spec();
        let wfsts = HashMap::new();
        let analysis = analyze_wpds(&spec, &wfsts);

        // Mutual recursion grammar has Expr→Decl and Decl→Expr calls
        // At least one cross-category edge should exist
        assert!(
            !analysis.cross_category_bp.is_empty(),
            "mutual recursion grammar should have cross-category BP entries"
        );

        // Each edge should have BP hints (0 = prefix, 1 = non-prefix)
        for ((caller, callee), bp_values) in &analysis.cross_category_bp {
            assert!(
                !bp_values.is_empty(),
                "BP values for {caller}→{callee} should not be empty"
            );
            for &bp in bp_values {
                assert!(
                    bp <= 1,
                    "BP hint should be 0 (prefix) or 1 (non-prefix), got {bp}"
                );
            }
        }
    }

    #[test]
    fn test_cs04_cross_category_bp_deduplication() {
        // Verify that BP values are deduplicated per edge
        let spec = mutual_recursion_spec();
        let wfsts = HashMap::new();
        let analysis = analyze_wpds(&spec, &wfsts);

        for ((_caller, _callee), bp_values) in &analysis.cross_category_bp {
            // After dedup, no adjacent duplicates
            for window in bp_values.windows(2) {
                assert_ne!(
                    window[0], window[1],
                    "BP values should be deduplicated"
                );
            }
        }
    }

    // ── CS-05: Context-Aware Ambiguity Resolution Tests ──────────────────

    #[test]
    fn test_cs05_calculator_context_unambiguous() {
        let spec = calculator_spec();
        let wfsts = HashMap::new();
        let analysis = analyze_wpds(&spec, &wfsts);

        // Calculator's single category "Expr" has no callers (top-level only)
        // → context_count = 0 → unambiguous
        let expr_unambiguous = analysis
            .context_unambiguous
            .get("Expr")
            .copied()
            .unwrap_or(false);
        assert!(
            expr_unambiguous,
            "top-level-only category should be context-unambiguous"
        );
    }

    #[test]
    fn test_cs05_mutual_recursion_ambiguity() {
        let spec = mutual_recursion_spec();
        let wfsts = HashMap::new();
        let analysis = analyze_wpds(&spec, &wfsts);

        // In mutual recursion, each category is called from at least the other
        // Check that both are present in the map
        assert!(
            analysis.context_unambiguous.contains_key("Expr"),
            "Expr should have context ambiguity analysis"
        );
        assert!(
            analysis.context_unambiguous.contains_key("Decl"),
            "Decl should have context ambiguity analysis"
        );
    }

    #[test]
    fn test_cs05_orphan_category_unambiguous() {
        let spec = orphan_grammar_spec();
        let wfsts = HashMap::new();
        let analysis = analyze_wpds(&spec, &wfsts);

        // Orphan is unreachable so it won't be in reachable_categories.
        // Only reachable categories get context ambiguity analysis.
        // Expr (the reachable one) has no callers → context_count = 0 → unambiguous
        if let Some(&unambiguous) = analysis.context_unambiguous.get("Expr") {
            assert!(
                unambiguous,
                "top-level category with no callers should be context-unambiguous"
            );
        }

        // Orphan, if present, should also be unambiguous (no callers)
        if let Some(&unambiguous) = analysis.context_unambiguous.get("Orphan") {
            assert!(
                unambiguous,
                "orphan category with no callers should be context-unambiguous"
            );
        }
    }

    #[test]
    fn test_cs05_single_caller_unambiguous() {
        // A category called from exactly one other category should be unambiguous
        let spec = mutual_recursion_spec();
        let wfsts = HashMap::new();
        let analysis = analyze_wpds(&spec, &wfsts);

        // At least one category should have a defined ambiguity status
        assert!(
            !analysis.context_unambiguous.is_empty(),
            "context_unambiguous map should not be empty for multi-category grammar"
        );

        // Verify the invariant: categories with ≤1 unique caller are unambiguous
        for (cat, &is_unambiguous) in &analysis.context_unambiguous {
            let unique_callers = analysis
                .calling_contexts
                .get(cat)
                .map(|contexts| {
                    contexts
                        .iter()
                        .map(|c| c.caller_category.as_str())
                        .collect::<HashSet<_>>()
                        .len()
                })
                .unwrap_or(0);

            if unique_callers <= 1 {
                assert!(
                    is_unambiguous,
                    "{cat} has {unique_callers} unique callers but is marked ambiguous"
                );
            } else {
                assert!(
                    !is_unambiguous,
                    "{cat} has {unique_callers} unique callers but is marked unambiguous"
                );
            }
        }
    }
}
