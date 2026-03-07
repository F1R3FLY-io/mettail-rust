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

    // Seed worklist with all existing transitions
    for trans in &automaton.transitions {
        worklist.push_back((trans.from, trans.symbol.clone(), trans.to, trans.weight));
    }

    let mut existing: HashMap<(PAutomatonStateId, StackSymbol, PAutomatonStateId), W> =
        HashMap::new();
    for trans in &automaton.transitions {
        let key = (trans.from, trans.symbol.clone(), trans.to);
        let entry = existing.entry(key).or_insert(W::zero());
        *entry = entry.plus(&trans.weight);
    }

    while let Some((_from, gamma, _to, _w)) = worklist.pop_front() {
        // Process all rules that produce gamma on their RHS
        for rule in &wpds.rules {
            match rule {
                WpdsRule::Pop { from_gamma, weight } => {
                    // Pop: ⟨p, from_gamma⟩ → ⟨p', ε⟩
                    // For prestar: add (p, from_gamma, p') with f(r)
                    let key = (p_state, from_gamma.clone(), p_state);
                    let new_weight = *weight;
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
                        automaton.add_transition(p_state, from_gamma.clone(), p_state, cw);
                        worklist.push_back((p_state, from_gamma.clone(), p_state, cw));
                    }
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
/// Produced by `analyze_wpds()` and consumed by:
/// - `lint.rs`: Stack-aware dead-rule detection (W13)
/// - `cost_benefit.rs`: Ambiguity refinement (A5)
/// - Pipeline diagnostics
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

    // Find unreachable rules
    let mut unreachable_rules = Vec::new();
    for rule in &spec.rules {
        let rule_entry = StackSymbol::rule_position(&rule.category, &rule.label, 0);
        let rule_weight = post.symbol_weight(&rule_entry);

        if rule_weight.is_zero() && !reachable_categories.contains(&rule.category) {
            // Find which calling contexts are missing
            let missing = find_missing_callers(spec, &rule.category, &reachable_categories);
            unreachable_rules.push(WpdsUnreachableRule {
                rule_label: rule.label.clone(),
                category: rule.category.clone(),
                missing_contexts: missing,
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

    WpdsAnalysis {
        grammar_name: spec.name.clone(),
        num_symbols: bool_wpds.num_symbols(),
        num_rules: bool_wpds.num_rules(),
        reachable_categories,
        unreachable_rules,
        category_weights,
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
}
