use super::*;

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
            },
            WpdsRule::Replace { from_gamma, to_gamma, weight } => {
                write!(f, "⟨p, {}⟩ ↪ ⟨p', {}⟩  [w={}]", from_gamma, to_gamma, weight)
            },
            WpdsRule::Push {
                from_gamma,
                to_gamma_bottom,
                to_gamma_top,
                weight,
            } => {
                write!(
                    f,
                    "⟨p, {}⟩ ↪ ⟨p', {} {}⟩  [w={}]",
                    from_gamma, to_gamma_bottom, to_gamma_top, weight
                )
            },
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
    pub(crate) fn ensure_symbol(&mut self, sym: StackSymbol) -> usize {
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
    pub(crate) fn add_rule(&mut self, rule: WpdsRule<W>) {
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
    /// Set of all stack symbols that appear in at least one transition.
    /// Maintained incrementally by `add_transition()` for O(1) lookup in
    /// `is_symbol_in_any_configuration()`.
    pub symbols_present: HashSet<StackSymbol>,
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
            symbols_present: HashSet::new(),
        }
    }

    /// Allocate a fresh state.
    pub fn add_state(&mut self) -> PAutomatonStateId {
        let id = self.num_states;
        self.num_states += 1;
        id
    }

    /// Add a transition.
    pub fn add_transition(
        &mut self,
        from: PAutomatonStateId,
        symbol: StackSymbol,
        to: PAutomatonStateId,
        weight: W,
    ) {
        let idx = self.transitions.len();
        self.symbols_present.insert(symbol.clone());
        self.transitions
            .push(PAutomatonTransition { from, symbol, to, weight });
        self.transitions_by_source
            .entry(from)
            .or_default()
            .push(idx);
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

    /// Check if a stack symbol appears in any reachable configuration at any
    /// stack depth.
    ///
    /// Scans ALL transitions in the P-automaton, not just those from the initial
    /// state. After poststar saturation, every transition participates in at least
    /// one reachable configuration, so presence in any transition means the symbol
    /// is live (can appear on the continuation stack during a valid parse).
    ///
    /// Use this instead of `is_symbol_accepted` when determining frame liveness:
    /// continuation symbols in Push rules appear as transitions from intermediate
    /// states (`q_r`), not from the initial state (`p`).
    pub fn is_symbol_in_any_configuration(&self, symbol: &StackSymbol) -> bool {
        self.symbols_present.contains(symbol)
    }

    /// Weight of the ONE-SYMBOL configuration `⟨p, symbol⟩` in the accepted set.
    ///
    /// Returns the semiring sum of the weights on transitions `(initial, symbol, q)`
    /// **whose target `q` is a final state**. That is the acceptance condition of
    /// Reps et al. (2007) Definition 3 for the stack word `u = symbol`: a path from
    /// `p` reading `u` that ENDS IN A FINAL STATE. It is the weighted counterpart of
    /// [`is_symbol_accepted`](Self::is_symbol_accepted), which decides the same
    /// membership question, and it agrees with `cegar::abstract_check`'s
    /// `accepts_initial_config`, the sibling implementation of the same query.
    ///
    /// # Why the target has to be checked
    ///
    /// Saturation adds transitions that lead nowhere accepting. `prestar`'s Phase 1
    /// seeds `(p, γ, p)` for every Pop rule — a SELF-LOOP on the initial state — and
    /// the Replace pass then propagates it onto other symbols. Summing every
    /// out-transition regardless of target counts those self-loops as membership, so
    /// a WPDS with rules came back non-zero against a bad set with NO transitions at
    /// all, i.e. against the empty set of configurations. `check_safety` read exactly
    /// this weight, so it reported `safe = false` with a witness for a property that
    /// nothing could violate (`verify::tests::test_empty_bad_states_is_safe`).
    ///
    /// # Not the query for "does this symbol occur anywhere?"
    ///
    /// A symbol can be live without being a one-symbol configuration: in a `poststar`
    /// automaton a pushed symbol `γ_top` sits on `(p, γ_top, q_r)` where `q_r` is the
    /// fresh intermediate state carrying the continuation, so `⟨p, γ_top γ_bottom⟩`
    /// is accepted while `⟨p, γ_top⟩` is not. Liveness questions of that shape —
    /// dead-rule detection, dispatch classification, EWPDS merge gating — want
    /// [`stack_top_weight`](Self::stack_top_weight) instead.
    pub fn symbol_weight(&self, symbol: &StackSymbol) -> W {
        let mut total = W::zero();
        if let Some(trans_indices) = self.transitions_by_source.get(&self.initial_state) {
            for &idx in trans_indices {
                let t = &self.transitions[idx];
                if t.symbol == *symbol && self.final_states.contains(&t.to) {
                    total = total.plus(&t.weight);
                }
            }
        }
        total
    }

    /// Weight of `symbol` appearing at the TOP of a reachable stack, at any depth.
    ///
    /// Returns the semiring sum of the weights on all transitions
    /// `(initial, symbol, q)` for any `q`, final or not — the weighted counterpart of
    /// [`is_symbol_reachable`](Self::is_symbol_reachable). In a `poststar` automaton
    /// the stack word continues from `q`, so a non-final target means the symbol is
    /// the top of a LONGER accepted configuration rather than a one-symbol one.
    ///
    /// # Direction of the approximation
    ///
    /// This OVER-approximates liveness: it also counts a target from which no final
    /// state is reachable, and such a target contributes to no accepted configuration.
    /// Every caller uses the result as `is_zero()` ⇒ "nothing here", so over-counting
    /// can only suppress a diagnostic, never invent one — no rule is called dead, no
    /// dispatch is called dead, and no first-token candidate is dropped on the
    /// strength of a transition that leads nowhere. Do NOT use it to decide
    /// membership of a configuration in the accepted set; that is
    /// [`symbol_weight`](Self::symbol_weight), and reading the two as
    /// interchangeable is what made `check_safety` unsound.
    pub fn stack_top_weight(&self, symbol: &StackSymbol) -> W {
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
