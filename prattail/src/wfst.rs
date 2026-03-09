//! WFST-based prediction for weighted dispatch.
//!
//! Provides the `PredictionWfst` — a per-category weighted finite state
//! transducer that ranks parse alternatives by weight. Given a token, the
//! predictor returns candidate `DispatchAction`s ordered by tropical weight
//! (lower = more likely), enabling the parser to try the most-likely path first.
//!
//! ## Architecture
//!
//! The prediction WFST is built at compile time during the PraTTaIL pipeline,
//! after FIRST/FOLLOW set computation. It encodes:
//!
//! - **Unambiguous tokens**: single transition, weight 0.0 (tropical one)
//! - **Ambiguous tokens**: multiple transitions weighted by declaration order
//!   and FIRST-set uniqueness analysis
//! - **Cross-category tokens unique to source**: weight 0.0 (deterministic)
//! - **Shared cross-category tokens**: weight based on overlap analysis
//!
//! ## Derived from lling-llang
//!
//! The `VectorWfst` and `WeightedTransition` types are minimal adaptations
//! from `lling-llang/src/wfst/`. Only the subset needed for prediction is
//! included (~150 LOC), not the full WFST algebra.

use std::collections::HashMap;

use crate::automata::semiring::{ContextWeight, Semiring, TropicalWeight};
use crate::prediction::{CrossCategoryOverlap, DispatchAction, FirstSet};
use crate::token_id::{TokenId, TokenIdMap};

// ══════════════════════════════════════════════════════════════════════════════
// WFST types (minimal, from lling-llang)
// ══════════════════════════════════════════════════════════════════════════════

/// State identifier in a WFST.
pub type WfstStateId = u32;

/// Sentinel for "no state".
pub const NO_STATE: WfstStateId = WfstStateId::MAX;

/// A weighted transition in the prediction WFST.
///
/// Maps an input token to a dispatch action with an associated weight.
#[derive(Debug, Clone)]
pub struct WeightedTransition {
    /// Source state.
    pub from: WfstStateId,
    /// Input label (token ID). `EPSILON_TOKEN` for epsilon transitions.
    pub input: TokenId,
    /// Output: index into the action table.
    pub action_idx: u32,
    /// Target state.
    pub to: WfstStateId,
    /// Transition weight (tropical: lower = more likely).
    pub weight: TropicalWeight,
}

/// A state in the prediction WFST.
#[derive(Debug, Clone)]
pub struct WfstState {
    /// State identifier.
    pub id: WfstStateId,
    /// Whether this is a final (accepting) state.
    pub is_final: bool,
    /// Final weight (if accepting).
    pub final_weight: TropicalWeight,
    /// Outgoing transitions.
    pub transitions: Vec<WeightedTransition>,
}

impl WfstState {
    /// Create a new non-final state.
    pub fn new(id: WfstStateId) -> Self {
        WfstState {
            id,
            is_final: false,
            final_weight: TropicalWeight::zero(),
            transitions: Vec::new(),
        }
    }

    /// Create a new final state with the given weight.
    pub fn final_state(id: WfstStateId, weight: TropicalWeight) -> Self {
        WfstState {
            id,
            is_final: true,
            final_weight: weight,
            transitions: Vec::new(),
        }
    }
}

/// A weighted prediction entry: dispatch action + tropical weight.
#[derive(Debug, Clone)]
pub struct WeightedAction {
    /// The dispatch action to take.
    pub action: DispatchAction,
    /// Weight for this action (tropical: lower = better).
    pub weight: TropicalWeight,
}

// ══════════════════════════════════════════════════════════════════════════════
// State equivalence signature (for B3 minimization)
// ══════════════════════════════════════════════════════════════════════════════

/// Signature capturing the observable behavior of a WFST state.
///
/// Two states with identical signatures are equivalent: they accept the same
/// inputs, produce the same outputs, and transition to the same targets with
/// the same weights. Used by `PredictionWfst::minimize()` to identify
/// mergeable states.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct StateSignature {
    is_final: bool,
    final_weight_bits: u64,
    /// Sorted transitions: (token_id, action_idx, target_state_id, weight_bits)
    transitions: Vec<(TokenId, u32, WfstStateId, u64)>,
}

impl StateSignature {
    fn from_state(state: &WfstState) -> Self {
        let mut transitions: Vec<(TokenId, u32, WfstStateId, u64)> = state
            .transitions
            .iter()
            .map(|t| (t.input, t.action_idx, t.to, t.weight.value().to_bits()))
            .collect();
        transitions.sort();

        StateSignature {
            is_final: state.is_final,
            final_weight_bits: state.final_weight.value().to_bits(),
            transitions,
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Sprint 8: Canonical WFST structure for alpha-equivalence / isomorphism detection
// ══════════════════════════════════════════════════════════════════════════════

/// The shape of a dispatch action, erasing category-specific names.
///
/// Two actions with the same shape but different names (e.g., `Direct { rule_label: "AddInt" }`
/// vs `Direct { rule_label: "AddFloat" }`) are considered alpha-equivalent. The shape
/// preserves structural properties that affect codegen (e.g., `needs_backtrack`, alternative
/// count) while erasing concrete identifiers.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum CanonicalActionShape {
    Direct,
    Lookahead {
        alternative_count: usize,
        has_fallback: bool,
    },
    CrossCategory {
        needs_backtrack: bool,
    },
    Cast,
    Grouping,
    Variable,
}

impl CanonicalActionShape {
    /// Extract the shape from a concrete `DispatchAction`.
    pub fn from_action(action: &crate::prediction::DispatchAction) -> Self {
        match action {
            crate::prediction::DispatchAction::Direct { .. } => CanonicalActionShape::Direct,
            crate::prediction::DispatchAction::Lookahead {
                alternatives,
                fallback,
            } => CanonicalActionShape::Lookahead {
                alternative_count: alternatives.len(),
                has_fallback: fallback.is_some(),
            },
            crate::prediction::DispatchAction::CrossCategory {
                needs_backtrack, ..
            } => CanonicalActionShape::CrossCategory {
                needs_backtrack: *needs_backtrack,
            },
            crate::prediction::DispatchAction::Cast { .. } => CanonicalActionShape::Cast,
            crate::prediction::DispatchAction::Grouping { .. } => CanonicalActionShape::Grouping,
            crate::prediction::DispatchAction::Variable { .. } => CanonicalActionShape::Variable,
        }
    }
}

/// A canonicalized state in a WFST, with De Bruijn action indices.
///
/// Action indices are replaced with encounter-order De Bruijn indices so that
/// two WFSTs with the same topology but different action tables produce identical
/// canonical states. This enables hash-based grouping of isomorphic WFSTs.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct CanonicalState {
    pub is_final: bool,
    pub final_weight_bits: u64,
    /// Sorted transitions: `(token_id, de_bruijn_action_index, target_state, weight_bits)`
    pub transitions: Vec<(TokenId, u32, WfstStateId, u64)>,
}

/// De Bruijn-canonicalized WFST structure for alpha-equivalence detection.
///
/// Two `PredictionWfst` instances are **alpha-equivalent** (isomorphic) if they
/// have identical `CanonicalWfstStructure` values. This means:
/// - Same state count, same state accepting status/weights
/// - Same transition topology (same tokens lead to same states with same weights)
/// - Same action *shapes* at each De Bruijn position (Direct vs Lookahead vs Cast etc.)
/// - Only the concrete names (rule labels, category names) differ
///
/// The De Bruijn canonicalization walks transitions in deterministic order
/// (state 0 first, sorted by token_id within each state) and replaces each
/// unique `action_idx` with a sequential index (0, 1, 2, ...).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct CanonicalWfstStructure {
    pub states: Vec<CanonicalState>,
    pub start: WfstStateId,
    /// Action shapes in De Bruijn order. `action_shapes[i]` is the shape of
    /// the action at De Bruijn index `i`.
    pub action_shapes: Vec<CanonicalActionShape>,
}

// ══════════════════════════════════════════════════════════════════════════════
// PredictionWfst — per-category prediction
// ══════════════════════════════════════════════════════════════════════════════

/// Per-category prediction WFST.
///
/// Maps tokens to weighted dispatch actions. The start state has one transition
/// per token in the category's FIRST set, each leading to a final state with
/// the corresponding dispatch action. For ambiguous tokens, multiple transitions
/// exist from the start state, weighted by declaration order and FIRST-set
/// uniqueness.
///
/// The base topology is a simple one-level WFST (start → accept) for
/// single-token dispatch. Two-token disambiguation extends this with
/// intermediate states: `start --(token1)--> intermediate --(token2)--> accept`,
/// enabling compile-time resolution of NFA-ambiguous groups where each rule
/// has a distinct second terminal.
#[derive(Debug, Clone)]
pub struct PredictionWfst {
    /// Category this predictor serves.
    pub category: String,
    /// WFST states.
    pub states: Vec<WfstState>,
    /// Start state ID.
    pub start: WfstStateId,
    /// Action table: indexed by `action_idx` in transitions.
    pub actions: Vec<WeightedAction>,
    /// Token ID mapping (shared across categories).
    pub token_map: TokenIdMap,
    /// Optional beam width for pruning low-probability actions.
    /// When `Some(w)`, actions with weight > best + w are pruned.
    pub beam_width: Option<TropicalWeight>,
    /// ContextWeight label assignments: maps rule_label → bit position (0..127).
    /// Used by the powerset WFST to track which rules are alive after consuming tokens.
    /// Built per-group: within each ambiguous dispatch token group, rules get
    /// sequential bit IDs. Empty when no ContextWeight analysis has been performed.
    pub context_labels: HashMap<String, u8>,
}

impl PredictionWfst {
    // ══════════════════════════════════════════════════════════════════════════
    // Sprint 8: Canonical structure for isomorphism detection
    // ══════════════════════════════════════════════════════════════════════════

    /// Compute the De Bruijn-canonicalized structure of this WFST.
    ///
    /// Walks states in ID order starting from state 0. For each transition
    /// encountered (sorted by token_id within each state), replaces the
    /// concrete `action_idx` with a sequential De Bruijn index. Two WFSTs
    /// with identical topology but different action tables produce identical
    /// canonical structures.
    ///
    /// The action shapes (Direct/Lookahead/CrossCategory/Cast/Grouping/Variable)
    /// are also recorded to ensure isomorphic WFSTs have compatible codegen
    /// requirements.
    pub fn canonical_structure(&self) -> CanonicalWfstStructure {
        let mut action_debruijn: HashMap<u32, u32> = HashMap::new();
        let mut next_debruijn: u32 = 0;
        let mut action_shapes: Vec<CanonicalActionShape> = Vec::new();

        let states: Vec<CanonicalState> = self
            .states
            .iter()
            .map(|state| {
                let mut transitions: Vec<(TokenId, u32, WfstStateId, u64)> = state
                    .transitions
                    .iter()
                    .map(|t| {
                        let db_idx = *action_debruijn.entry(t.action_idx).or_insert_with(|| {
                            let idx = next_debruijn;
                            next_debruijn += 1;
                            // Record the action shape at this De Bruijn index
                            if let Some(wa) = self.actions.get(t.action_idx as usize) {
                                action_shapes
                                    .push(CanonicalActionShape::from_action(&wa.action));
                            }
                            idx
                        });
                        (t.input, db_idx, t.to, t.weight.value().to_bits())
                    })
                    .collect();
                transitions.sort();

                CanonicalState {
                    is_final: state.is_final,
                    final_weight_bits: state.final_weight.value().to_bits(),
                    transitions,
                }
            })
            .collect();

        CanonicalWfstStructure {
            states,
            start: self.start,
            action_shapes,
        }
    }

    /// Compute a hash of the canonical WFST structure.
    ///
    /// Two WFSTs with the same canonical hash are candidates for isomorphism.
    /// (Hash collisions are possible but unlikely; use `canonical_structure()`
    /// equality for definitive comparison.)
    pub fn canonical_hash(&self) -> u64 {
        use std::hash::{Hash, Hasher};
        let canonical = self.canonical_structure();
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        canonical.hash(&mut hasher);
        hasher.finish()
    }

    // ══════════════════════════════════════════════════════════════════════════
    // Prediction queries
    // ══════════════════════════════════════════════════════════════════════════

    /// Query the prediction WFST for a token, returning weighted actions
    /// sorted by weight (lowest first = most likely).
    ///
    /// This is the core prediction interface used by dispatch code generation.
    pub fn predict(&self, token_name: &str) -> Vec<&WeightedAction> {
        let token_id = match self.token_map.get(token_name) {
            Some(id) => id,
            None => return Vec::new(),
        };

        let start_state = &self.states[self.start as usize];
        let mut results: Vec<&WeightedAction> = start_state
            .transitions
            .iter()
            .filter(|t| t.input == token_id)
            // Only follow transitions to final states (skip intermediate states
            // used by two-token paths — those are non-final with outgoing transitions)
            .filter(|t| {
                self.states.get(t.to as usize).map_or(false, |s| s.is_final)
            })
            .filter_map(|t| self.actions.get(t.action_idx as usize))
            .collect();

        // Sort by weight: lowest (best) first
        results.sort_by_key(|a| a.weight);
        results
    }

    /// Returns `(action, derivation_count)` for each dispatch action at the
    /// given token.
    ///
    /// The derivation count indicates ambiguity: `count > 1` means multiple
    /// rules can handle this token in the current category. The dispatch
    /// codegen can use this to prefer deterministic (count=1) arms over
    /// ambiguous ones.
    ///
    /// The total derivation count for a token is the number of actions
    /// returned by `predict()` — this method annotates each action with
    /// that count for downstream use in product semiring compositions.
    pub fn predict_with_confidence(&self, token_name: &str) -> Vec<(&WeightedAction, crate::automata::semiring::CountingWeight)> {
        let actions = self.predict(token_name);
        let count = crate::automata::semiring::CountingWeight::new(actions.len() as u64);
        actions.into_iter().map(|a| (a, count)).collect()
    }

    /// Query prediction with beam pruning: returns only actions within
    /// `beam_width` of the best action's weight.
    ///
    /// If no beam width is set, behaves identically to `predict()`.
    pub fn predict_pruned(&self, token_name: &str) -> Vec<&WeightedAction> {
        let actions = self.predict(token_name);
        match (self.beam_width, actions.first()) {
            (Some(beam), Some(best)) => {
                let threshold = best.weight.value() + beam.value();
                actions
                    .into_iter()
                    .filter(|a| a.weight.value() <= threshold)
                    .collect()
            },
            _ => actions,
        }
    }

    /// Returns indices into `rule_labels` sorted by weight (lowest first = most likely).
    ///
    /// Used by NFA merged prefix codegen to order try-all alternatives so that
    /// the weight-best alternative is tried first and returned as the primary
    /// result. Unknown rules get a default weight of 0.5 (cast-level priority).
    pub fn nfa_alternative_order(
        &self,
        token_name: &str,
        rule_labels: &[&str],
    ) -> Vec<(usize, TropicalWeight)> {
        let predictions = self.predict(token_name);
        let mut indexed: Vec<(usize, TropicalWeight)> = rule_labels
            .iter()
            .enumerate()
            .map(|(i, label)| {
                let weight = predictions
                    .iter()
                    .find(|a| a.action.rule_label() == *label)
                    .map(|a| a.weight)
                    .unwrap_or(TropicalWeight::new(0.5));
                (i, weight)
            })
            .collect();
        indexed.sort_by(|(_, wa), (_, wb)| wa.cmp(wb));
        indexed
    }

    /// A5: Query prediction and compute the NbestWeight\<2\> confidence gap.
    ///
    /// Returns the difference between the second-best and best prediction weights
    /// for the given token. A large gap indicates high confidence in the best
    /// alternative (the second-best is much worse), while a small gap indicates
    /// ambiguity (multiple alternatives are close in weight).
    ///
    /// Returns `f64::INFINITY` if there are fewer than 2 alternatives (single
    /// or no alternative = infinite confidence).
    pub fn confidence_gap(&self, token_name: &str) -> f64 {
        let actions = self.predict(token_name);
        match (actions.first(), actions.get(1)) {
            (Some(best), Some(second)) => second.weight.value() - best.weight.value(),
            _ => f64::INFINITY,
        }
    }

    // ══════════════════════════════════════════════════════════════════════════
    // Two-token prediction queries
    // ══════════════════════════════════════════════════════════════════════════

    /// Query the prediction WFST with a two-token lookahead sequence.
    ///
    /// Traverses two levels: `start --(token1)--> intermediate --(token2)--> accept`.
    /// Returns weighted actions reachable through the two-token path, sorted by
    /// weight (lowest first). Falls back to single-token `predict()` when no
    /// intermediate states exist for `token1`.
    ///
    /// Two-token paths are added via `PredictionWfstBuilder::add_two_token_action()`.
    pub fn predict_two_token(&self, token1: &str, token2: &str) -> Vec<&WeightedAction> {
        let token1_id = match self.token_map.get(token1) {
            Some(id) => id,
            None => return Vec::new(),
        };
        let token2_id = match self.token_map.get(token2) {
            Some(id) => id,
            None => return Vec::new(),
        };

        let start_state = &self.states[self.start as usize];

        // Find intermediate states reachable from start via token1 that are NOT final
        // (final states are single-token accept states; non-final intermediates are
        // two-token path intermediates)
        let intermediates: Vec<(WfstStateId, TropicalWeight)> = start_state
            .transitions
            .iter()
            .filter(|t| t.input == token1_id)
            .filter_map(|t| {
                let target = self.states.get(t.to as usize)?;
                if !target.is_final && !target.transitions.is_empty() {
                    Some((t.to, t.weight))
                } else {
                    None
                }
            })
            .collect();

        if intermediates.is_empty() {
            // No two-token paths for this token1 — fall back to single-token
            return self.predict(token1);
        }

        // Traverse from intermediate states via token2
        let mut results: Vec<(&WeightedAction, TropicalWeight)> = Vec::new();
        for (mid_id, weight1) in &intermediates {
            if let Some(mid_state) = self.states.get(*mid_id as usize) {
                for t in &mid_state.transitions {
                    if t.input == token2_id {
                        if let Some(action) = self.actions.get(t.action_idx as usize) {
                            // Accumulated weight = weight of first hop + weight of second hop
                            let total_weight = TropicalWeight::new(weight1.value() + t.weight.value());
                            results.push((action, total_weight));
                        }
                    }
                }
            }
        }

        if results.is_empty() {
            // token2 not found via any intermediate — fall back to single-token
            return self.predict(token1);
        }

        // Sort by accumulated weight (lowest first)
        results.sort_by(|(_, wa), (_, wb)| wa.cmp(wb));
        results.into_iter().map(|(action, _)| action).collect()
    }

    /// Check whether a two-token sequence deterministically identifies a single rule.
    ///
    /// Returns `Some(rule_label)` when `predict_two_token(token1, token2)` yields
    /// exactly one action, indicating the parser can commit without NFA try-all.
    /// Returns `None` when the sequence is still ambiguous or unrecognized.
    pub fn is_deterministic_after(&self, tokens: &[&str]) -> Option<String> {
        match tokens.len() {
            0 => None,
            1 => {
                let actions = self.predict(tokens[0]);
                if actions.len() == 1 {
                    Some(actions[0].action.rule_label())
                } else {
                    None
                }
            }
            _ => {
                let actions = self.predict_two_token(tokens[0], tokens[1]);
                if actions.len() == 1 {
                    Some(actions[0].action.rule_label())
                } else {
                    None
                }
            }
        }
    }

    /// Return the set of actions reachable after consuming the given token sequence.
    ///
    /// For a single token, returns all actions at that dispatch point.
    /// For two tokens, returns the narrowed set via two-token paths.
    /// Used by ContextWeight tracking to compute live rule sets.
    pub fn live_actions_after(&self, tokens: &[&str]) -> Vec<&WeightedAction> {
        match tokens.len() {
            0 => Vec::new(),
            1 => self.predict(tokens[0]),
            _ => self.predict_two_token(tokens[0], tokens[1]),
        }
    }

    // ══════════════════════════════════════════════════════════════════════════
    // ContextWeight powerset queries (Sprint 3)
    // ══════════════════════════════════════════════════════════════════════════

    /// Assign ContextWeight bit positions to rules in an ambiguous group.
    ///
    /// Each rule in `rule_labels` gets a sequential bit ID (0..N-1). These
    /// bit positions are stored in `context_labels` and used by
    /// `live_rules_context_after()` to track which rules survive token consumption.
    ///
    /// Typically called per ambiguous dispatch token group during pipeline
    /// enrichment. The 128-bit capacity (u128) supports up to 128 rules per
    /// group — far beyond the 2–10 rules seen in practice.
    pub fn assign_context_labels(&mut self, rule_labels: &[&str]) {
        for (i, label) in rule_labels.iter().enumerate() {
            if i < 128 {
                self.context_labels.insert(label.to_string(), i as u8);
            }
        }
    }

    /// Return a ContextWeight bitset indicating which rules from the ambiguous
    /// group survive after consuming the given token sequence.
    ///
    /// Uses `live_actions_after()` to find reachable actions, then maps each
    /// action's `rule_label()` to its assigned bit position via `context_labels`.
    /// Actions without assigned bit positions are ignored (they belong to a
    /// different ambiguous group or were not enriched).
    ///
    /// Returns `ContextWeight::zero()` (empty set) when no context labels have
    /// been assigned or when no actions survive.
    pub fn live_rules_context_after(&self, tokens: &[&str]) -> ContextWeight {
        if self.context_labels.is_empty() {
            return ContextWeight::zero();
        }

        let actions = self.live_actions_after(tokens);
        let mut ctx = ContextWeight::zero();
        for action in &actions {
            if let Some(&bit) = self.context_labels.get(&action.action.rule_label()) {
                ctx = ctx.plus(&ContextWeight::singleton(bit));
            }
        }
        ctx
    }

    /// Check whether the ContextWeight narrows to a singleton after consuming
    /// the given token sequence, meaning the parser can deterministically commit.
    ///
    /// Returns `Some(rule_label)` when exactly one rule survives, `None` otherwise.
    /// This is the ContextWeight analog of `is_deterministic_after()`, but uses
    /// the powerset bitset rather than action count.
    pub fn is_deterministic_context(&self, tokens: &[&str]) -> Option<String> {
        let ctx = self.live_rules_context_after(tokens);
        if ctx.count() == 1 {
            // Find the single surviving rule label
            let bit = ctx.bits().trailing_zeros() as u8;
            self.context_labels
                .iter()
                .find(|(_, &b)| b == bit)
                .map(|(label, _)| label.clone())
        } else {
            None
        }
    }

    /// Return the ContextWeight bitset for a specific ambiguous group at a
    /// dispatch token, along with the count of surviving rules.
    ///
    /// This combines `live_rules_context_after()` with the count for use in
    /// diagnostics and decision tree annotations.
    pub fn context_narrowing(&self, tokens: &[&str]) -> (ContextWeight, u32) {
        let ctx = self.live_rules_context_after(tokens);
        (ctx, ctx.count())
    }

    /// Set the beam width for pruning.
    pub fn set_beam_width(&mut self, beam: Option<TropicalWeight>) {
        self.beam_width = beam;
    }

    /// Get the current beam width.
    pub fn beam_width(&self) -> Option<TropicalWeight> {
        self.beam_width
    }

    /// Adjust weights for all transitions matching `token_variant` by `adjustment`.
    ///
    /// Positive adjustment = higher weight (less likely); negative = lower weight
    /// (more likely). Clamps to 0.0 minimum. Only adjusts transition weights,
    /// NOT action weights (actions may be shared across multiple transitions).
    pub fn adjust_weight(&mut self, token_variant: &str, adjustment: f64) {
        let token_id = match self.token_map.get(token_variant) {
            Some(id) => id,
            None => return,
        };
        let start = self.start as usize;
        if start >= self.states.len() {
            return;
        }
        for trans in &mut self.states[start].transitions {
            if trans.input == token_id {
                let new_val = (trans.weight.value() + adjustment).max(0.0);
                trans.weight = TropicalWeight::new(new_val);
            }
        }
    }

    /// Number of registered actions.
    pub fn num_actions(&self) -> usize {
        self.actions.len()
    }

    /// Number of states in the WFST.
    pub fn num_states(&self) -> usize {
        self.states.len()
    }

    // ── B6: Runtime query methods for incremental parsing ──

    /// B6: List all valid next tokens for this category's WFST.
    ///
    /// Returns token names that have at least one dispatch action from the start
    /// state, sorted by best weight (lowest first = most likely). Useful for
    /// autocomplete/suggestion features in a language server.
    pub fn valid_continuations(&self) -> Vec<(&str, TropicalWeight)> {
        let start_state = match self.states.get(self.start as usize) {
            Some(s) => s,
            None => return Vec::new(),
        };

        // Collect unique tokens with their best weight
        let mut token_best: std::collections::HashMap<u16, TropicalWeight> =
            std::collections::HashMap::new();
        for trans in &start_state.transitions {
            let entry = token_best.entry(trans.input).or_insert(TropicalWeight::zero());
            if trans.weight < *entry || entry.is_zero() {
                *entry = trans.weight;
            }
        }

        // Sort by weight (best first)
        let mut results: Vec<(&str, TropicalWeight)> = token_best
            .into_iter()
            .filter_map(|(token_id, weight)| {
                self.token_map.name(token_id).map(|name| (name, weight))
            })
            .collect();
        results.sort_by(|(_, wa), (_, wb)| wa.cmp(wb));
        results
    }

    /// B6: Check whether a token has any valid dispatch action in this category.
    ///
    /// Returns `true` if the token is recognized by this category's WFST, `false`
    /// otherwise. Useful for early error detection: before attempting a full parse,
    /// check if the next token can even be dispatched.
    pub fn has_valid_dispatch(&self, token_name: &str) -> bool {
        !self.predict(token_name).is_empty()
    }

    /// B6: Estimate parse progress as a fraction `[0.0, 1.0]`.
    ///
    /// For the simple star-shaped WFST (start → accept), returns `0.0` at the
    /// start state and `1.0` at any final state. For multi-level WFSTs (if ever
    /// extended), estimates progress as `current_depth / max_depth`.
    ///
    /// `current_state` is the WFST state ID (0 = start for star-shaped WFSTs).
    pub fn parse_progress(&self, current_state: WfstStateId) -> f64 {
        if self.states.is_empty() {
            return 0.0;
        }
        if let Some(state) = self.states.get(current_state as usize) {
            if state.is_final {
                return 1.0;
            }
        }
        if current_state == self.start {
            return 0.0;
        }
        // For multi-level WFSTs: estimate based on state position
        let max_state = self.states.len() as f64;
        (current_state as f64) / max_state
    }

    /// Reconstruct a `PredictionWfst` from flat CSR-format arrays.
    ///
    /// This is the deserialization constructor used by generated code to rebuild
    /// a `PredictionWfst` from `static` arrays embedded at compile time.
    ///
    /// ## CSR format
    ///
    /// - `state_offsets`: `&[(trans_start, trans_count, is_final, final_weight)]`
    ///   One entry per state. `trans_start` is the index into `transitions`,
    ///   `trans_count` is the number of transitions from this state.
    /// - `transitions`: `&[(token_id_u16, target_state_u32, weight_f64)]`
    ///   Flat array of all transitions, grouped by source state.
    /// - `token_names`: `&[&str]` — token names for the `TokenIdMap`.
    /// - `beam`: `Option<f64>` — beam width configuration.
    ///
    /// Actions are reconstructed: each unique (token_id, weight) pair becomes a
    /// `WeightedAction`. The action table is rebuilt during deserialization since
    /// `DispatchAction` contains strings that can't be embedded in static arrays
    /// without additional serialization.
    ///
    /// For runtime prediction, the action table is pre-populated with
    /// `DispatchAction::Direct` placeholders. The caller can override specific
    /// actions via `with_trained_weights()`.
    pub fn from_flat(
        category: &str,
        state_offsets: &[(usize, usize, bool, f64)],
        transitions: &[(u16, u32, f64)],
        token_names: &[&str],
        beam: Option<f64>,
    ) -> Self {
        let token_map = TokenIdMap::from_names(token_names.iter().map(|s| s.to_string()));

        let mut actions = Vec::new();
        let mut states = Vec::with_capacity(state_offsets.len());

        for (state_idx, &(trans_start, trans_count, is_final, final_weight)) in
            state_offsets.iter().enumerate()
        {
            let mut state = WfstState {
                id: state_idx as WfstStateId,
                is_final,
                final_weight: TropicalWeight::new(final_weight),
                transitions: Vec::with_capacity(trans_count),
            };

            for i in 0..trans_count {
                let (token_id, target_state, weight) = transitions[trans_start + i];
                let action_idx = actions.len() as u32;

                // Create a placeholder action — the label is derived from token name
                let token_name = token_names
                    .get(token_id as usize)
                    .map(|s| s.to_string())
                    .unwrap_or_else(|| format!("token_{}", token_id));
                actions.push(WeightedAction {
                    action: DispatchAction::Direct {
                        rule_label: token_name.clone(),
                        parse_fn: format!("handle_{}", token_name.to_lowercase()),
                    },
                    weight: TropicalWeight::new(weight),
                });

                state.transitions.push(WeightedTransition {
                    from: state_idx as WfstStateId,
                    input: token_id,
                    action_idx,
                    to: target_state,
                    weight: TropicalWeight::new(weight),
                });
            }

            states.push(state);
        }

        PredictionWfst {
            category: category.to_string(),
            states,
            start: 0,
            actions,
            token_map,
            beam_width: beam.map(TropicalWeight::new),
            context_labels: HashMap::new(),
        }
    }

    /// Merge another `PredictionWfst` into this one via weighted union.
    ///
    /// All actions and transitions from `other` are incorporated into `self`.
    /// Token maps are unified: tokens that exist in `other` but not `self` are
    /// added. When both WFSTs have transitions for the same token, all
    /// alternatives are kept; `predict()` sorts by weight so the lowest-cost
    /// action from either source is tried first.
    ///
    /// The merged WFST retains `self`'s category name and beam width.
    /// Use `set_beam_width()` afterwards to override if needed.
    ///
    /// ## Two-State Invariant
    ///
    /// Both WFSTs use the two-state architecture (one start state, one final
    /// state per action). The union rebuilds this structure with the combined
    /// action and transition sets.
    pub fn union(&mut self, other: &PredictionWfst) {
        // Build a mapping from other's token names to self's token IDs
        let mut other_to_self_token: Vec<Option<TokenId>> =
            Vec::with_capacity(other.token_map.len());
        for i in 0..other.token_map.len() {
            if let Some(name) = other.token_map.name(i as TokenId) {
                let self_id = self.token_map.get_or_insert(name);
                other_to_self_token.push(Some(self_id));
            } else {
                other_to_self_token.push(None);
            }
        }

        // Import actions from other, recording the action index mapping
        let action_offset = self.actions.len() as u32;
        self.actions.extend(other.actions.iter().cloned());

        // Import transitions from other's start state into self's start state,
        // remapping token IDs and action indices
        if let Some(other_start) = other.states.get(other.start as usize) {
            for trans in &other_start.transitions {
                let remapped_token = other_to_self_token
                    .get(trans.input as usize)
                    .copied()
                    .flatten()
                    .unwrap_or(trans.input);

                let new_action_idx = trans.action_idx + action_offset;

                // Create a new final state for this action
                let final_id = self.states.len() as WfstStateId;
                self.states
                    .push(WfstState::final_state(final_id, TropicalWeight::one()));

                if let Some(start) = self.states.get_mut(self.start as usize) {
                    start.transitions.push(WeightedTransition {
                        from: self.start,
                        input: remapped_token,
                        action_idx: new_action_idx,
                        to: final_id,
                        weight: trans.weight,
                    });
                }
            }
        }
    }

    /// Minimize the WFST by merging equivalent states.
    ///
    /// Two states are equivalent when they have identical:
    /// - `is_final` flag
    /// - `final_weight` (compared by f64 bit pattern for exact equality)
    /// - outgoing transitions (same token → same target with same weight)
    ///
    /// For the common two-state architecture (start → N final states), this
    /// merges final states that share the same `final_weight` and have no
    /// outgoing transitions. After `union()`, many such duplicates accumulate.
    ///
    /// The start state's transitions are updated to point to representative
    /// states, and orphaned states are removed. Action indices are preserved.
    ///
    /// Returns the number of states removed.
    pub fn minimize(&mut self) -> usize {
        if self.states.len() <= 1 {
            return 0;
        }

        // Build a signature for each state: (is_final, final_weight_bits, sorted transitions)
        // States with identical signatures are equivalent.
        let mut sig_to_representative: HashMap<StateSignature, WfstStateId> = HashMap::new();
        let mut state_mapping: Vec<WfstStateId> = Vec::with_capacity(self.states.len());

        for state in &self.states {
            let sig = StateSignature::from_state(state);
            let representative = *sig_to_representative
                .entry(sig)
                .or_insert(state.id);
            state_mapping.push(representative);
        }

        let original_count = self.states.len();
        let unique_count = sig_to_representative.len();

        if unique_count == original_count {
            return 0; // No merging possible
        }

        // Update all transitions to point to representative states
        for state in &mut self.states {
            for trans in &mut state.transitions {
                if let Some(&mapped) = state_mapping.get(trans.to as usize) {
                    trans.to = mapped;
                }
            }
        }

        // Collect which state IDs are still referenced (as representatives)
        let mut referenced: std::collections::HashSet<WfstStateId> =
            std::collections::HashSet::new();
        referenced.insert(self.start);
        for state in &self.states {
            for trans in &state.transitions {
                referenced.insert(trans.to);
            }
        }

        // Remove unreferenced states and build an ID remapping
        let mut new_states: Vec<WfstState> = Vec::with_capacity(unique_count);
        let mut id_remap: HashMap<WfstStateId, WfstStateId> = HashMap::new();

        // Ensure start state gets ID 0
        if let Some(start_state) = self.states.iter().find(|s| s.id == self.start) {
            let new_id = new_states.len() as WfstStateId;
            id_remap.insert(start_state.id, new_id);
            let mut cloned = start_state.clone();
            cloned.id = new_id;
            new_states.push(cloned);
        }

        for state in &self.states {
            if state.id == self.start {
                continue; // Already added
            }
            if !referenced.contains(&state.id) {
                continue; // Orphaned — skip
            }
            // Only keep representative states (skip duplicates)
            if state_mapping.get(state.id as usize).copied() != Some(state.id) {
                continue;
            }
            let new_id = new_states.len() as WfstStateId;
            id_remap.insert(state.id, new_id);
            let mut cloned = state.clone();
            cloned.id = new_id;
            new_states.push(cloned);
        }

        // Apply the ID remapping to all transitions
        for state in &mut new_states {
            for trans in &mut state.transitions {
                if let Some(&new_from) = id_remap.get(&trans.from) {
                    trans.from = new_from;
                }
                if let Some(&new_to) = id_remap.get(&trans.to) {
                    trans.to = new_to;
                }
            }
        }

        self.start = *id_remap.get(&self.start).unwrap_or(&0);
        self.states = new_states;

        original_count - self.states.len()
    }

    /// Total number of states in this WFST.
    #[inline]
    pub fn state_count(&self) -> usize {
        self.states.len()
    }

    /// Count states reachable from the start state via transitions.
    pub fn reachable_state_count(&self) -> usize {
        let mut visited = vec![false; self.states.len()];
        let mut stack = vec![self.start as usize];
        while let Some(sid) = stack.pop() {
            if sid >= visited.len() || visited[sid] {
                continue;
            }
            visited[sid] = true;
            for t in &self.states[sid].transitions {
                stack.push(t.to as usize);
            }
        }
        visited.iter().filter(|&&v| v).count()
    }

    /// Remove states not reachable from the start state.
    ///
    /// Compacts state IDs after removal.
    pub fn remove_unreachable_states(&mut self) {
        let mut visited = vec![false; self.states.len()];
        let mut stack = vec![self.start as usize];
        while let Some(sid) = stack.pop() {
            if sid >= visited.len() || visited[sid] {
                continue;
            }
            visited[sid] = true;
            for t in &self.states[sid].transitions {
                stack.push(t.to as usize);
            }
        }

        // If all states are reachable, nothing to do
        if visited.iter().all(|&v| v) {
            return;
        }

        // Build remapping: old_id → new_id (only for reachable states)
        let mut remap = HashMap::new();
        let mut new_states = Vec::new();
        for (old_id, is_reachable) in visited.iter().enumerate() {
            if *is_reachable {
                let new_id = new_states.len() as WfstStateId;
                remap.insert(old_id as WfstStateId, new_id);
                new_states.push(self.states[old_id].clone());
            }
        }

        // Update transition targets
        for state in &mut new_states {
            state.id = *remap.get(&state.id).expect("state in remap");
            for t in &mut state.transitions {
                t.to = *remap.get(&t.to).expect("transition target in remap");
            }
        }

        self.start = *remap.get(&self.start).unwrap_or(&0);
        self.states = new_states;
    }

    /// Prune transitions with weight outside the beam of the best transition
    /// from each state. Returns the number of transitions removed.
    pub fn prune_by_beam(&mut self, beam_width: f64) -> usize {
        let mut total_pruned = 0;
        for state in &mut self.states {
            if state.transitions.is_empty() {
                continue;
            }
            let best_weight = state
                .transitions
                .iter()
                .map(|t| t.weight.value())
                .fold(f64::INFINITY, f64::min);
            let threshold = best_weight + beam_width;
            let before = state.transitions.len();
            state
                .transitions
                .retain(|t| t.weight.value() <= threshold);
            total_pruned += before - state.transitions.len();
        }
        total_pruned
    }

    /// Normalize transition weights per state so the best weight is 0.0.
    ///
    /// Subtracts the minimum weight from all transitions in each state.
    /// This preserves relative ordering while aligning the scale.
    /// Returns the number of states that were normalized.
    pub fn normalize_weights(&mut self) -> usize {
        let mut normalized_count = 0;
        for state in &mut self.states {
            if state.transitions.is_empty() {
                continue;
            }
            let best_weight = state
                .transitions
                .iter()
                .map(|t| t.weight.value())
                .fold(f64::INFINITY, f64::min);
            if best_weight != 0.0 && best_weight.is_finite() {
                for t in &mut state.transitions {
                    t.weight = TropicalWeight::new(t.weight.value() - best_weight);
                }
                // Also update corresponding action weights
                for t in &state.transitions.clone() {
                    if let Some(action) = self.actions.get_mut(t.action_idx as usize) {
                        action.weight = t.weight;
                    }
                }
                normalized_count += 1;
            }
        }
        normalized_count
    }

    /// Override weights with trained model weights.
    ///
    /// For each action whose `rule_label` matches a key in the trained model's
    /// `rule_weights` map, the action's weight is replaced with the trained weight.
    /// Unmatched actions keep their original (heuristic) weights.
    ///
    /// Also updates the corresponding transitions in the start state.
    #[cfg(feature = "wfst-log")]
    pub fn with_trained_weights(&mut self, model: &crate::training::TrainedModel) {
        for (idx, action) in self.actions.iter_mut().enumerate() {
            let label = match &action.action {
                DispatchAction::Direct { rule_label, .. } => rule_label.as_str(),
                DispatchAction::Cast { wrapper_label, .. } => wrapper_label.as_str(),
                DispatchAction::CrossCategory { rule_label, .. } => rule_label.as_str(),
                _ => continue,
            };

            if let Some(&trained_weight) = model.rule_weights.get(label) {
                let new_weight = TropicalWeight::new(trained_weight);
                action.weight = new_weight;

                // Update corresponding transition weight in start state
                if let Some(start) = self.states.get_mut(self.start as usize) {
                    for trans in &mut start.transitions {
                        if trans.action_idx == idx as u32 {
                            trans.weight = new_weight;
                        }
                    }
                }
            }
        }
    }

    /// Sprint 5: Apply weight corrections from NFA spillover training signals.
    ///
    /// For each correction, adjusts the weights of actions whose `rule_label()`
    /// matches rules associated with the primary weight (penalize) or selected
    /// weight (reinforce). The adjustment magnitude is `learning_rate × weight_delta`,
    /// clamped to `[-max_adjustment, +max_adjustment]`.
    ///
    /// This provides the WFST-level interface for the `SpilloverTrainer`.
    #[cfg(feature = "wfst-log")]
    pub fn apply_corrections(
        &mut self,
        corrections: &[WeightCorrection],
        learning_rate: f64,
        max_adjustment: f64,
    ) {
        let tolerance = 0.1;
        for correction in corrections {
            let adj = correction.primary_adjustment(learning_rate, max_adjustment);
            if adj < 1e-10 {
                continue;
            }

            let start = self.start as usize;
            if start >= self.states.len() {
                continue;
            }

            // Adjust transition weights in the start state
            for trans in &mut self.states[start].transitions {
                let tw = trans.weight.value();
                if (tw - correction.primary_weight).abs() < tolerance {
                    // Penalize primary: increase weight (less likely)
                    trans.weight = TropicalWeight::new((tw + adj).max(0.0));
                } else if (tw - correction.selected_weight).abs() < tolerance {
                    // Reinforce selected: decrease weight (more likely)
                    trans.weight = TropicalWeight::new((tw - adj).max(0.0));
                }
            }

            // Adjust action weights correspondingly
            for action in &mut self.actions {
                let aw = action.weight.value();
                if (aw - correction.primary_weight).abs() < tolerance {
                    action.weight = TropicalWeight::new((aw + adj).max(0.0));
                } else if (aw - correction.selected_weight).abs() < tolerance {
                    action.weight = TropicalWeight::new((aw - adj).max(0.0));
                }
            }
        }
    }

    /// A7: Compute Shannon entropy of the prediction distribution at this category.
    ///
    /// Uses the expectation semiring (`EntropyWeight`) with forward-backward to compute
    /// `H = -Σ pᵢ ln(pᵢ)` over the WFST's transition weights, where `pᵢ = exp(-wᵢ) / Z`.
    ///
    /// For the common star-shaped WFST (start → accept states), this is the entropy of
    /// the normalized distribution over dispatch actions from the start state.
    ///
    /// Returns `(entropy_nats, entropy_bits)`.
    ///
    /// # Requires
    /// Feature `wfst-log` (EntropyWeight is gated).
    #[cfg(feature = "wfst-log")]
    pub fn compute_entropy(&self) -> (f64, f64) {
        use crate::automata::semiring::{EntropyWeight, Semiring};
        use crate::forward_backward::forward_scores;

        let n = self.states.len();
        if n == 0 {
            return (0.0, 0.0);
        }

        // Build edge list for forward-backward: edges[from] = [(to, EntropyWeight)]
        let mut edges: Vec<Vec<(usize, EntropyWeight)>> = vec![Vec::new(); n];

        for state in &self.states {
            let from = state.id as usize;
            for trans in &state.transitions {
                let to = trans.to as usize;
                let w = trans.weight.value();
                // For Shannon entropy: set expectation = weight (negative log-prob)
                edges[from].push((to, EntropyWeight::from_arc_weight(w)));
            }
        }

        // Forward pass: scores from start state
        let forward = forward_scores::<EntropyWeight>(&edges, n);

        // Find final states
        let mut final_score = EntropyWeight::zero();
        for state in &self.states {
            if state.is_final {
                let idx = state.id as usize;
                let fwd = forward[idx];
                let fw = EntropyWeight::new(state.final_weight.value(), state.final_weight.value());
                final_score = final_score.plus(&fwd.times(&fw));
            }
        }

        // Shannon entropy H = E_p[-ln(p)] = E_p[w] + ln(Z)
        // where Z = Σ exp(-wᵢ) = exp(-total_weight)
        // so ln(Z) = -total_weight
        // Therefore H = total_expectation - total_weight
        let entropy_nats = if final_score.weight().is_finite() {
            final_score.expectation() - final_score.weight()
        } else {
            0.0
        };
        let entropy_bits = entropy_nats / std::f64::consts::LN_2;

        (entropy_nats, entropy_bits)
    }

    // ── D3: DOT/Graphviz visualization ─────────────────────────────────

    /// D3: Generate a DOT (Graphviz) representation of this prediction WFST.
    ///
    /// Each state is a node, transitions are edges labeled with `token / action [weight]`.
    /// The start state is highlighted with a double circle, final states are
    /// drawn with a double border. Deterministic transitions (weight=0.0) are
    /// drawn in black; ambiguous transitions (weight>0.0) are drawn in red.
    ///
    /// # Example
    /// ```text
    /// digraph PredictionWfst_Proc {
    ///   rankdir=LR;
    ///   node [shape=circle];
    ///   0 [shape=doublecircle, label="S0\n(start)"];
    ///   1 [shape=doublecircle, label="S1\n(final, w=0.00)"];
    ///   0 -> 1 [label="Ident / PInput [0.00]"];
    /// }
    /// ```
    pub fn to_dot(&self) -> String {
        use std::fmt::Write;
        let mut out = String::new();
        let safe_cat = self.category.replace(|c: char| !c.is_alphanumeric() && c != '_', "_");
        writeln!(out, "digraph PredictionWfst_{} {{", safe_cat).unwrap();
        writeln!(out, "  rankdir=LR;").unwrap();
        writeln!(out, "  node [shape=circle, fontname=\"Helvetica\"];").unwrap();
        writeln!(out, "  edge [fontname=\"Helvetica\", fontsize=10];").unwrap();

        // Emit nodes
        for state in &self.states {
            let shape = if state.id == self.start || state.is_final {
                "doublecircle"
            } else {
                "circle"
            };
            let mut label = format!("S{}", state.id);
            if state.id == self.start {
                label.push_str("\\n(start)");
            }
            if state.is_final {
                let w = state.final_weight.value();
                if w == 0.0 {
                    label.push_str("\\n(final)");
                } else {
                    label.push_str(&format!("\\n(final, w={:.2})", w));
                }
            }
            writeln!(out, "  {} [shape={}, label=\"{}\"];", state.id, shape, label).unwrap();
        }

        // Emit edges
        for state in &self.states {
            for t in &state.transitions {
                let token_label = if t.input == crate::token_id::EPSILON_TOKEN {
                    "ε".to_string()
                } else {
                    self.token_map
                        .name(t.input)
                        .unwrap_or("?")
                        .to_string()
                };
                let action_label = self
                    .actions
                    .get(t.action_idx as usize)
                    .map(|a| a.action.rule_label())
                    .unwrap_or_else(|| format!("act#{}", t.action_idx));
                let w = t.weight.value();
                let color = if w > 0.0 { "red" } else { "black" };
                writeln!(
                    out,
                    "  {} -> {} [label=\"{} / {} [{:.2}]\", color={}];",
                    t.from, t.to, token_label, action_label, w, color
                )
                .unwrap();
            }
        }

        writeln!(out, "}}").unwrap();
        out
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// A7: Entropy-based adaptive beam width
// ══════════════════════════════════════════════════════════════════════════════

/// A7: Compute per-category beam widths from entropy.
///
/// Maps Shannon entropy to beam width using a linear scaling:
/// - Entropy ≤ `low_threshold` → no beam (deterministic, pruning unnecessary)
/// - Entropy > `low_threshold` → beam = `base_beam + scale * (entropy - low_threshold)`
///
/// Higher-entropy categories (many equally-likely alternatives) get wider beams
/// to explore more possibilities. Low-entropy categories (dominated by one or
/// few alternatives) get narrow beams or no beam at all.
///
/// # Arguments
///
/// * `entropy_bits` — Shannon entropy in bits for this category.
/// * `base_beam` — Minimum beam width for categories above threshold (default: 1.0).
/// * `scale` — Beam width increase per additional bit of entropy (default: 0.5).
/// * `low_threshold` — Entropy below this → no beam (default: 0.5 bits).
/// * `max_beam` — Maximum beam width cap (default: 10.0).
pub fn entropy_to_beam_width(
    entropy_bits: f64,
    base_beam: f64,
    scale: f64,
    low_threshold: f64,
    max_beam: f64,
) -> Option<f64> {
    if entropy_bits <= low_threshold {
        None
    } else {
        let beam = base_beam + scale * (entropy_bits - low_threshold);
        Some(beam.min(max_beam))
    }
}

/// A7: Default entropy-to-beam-width parameters.
pub const ENTROPY_BEAM_BASE: f64 = 1.0;
pub const ENTROPY_BEAM_SCALE: f64 = 0.5;
pub const ENTROPY_BEAM_LOW_THRESHOLD: f64 = 0.5;
pub const ENTROPY_BEAM_MAX: f64 = 10.0;

/// C2: Position-aware NFA disambiguation — weight penalty per token difference.
///
/// When an alternative parse consumed a different number of tokens than the primary,
/// its weight is adjusted by `|pos_diff| * POSITION_WEIGHT_PENALTY` before beam
/// comparison. This implements "longest match" preference analogous to lexing:
/// - Longer matches (higher `alt_pos`) are treated as closer in weight to the primary
///   (they consumed more input, a positive signal).
/// - Shorter matches get penalized (they left more input unconsumed).
///
/// The penalty is applied symmetrically: `adjusted_w = alt_w + |alt_pos - primary_pos| * penalty`.
/// This means a shorter match must have a proportionally lower raw weight to remain competitive.
pub const POSITION_WEIGHT_PENALTY: f64 = 0.5;

// ══════════════════════════════════════════════════════════════════════════════
// Builder
// ══════════════════════════════════════════════════════════════════════════════

/// Builder for constructing a `PredictionWfst` from FIRST sets and dispatch tables.
pub struct PredictionWfstBuilder {
    category: String,
    token_map: TokenIdMap,
    actions: Vec<WeightedAction>,
    transitions: Vec<(TokenId, u32, TropicalWeight)>, // (input, action_idx, weight)
    /// Two-token transitions: (token1_id, token2_id, action_idx, weight)
    two_token_transitions: Vec<(TokenId, TokenId, u32, TropicalWeight)>,
    beam_width: Option<TropicalWeight>,
}

impl PredictionWfstBuilder {
    /// Create a new builder for the given category.
    pub fn new(category: &str, token_map: TokenIdMap) -> Self {
        PredictionWfstBuilder {
            category: category.to_string(),
            token_map,
            actions: Vec::new(),
            transitions: Vec::new(),
            two_token_transitions: Vec::new(),
            beam_width: None,
        }
    }

    /// Set the beam width for the built WFST.
    pub fn with_beam_width(mut self, beam: TropicalWeight) -> Self {
        self.beam_width = Some(beam);
        self
    }

    /// Add a dispatch action for a token with the given weight.
    pub fn add_action(&mut self, token_name: &str, action: DispatchAction, weight: TropicalWeight) {
        let token_id = self.token_map.get_or_insert(token_name);
        let action_idx = self.actions.len() as u32;
        self.actions.push(WeightedAction { action, weight });
        self.transitions.push((token_id, action_idx, weight));
    }

    /// Add a two-token dispatch action: `token1 → intermediate → token2 → accept`.
    ///
    /// Creates a 3-state path: `start --(token1)--> intermediate --(token2)--> accept`.
    /// Used when the first token is ambiguous but the second token disambiguates.
    ///
    /// The weight is split: first hop carries `weight`, second hop carries 0.0
    /// (all disambiguation cost is attributed to the dispatch decision).
    pub fn add_two_token_action(
        &mut self,
        token1: &str,
        token2: &str,
        action: DispatchAction,
        weight: TropicalWeight,
    ) {
        let token1_id = self.token_map.get_or_insert(token1);
        let token2_id = self.token_map.get_or_insert(token2);
        let action_idx = self.actions.len() as u32;
        self.actions.push(WeightedAction { action, weight });
        self.two_token_transitions.push((token1_id, token2_id, action_idx, weight));
    }

    /// Build the prediction WFST.
    ///
    /// Creates a multi-level WFST:
    /// - Single-token paths: `start → final` (one final state per action)
    /// - Two-token paths: `start → intermediate → final` (intermediate per unique
    ///   (token1, intermediate_group), final per action)
    pub fn build(self) -> PredictionWfst {
        // State 0: start state
        let mut start_state = WfstState::new(0);

        // Estimate capacity: single-token finals + two-token intermediates + finals
        let estimated_states = 1 + self.transitions.len() + self.two_token_transitions.len() * 2;
        let mut states = Vec::with_capacity(estimated_states);
        states.push(WfstState::new(0)); // placeholder for start

        // Single-token paths: start → final
        for (token_id, action_idx, weight) in &self.transitions {
            let final_id = states.len() as WfstStateId;
            states.push(WfstState::final_state(final_id, TropicalWeight::one()));

            start_state.transitions.push(WeightedTransition {
                from: 0,
                input: *token_id,
                action_idx: *action_idx,
                to: final_id,
                weight: *weight,
            });
        }

        // Two-token paths: start → intermediate → final
        // Group by token1 to share intermediate states
        if !self.two_token_transitions.is_empty() {
            let mut intermediate_map: HashMap<TokenId, WfstStateId> = HashMap::new();

            for (token1_id, token2_id, action_idx, weight) in &self.two_token_transitions {
                // Get or create intermediate state for this token1
                let mid_id = *intermediate_map.entry(*token1_id).or_insert_with(|| {
                    let mid = states.len() as WfstStateId;
                    states.push(WfstState::new(mid)); // non-final intermediate
                    // Add transition from start to intermediate (weight on first hop)
                    start_state.transitions.push(WeightedTransition {
                        from: 0,
                        input: *token1_id,
                        action_idx: 0, // placeholder — intermediate, not an action
                        to: mid,
                        weight: TropicalWeight::new(0.0), // weight deferred to second hop
                    });
                    mid
                });

                // Create final state for this action
                let final_id = states.len() as WfstStateId;
                states.push(WfstState::final_state(final_id, TropicalWeight::one()));

                // Add transition from intermediate to final (carries the action weight)
                states[mid_id as usize].transitions.push(WeightedTransition {
                    from: mid_id,
                    input: *token2_id,
                    action_idx: *action_idx,
                    to: final_id,
                    weight: *weight,
                });
            }
        }

        states[0] = start_state;

        PredictionWfst {
            category: self.category,
            states,
            start: 0,
            actions: self.actions,
            token_map: self.token_map,
            beam_width: self.beam_width,
            context_labels: HashMap::new(),
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Construction from existing prediction analysis
// ══════════════════════════════════════════════════════════════════════════════

/// Build prediction WFSTs for all categories from FIRST sets and overlap analysis.
///
/// Weight assignment strategy:
/// - Tokens unique to one category (no overlap): weight 0.0 (deterministic)
/// - Tokens shared across categories: weight = declaration_order * 1.0
///   (earlier-declared rules get lower weight)
/// - Cross-category with backtrack: source path weight 0.5, fallback weight 1.0
///   (try source first since it's the explicit cross-category rule)
pub fn build_prediction_wfsts(
    categories: &[String],
    first_sets: &HashMap<String, FirstSet>,
    overlaps: &HashMap<(String, String), CrossCategoryOverlap>,
    dispatch_actions: &HashMap<String, HashMap<String, DispatchAction>>,
) -> HashMap<String, PredictionWfst> {
    let mut result = HashMap::new();

    // Build shared token ID map from all FIRST sets
    let mut all_tokens: Vec<String> = Vec::new();
    for first_set in first_sets.values() {
        all_tokens.extend(first_set.tokens.iter().cloned());
    }
    let token_map = TokenIdMap::from_names(all_tokens);

    for category in categories {
        let mut builder = PredictionWfstBuilder::new(category, token_map.clone());

        if let Some(category_actions) = dispatch_actions.get(category) {
            let mut token_order: Vec<(&String, &DispatchAction)> = category_actions.iter().collect();
            // Sort for deterministic ordering (HashMap iteration order is arbitrary)
            token_order.sort_by(|(a, _), (b, _)| a.cmp(b));

            for (order, (token_name, action)) in token_order.iter().enumerate() {
                // Determine weight based on ambiguity analysis
                let weight = compute_action_weight(
                    token_name, action, category, first_sets, overlaps, order,
                );

                builder.add_action(token_name, (*action).clone(), weight);
            }
        }

        result.insert(category.clone(), builder.build());
    }

    result
}

/// Enrich prediction WFSTs with two-token paths for NFA-ambiguous groups.
///
/// For each category, identifies dispatch tokens where multiple RD rules
/// share the same first token. When the second syntax item uniquely identifies
/// the rule within the group — either directly (terminal) or via FIRST set
/// expansion (nonterminal) — adds two-token paths to the WFST:
/// `start --(token1)--> intermediate --(token2)--> accept`.
///
/// This migrates the `second_token_lookahead()` and `suffix_disjointness_check()`
/// analyses from trampoline.rs into the WFST itself, making them queryable by
/// all consumers (lint, decision tree, cost-benefit, error recovery).
///
/// ## FIRST-Set Expansion (Sprint 2)
///
/// When `items[1]` is `NonTerminal { category }`, the second-level transitions
/// are expanded using `FIRST(category)`. Each token in the FIRST set becomes a
/// second-level transition. This resolves cases like:
/// - `float ( Expr )` vs `float ( Ident )` — if FIRST(Expr) and FIRST(Ident)
///   are disjoint, the second token disambiguates.
///
/// Returns the number of two-token paths added across all categories.
pub fn enrich_with_two_token_paths(
    wfsts: &mut HashMap<String, PredictionWfst>,
    rd_rules: &[crate::recursive::RDRuleInfo],
    category_names: &[String],
    first_sets: &HashMap<String, crate::prediction::FirstSet>,
) -> usize {
    use crate::recursive::RDSyntaxItem;

    let mut total_added = 0;

    for cat in category_names {
        let wfst = match wfsts.get_mut(cat) {
            Some(w) => w,
            None => continue,
        };

        // Group RD rules by their dispatch token (first terminal)
        let mut groups: HashMap<String, Vec<&crate::recursive::RDRuleInfo>> = HashMap::new();
        for rule in rd_rules {
            if rule.category != *cat {
                continue;
            }
            if rule.is_collection || rule.prefix_bp.is_some() {
                continue;
            }
            if let Some(RDSyntaxItem::Terminal(t)) = rule.items.first() {
                groups.entry(t.clone()).or_default().push(rule);
            }
        }

        // For ambiguous groups (>1 rule), check if second-position analysis resolves them
        for (dispatch_token, rules) in &groups {
            if rules.len() < 2 {
                continue;
            }

            // Build per-rule FIRST sets for items[1..] (suffix after dispatch token).
            // Terminal items[1] contribute their variant name directly.
            // NonTerminal items[1] contribute FIRST(category) tokens.
            // IdentCapture/Binder contribute "Ident".
            let mut per_rule_second_tokens: Vec<(&str, Vec<String>)> = Vec::with_capacity(rules.len());
            let mut all_valid = true;

            for rule in rules {
                if rule.items.len() < 2 {
                    all_valid = false;
                    break;
                }
                let suffix = &rule.items[1..];
                let (first, _nullable) = crate::prediction::first_of_rd_suffix(suffix, first_sets);
                if first.tokens.is_empty() {
                    all_valid = false;
                    break;
                }
                per_rule_second_tokens.push((&rule.label, first.tokens.into_iter().collect()));
            }

            if !all_valid {
                continue;
            }

            // Check pairwise disjointness: each second-position token must map to
            // exactly one rule. This is the WFST analog of suffix_disjointness_check().
            let mut token_to_rule: HashMap<String, Vec<&str>> = HashMap::new();
            for (rule_label, tokens) in &per_rule_second_tokens {
                for token in tokens {
                    token_to_rule.entry(token.clone()).or_default().push(rule_label);
                }
            }

            if token_to_rule.values().any(|rules| rules.len() > 1) {
                continue; // Overlapping FIRST sets — can't disambiguate
            }

            // Disjoint! Add two-token paths for each (token2 → rule) mapping.
            let dispatch_token_variant = crate::automata::codegen::terminal_to_variant_name(dispatch_token);
            let token1_id = match wfst.token_map.get(&dispatch_token_variant) {
                Some(id) => id,
                None => wfst.token_map.get_or_insert(&dispatch_token_variant),
            };

            // Create a shared intermediate state for this dispatch token group
            let mid_id = wfst.states.len() as WfstStateId;
            wfst.states.push(WfstState::new(mid_id));

            // Add start → intermediate transition
            if let Some(start) = wfst.states.get_mut(wfst.start as usize) {
                start.transitions.push(WeightedTransition {
                    from: wfst.start,
                    input: token1_id,
                    action_idx: 0, // placeholder for intermediate
                    to: mid_id,
                    weight: TropicalWeight::new(0.0),
                });
            }

            for (second_token, rule_labels) in &token_to_rule {
                let rule_label = rule_labels[0];

                // Find the existing action for this rule to clone it
                let action = wfst.actions.iter().find(|a| a.action.rule_label() == rule_label);
                let (dispatch_action, weight) = if let Some(wa) = action {
                    (wa.action.clone(), wa.weight)
                } else {
                    (
                        DispatchAction::Direct {
                            rule_label: rule_label.to_string(),
                            parse_fn: format!("parse_{}", rule_label.to_lowercase()),
                        },
                        TropicalWeight::new(0.0),
                    )
                };

                // Register second token in token map
                let token2_id = wfst.token_map.get_or_insert(second_token);

                // Create final state
                let final_id = wfst.states.len() as WfstStateId;
                wfst.states.push(WfstState::final_state(final_id, TropicalWeight::one()));

                // Register the action
                let action_idx = wfst.actions.len() as u32;
                wfst.actions.push(WeightedAction {
                    action: dispatch_action,
                    weight,
                });

                // Add intermediate → final transition
                wfst.states[mid_id as usize].transitions.push(WeightedTransition {
                    from: mid_id,
                    input: token2_id,
                    action_idx,
                    to: final_id,
                    weight,
                });

                total_added += 1;
            }
        }
    }

    total_added
}

/// Compute the tropical weight for a dispatch action.
///
/// Weight assignment:
/// - `Direct`: weight 0.0 (unambiguous, deterministic)
/// - `CrossCategory` with `needs_backtrack: false`: weight 0.0 (deterministic)
/// - `CrossCategory` with `needs_backtrack: true`: weight 0.5 (try source first)
/// - `Lookahead`: weight 1.0 + order (needs extra tokens to decide)
/// - `Cast`: weight 0.5 (slightly penalized vs direct)
/// - `Grouping`: weight 0.0 (delimiter-driven, deterministic)
/// - `Variable`: weight 2.0 (last resort)
fn compute_action_weight(
    _token_name: &str,
    action: &DispatchAction,
    _category: &str,
    _first_sets: &HashMap<String, FirstSet>,
    _overlaps: &HashMap<(String, String), CrossCategoryOverlap>,
    order: usize,
) -> TropicalWeight {
    match action {
        DispatchAction::Direct { .. } => TropicalWeight::new(0.0),
        DispatchAction::Grouping { .. } => TropicalWeight::new(0.0),
        DispatchAction::CrossCategory { needs_backtrack, .. } => {
            if *needs_backtrack {
                TropicalWeight::new(0.5)
            } else {
                TropicalWeight::new(0.0)
            }
        },
        DispatchAction::Cast { .. } => TropicalWeight::new(0.5),
        DispatchAction::Lookahead { .. } => TropicalWeight::new(1.0 + order as f64),
        DispatchAction::Variable { .. } => TropicalWeight::new(2.0),
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Dispatch code generation with weight ordering
// ══════════════════════════════════════════════════════════════════════════════

/// Generate weight-ordered backtracking dispatch code for a category.
///
/// Unlike the unweighted dispatch in `dispatch.rs`, this version orders
/// backtracking alternatives by weight: the lowest-weight (most likely) path
/// is tried first, reducing expected backtracking cost.
///
/// Returns the generated dispatch code as a String fragment, or `None` if
/// no WFST-based dispatch is needed for this category.
pub fn generate_weighted_dispatch(wfst: &PredictionWfst, category: &str) -> Option<String> {
    if wfst.actions.is_empty() {
        return None;
    }

    // Group actions by token: for each token, collect all alternatives sorted by weight
    let mut token_groups: HashMap<TokenId, Vec<&WeightedAction>> = HashMap::new();

    let start_state = &wfst.states[wfst.start as usize];
    for transition in &start_state.transitions {
        if let Some(action) = wfst.actions.get(transition.action_idx as usize) {
            token_groups
                .entry(transition.input)
                .or_default()
                .push(action);
        }
    }

    // Sort each group by weight
    for group in token_groups.values_mut() {
        group.sort_by_key(|a| a.weight);
    }

    // Count ambiguous tokens (multiple actions for same token)
    let ambiguous_count = token_groups.values().filter(|g| g.len() > 1).count();
    let deterministic_count = token_groups.values().filter(|g| g.len() == 1).count();

    // Build summary comment
    let mut buf = String::with_capacity(512);
    use std::fmt::Write;
    writeln!(
        buf,
        "// WFST prediction for {}: {} tokens ({} deterministic, {} ambiguous)",
        category,
        token_groups.len(),
        deterministic_count,
        ambiguous_count,
    )
    .unwrap();

    // Emit per-token weight annotations as comments (for debugging/documentation)
    for (token_id, group) in &token_groups {
        if let Some(name) = wfst.token_map.name(*token_id) {
            if group.len() > 1 {
                write!(buf, "// {}: [", name).unwrap();
                for (i, action) in group.iter().enumerate() {
                    if i > 0 {
                        buf.push_str(", ");
                    }
                    write!(buf, "w={}", action.weight).unwrap();
                }
                writeln!(buf, "]").unwrap();
            }
        }
    }

    Some(buf)
}

// ══════════════════════════════════════════════════════════════════════════════
// C1: Semantic Weight Feedback
// ══════════════════════════════════════════════════════════════════════════════

/// C1: A weight correction event recorded when the Ascent semantic layer
/// selects a non-primary alternative during NFA disambiguation.
///
/// When `from_alternatives()` or the spillover replay mechanism chooses an
/// alternative different from the weight-best (primary), this indicates that
/// the WFST's prediction weights were "wrong" for this input. Collecting
/// these corrections enables downstream consumers to:
///
/// 1. **Adjust weights offline**: Feed corrections to the `training.rs` SGD
///    infrastructure to update prediction weights between compilations.
/// 2. **Report weight accuracy**: Language servers can display per-category
///    prediction accuracy statistics.
/// 3. **Detect systematic mispredictions**: If the same category repeatedly
///    generates corrections, its WFST weights need retraining.
#[derive(Debug, Clone, PartialEq)]
pub struct WeightCorrection {
    /// Category where the correction occurred.
    pub category: &'static str,
    /// WFST tropical weight of the primary (best) alternative that was rejected.
    pub primary_weight: f64,
    /// WFST tropical weight of the alternative that was actually selected.
    pub selected_weight: f64,
    /// Number of alternatives that were considered (total candidates including primary).
    pub alternatives_considered: usize,
}

impl WeightCorrection {
    /// Weight delta: how much the prediction was off.
    ///
    /// Positive means the selected alternative had higher weight (worse predicted
    /// rank) than the primary — the WFST underestimated this alternative.
    /// Negative means the selected had lower weight — unusual, indicates the
    /// primary was accepted by weight but a better semantic match existed.
    #[inline]
    pub fn weight_delta(&self) -> f64 {
        self.selected_weight - self.primary_weight
    }

    /// Suggested weight adjustment for the primary rule: increase its weight
    /// (make it less preferred) by a fraction of the delta.
    ///
    /// The adjustment is clamped to `[0.0, max_adjustment]` to prevent
    /// overcorrection from a single event.
    #[inline]
    pub fn primary_adjustment(&self, learning_rate: f64, max_adjustment: f64) -> f64 {
        // If selected had higher weight, primary should also go up (penalize)
        // If selected had lower weight, primary should go down (this is rarer)
        let raw = self.weight_delta().abs() * learning_rate;
        raw.min(max_adjustment).max(0.0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_prediction_wfst_builder_basic() {
        let token_map =
            TokenIdMap::from_names(vec!["Plus", "Minus", "Ident"].into_iter().map(String::from));

        let mut builder = PredictionWfstBuilder::new("Expr", token_map);

        builder.add_action(
            "Plus",
            DispatchAction::Direct {
                rule_label: "Add".to_string(),
                parse_fn: "parse_add".to_string(),
            },
            TropicalWeight::new(0.0),
        );
        builder.add_action(
            "Minus",
            DispatchAction::Direct {
                rule_label: "Sub".to_string(),
                parse_fn: "parse_sub".to_string(),
            },
            TropicalWeight::new(0.0),
        );
        builder.add_action(
            "Ident",
            DispatchAction::Variable { category: "Expr".to_string() },
            TropicalWeight::new(2.0),
        );

        let wfst = builder.build();

        assert_eq!(wfst.num_actions(), 3);
        assert_eq!(wfst.num_states(), 4); // start + 3 final states
        assert_eq!(wfst.category, "Expr");
    }

    #[test]
    fn test_prediction_wfst_predict_deterministic() {
        let token_map = TokenIdMap::from_names(vec!["Plus", "Minus"].into_iter().map(String::from));

        let mut builder = PredictionWfstBuilder::new("Expr", token_map);
        builder.add_action(
            "Plus",
            DispatchAction::Direct {
                rule_label: "Add".to_string(),
                parse_fn: "parse_add".to_string(),
            },
            TropicalWeight::new(0.0),
        );
        builder.add_action(
            "Minus",
            DispatchAction::Direct {
                rule_label: "Sub".to_string(),
                parse_fn: "parse_sub".to_string(),
            },
            TropicalWeight::new(0.0),
        );

        let wfst = builder.build();

        // Plus → exactly one result (Direct Add)
        let results = wfst.predict("Plus");
        assert_eq!(results.len(), 1);
        assert_eq!(results[0].weight, TropicalWeight::new(0.0));
        assert!(
            matches!(&results[0].action, DispatchAction::Direct { rule_label, .. } if rule_label == "Add")
        );

        // Unknown token → empty
        let results = wfst.predict("Star");
        assert!(results.is_empty());
    }

    #[test]
    fn test_prediction_wfst_predict_ambiguous_ordered_by_weight() {
        let token_map = TokenIdMap::from_names(vec!["Ident"].into_iter().map(String::from));

        let mut builder = PredictionWfstBuilder::new("Expr", token_map);

        // Same token, two actions, different weights
        builder.add_action(
            "Ident",
            DispatchAction::Variable { category: "Expr".to_string() },
            TropicalWeight::new(2.0), // higher weight = less preferred
        );
        builder.add_action(
            "Ident",
            DispatchAction::CrossCategory {
                source_category: "Name".to_string(),
                operator_token: "EqEq".to_string(),
                rule_label: "Eq".to_string(),
                needs_backtrack: true,
            },
            TropicalWeight::new(0.5), // lower weight = preferred
        );

        let wfst = builder.build();

        let results = wfst.predict("Ident");
        assert_eq!(results.len(), 2);
        // First result should be the lower-weight (preferred) one
        assert_eq!(results[0].weight, TropicalWeight::new(0.5));
        assert!(matches!(&results[0].action, DispatchAction::CrossCategory { .. }));
        assert_eq!(results[1].weight, TropicalWeight::new(2.0));
        assert!(matches!(&results[1].action, DispatchAction::Variable { .. }));
    }

    #[test]
    fn test_confidence_gap_ambiguous() {
        // A5: Test confidence_gap with two alternatives of different weight
        let token_map = TokenIdMap::from_names(vec!["Ident"].into_iter().map(String::from));

        let mut builder = PredictionWfstBuilder::new("Expr", token_map);
        builder.add_action(
            "Ident",
            DispatchAction::Variable { category: "Expr".to_string() },
            TropicalWeight::new(2.0),
        );
        builder.add_action(
            "Ident",
            DispatchAction::CrossCategory {
                source_category: "Name".to_string(),
                operator_token: "EqEq".to_string(),
                rule_label: "Eq".to_string(),
                needs_backtrack: true,
            },
            TropicalWeight::new(0.5),
        );

        let wfst = builder.build();

        // confidence_gap = second_best - best = 2.0 - 0.5 = 1.5
        let gap = wfst.confidence_gap("Ident");
        assert!((gap - 1.5).abs() < 1e-9, "confidence gap should be 1.5, got {}", gap);
    }

    #[test]
    fn test_confidence_gap_single_alternative() {
        // A5: Single alternative → infinite confidence
        let token_map = TokenIdMap::from_names(vec!["Ident"].into_iter().map(String::from));

        let mut builder = PredictionWfstBuilder::new("Expr", token_map);
        builder.add_action(
            "Ident",
            DispatchAction::Direct { rule_label: "VarRef".to_string(), parse_fn: "parse_varref".to_string() },
            TropicalWeight::new(0.0),
        );

        let wfst = builder.build();
        assert_eq!(wfst.confidence_gap("Ident"), f64::INFINITY);
    }

    #[test]
    fn test_confidence_gap_unknown_token() {
        // A5: Unknown token → infinite confidence (no alternatives)
        let token_map = TokenIdMap::from_names(vec!["Ident"].into_iter().map(String::from));
        let builder = PredictionWfstBuilder::new("Expr", token_map);
        let wfst = builder.build();
        assert_eq!(wfst.confidence_gap("Plus"), f64::INFINITY);
    }

    #[test]
    fn test_confidence_gap_equal_weights() {
        // A5: Equal weights → zero gap (fully ambiguous)
        let token_map = TokenIdMap::from_names(vec!["Ident"].into_iter().map(String::from));

        let mut builder = PredictionWfstBuilder::new("Expr", token_map);
        builder.add_action(
            "Ident",
            DispatchAction::Variable { category: "Expr".to_string() },
            TropicalWeight::new(0.5),
        );
        builder.add_action(
            "Ident",
            DispatchAction::Direct { rule_label: "VarRef".to_string(), parse_fn: "parse_varref".to_string() },
            TropicalWeight::new(0.5),
        );

        let wfst = builder.build();
        assert!((wfst.confidence_gap("Ident")).abs() < 1e-9,
            "equal weights should produce zero gap");
    }

    #[test]
    fn test_compute_action_weight() {
        let first_sets = HashMap::new();
        let overlaps = HashMap::new();

        // Direct → 0.0
        let w = super::compute_action_weight(
            "Plus",
            &DispatchAction::Direct {
                rule_label: "Add".to_string(),
                parse_fn: "parse_add".to_string(),
            },
            "Expr",
            &first_sets,
            &overlaps,
            0,
        );
        assert_eq!(w, TropicalWeight::new(0.0));

        // Variable → 2.0
        let w = super::compute_action_weight(
            "Ident",
            &DispatchAction::Variable { category: "Expr".to_string() },
            "Expr",
            &first_sets,
            &overlaps,
            0,
        );
        assert_eq!(w, TropicalWeight::new(2.0));

        // CrossCategory with backtrack → 0.5
        let w = super::compute_action_weight(
            "Ident",
            &DispatchAction::CrossCategory {
                source_category: "Int".to_string(),
                operator_token: "EqEq".to_string(),
                rule_label: "Eq".to_string(),
                needs_backtrack: true,
            },
            "Bool",
            &first_sets,
            &overlaps,
            0,
        );
        assert_eq!(w, TropicalWeight::new(0.5));

        // CrossCategory without backtrack → 0.0
        let w = super::compute_action_weight(
            "Integer",
            &DispatchAction::CrossCategory {
                source_category: "Int".to_string(),
                operator_token: "EqEq".to_string(),
                rule_label: "Eq".to_string(),
                needs_backtrack: false,
            },
            "Bool",
            &first_sets,
            &overlaps,
            0,
        );
        assert_eq!(w, TropicalWeight::new(0.0));

        // Grouping → 0.0
        let w = super::compute_action_weight(
            "LParen",
            &DispatchAction::Grouping {
                open: "(".to_string(),
                close: ")".to_string(),
            },
            "Expr",
            &first_sets,
            &overlaps,
            0,
        );
        assert_eq!(w, TropicalWeight::new(0.0));
    }

    #[test]
    fn test_generate_weighted_dispatch_empty() {
        let token_map = TokenIdMap::new();
        let wfst = PredictionWfstBuilder::new("Expr", token_map).build();
        assert!(generate_weighted_dispatch(&wfst, "Expr").is_none());
    }

    #[test]
    fn test_generate_weighted_dispatch_produces_comments() {
        let token_map = TokenIdMap::from_names(vec!["Ident"].into_iter().map(String::from));

        let mut builder = PredictionWfstBuilder::new("Expr", token_map);
        builder.add_action(
            "Ident",
            DispatchAction::Variable { category: "Expr".to_string() },
            TropicalWeight::new(2.0),
        );
        builder.add_action(
            "Ident",
            DispatchAction::Direct {
                rule_label: "Var".to_string(),
                parse_fn: "parse_var".to_string(),
            },
            TropicalWeight::new(0.0),
        );

        let wfst = builder.build();
        let code = generate_weighted_dispatch(&wfst, "Expr").expect("should produce code");
        assert!(code.contains("WFST prediction for Expr"));
        assert!(code.contains("ambiguous"));
    }

    // ── Beam pruning tests ────────────────────────────────────────────────

    #[test]
    fn test_beam_pruning_none_is_identity() {
        let token_map = TokenIdMap::from_names(vec!["Ident"].into_iter().map(String::from));

        let mut builder = PredictionWfstBuilder::new("Expr", token_map);
        builder.add_action(
            "Ident",
            DispatchAction::Variable { category: "Expr".to_string() },
            TropicalWeight::new(2.0),
        );
        builder.add_action(
            "Ident",
            DispatchAction::Direct {
                rule_label: "Var".to_string(),
                parse_fn: "parse_var".to_string(),
            },
            TropicalWeight::new(0.0),
        );

        let wfst = builder.build();
        // No beam → predict_pruned == predict
        let all = wfst.predict("Ident");
        let pruned = wfst.predict_pruned("Ident");
        assert_eq!(all.len(), pruned.len());
    }

    #[test]
    fn test_beam_pruning_filters_high_weight() {
        let token_map = TokenIdMap::from_names(vec!["Ident"].into_iter().map(String::from));

        let mut builder = PredictionWfstBuilder::new("Expr", token_map);
        builder.add_action(
            "Ident",
            DispatchAction::Direct {
                rule_label: "Var".to_string(),
                parse_fn: "parse_var".to_string(),
            },
            TropicalWeight::new(0.0), // best
        );
        builder.add_action(
            "Ident",
            DispatchAction::Cast {
                source_category: "Int".to_string(),
                wrapper_label: "IntToExpr".to_string(),
            },
            TropicalWeight::new(0.5), // within beam
        );
        builder.add_action(
            "Ident",
            DispatchAction::Variable { category: "Expr".to_string() },
            TropicalWeight::new(5.0), // beyond beam
        );

        let mut wfst = builder.build();
        wfst.set_beam_width(Some(TropicalWeight::new(1.0)));

        let pruned = wfst.predict_pruned("Ident");
        // beam=1.0, best=0.0, threshold=1.0: only 0.0 and 0.5 pass
        assert_eq!(pruned.len(), 2);
        assert_eq!(pruned[0].weight, TropicalWeight::new(0.0));
        assert_eq!(pruned[1].weight, TropicalWeight::new(0.5));
    }

    #[test]
    fn test_beam_pruning_preserves_best() {
        let token_map = TokenIdMap::from_names(vec!["Plus"].into_iter().map(String::from));

        let mut builder = PredictionWfstBuilder::new("Expr", token_map);
        builder.add_action(
            "Plus",
            DispatchAction::Direct {
                rule_label: "Add".to_string(),
                parse_fn: "parse_add".to_string(),
            },
            TropicalWeight::new(3.0),
        );

        let mut wfst = builder.build();
        wfst.set_beam_width(Some(TropicalWeight::new(0.1)));

        let pruned = wfst.predict_pruned("Plus");
        assert_eq!(pruned.len(), 1, "best action must never be pruned");
    }

    #[test]
    fn test_beam_width_from_builder() {
        let token_map = TokenIdMap::from_names(vec!["Plus"].into_iter().map(String::from));

        let builder =
            PredictionWfstBuilder::new("Expr", token_map).with_beam_width(TropicalWeight::new(2.0));

        let wfst = builder.build();
        assert_eq!(wfst.beam_width(), Some(TropicalWeight::new(2.0)));
    }

    // ── from_flat() / CSR deserialization tests ────────────────────────

    #[test]
    fn test_from_flat_roundtrip() {
        // Build a WFST via the builder, then verify from_flat() reconstructs
        // equivalent structure from the CSR representation.
        let token_map =
            TokenIdMap::from_names(vec!["Plus", "Minus", "Ident"].into_iter().map(String::from));

        let mut builder = PredictionWfstBuilder::new("Expr", token_map);
        builder.add_action(
            "Plus",
            DispatchAction::Direct {
                rule_label: "Add".to_string(),
                parse_fn: "parse_add".to_string(),
            },
            TropicalWeight::new(0.0),
        );
        builder.add_action(
            "Minus",
            DispatchAction::Direct {
                rule_label: "Sub".to_string(),
                parse_fn: "parse_sub".to_string(),
            },
            TropicalWeight::new(1.0),
        );
        builder.add_action(
            "Ident",
            DispatchAction::Variable { category: "Expr".to_string() },
            TropicalWeight::new(2.0),
        );

        let original = builder.build();

        // Flatten into CSR format (mirroring what emit_prediction_wfst_static does)
        let mut transitions_flat: Vec<(u16, u32, f64)> = Vec::new();
        let mut state_offsets: Vec<(usize, usize, bool, f64)> = Vec::new();
        for state in &original.states {
            let start = transitions_flat.len();
            let count = state.transitions.len();
            for t in &state.transitions {
                transitions_flat.push((t.input, t.to, t.weight.value()));
            }
            state_offsets.push((start, count, state.is_final, state.final_weight.value()));
        }

        let mut token_names: Vec<String> = Vec::new();
        for i in 0..original.token_map.len() {
            if let Some(name) = original.token_map.name(i as u16) {
                token_names.push(name.to_string());
            }
        }
        let token_name_refs: Vec<&str> = token_names.iter().map(|s| s.as_str()).collect();

        // Reconstruct from flat
        let reconstructed = PredictionWfst::from_flat(
            "Expr",
            &state_offsets,
            &transitions_flat,
            &token_name_refs,
            None,
        );

        // Verify structural equivalence
        assert_eq!(reconstructed.category, "Expr");
        assert_eq!(reconstructed.num_states(), original.num_states());
        assert_eq!(reconstructed.start, original.start);
        assert_eq!(reconstructed.beam_width, None);

        // Verify prediction still works (weights are preserved)
        let plus_results = reconstructed.predict("Plus");
        assert_eq!(plus_results.len(), 1);
        assert_eq!(plus_results[0].weight, TropicalWeight::new(0.0));

        let ident_results = reconstructed.predict("Ident");
        assert_eq!(ident_results.len(), 1);
        assert_eq!(ident_results[0].weight, TropicalWeight::new(2.0));
    }

    #[test]
    fn test_from_flat_with_beam_width() {
        let state_offsets: &[(usize, usize, bool, f64)] = &[
            (0, 1, false, f64::INFINITY), // start state
            (1, 0, true, 0.0),            // final state
        ];
        let transitions: &[(u16, u32, f64)] = &[
            (0, 1, 0.5), // token 0 → state 1, weight 0.5
        ];
        let token_names: &[&str] = &["Plus"];

        let wfst =
            PredictionWfst::from_flat("Cat", state_offsets, transitions, token_names, Some(1.5));
        assert_eq!(wfst.beam_width(), Some(TropicalWeight::new(1.5)));
        assert_eq!(wfst.num_states(), 2);
        assert_eq!(wfst.num_actions(), 1);
    }

    #[test]
    fn test_from_flat_empty() {
        let wfst = PredictionWfst::from_flat("Empty", &[], &[], &[], None);
        assert_eq!(wfst.num_states(), 0);
        assert_eq!(wfst.num_actions(), 0);
        assert!(wfst.predict("Plus").is_empty());
    }

    // ── with_trained_weights() tests ────────────────────────────────────

    #[cfg(feature = "wfst-log")]
    #[test]
    fn test_with_trained_weights_overrides_matching() {
        let token_map = TokenIdMap::from_names(vec!["Plus", "Ident"].into_iter().map(String::from));

        let mut builder = PredictionWfstBuilder::new("Expr", token_map);
        builder.add_action(
            "Plus",
            DispatchAction::Direct {
                rule_label: "Add".to_string(),
                parse_fn: "parse_add".to_string(),
            },
            TropicalWeight::new(0.0), // original weight
        );
        builder.add_action(
            "Ident",
            DispatchAction::Variable { category: "Expr".to_string() },
            TropicalWeight::new(2.0), // original weight
        );

        let mut wfst = builder.build();

        // Create a trained model that overrides "Add" weight
        let mut rule_weights = std::collections::HashMap::new();
        rule_weights.insert("Add".to_string(), 0.3);
        // "NonExistent" should be silently ignored
        rule_weights.insert("NonExistent".to_string(), 99.0);

        let model = crate::training::TrainedModel {
            rule_weights,
            recommended_beam_width: None,
            recovery_weights: None,
            metadata: crate::training::TrainedModelMetadata {
                epochs: 10,
                final_loss: 0.01,
                converged: true,
                num_examples: 100,
                learning_rate: 0.01,
            },
        };

        wfst.with_trained_weights(&model);

        // "Plus" → "Add" should now have weight 0.3 (trained)
        let plus_results = wfst.predict("Plus");
        assert_eq!(plus_results.len(), 1);
        assert_eq!(plus_results[0].weight, TropicalWeight::new(0.3));

        // "Ident" → Variable has no matching trained weight, stays at 2.0
        // (Variable action doesn't match any rule_label in the model)
    }

    #[cfg(feature = "wfst-log")]
    #[test]
    fn test_with_trained_weights_updates_transitions() {
        let token_map = TokenIdMap::from_names(vec!["Plus"].into_iter().map(String::from));

        let mut builder = PredictionWfstBuilder::new("Expr", token_map);
        builder.add_action(
            "Plus",
            DispatchAction::Direct {
                rule_label: "Add".to_string(),
                parse_fn: "parse_add".to_string(),
            },
            TropicalWeight::new(5.0),
        );

        let mut wfst = builder.build();

        let mut rule_weights = std::collections::HashMap::new();
        rule_weights.insert("Add".to_string(), 0.1);

        let model = crate::training::TrainedModel {
            rule_weights,
            recommended_beam_width: None,
            recovery_weights: None,
            metadata: crate::training::TrainedModelMetadata {
                epochs: 5,
                final_loss: 0.05,
                converged: true,
                num_examples: 50,
                learning_rate: 0.01,
            },
        };

        wfst.with_trained_weights(&model);

        // Verify the transition weight was also updated (not just the action)
        let start_state = &wfst.states[wfst.start as usize];
        assert_eq!(start_state.transitions.len(), 1);
        assert_eq!(start_state.transitions[0].weight, TropicalWeight::new(0.1));
    }

    #[test]
    fn test_beam_width_from_language_spec() {
        use crate::binding_power::Associativity;
        use crate::{BeamWidthConfig, CategorySpec, LanguageSpec, RuleSpecInput, SyntaxItemSpec};

        // Create a minimal LanguageSpec with beam_width set
        let spec = LanguageSpec::with_options(
            "TestLang".to_string(),
            vec![CategorySpec {
                name: "Expr".to_string(),
                native_type: None,
                is_primary: true,
            }],
            vec![RuleSpecInput {
                label: "Lit".to_string(),
                category: "Expr".to_string(),
                syntax: vec![SyntaxItemSpec::Terminal("0".to_string())],
                associativity: Associativity::Left,
                prefix_precedence: None,
                has_rust_code: false,
                rust_code: None,
                eval_mode: None,
                source_location: None,
            }],
            BeamWidthConfig::Explicit(1.5),          // beam_width
            None,                                    // log_semiring_model_path
            crate::LiteralPatterns::default(),       // literal_patterns
        );

        assert_eq!(spec.beam_width, BeamWidthConfig::Explicit(1.5));
        assert!(spec.log_semiring_model_path.is_none());

        // Verify beam_width can be converted to TropicalWeight for WFST construction
        let beam = spec.beam_width.to_option().map(TropicalWeight::new);
        assert_eq!(beam, Some(TropicalWeight::new(1.5)));
    }

    // ── union() tests ─────────────────────────────────────────────────

    #[test]
    fn test_union_disjoint_tokens() {
        // WFST A: Plus → Add
        let token_map_a = TokenIdMap::from_names(vec!["Plus"].into_iter().map(String::from));
        let mut builder_a = PredictionWfstBuilder::new("Expr", token_map_a);
        builder_a.add_action(
            "Plus",
            DispatchAction::Direct {
                rule_label: "Add".to_string(),
                parse_fn: "parse_add".to_string(),
            },
            TropicalWeight::new(0.0),
        );
        let mut wfst_a = builder_a.build();

        // WFST B: Minus → Sub
        let token_map_b = TokenIdMap::from_names(vec!["Minus"].into_iter().map(String::from));
        let mut builder_b = PredictionWfstBuilder::new("Expr", token_map_b);
        builder_b.add_action(
            "Minus",
            DispatchAction::Direct {
                rule_label: "Sub".to_string(),
                parse_fn: "parse_sub".to_string(),
            },
            TropicalWeight::new(0.0),
        );
        let wfst_b = builder_b.build();

        assert_eq!(wfst_a.num_actions(), 1);
        assert_eq!(wfst_a.num_states(), 2);

        wfst_a.union(&wfst_b);

        // After union: should have both actions
        assert_eq!(wfst_a.num_actions(), 2);
        assert_eq!(wfst_a.num_states(), 3); // start + 2 final states

        // Both tokens should be predictable
        let plus_results = wfst_a.predict("Plus");
        assert_eq!(plus_results.len(), 1);
        assert_eq!(plus_results[0].weight, TropicalWeight::new(0.0));

        let minus_results = wfst_a.predict("Minus");
        assert_eq!(minus_results.len(), 1);
        assert_eq!(minus_results[0].weight, TropicalWeight::new(0.0));
    }

    #[test]
    fn test_union_overlapping_tokens() {
        // WFST A: Ident → Variable (w=2.0)
        let token_map_a = TokenIdMap::from_names(vec!["Ident"].into_iter().map(String::from));
        let mut builder_a = PredictionWfstBuilder::new("Expr", token_map_a);
        builder_a.add_action(
            "Ident",
            DispatchAction::Variable { category: "Expr".to_string() },
            TropicalWeight::new(2.0),
        );
        let mut wfst_a = builder_a.build();

        // WFST B: Ident → CrossCategory (w=0.5)
        let token_map_b = TokenIdMap::from_names(vec!["Ident"].into_iter().map(String::from));
        let mut builder_b = PredictionWfstBuilder::new("Expr", token_map_b);
        builder_b.add_action(
            "Ident",
            DispatchAction::CrossCategory {
                source_category: "Name".to_string(),
                operator_token: "EqEq".to_string(),
                rule_label: "Eq".to_string(),
                needs_backtrack: true,
            },
            TropicalWeight::new(0.5),
        );
        let wfst_b = builder_b.build();

        wfst_a.union(&wfst_b);

        // After union: Ident should have two alternatives, sorted by weight
        let results = wfst_a.predict("Ident");
        assert_eq!(results.len(), 2);
        // Lower weight first (0.5 < 2.0)
        assert_eq!(results[0].weight, TropicalWeight::new(0.5));
        assert!(matches!(&results[0].action, DispatchAction::CrossCategory { .. }));
        assert_eq!(results[1].weight, TropicalWeight::new(2.0));
        assert!(matches!(&results[1].action, DispatchAction::Variable { .. }));
    }

    #[test]
    fn test_union_preserves_beam_width() {
        let token_map_a = TokenIdMap::from_names(vec!["Plus"].into_iter().map(String::from));
        let builder_a = PredictionWfstBuilder::new("Expr", token_map_a)
            .with_beam_width(TropicalWeight::new(1.5));
        let mut wfst_a = builder_a.build();

        let token_map_b = TokenIdMap::from_names(vec!["Minus"].into_iter().map(String::from));
        let builder_b = PredictionWfstBuilder::new("Expr", token_map_b)
            .with_beam_width(TropicalWeight::new(2.0));
        let wfst_b = builder_b.build();

        wfst_a.union(&wfst_b);

        // Self's beam width is preserved
        assert_eq!(wfst_a.beam_width(), Some(TropicalWeight::new(1.5)));
    }

    #[test]
    fn test_union_empty_other() {
        let token_map = TokenIdMap::from_names(vec!["Plus"].into_iter().map(String::from));
        let mut builder = PredictionWfstBuilder::new("Expr", token_map);
        builder.add_action(
            "Plus",
            DispatchAction::Direct {
                rule_label: "Add".to_string(),
                parse_fn: "parse_add".to_string(),
            },
            TropicalWeight::new(0.0),
        );
        let mut wfst = builder.build();

        let empty_map = TokenIdMap::new();
        let empty_wfst = PredictionWfstBuilder::new("Expr", empty_map).build();

        let original_actions = wfst.num_actions();
        let original_states = wfst.num_states();

        wfst.union(&empty_wfst);

        // No change
        assert_eq!(wfst.num_actions(), original_actions);
        assert_eq!(wfst.num_states(), original_states);
    }

    // ── B3: minimize() tests ──────────────────────────────────────────

    #[test]
    fn test_minimize_merges_all_simple_finals() {
        // In the two-state architecture, transition weights live on edges from
        // start, not on final states. All final states have identical properties
        // (is_final=true, final_weight=0.0, no outgoing transitions), so they
        // all share the same signature and merge into one.
        let token_map =
            TokenIdMap::from_names(vec!["Plus", "Minus", "Star"].into_iter().map(String::from));
        let mut builder = PredictionWfstBuilder::new("Expr", token_map);
        builder.add_action(
            "Plus",
            DispatchAction::Direct {
                rule_label: "Add".to_string(),
                parse_fn: "parse_add".to_string(),
            },
            TropicalWeight::new(0.0),
        );
        builder.add_action(
            "Minus",
            DispatchAction::Direct {
                rule_label: "Sub".to_string(),
                parse_fn: "parse_sub".to_string(),
            },
            TropicalWeight::new(1.0),
        );
        builder.add_action(
            "Star",
            DispatchAction::Direct {
                rule_label: "Mul".to_string(),
                parse_fn: "parse_mul".to_string(),
            },
            TropicalWeight::new(2.0),
        );

        let mut wfst = builder.build();
        assert_eq!(wfst.num_states(), 4); // start + 3 finals

        let removed = wfst.minimize();
        // All 3 finals have identical signatures → merge to 1
        assert_eq!(removed, 2);
        assert_eq!(wfst.num_states(), 2); // start + 1 merged final

        // Prediction still works — transition weights preserved
        assert_eq!(wfst.predict("Plus").len(), 1);
        assert_eq!(wfst.predict("Plus")[0].weight, TropicalWeight::new(0.0));
        assert_eq!(wfst.predict("Minus").len(), 1);
        assert_eq!(wfst.predict("Minus")[0].weight, TropicalWeight::new(1.0));
        assert_eq!(wfst.predict("Star").len(), 1);
        assert_eq!(wfst.predict("Star")[0].weight, TropicalWeight::new(2.0));
    }

    #[test]
    fn test_minimize_merges_identical_finals_after_union() {
        // Two WFSTs with different tokens but same final-state properties.
        // After union, the final states are duplicated. They have different
        // action_idx values, so their signatures differ. However, if we
        // construct a scenario with truly identical signatures (same action_idx,
        // same target, same weight), they should merge.

        // Build a WFST with two disjoint tokens
        let token_map =
            TokenIdMap::from_names(vec!["Plus", "Minus"].into_iter().map(String::from));
        let mut builder = PredictionWfstBuilder::new("Expr", token_map);
        builder.add_action(
            "Plus",
            DispatchAction::Direct {
                rule_label: "Add".to_string(),
                parse_fn: "parse_add".to_string(),
            },
            TropicalWeight::new(0.0),
        );
        builder.add_action(
            "Minus",
            DispatchAction::Direct {
                rule_label: "Sub".to_string(),
                parse_fn: "parse_sub".to_string(),
            },
            TropicalWeight::new(0.0),
        );
        let mut wfst = builder.build();

        // Before minimize: start + 2 final states (action_idx 0 and 1)
        assert_eq!(wfst.num_states(), 3);

        // The final states have the same (is_final, final_weight) but different
        // action_idx in their parent's transitions. The final states themselves
        // have no outgoing transitions, so their own signatures are:
        //   state 1: (true, 0.0_bits, [])
        //   state 2: (true, 0.0_bits, [])
        // These ARE identical → they should merge.
        let removed = wfst.minimize();
        assert_eq!(removed, 1, "one duplicate final state should be removed");
        assert_eq!(wfst.num_states(), 2); // start + 1 merged final

        // Prediction still works — both tokens point to the same final state
        let plus = wfst.predict("Plus");
        assert_eq!(plus.len(), 1);
        assert_eq!(plus[0].weight, TropicalWeight::new(0.0));

        let minus = wfst.predict("Minus");
        assert_eq!(minus.len(), 1);
        assert_eq!(minus[0].weight, TropicalWeight::new(0.0));
    }

    #[test]
    fn test_minimize_after_union_with_overlapping_tokens() {
        // Union creates additional final states; minimize should merge equivalent ones
        let token_map_a = TokenIdMap::from_names(vec!["Ident"].into_iter().map(String::from));
        let mut builder_a = PredictionWfstBuilder::new("Expr", token_map_a);
        builder_a.add_action(
            "Ident",
            DispatchAction::Variable { category: "Expr".to_string() },
            TropicalWeight::new(2.0),
        );
        let mut wfst = builder_a.build();
        assert_eq!(wfst.num_states(), 2); // start + 1 final

        // Union with another WFST that also maps Ident
        let token_map_b = TokenIdMap::from_names(vec!["Ident"].into_iter().map(String::from));
        let mut builder_b = PredictionWfstBuilder::new("Expr", token_map_b);
        builder_b.add_action(
            "Ident",
            DispatchAction::CrossCategory {
                source_category: "Name".to_string(),
                operator_token: "EqEq".to_string(),
                rule_label: "Eq".to_string(),
                needs_backtrack: true,
            },
            TropicalWeight::new(0.5),
        );
        let wfst_b = builder_b.build();
        wfst.union(&wfst_b);

        // After union: start + 2 final states (different weights: 2.0 and 0.5)
        assert_eq!(wfst.num_states(), 3);

        // Final state weights differ (one has final_weight from TropicalWeight::one()
        // which is 0.0, so they may actually share the same signature).
        // Both final states: is_final=true, final_weight=TropicalWeight::one()=0.0,
        // no outgoing transitions → identical signatures → merge to 1.
        let removed = wfst.minimize();
        assert_eq!(removed, 1);
        assert_eq!(wfst.num_states(), 2);

        // Prediction preserves both alternatives for Ident
        let results = wfst.predict("Ident");
        assert_eq!(results.len(), 2);
        assert_eq!(results[0].weight, TropicalWeight::new(0.5));
        assert_eq!(results[1].weight, TropicalWeight::new(2.0));
    }

    #[test]
    fn test_minimize_empty_wfst() {
        let token_map = TokenIdMap::new();
        let mut wfst = PredictionWfstBuilder::new("Empty", token_map).build();
        // Single start state, no finals
        let removed = wfst.minimize();
        assert_eq!(removed, 0);
    }

    #[test]
    fn test_minimize_single_state() {
        // A WFST with only a start state and no actions
        let token_map = TokenIdMap::new();
        let mut wfst = PredictionWfstBuilder::new("Lone", token_map).build();
        assert_eq!(wfst.num_states(), 1);
        let removed = wfst.minimize();
        assert_eq!(removed, 0);
        assert_eq!(wfst.num_states(), 1);
    }

    #[test]
    fn test_minimize_preserves_beam_width() {
        let token_map = TokenIdMap::from_names(vec!["A", "B"].into_iter().map(String::from));
        let mut builder = PredictionWfstBuilder::new("Cat", token_map);
        builder.add_action(
            "A",
            DispatchAction::Direct {
                rule_label: "R1".to_string(),
                parse_fn: "p1".to_string(),
            },
            TropicalWeight::new(0.0),
        );
        builder.add_action(
            "B",
            DispatchAction::Direct {
                rule_label: "R2".to_string(),
                parse_fn: "p2".to_string(),
            },
            TropicalWeight::new(0.0),
        );
        let mut wfst = builder
            .with_beam_width(TropicalWeight::new(1.5))
            .build();

        wfst.minimize();
        assert_eq!(wfst.beam_width(), Some(TropicalWeight::new(1.5)));
    }

    #[test]
    fn test_minimize_large_union_many_duplicates() {
        // Simulate a larger scenario: 10 tokens all leading to final states
        // with the same weight — all 10 finals should merge to 1.
        let names: Vec<String> = (0..10).map(|i| format!("T{}", i)).collect();
        let token_map = TokenIdMap::from_names(names.iter().cloned());
        let mut builder = PredictionWfstBuilder::new("Big", token_map);

        for name in &names {
            builder.add_action(
                name,
                DispatchAction::Direct {
                    rule_label: format!("R_{}", name),
                    parse_fn: format!("p_{}", name.to_lowercase()),
                },
                TropicalWeight::new(0.0),
            );
        }

        let mut wfst = builder.build();
        assert_eq!(wfst.num_states(), 11); // start + 10 finals

        let removed = wfst.minimize();
        // All 10 finals have identical signatures → merge to 1
        assert_eq!(removed, 9);
        assert_eq!(wfst.num_states(), 2); // start + 1 merged final

        // All 10 tokens still predict correctly
        for name in &names {
            let results = wfst.predict(name);
            assert_eq!(results.len(), 1, "token {} should still predict", name);
            assert_eq!(results[0].weight, TropicalWeight::new(0.0));
        }
    }

    #[test]
    fn test_minimize_mixed_weights_partial_merge() {
        // 4 tokens: 2 with weight 0.0, 2 with weight 1.0
        // Should merge to 2 final states
        let token_map =
            TokenIdMap::from_names(vec!["A", "B", "C", "D"].into_iter().map(String::from));
        let mut builder = PredictionWfstBuilder::new("Mix", token_map);
        builder.add_action(
            "A",
            DispatchAction::Direct {
                rule_label: "R1".to_string(),
                parse_fn: "p1".to_string(),
            },
            TropicalWeight::new(0.0),
        );
        builder.add_action(
            "B",
            DispatchAction::Direct {
                rule_label: "R2".to_string(),
                parse_fn: "p2".to_string(),
            },
            TropicalWeight::new(1.0),
        );
        builder.add_action(
            "C",
            DispatchAction::Direct {
                rule_label: "R3".to_string(),
                parse_fn: "p3".to_string(),
            },
            TropicalWeight::new(0.0),
        );
        builder.add_action(
            "D",
            DispatchAction::Direct {
                rule_label: "R4".to_string(),
                parse_fn: "p4".to_string(),
            },
            TropicalWeight::new(1.0),
        );

        let mut wfst = builder.build();
        assert_eq!(wfst.num_states(), 5); // start + 4 finals

        let removed = wfst.minimize();
        // Finals: 2 groups (weight 0.0 and weight 1.0)
        // Wait — final_weight is TropicalWeight::one() (= 0.0) for all finals,
        // since the weight is on the *transition*, not the final state.
        // So all 4 finals have identical signatures → merge to 1
        assert_eq!(removed, 3);
        assert_eq!(wfst.num_states(), 2);

        // All tokens still work
        assert_eq!(wfst.predict("A")[0].weight, TropicalWeight::new(0.0));
        assert_eq!(wfst.predict("B")[0].weight, TropicalWeight::new(1.0));
        assert_eq!(wfst.predict("C")[0].weight, TropicalWeight::new(0.0));
        assert_eq!(wfst.predict("D")[0].weight, TropicalWeight::new(1.0));
    }

    // ── C1: WeightCorrection tests ──

    #[test]
    fn test_c1_weight_correction_delta_positive() {
        // C1: When a higher-weight (worse predicted rank) alternative is selected,
        // the delta should be positive.
        let c = WeightCorrection {
            category: "TestGrammar",
            primary_weight: 0.0,
            selected_weight: 1.5,
            alternatives_considered: 3,
        };
        assert_eq!(c.weight_delta(), 1.5);
    }

    #[test]
    fn test_c1_weight_correction_delta_negative() {
        // C1: Negative delta when selected had lower weight than primary.
        // This can happen when the weight-best overall was rejected but a
        // lower-weight accepting alternative was found in the spillover.
        let c = WeightCorrection {
            category: "TestGrammar",
            primary_weight: 2.0,
            selected_weight: 0.5,
            alternatives_considered: 2,
        };
        assert_eq!(c.weight_delta(), -1.5);
    }

    #[test]
    fn test_c1_weight_correction_delta_zero() {
        // C1: Zero delta means primary was also the selected (no correction needed).
        let c = WeightCorrection {
            category: "TestGrammar",
            primary_weight: 0.5,
            selected_weight: 0.5,
            alternatives_considered: 2,
        };
        assert_eq!(c.weight_delta(), 0.0);
    }

    #[test]
    fn test_c1_primary_adjustment_clamped() {
        // C1: primary_adjustment should be clamped to [0, max_adjustment].
        let c = WeightCorrection {
            category: "TestGrammar",
            primary_weight: 0.0,
            selected_weight: 10.0,
            alternatives_considered: 5,
        };
        // learning_rate=0.1, max=0.5 → raw=1.0, clamped to 0.5
        assert_eq!(c.primary_adjustment(0.1, 0.5), 0.5);
        // learning_rate=0.01, max=0.5 → raw=0.1, unclamped
        assert!((c.primary_adjustment(0.01, 0.5) - 0.1).abs() < 1e-10);
    }

    #[test]
    fn test_c1_primary_adjustment_zero_delta() {
        // C1: Zero delta → zero adjustment.
        let c = WeightCorrection {
            category: "TestGrammar",
            primary_weight: 1.0,
            selected_weight: 1.0,
            alternatives_considered: 2,
        };
        assert_eq!(c.primary_adjustment(0.1, 0.5), 0.0);
    }

    // ── C2: Position-aware NFA disambiguation tests ──

    #[test]
    fn test_c2_position_weight_penalty_value() {
        // C2: The position weight penalty constant should be positive.
        assert!(POSITION_WEIGHT_PENALTY > 0.0, "POSITION_WEIGHT_PENALTY should be positive");
    }

    #[test]
    fn test_c2_position_weight_adjustment_same_position() {
        // C2: Same position → zero penalty, adjusted weight equals original.
        let pos_diff: usize = 0;
        let original_weight = 1.5;
        let adjusted = original_weight + pos_diff as f64 * POSITION_WEIGHT_PENALTY;
        assert_eq!(adjusted, original_weight, "same position should have no penalty");
    }

    #[test]
    fn test_c2_position_weight_adjustment_longer_match() {
        // C2: Longer match (positive pos_diff) → penalty added.
        let primary_pos: usize = 5;
        let alt_pos: usize = 7;
        let pos_diff = (alt_pos as isize - primary_pos as isize).unsigned_abs();
        let original_weight = 1.0;
        let adjusted = original_weight + pos_diff as f64 * POSITION_WEIGHT_PENALTY;
        // pos_diff = 2, penalty = 2 * 0.5 = 1.0
        assert_eq!(adjusted, 2.0, "longer match penalty: 1.0 + 2*0.5 = 2.0");
    }

    #[test]
    fn test_c2_position_weight_adjustment_shorter_match() {
        // C2: Shorter match (negative pos_diff) → penalty added symmetrically.
        let primary_pos: usize = 7;
        let alt_pos: usize = 5;
        let pos_diff = (alt_pos as isize - primary_pos as isize).unsigned_abs();
        let original_weight = 0.5;
        let adjusted = original_weight + pos_diff as f64 * POSITION_WEIGHT_PENALTY;
        // pos_diff = 2, penalty = 2 * 0.5 = 1.0
        assert_eq!(adjusted, 1.5, "shorter match penalty: 0.5 + 2*0.5 = 1.5");
    }

    // ── B6: Runtime WFST query tests ──

    #[test]
    fn test_b6_valid_continuations_basic() {
        // B6: valid_continuations returns all tokens with dispatch actions
        let token_map = TokenIdMap::from_names(vec!["A".to_string(), "B".to_string(), "C".to_string()].into_iter());
        let mut builder = PredictionWfstBuilder::new("Expr", token_map);
        builder.add_action("A", DispatchAction::Direct { rule_label: "R1".into(), parse_fn: "p1".into() }, TropicalWeight::new(1.0));
        builder.add_action("B", DispatchAction::Direct { rule_label: "R2".into(), parse_fn: "p2".into() }, TropicalWeight::new(0.0));
        let wfst = builder.build();

        let conts = wfst.valid_continuations();
        assert_eq!(conts.len(), 2, "expected 2 valid continuations, got {}", conts.len());
        // Sorted by weight: B(0.0) before A(1.0)
        assert_eq!(conts[0].0, "B");
        assert_eq!(conts[0].1, TropicalWeight::new(0.0));
        assert_eq!(conts[1].0, "A");
        assert_eq!(conts[1].1, TropicalWeight::new(1.0));
    }

    #[test]
    fn test_b6_valid_continuations_empty() {
        // B6: Empty WFST → no valid continuations
        let token_map = TokenIdMap::from_names(std::iter::empty::<String>());
        let builder = PredictionWfstBuilder::new("X", token_map);
        let wfst = builder.build();

        let conts = wfst.valid_continuations();
        assert!(conts.is_empty());
    }

    #[test]
    fn test_b6_has_valid_dispatch() {
        // B6: has_valid_dispatch checks if token is recognized
        let token_map = TokenIdMap::from_names(vec!["A".to_string(), "B".to_string()].into_iter());
        let mut builder = PredictionWfstBuilder::new("Expr", token_map);
        builder.add_action("A", DispatchAction::Direct { rule_label: "R1".into(), parse_fn: "p1".into() }, TropicalWeight::new(0.0));
        let wfst = builder.build();

        assert!(wfst.has_valid_dispatch("A"), "A should have valid dispatch");
        assert!(!wfst.has_valid_dispatch("B"), "B should have no dispatch (no action added)");
        assert!(!wfst.has_valid_dispatch("C"), "C should have no dispatch (unknown token)");
    }

    #[test]
    fn test_b6_parse_progress() {
        // B6: parse_progress returns 0.0 at start, 1.0 at final
        let token_map = TokenIdMap::from_names(vec!["A".to_string()].into_iter());
        let mut builder = PredictionWfstBuilder::new("Expr", token_map);
        builder.add_action("A", DispatchAction::Direct { rule_label: "R1".into(), parse_fn: "p1".into() }, TropicalWeight::new(0.0));
        let wfst = builder.build();

        // Start state = 0
        assert_eq!(wfst.parse_progress(0), 0.0);
        // Final state = 1 (star-shaped: start → accept)
        assert_eq!(wfst.parse_progress(1), 1.0);
    }

    #[test]
    fn test_b6_parse_progress_empty() {
        // B6: Empty WFST → progress = 0.0
        let token_map = TokenIdMap::from_names(std::iter::empty::<String>());
        let builder = PredictionWfstBuilder::new("X", token_map);
        let wfst = builder.build();

        assert_eq!(wfst.parse_progress(0), 0.0);
    }

    // ── A7: Entropy-based beam width tests ──

    #[test]
    fn test_a7_entropy_to_beam_width_below_threshold() {
        // A7: Entropy below threshold → no beam (deterministic dispatch)
        let beam = entropy_to_beam_width(0.3, 1.0, 0.5, 0.5, 10.0);
        assert!(beam.is_none(), "entropy below threshold should produce no beam");
    }

    #[test]
    fn test_a7_entropy_to_beam_width_at_threshold() {
        // A7: Entropy exactly at threshold → no beam
        let beam = entropy_to_beam_width(0.5, 1.0, 0.5, 0.5, 10.0);
        assert!(beam.is_none(), "entropy at threshold should produce no beam");
    }

    #[test]
    fn test_a7_entropy_to_beam_width_above_threshold() {
        // A7: Entropy above threshold → base + scale * (entropy - threshold)
        let beam = entropy_to_beam_width(2.5, 1.0, 0.5, 0.5, 10.0);
        // beam = 1.0 + 0.5 * (2.5 - 0.5) = 1.0 + 1.0 = 2.0
        let expected = 2.0;
        assert!((beam.expect("should have beam") - expected).abs() < 1e-10,
            "expected beam={}, got {:?}", expected, beam);
    }

    #[test]
    fn test_a7_entropy_to_beam_width_capped() {
        // A7: Very high entropy → capped at max_beam
        let beam = entropy_to_beam_width(100.0, 1.0, 0.5, 0.5, 10.0);
        assert_eq!(beam, Some(10.0), "beam should be capped at max_beam");
    }

    #[test]
    fn test_a7_entropy_to_beam_width_constants() {
        // A7: Default constants produce reasonable results
        let beam = entropy_to_beam_width(3.0, ENTROPY_BEAM_BASE, ENTROPY_BEAM_SCALE,
            ENTROPY_BEAM_LOW_THRESHOLD, ENTROPY_BEAM_MAX);
        // beam = 1.0 + 0.5 * (3.0 - 0.5) = 1.0 + 1.25 = 2.25
        assert!((beam.expect("should have beam") - 2.25).abs() < 1e-10);
    }

    #[cfg(feature = "wfst-log")]
    #[test]
    fn test_a7_compute_entropy_single_action() {
        // A7: Single deterministic action → entropy = 0 (no uncertainty)
        let token_map = TokenIdMap::from_names(vec!["A".to_string()].into_iter());
        let mut builder = PredictionWfstBuilder::new("X", token_map);
        builder.add_action(
            "A",
            DispatchAction::Direct {
                rule_label: "R1".to_string(),
                parse_fn: "p1".to_string(),
            },
            TropicalWeight::new(0.0),
        );
        let wfst = builder.build();

        let (entropy_nats, entropy_bits) = wfst.compute_entropy();
        // Single action with weight 0 → deterministic, entropy ≈ 0
        assert!(entropy_nats.abs() < 0.1,
            "single action should have near-zero entropy, got {}", entropy_nats);
        assert!(entropy_bits.abs() < 0.1,
            "single action should have near-zero bits, got {}", entropy_bits);
    }

    #[cfg(feature = "wfst-log")]
    #[test]
    fn test_a7_compute_entropy_uniform_two_actions() {
        // A7: Two actions with equal weight → entropy = ln(2) nats ≈ 1 bit
        let token_map = TokenIdMap::from_names(vec!["A".to_string(), "B".to_string()].into_iter());
        let mut builder = PredictionWfstBuilder::new("X", token_map);
        builder.add_action(
            "A",
            DispatchAction::Direct {
                rule_label: "R1".to_string(),
                parse_fn: "p1".to_string(),
            },
            TropicalWeight::new(0.0),
        );
        builder.add_action(
            "B",
            DispatchAction::Direct {
                rule_label: "R2".to_string(),
                parse_fn: "p2".to_string(),
            },
            TropicalWeight::new(0.0),
        );
        let wfst = builder.build();

        let (_entropy_nats, entropy_bits) = wfst.compute_entropy();
        // Two equal-weight paths: H = ln(2) ≈ 0.693 nats ≈ 1.0 bits
        assert!((entropy_bits - 1.0).abs() < 0.15,
            "two equal actions should have ~1 bit entropy, got {}", entropy_bits);
    }

    #[cfg(feature = "wfst-log")]
    #[test]
    fn test_a7_compute_entropy_skewed_actions() {
        // A7: One dominant action (weight 0.0) vs one unlikely (weight 5.0)
        // → entropy should be low (near-deterministic)
        let token_map = TokenIdMap::from_names(vec!["A".to_string(), "B".to_string()].into_iter());
        let mut builder = PredictionWfstBuilder::new("X", token_map);
        builder.add_action(
            "A",
            DispatchAction::Direct {
                rule_label: "R1".to_string(),
                parse_fn: "p1".to_string(),
            },
            TropicalWeight::new(0.0),
        );
        builder.add_action(
            "B",
            DispatchAction::Direct {
                rule_label: "R2".to_string(),
                parse_fn: "p2".to_string(),
            },
            TropicalWeight::new(5.0),
        );
        let wfst = builder.build();

        let (_entropy_nats, entropy_bits) = wfst.compute_entropy();
        // Heavily skewed → entropy << 1 bit
        assert!(entropy_bits < 0.5,
            "skewed distribution should have low entropy, got {}", entropy_bits);
    }

    #[cfg(feature = "wfst-log")]
    #[test]
    fn test_a7_compute_entropy_empty_wfst() {
        // A7: Empty WFST → entropy = 0
        let token_map = TokenIdMap::from_names(std::iter::empty::<String>());
        let builder = PredictionWfstBuilder::new("X", token_map);
        let wfst = builder.build();

        let (entropy_nats, _entropy_bits) = wfst.compute_entropy();
        assert!(entropy_nats.abs() < 1e-10, "empty WFST should have zero entropy");
    }

    // ── D3: DOT visualization tests ────────────────────────────────────

    #[test]
    fn test_d3_prediction_wfst_dot_basic() {
        // D3: A simple 2-action WFST should produce valid DOT with correct structure
        let token_map = TokenIdMap::from_names(
            vec!["Ident".to_string(), "LParen".to_string()].into_iter(),
        );
        let mut builder = PredictionWfstBuilder::new("Proc", token_map);
        builder.add_action(
            "Ident",
            DispatchAction::Direct {
                rule_label: "PInput".to_string(),
                parse_fn: "parse_pinput".to_string(),
            },
            TropicalWeight::new(0.0),
        );
        builder.add_action(
            "LParen",
            DispatchAction::Direct {
                rule_label: "PSend".to_string(),
                parse_fn: "parse_psend".to_string(),
            },
            TropicalWeight::new(0.0),
        );
        let wfst = builder.build();
        let dot = wfst.to_dot();

        assert!(dot.contains("digraph PredictionWfst_Proc"), "should have digraph header");
        assert!(dot.contains("rankdir=LR"), "should be left-to-right layout");
        assert!(dot.contains("(start)"), "should mark start state");
        assert!(dot.contains("(final)"), "should mark final state(s)");
        assert!(dot.contains("Ident"), "should label Ident token");
        assert!(dot.contains("LParen"), "should label LParen token");
        assert!(dot.contains("PInput"), "should label PInput action");
        assert!(dot.contains("PSend"), "should label PSend action");
        assert!(dot.contains("color=black"), "weight=0.0 edges should be black");
        assert!(dot.ends_with("}\n"), "should end with closing brace");
    }

    #[test]
    fn test_d3_prediction_wfst_dot_ambiguous_red_edges() {
        // D3: Ambiguous transitions (weight > 0.0) should be colored red
        let token_map = TokenIdMap::from_names(
            vec!["Ident".to_string()].into_iter(),
        );
        let mut builder = PredictionWfstBuilder::new("Expr", token_map);
        builder.add_action(
            "Ident",
            DispatchAction::Direct {
                rule_label: "R1".to_string(),
                parse_fn: "p1".to_string(),
            },
            TropicalWeight::new(0.0),
        );
        builder.add_action(
            "Ident",
            DispatchAction::Direct {
                rule_label: "R2".to_string(),
                parse_fn: "p2".to_string(),
            },
            TropicalWeight::new(1.0),
        );
        let wfst = builder.build();
        let dot = wfst.to_dot();

        assert!(dot.contains("color=red"), "ambiguous edge (weight=1.0) should be red");
        assert!(dot.contains("color=black"), "deterministic edge (weight=0.0) should be black");
        assert!(dot.contains("R1"), "should contain first rule label");
        assert!(dot.contains("R2"), "should contain second rule label");
    }

    #[test]
    fn test_d3_prediction_wfst_dot_empty() {
        // D3: Empty WFST should still produce valid DOT
        let token_map = TokenIdMap::from_names(std::iter::empty::<String>());
        let builder = PredictionWfstBuilder::new("Empty", token_map);
        let wfst = builder.build();
        let dot = wfst.to_dot();

        assert!(dot.contains("digraph PredictionWfst_Empty"));
        assert!(dot.contains("(start)"));
        // Should have at least the start state node
        assert!(dot.contains("S0"));
    }

    #[test]
    fn test_d3_prediction_wfst_dot_weight_format() {
        // D3: Weights should be formatted with 2 decimal places
        let token_map = TokenIdMap::from_names(
            vec!["X".to_string()].into_iter(),
        );
        let mut builder = PredictionWfstBuilder::new("W", token_map);
        builder.add_action(
            "X",
            DispatchAction::Direct {
                rule_label: "Rx".to_string(),
                parse_fn: "px".to_string(),
            },
            TropicalWeight::new(2.5),
        );
        let wfst = builder.build();
        let dot = wfst.to_dot();

        assert!(dot.contains("[2.50]"), "weight should be formatted as [2.50], got:\n{}", dot);
    }

    // ══════════════════════════════════════════════════════════════════════════
    // Sprint 8: Canonical structure & isomorphism tests
    // ══════════════════════════════════════════════════════════════════════════

    /// Helper: build a WFST with the given token→action mapping.
    fn build_test_wfst(
        category: &str,
        token_actions: &[(&str, &str, &str, f64)], // (token, rule_label, parse_fn, weight)
    ) -> PredictionWfst {
        let token_names: Vec<String> = token_actions.iter().map(|(t, _, _, _)| t.to_string()).collect();
        let token_map = TokenIdMap::from_names(token_names.into_iter());
        let mut builder = PredictionWfstBuilder::new(category, token_map);
        for (tok, label, parse_fn, weight) in token_actions {
            builder.add_action(
                tok,
                DispatchAction::Direct {
                    rule_label: label.to_string(),
                    parse_fn: parse_fn.to_string(),
                },
                TropicalWeight::new(*weight),
            );
        }
        builder.build()
    }

    #[test]
    fn test_canonical_structure_same_topology_different_labels() {
        // Two WFSTs with identical topology but different action labels
        // should produce identical canonical structures.
        let wfst_int = build_test_wfst("Int", &[
            ("Plus", "AddInt", "parse_add_int", 0.0),
            ("Minus", "SubInt", "parse_sub_int", 0.0),
            ("Ident", "VarInt", "parse_var_int", 1.0),
        ]);
        let wfst_float = build_test_wfst("Float", &[
            ("Plus", "AddFloat", "parse_add_float", 0.0),
            ("Minus", "SubFloat", "parse_sub_float", 0.0),
            ("Ident", "VarFloat", "parse_var_float", 1.0),
        ]);

        let canon_int = wfst_int.canonical_structure();
        let canon_float = wfst_float.canonical_structure();

        assert_eq!(canon_int, canon_float, "Isomorphic WFSTs should have equal canonical structures");
        assert_eq!(
            wfst_int.canonical_hash(),
            wfst_float.canonical_hash(),
            "Isomorphic WFSTs should have equal canonical hashes"
        );
    }

    #[test]
    fn test_canonical_structure_different_topology() {
        // Two WFSTs with different topologies should have different canonical structures.
        let wfst_a = build_test_wfst("A", &[
            ("Plus", "Add", "pa", 0.0),
            ("Minus", "Sub", "ps", 0.0),
        ]);
        let wfst_b = build_test_wfst("B", &[
            ("Plus", "Add", "pa", 0.0),
            ("Star", "Mul", "pm", 0.0), // Different token
        ]);

        let canon_a = wfst_a.canonical_structure();
        let canon_b = wfst_b.canonical_structure();

        assert_ne!(canon_a, canon_b, "Different topologies should produce different canonical structures");
    }

    #[test]
    fn test_canonical_structure_different_weights() {
        // Same tokens and actions but different weights → different canonical structures.
        let wfst_a = build_test_wfst("A", &[
            ("Plus", "Add", "pa", 0.0),
        ]);
        let wfst_b = build_test_wfst("B", &[
            ("Plus", "Add", "pa", 1.0), // Different weight
        ]);

        let canon_a = wfst_a.canonical_structure();
        let canon_b = wfst_b.canonical_structure();

        assert_ne!(canon_a, canon_b, "Different weights should produce different canonical structures");
    }

    #[test]
    fn test_canonical_structure_debruijn_indexing() {
        // Verify De Bruijn indices are assigned in encounter order.
        let wfst = build_test_wfst("Test", &[
            ("Plus", "Add", "pa", 0.0),
            ("Minus", "Sub", "ps", 0.5),
            ("Star", "Mul", "pm", 1.0),
        ]);

        let canonical = wfst.canonical_structure();

        // Action shapes should all be Direct
        assert_eq!(canonical.action_shapes.len(), 3);
        for shape in &canonical.action_shapes {
            assert_eq!(*shape, CanonicalActionShape::Direct);
        }

        // Start state transitions should use De Bruijn indices 0, 1, 2
        let start = &canonical.states[0];
        let db_indices: Vec<u32> = start.transitions.iter().map(|(_, db, _, _)| *db).collect();
        // After sorting by token_id, the De Bruijn indices should cover {0, 1, 2}
        let mut sorted_indices = db_indices.clone();
        sorted_indices.sort();
        sorted_indices.dedup();
        assert_eq!(sorted_indices, vec![0, 1, 2], "De Bruijn indices should be 0, 1, 2");
    }

    #[test]
    fn test_canonical_structure_action_shape_mismatch() {
        // Two WFSTs with same topology but different action shapes are NOT isomorphic.
        let token_map = TokenIdMap::from_names(vec!["X".to_string()].into_iter());

        let mut builder_a = PredictionWfstBuilder::new("A", token_map.clone());
        builder_a.add_action(
            "X",
            DispatchAction::Direct {
                rule_label: "RuleA".to_string(),
                parse_fn: "parse_a".to_string(),
            },
            TropicalWeight::new(0.0),
        );
        let wfst_a = builder_a.build();

        let mut builder_b = PredictionWfstBuilder::new("B", token_map);
        builder_b.add_action(
            "X",
            DispatchAction::Variable { category: "B".to_string() },
            TropicalWeight::new(0.0),
        );
        let wfst_b = builder_b.build();

        let canon_a = wfst_a.canonical_structure();
        let canon_b = wfst_b.canonical_structure();

        assert_ne!(
            canon_a, canon_b,
            "WFSTs with different action shapes should not be isomorphic"
        );
    }

    #[test]
    fn test_canonical_hash_deterministic() {
        // Same WFST should always produce the same hash.
        let wfst = build_test_wfst("Test", &[
            ("A", "R1", "p1", 0.0),
            ("B", "R2", "p2", 1.0),
        ]);
        let h1 = wfst.canonical_hash();
        let h2 = wfst.canonical_hash();
        assert_eq!(h1, h2, "Canonical hash should be deterministic");
    }

    // ══════════════════════════════════════════════════════════════════════════
    // Two-token WFST tests (Sprint 1)
    // ══════════════════════════════════════════════════════════════════════════

    #[test]
    fn test_two_token_builder_creates_intermediate_states() {
        // Two-token paths should create intermediate (non-final) states
        let token_map = TokenIdMap::from_names(
            vec!["Float", "LParen", "Integer", "Boolean"].into_iter().map(String::from),
        );

        let mut builder = PredictionWfstBuilder::new("Expr", token_map);

        // Single-token action
        builder.add_action(
            "Integer",
            DispatchAction::Direct { rule_label: "IntLit".to_string(), parse_fn: "parse_intlit".to_string() },
            TropicalWeight::new(0.0),
        );

        // Two-token actions: Float → ( → FloatId, Float → Boolean → BoolToFloat
        builder.add_two_token_action(
            "Float", "LParen",
            DispatchAction::Direct { rule_label: "FloatId".to_string(), parse_fn: "parse_floatid".to_string() },
            TropicalWeight::new(0.0),
        );
        builder.add_two_token_action(
            "Float", "Boolean",
            DispatchAction::Direct { rule_label: "BoolToFloat".to_string(), parse_fn: "parse_booltofloat".to_string() },
            TropicalWeight::new(0.5),
        );

        let wfst = builder.build();

        // Should have: start(0) + 1 single-token final + 1 intermediate(Float) + 2 two-token finals
        assert_eq!(wfst.num_states(), 5, "expected 5 states: start + 1 single final + 1 intermediate + 2 two-token finals");

        // The intermediate state should NOT be final
        let intermediate = wfst.states.iter().find(|s| !s.is_final && s.id != 0);
        assert!(intermediate.is_some(), "should have a non-final intermediate state");

        // The intermediate should have 2 outgoing transitions (LParen, Boolean)
        let mid = intermediate.expect("intermediate exists");
        assert_eq!(mid.transitions.len(), 2, "intermediate should have 2 transitions");
    }

    #[test]
    fn test_predict_two_token_resolves_ambiguity() {
        // predict_two_token should return narrowed results via intermediate states
        let token_map = TokenIdMap::from_names(
            vec!["Float", "LParen", "Integer"].into_iter().map(String::from),
        );

        let mut builder = PredictionWfstBuilder::new("Expr", token_map);

        // Two ambiguous rules sharing dispatch token "Float"
        builder.add_two_token_action(
            "Float", "LParen",
            DispatchAction::Direct { rule_label: "FloatId".to_string(), parse_fn: "parse_floatid".to_string() },
            TropicalWeight::new(0.0),
        );
        builder.add_two_token_action(
            "Float", "Integer",
            DispatchAction::Direct { rule_label: "IntToFloat".to_string(), parse_fn: "parse_inttofloat".to_string() },
            TropicalWeight::new(0.5),
        );

        let wfst = builder.build();

        // Two-token query: Float + LParen → FloatId only
        let results = wfst.predict_two_token("Float", "LParen");
        assert_eq!(results.len(), 1, "two-token query should resolve to single action");
        assert_eq!(results[0].action.rule_label(), "FloatId");

        // Two-token query: Float + Integer → IntToFloat only
        let results = wfst.predict_two_token("Float", "Integer");
        assert_eq!(results.len(), 1, "two-token query should resolve to single action");
        assert_eq!(results[0].action.rule_label(), "IntToFloat");
    }

    #[test]
    fn test_predict_two_token_fallback_to_single() {
        // When no intermediate states exist for token1, fall back to single-token predict
        let token_map = TokenIdMap::from_names(
            vec!["Plus", "Minus"].into_iter().map(String::from),
        );

        let mut builder = PredictionWfstBuilder::new("Expr", token_map);
        builder.add_action(
            "Plus",
            DispatchAction::Direct { rule_label: "Add".to_string(), parse_fn: "parse_add".to_string() },
            TropicalWeight::new(0.0),
        );

        let wfst = builder.build();

        // No two-token paths for Plus — should fall back to single-token
        let results = wfst.predict_two_token("Plus", "Minus");
        assert_eq!(results.len(), 1, "should fall back to single-token predict");
        assert_eq!(results[0].action.rule_label(), "Add");
    }

    #[test]
    fn test_predict_two_token_unknown_token2_fallback() {
        // When token2 is not found in intermediate transitions, fall back to single-token
        let token_map = TokenIdMap::from_names(
            vec!["Float", "LParen", "Unknown"].into_iter().map(String::from),
        );

        let mut builder = PredictionWfstBuilder::new("Expr", token_map);
        builder.add_two_token_action(
            "Float", "LParen",
            DispatchAction::Direct { rule_label: "FloatId".to_string(), parse_fn: "parse_floatid".to_string() },
            TropicalWeight::new(0.0),
        );

        let wfst = builder.build();

        // Float + Unknown → no match via intermediate, should fall back to single-token
        // But there's no single-token "Float" action either, so predict("Float") would
        // find the intermediate transition (non-final), skip it, and return empty.
        // Actually, predict() returns actions from final states, and intermediates are not final.
        // So it returns empty. predict_two_token should also handle this gracefully.
        let results = wfst.predict_two_token("Float", "Unknown");
        // Falls back to predict("Float"), which finds no actions via final states
        assert!(results.is_empty(), "unknown token2 should result in empty or single-token fallback");
    }

    #[test]
    fn test_is_deterministic_after_two_tokens() {
        // is_deterministic_after should return Some when two-token path yields singleton
        let token_map = TokenIdMap::from_names(
            vec!["Float", "LParen", "Integer"].into_iter().map(String::from),
        );

        let mut builder = PredictionWfstBuilder::new("Expr", token_map);
        builder.add_two_token_action(
            "Float", "LParen",
            DispatchAction::Direct { rule_label: "FloatId".to_string(), parse_fn: "parse_floatid".to_string() },
            TropicalWeight::new(0.0),
        );
        builder.add_two_token_action(
            "Float", "Integer",
            DispatchAction::Direct { rule_label: "IntToFloat".to_string(), parse_fn: "parse_inttofloat".to_string() },
            TropicalWeight::new(0.5),
        );

        let wfst = builder.build();

        // Two-token: Float + LParen → FloatId (deterministic)
        assert_eq!(
            wfst.is_deterministic_after(&["Float", "LParen"]),
            Some("FloatId".to_string()),
        );
        // Two-token: Float + Integer → IntToFloat (deterministic)
        assert_eq!(
            wfst.is_deterministic_after(&["Float", "Integer"]),
            Some("IntToFloat".to_string()),
        );
        // Single-token: Integer → no action (empty)
        assert_eq!(wfst.is_deterministic_after(&["Integer"]), None);
        // Empty sequence
        assert_eq!(wfst.is_deterministic_after(&[]), None);
    }

    #[test]
    fn test_live_actions_after_returns_narrowed_set() {
        let token_map = TokenIdMap::from_names(
            vec!["Float", "LParen", "Integer"].into_iter().map(String::from),
        );

        let mut builder = PredictionWfstBuilder::new("Expr", token_map);
        builder.add_two_token_action(
            "Float", "LParen",
            DispatchAction::Direct { rule_label: "FloatId".to_string(), parse_fn: "parse_floatid".to_string() },
            TropicalWeight::new(0.0),
        );
        builder.add_two_token_action(
            "Float", "Integer",
            DispatchAction::Direct { rule_label: "IntToFloat".to_string(), parse_fn: "parse_inttofloat".to_string() },
            TropicalWeight::new(0.5),
        );

        let wfst = builder.build();

        // Two tokens: narrowed to 1
        let actions = wfst.live_actions_after(&["Float", "LParen"]);
        assert_eq!(actions.len(), 1);
        assert_eq!(actions[0].action.rule_label(), "FloatId");

        // Single token with no single-token actions: empty
        let actions = wfst.live_actions_after(&["Float"]);
        assert!(actions.is_empty(), "no single-token Float action");

        // Empty sequence
        let actions = wfst.live_actions_after(&[]);
        assert!(actions.is_empty());
    }

    // ══════════════════════════════════════════════════════════════════════════
    // FIRST-set expansion tests (Sprint 2)
    // ══════════════════════════════════════════════════════════════════════════

    #[test]
    fn test_enrich_terminal_second_items() {
        // enrich_with_two_token_paths should add paths when 2nd items are disjoint terminals
        use crate::recursive::{RDRuleInfo, RDSyntaxItem};
        let rd_rules = vec![
            RDRuleInfo {
                label: "IfThen".to_string(),
                category: "Stmt".to_string(),
                items: vec![
                    RDSyntaxItem::Terminal("if".to_string()),
                    RDSyntaxItem::Terminal("(".to_string()),
                ],
                has_binder: false, has_multi_binder: false, is_collection: false,
                collection_type: None, separator: None, prefix_bp: None, eval_mode: None,
            },
            RDRuleInfo {
                label: "IfNot".to_string(),
                category: "Stmt".to_string(),
                items: vec![
                    RDSyntaxItem::Terminal("if".to_string()),
                    RDSyntaxItem::Terminal("!".to_string()),
                ],
                has_binder: false, has_multi_binder: false, is_collection: false,
                collection_type: None, separator: None, prefix_bp: None, eval_mode: None,
            },
        ];

        let token_map = TokenIdMap::from_names(
            vec!["KwIf", "LParen", "Bang"].into_iter().map(String::from),
        );
        let mut builder = PredictionWfstBuilder::new("Stmt", token_map);
        builder.add_action(
            "KwIf",
            DispatchAction::Direct { rule_label: "IfThen".to_string(), parse_fn: "p1".to_string() },
            TropicalWeight::new(0.0),
        );
        builder.add_action(
            "KwIf",
            DispatchAction::Direct { rule_label: "IfNot".to_string(), parse_fn: "p2".to_string() },
            TropicalWeight::new(0.5),
        );
        let mut wfsts = HashMap::new();
        wfsts.insert("Stmt".to_string(), builder.build());

        let first_sets = HashMap::new(); // Not needed for terminal second items

        let added = enrich_with_two_token_paths(
            &mut wfsts, &rd_rules, &["Stmt".to_string()], &first_sets,
        );

        assert!(added >= 2, "should add at least 2 two-token paths, got {}", added);

        let wfst = wfsts.get("Stmt").expect("Stmt WFST exists");
        // Should be able to resolve via two-token query
        let results = wfst.predict_two_token("KwIf", "LParen");
        assert_eq!(results.len(), 1, "KwIf + LParen should resolve to IfThen");
        assert_eq!(results[0].action.rule_label(), "IfThen");

        let results = wfst.predict_two_token("KwIf", "Bang");
        assert_eq!(results.len(), 1, "KwIf + Bang should resolve to IfNot");
        assert_eq!(results[0].action.rule_label(), "IfNot");
    }

    #[test]
    fn test_enrich_nonterminal_first_set_expansion() {
        // Sprint 2: enrich should expand NonTerminal second items via FIRST sets
        use crate::recursive::{RDRuleInfo, RDSyntaxItem};
        use crate::prediction::FirstSet;

        // Rule A: float ( Expr ) — FIRST(Expr) = {Integer, Ident}
        // Rule B: float [ List ] — FIRST(List) = {LBracket, Ident} — overlaps with Expr on Ident
        // Since Ident appears in both, this group should NOT be enriched (overlap)
        let rd_rules_overlapping = vec![
            RDRuleInfo {
                label: "FloatExpr".to_string(),
                category: "Val".to_string(),
                items: vec![
                    RDSyntaxItem::Terminal("float".to_string()),
                    RDSyntaxItem::NonTerminal { category: "Expr".to_string(), param_name: "e".to_string() },
                ],
                has_binder: false, has_multi_binder: false, is_collection: false,
                collection_type: None, separator: None, prefix_bp: None, eval_mode: None,
            },
            RDRuleInfo {
                label: "FloatList".to_string(),
                category: "Val".to_string(),
                items: vec![
                    RDSyntaxItem::Terminal("float".to_string()),
                    RDSyntaxItem::NonTerminal { category: "List".to_string(), param_name: "l".to_string() },
                ],
                has_binder: false, has_multi_binder: false, is_collection: false,
                collection_type: None, separator: None, prefix_bp: None, eval_mode: None,
            },
        ];

        let mut first_sets_overlapping = HashMap::new();
        let mut expr_first = FirstSet::new();
        expr_first.insert("Integer");
        expr_first.insert("Ident");
        first_sets_overlapping.insert("Expr".to_string(), expr_first);
        let mut list_first = FirstSet::new();
        list_first.insert("LBracket");
        list_first.insert("Ident"); // overlaps with Expr
        first_sets_overlapping.insert("List".to_string(), list_first);

        let token_map = TokenIdMap::from_names(
            vec!["KwFloat"].into_iter().map(String::from),
        );
        let mut builder = PredictionWfstBuilder::new("Val", token_map);
        builder.add_action(
            "KwFloat",
            DispatchAction::Direct { rule_label: "FloatExpr".to_string(), parse_fn: "p1".to_string() },
            TropicalWeight::new(0.0),
        );
        builder.add_action(
            "KwFloat",
            DispatchAction::Direct { rule_label: "FloatList".to_string(), parse_fn: "p2".to_string() },
            TropicalWeight::new(0.5),
        );
        let mut wfsts_overlap = HashMap::new();
        wfsts_overlap.insert("Val".to_string(), builder.build());

        let added = enrich_with_two_token_paths(
            &mut wfsts_overlap, &rd_rules_overlapping, &["Val".to_string()], &first_sets_overlapping,
        );
        assert_eq!(added, 0, "overlapping FIRST sets should NOT be enriched");

        // Now test disjoint case:
        // Rule A: float ( Expr ) — FIRST(Expr) = {Integer, LParen}
        // Rule B: float [ List ] — FIRST(List) = {LBracket, Ident}
        // Disjoint: no overlap → should add paths
        let rd_rules_disjoint = vec![
            RDRuleInfo {
                label: "FloatExpr".to_string(),
                category: "Val".to_string(),
                items: vec![
                    RDSyntaxItem::Terminal("float".to_string()),
                    RDSyntaxItem::NonTerminal { category: "Expr".to_string(), param_name: "e".to_string() },
                ],
                has_binder: false, has_multi_binder: false, is_collection: false,
                collection_type: None, separator: None, prefix_bp: None, eval_mode: None,
            },
            RDRuleInfo {
                label: "FloatList".to_string(),
                category: "Val".to_string(),
                items: vec![
                    RDSyntaxItem::Terminal("float".to_string()),
                    RDSyntaxItem::NonTerminal { category: "List".to_string(), param_name: "l".to_string() },
                ],
                has_binder: false, has_multi_binder: false, is_collection: false,
                collection_type: None, separator: None, prefix_bp: None, eval_mode: None,
            },
        ];

        let mut first_sets_disjoint = HashMap::new();
        let mut expr_first2 = FirstSet::new();
        expr_first2.insert("Integer");
        expr_first2.insert("LParen");
        first_sets_disjoint.insert("Expr".to_string(), expr_first2);
        let mut list_first2 = FirstSet::new();
        list_first2.insert("LBracket");
        list_first2.insert("Ident");
        first_sets_disjoint.insert("List".to_string(), list_first2);

        let token_map2 = TokenIdMap::from_names(
            vec!["KwFloat"].into_iter().map(String::from),
        );
        let mut builder2 = PredictionWfstBuilder::new("Val", token_map2);
        builder2.add_action(
            "KwFloat",
            DispatchAction::Direct { rule_label: "FloatExpr".to_string(), parse_fn: "p1".to_string() },
            TropicalWeight::new(0.0),
        );
        builder2.add_action(
            "KwFloat",
            DispatchAction::Direct { rule_label: "FloatList".to_string(), parse_fn: "p2".to_string() },
            TropicalWeight::new(0.5),
        );
        let mut wfsts_disjoint = HashMap::new();
        wfsts_disjoint.insert("Val".to_string(), builder2.build());

        let added = enrich_with_two_token_paths(
            &mut wfsts_disjoint, &rd_rules_disjoint, &["Val".to_string()], &first_sets_disjoint,
        );
        assert_eq!(added, 4, "disjoint FIRST sets should add 4 two-token paths (2+2)");

        // Verify: Integer → FloatExpr, LParen → FloatExpr, LBracket → FloatList, Ident → FloatList
        let wfst = wfsts_disjoint.get("Val").expect("Val WFST exists");
        let r = wfst.predict_two_token("KwFloat", "Integer");
        assert_eq!(r.len(), 1);
        assert_eq!(r[0].action.rule_label(), "FloatExpr");

        let r = wfst.predict_two_token("KwFloat", "LBracket");
        assert_eq!(r.len(), 1);
        assert_eq!(r[0].action.rule_label(), "FloatList");
    }

    #[test]
    fn test_enrich_mixed_terminal_nonterminal() {
        // Mix of terminal and nonterminal second items
        // terminal_to_variant_name("cmd") = "KwCmd"
        use crate::recursive::{RDRuleInfo, RDSyntaxItem};
        use crate::prediction::FirstSet;

        // Rule A: cmd ( — terminal second item "("
        // Rule B: cmd Expr — nonterminal second item, FIRST(Expr) = {Integer}
        // Disjoint: "LParen" ≠ "Integer"
        let rd_rules = vec![
            RDRuleInfo {
                label: "CmdParen".to_string(),
                category: "Cmd".to_string(),
                items: vec![
                    RDSyntaxItem::Terminal("cmd".to_string()),
                    RDSyntaxItem::Terminal("(".to_string()),
                ],
                has_binder: false, has_multi_binder: false, is_collection: false,
                collection_type: None, separator: None, prefix_bp: None, eval_mode: None,
            },
            RDRuleInfo {
                label: "CmdExpr".to_string(),
                category: "Cmd".to_string(),
                items: vec![
                    RDSyntaxItem::Terminal("cmd".to_string()),
                    RDSyntaxItem::NonTerminal { category: "Expr".to_string(), param_name: "e".to_string() },
                ],
                has_binder: false, has_multi_binder: false, is_collection: false,
                collection_type: None, separator: None, prefix_bp: None, eval_mode: None,
            },
        ];

        let mut first_sets = HashMap::new();
        let mut expr_first = FirstSet::new();
        expr_first.insert("Integer");
        first_sets.insert("Expr".to_string(), expr_first);

        // terminal_to_variant_name("cmd") = "KwCmd"
        let token_map = TokenIdMap::from_names(
            vec!["KwCmd"].into_iter().map(String::from),
        );
        let mut builder = PredictionWfstBuilder::new("Cmd", token_map);
        builder.add_action(
            "KwCmd",
            DispatchAction::Direct { rule_label: "CmdParen".to_string(), parse_fn: "p1".to_string() },
            TropicalWeight::new(0.0),
        );
        builder.add_action(
            "KwCmd",
            DispatchAction::Direct { rule_label: "CmdExpr".to_string(), parse_fn: "p2".to_string() },
            TropicalWeight::new(0.5),
        );
        let mut wfsts = HashMap::new();
        wfsts.insert("Cmd".to_string(), builder.build());

        let added = enrich_with_two_token_paths(
            &mut wfsts, &rd_rules, &["Cmd".to_string()], &first_sets,
        );
        assert_eq!(added, 2, "mixed terminal+nonterminal should add 2 paths");

        let wfst = wfsts.get("Cmd").expect("Cmd WFST exists");
        let r = wfst.predict_two_token("KwCmd", "LParen");
        assert_eq!(r.len(), 1);
        assert_eq!(r[0].action.rule_label(), "CmdParen");

        let r = wfst.predict_two_token("KwCmd", "Integer");
        assert_eq!(r.len(), 1);
        assert_eq!(r[0].action.rule_label(), "CmdExpr");
    }

    #[test]
    fn test_two_token_mixed_single_and_two_token_paths() {
        // WFST with both single-token and two-token paths for the same first token
        let token_map = TokenIdMap::from_names(
            vec!["Float", "LParen", "Integer"].into_iter().map(String::from),
        );

        let mut builder = PredictionWfstBuilder::new("Expr", token_map);

        // Single-token path: Float → Direct action (cast rule)
        builder.add_action(
            "Float",
            DispatchAction::Cast {
                source_category: "Float".to_string(),
                wrapper_label: "CastFloat".to_string(),
            },
            TropicalWeight::new(0.5),
        );

        // Two-token path: Float + LParen → FloatId
        builder.add_two_token_action(
            "Float", "LParen",
            DispatchAction::Direct { rule_label: "FloatId".to_string(), parse_fn: "parse_floatid".to_string() },
            TropicalWeight::new(0.0),
        );

        let wfst = builder.build();

        // Single-token query: Float → CastFloat (from single-token path)
        let results = wfst.predict("Float");
        assert_eq!(results.len(), 1, "single-token predict should find CastFloat");
        assert_eq!(results[0].action.rule_label(), "CastFloat");

        // Two-token query: Float + LParen → FloatId (from two-token path)
        let results = wfst.predict_two_token("Float", "LParen");
        assert_eq!(results.len(), 1, "two-token predict should find FloatId via intermediate");
        assert_eq!(results[0].action.rule_label(), "FloatId");

        // Two-token query with unmatched token2: Float + Integer → fallback to single-token
        let results = wfst.predict_two_token("Float", "Integer");
        assert_eq!(results.len(), 1, "unmatched token2 should fall back to single-token CastFloat");
        assert_eq!(results[0].action.rule_label(), "CastFloat");
    }

    // ══════════════════════════════════════════════════════════════════════════
    // Sprint 3: ContextWeight powerset query tests
    // ══════════════════════════════════════════════════════════════════════════

    #[test]
    fn test_context_labels_assignment() {
        // Assign context labels and verify bit positions
        let token_map = TokenIdMap::from_names(
            vec!["Float"].into_iter().map(String::from),
        );
        let mut builder = PredictionWfstBuilder::new("Expr", token_map);
        builder.add_action(
            "Float",
            DispatchAction::Direct { rule_label: "FloatId".to_string(), parse_fn: "p1".to_string() },
            TropicalWeight::new(0.0),
        );
        builder.add_action(
            "Float",
            DispatchAction::Direct { rule_label: "IntToFloat".to_string(), parse_fn: "p2".to_string() },
            TropicalWeight::new(0.5),
        );
        builder.add_action(
            "Float",
            DispatchAction::Direct { rule_label: "BoolToFloat".to_string(), parse_fn: "p3".to_string() },
            TropicalWeight::new(1.0),
        );

        let mut wfst = builder.build();
        wfst.assign_context_labels(&["FloatId", "IntToFloat", "BoolToFloat"]);

        assert_eq!(wfst.context_labels.len(), 3);
        assert_eq!(wfst.context_labels["FloatId"], 0);
        assert_eq!(wfst.context_labels["IntToFloat"], 1);
        assert_eq!(wfst.context_labels["BoolToFloat"], 2);
    }

    #[test]
    fn test_live_rules_context_all_alive() {
        // All rules alive when querying the shared dispatch token
        let token_map = TokenIdMap::from_names(
            vec!["Float"].into_iter().map(String::from),
        );
        let mut builder = PredictionWfstBuilder::new("Expr", token_map);
        builder.add_action(
            "Float",
            DispatchAction::Direct { rule_label: "FloatId".to_string(), parse_fn: "p1".to_string() },
            TropicalWeight::new(0.0),
        );
        builder.add_action(
            "Float",
            DispatchAction::Direct { rule_label: "IntToFloat".to_string(), parse_fn: "p2".to_string() },
            TropicalWeight::new(0.5),
        );

        let mut wfst = builder.build();
        wfst.assign_context_labels(&["FloatId", "IntToFloat"]);

        let ctx = wfst.live_rules_context_after(&["Float"]);
        assert_eq!(ctx.count(), 2, "both rules should be alive after dispatch token");
        assert!(ctx.contains(0), "FloatId (bit 0) should be alive");
        assert!(ctx.contains(1), "IntToFloat (bit 1) should be alive");
    }

    #[test]
    fn test_live_rules_context_narrowed_by_two_token() {
        // Two-token paths narrow the live set to a singleton
        let token_map = TokenIdMap::from_names(
            vec!["Float", "LParen", "Integer"].into_iter().map(String::from),
        );

        let mut builder = PredictionWfstBuilder::new("Expr", token_map);
        // Two rules share dispatch token "Float"
        builder.add_two_token_action(
            "Float", "LParen",
            DispatchAction::Direct { rule_label: "FloatId".to_string(), parse_fn: "p1".to_string() },
            TropicalWeight::new(0.0),
        );
        builder.add_two_token_action(
            "Float", "Integer",
            DispatchAction::Direct { rule_label: "IntToFloat".to_string(), parse_fn: "p2".to_string() },
            TropicalWeight::new(0.5),
        );

        let mut wfst = builder.build();
        wfst.assign_context_labels(&["FloatId", "IntToFloat"]);

        // Two-token query narrows to singleton
        let ctx = wfst.live_rules_context_after(&["Float", "LParen"]);
        assert_eq!(ctx.count(), 1, "should narrow to FloatId");
        assert!(ctx.contains(0), "FloatId (bit 0) should survive");
        assert!(!ctx.contains(1), "IntToFloat (bit 1) should be eliminated");

        let ctx = wfst.live_rules_context_after(&["Float", "Integer"]);
        assert_eq!(ctx.count(), 1, "should narrow to IntToFloat");
        assert!(!ctx.contains(0), "FloatId should be eliminated");
        assert!(ctx.contains(1), "IntToFloat should survive");
    }

    #[test]
    fn test_is_deterministic_context_singleton() {
        // is_deterministic_context returns Some when ContextWeight is singleton
        let token_map = TokenIdMap::from_names(
            vec!["Float", "LParen", "Integer"].into_iter().map(String::from),
        );

        let mut builder = PredictionWfstBuilder::new("Expr", token_map);
        builder.add_two_token_action(
            "Float", "LParen",
            DispatchAction::Direct { rule_label: "FloatId".to_string(), parse_fn: "p1".to_string() },
            TropicalWeight::new(0.0),
        );
        builder.add_two_token_action(
            "Float", "Integer",
            DispatchAction::Direct { rule_label: "IntToFloat".to_string(), parse_fn: "p2".to_string() },
            TropicalWeight::new(0.5),
        );

        let mut wfst = builder.build();
        wfst.assign_context_labels(&["FloatId", "IntToFloat"]);

        assert_eq!(
            wfst.is_deterministic_context(&["Float", "LParen"]),
            Some("FloatId".to_string()),
        );
        assert_eq!(
            wfst.is_deterministic_context(&["Float", "Integer"]),
            Some("IntToFloat".to_string()),
        );
    }

    #[test]
    fn test_is_deterministic_context_ambiguous() {
        // is_deterministic_context returns None when multiple rules survive
        let token_map = TokenIdMap::from_names(
            vec!["Float"].into_iter().map(String::from),
        );
        let mut builder = PredictionWfstBuilder::new("Expr", token_map);
        builder.add_action(
            "Float",
            DispatchAction::Direct { rule_label: "FloatId".to_string(), parse_fn: "p1".to_string() },
            TropicalWeight::new(0.0),
        );
        builder.add_action(
            "Float",
            DispatchAction::Direct { rule_label: "IntToFloat".to_string(), parse_fn: "p2".to_string() },
            TropicalWeight::new(0.5),
        );

        let mut wfst = builder.build();
        wfst.assign_context_labels(&["FloatId", "IntToFloat"]);

        // Single-token query: both rules alive → None
        assert_eq!(wfst.is_deterministic_context(&["Float"]), None);
    }

    #[test]
    fn test_context_narrowing_reports_count() {
        // context_narrowing returns the correct count
        let token_map = TokenIdMap::from_names(
            vec!["Float", "LParen", "Integer"].into_iter().map(String::from),
        );

        let mut builder = PredictionWfstBuilder::new("Expr", token_map);
        builder.add_two_token_action(
            "Float", "LParen",
            DispatchAction::Direct { rule_label: "FloatId".to_string(), parse_fn: "p1".to_string() },
            TropicalWeight::new(0.0),
        );
        builder.add_two_token_action(
            "Float", "Integer",
            DispatchAction::Direct { rule_label: "IntToFloat".to_string(), parse_fn: "p2".to_string() },
            TropicalWeight::new(0.5),
        );

        let mut wfst = builder.build();
        wfst.assign_context_labels(&["FloatId", "IntToFloat"]);

        let (ctx, count) = wfst.context_narrowing(&["Float", "LParen"]);
        assert_eq!(count, 1);
        assert!(ctx.contains(0));

        let (ctx, count) = wfst.context_narrowing(&["Float", "Integer"]);
        assert_eq!(count, 1);
        assert!(ctx.contains(1));
    }

    #[test]
    fn test_context_labels_empty_no_crash() {
        // When no context labels are assigned, queries return zero ContextWeight
        let token_map = TokenIdMap::from_names(
            vec!["Float"].into_iter().map(String::from),
        );
        let mut builder = PredictionWfstBuilder::new("Expr", token_map);
        builder.add_action(
            "Float",
            DispatchAction::Direct { rule_label: "FloatId".to_string(), parse_fn: "p1".to_string() },
            TropicalWeight::new(0.0),
        );

        let wfst = builder.build();

        // No context labels assigned — should return zero
        let ctx = wfst.live_rules_context_after(&["Float"]);
        assert_eq!(ctx.count(), 0, "no context labels → zero ContextWeight");
        assert_eq!(wfst.is_deterministic_context(&["Float"]), None);
    }

    #[test]
    fn test_context_labels_unknown_token() {
        // Query with unknown token returns zero ContextWeight
        let token_map = TokenIdMap::from_names(
            vec!["Float"].into_iter().map(String::from),
        );
        let mut builder = PredictionWfstBuilder::new("Expr", token_map);
        builder.add_action(
            "Float",
            DispatchAction::Direct { rule_label: "FloatId".to_string(), parse_fn: "p1".to_string() },
            TropicalWeight::new(0.0),
        );
        let mut wfst = builder.build();
        wfst.assign_context_labels(&["FloatId"]);

        let ctx = wfst.live_rules_context_after(&["Unknown"]);
        assert_eq!(ctx.count(), 0, "unknown token → empty live set");
    }

    // ══════════════════════════════════════════════════════════════════════════
    // Sprint 4: Narrowed NFA candidate filtering tests
    // ══════════════════════════════════════════════════════════════════════════

    #[test]
    fn test_nfa_order_with_context_narrowing() {
        // Verify that nfa_alternative_order works correctly on a narrowed
        // candidate set (simulates what the trampoline does in Sprint 4).
        let token_map = TokenIdMap::from_names(
            vec!["Float", "LParen", "Integer"].into_iter().map(String::from),
        );

        let mut builder = PredictionWfstBuilder::new("Expr", token_map);
        // Three rules share "Float", but two-token paths narrow to singletons
        builder.add_two_token_action(
            "Float", "LParen",
            DispatchAction::Direct { rule_label: "FloatId".to_string(), parse_fn: "p1".to_string() },
            TropicalWeight::new(0.0),
        );
        builder.add_two_token_action(
            "Float", "Integer",
            DispatchAction::Direct { rule_label: "IntToFloat".to_string(), parse_fn: "p2".to_string() },
            TropicalWeight::new(0.5),
        );

        let mut wfst = builder.build();
        wfst.assign_context_labels(&["FloatId", "IntToFloat"]);

        // Without narrowing: both rules alive at single-token level
        let all_labels = vec!["FloatId", "IntToFloat"];
        let order = wfst.nfa_alternative_order("Float", &all_labels);
        // Both rules should be orderable — the fallback to single-token returns both
        assert!(order.len() >= 1, "should return at least 1 alternative");

        // With narrowing (simulating trampoline Sprint 4 logic):
        // When only two-token actions exist (no single-token), predict("Float")
        // returns empty (no final states reachable in one hop), so
        // live_rules_context_after(&["Float"]) returns zero. The trampoline
        // code falls through to try-all in this case (ctx.count() == 0 → keep all).
        let ctx = wfst.live_rules_context_after(&["Float"]);
        assert_eq!(ctx.count(), 0, "no single-token paths → empty context");

        // At two-token level, narrowing gives singletons
        let ctx2 = wfst.live_rules_context_after(&["Float", "LParen"]);
        let narrowed2: Vec<&str> = all_labels.iter().copied().filter(|label| {
            wfst.context_labels.get(*label)
                .map_or(true, |&bit| ctx2.contains(bit))
        }).collect();
        assert_eq!(narrowed2.len(), 1, "two-token narrows to FloatId");
        assert_eq!(narrowed2[0], "FloatId");
    }

    #[test]
    fn test_narrowed_candidate_excludes_dead_rules() {
        // Verify that ContextWeight filtering correctly excludes rules
        // not in the live set.
        let token_map = TokenIdMap::from_names(
            vec!["KwFn"].into_iter().map(String::from),
        );

        let mut builder = PredictionWfstBuilder::new("Stmt", token_map);
        builder.add_action(
            "KwFn",
            DispatchAction::Direct { rule_label: "FnDecl".to_string(), parse_fn: "p1".to_string() },
            TropicalWeight::new(0.0),
        );
        builder.add_action(
            "KwFn",
            DispatchAction::Direct { rule_label: "FnExpr".to_string(), parse_fn: "p2".to_string() },
            TropicalWeight::new(0.5),
        );
        builder.add_action(
            "KwFn",
            DispatchAction::Direct { rule_label: "FnType".to_string(), parse_fn: "p3".to_string() },
            TropicalWeight::new(1.0),
        );

        let mut wfst = builder.build();
        // Only assign labels to 2 of 3 rules (simulating a partial group)
        wfst.assign_context_labels(&["FnDecl", "FnExpr", "FnType"]);

        let ctx = wfst.live_rules_context_after(&["KwFn"]);
        assert_eq!(ctx.count(), 3, "all three rules alive at dispatch token");

        // Simulate removing FnType from the live set (as if two-token narrowed it)
        // by manually constructing a narrowed context
        use crate::automata::semiring::ContextWeight;
        let narrowed_ctx = ContextWeight::singleton(0).plus(&ContextWeight::singleton(1));
        assert_eq!(narrowed_ctx.count(), 2);

        let all_labels = vec!["FnDecl", "FnExpr", "FnType"];
        let narrowed: Vec<&str> = all_labels.iter().copied().filter(|label| {
            wfst.context_labels.get(*label)
                .map_or(true, |&bit| narrowed_ctx.contains(bit))
        }).collect();
        assert_eq!(narrowed.len(), 2);
        assert!(narrowed.contains(&"FnDecl"));
        assert!(narrowed.contains(&"FnExpr"));
        assert!(!narrowed.contains(&"FnType"));
    }

    #[test]
    fn test_narrowed_preserves_order() {
        // After narrowing, nfa_alternative_order on the narrowed set preserves
        // WFST weight ordering.
        let token_map = TokenIdMap::from_names(
            vec!["KwLet"].into_iter().map(String::from),
        );

        let mut builder = PredictionWfstBuilder::new("Stmt", token_map);
        builder.add_action(
            "KwLet",
            DispatchAction::Direct { rule_label: "LetMut".to_string(), parse_fn: "p1".to_string() },
            TropicalWeight::new(0.0),
        );
        builder.add_action(
            "KwLet",
            DispatchAction::Direct { rule_label: "LetConst".to_string(), parse_fn: "p2".to_string() },
            TropicalWeight::new(0.3),
        );

        let mut wfst = builder.build();
        wfst.assign_context_labels(&["LetMut", "LetConst"]);

        let narrowed = vec!["LetMut", "LetConst"];
        let ordered = wfst.nfa_alternative_order("KwLet", &narrowed);

        // Should be ordered by weight: LetMut (0.0) before LetConst (0.3)
        assert_eq!(ordered.len(), 2);
        assert_eq!(ordered[0].0, 0, "LetMut at index 0 (lowest weight)");
        assert_eq!(ordered[1].0, 1, "LetConst at index 1 (higher weight)");
        assert!(ordered[0].1.value() < ordered[1].1.value(), "weights should be ordered");
    }
}
