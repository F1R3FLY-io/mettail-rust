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

use std::collections::BTreeMap;

use crate::automata::semiring::{Semiring, TropicalWeight};
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
/// This is a simple one-level WFST (start → accept) since prefix dispatch
/// is a single-token decision. Lookahead (2+ tokens) could extend this to
/// multi-level paths in the future.
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
}

impl PredictionWfst {
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
            .filter_map(|t| self.actions.get(t.action_idx as usize))
            .collect();

        // Sort by weight: lowest (best) first
        results.sort_by_key(|a| a.weight);
        results
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

    /// Set the beam width for pruning.
    pub fn set_beam_width(&mut self, beam: Option<TropicalWeight>) {
        self.beam_width = beam;
    }

    /// Get the current beam width.
    pub fn beam_width(&self) -> Option<TropicalWeight> {
        self.beam_width
    }

    /// Number of registered actions.
    pub fn num_actions(&self) -> usize {
        self.actions.len()
    }

    /// Number of states in the WFST.
    pub fn num_states(&self) -> usize {
        self.states.len()
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
}

// ══════════════════════════════════════════════════════════════════════════════
// Builder
// ══════════════════════════════════════════════════════════════════════════════

/// Builder for constructing a `PredictionWfst` from FIRST sets and dispatch tables.
pub struct PredictionWfstBuilder {
    category: String,
    token_map: TokenIdMap,
    actions: Vec<WeightedAction>,
    transitions: Vec<(TokenId, u32, TropicalWeight)>, // (input, action_idx, weight)
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

    /// Build the prediction WFST.
    ///
    /// Creates a simple two-level WFST: start state → final state per action.
    /// Transitions from start carry the token label and weight.
    pub fn build(self) -> PredictionWfst {
        // State 0: start state
        let mut start_state = WfstState::new(0);

        // Create one final state per action + transitions from start
        let mut states = Vec::with_capacity(1 + self.transitions.len());
        states.push(WfstState::new(0)); // placeholder for start

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

        states[0] = start_state;

        PredictionWfst {
            category: self.category,
            states,
            start: 0,
            actions: self.actions,
            token_map: self.token_map,
            beam_width: self.beam_width,
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
    first_sets: &BTreeMap<String, FirstSet>,
    overlaps: &BTreeMap<(String, String), CrossCategoryOverlap>,
    dispatch_actions: &BTreeMap<String, BTreeMap<String, DispatchAction>>,
) -> BTreeMap<String, PredictionWfst> {
    let mut result = BTreeMap::new();

    // Build shared token ID map from all FIRST sets
    let mut all_tokens: Vec<String> = Vec::new();
    for first_set in first_sets.values() {
        all_tokens.extend(first_set.tokens.iter().cloned());
    }
    let token_map = TokenIdMap::from_names(all_tokens);

    for category in categories {
        let mut builder = PredictionWfstBuilder::new(category, token_map.clone());

        if let Some(category_actions) = dispatch_actions.get(category) {
            let token_order: Vec<(&String, &DispatchAction)> = category_actions.iter().collect();
            // Maintain declaration order (BTreeMap iterates in key order = sorted token names)
            // We use enumeration index as a proxy for declaration order

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
    _first_sets: &BTreeMap<String, FirstSet>,
    _overlaps: &BTreeMap<(String, String), CrossCategoryOverlap>,
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
    let mut token_groups: BTreeMap<TokenId, Vec<&WeightedAction>> = BTreeMap::new();

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
    fn test_compute_action_weight() {
        let first_sets = BTreeMap::new();
        let overlaps = BTreeMap::new();

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
        let mut rule_weights = std::collections::BTreeMap::new();
        rule_weights.insert("Add".to_string(), 0.3);
        // "NonExistent" should be silently ignored
        rule_weights.insert("NonExistent".to_string(), 99.0);

        let model = crate::training::TrainedModel {
            rule_weights,
            recommended_beam_width: None,
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

        let mut rule_weights = std::collections::BTreeMap::new();
        rule_weights.insert("Add".to_string(), 0.1);

        let model = crate::training::TrainedModel {
            rule_weights,
            recommended_beam_width: None,
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
                wrap_collection_in_literal: false,
            }],
            BeamWidthConfig::Explicit(1.5),  // beam_width
            None,                            // log_semiring_model_path
            crate::DispatchStrategy::Static, // dispatch_strategy
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
}
