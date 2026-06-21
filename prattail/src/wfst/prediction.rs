use super::*;

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
                                action_shapes.push(CanonicalActionShape::from_action(&wa.action));
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

        CanonicalWfstStructure { states, start: self.start, action_shapes }
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
    pub fn predict_with_confidence(
        &self,
        token_name: &str,
    ) -> Vec<(&WeightedAction, crate::automata::semiring::CountingWeight)> {
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
                            let total_weight =
                                TropicalWeight::new(weight1.value() + t.weight.value());
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
            },
            _ => {
                let actions = self.predict_two_token(tokens[0], tokens[1]);
                if actions.len() == 1 {
                    Some(actions[0].action.rule_label())
                } else {
                    None
                }
            },
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
            let entry = token_best
                .entry(trans.input)
                .or_insert(TropicalWeight::zero());
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
    /// reconstructed `DispatchAction::Direct` entries. The caller can override specific
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

                // Reconstruct a direct action; the label is derived from the token name.
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
            let representative = *sig_to_representative.entry(sig).or_insert(state.id);
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
            state.transitions.retain(|t| t.weight.value() <= threshold);
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

    // Stage 10.8 (2026-05-05): with_trained_weights method DELETED. Consumed
    // TrainedModel produced by SpilloverTrainer (also deleted in Stage 10.8).
    // Walker-derived weight corrections will need a fresh API design when
    // they exist; the underlying mechanism (DispatchAction.weight override)
    // is preserved for future use via apply_corrections.

    /// Sprint 5: Apply weight corrections from NFA spillover training signals.
    ///
    /// For each correction, adjusts the weights of actions whose `rule_label()`
    /// matches rules associated with the primary weight (penalize) or selected
    /// weight (reinforce). The adjustment magnitude is `learning_rate × weight_delta`,
    /// clamped to `[-max_adjustment, +max_adjustment]`.
    ///
    /// This provides the WFST-level interface for the `SpilloverTrainer`.
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
        let safe_cat = self
            .category
            .replace(|c: char| !c.is_alphanumeric() && c != '_', "_");
        writeln!(out, "digraph PredictionWfst_{} {{", safe_cat)
            .expect("wfst: DOT write into in-memory String is infallible");
        writeln!(out, "  rankdir=LR;")
            .expect("wfst: DOT write into in-memory String is infallible");
        writeln!(out, "  node [shape=circle, fontname=\"Helvetica\"];")
            .expect("wfst: DOT write into in-memory String is infallible");
        writeln!(out, "  edge [fontname=\"Helvetica\", fontsize=10];")
            .expect("wfst: DOT write into in-memory String is infallible");

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
            writeln!(out, "  {} [shape={}, label=\"{}\"];", state.id, shape, label)
                .expect("wfst: DOT write into in-memory String is infallible");
        }

        // Emit edges
        for state in &self.states {
            for t in &state.transitions {
                let token_label = if t.input == crate::token_id::EPSILON_TOKEN {
                    "ε".to_string()
                } else {
                    self.token_map.name(t.input).unwrap_or("?").to_string()
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
                .expect("wfst: DOT write into in-memory String is infallible");
            }
        }

        writeln!(out, "}}").expect("wfst: DOT write into in-memory String is infallible");
        out
    }
}
