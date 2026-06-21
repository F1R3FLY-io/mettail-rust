use super::*;

// ══════════════════════════════════════════════════════════════════════════════
// RecoveryWfst — per-category recovery automaton
// ══════════════════════════════════════════════════════════════════════════════

/// Per-category recovery WFST for weighted error repair.
///
/// Built at compile time from the category's sync tokens (FOLLOW set +
/// structural delimiters). At parse time, when an error occurs, the
/// recovery WFST evaluates all possible repair actions and returns the
/// minimum-cost one via Viterbi.
#[derive(Debug, Clone)]
pub struct RecoveryWfst {
    /// Category name.
    category: String,
    /// Sync token IDs for this category (from FOLLOW + structural delimiters).
    pub(crate) sync_tokens: BTreeSet<TokenId>,
    /// Token ID map for resolving names.
    token_map: TokenIdMap,
    /// B1: Prediction-aware discount factors for sync tokens.
    ///
    /// Maps each sync token ID to a discount factor in `(0.0, 1.0]`:
    /// - `1.0` = no discount (token not in prediction WFST or weight 0.0)
    /// - `< 1.0` = discount (token has high prediction confidence, prefer for recovery)
    ///
    /// The discount factor is computed as `max(1.0 - best_weight, 0.1)` where
    /// `best_weight` is the minimum prediction weight for this token in the
    /// category's prediction WFST. Tokens with lower prediction weight (higher
    /// confidence) get larger discounts, making them preferred recovery targets.
    prediction_discounts: std::collections::HashMap<TokenId, f64>,
    /// A1: Per-sync-token ContextWeight indicating which rules can reach that sync token.
    ///
    /// Each sync token is annotated with a bitset of rule indices whose FOLLOW set
    /// includes that token. When recovery is invoked with a dispatch context (the rules
    /// active at the error point), the intersection filters out sync tokens that are
    /// unreachable from the current parse path. An empty intersection means the sync
    /// token is a false positive for this dispatch context.
    ///
    /// Structural tokens (Eof, RParen, RBrace, etc.) get `ContextWeight::one()` (always valid).
    follow_contexts: std::collections::HashMap<TokenId, crate::automata::semiring::ContextWeight>,
    /// Sprint A2: Token IDs with ambiguous bracket classification (both open and close).
    ///
    /// When VPA analysis finds tokens used as both call and return symbols (e.g., `|`
    /// in Rust closures), InsertToken for these tokens becomes unreliable — it may
    /// insert the wrong bracket direction. Recovery penalizes InsertToken for these
    /// tokens with a 2.0x cost multiplier.
    bracket_mismatch_ids: BTreeSet<TokenId>,
    /// Sprint C2: Whether this category participates in an accepting SCC
    /// (recursive grammar loop). When true, InsertToken is discounted (0.7x)
    /// and SkipToSync is penalized (1.3x) to maintain the loop structure.
    recursive_category: bool,
}

impl RecoveryWfst {
    /// Build a recovery WFST for a category.
    ///
    /// # Arguments
    ///
    /// * `category` — Category name (e.g., "Int", "Proc").
    /// * `sync_token_names` — Names of sync tokens (from FOLLOW set + structural).
    /// * `token_map` — Bidirectional token name ↔ ID map.
    pub fn new(category: String, sync_token_names: &[String], token_map: &TokenIdMap) -> Self {
        let sync_tokens: BTreeSet<TokenId> = sync_token_names
            .iter()
            .filter_map(|name| token_map.get(name))
            .collect();

        RecoveryWfst {
            category,
            sync_tokens,
            token_map: token_map.clone(),
            prediction_discounts: std::collections::HashMap::new(),
            follow_contexts: std::collections::HashMap::new(),
            bracket_mismatch_ids: BTreeSet::new(),
            recursive_category: false,
        }
    }

    /// Sprint A2: Set bracket mismatch token IDs.
    ///
    /// Called after construction to wire in VPA analysis data. Tokens in this set
    /// are penalized with a 2.0x cost multiplier when used as InsertToken targets,
    /// because their ambiguous bracket classification (both open and close) makes
    /// insertion unreliable.
    pub fn set_bracket_mismatch_ids(&mut self, ids: BTreeSet<TokenId>) {
        self.bracket_mismatch_ids = ids;
    }

    /// Sprint A2: Get the bracket mismatch insert penalty for a token.
    ///
    /// Returns `2.0` for tokens with ambiguous bracket classification, `1.0` otherwise.
    #[inline]
    pub fn bracket_mismatch_penalty(&self, token_id: TokenId) -> f64 {
        if self.bracket_mismatch_ids.contains(&token_id) {
            2.0
        } else {
            1.0
        }
    }

    /// Sprint C2: Set whether this category participates in a recursive SCC.
    ///
    /// Called after construction to wire in Büchi analysis data. When true,
    /// InsertToken is discounted (0.7x) and SkipToSync is penalized (1.3x)
    /// to maintain the recursive loop structure during recovery.
    pub fn set_recursive_category(&mut self, recursive: bool) {
        self.recursive_category = recursive;
    }

    /// Sprint C2: Check whether this category is in a recursive SCC.
    #[inline]
    pub fn is_recursive_category(&self) -> bool {
        self.recursive_category
    }

    /// B1: Set prediction-aware discount factors for sync tokens.
    ///
    /// Called after construction to wire in prediction WFST weight data.
    /// Each entry maps a sync token ID to a discount factor in `(0.0, 1.0]`.
    pub fn set_prediction_discounts(&mut self, discounts: std::collections::HashMap<TokenId, f64>) {
        self.prediction_discounts = discounts
            .into_iter()
            .filter_map(|(token, discount)| {
                if discount.is_finite() && discount >= 0.0 {
                    Some((token, discount))
                } else {
                    None
                }
            })
            .collect();
    }

    /// B1: Get the prediction discount for a sync token.
    ///
    /// Returns `1.0` (no discount) for tokens without prediction data.
    #[inline]
    pub fn prediction_discount(&self, token_id: TokenId) -> f64 {
        self.prediction_discounts
            .get(&token_id)
            .copied()
            .filter(|discount| discount.is_finite() && *discount >= 0.0)
            .unwrap_or(1.0)
    }

    /// B1: Return prediction discounts for exact cache signatures and diagnostics.
    pub fn prediction_discounts(&self) -> &std::collections::HashMap<TokenId, f64> {
        &self.prediction_discounts
    }

    /// A1: Set per-sync-token follow context weights.
    ///
    /// Each entry maps a sync token ID to a `ContextWeight` bitset encoding which
    /// rule indices can reach that sync token. Used for follow-set tightening.
    pub fn set_follow_contexts(
        &mut self,
        contexts: std::collections::HashMap<TokenId, crate::automata::semiring::ContextWeight>,
    ) {
        self.follow_contexts = contexts;
    }

    /// A1: Check whether a sync token is reachable from the given dispatch context.
    ///
    /// Returns `true` if:
    /// - No follow contexts are set (default: all sync tokens valid), or
    /// - The sync token has no context annotation (structural tokens: always valid), or
    /// - The intersection of the sync token's follow context and the dispatch context
    ///   is non-empty (at least one active rule can reach this sync token).
    #[inline]
    pub fn is_sync_reachable(
        &self,
        sync_id: TokenId,
        dispatch_context: crate::automata::semiring::ContextWeight,
    ) -> bool {
        if self.follow_contexts.is_empty() {
            return true; // no context data → all sync tokens valid
        }
        match self.follow_contexts.get(&sync_id) {
            None => true, // unannotated → structural token, always valid
            Some(ctx) => {
                use crate::automata::semiring::Semiring;
                !ctx.times(&dispatch_context).is_zero()
            },
        }
    }

    /// A1: Return the tightened sync token set for a given dispatch context.
    ///
    /// Filters the full sync token set, keeping only tokens reachable from the
    /// dispatch context. When no follow contexts are set, returns all sync tokens.
    pub fn tightened_sync_tokens(
        &self,
        dispatch_context: crate::automata::semiring::ContextWeight,
    ) -> std::borrow::Cow<'_, BTreeSet<TokenId>> {
        if self.follow_contexts.is_empty() || dispatch_context.is_one() {
            std::borrow::Cow::Borrowed(&self.sync_tokens)
        } else {
            let filtered: BTreeSet<TokenId> = self
                .sync_tokens
                .iter()
                .copied()
                .filter(|&id| self.is_sync_reachable(id, dispatch_context))
                .collect();
            std::borrow::Cow::Owned(filtered)
        }
    }

    /// A1: Return the follow context for this recovery WFST (for diagnostics/testing).
    pub fn follow_contexts(
        &self,
    ) -> &std::collections::HashMap<TokenId, crate::automata::semiring::ContextWeight> {
        &self.follow_contexts
    }

    /// Sprint A2: Return bracket-mismatch token IDs for exact cache signatures.
    pub fn bracket_mismatch_ids(&self) -> &BTreeSet<TokenId> {
        &self.bracket_mismatch_ids
    }

    /// The category this recovery WFST covers.
    pub fn category(&self) -> &str {
        &self.category
    }

    /// Token ID map used internally by this recovery WFST.
    pub fn token_map(&self) -> &TokenIdMap {
        &self.token_map
    }

    /// Find the best recovery action from the given position.
    ///
    /// Evaluates all repair strategies and returns the minimum-cost one:
    ///
    /// 1. **SkipToSync**: For each reachable sync token within `MAX_SKIP_LOOKAHEAD`,
    ///    compute `skip_count * SKIP_PER_TOKEN`.
    /// 2. **DeleteToken**: Delete the current token (cost `DELETE`), only if there
    ///    are tokens remaining.
    /// 3. **InsertToken**: For each sync token, insert it at the current position
    ///    (cost `INSERT`).
    /// 4. **SubstituteToken**: For each sync token, substitute the current token
    ///    (cost `SUBSTITUTE`), only if tokens remain.
    ///
    /// Returns `None` if no recovery is possible (e.g., at EOF with no sync tokens).
    pub fn find_best_recovery(&self, token_ids: &[TokenId], pos: usize) -> Option<RepairResult> {
        let remaining = token_ids.get(pos..)?;
        let mut best: Option<RepairResult> = None;

        // Strategy 1: SkipToSync — skip tokens until a sync point
        let max_lookahead = remaining.len().min(costs::MAX_SKIP_LOOKAHEAD);
        #[allow(clippy::needless_range_loop)]
        // `skip` used for arithmetic, cost calc, struct field, and position offset
        for skip in 0..max_lookahead {
            let token_at = remaining[skip];
            if self.sync_tokens.contains(&token_at) {
                let action = RepairAction::SkipToSync { skip_count: skip, sync_token: token_at };
                let cost = if skip == 0 {
                    // Already at a sync token — zero cost
                    RecoveryCost::one()
                } else {
                    // B1: prediction discount — prefer skipping to high-confidence tokens
                    let pred_discount = self.prediction_discount(token_at);
                    // B2: joint tropical + edit cost
                    costs::joint(
                        skip as f64 * costs::SKIP_PER_TOKEN.value() * pred_discount,
                        skip as u32,
                    )
                };
                let result = RepairResult { action, new_pos: pos + skip, cost };
                best = Some(pick_better(best, result));
                // First sync point found — skip further is always worse
                break;
            }
        }

        // Strategy 2: DeleteToken — skip exactly one token
        if !remaining.is_empty() {
            let action = RepairAction::DeleteToken;
            let result = RepairResult {
                cost: costs::joint_edit(costs::DELETE.value(), action.edit_cost()),
                action,
                new_pos: pos + 1,
            };
            best = Some(pick_better(best, result));
        }

        // Strategy 3: InsertToken — insert each sync token at current position
        for &sync_id in &self.sync_tokens {
            // B1: prediction discount — prefer inserting high-confidence tokens
            let pred_discount = self.prediction_discount(sync_id);
            // Sprint A2: bracket mismatch penalty — penalize inserting ambiguous bracket tokens
            let bracket_mult = self.bracket_mismatch_penalty(sync_id);
            let action = RepairAction::InsertToken { token: sync_id };
            let result = RepairResult {
                cost: costs::joint_edit(
                    costs::INSERT.value() * pred_discount * bracket_mult,
                    action.edit_cost(),
                ),
                action,
                new_pos: pos, // no position change — inserted token is phantom
            };
            best = Some(pick_better(best, result));
        }

        // Strategy 4: SubstituteToken — replace current token with a sync token
        if !remaining.is_empty() {
            for &sync_id in &self.sync_tokens {
                // B1: prediction discount — prefer substituting with high-confidence tokens
                let pred_discount = self.prediction_discount(sync_id);
                let action = RepairAction::SubstituteToken { replacement: sync_id };
                let result = RepairResult {
                    cost: costs::joint_edit(
                        costs::SUBSTITUTE.value() * pred_discount,
                        action.edit_cost(),
                    ),
                    action,
                    new_pos: pos + 1, // consume the substituted token
                };
                best = Some(pick_better(best, result));
            }
        }

        // Strategy 5: SwapTokens — swap adjacent tokens
        if remaining.len() >= 2 {
            // Check if swapping remaining[0] and remaining[1] produces a sync token
            // at position 0, or if the swapped pair looks better to the parser
            let swapped_first = remaining[1];
            if self.sync_tokens.contains(&swapped_first) {
                // B1: prediction discount on the sync token revealed by the swap
                let pred_discount = self.prediction_discount(swapped_first);
                let action = RepairAction::SwapTokens { pos_a: pos, pos_b: pos + 1 };
                let result = RepairResult {
                    cost: costs::joint_edit(1.25 * pred_discount, action.edit_cost()), // SWAP cost
                    action,
                    new_pos: pos + 2, // consume both tokens in swapped order
                };
                best = Some(pick_better(best, result));
            }
        }

        best
    }

    /// Resolve a token ID to its name (for diagnostics).
    pub fn token_name(&self, id: TokenId) -> Option<&str> {
        self.token_map.name(id)
    }

    /// The set of sync token IDs for this category.
    pub fn sync_tokens(&self) -> &BTreeSet<TokenId> {
        &self.sync_tokens
    }

    /// Reconstruct a `RecoveryWfst` from flat arrays embedded in generated code.
    ///
    /// This is the deserialization constructor for CSR-format static data.
    ///
    /// ## Arguments
    ///
    /// * `category` — Category name.
    /// * `sync_token_ids` — Sorted slice of sync token IDs.
    /// * `sync_sources` — Parallel slice of `(token_id, source_tag)` pairs where
    ///   `source_tag` is 0=Eof, 1=StructuralDelimiter, 2=FollowSet.
    /// * `token_names` — Token name strings for rebuilding the `TokenIdMap`.
    pub fn from_flat(
        category: &str,
        sync_token_ids: &[u16],
        _sync_sources: &[(u16, u8)],
        token_names: &[&str],
    ) -> Self {
        let token_map = TokenIdMap::from_names(token_names.iter().map(|s| s.to_string()));
        let sync_tokens: BTreeSet<TokenId> = sync_token_ids.iter().copied().collect();

        RecoveryWfst {
            category: category.to_string(),
            sync_tokens,
            token_map,
            prediction_discounts: std::collections::HashMap::new(),
            follow_contexts: std::collections::HashMap::new(),
            bracket_mismatch_ids: BTreeSet::new(),
            recursive_category: false,
        }
    }

    // ── D3: DOT/Graphviz visualization ─────────────────────────────────

    /// D3: Generate a DOT (Graphviz) representation of this recovery WFST.
    ///
    /// The output is a graph with:
    /// - A single "Error" start state
    /// - One "Sync_TOKEN" node per sync token
    /// - Edges labeled with the sync token name (and B1 discount if < 1.0)
    /// - A1 context annotations shown as tooltip attributes
    ///
    /// This is a conceptual visualization: the recovery WFST doesn't have
    /// explicit state/transition structures like `PredictionWfst`, so we
    /// synthesize a star-topology graph from the sync token set.
    pub fn to_dot(&self) -> String {
        use std::fmt::Write;
        let mut out = String::new();
        let safe_cat = self
            .category
            .replace(|c: char| !c.is_alphanumeric() && c != '_', "_");
        writeln!(out, "digraph RecoveryWfst_{} {{", safe_cat)
            .expect("recovery: DOT write into in-memory String is infallible");
        writeln!(out, "  rankdir=LR;")
            .expect("recovery: DOT write into in-memory String is infallible");
        writeln!(out, "  node [shape=circle, fontname=\"Helvetica\"];")
            .expect("recovery: DOT write into in-memory String is infallible");
        writeln!(out, "  edge [fontname=\"Helvetica\", fontsize=10];")
            .expect("recovery: DOT write into in-memory String is infallible");
        writeln!(out, "  error [shape=doublecircle, label=\"Error\\n(start)\", style=filled, fillcolor=lightyellow];").expect("recovery: DOT write into in-memory String is infallible");

        for (i, &token_id) in self.sync_tokens.iter().enumerate() {
            let token_name = self.token_map.name(token_id).unwrap_or("?").to_string();
            let node_id = format!("sync_{}", i);

            // Node: sync token target
            writeln!(out, "  {} [shape=doublecircle, label=\"Sync\\n{}\"];", node_id, token_name)
                .expect("recovery: DOT write into in-memory String is infallible");

            // Edge: Error → Sync token, with discount annotation
            let discount = self.prediction_discount(token_id);
            let label = if (discount - 1.0).abs() < 1e-9 {
                token_name.clone()
            } else {
                format!("{} (B1 disc={:.2})", token_name, discount)
            };
            let color = if discount < 1.0 { "blue" } else { "black" };
            writeln!(out, "  error -> {} [label=\"{}\", color={}];", node_id, label, color)
                .expect("recovery: DOT write into in-memory String is infallible");
        }

        writeln!(out, "}}").expect("recovery: DOT write into in-memory String is infallible");
        out
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Builder — construct RecoveryWfsts for all categories
// ══════════════════════════════════════════════════════════════════════════════

/// Build recovery WFSTs for all categories from their FOLLOW sets and grammar terminals.
///
/// This mirrors the construction in `prediction::generate_sync_predicate()` but
/// produces a structured `RecoveryWfst` instead of generated code.
pub fn build_recovery_wfsts(
    categories: &[String],
    follow_sets: &std::collections::HashMap<String, crate::prediction::FirstSet>,
    grammar_terminals: &std::collections::HashSet<String>,
    token_map: &TokenIdMap,
    prediction_wfsts: Option<&std::collections::HashMap<String, crate::wfst::PredictionWfst>>,
) -> Vec<RecoveryWfst> {
    let structural = [
        ("RParen", ")"),
        ("RBrace", "}"),
        ("RBracket", "]"),
        ("Semi", ";"),
        ("Comma", ","),
    ];

    categories
        .iter()
        .map(|category| {
            let mut sync_names: Vec<String> = Vec::new();

            // Always include Eof
            sync_names.push("Eof".to_string());

            // Structural delimiters present in the grammar
            for (variant, terminal) in &structural {
                if grammar_terminals.contains(*terminal) {
                    sync_names.push(variant.to_string());
                }
            }

            // FOLLOW set tokens
            if let Some(follow_set) = follow_sets.get(category) {
                for token in &follow_set.tokens {
                    if !sync_names.contains(token) {
                        sync_names.push(token.clone());
                    }
                }
            }

            let mut wfst = RecoveryWfst::new(category.clone(), &sync_names, token_map);

            // B1: Compute prediction discounts for sync tokens from prediction WFST.
            //
            // For each sync token, query the category's prediction WFST to get the
            // minimum weight. Tokens appearing in the FIRST set with low weight
            // (high confidence) get larger discounts, making them preferred recovery
            // targets for insert/substitute/skip-to-sync strategies.
            if let Some(pred_wfsts) = prediction_wfsts {
                if let Some(pred) = pred_wfsts.get(category) {
                    let mut discounts = std::collections::HashMap::new();
                    for sync_name in &sync_names {
                        if let Some(sync_id) = token_map.get(sync_name) {
                            let predictions = pred.predict(sync_name);
                            if let Some(best) = predictions.first() {
                                // discount = max(1.0 - best_weight, 0.1)
                                // weight 0.0 → discount 1.0 (no discount: already best)
                                // weight 0.5 → discount 0.5 (moderate discount)
                                // weight 2.0 → discount 0.1 (minimal floor)
                                let discount = (1.0 - best.weight.value().min(0.9)).max(0.1);
                                discounts.insert(sync_id, discount);
                            }
                            // Tokens not in FIRST set get no discount (1.0 = no entry)
                        }
                    }
                    wfst.set_prediction_discounts(discounts);

                    // A1: Compute follow contexts for sync tokens.
                    //
                    // For each sync token, determine which rules (identified by bit
                    // position in a ContextWeight) can reach that token. Rules are
                    // indexed by their position in the prediction WFST's action table.
                    //
                    // The approach:
                    // - For each dispatch token D in the prediction WFST, get the rules
                    //   it dispatches to (from predict(D)).
                    // - For each rule R (indexed by its position in the action table),
                    //   record that ALL sync tokens are reachable (conservative).
                    // - Then, for sync tokens that are also FIRST set tokens, refine:
                    //   they're only reachable from rules that dispatch on tokens
                    //   sharing the same FOLLOW set.
                    //
                    // We assign rule indices = action index in the WFST action table
                    // (capped at 127 for the 128-bit ContextWeight capacity).
                    let mut follow_ctxs: std::collections::HashMap<
                        TokenId,
                        crate::automata::semiring::ContextWeight,
                    > = std::collections::HashMap::new();

                    // Structural sync tokens (Eof, RParen, etc.) are always reachable
                    // from any rule → ContextWeight::one()
                    let structural_names: std::collections::HashSet<&str> =
                        ["Eof", "RParen", "RBrace", "RBracket", "Semi", "Comma"]
                            .into_iter()
                            .collect();

                    for sync_name in &sync_names {
                        if let Some(sync_id) = token_map.get(sync_name) {
                            if structural_names.contains(sync_name.as_str()) {
                                follow_ctxs.insert(
                                    sync_id,
                                    crate::automata::semiring::ContextWeight::one(),
                                );
                            } else {
                                // Non-structural FOLLOW token: compute which rules can reach it.
                                // A rule can reach this sync token if any of its dispatch tokens
                                // share a FOLLOW context with this token.
                                // For now, use a conservative approach: check all dispatch tokens
                                // in the WFST and union the rule bits for tokens that are
                                // associated with rules whose FOLLOW set includes sync_name.
                                let mut reachable =
                                    crate::automata::semiring::ContextWeight::zero();

                                // Iterate all tokens that have predictions in this WFST
                                for (action_idx, _action) in pred.actions.iter().enumerate() {
                                    if action_idx < 128 {
                                        // Conservatively: all actions can reach any FOLLOW token
                                        // This will be refined later with per-rule FOLLOW analysis
                                        reachable = reachable.insert(action_idx as u8);
                                    }
                                }

                                if reachable.is_zero() {
                                    // No actions → use one() (don't filter)
                                    follow_ctxs.insert(
                                        sync_id,
                                        crate::automata::semiring::ContextWeight::one(),
                                    );
                                } else {
                                    follow_ctxs.insert(sync_id, reachable);
                                }
                            }
                        }
                    }

                    wfst.set_follow_contexts(follow_ctxs);
                }
            }

            wfst
        })
        .collect()
}

// ══════════════════════════════════════════════════════════════════════════════
// Context-Aware Recovery — combines all 3 tiers
// ══════════════════════════════════════════════════════════════════════════════

impl RecoveryWfst {
    /// Find the best recovery action with context-aware cost adjustments.
    ///
    /// Combines all four tiers:
    /// - **Tier 1**: Frame context (depth, binding power, frame kind)
    /// - **Tier 2**: FOLLOW stratification + bracket balance
    /// - **Tier 3**: Predictive repair simulation (optional)
    /// - **Tier 4**: B1 prediction WFST discount (grammar-aware token preference)
    ///
    /// Falls back to `find_best_recovery()` behavior when `ctx` has default
    /// values and `simulator` is `None`.
    pub fn find_best_recovery_contextual(
        &self,
        token_ids: &[TokenId],
        pos: usize,
        ctx: &RecoveryContext,
        simulator: Option<&ParseSimulator>,
        category: &str,
    ) -> Option<RepairResult> {
        let default_config = RecoveryConfig::default();
        self.find_best_recovery_contextual_with_config(
            token_ids,
            pos,
            ctx,
            simulator,
            category,
            &default_config,
        )
    }

    /// Find the best recovery action with context-aware cost adjustments
    /// using the supplied recovery configuration.
    pub fn find_best_recovery_contextual_with_config(
        &self,
        token_ids: &[TokenId],
        pos: usize,
        ctx: &RecoveryContext,
        simulator: Option<&ParseSimulator>,
        category: &str,
        config: &RecoveryConfig,
    ) -> Option<RepairResult> {
        self.find_best_recovery_contextual_with_config_filtered(
            token_ids,
            pos,
            ctx,
            simulator,
            category,
            config,
            |_| true,
        )
    }

    /// Find the best configured contextual recovery action satisfying an
    /// additional candidate predicate.
    pub(crate) fn find_best_recovery_contextual_with_config_filtered<F>(
        &self,
        token_ids: &[TokenId],
        pos: usize,
        ctx: &RecoveryContext,
        simulator: Option<&ParseSimulator>,
        category: &str,
        config: &RecoveryConfig,
        mut accept_candidate: F,
    ) -> Option<RepairResult>
    where
        F: FnMut(&RepairResult) -> bool,
    {
        let normalized_config = config.normalized_for_recovery_search();
        let config = &normalized_config;
        let remaining = token_ids.get(pos..)?;
        let mut best: Option<RepairResult> = None;

        // ── Strategy 1: SkipToSync ─────────────────────────────────────────
        let max_lookahead = remaining.len().min(config.max_skip_lookahead);
        #[allow(clippy::needless_range_loop)]
        // `skip` used for arithmetic, cost calc, struct field, and position offset
        for skip in 0..max_lookahead {
            let token_at = remaining[skip];
            if self.sync_tokens.contains(&token_at) {
                let base_cost = if skip == 0 {
                    TropicalWeight::one()
                } else {
                    TropicalWeight::new(skip as f64 * config.skip_per_token)
                };

                // Tier 1: frame context multiplier for skip
                let tier1_mult = ctx.skip_multiplier_with(config);

                // Tier 3: simulation after the skip
                let tier3_mult = if let Some(sim) = simulator {
                    let sim_result = sim.simulate_after_repair(token_ids, pos + skip, category);
                    sim.cost_multiplier_with(&sim_result, config)
                } else {
                    1.0
                };

                let action = RepairAction::SkipToSync { skip_count: skip, sync_token: token_at };
                let adjusted_cost = if base_cost == TropicalWeight::one() {
                    RecoveryCost::one() // zero-cost sync: don't multiply
                } else {
                    // Tier 4: B1 prediction discount
                    let tier4_mult = self.prediction_discount(token_at);
                    // Tier 5 (Sprint 7): ContextWeight viability
                    let tier5_mult = self
                        .follow_contexts
                        .get(&token_at)
                        .map_or(1.0, |fc| ctx.context_viability_multiplier(fc));
                    // Sprint C2: Liveness — penalize skip in recursive categories
                    // Breaking out of a recursive loop via skip is structurally damaging.
                    let liveness_skip_mult = if self.recursive_category { 1.3 } else { 1.0 };
                    costs::joint_edit(
                        base_cost.value()
                            * tier1_mult
                            * tier3_mult
                            * tier4_mult
                            * tier5_mult
                            * liveness_skip_mult,
                        action.edit_cost(),
                    )
                };

                let result = RepairResult {
                    action,
                    new_pos: pos + skip,
                    cost: adjusted_cost,
                };
                best = pick_better_if_allowed(best, result, &mut accept_candidate);
                break; // first sync point only
            }
        }

        // ── Strategy 2: DeleteToken ────────────────────────────────────────
        if !remaining.is_empty() {
            let base_cost = TropicalWeight::new(config.delete_cost);
            // Delete is a mild skip variant — use skip multiplier
            let tier1_mult = ctx.skip_multiplier_with(config);

            let tier3_mult = if let Some(sim) = simulator {
                let sim_result = sim.simulate_after_repair(token_ids, pos + 1, category);
                sim.cost_multiplier_with(&sim_result, config)
            } else {
                1.0
            };

            let action = RepairAction::DeleteToken;
            let result = RepairResult {
                cost: costs::joint_edit(
                    base_cost.value() * tier1_mult * tier3_mult,
                    action.edit_cost(),
                ),
                action,
                new_pos: pos + 1,
            };
            best = pick_better_if_allowed(best, result, &mut accept_candidate);
        }

        // ── Strategy 3: InsertToken ────────────────────────────────────────
        for &sync_id in &self.sync_tokens {
            let base_cost = TropicalWeight::new(config.insert_cost);

            // Tier 1: frame context multiplier for insert
            let tier1_mult = ctx.insert_multiplier_with(config);

            // Tier 2: bracket balance multiplier
            let token_name = self.token_map.name(sync_id);
            let tier2_mult = ctx.bracket_insert_multiplier_with(token_name, config);

            // Tier 3: simulation after inserting this token
            let tier3_mult = if let Some(sim) = simulator {
                let sim_result = sim.simulate_after_repair(token_ids, pos, category);
                sim.cost_multiplier_with(&sim_result, config)
            } else {
                1.0
            };

            // Tier 4: B1 prediction discount — prefer inserting high-confidence tokens
            let tier4_mult = self.prediction_discount(sync_id);

            // Sprint A2: bracket mismatch penalty — penalize inserting ambiguous bracket tokens
            let bracket_mult = self.bracket_mismatch_penalty(sync_id);

            // Sprint C2: Liveness — discount insert in recursive categories
            // Inserting tokens to maintain a recursive loop is structurally preserving.
            let liveness_insert_mult = if self.recursive_category { 0.7 } else { 1.0 };

            let action = RepairAction::InsertToken { token: sync_id };
            let result = RepairResult {
                cost: costs::joint_edit(
                    base_cost.value()
                        * tier1_mult
                        * tier2_mult
                        * tier3_mult
                        * tier4_mult
                        * bracket_mult
                        * liveness_insert_mult,
                    action.edit_cost(),
                ),
                action,
                new_pos: pos,
            };
            best = pick_better_if_allowed(best, result, &mut accept_candidate);
        }

        // ── Strategy 4: SubstituteToken ────────────────────────────────────
        if !remaining.is_empty() {
            for &sync_id in &self.sync_tokens {
                let base_cost = TropicalWeight::new(config.substitute_cost);

                // Tier 1: frame context multiplier for substitute
                let tier1_mult = ctx.substitute_multiplier_with(config);

                let tier3_mult = if let Some(sim) = simulator {
                    let sim_result = sim.simulate_after_repair(token_ids, pos + 1, category);
                    sim.cost_multiplier_with(&sim_result, config)
                } else {
                    1.0
                };

                // Tier 4: B1 prediction discount — prefer substituting with high-confidence tokens
                let tier4_mult = self.prediction_discount(sync_id);

                let action = RepairAction::SubstituteToken { replacement: sync_id };
                let result = RepairResult {
                    cost: costs::joint_edit(
                        base_cost.value() * tier1_mult * tier3_mult * tier4_mult,
                        action.edit_cost(),
                    ),
                    action,
                    new_pos: pos + 1,
                };
                best = pick_better_if_allowed(best, result, &mut accept_candidate);
            }
        }

        // ── Strategy 5: SwapTokens ───────────────────────────────────────
        if remaining.len() >= 2 {
            let swapped_first = remaining[1];
            if self.sync_tokens.contains(&swapped_first) {
                let base_cost = config.swap_cost;
                let tier1_mult = ctx.skip_multiplier_with(config); // swap is a mild reorder

                let tier3_mult = if let Some(sim) = simulator {
                    let sim_result = sim.simulate_after_repair(token_ids, pos + 2, category);
                    sim.cost_multiplier_with(&sim_result, config)
                } else {
                    1.0
                };

                // Tier 4: B1 prediction discount on the sync token revealed by the swap
                let tier4_mult = self.prediction_discount(swapped_first);

                let action = RepairAction::SwapTokens { pos_a: pos, pos_b: pos + 1 };
                let result = RepairResult {
                    cost: costs::joint_edit(
                        base_cost * tier1_mult * tier3_mult * tier4_mult,
                        action.edit_cost(),
                    ),
                    action,
                    new_pos: pos + 2,
                };
                best = pick_better_if_allowed(best, result, &mut accept_candidate);
            }
        }

        best
    }
}
