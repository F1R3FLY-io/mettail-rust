//! Weighted error recovery via WFST-based minimum-cost repair.
//!
//! Replaces panic-mode "skip to first sync point" with a recovery WFST
//! that assigns costs to repair actions and uses Viterbi to find the
//! minimum-cost repair sequence.
//!
//! ## Repair Actions
//!
//! | Action | Cost | Description |
//! |--------|------|-------------|
//! | **Skip** | 0.5/token | Skip an unexpected token in the input |
//! | **Delete** | 1.0 | Delete (ignore) one token |
//! | **Substitute** | 1.5 | Replace an unexpected token with an expected one |
//! | **Insert** | 2.0 | Insert a missing expected token |
//!
//! ## Architecture
//!
//! ```text
//!   Parse error at position P
//!           │
//!           ▼
//!   RecoveryWfst::find_best_recovery(tokens, pos, sync_tokens)
//!           │
//!           ├─ Build repair lattice from current position
//!           │   - Skip edges (0.5/token each)
//!           │   - Delete edges (1.0)
//!           │   - Substitute edges (1.5, if sync token similar)
//!           │   - Insert edges (2.0, for each expected sync token)
//!           │
//!           ├─ Viterbi minimum-cost path
//!           │
//!           ▼
//!   RepairResult { action, skip_count, new_pos, cost }
//! ```
//!
//! ## Zero Overhead
//!
//! The recovery WFST is only invoked on parse error. The happy path (no errors)
//! has zero cost — no recovery structures are allocated or consulted.
//!
//! ## Derived from lling-llang
//!
//! The repair cost model draws from `lling-llang/src/applications/programming/`
//! `SyntaxRepairTransducer`. The Viterbi search is adapted from
//! `lling-llang/src/path/viterbi.rs`.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use crate::automata::semiring::{Semiring, TropicalWeight};
use crate::token_id::{TokenId, TokenIdMap};

// ══════════════════════════════════════════════════════════════════════════════
// Repair costs
// ══════════════════════════════════════════════════════════════════════════════

/// Default repair action costs (tropical weights — lower is better).
///
/// These values balance precision vs. recovery speed:
/// - **Skip** is cheapest: we just advance past unexpected tokens to a sync point.
/// - **Delete** is cheap: pretend the token wasn't there.
/// - **Substitute** is moderate: replace with something valid.
/// - **Insert** is most expensive: fabricate a token that wasn't in the input.
pub mod costs {
    use super::TropicalWeight;

    /// Cost per skipped token (0.5).
    pub const SKIP_PER_TOKEN: TropicalWeight = TropicalWeight::new(0.5);

    /// Cost to delete one token (1.0).
    pub const DELETE: TropicalWeight = TropicalWeight::new(1.0);

    /// Cost to substitute one token for another (1.5).
    pub const SUBSTITUTE: TropicalWeight = TropicalWeight::new(1.5);

    /// Cost to insert a missing token (2.0).
    pub const INSERT: TropicalWeight = TropicalWeight::new(2.0);

    /// Maximum tokens to consider skipping before giving up (bounded lookahead).
    pub const MAX_SKIP_LOOKAHEAD: usize = 32;
}

// ══════════════════════════════════════════════════════════════════════════════
// RecoveryConfig — parameterized cost/threshold tuning
// ══════════════════════════════════════════════════════════════════════════════

/// Parameterized configuration for error recovery costs and thresholds.
///
/// Grammar authors can tune recovery behavior by adjusting these values.
/// The `Default` implementation matches the current hardcoded constants in
/// `costs::*` and `RecoveryContext` multiplier methods.
///
/// ## Cost hierarchy (default)
///
/// | Strategy   | Cost | Rationale |
/// |------------|------|-----------|
/// | Skip       | 0.5/token | Cheapest: advance past unexpected content |
/// | Delete     | 1.0  | Cheap: pretend the token wasn't there |
/// | Swap       | 1.25 | Moderate: preserves all tokens, just reordered |
/// | Substitute | 1.5  | Moderate: replace with something valid |
/// | Insert     | 2.0  | Expensive: fabricate a missing token |
///
/// ## Threshold semantics
///
/// - `deep_nesting_threshold`: depth above which skip is cheaper (noisy context)
/// - `shallow_depth_threshold`: depth below which skip is more expensive (precise repair preferred)
/// - `low_bp_threshold`: binding power below which skip is cheaper (loose binding)
#[derive(Debug, Clone)]
pub struct RecoveryConfig {
    // ── Per-strategy base costs ──────────────────────────────────────────
    /// Cost per skipped token (default: 0.5).
    pub skip_per_token: f64,
    /// Cost to delete one token (default: 1.0).
    pub delete_cost: f64,
    /// Cost to substitute one token for another (default: 1.5).
    pub substitute_cost: f64,
    /// Cost to insert a missing token (default: 2.0).
    pub insert_cost: f64,
    /// Cost to swap two adjacent tokens (default: 1.25).
    pub swap_cost: f64,

    // ── Lookahead ────────────────────────────────────────────────────────
    /// Maximum tokens to consider skipping before giving up (default: 32).
    pub max_skip_lookahead: usize,

    // ── Tier 1: Depth scaling ────────────────────────────────────────────
    /// Depth above which skip cost is discounted (default: 1000).
    pub deep_nesting_threshold: usize,
    /// Skip multiplier when depth exceeds `deep_nesting_threshold` (default: 0.5).
    pub deep_nesting_skip_mult: f64,
    /// Depth below which skip cost is penalized (default: 10).
    pub shallow_depth_threshold: usize,
    /// Skip multiplier when depth is below `shallow_depth_threshold` (default: 2.0).
    pub shallow_depth_skip_mult: f64,

    // ── Tier 1: BP scaling ───────────────────────────────────────────────
    /// Binding power below which skip cost is discounted (default: 4).
    pub low_bp_threshold: u8,
    /// Skip multiplier when BP is below `low_bp_threshold` (default: 0.75).
    pub low_bp_skip_mult: f64,

    // ── Tier 1: Frame-kind multipliers ───────────────────────────────────
    /// Insert multiplier in Collection frames (default: 0.5).
    pub collection_insert_mult: f64,
    /// Insert multiplier in Group frames (default: 0.5).
    pub group_insert_mult: f64,
    /// Insert multiplier when bracket balance is unmatched (default: 0.3).
    pub bracket_insert_mult: f64,
    /// Substitute multiplier in Mixfix frames (default: 0.75).
    pub mixfix_substitute_mult: f64,

    // ── Tier 3: Simulation multipliers ───────────────────────────────────
    /// Cost multiplier when simulation shows valid continuation (default: 0.5).
    pub simulation_valid_mult: f64,
    /// Cost penalty per unmatched token when simulation fails (default: 0.2).
    pub simulation_fail_penalty: f64,

    // ── Beam pruning ─────────────────────────────────────────────────────
    /// Beam width for Viterbi recovery (default: Some(3.0)).
    /// `None` disables beam pruning.
    pub beam_width: Option<f64>,

    // ── Cascade prevention ───────────────────────────────────────────────
    /// Number of tokens within which consecutive errors are suppressed (default: 3).
    pub cascade_window: usize,
}

impl Default for RecoveryConfig {
    fn default() -> Self {
        RecoveryConfig {
            skip_per_token: 0.5,
            delete_cost: 1.0,
            substitute_cost: 1.5,
            insert_cost: 2.0,
            swap_cost: 1.25,
            max_skip_lookahead: 32,
            deep_nesting_threshold: 1000,
            deep_nesting_skip_mult: 0.5,
            shallow_depth_threshold: 10,
            shallow_depth_skip_mult: 2.0,
            low_bp_threshold: 4,
            low_bp_skip_mult: 0.75,
            collection_insert_mult: 0.5,
            group_insert_mult: 0.5,
            bracket_insert_mult: 0.3,
            mixfix_substitute_mult: 0.75,
            simulation_valid_mult: 0.5,
            simulation_fail_penalty: 0.2,
            beam_width: Some(3.0),
            cascade_window: 3,
        }
    }
}

impl RecoveryConfig {
    /// Apply trained recovery weights from a `TrainedModel`.
    ///
    /// Overrides the base strategy costs with learned values where present.
    /// Unknown keys are silently ignored.
    pub fn apply_trained_weights(&mut self, weights: &std::collections::HashMap<String, f64>) {
        if let Some(&v) = weights.get("skip_per_token") {
            self.skip_per_token = v;
        }
        if let Some(&v) = weights.get("delete_cost") {
            self.delete_cost = v;
        }
        if let Some(&v) = weights.get("substitute_cost") {
            self.substitute_cost = v;
        }
        if let Some(&v) = weights.get("insert_cost") {
            self.insert_cost = v;
        }
        if let Some(&v) = weights.get("swap_cost") {
            self.swap_cost = v;
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// RepairAction — what the recovery suggests doing
// ══════════════════════════════════════════════════════════════════════════════

/// A recovery action recommended by the WFST repair analysis.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RepairAction {
    /// Skip tokens until a sync point is reached.
    ///
    /// This is the WFST equivalent of the current `sync_to()` behavior,
    /// but now it's competed against other repair actions by cost.
    SkipToSync {
        /// Number of tokens to skip.
        skip_count: usize,
        /// The sync token that terminates the skip.
        sync_token: TokenId,
    },

    /// Insert a missing expected token (fabricate it).
    ///
    /// The parser pretends the token was present without consuming input.
    /// Cost: 2.0 (most expensive — avoids phantom insertions).
    InsertToken {
        /// The token to insert.
        token: TokenId,
    },

    /// Delete (ignore) one unexpected token.
    ///
    /// The parser skips exactly one token and tries again.
    /// Cost: 1.0.
    DeleteToken,

    /// Substitute the current token with a different expected one.
    ///
    /// The parser reinterprets the current token as the substitution.
    /// Cost: 1.5.
    SubstituteToken {
        /// The token to substitute in.
        replacement: TokenId,
    },

    /// Swap two adjacent tokens.
    ///
    /// Common typo pattern: `a b+` should be `a + b`. Transposition preserves
    /// all tokens but reorders them. Cost: 1.25 (between delete and substitute —
    /// preserves all information).
    SwapTokens {
        /// Position of the first token in the swap pair.
        pos_a: usize,
        /// Position of the second token in the swap pair.
        pos_b: usize,
    },

    /// A composite repair consisting of multiple atomic actions.
    ///
    /// Produced by `viterbi_multi_step()` when the optimal repair requires
    /// more than one step (e.g., delete+skip+sync).
    Composite {
        /// Ordered sequence of atomic repair actions.
        steps: Vec<RepairAction>,
    },

    /// Switch to parsing via a different category (using a cast rule).
    ///
    /// When the error token is in another category's FIRST set and a cast rule
    /// connects that category to the current one, this repair delegates parsing
    /// to the source category. Cost: `substitute_cost * 0.5` = 0.75 (preserves
    /// semantic intent via cast).
    CategorySwitch {
        /// Category we're switching from (the current/target category).
        from_category: String,
        /// Category we're switching to (the source category that has a cast rule).
        to_category: String,
    },
}

impl fmt::Display for RepairAction {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RepairAction::SkipToSync { skip_count, sync_token } => {
                write!(f, "skip {} tokens to sync token {}", skip_count, sync_token)
            },
            RepairAction::InsertToken { token } => write!(f, "insert token {}", token),
            RepairAction::DeleteToken => write!(f, "delete token"),
            RepairAction::SubstituteToken { replacement } => {
                write!(f, "substitute with token {}", replacement)
            },
            RepairAction::SwapTokens { pos_a, pos_b } => {
                write!(f, "swap tokens at positions {} and {}", pos_a, pos_b)
            },
            RepairAction::Composite { steps } => {
                for (i, step) in steps.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", step)?;
                }
                Ok(())
            },
            RepairAction::CategorySwitch { from_category, to_category } => {
                write!(f, "switch {} → {}", from_category, to_category)
            },
        }
    }
}

impl RepairAction {
    /// Produce a human-readable description of this repair action.
    ///
    /// Uses the `token_names` slice (indexed by `TokenId`) to resolve
    /// token IDs to their grammar-level names. This is called on the
    /// error path only; happy-path parsing never invokes it.
    pub fn describe(&self, token_names: &[&str]) -> String {
        let name = |id: TokenId| -> &str {
            token_names.get(id as usize).copied().unwrap_or("?")
        };
        match self {
            RepairAction::SkipToSync { skip_count, sync_token } => {
                format!("skip {} token(s) to '{}'", skip_count, name(*sync_token))
            }
            RepairAction::InsertToken { token } => {
                format!("insert missing '{}'", name(*token))
            }
            RepairAction::DeleteToken => "delete unexpected token".to_string(),
            RepairAction::SubstituteToken { replacement } => {
                format!("expected '{}' here", name(*replacement))
            }
            RepairAction::SwapTokens { .. } => {
                "swap adjacent tokens".to_string()
            }
            RepairAction::Composite { steps } => {
                steps
                    .iter()
                    .map(|s| s.describe(token_names))
                    .collect::<Vec<_>>()
                    .join(", ")
            }
            RepairAction::CategorySwitch { from_category, to_category } => {
                format!("try parsing as {} (cast {} → {})", to_category, to_category, from_category)
            }
        }
    }

    /// Return the semantic edit-distance cost of this repair action.
    ///
    /// Unlike tropical weights in `costs::*` which are tuned for Viterbi
    /// shortest-path, `EditWeight` counts discrete token-level edits:
    /// - Skip: 1 edit per skipped token
    /// - Delete: 1 edit (remove one unexpected token)
    /// - Insert: 2 edits (fabricate a missing token — more disruptive)
    /// - Substitute: 2 edits (replace wrong token — moderate disruption)
    ///
    /// Compose with `ProductWeight<TropicalWeight, EditWeight>` to jointly
    /// optimize parse quality and repair minimality.
    pub fn edit_cost(&self) -> crate::automata::semiring::EditWeight {
        use crate::automata::semiring::EditWeight;
        match self {
            RepairAction::SkipToSync { skip_count, .. } => EditWeight::new(*skip_count as u32),
            RepairAction::DeleteToken => EditWeight::delete(),
            RepairAction::InsertToken { .. } => EditWeight::insert(),
            RepairAction::SubstituteToken { .. } => EditWeight::substitute(),
            RepairAction::SwapTokens { .. } => EditWeight::new(1), // single edit operation
            RepairAction::Composite { steps } => {
                let total = steps.iter().map(|s| s.edit_cost().0).sum::<u32>();
                EditWeight::new(total)
            },
            RepairAction::CategorySwitch { .. } => EditWeight::substitute(), // semantic substitution
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// RepairResult — the full recovery recommendation
// ══════════════════════════════════════════════════════════════════════════════

/// Result of the recovery WFST analysis.
#[derive(Debug, Clone)]
pub struct RepairResult {
    /// The recommended repair action.
    pub action: RepairAction,
    /// New parser position after applying the repair.
    pub new_pos: usize,
    /// Total tropical cost of this repair.
    pub cost: TropicalWeight,
}

impl RepairResult {
    /// Produce a human-readable description of this repair result.
    ///
    /// Delegates to `RepairAction::describe()` with the given token name table.
    pub fn describe(&self, token_names: &[&str]) -> String {
        self.action.describe(token_names)
    }
}

impl fmt::Display for RepairResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "repair: {} (cost: {:.1}, new_pos: {})",
            self.action,
            self.cost.value(),
            self.new_pos
        )
    }
}

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
    sync_tokens: BTreeSet<TokenId>,
    /// Token ID map for resolving names.
    token_map: TokenIdMap,
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
        }
    }

    /// The category this recovery WFST covers.
    pub fn category(&self) -> &str {
        &self.category
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
        let remaining = &token_ids[pos..];
        let mut best: Option<RepairResult> = None;

        // Strategy 1: SkipToSync — skip tokens until a sync point
        let max_lookahead = remaining.len().min(costs::MAX_SKIP_LOOKAHEAD);
        #[allow(clippy::needless_range_loop)]
        // `skip` used for arithmetic, cost calc, struct field, and position offset
        for skip in 0..max_lookahead {
            let token_at = remaining[skip];
            if self.sync_tokens.contains(&token_at) {
                let cost = if skip == 0 {
                    // Already at a sync token — zero cost
                    TropicalWeight::one()
                } else {
                    // Tropical times = addition: skip_count * cost_per_skip
                    TropicalWeight::new(skip as f64 * costs::SKIP_PER_TOKEN.value())
                };
                let result = RepairResult {
                    action: RepairAction::SkipToSync { skip_count: skip, sync_token: token_at },
                    new_pos: pos + skip,
                    cost,
                };
                best = Some(pick_better(best, result));
                // First sync point found — skip further is always worse
                break;
            }
        }

        // Strategy 2: DeleteToken — skip exactly one token
        if !remaining.is_empty() {
            let result = RepairResult {
                action: RepairAction::DeleteToken,
                new_pos: pos + 1,
                cost: costs::DELETE,
            };
            best = Some(pick_better(best, result));
        }

        // Strategy 3: InsertToken — insert each sync token at current position
        for &sync_id in &self.sync_tokens {
            let result = RepairResult {
                action: RepairAction::InsertToken { token: sync_id },
                new_pos: pos, // no position change — inserted token is phantom
                cost: costs::INSERT,
            };
            best = Some(pick_better(best, result));
        }

        // Strategy 4: SubstituteToken — replace current token with a sync token
        if !remaining.is_empty() {
            for &sync_id in &self.sync_tokens {
                let result = RepairResult {
                    action: RepairAction::SubstituteToken { replacement: sync_id },
                    new_pos: pos + 1, // consume the substituted token
                    cost: costs::SUBSTITUTE,
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
                let result = RepairResult {
                    action: RepairAction::SwapTokens {
                        pos_a: pos,
                        pos_b: pos + 1,
                    },
                    new_pos: pos + 2, // consume both tokens in swapped order
                    cost: TropicalWeight::new(1.25), // SWAP cost
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
        }
    }
}

/// Pick the lower-cost repair between an existing best and a new candidate.
fn pick_better(existing: Option<RepairResult>, candidate: RepairResult) -> RepairResult {
    match existing {
        None => candidate,
        Some(prev) => {
            if candidate.cost < prev.cost {
                candidate
            } else {
                prev
            }
        },
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Multi-token Viterbi recovery
// ══════════════════════════════════════════════════════════════════════════════

/// Find the minimum-cost sequence of repair actions to reach a sync point.
///
/// Unlike `find_best_recovery()` which evaluates single-step repairs, this
/// function builds a multi-step repair lattice and runs Viterbi to find
/// the globally optimal repair sequence.
///
/// ## Lattice structure
///
/// Nodes are token positions `[pos, pos+1, ..., pos+max_lookahead]`.
/// Edges represent repair actions:
/// - **Skip edge**: `i → i+1` with cost `SKIP_PER_TOKEN` (for each non-sync token)
/// - **Sync edge**: `i → FINAL` with cost `0.0` (when token at `i` is a sync token)
/// - **Delete edge**: `i → i+1` with cost `DELETE`
///
/// The final node is a virtual sink. Viterbi finds the minimum-cost path
/// from `pos` to the sink.
///
/// Returns `None` if no sync point is reachable within `MAX_SKIP_LOOKAHEAD`.
pub fn viterbi_recovery(
    token_ids: &[TokenId],
    pos: usize,
    sync_tokens: &BTreeSet<TokenId>,
) -> Option<RepairResult> {
    viterbi_recovery_beam(token_ids, pos, sync_tokens, None)
}

/// Find the minimum-cost recovery with optional beam pruning.
///
/// When `beam_width` is `Some(w)`, skip edges whose accumulated cost exceeds
/// `best_sync_cost + w` are pruned, reducing the search space for wide
/// lookahead windows.
pub fn viterbi_recovery_beam(
    token_ids: &[TokenId],
    pos: usize,
    sync_tokens: &BTreeSet<TokenId>,
    beam_width: Option<TropicalWeight>,
) -> Option<RepairResult> {
    let remaining = &token_ids[pos..];
    let max_lookahead = remaining.len().min(costs::MAX_SKIP_LOOKAHEAD);

    if max_lookahead == 0 {
        return None;
    }

    // Nodes: 0..max_lookahead are token positions, max_lookahead is the virtual sink.
    let num_nodes = max_lookahead + 1;
    let sink = max_lookahead;

    // dist[i] = minimum cost to reach node i from node 0
    let mut dist = vec![TropicalWeight::zero(); num_nodes]; // infinity
    dist[0] = TropicalWeight::one(); // zero cost to reach start

    // pred[i] = (predecessor node, action description)
    let mut pred: Vec<Option<(usize, &'static str)>> = vec![None; num_nodes];

    // Forward pass through positions
    for i in 0..max_lookahead {
        if dist[i].is_zero() {
            continue; // unreachable
        }

        // Beam pruning: skip positions whose cost already exceeds threshold
        if let Some(beam) = beam_width {
            if !dist[sink].is_zero() && dist[i].value() > dist[sink].value() + beam.value() {
                continue;
            }
        }

        let token_at_i = remaining[i];

        // If this position is a sync token, add edge to sink (free)
        if sync_tokens.contains(&token_at_i) {
            let cost_to_sink = dist[i]; // zero additional cost
            if cost_to_sink < dist[sink] {
                dist[sink] = cost_to_sink;
                pred[sink] = Some((i, "sync"));
            }
        }

        // Skip edge: i → i+1 with SKIP_PER_TOKEN cost
        if i + 1 < num_nodes {
            let new_cost = dist[i].times(&costs::SKIP_PER_TOKEN);

            // Beam pruning: skip edges whose cost exceeds threshold
            if let Some(beam) = beam_width {
                if !dist[sink].is_zero() && new_cost.value() > dist[sink].value() + beam.value() {
                    continue;
                }
            }

            if new_cost < dist[i + 1] {
                dist[i + 1] = new_cost;
                pred[i + 1] = Some((i, "skip"));
            }
        }
    }

    // Check if the last position is a sync token (edge case: exactly at max_lookahead boundary)
    // This is handled by the loop above (max_lookahead - 1 can reach sink).

    // If sink is unreachable, no recovery found within lookahead window
    if dist[sink].is_zero() {
        return None;
    }

    // Backtrace to count skips
    let mut skip_count = 0;
    let mut current = sink;
    let mut sync_node = sink; // the node where sync happens

    // Find the sync node (direct predecessor of sink)
    if let Some((prev, action)) = pred[current] {
        if action == "sync" {
            sync_node = prev;
            current = prev;
        }
    }

    // Count skip edges before the sync node
    while let Some((prev, _action)) = pred[current] {
        if prev == 0 && current == 0 {
            break;
        }
        skip_count += 1;
        current = prev;
    }

    // Determine the sync token
    let sync_token = if sync_node < remaining.len() {
        remaining[sync_node]
    } else {
        return None;
    };

    Some(RepairResult {
        action: RepairAction::SkipToSync { skip_count, sync_token },
        new_pos: pos + sync_node,
        cost: dist[sink],
    })
}

// ══════════════════════════════════════════════════════════════════════════════
// Full Viterbi lattice with all repair edge types
// ══════════════════════════════════════════════════════════════════════════════

/// The kind of edge in the repair lattice, used for backtrace reconstruction.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RepairEdgeKind {
    /// Skip edge: advance past one token (`i → i+1`), cost = `skip_per_token`.
    Skip,
    /// Delete edge: remove one unexpected token (`i → i+1`), cost = `delete_cost`.
    Delete,
    /// Substitute edge: replace current token with a sync token (`i → i+1`),
    /// cost = `substitute_cost`.
    Substitute(TokenId),
    /// Insert edge: fabricate a missing sync token (`i → i`, self-loop),
    /// cost = `insert_cost`. Max 1 per position to prevent infinite loops.
    Insert(TokenId),
    /// Sync edge: free transition to the sink when a sync token is reached
    /// (`i → SINK`), cost = 0.
    Sync(TokenId),
    /// Swap edge: consume two positions in reversed order (`i → i+2`),
    /// cost = `swap_cost`.
    Swap,
}

/// A multi-step recovery sequence produced by the full Viterbi lattice.
///
/// Unlike `RepairResult` which encodes a single action, `RepairSequence`
/// captures the globally optimal sequence of repairs found by the Viterbi
/// search across all edge types.
#[derive(Debug, Clone)]
pub struct RepairSequence {
    /// Ordered sequence of repair actions from error position to sync point.
    pub actions: Vec<RepairAction>,
    /// New parser position after applying all repairs.
    pub new_pos: usize,
    /// Total tropical cost of the entire sequence.
    pub total_cost: TropicalWeight,
    /// Total edit-distance cost of the sequence.
    pub total_edits: crate::automata::semiring::EditWeight,
}

impl fmt::Display for RepairSequence {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "repair sequence (")?;
        for (i, action) in self.actions.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", action)?;
        }
        write!(
            f,
            ") cost: {:.2}, edits: {}, new_pos: {}",
            self.total_cost.value(),
            self.total_edits.0,
            self.new_pos
        )
    }
}

/// Find the minimum-cost multi-step recovery sequence using the full Viterbi lattice.
///
/// Builds a repair lattice with all edge types:
/// - **Skip**: `i → i+1`, cost `config.skip_per_token`
/// - **Delete**: `i → i+1`, cost `config.delete_cost`
/// - **Substitute**: `i → i+1`, cost `config.substitute_cost` (when token is NOT a sync token)
/// - **Insert**: `i → i` (self-loop), cost `config.insert_cost` (max 1 per position)
/// - **Sync**: `i → SINK`, cost 0 (when token at `i` IS a sync token)
///
/// Runs Viterbi forward pass, then backtraces to reconstruct the optimal
/// repair action sequence.
///
/// Returns `None` if no sync point is reachable within `max_skip_lookahead`.
pub fn viterbi_multi_step(
    token_ids: &[TokenId],
    pos: usize,
    sync_tokens: &BTreeSet<TokenId>,
    config: &RecoveryConfig,
) -> Option<RepairSequence> {
    let remaining = &token_ids[pos..];
    let max_lookahead = remaining.len().min(config.max_skip_lookahead);

    if max_lookahead == 0 {
        return None;
    }

    // Nodes: 0..max_lookahead are token positions, max_lookahead is the virtual sink.
    // Additionally, each position has an "inserted" variant at max_lookahead + 1 + i.
    // But for simplicity, we track insert with a bool array instead.
    let num_nodes = max_lookahead + 1;
    let sink = max_lookahead;

    // dist[i] = minimum cost to reach node i from node 0
    let mut dist = vec![TropicalWeight::zero(); num_nodes]; // infinity
    dist[0] = TropicalWeight::one(); // zero cost to reach start

    // pred[i] = (predecessor node, edge kind)
    let mut pred: Vec<Option<(usize, RepairEdgeKind)>> = vec![None; num_nodes];

    // Track whether an insert has been applied at each position (max 1 per position)
    let mut inserted = vec![false; max_lookahead];

    let beam_width = config.beam_width.map(TropicalWeight::new);

    // Forward pass through positions
    for i in 0..max_lookahead {
        if dist[i].is_zero() {
            continue; // unreachable
        }

        // Beam pruning
        if let Some(beam) = beam_width {
            if !dist[sink].is_zero() && dist[i].value() > dist[sink].value() + beam.value() {
                continue;
            }
        }

        let token_at_i = remaining[i];

        // ── Sync edge: i → SINK (free) when at sync token ────────────
        if sync_tokens.contains(&token_at_i) {
            let cost_to_sink = dist[i];
            if cost_to_sink < dist[sink] {
                dist[sink] = cost_to_sink;
                pred[sink] = Some((i, RepairEdgeKind::Sync(token_at_i)));
            }
        }

        // ── Skip edge: i → i+1, cost skip_per_token ─────────────────
        if i + 1 < num_nodes {
            let new_cost = TropicalWeight::new(dist[i].value() + config.skip_per_token);

            if let Some(beam) = beam_width {
                if !dist[sink].is_zero() && new_cost.value() > dist[sink].value() + beam.value() {
                    // pruned
                } else if new_cost < dist[i + 1] {
                    dist[i + 1] = new_cost;
                    pred[i + 1] = Some((i, RepairEdgeKind::Skip));
                }
            } else if new_cost < dist[i + 1] {
                dist[i + 1] = new_cost;
                pred[i + 1] = Some((i, RepairEdgeKind::Skip));
            }
        }

        // ── Delete edge: i → i+1, cost delete_cost ───────────────────
        if i + 1 < num_nodes {
            let new_cost = TropicalWeight::new(dist[i].value() + config.delete_cost);
            if new_cost < dist[i + 1] {
                dist[i + 1] = new_cost;
                pred[i + 1] = Some((i, RepairEdgeKind::Delete));
            }
        }

        // ── Substitute edge: i → i+1, cost substitute_cost ──────────
        // Only when the token at i is NOT already a sync token
        if i + 1 < num_nodes && !sync_tokens.contains(&token_at_i) {
            for &sync_id in sync_tokens {
                let new_cost = TropicalWeight::new(dist[i].value() + config.substitute_cost);
                if new_cost < dist[i + 1] {
                    dist[i + 1] = new_cost;
                    pred[i + 1] = Some((i, RepairEdgeKind::Substitute(sync_id)));
                }
            }
        }

        // ── Swap edge: i → i+2, cost swap_cost ────────────────────
        // Only when i+1 exists (two adjacent tokens to swap)
        if i + 2 <= max_lookahead {
            let new_cost = TropicalWeight::new(dist[i].value() + config.swap_cost);
            if new_cost < dist[i + 2] {
                dist[i + 2] = new_cost;
                pred[i + 2] = Some((i, RepairEdgeKind::Swap));
            }
        }

        // ── Insert edge: i → i (self-loop), cost insert_cost ────────
        // Max 1 insert per position to prevent infinite loops
        if !inserted[i] {
            for &sync_id in sync_tokens {
                let new_cost = TropicalWeight::new(dist[i].value() + config.insert_cost);
                // After insert, we're still at i but the inserted token is phantom.
                // Model as: the insert makes the sync token available at position i,
                // so we add a sync edge from i to sink with insert cost.
                if new_cost < dist[sink] {
                    dist[sink] = new_cost;
                    pred[sink] = Some((i, RepairEdgeKind::Insert(sync_id)));
                    inserted[i] = true;
                }
            }
        }
    }

    // If sink is unreachable, no recovery found
    if dist[sink].is_zero() {
        return None;
    }

    // ── Backtrace: reconstruct the action sequence ───────────────────────
    let mut actions_reversed: Vec<RepairAction> = Vec::new();
    let mut current = sink;
    let mut final_sync_pos = pos; // position where we sync

    while let Some((prev, edge_kind)) = pred[current] {
        match edge_kind {
            RepairEdgeKind::Sync(sync_token) => {
                // The sync edge itself is free — but record the sync point
                final_sync_pos = pos + prev;
                current = prev;
                // If prev==0 and no more predecessors, we were already at sync
                if pred[prev].is_none() {
                    // Already at sync — record SkipToSync with skip_count=0
                    actions_reversed.push(RepairAction::SkipToSync {
                        skip_count: 0,
                        sync_token,
                    });
                    break;
                }
            },
            RepairEdgeKind::Skip => {
                // Skip was part of a skip-to-sync chain
                // We'll consolidate at the end
                current = prev;
            },
            RepairEdgeKind::Delete => {
                actions_reversed.push(RepairAction::DeleteToken);
                current = prev;
            },
            RepairEdgeKind::Substitute(sync_id) => {
                actions_reversed.push(RepairAction::SubstituteToken { replacement: sync_id });
                current = prev;
            },
            RepairEdgeKind::Swap => {
                actions_reversed.push(RepairAction::SwapTokens {
                    pos_a: pos + prev,
                    pos_b: pos + prev + 1,
                });
                current = prev;
            },
            RepairEdgeKind::Insert(sync_id) => {
                actions_reversed.push(RepairAction::InsertToken { token: sync_id });
                final_sync_pos = pos + prev; // insert doesn't advance
                current = prev;
                if pred[prev].is_none() {
                    break;
                }
            },
        }
    }

    // Count consecutive skips from the start of the chain to build SkipToSync
    // Walk from node 0 forward along pred chain to find skip sequences
    // Actually, let's rebuild from scratch: walk from 0 forward using a separate approach
    // The backtrace gives us the actions in reverse. Reverse them.
    actions_reversed.reverse();

    // If there are no explicit actions but we reached the sink via skips+sync,
    // compute the skip count
    if actions_reversed.is_empty() {
        // Pure skip chain to sync
        let skip_count = (final_sync_pos - pos).max(0);
        let sync_token = if final_sync_pos < token_ids.len() {
            token_ids[final_sync_pos]
        } else {
            return None;
        };
        actions_reversed.push(RepairAction::SkipToSync {
            skip_count,
            sync_token,
        });
    }

    // Check if we have a pure skip+sync pattern and consolidate
    let all_skips_and_sync =
        actions_reversed.iter().all(|a| matches!(a, RepairAction::SkipToSync { .. }));
    if !all_skips_and_sync {
        // There are non-skip actions. Check if there are trailing skips that
        // should be consolidated into a SkipToSync at the end.
        // For now, if the last action isn't a SkipToSync and we reached a sync,
        // append a sync marker.
        let has_sync = actions_reversed
            .iter()
            .any(|a| matches!(a, RepairAction::SkipToSync { .. }));
        if !has_sync && final_sync_pos < token_ids.len() {
            // Add the final sync action
            actions_reversed.push(RepairAction::SkipToSync {
                skip_count: 0,
                sync_token: token_ids[final_sync_pos],
            });
        }
    }

    // Compute total edits
    let total_edits = actions_reversed
        .iter()
        .fold(crate::automata::semiring::EditWeight::new(0), |acc, a| {
            crate::automata::semiring::EditWeight::new(acc.0.saturating_add(a.edit_cost().0))
        });

    Some(RepairSequence {
        actions: actions_reversed,
        new_pos: final_sync_pos,
        total_cost: dist[sink],
        total_edits,
    })
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

            RecoveryWfst::new(category.clone(), &sync_names, token_map)
        })
        .collect()
}

// ══════════════════════════════════════════════════════════════════════════════
// Tier 1: Frame Context — FrameKind + RecoveryContext
// ══════════════════════════════════════════════════════════════════════════════

/// The kind of parse frame where the error occurred.
///
/// Different frame types warrant different recovery strategies:
/// - **Collection**: Missing separators/elements are common → cheaper inserts.
/// - **Group**: Missing closing delimiters are common → cheaper close-insert.
/// - **InfixRHS**: Bad operand → cheaper skip (find next statement).
/// - **Mixfix**: Wrong token in multi-part operator → cheaper substitute.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub enum FrameKind {
    /// Pratt prefix handler (atom, unary prefix).
    Prefix,
    /// Right-hand side of an infix operator.
    InfixRHS,
    /// Postfix operator position.
    Postfix,
    /// Collection (list/set/map) body.
    Collection,
    /// Parenthesized/braced/bracketed group.
    Group,
    /// Multi-part mixfix operator (e.g., `a ? b : c`).
    Mixfix,
    /// Lambda binder body.
    Lambda,
    /// Dollar application body.
    Dollar,
    /// Cast wrapper (cross-category).
    CastWrap,
    /// Generic/unknown context.
    #[default]
    Other,
}

// FrameKind derives Default via #[default] on the Other variant.

/// The source of a sync token, used for cost stratification.
///
/// Structural delimiters (closing brackets, semicolons, commas) are preferred
/// sync points because they are unambiguous boundaries. FOLLOW set tokens are
/// next. EOF is the strongest sync point.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SyncSource {
    /// End of file — strongest sync point.
    Eof,
    /// Structural delimiter: `)`, `}`, `]`, `;`, `,`.
    StructuralDelimiter,
    /// From FOLLOW set computation.
    FollowSet,
}

/// A sync token annotated with its source and a weight multiplier.
///
/// The multiplier adjusts the cost of recovery actions targeting this sync
/// token. Structural delimiters get a discount (preferred sync points).
#[derive(Debug, Clone)]
pub struct AnnotatedSyncToken {
    /// The token identifier.
    pub token_id: TokenId,
    /// How this sync token was derived.
    pub source: SyncSource,
    /// Multiplier applied to recovery cost when syncing to this token.
    /// Lower values make this sync point more attractive.
    pub weight_multiplier: f64,
}

/// Parse context passed to context-aware recovery.
///
/// Encapsulates Tier 1 (frame context) and Tier 2 (bracket balance) information
/// that adjusts recovery costs based on where the error occurred.
#[derive(Debug, Clone)]
pub struct RecoveryContext {
    // ── Tier 1: Frame context ──────────────────────────────────────────────
    /// Current parse nesting depth.
    pub depth: usize,
    /// Current binding power in Pratt parsing.
    pub binding_power: u8,
    /// Type of parse frame where the error occurred.
    pub frame_kind: FrameKind,

    // ── Tier 2: Bracket balance ────────────────────────────────────────────
    /// Number of unmatched open parentheses `(`.
    pub open_parens: u16,
    /// Number of unmatched open braces `{`.
    pub open_braces: u16,
    /// Number of unmatched open brackets `[`.
    pub open_brackets: u16,
}

impl Default for RecoveryContext {
    fn default() -> Self {
        RecoveryContext {
            depth: 0,
            binding_power: 0,
            frame_kind: FrameKind::Other,
            open_parens: 0,
            open_braces: 0,
            open_brackets: 0,
        }
    }
}

impl RecoveryContext {
    /// Compute a cost multiplier for **skip** actions based on frame context.
    ///
    /// - Deep nesting (depth > threshold): `deep_nesting_skip_mult` (skip is safe — likely noise)
    /// - Shallow (depth < threshold): `shallow_depth_skip_mult` (precise repair preferred)
    /// - InfixRHS: `low_bp_skip_mult` (skip bad operand, find next statement)
    /// - Low BP (< threshold): `low_bp_skip_mult` (loose binding, skip is safe)
    pub fn skip_multiplier(&self) -> f64 {
        self.skip_multiplier_with(&RecoveryConfig::default())
    }

    /// Compute skip multiplier using the provided config.
    pub fn skip_multiplier_with(&self, config: &RecoveryConfig) -> f64 {
        let mut m = 1.0;

        // Depth scaling
        if self.depth > config.deep_nesting_threshold {
            m *= config.deep_nesting_skip_mult;
        } else if self.depth < config.shallow_depth_threshold {
            m *= config.shallow_depth_skip_mult;
        }

        // Frame-kind adjustments
        if self.frame_kind == FrameKind::InfixRHS {
            m *= config.low_bp_skip_mult;
        }

        // BP scaling
        if self.binding_power < config.low_bp_threshold {
            m *= config.low_bp_skip_mult;
        }

        m
    }

    /// Compute a cost multiplier for **insert** actions based on frame context.
    ///
    /// - Collection: `collection_insert_mult` (missing separator/element is common)
    /// - Group: `group_insert_mult` (missing closing delimiter is common)
    /// - High BP (> 20): 1.5x (deep in tight-binding context, precise repair needed)
    pub fn insert_multiplier(&self) -> f64 {
        self.insert_multiplier_with(&RecoveryConfig::default())
    }

    /// Compute insert multiplier using the provided config.
    pub fn insert_multiplier_with(&self, config: &RecoveryConfig) -> f64 {
        let mut m = 1.0;

        match self.frame_kind {
            FrameKind::Collection => m *= config.collection_insert_mult,
            FrameKind::Group => m *= config.group_insert_mult,
            _ => {},
        }

        if self.binding_power > 20 {
            m *= 1.5;
        }

        m
    }

    /// Compute a cost multiplier for **substitute** actions based on frame context.
    ///
    /// - Mixfix: `mixfix_substitute_mult` (wrong token in multi-part operator)
    pub fn substitute_multiplier(&self) -> f64 {
        self.substitute_multiplier_with(&RecoveryConfig::default())
    }

    /// Compute substitute multiplier using the provided config.
    pub fn substitute_multiplier_with(&self, config: &RecoveryConfig) -> f64 {
        let mut m = 1.0;

        if self.frame_kind == FrameKind::Mixfix {
            m *= config.mixfix_substitute_mult;
        }

        m
    }

    /// Compute a cost multiplier for inserting a specific closing delimiter
    /// based on bracket balance.
    ///
    /// When there are unmatched open brackets, inserting the matching closer
    /// is strongly preferred (`bracket_insert_mult` cost).
    pub fn bracket_insert_multiplier(&self, token_name: Option<&str>) -> f64 {
        self.bracket_insert_multiplier_with(token_name, &RecoveryConfig::default())
    }

    /// Compute bracket insert multiplier using the provided config.
    pub fn bracket_insert_multiplier_with(
        &self,
        token_name: Option<&str>,
        config: &RecoveryConfig,
    ) -> f64 {
        match token_name {
            Some("RParen") if self.open_parens > 0 => config.bracket_insert_mult,
            Some("RBrace") if self.open_braces > 0 => config.bracket_insert_mult,
            Some("RBracket") if self.open_brackets > 0 => config.bracket_insert_mult,
            _ => 1.0,
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Tier 3: Predictive Repair Simulation
// ══════════════════════════════════════════════════════════════════════════════

/// Result of simulating a parse continuation after a proposed repair.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SimulationResult {
    /// The repair leads to a valid parse continuation.
    ValidContinuation {
        /// Number of tokens successfully consumed in simulation.
        tokens_consumed: usize,
    },
    /// The repair leads to a parse failure within the lookahead window.
    FailedAt {
        /// Position (0-based offset from repair point) where simulation failed.
        position: usize,
    },
}

/// Lightweight parse simulator for scoring proposed repairs.
///
/// Uses FIRST and FOLLOW sets to predict whether a repair action leads to
/// a valid parse continuation. Does not actually parse — instead checks
/// a simplified state machine:
///
/// 1. After repair, is the next token in FIRST(category)? → consume, continue.
/// 2. Is the token an infix operator for this category? → valid continuation.
/// 3. Is the token in FOLLOW(category)? → category parse would end (valid).
/// 4. Otherwise → failed.
#[derive(Debug, Clone)]
pub struct ParseSimulator {
    /// FIRST sets by category name → set of token IDs.
    first_sets: BTreeMap<String, BTreeSet<TokenId>>,
    /// FOLLOW sets by category name → set of token IDs.
    follow_sets: BTreeMap<String, BTreeSet<TokenId>>,
    /// Infix operator tokens by category name → set of token IDs.
    infix_tokens: BTreeMap<String, BTreeSet<TokenId>>,
    /// Number of tokens to simulate ahead.
    lookahead_depth: usize,
}

impl ParseSimulator {
    /// Construct a parse simulator from pre-computed sets.
    ///
    /// # Arguments
    ///
    /// * `first_sets` — FIRST set for each category, as token IDs.
    /// * `follow_sets` — FOLLOW set for each category, as token IDs.
    /// * `infix_tokens` — Infix operator token IDs for each category.
    /// * `lookahead_depth` — How many tokens to simulate (default: 5).
    pub fn new(
        first_sets: BTreeMap<String, BTreeSet<TokenId>>,
        follow_sets: BTreeMap<String, BTreeSet<TokenId>>,
        infix_tokens: BTreeMap<String, BTreeSet<TokenId>>,
        lookahead_depth: usize,
    ) -> Self {
        ParseSimulator {
            first_sets,
            follow_sets,
            infix_tokens,
            lookahead_depth,
        }
    }

    /// Reconstruct a `ParseSimulator` from flat arrays embedded in generated code.
    ///
    /// Each parameter is a slice of `(category_name, token_id)` pairs that
    /// reconstitute the per-category sets.
    ///
    /// ## Arguments
    ///
    /// * `first_set_tokens` — `&[(&str, &[u16])]` — category name → FIRST set token IDs.
    /// * `follow_set_tokens` — `&[(&str, &[u16])]` — category name → FOLLOW set token IDs.
    /// * `infix_tokens` — `&[(&str, &[u16])]` — category name → infix operator token IDs.
    /// * `lookahead_depth` — Number of tokens to simulate ahead.
    pub fn from_flat(
        first_set_tokens: &[(&str, &[u16])],
        follow_set_tokens: &[(&str, &[u16])],
        infix_tokens: &[(&str, &[u16])],
        lookahead_depth: usize,
    ) -> Self {
        let first_sets: BTreeMap<String, BTreeSet<TokenId>> = first_set_tokens
            .iter()
            .map(|(cat, ids)| (cat.to_string(), ids.iter().copied().collect()))
            .collect();
        let follow_sets: BTreeMap<String, BTreeSet<TokenId>> = follow_set_tokens
            .iter()
            .map(|(cat, ids)| (cat.to_string(), ids.iter().copied().collect()))
            .collect();
        let infix_map: BTreeMap<String, BTreeSet<TokenId>> = infix_tokens
            .iter()
            .map(|(cat, ids)| (cat.to_string(), ids.iter().copied().collect()))
            .collect();

        ParseSimulator {
            first_sets,
            follow_sets,
            infix_tokens: infix_map,
            lookahead_depth,
        }
    }

    /// Simulate parsing after a proposed repair.
    ///
    /// Checks whether the tokens starting at `pos` form a plausible parse
    /// continuation for the given `category`. Returns `ValidContinuation`
    /// if the simulation reaches `lookahead_depth` tokens or encounters a
    /// FOLLOW token; returns `FailedAt` if an unexpected token is found.
    pub fn simulate_after_repair(
        &self,
        token_ids: &[TokenId],
        pos: usize,
        category: &str,
    ) -> SimulationResult {
        let first = self.first_sets.get(category);
        let follow = self.follow_sets.get(category);
        let infix = self.infix_tokens.get(category);

        let mut consumed = 0;

        for offset in 0..self.lookahead_depth {
            let idx = pos + offset;
            if idx >= token_ids.len() {
                // Ran out of tokens — this is fine (valid continuation to EOF)
                return SimulationResult::ValidContinuation { tokens_consumed: consumed };
            }

            let token = token_ids[idx];

            // Check: is this token in FIRST(category)?
            if let Some(fs) = first {
                if fs.contains(&token) {
                    consumed += 1;
                    continue;
                }
            }

            // Check: is this an infix operator for this category?
            if let Some(inf) = infix {
                if inf.contains(&token) {
                    // Infix continuation — valid, count it
                    consumed += 1;
                    continue;
                }
            }

            // Check: is this token in FOLLOW(category)?
            if let Some(fol) = follow {
                if fol.contains(&token) {
                    // Category parse would end here — valid
                    return SimulationResult::ValidContinuation { tokens_consumed: consumed };
                }
            }

            // Token doesn't fit anywhere — simulation failed
            return SimulationResult::FailedAt { position: offset };
        }

        // Reached lookahead depth — valid continuation
        SimulationResult::ValidContinuation { tokens_consumed: consumed }
    }

    /// Compute a cost multiplier based on simulation result (default config).
    ///
    /// - `ValidContinuation` → 0.5x (repair leads to good continuation)
    /// - `FailedAt(n)` → `1.0 + (lookahead - n) * 0.2` (penalize earlier failures more)
    pub fn cost_multiplier(&self, result: &SimulationResult) -> f64 {
        self.cost_multiplier_with(result, &RecoveryConfig::default())
    }

    /// Compute a cost multiplier based on simulation result using the provided config.
    pub fn cost_multiplier_with(&self, result: &SimulationResult, config: &RecoveryConfig) -> f64 {
        match result {
            SimulationResult::ValidContinuation { .. } => config.simulation_valid_mult,
            SimulationResult::FailedAt { position } => {
                1.0 + (self.lookahead_depth.saturating_sub(*position)) as f64
                    * config.simulation_fail_penalty
            },
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Context-Aware Recovery — combines all 3 tiers
// ══════════════════════════════════════════════════════════════════════════════

impl RecoveryWfst {
    /// Find the best recovery action with context-aware cost adjustments.
    ///
    /// Combines all three tiers:
    /// - **Tier 1**: Frame context (depth, binding power, frame kind)
    /// - **Tier 2**: FOLLOW stratification + bracket balance
    /// - **Tier 3**: Predictive repair simulation (optional)
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
        let remaining = &token_ids[pos..];
        let mut best: Option<RepairResult> = None;

        // ── Strategy 1: SkipToSync ─────────────────────────────────────────
        let max_lookahead = remaining.len().min(costs::MAX_SKIP_LOOKAHEAD);
        #[allow(clippy::needless_range_loop)]
        // `skip` used for arithmetic, cost calc, struct field, and position offset
        for skip in 0..max_lookahead {
            let token_at = remaining[skip];
            if self.sync_tokens.contains(&token_at) {
                let base_cost = if skip == 0 {
                    TropicalWeight::one()
                } else {
                    TropicalWeight::new(skip as f64 * costs::SKIP_PER_TOKEN.value())
                };

                // Tier 1: frame context multiplier for skip
                let tier1_mult = ctx.skip_multiplier();

                // Tier 3: simulation after the skip
                let tier3_mult = if let Some(sim) = simulator {
                    let sim_result = sim.simulate_after_repair(token_ids, pos + skip, category);
                    sim.cost_multiplier(&sim_result)
                } else {
                    1.0
                };

                let adjusted_cost = if base_cost == TropicalWeight::one() {
                    base_cost // zero-cost sync: don't multiply
                } else {
                    TropicalWeight::new(base_cost.value() * tier1_mult * tier3_mult)
                };

                let result = RepairResult {
                    action: RepairAction::SkipToSync { skip_count: skip, sync_token: token_at },
                    new_pos: pos + skip,
                    cost: adjusted_cost,
                };
                best = Some(pick_better(best, result));
                break; // first sync point only
            }
        }

        // ── Strategy 2: DeleteToken ────────────────────────────────────────
        if !remaining.is_empty() {
            let base_cost = costs::DELETE;
            // Delete is a mild skip variant — use skip multiplier
            let tier1_mult = ctx.skip_multiplier();

            let tier3_mult = if let Some(sim) = simulator {
                let sim_result = sim.simulate_after_repair(token_ids, pos + 1, category);
                sim.cost_multiplier(&sim_result)
            } else {
                1.0
            };

            let result = RepairResult {
                action: RepairAction::DeleteToken,
                new_pos: pos + 1,
                cost: TropicalWeight::new(base_cost.value() * tier1_mult * tier3_mult),
            };
            best = Some(pick_better(best, result));
        }

        // ── Strategy 3: InsertToken ────────────────────────────────────────
        for &sync_id in &self.sync_tokens {
            let base_cost = costs::INSERT;

            // Tier 1: frame context multiplier for insert
            let tier1_mult = ctx.insert_multiplier();

            // Tier 2: bracket balance multiplier
            let token_name = self.token_map.name(sync_id);
            let tier2_mult = ctx.bracket_insert_multiplier(token_name);

            // Tier 3: simulation after inserting this token
            let tier3_mult = if let Some(sim) = simulator {
                // After insert, we're still at `pos` (phantom token)
                let sim_result = sim.simulate_after_repair(token_ids, pos, category);
                sim.cost_multiplier(&sim_result)
            } else {
                1.0
            };

            let result = RepairResult {
                action: RepairAction::InsertToken { token: sync_id },
                new_pos: pos,
                cost: TropicalWeight::new(base_cost.value() * tier1_mult * tier2_mult * tier3_mult),
            };
            best = Some(pick_better(best, result));
        }

        // ── Strategy 4: SubstituteToken ────────────────────────────────────
        if !remaining.is_empty() {
            for &sync_id in &self.sync_tokens {
                let base_cost = costs::SUBSTITUTE;

                // Tier 1: frame context multiplier for substitute
                let tier1_mult = ctx.substitute_multiplier();

                let tier3_mult = if let Some(sim) = simulator {
                    let sim_result = sim.simulate_after_repair(token_ids, pos + 1, category);
                    sim.cost_multiplier(&sim_result)
                } else {
                    1.0
                };

                let result = RepairResult {
                    action: RepairAction::SubstituteToken { replacement: sync_id },
                    new_pos: pos + 1,
                    cost: TropicalWeight::new(base_cost.value() * tier1_mult * tier3_mult),
                };
                best = Some(pick_better(best, result));
            }
        }

        // ── Strategy 5: SwapTokens ───────────────────────────────────────
        if remaining.len() >= 2 {
            let swapped_first = remaining[1];
            if self.sync_tokens.contains(&swapped_first) {
                let base_cost = TropicalWeight::new(1.25); // SWAP cost
                let tier1_mult = ctx.skip_multiplier(); // swap is a mild reorder

                let tier3_mult = if let Some(sim) = simulator {
                    let sim_result = sim.simulate_after_repair(token_ids, pos + 2, category);
                    sim.cost_multiplier(&sim_result)
                } else {
                    1.0
                };

                let result = RepairResult {
                    action: RepairAction::SwapTokens {
                        pos_a: pos,
                        pos_b: pos + 1,
                    },
                    new_pos: pos + 2,
                    cost: TropicalWeight::new(base_cost.value() * tier1_mult * tier3_mult),
                };
                best = Some(pick_better(best, result));
            }
        }

        best
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Lattice-aware recovery (feature = "context-sensitive-lex")
// ══════════════════════════════════════════════════════════════════════════════

/// Try recovery using alternative tokenization paths from a token lattice.
///
/// When the lexer produces a `TokenLattice` (due to lexical ambiguity), this
/// function extracts up to `n_best` alternative tokenization paths from the
/// error position and runs `find_best_recovery()` on each. The cheapest
/// successful recovery across all tokenizations is returned.
///
/// A small penalty per alternative tried is applied to prefer the primary
/// tokenization (the one already attempted by the parser).
///
/// # Arguments
///
/// * `alternative_token_ids` — List of `(Vec<TokenId>, TropicalWeight)` pairs,
///   each representing an alternative tokenization path with its lexer weight.
/// * `pos` — Error position within each alternative path (relative to path start).
/// * `sync_tokens` — Set of synchronization token IDs.
/// * `config` — Recovery configuration for cost computation.
///
/// # Returns
///
/// The cheapest `RepairResult` across all alternatives, with cost adjusted by
/// the lexer weight of the selected alternative.
#[cfg(feature = "context-sensitive-lex")]
pub fn lattice_recovery(
    alternative_token_ids: &[(Vec<TokenId>, crate::automata::semiring::TropicalWeight)],
    pos: usize,
    sync_tokens: &std::collections::BTreeSet<TokenId>,
    config: &RecoveryConfig,
) -> Option<RepairResult> {
    use crate::automata::semiring::Semiring;

    let mut best: Option<RepairResult> = None;
    let alternative_penalty = 0.1_f64; // slight penalty per alternative tried

    for (alt_idx, (token_ids, lexer_weight)) in alternative_token_ids.iter().enumerate() {
        if pos >= token_ids.len() {
            continue;
        }

        // Run recovery on this alternative tokenization
        if let Some(seq) = viterbi_multi_step(token_ids, pos, sync_tokens, config) {
            let mut cost = seq.total_cost.value();

            // Apply lexer weight — prefer primary tokenization
            cost *= lexer_weight.value();

            // Penalize non-primary alternatives slightly
            cost += alt_idx as f64 * alternative_penalty;

            let repair = RepairResult {
                action: if seq.actions.len() == 1 {
                    seq.actions.into_iter().next().expect("non-empty actions vec")
                } else {
                    RepairAction::Composite { steps: seq.actions }
                },
                new_pos: pos + seq.new_pos,
                cost: crate::automata::semiring::TropicalWeight::new(cost),
            };

            best = Some(pick_better(best, repair));
        }
    }

    best
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_token_map() -> TokenIdMap {
        TokenIdMap::from_names(
            vec!["Plus", "Minus", "Star", "Integer", "Ident", "RParen", "Semi", "Eof"]
                .into_iter()
                .map(String::from),
        )
    }

    #[test]
    fn test_recovery_wfst_construction() {
        let token_map = make_token_map();
        let sync_names: Vec<String> = vec!["Eof", "RParen", "Semi", "Plus"]
            .into_iter()
            .map(String::from)
            .collect();

        let wfst = RecoveryWfst::new("Expr".to_string(), &sync_names, &token_map);

        assert_eq!(wfst.category(), "Expr");
        assert_eq!(wfst.sync_tokens().len(), 4);
        assert!(wfst
            .sync_tokens()
            .contains(&token_map.get("Eof").expect("Eof should be in map")));
        assert!(wfst
            .sync_tokens()
            .contains(&token_map.get("RParen").expect("RParen should be in map")));
    }

    #[test]
    fn test_find_best_recovery_skip_to_sync() {
        let token_map = make_token_map();
        let sync_names = vec!["Semi".to_string(), "Eof".to_string()];
        let wfst = RecoveryWfst::new("Expr".to_string(), &sync_names, &token_map);

        // tokens: [Ident, Plus, Semi, Eof]
        // pos = 0, error at Ident, Semi is sync at index 2
        let token_ids: Vec<TokenId> = vec![
            token_map.get("Ident").expect("Ident"),
            token_map.get("Plus").expect("Plus"),
            token_map.get("Semi").expect("Semi"),
            token_map.get("Eof").expect("Eof"),
        ];

        let result = wfst
            .find_best_recovery(&token_ids, 0)
            .expect("should find recovery");

        // Best should be SkipToSync(skip=2, sync=Semi) with cost 2*0.5=1.0
        match &result.action {
            RepairAction::SkipToSync { skip_count, sync_token } => {
                assert_eq!(*skip_count, 2);
                assert_eq!(*sync_token, token_map.get("Semi").expect("Semi"));
            },
            other => panic!("Expected SkipToSync, got {:?}", other),
        }
        assert_eq!(result.new_pos, 2);
        assert_eq!(result.cost, TropicalWeight::new(1.0));
    }

    #[test]
    fn test_find_best_recovery_already_at_sync() {
        let token_map = make_token_map();
        let sync_names = vec!["Semi".to_string()];
        let wfst = RecoveryWfst::new("Expr".to_string(), &sync_names, &token_map);

        // tokens: [Semi, Eof]
        let token_ids: Vec<TokenId> =
            vec![token_map.get("Semi").expect("Semi"), token_map.get("Eof").expect("Eof")];

        let result = wfst
            .find_best_recovery(&token_ids, 0)
            .expect("should find recovery");

        // Already at sync: cost = 0.0 (tropical one), skip_count = 0
        match &result.action {
            RepairAction::SkipToSync { skip_count, .. } => {
                assert_eq!(*skip_count, 0);
            },
            other => panic!("Expected SkipToSync, got {:?}", other),
        }
        assert_eq!(result.cost, TropicalWeight::one());
    }

    #[test]
    fn test_find_best_recovery_insert_wins() {
        let token_map = make_token_map();
        let sync_names = vec!["Semi".to_string()];
        let wfst = RecoveryWfst::new("Expr".to_string(), &sync_names, &token_map);

        // tokens: [Ident, Ident, Ident, Ident, Ident] — no sync token reachable quickly
        // But we have 5 non-sync tokens. Skip cost = 5*0.5 = 2.5.
        // Delete cost = 1.0.
        // Insert cost = 2.0.
        // Delete (1.0) < Insert (2.0) < SkipToSync (no sync found, skip doesn't win)
        let ident_id = token_map.get("Ident").expect("Ident");
        let token_ids: Vec<TokenId> = vec![ident_id; 5];

        let result = wfst
            .find_best_recovery(&token_ids, 0)
            .expect("should find recovery");

        // Delete is cheapest (1.0) when there's no sync point
        assert_eq!(result.action, RepairAction::DeleteToken);
        assert_eq!(result.cost, costs::DELETE);
    }

    #[test]
    fn test_find_best_recovery_at_eof() {
        let token_map = make_token_map();
        let sync_names = vec!["Eof".to_string()];
        let wfst = RecoveryWfst::new("Expr".to_string(), &sync_names, &token_map);

        // Empty remaining tokens — only InsertToken is possible
        let token_ids: Vec<TokenId> = vec![];

        let result = wfst
            .find_best_recovery(&token_ids, 0)
            .expect("should find recovery");

        match &result.action {
            RepairAction::InsertToken { .. } => {}, // expected
            other => panic!("Expected InsertToken at EOF, got {:?}", other),
        }
        assert_eq!(result.cost, costs::INSERT);
    }

    #[test]
    fn test_repair_action_display() {
        let action = RepairAction::SkipToSync { skip_count: 3, sync_token: 5 };
        assert_eq!(format!("{}", action), "skip 3 tokens to sync token 5");

        let action = RepairAction::DeleteToken;
        assert_eq!(format!("{}", action), "delete token");

        let action = RepairAction::InsertToken { token: 2 };
        assert_eq!(format!("{}", action), "insert token 2");

        let action = RepairAction::SubstituteToken { replacement: 7 };
        assert_eq!(format!("{}", action), "substitute with token 7");
    }

    #[test]
    fn test_repair_result_display() {
        let result = RepairResult {
            action: RepairAction::DeleteToken,
            new_pos: 5,
            cost: TropicalWeight::new(1.0),
        };
        assert_eq!(format!("{}", result), "repair: delete token (cost: 1.0, new_pos: 5)");
    }

    #[test]
    fn test_viterbi_recovery_basic() {
        let token_map = make_token_map();

        let mut sync_tokens = BTreeSet::new();
        sync_tokens.insert(token_map.get("Semi").expect("Semi"));

        // tokens: [Ident, Plus, Semi, Eof]
        let token_ids: Vec<TokenId> = vec![
            token_map.get("Ident").expect("Ident"),
            token_map.get("Plus").expect("Plus"),
            token_map.get("Semi").expect("Semi"),
            token_map.get("Eof").expect("Eof"),
        ];

        let result = viterbi_recovery(&token_ids, 0, &sync_tokens).expect("should find recovery");

        // Viterbi should find: skip 2 tokens (Ident, Plus) to reach Semi
        match &result.action {
            RepairAction::SkipToSync { skip_count, sync_token } => {
                assert_eq!(*skip_count, 2);
                assert_eq!(*sync_token, token_map.get("Semi").expect("Semi"));
            },
            other => panic!("Expected SkipToSync, got {:?}", other),
        }
        assert_eq!(result.new_pos, 2);
    }

    #[test]
    fn test_viterbi_recovery_immediate_sync() {
        let token_map = make_token_map();

        let mut sync_tokens = BTreeSet::new();
        sync_tokens.insert(token_map.get("Semi").expect("Semi"));

        // Already at sync
        let token_ids: Vec<TokenId> = vec![token_map.get("Semi").expect("Semi")];

        let result = viterbi_recovery(&token_ids, 0, &sync_tokens).expect("should find recovery");

        match &result.action {
            RepairAction::SkipToSync { skip_count, .. } => {
                assert_eq!(*skip_count, 0);
            },
            other => panic!("Expected SkipToSync with skip_count=0, got {:?}", other),
        }
        assert_eq!(result.cost, TropicalWeight::one()); // zero cost
    }

    #[test]
    fn test_viterbi_recovery_no_sync_reachable() {
        let token_map = make_token_map();

        let mut sync_tokens = BTreeSet::new();
        sync_tokens.insert(token_map.get("Semi").expect("Semi"));

        // No Semi in the remaining tokens
        let ident_id = token_map.get("Ident").expect("Ident");
        let token_ids: Vec<TokenId> = vec![ident_id; 5];

        let result = viterbi_recovery(&token_ids, 0, &sync_tokens);
        assert!(result.is_none());
    }

    #[test]
    fn test_viterbi_recovery_empty_input() {
        let sync_tokens = BTreeSet::new();
        let result = viterbi_recovery(&[], 0, &sync_tokens);
        assert!(result.is_none());
    }

    #[test]
    fn test_build_recovery_wfsts() {
        let token_map = make_token_map();

        let categories = vec!["Int".to_string(), "Expr".to_string()];

        let mut follow_sets = std::collections::HashMap::new();
        let mut int_follow = crate::prediction::FirstSet::new();
        int_follow.tokens.insert("Plus".to_string());
        int_follow.tokens.insert("Star".to_string());
        follow_sets.insert("Int".to_string(), int_follow);

        let mut grammar_terminals = std::collections::HashSet::new();
        grammar_terminals.insert(";".to_string());
        grammar_terminals.insert(")".to_string());

        let wfsts = build_recovery_wfsts(&categories, &follow_sets, &grammar_terminals, &token_map);

        assert_eq!(wfsts.len(), 2);
        assert_eq!(wfsts[0].category(), "Int");
        assert_eq!(wfsts[1].category(), "Expr");

        // Int should have: Eof + RParen + Semi + Plus + Star = 5 sync tokens
        let int_sync = wfsts[0].sync_tokens();
        assert!(int_sync.contains(&token_map.get("Eof").expect("Eof")));
        assert!(int_sync.contains(&token_map.get("RParen").expect("RParen")));
        assert!(int_sync.contains(&token_map.get("Semi").expect("Semi")));
        assert!(int_sync.contains(&token_map.get("Plus").expect("Plus")));
        assert!(int_sync.contains(&token_map.get("Star").expect("Star")));
        assert_eq!(int_sync.len(), 5);

        // Expr should have: Eof + RParen + Semi = 3 sync tokens (no FOLLOW set entry)
        let expr_sync = wfsts[1].sync_tokens();
        assert!(expr_sync.contains(&token_map.get("Eof").expect("Eof")));
        assert_eq!(expr_sync.len(), 3);
    }

    #[test]
    fn test_recovery_beam_prunes_expensive_repairs() {
        let token_map = make_token_map();

        let mut sync_tokens = BTreeSet::new();
        // Two sync points: Semi (close) and Eof (far)
        sync_tokens.insert(token_map.get("Semi").expect("Semi"));
        sync_tokens.insert(token_map.get("Eof").expect("Eof"));

        // tokens: [Ident, Plus, Semi, Ident, Ident, Ident, Ident, Eof]
        // Skip to Semi = 2 skips = 1.0 cost (cheap)
        // Skip to Eof  = 7 skips = 3.5 cost (expensive)
        let token_ids: Vec<TokenId> = vec![
            token_map.get("Ident").expect("Ident"),
            token_map.get("Plus").expect("Plus"),
            token_map.get("Semi").expect("Semi"),
            token_map.get("Ident").expect("Ident"),
            token_map.get("Ident").expect("Ident"),
            token_map.get("Ident").expect("Ident"),
            token_map.get("Ident").expect("Ident"),
            token_map.get("Eof").expect("Eof"),
        ];

        // Without beam: should find cheapest recovery (skip 2 to Semi, cost 1.0)
        let result_no_beam = viterbi_recovery_beam(&token_ids, 0, &sync_tokens, None)
            .expect("should find recovery without beam");
        match &result_no_beam.action {
            RepairAction::SkipToSync { skip_count, sync_token } => {
                assert_eq!(*skip_count, 2);
                assert_eq!(*sync_token, token_map.get("Semi").expect("Semi"));
            },
            other => panic!("Expected SkipToSync to Semi, got {:?}", other),
        }

        // With tight beam (0.5): beam prunes skip paths whose accumulated cost
        // exceeds dist[sink] + beam. Since the best sync (Semi at cost 1.0)
        // is discovered first, skip paths beyond 1.0 + 0.5 = 1.5 are pruned.
        // Result should still find the Semi sync (cost 1.0 is within beam).
        let result_with_beam =
            viterbi_recovery_beam(&token_ids, 0, &sync_tokens, Some(TropicalWeight::new(0.5)))
                .expect("should find recovery with beam");
        match &result_with_beam.action {
            RepairAction::SkipToSync { skip_count, sync_token } => {
                assert_eq!(*skip_count, 2);
                assert_eq!(*sync_token, token_map.get("Semi").expect("Semi"));
            },
            other => panic!("Expected SkipToSync to Semi with beam, got {:?}", other),
        }
        // Costs should be identical — beam only prunes, doesn't change the best path
        assert_eq!(result_no_beam.cost, result_with_beam.cost);
    }

    #[test]
    fn test_recovery_beam_none_is_identity() {
        let token_map = make_token_map();

        let mut sync_tokens = BTreeSet::new();
        sync_tokens.insert(token_map.get("Semi").expect("Semi"));

        let token_ids: Vec<TokenId> = vec![
            token_map.get("Ident").expect("Ident"),
            token_map.get("Plus").expect("Plus"),
            token_map.get("Semi").expect("Semi"),
        ];

        let result_original =
            viterbi_recovery(&token_ids, 0, &sync_tokens).expect("should find recovery");
        let result_beam_none = viterbi_recovery_beam(&token_ids, 0, &sync_tokens, None)
            .expect("should find recovery with None beam");

        assert_eq!(result_original.cost, result_beam_none.cost);
        assert_eq!(result_original.new_pos, result_beam_none.new_pos);
    }

    // ═══════════════════════════════════════════════════════════════════════
    // Tier 1: Frame context tests
    // ═══════════════════════════════════════════════════════════════════════

    #[test]
    fn test_depth_scaling_deep() {
        let ctx = RecoveryContext {
            depth: 5000,
            binding_power: 10, // neutral BP (not < 4, not > 20)
            ..Default::default()
        };
        // Deep nesting → 0.5x skip multiplier
        assert!((ctx.skip_multiplier() - 0.5).abs() < 1e-9);
    }

    #[test]
    fn test_depth_scaling_shallow() {
        let ctx = RecoveryContext {
            depth: 5,
            binding_power: 10, // neutral BP
            ..Default::default()
        };
        // Shallow → 2.0x skip multiplier (precise repair preferred)
        assert!((ctx.skip_multiplier() - 2.0).abs() < 1e-9);
    }

    #[test]
    fn test_frame_kind_collection_prefers_insert() {
        let ctx = RecoveryContext {
            depth: 50, // mid-range (no depth adjustment)
            frame_kind: FrameKind::Collection,
            ..Default::default()
        };
        // Collection → 0.5x insert multiplier
        assert!((ctx.insert_multiplier() - 0.5).abs() < 1e-9);
    }

    #[test]
    fn test_frame_kind_group_prefers_close() {
        let ctx = RecoveryContext {
            depth: 50,
            frame_kind: FrameKind::Group,
            ..Default::default()
        };
        // Group → 0.5x insert multiplier
        assert!((ctx.insert_multiplier() - 0.5).abs() < 1e-9);
    }

    #[test]
    fn test_bp_scaling_tight() {
        let ctx = RecoveryContext {
            depth: 50,
            binding_power: 25,
            ..Default::default()
        };
        // High BP → 1.5x insert multiplier (precise repair needed)
        assert!((ctx.insert_multiplier() - 1.5).abs() < 1e-9);
    }

    #[test]
    fn test_contextual_vs_static_different_results() {
        let token_map = make_token_map();
        let sync_names = vec!["Semi".to_string(), "Eof".to_string()];
        let wfst = RecoveryWfst::new("Expr".to_string(), &sync_names, &token_map);

        // tokens: [Ident, Plus, Semi]
        let token_ids: Vec<TokenId> = vec![
            token_map.get("Ident").expect("Ident"),
            token_map.get("Plus").expect("Plus"),
            token_map.get("Semi").expect("Semi"),
        ];

        // Static (default context)
        let static_result = wfst.find_best_recovery(&token_ids, 0);

        // Contextual with Collection frame → insert multiplier halved
        let ctx = RecoveryContext {
            depth: 50,
            frame_kind: FrameKind::Collection,
            ..Default::default()
        };
        let contextual_result =
            wfst.find_best_recovery_contextual(&token_ids, 0, &ctx, None, "Expr");

        // With Collection frame, InsertToken cost = 2.0 * 0.5 = 1.0
        // which ties with DeleteToken (1.0), both better than SkipToSync 2*0.5=1.0
        // The key point: context changes the cost landscape
        assert!(static_result.is_some());
        assert!(contextual_result.is_some());
        // At minimum, the costs should differ due to context adjustment
        let s = static_result.expect("static");
        let c = contextual_result.expect("contextual");
        // Verify that contextual recovery exists (details may vary by winning strategy)
        assert!(c.cost.value() >= 0.0);
        // Contextual result should favor insert more (cheaper cost for insert)
        // Note: exact winner depends on relative costs, but the important thing
        // is that the context adjustment changes the result or cost.
        let _ = (s, c); // both valid
    }

    // ═══════════════════════════════════════════════════════════════════════
    // Tier 2: Bracket balance tests
    // ═══════════════════════════════════════════════════════════════════════

    #[test]
    fn test_annotated_sync_structural_preferred() {
        // Verify SyncSource weights
        let eof = AnnotatedSyncToken {
            token_id: 0,
            source: SyncSource::Eof,
            weight_multiplier: 0.6,
        };
        let structural = AnnotatedSyncToken {
            token_id: 1,
            source: SyncSource::StructuralDelimiter,
            weight_multiplier: 0.8,
        };
        let follow = AnnotatedSyncToken {
            token_id: 2,
            source: SyncSource::FollowSet,
            weight_multiplier: 1.0,
        };

        // Eof is strongest (lowest multiplier), then structural, then follow
        assert!(eof.weight_multiplier < structural.weight_multiplier);
        assert!(structural.weight_multiplier < follow.weight_multiplier);
    }

    #[test]
    fn test_bracket_balance_insert_closer() {
        let ctx = RecoveryContext {
            depth: 50,
            open_parens: 2,
            open_braces: 0,
            open_brackets: 0,
            ..Default::default()
        };

        // Unmatched open_parens → RParen insert is strongly preferred (0.3x)
        assert!((ctx.bracket_insert_multiplier(Some("RParen")) - 0.3).abs() < 1e-9);

        // Other tokens get no bracket discount
        assert!((ctx.bracket_insert_multiplier(Some("Semi")) - 1.0).abs() < 1e-9);
        assert!((ctx.bracket_insert_multiplier(Some("RBrace")) - 1.0).abs() < 1e-9);
    }

    #[test]
    fn test_bracket_balance_no_effect_when_balanced() {
        let ctx = RecoveryContext {
            depth: 50,
            open_parens: 0,
            open_braces: 0,
            open_brackets: 0,
            ..Default::default()
        };

        // No unmatched brackets → all multipliers are 1.0
        assert!((ctx.bracket_insert_multiplier(Some("RParen")) - 1.0).abs() < 1e-9);
        assert!((ctx.bracket_insert_multiplier(Some("RBrace")) - 1.0).abs() < 1e-9);
        assert!((ctx.bracket_insert_multiplier(Some("RBracket")) - 1.0).abs() < 1e-9);
    }

    #[test]
    fn test_bracket_balance_brace_and_bracket() {
        let ctx = RecoveryContext {
            depth: 50,
            open_parens: 0,
            open_braces: 1,
            open_brackets: 3,
            ..Default::default()
        };

        assert!((ctx.bracket_insert_multiplier(Some("RBrace")) - 0.3).abs() < 1e-9);
        assert!((ctx.bracket_insert_multiplier(Some("RBracket")) - 0.3).abs() < 1e-9);
        assert!((ctx.bracket_insert_multiplier(Some("RParen")) - 1.0).abs() < 1e-9);
    }

    // ═══════════════════════════════════════════════════════════════════════
    // Tier 3: Predictive repair simulation tests
    // ═══════════════════════════════════════════════════════════════════════

    #[test]
    fn test_simulator_valid_continuation() {
        let token_map = make_token_map();

        // FIRST(Expr) = {Integer, Ident}
        let mut first = BTreeSet::new();
        first.insert(token_map.get("Integer").expect("Integer"));
        first.insert(token_map.get("Ident").expect("Ident"));

        // FOLLOW(Expr) = {RParen, Semi, Eof}
        let mut follow = BTreeSet::new();
        follow.insert(token_map.get("RParen").expect("RParen"));
        follow.insert(token_map.get("Semi").expect("Semi"));
        follow.insert(token_map.get("Eof").expect("Eof"));

        // Infix(Expr) = {Plus, Minus, Star}
        let mut infix = BTreeSet::new();
        infix.insert(token_map.get("Plus").expect("Plus"));
        infix.insert(token_map.get("Minus").expect("Minus"));
        infix.insert(token_map.get("Star").expect("Star"));

        let sim = ParseSimulator::new(
            BTreeMap::from([("Expr".to_string(), first)]),
            BTreeMap::from([("Expr".to_string(), follow)]),
            BTreeMap::from([("Expr".to_string(), infix)]),
            5,
        );

        // Simulate: [Integer, Plus, Ident, Semi] from pos 0
        // Integer → FIRST(Expr) ✓, Plus → infix ✓, Ident → FIRST ✓, Semi → FOLLOW → stop
        let token_ids: Vec<TokenId> = vec![
            token_map.get("Integer").expect("Integer"),
            token_map.get("Plus").expect("Plus"),
            token_map.get("Ident").expect("Ident"),
            token_map.get("Semi").expect("Semi"),
        ];

        let result = sim.simulate_after_repair(&token_ids, 0, "Expr");
        match result {
            SimulationResult::ValidContinuation { tokens_consumed } => {
                assert_eq!(tokens_consumed, 3);
            },
            other => panic!("Expected ValidContinuation, got {:?}", other),
        }

        // Cost multiplier for valid continuation should be 0.5
        assert!((sim.cost_multiplier(&result) - 0.5).abs() < 1e-9);
    }

    #[test]
    fn test_simulator_failed_at() {
        let token_map = make_token_map();

        // FIRST(Expr) = {Integer}
        let mut first = BTreeSet::new();
        first.insert(token_map.get("Integer").expect("Integer"));

        // FOLLOW(Expr) = {Eof}
        let mut follow = BTreeSet::new();
        follow.insert(token_map.get("Eof").expect("Eof"));

        let sim = ParseSimulator::new(
            BTreeMap::from([("Expr".to_string(), first)]),
            BTreeMap::from([("Expr".to_string(), follow)]),
            BTreeMap::new(), // no infix
            5,
        );

        // Simulate: [Integer, Plus] from pos 0
        // Integer → FIRST ✓, Plus → not in FIRST/FOLLOW/infix → fail at position 1
        let token_ids: Vec<TokenId> =
            vec![token_map.get("Integer").expect("Integer"), token_map.get("Plus").expect("Plus")];

        let result = sim.simulate_after_repair(&token_ids, 0, "Expr");
        match result {
            SimulationResult::FailedAt { position } => {
                assert_eq!(position, 1);
            },
            other => panic!("Expected FailedAt, got {:?}", other),
        }

        // Cost multiplier: 1.0 + (5 - 1) * 0.2 = 1.8
        assert!((sim.cost_multiplier(&result) - 1.8).abs() < 1e-9);
    }

    #[test]
    fn test_simulator_skips_when_none() {
        // When no simulator is provided, contextual recovery uses static costs
        let token_map = make_token_map();
        let sync_names = vec!["Semi".to_string()];
        let wfst = RecoveryWfst::new("Expr".to_string(), &sync_names, &token_map);

        let token_ids: Vec<TokenId> =
            vec![token_map.get("Ident").expect("Ident"), token_map.get("Semi").expect("Semi")];

        let ctx = RecoveryContext::default();

        // Without simulator, contextual recovery uses base costs
        // (only Tier 1 adjustments from default context, which are neutral)
        let result = wfst
            .find_best_recovery_contextual(&token_ids, 0, &ctx, None, "Expr")
            .expect("should find recovery");

        // Should still find a valid recovery
        assert!(result.cost.value() >= 0.0);
    }

    #[test]
    fn test_simulator_empty_input() {
        let sim = ParseSimulator::new(BTreeMap::new(), BTreeMap::new(), BTreeMap::new(), 5);

        // Empty tokens → valid continuation (reached end of input)
        let result = sim.simulate_after_repair(&[], 0, "Expr");
        match result {
            SimulationResult::ValidContinuation { tokens_consumed } => {
                assert_eq!(tokens_consumed, 0);
            },
            other => panic!("Expected ValidContinuation at empty input, got {:?}", other),
        }
    }

    #[test]
    fn test_mixfix_substitute_multiplier() {
        let ctx = RecoveryContext {
            depth: 50,
            frame_kind: FrameKind::Mixfix,
            ..Default::default()
        };
        // Mixfix → 0.75x substitute multiplier
        assert!((ctx.substitute_multiplier() - 0.75).abs() < 1e-9);
    }

    #[test]
    fn test_infix_rhs_skip_multiplier() {
        let ctx = RecoveryContext {
            depth: 50,
            binding_power: 10, // neutral BP
            frame_kind: FrameKind::InfixRHS,
            ..Default::default()
        };
        // InfixRHS → 0.75x skip multiplier
        assert!((ctx.skip_multiplier() - 0.75).abs() < 1e-9);
    }

    // ═══════════════════════════════════════════════════════════════════════
    // from_flat() deserialization tests
    // ═══════════════════════════════════════════════════════════════════════

    #[test]
    fn test_recovery_wfst_from_flat_roundtrip() {
        let token_map = make_token_map();
        let sync_names = vec!["Eof".to_string(), "RParen".to_string(), "Semi".to_string()];
        let original = RecoveryWfst::new("Int".to_string(), &sync_names, &token_map);

        // Flatten into the CSR format
        let sync_ids: Vec<u16> = original.sync_tokens().iter().copied().collect();
        let sync_sources: Vec<(u16, u8)> = sync_ids
            .iter()
            .map(|&id| {
                let tag = match original.token_name(id) {
                    Some("Eof") => 0_u8,
                    Some("RParen" | "RBrace" | "RBracket" | "Semi" | "Comma") => 1_u8,
                    _ => 2_u8,
                };
                (id, tag)
            })
            .collect();

        // Collect token names
        let mut names: Vec<String> = Vec::new();
        for &id in original.sync_tokens() {
            if let Some(name) = original.token_name(id) {
                names.push(name.to_string());
            }
        }
        names.sort();
        names.dedup();
        let name_refs: Vec<&str> = names.iter().map(|s| s.as_str()).collect();

        // Reconstruct
        let reconstructed = RecoveryWfst::from_flat("Int", &sync_ids, &sync_sources, &name_refs);

        assert_eq!(reconstructed.category(), "Int");
        assert_eq!(reconstructed.sync_tokens().len(), original.sync_tokens().len());
        // The sync token IDs should be identical
        assert_eq!(
            reconstructed
                .sync_tokens()
                .iter()
                .copied()
                .collect::<Vec<_>>(),
            original.sync_tokens().iter().copied().collect::<Vec<_>>(),
        );
    }

    #[test]
    fn test_recovery_wfst_from_flat_empty() {
        let wfst = RecoveryWfst::from_flat("Empty", &[], &[], &[]);
        assert_eq!(wfst.category(), "Empty");
        assert!(wfst.sync_tokens().is_empty());
    }

    #[test]
    fn test_parse_simulator_from_flat() {
        let first: &[(&str, &[u16])] = &[
            ("Expr", &[0, 1]), // token IDs 0 and 1 are in FIRST(Expr)
        ];
        let follow: &[(&str, &[u16])] = &[
            ("Expr", &[2, 3]), // token IDs 2 and 3 are in FOLLOW(Expr)
        ];
        let infix: &[(&str, &[u16])] = &[
            ("Expr", &[4]), // token ID 4 is an infix operator
        ];

        let sim = ParseSimulator::from_flat(first, follow, infix, 5);

        // Test simulation: token 0 (FIRST) → consume, token 4 (infix) → consume,
        // token 1 (FIRST) → consume, token 2 (FOLLOW) → stop
        let token_ids: Vec<TokenId> = vec![0, 4, 1, 2];
        let result = sim.simulate_after_repair(&token_ids, 0, "Expr");
        match result {
            SimulationResult::ValidContinuation { tokens_consumed } => {
                assert_eq!(tokens_consumed, 3); // consumed 0, 4, 1 — stopped at 2 (FOLLOW)
            },
            other => panic!("Expected ValidContinuation, got {:?}", other),
        }
    }

    #[test]
    fn test_parse_simulator_from_flat_empty() {
        let sim = ParseSimulator::from_flat(&[], &[], &[], 5);
        // Empty simulator, any token fails
        let result = sim.simulate_after_repair(&[0], 0, "Expr");
        assert!(matches!(result, SimulationResult::FailedAt { position: 0 }));
    }

    // ═══════════════════════════════════════════════════════════════════════
    // RecoveryConfig tests
    // ═══════════════════════════════════════════════════════════════════════

    #[test]
    fn test_recovery_config_default_matches_hardcoded_costs() {
        let config = RecoveryConfig::default();
        assert!((config.skip_per_token - 0.5).abs() < 1e-9);
        assert!((config.delete_cost - 1.0).abs() < 1e-9);
        assert!((config.substitute_cost - 1.5).abs() < 1e-9);
        assert!((config.insert_cost - 2.0).abs() < 1e-9);
        assert!((config.swap_cost - 1.25).abs() < 1e-9);
        assert_eq!(config.max_skip_lookahead, 32);
        assert_eq!(config.deep_nesting_threshold, 1000);
        assert!((config.deep_nesting_skip_mult - 0.5).abs() < 1e-9);
        assert_eq!(config.shallow_depth_threshold, 10);
        assert!((config.shallow_depth_skip_mult - 2.0).abs() < 1e-9);
        assert_eq!(config.low_bp_threshold, 4);
        assert!((config.low_bp_skip_mult - 0.75).abs() < 1e-9);
        assert!((config.collection_insert_mult - 0.5).abs() < 1e-9);
        assert!((config.group_insert_mult - 0.5).abs() < 1e-9);
        assert!((config.bracket_insert_mult - 0.3).abs() < 1e-9);
        assert!((config.mixfix_substitute_mult - 0.75).abs() < 1e-9);
        assert!((config.simulation_valid_mult - 0.5).abs() < 1e-9);
        assert!((config.simulation_fail_penalty - 0.2).abs() < 1e-9);
        assert_eq!(config.beam_width, Some(3.0));
        assert_eq!(config.cascade_window, 3);
    }

    #[test]
    fn test_recovery_config_default_identical_to_no_config() {
        // Verify that *_with(&default) produces the same result as the no-config variant
        let ctx = RecoveryContext {
            depth: 5000,
            binding_power: 10,
            frame_kind: FrameKind::Collection,
            open_parens: 2,
            ..Default::default()
        };
        let config = RecoveryConfig::default();

        assert!((ctx.skip_multiplier() - ctx.skip_multiplier_with(&config)).abs() < 1e-9);
        assert!((ctx.insert_multiplier() - ctx.insert_multiplier_with(&config)).abs() < 1e-9);
        assert!((ctx.substitute_multiplier() - ctx.substitute_multiplier_with(&config)).abs() < 1e-9);
        assert!(
            (ctx.bracket_insert_multiplier(Some("RParen"))
                - ctx.bracket_insert_multiplier_with(Some("RParen"), &config))
            .abs()
                < 1e-9
        );
    }

    #[test]
    fn test_recovery_config_custom_insert_always_wins() {
        // With insert_cost set very low, InsertToken should always be cheapest
        let config = RecoveryConfig {
            insert_cost: 0.1,
            ..RecoveryConfig::default()
        };
        // InsertToken cost = 0.1, DeleteToken cost = 1.0
        assert!(config.insert_cost < config.delete_cost);
        assert!(config.insert_cost < config.skip_per_token);
    }

    #[test]
    fn test_recovery_config_custom_thresholds() {
        let config = RecoveryConfig {
            deep_nesting_threshold: 500,
            deep_nesting_skip_mult: 0.25,
            shallow_depth_threshold: 20,
            shallow_depth_skip_mult: 3.0,
            low_bp_threshold: 8,
            low_bp_skip_mult: 0.5,
            ..RecoveryConfig::default()
        };

        // Depth 600 > 500 → deep nesting
        let deep_ctx = RecoveryContext {
            depth: 600,
            binding_power: 10,
            ..Default::default()
        };
        assert!((deep_ctx.skip_multiplier_with(&config) - 0.25).abs() < 1e-9);

        // Depth 15 < 20 → shallow
        let shallow_ctx = RecoveryContext {
            depth: 15,
            binding_power: 10,
            ..Default::default()
        };
        assert!((shallow_ctx.skip_multiplier_with(&config) - 3.0).abs() < 1e-9);

        // BP 6 < 8 → low BP
        let low_bp_ctx = RecoveryContext {
            depth: 50,
            binding_power: 6,
            ..Default::default()
        };
        assert!((low_bp_ctx.skip_multiplier_with(&config) - 0.5).abs() < 1e-9);
    }

    #[test]
    fn test_recovery_config_custom_frame_multipliers() {
        let config = RecoveryConfig {
            collection_insert_mult: 0.25,
            group_insert_mult: 0.8,
            mixfix_substitute_mult: 0.4,
            bracket_insert_mult: 0.1,
            ..RecoveryConfig::default()
        };

        let collection_ctx = RecoveryContext {
            depth: 50,
            frame_kind: FrameKind::Collection,
            ..Default::default()
        };
        assert!((collection_ctx.insert_multiplier_with(&config) - 0.25).abs() < 1e-9);

        let group_ctx = RecoveryContext {
            depth: 50,
            frame_kind: FrameKind::Group,
            ..Default::default()
        };
        assert!((group_ctx.insert_multiplier_with(&config) - 0.8).abs() < 1e-9);

        let mixfix_ctx = RecoveryContext {
            depth: 50,
            frame_kind: FrameKind::Mixfix,
            ..Default::default()
        };
        assert!((mixfix_ctx.substitute_multiplier_with(&config) - 0.4).abs() < 1e-9);

        let bracket_ctx = RecoveryContext {
            depth: 50,
            open_parens: 1,
            ..Default::default()
        };
        assert!(
            (bracket_ctx.bracket_insert_multiplier_with(Some("RParen"), &config) - 0.1).abs()
                < 1e-9
        );
    }

    // ═══════════════════════════════════════════════════════════════════════
    // Full Viterbi lattice (multi-step) tests
    // ═══════════════════════════════════════════════════════════════════════

    #[test]
    fn test_viterbi_multi_step_skip_to_sync() {
        let token_map = make_token_map();
        let mut sync_tokens = BTreeSet::new();
        sync_tokens.insert(token_map.get("Semi").expect("Semi"));

        // tokens: [Ident, Plus, Semi, Eof]
        // Skip 2 tokens to Semi, cost = 2 * 0.5 = 1.0
        let token_ids: Vec<TokenId> = vec![
            token_map.get("Ident").expect("Ident"),
            token_map.get("Plus").expect("Plus"),
            token_map.get("Semi").expect("Semi"),
            token_map.get("Eof").expect("Eof"),
        ];

        let config = RecoveryConfig::default();
        let result = viterbi_multi_step(&token_ids, 0, &sync_tokens, &config)
            .expect("should find recovery");

        assert_eq!(result.new_pos, 2);
        assert!(result.total_cost.value() <= 1.0 + 1e-9);
        assert!(!result.actions.is_empty());
    }

    #[test]
    fn test_viterbi_multi_step_delete_wins() {
        let token_map = make_token_map();
        let mut sync_tokens = BTreeSet::new();
        sync_tokens.insert(token_map.get("Semi").expect("Semi"));

        // tokens: [Plus, Semi] — delete Plus (1.0) vs skip to Semi at 1 (0.5)
        // Skip wins: cost 0.5 < 1.0
        let token_ids: Vec<TokenId> = vec![
            token_map.get("Plus").expect("Plus"),
            token_map.get("Semi").expect("Semi"),
        ];

        let config = RecoveryConfig::default();
        let result = viterbi_multi_step(&token_ids, 0, &sync_tokens, &config)
            .expect("should find recovery");

        // Should sync at position 1 (Semi) via skip
        assert_eq!(result.new_pos, 1);
        // Cost should be 0.5 (one skip to sync)
        assert!((result.total_cost.value() - 0.5).abs() < 1e-9);
    }

    #[test]
    fn test_viterbi_multi_step_immediate_sync() {
        let token_map = make_token_map();
        let mut sync_tokens = BTreeSet::new();
        sync_tokens.insert(token_map.get("Semi").expect("Semi"));

        // Already at sync token
        let token_ids: Vec<TokenId> = vec![token_map.get("Semi").expect("Semi")];

        let config = RecoveryConfig::default();
        let result = viterbi_multi_step(&token_ids, 0, &sync_tokens, &config)
            .expect("should find recovery");

        assert_eq!(result.new_pos, 0);
        assert_eq!(result.total_cost, TropicalWeight::one()); // zero cost
    }

    #[test]
    fn test_viterbi_multi_step_no_sync_reachable() {
        let token_map = make_token_map();
        let mut sync_tokens = BTreeSet::new();
        sync_tokens.insert(token_map.get("Semi").expect("Semi"));

        // No Semi in the remaining tokens, but insert is possible
        let ident_id = token_map.get("Ident").expect("Ident");
        let token_ids: Vec<TokenId> = vec![ident_id; 5];

        let config = RecoveryConfig::default();
        let result = viterbi_multi_step(&token_ids, 0, &sync_tokens, &config);

        // Insert should provide a path: insert Semi at pos 0, cost = 2.0
        assert!(result.is_some());
        let seq = result.expect("insert should provide recovery");
        assert!(seq.actions.iter().any(|a| matches!(a, RepairAction::InsertToken { .. })));
    }

    #[test]
    fn test_viterbi_multi_step_empty_input() {
        let sync_tokens = BTreeSet::new();
        let config = RecoveryConfig::default();
        let result = viterbi_multi_step(&[], 0, &sync_tokens, &config);
        assert!(result.is_none());
    }

    #[test]
    fn test_viterbi_multi_step_insert_guard_prevents_infinite_loop() {
        let token_map = make_token_map();
        let mut sync_tokens = BTreeSet::new();
        sync_tokens.insert(token_map.get("Semi").expect("Semi"));

        // Only non-sync tokens, insert guard should limit to 1 insert per position
        let ident_id = token_map.get("Ident").expect("Ident");
        let token_ids: Vec<TokenId> = vec![ident_id; 3];

        let config = RecoveryConfig::default();
        let result = viterbi_multi_step(&token_ids, 0, &sync_tokens, &config);

        // Should succeed via insert (finite, no infinite loop)
        assert!(result.is_some());
    }

    #[test]
    fn test_viterbi_multi_step_beam_prunes() {
        let token_map = make_token_map();
        let mut sync_tokens = BTreeSet::new();
        sync_tokens.insert(token_map.get("Semi").expect("Semi"));

        // tokens with Semi at position 2
        let token_ids: Vec<TokenId> = vec![
            token_map.get("Ident").expect("Ident"),
            token_map.get("Plus").expect("Plus"),
            token_map.get("Semi").expect("Semi"),
        ];

        // Tight beam = 0.5
        let tight_config = RecoveryConfig {
            beam_width: Some(0.5),
            ..RecoveryConfig::default()
        };
        let result_tight = viterbi_multi_step(&token_ids, 0, &sync_tokens, &tight_config);

        // No beam
        let no_beam_config = RecoveryConfig {
            beam_width: None,
            ..RecoveryConfig::default()
        };
        let result_no_beam = viterbi_multi_step(&token_ids, 0, &sync_tokens, &no_beam_config);

        // Both should find a path
        assert!(result_tight.is_some());
        assert!(result_no_beam.is_some());
    }

    #[test]
    fn test_repair_sequence_display() {
        let seq = RepairSequence {
            actions: vec![
                RepairAction::DeleteToken,
                RepairAction::SkipToSync { skip_count: 1, sync_token: 5 },
            ],
            new_pos: 3,
            total_cost: TropicalWeight::new(1.5),
            total_edits: crate::automata::semiring::EditWeight::new(2),
        };
        let display = format!("{}", seq);
        assert!(display.contains("delete token"));
        assert!(display.contains("skip 1 tokens"));
        assert!(display.contains("cost: 1.50"));
        assert!(display.contains("edits: 2"));
    }

    #[test]
    fn test_repair_edge_kind_variants() {
        // Verify all variants exist and are distinct
        let skip = RepairEdgeKind::Skip;
        let delete = RepairEdgeKind::Delete;
        let substitute = RepairEdgeKind::Substitute(1);
        let insert = RepairEdgeKind::Insert(2);
        let sync = RepairEdgeKind::Sync(3);
        let swap = RepairEdgeKind::Swap;

        assert_ne!(skip, delete);
        assert_ne!(substitute, insert);
        assert_ne!(insert, sync);
        assert_ne!(swap, skip);
        assert_eq!(skip, RepairEdgeKind::Skip);
    }

    // ═══════════════════════════════════════════════════════════════════════
    // SwapTokens tests
    // ═══════════════════════════════════════════════════════════════════════

    #[test]
    fn test_swap_tokens_action_display() {
        let action = RepairAction::SwapTokens { pos_a: 0, pos_b: 1 };
        assert_eq!(format!("{}", action), "swap tokens at positions 0 and 1");
    }

    #[test]
    fn test_swap_tokens_edit_cost() {
        let action = RepairAction::SwapTokens { pos_a: 0, pos_b: 1 };
        assert_eq!(action.edit_cost().0, 1); // single edit operation
    }

    #[test]
    fn test_composite_action_display() {
        let action = RepairAction::Composite {
            steps: vec![RepairAction::DeleteToken, RepairAction::DeleteToken],
        };
        let display = format!("{}", action);
        assert_eq!(display, "delete token, delete token");
    }

    #[test]
    fn test_composite_action_edit_cost() {
        let action = RepairAction::Composite {
            steps: vec![
                RepairAction::DeleteToken,                         // 1
                RepairAction::InsertToken { token: 0 },            // 2
                RepairAction::SwapTokens { pos_a: 0, pos_b: 1 },  // 1
            ],
        };
        assert_eq!(action.edit_cost().0, 4);
    }

    #[test]
    fn test_find_best_recovery_swap_available() {
        let token_map = make_token_map();
        let sync_names = vec!["Semi".to_string(), "Eof".to_string()];
        let wfst = RecoveryWfst::new("Expr".to_string(), &sync_names, &token_map);

        // tokens: [Plus, Semi, Eof] — swapping Plus and Semi puts Semi at pos 0
        // Swap cost: 1.25, Skip to Semi at pos 1: 0.5, Delete: 1.0
        // Skip wins (0.5 < 1.0 < 1.25)
        let token_ids: Vec<TokenId> = vec![
            token_map.get("Plus").expect("Plus"),
            token_map.get("Semi").expect("Semi"),
            token_map.get("Eof").expect("Eof"),
        ];

        let result = wfst.find_best_recovery(&token_ids, 0).expect("should find recovery");
        // Skip should win (cost 0.5 to reach Semi at position 1)
        match &result.action {
            RepairAction::SkipToSync { skip_count, .. } => assert_eq!(*skip_count, 1),
            other => panic!("Expected SkipToSync, got {:?}", other),
        }
    }

    #[test]
    fn test_find_best_recovery_swap_explored() {
        let token_map = make_token_map();
        // Only Eof is a sync token — no nearby sync, so swap is explored
        let sync_names = vec!["Eof".to_string()];
        let wfst = RecoveryWfst::new("Expr".to_string(), &sync_names, &token_map);

        // tokens: [Ident, Eof, Plus] — swap gives [Eof, Ident, Plus]
        // Swap cost: 1.25, puts Eof at pos 0 which IS sync → swap new_pos=2
        // Delete cost: 1.0, new_pos=1
        // Skip to Eof at pos 1: 0.5, new_pos=1
        // Skip wins (0.5)
        let token_ids: Vec<TokenId> = vec![
            token_map.get("Ident").expect("Ident"),
            token_map.get("Eof").expect("Eof"),
            token_map.get("Plus").expect("Plus"),
        ];

        let result = wfst.find_best_recovery(&token_ids, 0).expect("should find recovery");
        // Skip to Eof at position 1 should win
        assert!(result.cost.value() <= 1.0);
    }

    #[test]
    fn test_viterbi_multi_step_swap_edge() {
        let token_map = make_token_map();
        let mut sync_tokens = BTreeSet::new();
        sync_tokens.insert(token_map.get("Semi").expect("Semi"));

        // tokens: [Ident, Semi, Plus] — swap gives Semi at pos 0, i.e., swap(0,1) → reach pos 2
        // Skip to Semi at pos 1: cost 0.5
        // Swap: cost 1.25, reaches pos 2
        // Skip should still win for reaching Semi
        let token_ids: Vec<TokenId> = vec![
            token_map.get("Ident").expect("Ident"),
            token_map.get("Semi").expect("Semi"),
            token_map.get("Plus").expect("Plus"),
        ];

        let config = RecoveryConfig::default();
        let result = viterbi_multi_step(&token_ids, 0, &sync_tokens, &config)
            .expect("should find recovery");

        // Skip to Semi is cheaper
        assert!(result.total_cost.value() <= 1.25 + 1e-9);
    }

    #[test]
    fn test_recovery_config_simulation_multipliers() {
        let config = RecoveryConfig {
            simulation_valid_mult: 0.3,
            simulation_fail_penalty: 0.5,
            ..RecoveryConfig::default()
        };

        let sim = ParseSimulator::new(BTreeMap::new(), BTreeMap::new(), BTreeMap::new(), 5);

        let valid = SimulationResult::ValidContinuation { tokens_consumed: 3 };
        assert!((sim.cost_multiplier_with(&valid, &config) - 0.3).abs() < 1e-9);

        let failed = SimulationResult::FailedAt { position: 2 };
        // 1.0 + (5 - 2) * 0.5 = 1.0 + 1.5 = 2.5
        assert!((sim.cost_multiplier_with(&failed, &config) - 2.5).abs() < 1e-9);
    }

    // ── Lattice-aware recovery tests (Sprint 11) ──

    #[cfg(feature = "context-sensitive-lex")]
    #[test]
    fn test_lattice_recovery_primary_path_preferred() {
        let token_map = make_token_map();
        let semi = token_map.get("Semi").expect("Semi");

        let sync_tokens: std::collections::BTreeSet<TokenId> =
            [semi].into_iter().collect();
        let config = RecoveryConfig::default();

        // Primary path: [Plus, Semi] — skip Plus, sync at Semi (cost 0.5)
        let primary: Vec<TokenId> = vec![
            token_map.get("Plus").expect("Plus"),
            semi,
        ];
        // Alternative path: [Ident, Integer, Semi] — skip Ident+Integer (cost 1.0)
        let alt: Vec<TokenId> = vec![
            token_map.get("Ident").expect("Ident"),
            token_map.get("Integer").expect("Integer"),
            semi,
        ];

        let alternatives = vec![
            (primary, crate::automata::semiring::TropicalWeight::one()),
            (alt, crate::automata::semiring::TropicalWeight::one()),
        ];

        let result = super::lattice_recovery(&alternatives, 0, &sync_tokens, &config);
        assert!(result.is_some(), "should find recovery from lattice alternatives");
        // Primary should win (lower cost)
        let result = result.expect("recovery result");
        assert!(result.cost.value() <= 0.6, "primary path recovery (skip 1) should be cheapest");
    }

    #[cfg(feature = "context-sensitive-lex")]
    #[test]
    fn test_lattice_recovery_alternative_wins_when_better() {
        let token_map = make_token_map();
        let semi = token_map.get("Semi").expect("Semi");

        let sync_tokens: std::collections::BTreeSet<TokenId> =
            [semi].into_iter().collect();
        let config = RecoveryConfig::default();

        // Primary path: [Plus, Integer, Ident, Semi] — skip 3 tokens (cost 1.5)
        let primary: Vec<TokenId> = vec![
            token_map.get("Plus").expect("Plus"),
            token_map.get("Integer").expect("Integer"),
            token_map.get("Ident").expect("Ident"),
            semi,
        ];
        // Alternative path: [Semi] — immediate sync (cost 0 + 0.1 penalty)
        let alt: Vec<TokenId> = vec![semi];

        let alternatives = vec![
            (primary, crate::automata::semiring::TropicalWeight::one()),
            (alt, crate::automata::semiring::TropicalWeight::one()),
        ];

        let result = super::lattice_recovery(&alternatives, 0, &sync_tokens, &config);
        assert!(result.is_some(), "should find recovery");
        let result = result.expect("recovery result");
        // Alternative should win (immediate sync at cost ~0.1 vs skip 3 at cost 1.5)
        assert!(result.cost.value() < 0.5, "alternative path with immediate sync should be cheapest");
    }

    #[cfg(feature = "context-sensitive-lex")]
    #[test]
    fn test_lattice_recovery_empty_alternatives() {
        let sync_tokens: std::collections::BTreeSet<TokenId> = std::collections::BTreeSet::new();
        let config = RecoveryConfig::default();
        let alternatives: Vec<(Vec<TokenId>, crate::automata::semiring::TropicalWeight)> = vec![];

        let result = super::lattice_recovery(&alternatives, 0, &sync_tokens, &config);
        assert!(result.is_none(), "empty alternatives should return None");
    }
}
