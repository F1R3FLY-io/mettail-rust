use super::*;

/// B2: Joint recovery cost — tropical for parse quality, edit-distance for repair minimality.
///
/// Lexicographic ordering via `ProductWeight`: tropical cost is primary (parse quality),
/// edit-distance is tiebreaker (repair minimality). Among equally-ranked repairs,
/// the one with fewer edits wins.
pub type RecoveryCost = ProductWeight<TropicalWeight, EditWeight>;

// ══════════════════════════════════════════════════════════════════════════════
// RecoveryConfig — parameterized cost/threshold tuning
// ══════════════════════════════════════════════════════════════════════════════

/// Parameterized configuration for error recovery costs and thresholds.
///
/// Grammar authors can tune recovery behavior by adjusting these values.
/// Search routines observe `normalized_for_recovery_search()`, so negative
/// or non-finite costs and multipliers fall back to defaults before they can
/// affect Viterbi cutoffs or posterior analysis. The `Default` implementation
/// matches the current hardcoded constants in `costs::*` and
/// `RecoveryContext` multiplier methods.
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

    // ── Viterbi search bound ─────────────────────────────────────────────
    /// Beam width for Viterbi recovery (default: Some(3.0)).
    /// `None` disables the cutoff. Negative and non-finite values are treated
    /// as disabled by the search routines so the cutoff cannot prune a cheaper
    /// path than the best complete repair found so far.
    pub beam_width: Option<f64>,

    // ── Cascade prevention ───────────────────────────────────────────────
    /// Number of tokens within which consecutive errors are suppressed (default: 3).
    pub cascade_window: usize,

    // ── B2: Adaptive recovery weight modulation ─────────────────────────
    // ── A1: VPA nesting depth → recovery cost modulation ────────────────
    /// VPA-derived upper bound on valid nesting depth.
    /// When set and current depth exceeds this value, skip actions are strongly favored
    /// (input is structurally beyond grammar's capacity). Default: None.
    pub vpa_nesting_ceiling: Option<usize>,

    // ── B2: Adaptive recovery weight modulation ─────────────────────────
    /// Running weight above which the ambiguous regime activates (default: 1.0).
    /// Below this threshold, the parse path is considered deterministic;
    /// above it, the path has accumulated significant ambiguity.
    pub adaptive_weight_threshold: f64,
    /// Skip cost multiplier in deterministic regime (weight < threshold).
    /// Lower values make skip cheaper when the parse path is confident.
    /// Default: 0.75.
    pub deterministic_skip_discount: f64,
    /// Insert cost multiplier in ambiguous regime (weight >= threshold).
    /// Lower values make insert cheaper when the parse path is ambiguous,
    /// preserving context when confidence is low. Default: 0.5.
    pub ambiguous_insert_discount: f64,

    // ── Bounded recovery (Stage 3.20 / L12, 2026-05-06) ─────────────────
    /// Maximum number of recovery dispatches a single cursor may experience
    /// before the walker emits Error instead of allocating another recovery
    /// Fork. Bounds the 8^N cursor-explosion that recursive recovery
    /// dispatch would otherwise produce when every Fork branch transitions
    /// back to PrefixDispatch and re-encounters the orphan dead-end.
    /// Default 3 — empirically sufficient for real-world parses while
    /// bounding recursive recovery fanout. Each `apply_action_to_cursor::Fork`
    /// arm increments the child's `recovery_depth` by 1 when it detects a
    /// recovery Fork (branches whose BuilderDelta effect is RecoveryEvent /
    /// InsertToken / SubstituteToken / ApplyRecoverySequence).
    pub max_recovery_depth: u8,
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
            vpa_nesting_ceiling: None,
            adaptive_weight_threshold: 1.0,
            deterministic_skip_discount: 0.75,
            ambiguous_insert_discount: 0.5,
            max_recovery_depth: 3,
        }
    }
}

impl RecoveryConfig {
    #[inline]
    fn normalized_nonnegative(value: f64, fallback: f64) -> f64 {
        if value.is_finite() && value >= 0.0 {
            value
        } else {
            fallback
        }
    }

    /// Return the cost configuration observed by recovery search.
    ///
    /// Public callers may construct `RecoveryConfig` values directly or load
    /// learned weights. The Viterbi cutoff and the forward/backward lattice
    /// rely on finite, nonnegative edge weights so path extension cannot make
    /// a candidate cheaper after it has crossed a bound.
    pub fn normalized_for_recovery_search(&self) -> Self {
        let default = RecoveryConfig::default();
        RecoveryConfig {
            skip_per_token: Self::normalized_nonnegative(
                self.skip_per_token,
                default.skip_per_token,
            ),
            delete_cost: Self::normalized_nonnegative(self.delete_cost, default.delete_cost),
            substitute_cost: Self::normalized_nonnegative(
                self.substitute_cost,
                default.substitute_cost,
            ),
            insert_cost: Self::normalized_nonnegative(self.insert_cost, default.insert_cost),
            swap_cost: Self::normalized_nonnegative(self.swap_cost, default.swap_cost),
            max_skip_lookahead: self.max_skip_lookahead,
            deep_nesting_threshold: self.deep_nesting_threshold,
            deep_nesting_skip_mult: Self::normalized_nonnegative(
                self.deep_nesting_skip_mult,
                default.deep_nesting_skip_mult,
            ),
            shallow_depth_threshold: self.shallow_depth_threshold,
            shallow_depth_skip_mult: Self::normalized_nonnegative(
                self.shallow_depth_skip_mult,
                default.shallow_depth_skip_mult,
            ),
            low_bp_threshold: self.low_bp_threshold,
            low_bp_skip_mult: Self::normalized_nonnegative(
                self.low_bp_skip_mult,
                default.low_bp_skip_mult,
            ),
            collection_insert_mult: Self::normalized_nonnegative(
                self.collection_insert_mult,
                default.collection_insert_mult,
            ),
            group_insert_mult: Self::normalized_nonnegative(
                self.group_insert_mult,
                default.group_insert_mult,
            ),
            bracket_insert_mult: Self::normalized_nonnegative(
                self.bracket_insert_mult,
                default.bracket_insert_mult,
            ),
            mixfix_substitute_mult: Self::normalized_nonnegative(
                self.mixfix_substitute_mult,
                default.mixfix_substitute_mult,
            ),
            simulation_valid_mult: Self::normalized_nonnegative(
                self.simulation_valid_mult,
                default.simulation_valid_mult,
            ),
            simulation_fail_penalty: Self::normalized_nonnegative(
                self.simulation_fail_penalty,
                default.simulation_fail_penalty,
            ),
            beam_width: self
                .beam_width
                .filter(|width| width.is_finite() && *width >= 0.0),
            cascade_window: self.cascade_window,
            vpa_nesting_ceiling: self.vpa_nesting_ceiling,
            adaptive_weight_threshold: Self::normalized_nonnegative(
                self.adaptive_weight_threshold,
                default.adaptive_weight_threshold,
            ),
            deterministic_skip_discount: Self::normalized_nonnegative(
                self.deterministic_skip_discount,
                default.deterministic_skip_discount,
            ),
            ambiguous_insert_discount: Self::normalized_nonnegative(
                self.ambiguous_insert_discount,
                default.ambiguous_insert_discount,
            ),
            max_recovery_depth: self.max_recovery_depth,
        }
    }

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
        if let Some(&v) = weights.get("adaptive_weight_threshold") {
            self.adaptive_weight_threshold = v;
        }
        if let Some(&v) = weights.get("deterministic_skip_discount") {
            self.deterministic_skip_discount = v;
        }
        if let Some(&v) = weights.get("ambiguous_insert_discount") {
            self.ambiguous_insert_discount = v;
        }
        *self = self.normalized_for_recovery_search();
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
        let name = |id: TokenId| -> &str { token_names.get(id as usize).copied().unwrap_or("?") };
        match self {
            RepairAction::SkipToSync { skip_count, sync_token } => {
                format!("skip {} token(s) to '{}'", skip_count, name(*sync_token))
            },
            RepairAction::InsertToken { token } => {
                format!("insert missing '{}'", name(*token))
            },
            RepairAction::DeleteToken => "delete unexpected token".to_string(),
            RepairAction::SubstituteToken { replacement } => {
                format!("expected '{}' here", name(*replacement))
            },
            RepairAction::SwapTokens { .. } => "swap adjacent tokens".to_string(),
            RepairAction::Composite { steps } => steps
                .iter()
                .map(|s| s.describe(token_names))
                .collect::<Vec<_>>()
                .join(", "),
            RepairAction::CategorySwitch { from_category, to_category } => {
                format!("try parsing as {} (cast {} → {})", to_category, to_category, from_category)
            },
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
    /// B2: Joint cost — ProductWeight<TropicalWeight, EditWeight>.
    ///
    /// Lexicographic ordering: tropical cost is primary (parse quality),
    /// edit-distance is tiebreaker (repair minimality).
    pub cost: RecoveryCost,
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
            "repair: {} (cost: {:.1}, edits: {}, new_pos: {})",
            self.action,
            self.cost.left.value(),
            self.cost.right.0,
            self.new_pos
        )
    }
}
