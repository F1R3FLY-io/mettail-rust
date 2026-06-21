use super::*;

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

    // ── Sprint 7: Dispatch context ────────────────────────────────────────
    /// ContextWeight bitset of rules active at the error point.
    /// When set, recovery actions are scored by context viability: sync tokens
    /// whose FOLLOW context intersects the dispatch context are preferred.
    /// `None` when no ContextWeight analysis is available.
    pub dispatch_context: Option<crate::automata::semiring::ContextWeight>,
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
            dispatch_context: None,
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

        // VPA-derived nesting ceiling: strongly favor skip when beyond grammar capacity
        if let Some(ceiling) = config.vpa_nesting_ceiling {
            if self.depth > ceiling {
                m *= 0.3;
            }
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

    /// Sprint 7: Compute a cost multiplier based on ContextWeight viability.
    ///
    /// When `dispatch_context` is set, intersects it with the sync token's
    /// `follow_context` to determine how many active rules can reach this
    /// sync token. More viable rules → lower multiplier (cheaper recovery).
    ///
    /// Returns `1.0` when no dispatch context is available.
    pub fn context_viability_multiplier(
        &self,
        follow_ctx: &crate::automata::semiring::ContextWeight,
    ) -> f64 {
        use crate::automata::semiring::Semiring;

        match &self.dispatch_context {
            Some(dispatch) => {
                let intersection = dispatch.times(follow_ctx);
                let viable = intersection.count();
                if viable == 0 {
                    // No viable rules — this sync token is a false positive
                    5.0 // heavy penalty
                } else {
                    // More viable rules → cheaper (inverse)
                    1.0 / (viable as f64).max(1.0)
                }
            },
            None => 1.0, // no dispatch context → neutral
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
