//! Lexicographic weight semiring with left-projection times semantics.
//!
//! Stage 2 of W7 plan v5.1. Provides [`LexicographicWeight`], the canonical
//! weight type for the runtime WPDS-based parser. Encodes a primary cost
//! (tropical) plus two integer tiebreaks (`src_idx`, `rule_idx`) corresponding
//! to source-category-order and rule-within-category declaration order.
//!
//! ## Semiring axioms
//!
//! `(LexicographicWeight, ⊕, ⊗, 0, 1)` forms a semiring where:
//!
//! - `0 = (∞, u16::MAX, u16::MAX)` — additive identity (unreachable)
//! - `1 = (0, _, _)` where `_.is_one()` checks only the primary
//! - `a ⊕ b` — lex-min: compare `primary`, then `src_idx`, then `rule_idx`
//! - `a ⊗ b` — primary is tropical sum (`+`); secondary uses **left-projection**
//!   with identity-aware short-circuit (see §2 below)
//!
//! Verified by proptest tests at the bottom of this module:
//! - Identity laws (`1 ⊗ a = a ⊗ 1 = a`) — exact
//! - Zero annihilation (`0 ⊗ a = a ⊗ 0 = 0`) — exact
//! - Plus commutativity (`a ⊕ b = b ⊕ a`) — exact (lex-min selection)
//! - Plus associativity (`(a ⊕ b) ⊕ c = a ⊕ (b ⊕ c)`) — exact
//! - Plus idempotence (`a ⊕ a = a`) — exact
//! - Times associativity (`(a ⊗ b) ⊗ c ≈ a ⊗ (b ⊗ c)`) — **approximate** (see §5)
//! - Distributivity (`a ⊗ (b ⊕ c) = (a ⊗ b) ⊕ (a ⊗ c)` and right form) — exact
//! - Left-projection demonstration when `a` is non-identity — exact
//!
//! ## §5. Floating-point associativity caveat
//!
//! IEEE 754 `f64` addition is **not exactly associative**: `(a + b) + c` and
//! `a + (b + c)` may differ in the last bit due to intermediate rounding.
//! Since `TropicalWeight::times` is `f64::+`, lexicographic times inherits
//! this approximation.
//!
//! Practical impact:
//! - Distributivity (`a ⊗ (b ⊕ c) = (a ⊗ b) ⊕ (a ⊗ c)`) is **exact** because
//!   `⊕` is lex-min selection, not addition — both sides pick the same branch.
//! - Times associativity holds **up to ε** (1e-6 in our property tests).
//! - For grammars with bounded rule weights and bounded path lengths
//!   (the realistic case), the discrepancy is far below any tiebreak boundary.
//!
//! If exact associativity is required (e.g., for formal verification of
//! WPDS poststar convergence), substitute a rational-weight semiring such
//! as `LexicographicWeightQ` (deferred — not needed for runtime parsing).
//!
//! ## §1. Why three components?
//!
//! WPDS rule weights for the runtime parser carry:
//!
//! 1. **Primary cost** (`TropicalWeight`): Sum of per-step costs along the
//!    parse path. Lower is better. Drives the principal "shortest-path"
//!    selection between parse alternatives.
//! 2. **Source-category index** (`src_idx`): Position of the rule's source
//!    category in the `language!` declared order. Encodes the user's
//!    cross-category preference: when two parses produce the same primary
//!    cost, the one originating in the earlier-declared category wins.
//! 3. **Rule index** (`rule_idx`): Position of the rule within its category's
//!    `rules { … }` block. Final tiebreak: among same-cost, same-category
//!    parses, the earlier-declared rule wins.
//!
//! These two integer tiebreaks satisfy the user mandate (recorded in plan
//! v5.1): "rule-within-category tiebreak so long as it does not conflict
//! with source-category-order tiebreak."
//!
//! ## §2. The three candidate `times` semantics
//!
//! Combining tiebreaks along a parse path admits multiple choices. We
//! enumerate them and explain why **left-projection** is correct here.
//!
//! Given `(a, b)` and `(c, d)` (suppressing the third component for brevity):
//!
//! ### Option A — Full-product times (rejected)
//!
//! ```text
//! (a, b) ⊗ (c, d) = (a ⊗_L c, b ⊗_R d)
//! ```
//!
//! What `ProductWeight` does (component-wise). Suitable when both components
//! genuinely accumulate (e.g., parse-cost AND repair-cost in
//! `RecoveryCost = ProductWeight<TropicalWeight, EditWeight>`).
//!
//! **Rejected for lex tiebreak**: `src_idx ⊗_R src_idx` has no natural
//! semantics. We are not summing category indices; we want to retain the
//! identity of the entry-most rule.
//!
//! ### Option B — Min-projection times (rejected)
//!
//! ```text
//! (a, b) ⊗ (c, d) = (a ⊗_L c, min(b, d))
//! ```
//!
//! Tiebreak takes the minimum (best) value encountered anywhere along the
//! path. Useful when "best category visited" is the criterion.
//!
//! **Rejected for lex tiebreak**: A parse rooted in a low-priority category
//! could "inherit" a high-priority cousin's tiebreak via composition,
//! masking the real source. This violates user intent, which is to
//! disambiguate based on **where the parse started**, not what it later
//! encountered.
//!
//! ### Option C — Left-projection times (chosen)
//!
//! ```text
//! (a, b) ⊗ (c, d) = (a ⊗_L c, b)   if neither operand is identity
//! 1     ⊗ (c, d) = (c, d)
//! (a, b) ⊗ 1     = (a, b)
//! ```
//!
//! The **leftmost rule** in the composition determines the tiebreak. Since
//! WPDS push rules emit the entry symbol first (callee bottom), and replace
//! rules step inside a single category, the leftmost factor in the times
//! product is the **entry decision**. This is exactly the user-intended
//! semantics: "this parse used category X first, even if it later called
//! into Y."
//!
//! Identity short-circuit is required to satisfy `1 ⊗ a = a` and `a ⊗ 1 = a`
//! since `1.src_idx = u16::MAX` would otherwise leak as the projected value.
//!
//! ## §3. Identity check semantics
//!
//! `is_one()` checks **only** the primary component (tropical zero). The
//! tiebreak components are unconstrained for identities — any `(0, X, Y)`
//! is multiplicatively neutral. Multiple "identity-like" weights exist
//! algebraically, but `LexicographicWeight::one()` returns the canonical
//! `(0, u16::MAX, u16::MAX)` form. The is-one check ignores tiebreak so
//! that:
//!
//! - `(0, src, rule) ⊗ (a, b, c) = (a, b, c)` — left's tiebreak is dropped
//!   because the left contributed no cost.
//! - This makes path concatenation associative without depending on the
//!   specific tiebreak values held by intermediate identity-like weights.
//!
//! `is_zero()` similarly checks only the primary (tropical infinity).
//!
//! ## §4. Mapping to the WPDS rule emitter
//!
//! Stage 6 codegen will emit each WPDS rule with:
//!
//! ```rust,ignore
//! WpdsRule::Push {
//!     from_gamma,
//!     to_gamma_bottom,
//!     to_gamma_top,
//!     weight: LexicographicWeight {
//!         primary: TropicalWeight(rule_cost),
//!         src_idx: rule.source_category_src_idx,
//!         rule_idx: rule.index_within_category,
//!     },
//! }
//! ```
//!
//! The walker (Stage 4) accumulates these via `times` along the active
//! configuration's path; ambiguous fanout merges via `plus`.

use std::cmp::Ordering;
use std::fmt;

use crate::{
    CompleteSemiring, DetectableZero, IdempotentSemiring, LexProvenance, Semiring, StarSemiring,
    TropicalDeltaWeight, TropicalWeight,
};

// ══════════════════════════════════════════════════════════════════════════════
// LexicographicWeight
// ══════════════════════════════════════════════════════════════════════════════

/// Four-component lexicographic weight: primary tropical cost + three integer
/// tiebreaks. Order: `primary > lex_alt_idx > src_idx > rule_idx`.
///
/// L1 (2026-04-28): added `lex_alt_idx` for lex-time disambiguation. When a
/// DFA's `alt_accepts` slice contains 2+ TokenKinds at the same byte position,
/// the walker forks across alternatives and uses `lex_alt_idx` (per the L2
/// `LexAlternative` ordering) to break ties. Lower index = higher-priority
/// alternative. Default `0` means "no lex ambiguity at this token".
///
/// `lex_alt_idx` lives ABOVE `src_idx` in priority: lex disambiguation runs
/// before parser dispatch (per the WPDS-edge model in #64), so a parse path
/// preferring a lower-index lex alternative wins over a path with the same
/// primary cost but a higher-index alternative even if its `src_idx` would
/// otherwise have won.
///
/// See module docs for the semantic justification of left-projection times.
#[derive(Clone, Copy, PartialEq)]
pub struct LexicographicWeight {
    /// Primary cost — tropical (lower is better).
    pub primary: TropicalWeight,
    /// Lex-alternative index within a DFA accept state (L1, lower wins).
    /// `0` means "no lex ambiguity at this token" — the default.
    pub lex_alt_idx: u16,
    /// Source-category index in the language's declared order (lower wins).
    pub src_idx: u16,
    /// Rule index within the category (lower wins).
    pub rule_idx: u16,
}

/// Stage 3.12 / Class A.i (2026-05-01): epsilon cost added to the SKIP
/// branch of an Opt-Group Fork to give TAKE preference when both
/// branches reach Accepted with the same primary cost.
///
/// Reasoning:
/// - TAKE branch weight: `from_cost(0.0, src, rule)` — no penalty.
/// - SKIP branch weight: `from_cost(EPSILON_OPT_SKIP, src, rule)` — a
///   small floor penalty.
///
/// When TAKE succeeds (FIRST set matches), TAKE's primary < SKIP's
/// primary → TAKE wins. When TAKE fails (FIRST set rejects mid-parse),
/// TAKE's cursor dies, SKIP survives at primary `EPSILON_OPT_SKIP`.
///
/// Magnitude `0.5`:
/// - Large enough to dominate floating-point noise from down-stream
///   weight composition.
/// - Small enough that recovery costs (typically `1.0+` per token,
///   per `recovery.rs::TIER1_INSERT_COST`) dominate this epsilon —
///   recovery always loses to a successful Opt-Group SKIP.
///
/// Right-associative dangling-else mechanism (per
/// `plan-class-a-i-opt-group-fork.md`):
/// `if false then if false then 1 else 2`:
/// - Inner-TAKE+Outer-SKIP: weight = 0.0 + EPSILON_OPT_SKIP = 0.5.
/// - Inner-SKIP+Outer-TAKE: weight = EPSILON_OPT_SKIP + 0.0 = 0.5.
/// Both reach Accepted with identical primary (0.5). Tiebreak by
/// cursor-allocation order (TAKE branch is first per `vec![take, skip]`)
/// → Inner-TAKE descendant wins → `IfElse(false, IfElse(false, 1, Some(2)), None)`
/// — right-associative.
pub const EPSILON_OPT_SKIP: f64 = 0.5;

/// Stage 3.18 Cluster 3 BP-tier biases (Commit 2 / Mechanism γ, 2026-05-05).
///
/// These weights bias lex-min selection across the InfixLoop's three
/// operator tiers (infix / postfix / mixfix) when multiple tiers' guards
/// succeed at the same l_bp >= cur_bp. Strictly increasing so that on
/// weight ties (same l_bp, same source category, same rule_idx), the lex-min
/// picks lower tiers (infix preferred over postfix preferred over mixfix).
///
/// For grammars with deliberate inter-tier ambiguity at a token (e.g.
/// G5 — infix and postfix sharing the same trigger token at the same l_bp),
/// these biases enforce the canonical interpretation.
pub const BP_TIER_INFIX: f64 = 0.00;
/// B10 / Option κ Fix B (2026-05-07): Pass 2a CrossCatProjection tier.
/// Strictly between INFIX (0.0) and CROSSCAT_LHS (0.05) so atomic-home
/// wins ties on the same `(pat, guard)` key (preserving home-cat parses)
/// while cross-cat-projection (a direct cat→cat conversion) beats
/// cross-cat-LHS (operator-driven, demands more grammar) when both
/// branches are alive in a mixed bucket.
pub const BP_TIER_CROSSCAT_PROJECTION: f64 = 0.025;
pub const BP_TIER_CROSSCAT_LHS: f64 = 0.05;
pub const BP_TIER_POSTFIX: f64 = 0.10;
pub const BP_TIER_MIXFIX: f64 = 0.20;

/// Pass 2c implicit-cast tier. Pass 2c emits a trigger-bearing syntactic cast
/// (`<Y>To<X> . a:Y |- "trig" "(" a ")" : X`) as a CrossCatDelegate wrap into
/// result_cat's prefix dispatch (covering FIRST(Y) tokens) so internal
/// cross-cat sub-parses succeed (e.g. LtBool's RHS wraps an Int as IntToBool
/// inside `int(false > b < -N)`).
///
/// ## Soundness is NOT this tier's job (Pass-2c token-soundness fix, §5,
/// 2026-05-30)
/// Historically this tier (`0.15`) was justified as making a DIRECT cast
/// "always win lex-min" over an implicit-cast CHAIN that reaches the same
/// configuration — which conflated DISAMBIGUATION with SOUNDNESS and MASKED a
/// token-unsound fabrication (the wrap fires the cast action WITHOUT the
/// cast's `"("`/`")"` being matched, e.g. `bool(0)` → `FloatToBool(IntToFloat(0))`,
/// yield != input). Soundness is now enforced INDEPENDENTLY and on EVIDENCE by
/// `WpdaEngine::min_terminal_span` + the realize-time span filter in
/// `realize_node_leave` (drops any derivation whose result-Symbol span leaves
/// no room for a rule's in-span literal terminals). With the unsound
/// derivations gone regardless of weight, this tier's REMAINING role is a
/// legitimate bias among SOUND coexisting branches — preferring the minimal
/// (fewest-hop) cast interpretation when several SOUND ones tie — exactly like
/// `BP_TIER_CROSSCAT_PROJECTION` / `BP_TIER_CROSSCAT_LHS`. It is RETAINED at
/// `0.15` for that sound-branch ordering (and because removing it regresses
/// legitimately-ambiguous SOUND chained-comparison cases such as
/// `int(b >= N <= b >= M)`, whose canonical interpretation depends on this
/// ordering). The name is kept for continuity; read it as "Pass-2c sound-branch
/// tier", not a soundness guarantee.
///
/// Magnitude `0.15`:
/// - Higher than `BP_TIER_CROSSCAT_LHS = 0.05` so cross-cat-LHS still wins
///   over implicit-cast synthesis when both apply.
/// - Lower than `EPSILON_OPT_SKIP = 0.5` so Opt-Group dangling-else ordering
///   is preserved (`0.5 > 0.15 + 0.025`).
/// - Lower than recovery costs (`TIER1_INSERT_COST = 1.0+`) so productive
///   Pass 2c paths beat recovery dispatch.
pub const BP_TIER_PASS2C_SYNTHESIZED: f64 = 0.15;

impl LexicographicWeight {
    /// Construct a weight with the given components. Sets `lex_alt_idx` to 0.
    #[inline]
    pub const fn new(primary: TropicalWeight, src_idx: u16, rule_idx: u16) -> Self {
        LexicographicWeight {
            primary,
            lex_alt_idx: 0,
            src_idx,
            rule_idx,
        }
    }

    /// Construct a weight with explicit lex-alt index.
    #[inline]
    pub const fn new_with_lex(
        primary: TropicalWeight,
        lex_alt_idx: u16,
        src_idx: u16,
        rule_idx: u16,
    ) -> Self {
        LexicographicWeight { primary, lex_alt_idx, src_idx, rule_idx }
    }

    /// Construct a weight from a raw tropical cost and indices.
    /// Sets `lex_alt_idx` to 0 (default — no lex ambiguity).
    #[inline]
    pub const fn from_cost(cost: f64, src_idx: u16, rule_idx: u16) -> Self {
        LexicographicWeight {
            primary: TropicalWeight::new(cost),
            lex_alt_idx: 0,
            src_idx,
            rule_idx,
        }
    }

    /// Construct a weight with explicit `lex_alt_idx` for lex-fork branches.
    /// L1 (2026-04-28): used by the lex-Fork emission path (L6) when a DFA
    /// position has multiple accepting `TokenKind` alternatives.
    #[inline]
    pub const fn from_cost_with_lex(
        cost: f64,
        src_idx: u16,
        rule_idx: u16,
        lex_alt_idx: u16,
    ) -> Self {
        LexicographicWeight {
            primary: TropicalWeight::new(cost),
            lex_alt_idx,
            src_idx,
            rule_idx,
        }
    }

    /// Lex-comparison: primary, then lex_alt_idx, then src_idx, then rule_idx.
    ///
    /// Returns `Ordering::Less` for the lexicographically smaller weight
    /// (the "better" parse under our priority rules).
    #[inline]
    pub fn lex_cmp(&self, other: &Self) -> Ordering {
        // TropicalWeight uses f64 internally; use total_cmp for NaN safety.
        self.primary
            .0
            .total_cmp(&other.primary.0)
            .then(self.lex_alt_idx.cmp(&other.lex_alt_idx))
            .then(self.src_idx.cmp(&other.src_idx))
            .then(self.rule_idx.cmp(&other.rule_idx))
    }
}

impl Eq for LexicographicWeight {}

impl PartialOrd for LexicographicWeight {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.lex_cmp(other))
    }
}

impl Ord for LexicographicWeight {
    fn cmp(&self, other: &Self) -> Ordering {
        self.lex_cmp(other)
    }
}

impl std::hash::Hash for LexicographicWeight {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        // Hash via bit pattern of primary plus the three indices.
        self.primary.0.to_bits().hash(state);
        self.lex_alt_idx.hash(state);
        self.src_idx.hash(state);
        self.rule_idx.hash(state);
    }
}

impl Semiring for LexicographicWeight {
    #[inline]
    fn zero() -> Self {
        LexicographicWeight {
            primary: TropicalWeight::zero(),
            lex_alt_idx: u16::MAX,
            src_idx: u16::MAX,
            rule_idx: u16::MAX,
        }
    }

    #[inline]
    fn one() -> Self {
        LexicographicWeight {
            primary: TropicalWeight::one(),
            lex_alt_idx: u16::MAX,
            src_idx: u16::MAX,
            rule_idx: u16::MAX,
        }
    }

    /// Lex-min selection: return the lex-smaller of the two operands.
    ///
    /// Equal weights return `*self` (a value-stable but receiver-dependent
    /// choice; result equality is preserved).
    #[inline]
    fn plus(&self, other: &Self) -> Self {
        match self.lex_cmp(other) {
            Ordering::Less | Ordering::Equal => *self,
            Ordering::Greater => *other,
        }
    }

    /// Tropical-sum primary; left-projection on tiebreak components.
    ///
    /// The identity-aware short-circuit is essential: without it,
    /// `1.times(a)` would project `1.src_idx = u16::MAX` and lose `a`'s
    /// real tiebreak.
    #[inline]
    fn times(&self, other: &Self) -> Self {
        if self.is_one() {
            *other
        } else if other.is_one() {
            *self
        } else {
            LexicographicWeight {
                primary: self.primary.times(&other.primary),
                lex_alt_idx: self.lex_alt_idx,
                src_idx: self.src_idx,
                rule_idx: self.rule_idx,
            }
        }
    }

    #[inline]
    fn is_zero(&self) -> bool {
        self.primary.is_zero()
    }

    #[inline]
    fn is_one(&self) -> bool {
        self.primary.is_one()
    }

    fn approx_eq(&self, other: &Self, epsilon: f64) -> bool {
        self.primary.approx_eq(&other.primary, epsilon)
            && self.lex_alt_idx == other.lex_alt_idx
            && self.src_idx == other.src_idx
            && self.rule_idx == other.rule_idx
    }

    /// EP-P4 (Stage E) ESS: the PRIMARY tropical cost as an `f64`. This is
    /// the `-log`-probability path cost (LOWER = more likely; the path
    /// likelihood mass is `exp(-cost)`, exactly the `parse_with_confidence`
    /// semantics). `+inf` (the `zero()` additive identity = an unreachable
    /// path) maps to `Some(inf)`, which the ESS fold reads as likelihood
    /// mass `exp(-inf) = 0` (contributes nothing) — correct.
    #[inline]
    fn ess_primary_cost(&self) -> Option<f64> {
        Some(self.primary.value())
    }
}

impl Default for LexicographicWeight {
    fn default() -> Self {
        Self::one()
    }
}

impl fmt::Debug for LexicographicWeight {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "LexWeight(primary={:?}, lex_alt={}, src={}, rule={})",
            self.primary, self.lex_alt_idx, self.src_idx, self.rule_idx
        )
    }
}

impl fmt::Display for LexicographicWeight {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "({}, lex#{}, src#{}, rule#{})",
            self.primary.0, self.lex_alt_idx, self.src_idx, self.rule_idx
        )
    }
}

impl DetectableZero for LexicographicWeight {}
impl IdempotentSemiring for LexicographicWeight {}

/// Phase F.13 H12 Stage 1.5.3 (2026-05-21): tropical primary delta.
/// `pre.primary` and `post.primary` are `TropicalWeight(f64)`; tropical
/// `times` is `+`, so the inverse is `-`. Tiebreak fields are preserved
/// from `post` (algebraically irrelevant under cohort.pre's
/// left-projection at the consume site).
impl TropicalDeltaWeight for LexicographicWeight {
    #[inline]
    fn tropical_primary_delta(pre: &Self, post: &Self) -> Self {
        // Tropical (additive) subtraction, CLAMPED to non-negative.
        //
        // Negative deltas occur when the worker's cursor.weight was
        // reduced mid-sub-parse via merge_equivalent_cursors collapsing
        // it to a lex-min winner from a DIFFERENT cursor's path
        // (potentially a cursor that came through a CHEAPER pre-dispatch
        // history). Propagating that negative delta to a cohort revive
        // would give the cohort cursor an artificially-light weight
        // — letting it dominate downstream lex-min selections it
        // shouldn't.
        //
        // The clamp `(post - pre).max(0)` enforces a CONSERVATIVE
        // semantic: cohort cursors don't get merge-bonus discounts
        // they didn't earn. Mathematically this preserves the
        // per-packing distinction we want (different snapshots yield
        // different deltas via their post values) while preventing
        // cohort cursors from undercutting their per-cursor baseline
        // weights.
        let delta_primary = (post.primary.0 - pre.primary.0).max(0.0);
        LexicographicWeight {
            primary: TropicalWeight(delta_primary),
            lex_alt_idx: post.lex_alt_idx,
            src_idx: post.src_idx,
            rule_idx: post.rule_idx,
        }
    }
}

/// Phase F.13 Stage 2.0 (2026-05-22): LexicographicWeight has
/// inherent lex-Fork provenance from `from_cost_with_lex`. Expose
/// the three discriminator fields for inclusion in `ConfigKey`.
impl LexProvenance for LexicographicWeight {
    #[inline]
    fn lex_alt_idx(&self) -> u16 {
        self.lex_alt_idx
    }
    #[inline]
    fn lex_src_idx(&self) -> u16 {
        self.src_idx
    }
    #[inline]
    fn lex_rule_idx(&self) -> u16 {
        self.rule_idx
    }
}
impl CompleteSemiring for LexicographicWeight {}

/// Phase C-bis (2026-05-17, per
/// `docs/design/plans/closed-semiring-cycle-handling.md` §8): Kleene
/// star for the production walker weight type.
///
/// **Mathematical content**: `a* = 1 ⊕ a ⊕ a² ⊕ ...`. Under
/// `LexicographicWeight`'s tropical / lex-min `⊕`, this geometric
/// sum collapses (since `⊕` is idempotent: `a ⊕ a = a`). Concretely:
///
/// - If `self` is the multiplicative identity (`one_ref()`): `a* = 1 ⊕ 1
///   ⊕ ... = 1` (idempotent).
/// - If `self.primary > 0`: under tropical `min`, `min(1, a, 2a, ...) = 1`
///   (because `2a ≥ a ≥ 1 = 0` for primary ≥ 0).
/// - If `self.primary < 0`: under tropical `min`, the geometric sum
///   diverges to `-∞` — but `LexicographicWeight` represents weights
///   with finite `f64` primary, so this case is structurally absent
///   under PraTTaIL's WPDA usage.
///
/// In all practically-reachable cases for cyclic SPPF realize,
/// `LexicographicWeight::star(self) = Self::one()`. This matches the
/// existing cycle-skip behavior at `wpda_walker.rs:3348`, which under
/// idempotency is equivalent to "include the cyclic packing exactly
/// once with multiplier 1."
///
/// **Lex tiebreak**: returns the canonical `one_ref()` (lex_alt_idx
/// = 0, src_idx = 0, rule_idx = 0). The cycle-aggregated weight has
/// no specific "winning" alt/src/rule (it represents the closed sum,
/// not a particular path), so the identity-element tiebreak is the
/// correct semantic.
impl StarSemiring for LexicographicWeight {
    #[inline]
    fn star(&self) -> Self {
        Self::one()
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Tests
// ══════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    fn finite_weight() -> impl Strategy<Value = LexicographicWeight> {
        // Bounded ranges keep the algebra honest (no NaN, no overflow surprises).
        (0.0_f64..1000.0, 0u16..1000, 0u16..1000)
            .prop_map(|(c, s, r)| LexicographicWeight::from_cost(c, s, r))
    }

    fn nonidentity_finite_weight() -> impl Strategy<Value = LexicographicWeight> {
        // Bounds excluding zero primary; useful for tests that rely on
        // observing left-projection (without identity short-circuit kicking in).
        // Note: proptest shrinking may still produce values at the boundary,
        // so tests using this strategy should remain robust to identity-like inputs.
        (1.0_f64..1000.0, 0u16..1000, 0u16..1000)
            .prop_map(|(c, s, r)| LexicographicWeight::from_cost(c, s, r))
    }

    // ─── Hand-picked invariants ──────────────────────────────────────────────

    #[test]
    fn zero_and_one_are_distinct() {
        let z = LexicographicWeight::zero();
        let o = LexicographicWeight::one();
        assert!(z.is_zero());
        assert!(!z.is_one());
        assert!(o.is_one());
        assert!(!o.is_zero());
        assert_ne!(z, o);
    }

    #[test]
    fn identity_short_circuits_preserve_other_tiebreak() {
        // 1 ⊗ a = a — even though 1.src_idx = u16::MAX and a.src_idx = 5.
        let a = LexicographicWeight::from_cost(3.0, 5, 7);
        let one = LexicographicWeight::one();
        let left = one.times(&a);
        let right = a.times(&one);
        assert_eq!(left, a);
        assert_eq!(right, a);
        // Concretely: src_idx and rule_idx must NOT be u16::MAX after the product.
        assert_eq!(left.src_idx, 5);
        assert_eq!(left.rule_idx, 7);
    }

    #[test]
    fn left_projection_demonstration() {
        // Left always wins on tiebreak.
        let l = LexicographicWeight::from_cost(2.0, 3, 4);
        let r = LexicographicWeight::from_cost(5.0, 7, 8);
        let prod = l.times(&r);
        assert_eq!(prod.primary.0, 7.0); // 2 + 5
        assert_eq!(prod.src_idx, 3); // left's src_idx, NOT 7
        assert_eq!(prod.rule_idx, 4); // left's rule_idx, NOT 8
    }

    #[test]
    fn lex_min_selects_better_primary_first() {
        let lower_pri = LexicographicWeight::from_cost(1.0, 100, 100);
        let higher_pri = LexicographicWeight::from_cost(2.0, 0, 0);
        // Lower primary wins despite worse tiebreak.
        assert_eq!(lower_pri.plus(&higher_pri), lower_pri);
        assert_eq!(higher_pri.plus(&lower_pri), lower_pri);
    }

    #[test]
    fn lex_min_breaks_ties_with_src_idx() {
        let early_cat = LexicographicWeight::from_cost(5.0, 1, 100);
        let late_cat = LexicographicWeight::from_cost(5.0, 9, 0);
        // Same primary; earlier src_idx wins despite worse rule_idx.
        assert_eq!(early_cat.plus(&late_cat), early_cat);
        assert_eq!(late_cat.plus(&early_cat), early_cat);
    }

    #[test]
    fn lex_min_breaks_remaining_ties_with_rule_idx() {
        let early_rule = LexicographicWeight::from_cost(5.0, 3, 1);
        let late_rule = LexicographicWeight::from_cost(5.0, 3, 9);
        assert_eq!(early_rule.plus(&late_rule), early_rule);
        assert_eq!(late_rule.plus(&early_rule), early_rule);
    }

    #[test]
    fn lex_alt_idx_breaks_tie_above_src_idx() {
        // L1 (2026-04-28): lex_alt_idx beats src_idx in tiebreak ordering.
        // Same primary cost → lower lex_alt_idx wins, even if its src_idx
        // would otherwise lose. Lex disambiguation runs before parser dispatch.
        let lex_pref = LexicographicWeight::from_cost_with_lex(5.0, 9, 9, 0);
        let lex_alt = LexicographicWeight::from_cost_with_lex(5.0, 1, 1, 1);
        assert_eq!(lex_pref.plus(&lex_alt), lex_pref);
        assert_eq!(lex_alt.plus(&lex_pref), lex_pref);
    }

    #[test]
    fn lex_alt_idx_yields_to_lower_primary() {
        // Primary cost still dominates: a higher lex_alt_idx with a
        // strictly-better primary cost wins.
        let alt_with_better_cost = LexicographicWeight::from_cost_with_lex(2.0, 0, 0, 5);
        let pref_with_worse_cost = LexicographicWeight::from_cost_with_lex(3.0, 0, 0, 0);
        assert_eq!(alt_with_better_cost.plus(&pref_with_worse_cost), alt_with_better_cost,);
    }

    #[test]
    fn from_cost_defaults_lex_alt_to_zero() {
        // The 3-arg constructor sets lex_alt_idx to 0 (no lex ambiguity).
        // This preserves source compatibility for the many callers that
        // don't reason about lex alternatives.
        let w = LexicographicWeight::from_cost(1.0, 2, 3);
        assert_eq!(w.lex_alt_idx, 0);
    }

    #[test]
    fn zero_annihilates_under_times() {
        let z = LexicographicWeight::zero();
        let a = LexicographicWeight::from_cost(3.5, 2, 4);
        let za = z.times(&a);
        let az = a.times(&z);
        assert!(za.is_zero(), "0 ⊗ a should be zero, got {:?}", za);
        assert!(az.is_zero(), "a ⊗ 0 should be zero, got {:?}", az);
    }

    #[test]
    fn approx_eq_respects_tiebreak() {
        let a = LexicographicWeight::from_cost(1.0, 5, 7);
        let b = LexicographicWeight::from_cost(1.0 + 1e-9, 5, 7);
        let c = LexicographicWeight::from_cost(1.0, 5, 8);
        assert!(a.approx_eq(&b, 1e-6), "near-equal primary, same tiebreak");
        assert!(!a.approx_eq(&c, 1e-6), "differing rule_idx is never approx-equal");
    }

    // ─── Property-based axiom checks ─────────────────────────────────────────

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(256))]

        #[test]
        fn axiom_times_left_identity(a in finite_weight()) {
            let one = LexicographicWeight::one();
            prop_assert_eq!(one.times(&a), a);
        }

        #[test]
        fn axiom_times_right_identity(a in finite_weight()) {
            let one = LexicographicWeight::one();
            prop_assert_eq!(a.times(&one), a);
        }

        #[test]
        fn axiom_zero_left_annihilates(a in finite_weight()) {
            let z = LexicographicWeight::zero();
            prop_assert!(z.times(&a).is_zero());
        }

        #[test]
        fn axiom_zero_right_annihilates(a in finite_weight()) {
            let z = LexicographicWeight::zero();
            prop_assert!(a.times(&z).is_zero());
        }

        #[test]
        fn axiom_plus_commutative(a in finite_weight(), b in finite_weight()) {
            // Lex-min is commutative on values: same lex-smaller weight returned.
            prop_assert_eq!(a.plus(&b), b.plus(&a));
        }

        #[test]
        fn axiom_plus_associative(
            a in finite_weight(),
            b in finite_weight(),
            c in finite_weight(),
        ) {
            let lhs = a.plus(&b).plus(&c);
            let rhs = a.plus(&b.plus(&c));
            prop_assert_eq!(lhs, rhs);
        }

        #[test]
        fn axiom_plus_idempotent(a in finite_weight()) {
            // Idempotent semiring: a ⊕ a = a.
            prop_assert_eq!(a.plus(&a), a);
        }

        #[test]
        fn axiom_times_associative_approx(
            a in finite_weight(),
            b in finite_weight(),
            c in finite_weight(),
        ) {
            // Approximate associativity: holds up to ε due to f64 rounding in
            // tropical addition. See module docs §5 for justification.
            let lhs = a.times(&b).times(&c);
            let rhs = a.times(&b.times(&c));
            prop_assert!(
                lhs.approx_eq(&rhs, 1e-6),
                "associativity (mod fp ε=1e-6): lhs = {:?}, rhs = {:?}",
                lhs,
                rhs,
            );
        }

        #[test]
        fn axiom_times_left_projection_when_a_nonidentity(
            a in nonidentity_finite_weight(),
            b in nonidentity_finite_weight(),
            c in nonidentity_finite_weight(),
        ) {
            // When a is non-identity, left-projection guarantees the tiebreak
            // always inherits from a regardless of association.
            let lhs = a.times(&b).times(&c);
            let rhs = a.times(&b.times(&c));
            prop_assert_eq!(lhs.src_idx, a.src_idx);
            prop_assert_eq!(rhs.src_idx, a.src_idx);
            prop_assert_eq!(lhs.rule_idx, a.rule_idx);
            prop_assert_eq!(rhs.rule_idx, a.rule_idx);
        }

        #[test]
        fn axiom_distributivity_left(
            a in finite_weight(),
            b in finite_weight(),
            c in finite_weight(),
        ) {
            // a ⊗ (b ⊕ c) = (a ⊗ b) ⊕ (a ⊗ c)
            let lhs = a.times(&b.plus(&c));
            let rhs = a.times(&b).plus(&a.times(&c));
            prop_assert_eq!(lhs, rhs);
        }

        #[test]
        fn axiom_distributivity_right(
            a in finite_weight(),
            b in finite_weight(),
            c in finite_weight(),
        ) {
            // (a ⊕ b) ⊗ c = (a ⊗ c) ⊕ (b ⊗ c)
            let lhs = a.plus(&b).times(&c);
            let rhs = a.times(&c).plus(&b.times(&c));
            prop_assert_eq!(lhs, rhs);
        }

        #[test]
        fn lex_cmp_is_total_order(a in finite_weight(), b in finite_weight()) {
            // Either a ≤ b or b ≤ a (totality).
            let ab = a.lex_cmp(&b);
            let ba = b.lex_cmp(&a);
            prop_assert_eq!(ab, ba.reverse());
        }

        // Phase F.13 H12 Stage 1.5.3b (2026-05-21): TropicalDeltaWeight
        // axioms.

        /// `delta(pre, post)` should reconstruct `post.primary` when
        /// `pre` is added back (tropical primary recovery).
        #[test]
        fn axiom_tropical_delta_recovers_primary(
            pre in nonidentity_finite_weight(),
            post in nonidentity_finite_weight(),
        ) {
            // Constrain post.primary >= pre.primary to satisfy the
            // monotonicity debug_assert in tropical_primary_delta.
            let pre_c = pre.primary.0.min(post.primary.0);
            let post_c = pre.primary.0.max(post.primary.0);
            let pre2 = LexicographicWeight::from_cost(pre_c, pre.src_idx, pre.rule_idx);
            let post2 = LexicographicWeight::from_cost(post_c, post.src_idx, post.rule_idx);
            let delta = LexicographicWeight::tropical_primary_delta(&pre2, &post2);
            // Recovery: pre.primary + delta.primary = post.primary.
            let recovered = pre2.primary.0 + delta.primary.0;
            prop_assert!((recovered - post2.primary.0).abs() < 1e-9);
        }

        /// For non-identity cohort.pre, cohort.pre.times(&delta) carries
        /// cohort.pre's tiebreak (left-projection).
        #[test]
        fn axiom_cohort_revive_preserves_cohort_tiebreak(
            cohort_pre in nonidentity_finite_weight(),
            pre in nonidentity_finite_weight(),
            post in nonidentity_finite_weight(),
        ) {
            // Ensure post.primary >= pre.primary.
            let pre_c = pre.primary.0.min(post.primary.0);
            let post_c = pre.primary.0.max(post.primary.0);
            let pre2 = LexicographicWeight::from_cost(pre_c, pre.src_idx, pre.rule_idx);
            let post2 = LexicographicWeight::from_cost(post_c, post.src_idx, post.rule_idx);
            let delta = LexicographicWeight::tropical_primary_delta(&pre2, &post2);
            let revive = cohort_pre.times(&delta);
            // cohort_pre is non-identity → left-projection preserves its tiebreak.
            prop_assert_eq!(revive.src_idx, cohort_pre.src_idx);
            prop_assert_eq!(revive.rule_idx, cohort_pre.rule_idx);
            // Primary: cohort_pre.primary + delta.primary (which = post.primary - pre.primary).
            let expected = cohort_pre.primary.0 + (post2.primary.0 - pre2.primary.0);
            prop_assert!((revive.primary.0 - expected).abs() < 1e-9);
        }
    }

    // Phase F.13 H12 Stage 1.5.3b: hand-picked semantic test.
    #[test]
    fn delta_recovers_per_packing_weight() {
        // Synthetic scenario: a cohort member with (primary 0.5, src 3, rule 7)
        // arrives at a dispatch with two workers (Branch A, Branch B). Worker
        // pre-dispatch weight = (primary 0.1, src 9, rule 11). Worker post-pop
        // weights differ by path (Branch A: +0.2, Branch B: +0.3).
        let cohort_pre = LexicographicWeight::from_cost(0.5, 3, 7);
        let worker_pre = LexicographicWeight::from_cost(0.1, 9, 11);
        let worker_post_a = LexicographicWeight::from_cost(0.3, 9, 11);
        let worker_post_b = LexicographicWeight::from_cost(0.4, 9, 11);

        let delta_a = LexicographicWeight::tropical_primary_delta(&worker_pre, &worker_post_a);
        let delta_b = LexicographicWeight::tropical_primary_delta(&worker_pre, &worker_post_b);

        // Delta primaries: tropical subtraction.
        assert!((delta_a.primary.0 - 0.2).abs() < 1e-9);
        assert!((delta_b.primary.0 - 0.3).abs() < 1e-9);

        let revive_a = cohort_pre.times(&delta_a);
        let revive_b = cohort_pre.times(&delta_b);

        // Per-cursor baseline equivalence: cohort_pre.primary + delta.primary.
        assert!((revive_a.primary.0 - 0.7).abs() < 1e-9);
        assert!((revive_b.primary.0 - 0.8).abs() < 1e-9);

        // Left-projection: cohort_pre's tiebreak preserved.
        assert_eq!(revive_a.src_idx, 3);
        assert_eq!(revive_a.rule_idx, 7);
        assert_eq!(revive_b.src_idx, 3);
        assert_eq!(revive_b.rule_idx, 7);

        // Per-packing distinction restored: revive_a ≠ revive_b.
        assert_ne!(revive_a.primary.0, revive_b.primary.0);
    }
}
