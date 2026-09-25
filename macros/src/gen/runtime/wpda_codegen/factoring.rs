//! S1-FACTORING Stage F0 — generic FGLL-style shared-prefix factoring of the
//! PrefixDispatch fan: eligibility, trie build, spine-pos → member-pos maps
//! (2026-07-11).
//!
//! Plan of record: `scratchpad/zz_probes/s1_factoring_plan.md` (§0-§5 plus the
//! RED-TEAM VERDICTS with amendments A1-A10). Literature anchor: Scott &
//! Johnstone, *Structuring the GLL parsing algorithm for performance*, SCP 125
//! (2016) — the FGLL shared-prefix factoring this module ports to the
//! unified-bucket WPDA emission.
//!
//! ## What this module IS in F0
//!
//! A PURE data-structure computation over the SAME classifier outputs the
//! unified-bucket emission in [`super::prefix::emit_prefix_arms_for_category`]
//! consumes (`classify_binder_in` / `classify_atomic`). It is exercised only
//! by the unit tests below and by the grammar-generality INV-8 prefix-surface
//! no-loss invariant (`super::grammar_generality_prop`, amendment A5). NOTHING
//! in the emission path consults it while [`super::forks::S1_FACTORING`] is
//! `false`: the generated `target/generated/<lang>/wpda.rs` stays
//! BYTE-IDENTICAL (the F0 gate; receipts in
//! `scratchpad/zz_probes/logs_s1f0/`). F1 wires [`emission_partition`] into
//! the `prefix.rs` unified-bucket Fork emission, the `binder.rs` BinderRule
//! key space, and the lex-alt surface (`kind_dispatch.rs` +
//! `forks.rs::emit_lex_fork_at_prefix_dispatch`).
//!
//! ## The fan being factored (plan §0, receipts)
//!
//! At `WpdaState::PrefixDispatch` on `@` in Rholang `Proc`, the generated
//! engine emits ONE Fork with 16 branches — 1 CrossCatLhs + 15 rule branches
//! (rules 10-24), each pushing its own `rule_at(0, r, 1)` and mirroring the
//! SAME `@` token into the SPPF 15 times under 15 distinct TriggerTerminal
//! owners; all six Short-group rules then emit the byte-identical pos-1
//! `ReplaceAndPush { CategoryEntry(0), cur_bp: 0 }` — six duplicate inner-Proc
//! sub-parses per span, at every nesting level. The factored shape (plan §2)
//! replaces the 15 per-rule branches with one spine branch per GROUP (3 for
//! the `@`-cohort), committing to the member rule at trie divergence leaves.
//!
//! ## Group / trie construction (plan §2, amended)
//!
//! Per `(category_src_idx, leading_literal)` bucket, the BinderPrefix and
//! NullaryLiteralRun descriptor members are partitioned into GROUPS by their
//! first post-trigger item's EMITTED-ACTION SHAPE. Red-team AV2 gap (a): the
//! item alphabet comes from TWO classifier sources —
//! `BinderShape.positions` for binder members and the
//! `mixfix_nullary_literals` trailing-literal list
//! (`AtomicShape::NullaryLiteralRun::trailing_literals`) for nullary members
//! such as Rholang rules 15/16, whose whole tail is literals. Item equality:
//!
//!   - [`SpineItem::Literal`] — exact text plus the derived
//!     `required_top_cat` guard payload (equal by induction along a shared
//!     spine; carried in the key as defense against emission drift);
//!   - [`SpineItem::ParamParse`] — equal iff `(pushed category, cur_bp,
//!     collection = None)` equal, where `cur_bp` is the SAME
//!     `build_prefix_bp_map` lookup the `emit_binder_rule_body` ParamParse
//!     arm emits. Red-team AV2: the `prefix(220)` spec annotation does NOT
//!     surface here — `build_prefix_bp_map` only maps
//!     `classify_unary_prefix_shape` rules, so the six Rholang Short-group
//!     pos-1 arms are byte-equal with `cur_bp: 0` (pinned below).
//!
//! Any collection / binder-list / optional-group / guard item TERMINATES
//! mergeability (leaf-side only, plan §2): it never forms a shared spine
//! edge; the member must commit at or before that depth and run its
//! remainder in its own per-rule machinery.
//!
//! ## Eligibility (plan §2/§5 F0, amendments A2/A4/A9)
//!
//!   - Members: BinderPrefix / NullaryLiteralRun descriptors ONLY, mirrored
//!     from the `prefix.rs` bucket-insertion chain (CrossCatPrefixUnary /
//!     CrossCatProjection shapes and `"("`-triggered binders never
//!     participate).
//!   - ★A2 (the red-team blocking hole): rules participating in the cast
//!     machinery are EXCLUDED as singletons — see
//!     [`crate::gen::runtime::numeric_cast_adapter::cast_machinery_participates`]
//!     for the row definition (same source data as the walker-consulted
//!     tables) and the deliberate boundary (same-category sends such as
//!     Rholang `POutputNil` and non-numeric wrappers such as
//!     `POutputQuotedEmpty` stay groupable — the pinned `@`-cohort trie
//!     depends on it).
//!   - Proper-prefix members (interior accept-nodes, e.g. Rholang
//!     `InputBindQuoted` inside the `@`-led query row): stance-gated by
//!     [`super::forks::S1F5_ACCEPT_CONTINUE`] (F5-1, plan
//!     `f5_accept_continue_plan.md`). With the const `false` they are
//!     recorded on the ineligible group and the whole group falls back to
//!     unfactored emission (the F0 stance, byte-identical); with the const
//!     `true` the exhausted member becomes an ordinary SIBLING LEAF sharing
//!     its edge item with the continuation subtree (see [`build_tree`] — the
//!     sibling-leaf form; the ε-branch reading is refuted, plan §9-FS1) and
//!     the group proceeds to ordinary eligibility. Either way every leaf of
//!     an ELIGIBLE group carries exactly one rule (asserted).
//!   - `body_src_idx` uniformity across a group's binder members is an
//!     eligibility assert (red-team AV2 gap b): the spine's single
//!     `BinderRule { body_src_idx }` state must be well-defined.
//!   - ★A9: `SPINE_RULE_BASE + n_groups` must stay below
//!     [`super::forks::RECOVERY_BASE`] AND `u16::MAX` (asserted at
//!     allocation).
//!
//! ## Commit coordinates (amendment A4 — TYPED per member kind)
//!
//! Red-team AV1: the `@`-cohort mixes TWO state machines — binder members
//! run `rule_at`/`BinderRule` markers while nullary members (rules 15/16)
//! push `mixfix_marker` + `MixfixLiteralRun { kind: 2 }` — so commit
//! coordinates are typed, never conflated:
//!
//!   - Binder members commit as `rule_at(cat, member_rule, resume_pos)` with
//!     `resume_pos = leaf_depth + 1` (1-based BinderRule position after
//!     consuming the leaf edge; equals the existing `positions.len() + 1`
//!     final-pos Pop → fire arm when the leaf edge is the member's last
//!     item).
//!   - Nullary members commit into their EXISTING `MixfixLiteralRun{kind:2}`
//!     tail at `(completed_idx = 0, sub_pos = leaf_depth)` against the
//!     `mixfix_nullary_literals` indexing (a leaf at the last trailing
//!     literal yields `sub_pos == parts_len` — the tail-complete
//!     pop-and-fire arm).

#[cfg(test)]
use std::collections::BTreeSet;

use mettail_ast::grammar::{GrammarRule, SyntaxExpr};
use mettail_ast::language::LanguageDef;

#[cfg(test)]
use super::binder::BinderPosition;
use super::binder::{build_prefix_bp_map, classify_binder_in};
use super::prefix::{classify_atomic, AtomicShape};

// ═══════════════════════════════════════════════════════════════════════════
// Item model — the EMITTED-ACTION-SHAPE alphabet (plan §2 merge criterion).
// ═══════════════════════════════════════════════════════════════════════════

#[cfg(test)]
pub(crate) use mettail_prattail::wpda_rule_analysis::factoring::{
    binder_items, finalize_leaf, FactoringBucket, GroupMember, MemberKind, SpinePosMap,
    SPINE_RULE_BASE,
};
#[cfg(any(test, doc))]
pub(crate) use mettail_prattail::wpda_rule_analysis::factoring::{
    build_tree, IneligibleReason, SingletonReason,
};
pub(crate) use mettail_prattail::wpda_rule_analysis::factoring::{
    flatten_forest, mixfix_spine_arm_coords, CandidateMember, CategoryFactoring, MemberCommit,
    SpineItem, SpineTree, LIMIT_REFUSAL,
};

#[cfg(test)]
#[path = "../../../../tests/support/spine_tree_lifecycle.rs"]
mod spine_tree_lifecycle_tests;

#[cfg(test)]
#[path = "../../../../tests/support/prefix_member_descriptor_baselines.rs"]
mod prefix_member_descriptor_baselines;

#[cfg(test)]
#[path = "../../../../tests/support/prefix_discovery_baselines.rs"]
mod prefix_discovery_baselines;

#[cfg(test)]
#[path = "../../../../tests/support/mixfix_descriptor_baselines.rs"]
mod mixfix_descriptor_baselines;

// ═══════════════════════════════════════════════════════════════════════════
// Member discovery — mirrors the `prefix.rs` unified-bucket insertion
// conditions exactly (BinderPrefix / NullaryLiteralRun only).
// ═══════════════════════════════════════════════════════════════════════════

/// Discover the bucket members of one category, in rule order, mirroring the
/// `prefix.rs` unified-bucket insertion chain (`classify_atomic` shape gates
/// first — CrossCatPrefixUnary / CrossCatProjection never participate, a
/// NullaryLiteralRun inserts the nullary member — then `classify_binder_in`
/// with the leading-`Literal`, non-`"("` trigger guard).
fn discover_members(
    language: &LanguageDef,
    categories: &[String],
    category_src_idx: u16,
    rules: &[GrammarRule],
    prefix_bp_map: &std::collections::HashMap<(u16, u16), u8>,
) -> Vec<(String, CandidateMember)> {
    use mettail_prattail::wpda_rule_analysis::factoring::PrefixAtomicObservation;
    mettail_prattail::wpda_rule_analysis::factoring::discover_prefix_members_with(
        categories,
        category_src_idx,
        rules,
        prefix_bp_map,
        |rule| match classify_atomic(rule, language) {
            AtomicShape::CrossCatPrefixUnary { .. } => PrefixAtomicObservation::CrossCatPrefixUnary,
            AtomicShape::NullaryLiteralRun { trigger, trailing_literals, .. } => {
                PrefixAtomicObservation::NullaryLiteralRun { trigger, trailing_literals }
            },
            AtomicShape::CrossCatProjection { .. } => PrefixAtomicObservation::CrossCatProjection,
            _ => PrefixAtomicObservation::Other,
        },
        |rule| classify_binder_in(rule, language),
        |rule| match rule.syntax_pattern.as_ref().and_then(|sp| sp.first()) {
            Some(SyntaxExpr::Literal(trigger)) => Some(trigger.as_str()),
            _ => None,
        },
    )
}

#[cfg(test)]
#[path = "../../../../tests/support/factoring_tree_recursive_oracle.rs"]
mod factoring_tree_recursive_oracle;

// ═══════════════════════════════════════════════════════════════════════════
// The factoring computation.
// ═══════════════════════════════════════════════════════════════════════════

/// Build the full prefix-factoring model for every category: buckets, groups
/// (spine forests, SPINE_IDs, typed commit maps), ineligible groups, and
/// singletons. PURE — consumes the same classifier outputs as the emission
/// and produces no tokens. `per_cat` must be the SAME
/// `synthetic::build_per_category_rules` product the emission uses so
/// `rule_idx` values agree. Proper-prefix admission follows
/// [`super::forks::S1F5_ACCEPT_CONTINUE`]; use
/// [`build_prefix_factoring_with`] to pin a stance explicitly.
pub(crate) fn build_prefix_factoring(
    language: &LanguageDef,
    categories: &[String],
    per_cat: &[Vec<GrammarRule>],
) -> Vec<CategoryFactoring> {
    build_prefix_factoring_with(language, categories, per_cat, super::forks::S1F5_ACCEPT_CONTINUE)
}

/// The `accept_continue`-explicit core of [`build_prefix_factoring`] (the F1
/// `build_spine_emission_from` precedent): tests pin BOTH F5-1 stances
/// without const flips. `accept_continue == false` reproduces the F0 model
/// byte-identically (exhausted members defer their group via
/// `IneligibleReason::InteriorAccept`); `accept_continue == true` admits
/// them as sibling accept leaves (see [`build_tree`]).
pub(crate) fn build_prefix_factoring_with(
    language: &LanguageDef,
    categories: &[String],
    per_cat: &[Vec<GrammarRule>],
    accept_continue: bool,
) -> Vec<CategoryFactoring> {
    let prefix_bp_map = build_prefix_bp_map(language, per_cat);
    mettail_prattail::wpda_rule_analysis::factoring::build_prefix_factoring_with(
        per_cat,
        accept_continue,
        super::forks::RECOVERY_BASE,
        |category_src_idx, rules| {
            discover_members(language, categories, category_src_idx, rules, &prefix_bp_map)
        },
        |rule| {
            crate::gen::runtime::numeric_cast_adapter::cast_machinery_participates(language, rule)
        },
    )
}

/// The EMISSION-EFFECTIVE partition (the F1 integration point — NOT consulted
/// by any emitter in F0). With [`super::forks::S1_FACTORING`] `false` it
/// degenerates to the identity partition: every bucket member its own
/// [`SingletonReason::FactoringDisabled`] singleton, zero groups — the shape
/// whose emission is byte-identical to today's per-rule arms. With the const
/// `true` it is [`build_prefix_factoring`].
pub(crate) fn emission_partition(
    language: &LanguageDef,
    categories: &[String],
    per_cat: &[Vec<GrammarRule>],
) -> Vec<CategoryFactoring> {
    if super::forks::S1_FACTORING {
        return build_prefix_factoring(language, categories, per_cat);
    }
    let prefix_bp_map = build_prefix_bp_map(language, per_cat);
    mettail_prattail::wpda_rule_analysis::factoring::prefix_identity_partition(
        per_cat,
        |category_src_idx, rules| {
            discover_members(language, categories, category_src_idx, rules, &prefix_bp_map)
        },
    )
}

/// Test-only explicit switch over the same static discovery callback.
#[cfg(test)]
pub(crate) fn original_prefix_partition_for_test(
    language: &LanguageDef,
    categories: &[String],
    per_cat: &[Vec<GrammarRule>],
    enabled: bool,
) -> Vec<CategoryFactoring> {
    if enabled {
        return build_prefix_factoring(language, categories, per_cat);
    }
    let prefix_bp_map = build_prefix_bp_map(language, per_cat);
    mettail_prattail::wpda_rule_analysis::factoring::prefix_identity_partition(
        per_cat,
        |category, rules| discover_members(language, categories, category, rules, &prefix_bp_map),
    )
}

// ═══════════════════════════════════════════════════════════════════════════
// F5-2 — MIXFIX SEND COHORTS: the SECOND factoring surface (plan
// `scratchpad/zz_probes/f5_mixfix_cohorts_plan.md` + its §RED-TEAM
// GO-WITH-AMENDMENTS A-M1..A-M5, 2026-07-13).
//
// The InfixLoop mixfix fan (engine_impl.rs `__mixfix_slice` loop) forks one
// `mixfix_marker` + `MixfixLiteralRun{kind:2}` branch per slice member; the
// bundled census has exactly TWO factorable cohorts — rholang Name `!`
// {4,6,8} and `!!` {5,7,9} (isomorphic tries: divergences at depths 1 and 2,
// rule 8/9 truncated at its rep, NO interior accepts). Discovery mirrors the
// `mixfix_bp_<cat>` slice construction EXACTLY (same
// `group_ops_by_cat_terminal` grouping, same `GEN1_MAX_SLICE` truncation ⇒
// cohort membership == emitted slice); the trie build REUSES [`build_tree`]
// (same `SpineItem` alphabet, operands as `ParamParse{cat, 0}` — the mixfix
// machine always dispatches operands at `cur_bp: 0`) with
// `accept_continue == false` ALWAYS: a future interior-accept mixfix group
// routes to [`IneligibleReason::InteriorAccept`], whole-group-unfactored (the
// coordinator-mandated exhaustion-at-interior check; the sibling-leaf F5-1
// mechanism would need the typed mixfix commits this module defines).
//
// Eligibility (D-1/D-5 + A-M5), all recorded per-cohort for INV-8-mixfix:
//   - whole-slice coverage (D-5): one root part covering the ENTIRE slice;
//   - uniform `result_src_idx` (goal gate / marker category / fire output);
//   - cast-machinery exclusion mirrored from F0 (vacuous today);
//   - operand-absorbability guard (A-M5 mitigant-(a)): post-operand literal
//     items must not be operator triggers of the operand's category;
//   - single shared operand (spine re-entry key uniqueness).
//
// SPINE COORDINATES: the spine's own arms are keyed by the same
// `(kind, completed_idx, sub_pos)` walk the generic machine performs over
// the SHARED item prefix (kind-2 literal chain → operand → `(0, 0, j)`
// post-operand chain); commits carry the member-side coordinate recorded at
// discovery ([`MemberCommit::MixfixRun`]). The fan pushes
// `MixfixLiteralRun{spine, kind: 2, completed: 0, sub_pos: 0}` and the
// post-operand re-entry rides the UNCHANGED Unwinding-MixfixMarker arm (it
// needs only the `mixfix_parts_len` presence poison row,
// [`mixfix_spine_parts_len_rows`]).
// ═══════════════════════════════════════════════════════════════════════════

#[cfg(test)]
use mettail_prattail::wpda_rule_analysis::mixfix::MixfixBucket;
pub(crate) use mettail_prattail::wpda_rule_analysis::mixfix::{MixfixFactoring, MixfixGroup};

#[cfg(test)]
fn mixfix_member_items(
    op: &mettail_prattail::binding_power::InfixOperator,
    categories: &[String],
) -> (Vec<SpineItem>, Vec<(u8, u8, u8)>, bool) {
    mettail_prattail::wpda_rule_analysis::mixfix::mixfix_member_items_with(
        op,
        categories,
        &mut super::binder::resolve_cat_idx,
    )
}

/// The always-computable mixfix cohort model. `prefix_partition` supplies
/// the per-RESULT-category prefix group counts so mixfix spine ids CONTINUE
/// each category's ordinal (Proc: prefix `@`-cohort groups 0xF800-0xF802 ⇒
/// `!` = 0xF803, `!!` = 0xF804). PURE — consumes the SAME
/// `group_ops_by_cat_terminal` grouping the `mixfix_bp_<cat>` /
/// `lex_alt_rules_for_infix` emitters consume (NO-LOSS by construction).
pub(crate) fn build_mixfix_factoring(
    language: &LanguageDef,
    categories: &[String],
    per_cat: &[Vec<GrammarRule>],
    prefix_partition: &[CategoryFactoring],
) -> Vec<MixfixFactoring> {
    let bp_table = super::infix::build_bp_table(language);
    let label_index = super::infix::build_label_index(categories, per_cat);
    let grouped = super::infix::group_ops_by_cat_terminal(&bp_table, categories, &label_index);
    mettail_prattail::wpda_rule_analysis::mixfix::build_mixfix_factoring_with(
        categories,
        per_cat,
        prefix_partition,
        &grouped,
        super::infix::GEN1_MAX_SLICE,
        super::forks::RECOVERY_BASE,
        super::binder::resolve_cat_idx,
        |rule| {
            crate::gen::runtime::numeric_cast_adapter::cast_machinery_participates(language, rule)
        },
    )
}

/// The EMISSION-EFFECTIVE mixfix partition (the F5-2 integration point).
/// With [`super::forks::S1_FACTORING`] `&&`
/// [`super::forks::S1F5_MIXFIX_COHORTS`] it is [`build_mixfix_factoring`]
/// over the const-following prefix partition; otherwise the identity: every
/// slice member its own `FactoringDisabled` singleton, zero groups — the
/// shape whose emission is byte-identical to today's per-member fan.
pub(crate) fn mixfix_emission_partition(
    language: &LanguageDef,
    categories: &[String],
    per_cat: &[Vec<GrammarRule>],
) -> Vec<MixfixFactoring> {
    if super::forks::S1_FACTORING && super::forks::S1F5_MIXFIX_COHORTS {
        let prefix = build_prefix_factoring(language, categories, per_cat);
        return build_mixfix_factoring(language, categories, per_cat, &prefix);
    }
    mixfix_identity_partition(language, categories, per_cat)
}

/// The identity mixfix partition: the same cohort census (slice membership),
/// zero groups, every member a `FactoringDisabled` singleton — the INV-8
/// OFF-branch shape.
pub(crate) fn mixfix_identity_partition(
    language: &LanguageDef,
    categories: &[String],
    per_cat: &[Vec<GrammarRule>],
) -> Vec<MixfixFactoring> {
    let bp_table = super::infix::build_bp_table(language);
    let label_index = super::infix::build_label_index(categories, per_cat);
    let grouped = super::infix::group_ops_by_cat_terminal(&bp_table, categories, &label_index);
    mettail_prattail::wpda_rule_analysis::mixfix::mixfix_identity_partition(
        &grouped,
        super::infix::GEN1_MAX_SLICE,
    )
}

/// The `mixfix_parts_len` SPINE presence rows `(result_src, spine_id)` —
/// consumed by `infix::emit_mixfix_parts_fn` (the Unwinding-MixfixMarker arm
/// validates `Some(..)` then DISCARDS the value, so the `u8::MAX` poison is
/// inert there and an escaped spine id dies LOUDLY at every other
/// `parts_len` consumer). Empty while the consts are off (byte-identity).
/// Recomputed from the pure const-gated model — deterministic, so this
/// agrees with the `build_spine_emission` bundle without threading.
pub(crate) fn mixfix_spine_parts_len_rows(
    language: &LanguageDef,
    categories: &[String],
    per_cat: &[Vec<GrammarRule>],
) -> Vec<(u16, u16)> {
    let partition = mixfix_emission_partition(language, categories, per_cat);
    mettail_prattail::wpda_rule_analysis::mixfix::mixfix_spine_parts_len_rows(&partition)
}

// ═══════════════════════════════════════════════════════════════════════════
// Tests — the F0 gate's rholang trie pins (real grammar, real indices),
// the A2 exclusion receipts, and the synthetic eligibility witnesses.
// ═══════════════════════════════════════════════════════════════════════════

// ═══════════════════════════════════════════════════════════════════════════
// F1 — EMISSION (plan §D F1 + delta amendments A-1/A-3/A-4/A-5).
//
// Everything below is a PURE token producer over `emission_partition`: with
// `S1_FACTORING = false` the partition has zero groups, every stream/map here
// is empty, and every consumer emits byte-identically to the pre-F1 output
// (the F0 receipt discipline). With the const `true`, prefix.rs's
// multi-branch fork emits ONE spine ConsumeAndPush branch per eligible group
// (weight identity = (cat, MIN member rule) per AV5 — the trigger stamp joins
// lex plus()-elections, so a SPINE_ID stamp would flip lattice elections),
// binder.rs's BinderRule match gains `(cat, SPINE_ID, node_pos)` arms, the
// lex-alt surface emits GROUP entries (A3 — otherwise the lex-fork path
// re-creates the per-rule fan), and the engine tables gain the spine rows.
//
// SPINE ARM COORDINATES: the marker-position field of the spine arms is a
// PREORDER NODE ID over the group's forest (pre-root = 1, interior roots
// from 2 — see `flatten_forest`), NOT the literal depth — sibling subtrees
// at equal depth need distinct arm keys (the Nil-group's `!` and `!!`
// subtrees both continue at depth 3 with different member sets). Nothing
// else interprets spine positions; the member-side translation happens at
// commit via the A4 typed coordinates.
// ═══════════════════════════════════════════════════════════════════════════

use std::collections::HashMap;

use proc_macro2::TokenStream;
use quote::quote;

use super::binder::ActionArgKind;

pub(crate) use mettail_prattail::wpda_rule_analysis::factoring::emission::{
    MixfixGroupEmission, SpineDisposition, SpineLexAlt,
};

/// The complete F1 emission bundle.
pub(crate) struct SpineEmission {
    /// `rule_idx -> disposition` per category index.
    pub dispositions: Vec<HashMap<u16, SpineDisposition>>,
    /// Task #10 item 1: `GroupFirst member rule_idx -> ORDERED member rule
    /// idxs` per category index (built from the SAME `ordered` list the
    /// disposition loop walks, so it can never diverge from the emission).
    /// Consumed by the fork-emission ordinal derivation: a `GroupFirst`
    /// descriptor at static declaration position `i` yields one site-2 row
    /// per MEMBER at ordinal `i` (the spine trigger branch is every
    /// member's initiating branch); `GroupRest` descriptors yield nothing
    /// (their rows were derived at their group's `GroupFirst`).
    pub group_members: Vec<HashMap<u16, Vec<u16>>>,
    /// `(cat, SPINE_ID, node_pos)` arms for `emit_binder_rule_body`'s match.
    pub binder_arms: TokenStream,
    /// `fn trigger_spine_owner` override for the generated engine impl
    /// (EMPTY stream when no groups ⇒ the prattail trait default `None`
    /// stands and the generated file is byte-identical).
    pub trigger_spine_owner_fn: TokenStream,
    /// `fn spine_members` override (A-1); EMPTY when no groups.
    pub spine_members_fn: TokenStream,
    /// Early-return prelude arms for `action_for` (H9: expected_input_cats =
    /// member union, arity = the u8::MAX poison; the LOUD asserts live at
    /// the walker consumption sites).
    pub action_for_prelude: TokenStream,
    /// Early-return prelude for `rule_has_leading_structural_trigger` (A7:
    /// conjunction over members — vacuously all-true under F0 eligibility,
    /// every member leads with the bucket trigger literal; emitted
    /// regardless per the A7 consumer census, which includes the classic B2
    /// shape mask @20495, `sppf_shallow_ident_trigger_masked` @20444, the
    /// stats-only `cgll_w_cond` @34598, and the dormant `step_canonical`
    /// variant).
    pub leading_trigger_prelude: TokenStream,
    /// Early-return prelude for `min_terminal_span` (min over members;
    /// omitted when the min is 0 = the table default). Parikh needs NO rows:
    /// `WPDA_MUST_MASK`'s default arm is 0 (all-zero spine rows = the plan's
    /// sound initial choice = the default).
    pub min_span_prelude: TokenStream,
    /// A3 lex-alt adjustments per category index.
    // dead_code: model field read only by the `#[cfg(test)]` assertions.
    #[cfg_attr(not(test), allow(dead_code))]
    pub lex_alt: Vec<SpineLexAlt>,
    /// ★ #141 G8 — the ENCODING-LIMIT refusals, as `compile_error!` items.
    ///
    /// EMPTY on every path where the factoring encodes, which is every shipped
    /// grammar (`cargo check -p languages --features all-languages,rho-codegen`
    /// is the measurement). It is spliced into the generated engine module
    /// beside `spine_weight_rule_fn`, so an unencodable factoring fails the
    /// build with a message naming the category and the ceiling it crossed
    /// instead of aborting `rustc` with no output at all.
    pub refusals: TokenStream,
    /// `fn __s1_spine_weight_rule(cat, rule) -> u16` free fn for the
    /// lex-fork weight stamps (identity for real ids; MIN member for spine
    /// ids — AV5). Emitted only when groups exist.
    pub spine_weight_rule_fn: TokenStream,
    /// F5-2: distilled per-group coordinates for the mixfix consumers
    /// (kind_dispatch's `lex_alt_rules_for_infix` group entries, the
    /// engine_impl loop-v2 gating, receipts). EMPTY while
    /// `S1_FACTORING && S1F5_MIXFIX_COHORTS` is not satisfied.
    pub mixfix_groups: Vec<MixfixGroupEmission>,
    /// F5-2: the loop-v2 group match arms spliced into the InfixLoop mixfix
    /// tier (`match (state_cat_src_idx, token_text) { <these arms> _ =>
    /// <verbatim per-member loop> }`). EMPTY when no mixfix groups.
    pub mixfix_fan_arms: TokenStream,
    /// F5-2: the spine prelude arms spliced at the TOP of the generic
    /// `MixfixLiteralRun` arm (`match (*result_src_idx, *rule_idx, *kind,
    /// *completed_idx, *sub_pos) { <these arms> _ => {} }` — every arm
    /// early-returns, so spine ids never reach the generic
    /// `mixfix_part`/`mixfix_parts_len` reads). EMPTY when no mixfix groups.
    pub mixfix_prelude_arms: TokenStream,
}

impl SpineEmission {
    /// True iff the emission-effective partition produced ≥1 factored group
    /// (⇒ the engine-table overrides / the `__s1_spine_weight_rule` free fn
    /// are emitted and the lex-fork weight sites must route through it).
    /// `S1_FACTORING == false` ⇒ always `false` — every consumer emits
    /// byte-identically to the pre-F1 output.
    pub(crate) fn any_groups(&self) -> bool {
        !self.trigger_spine_owner_fn.is_empty()
    }
}

/// The (symbol, new_state) target tokens for consuming a child edge.
/// `cat` = owning category; `spine_id` = the group id.
fn child_target_tokens(
    cat: u16,
    spine_id: u16,
    child: &SpineTree,
    child_id: u8,
) -> (TokenStream, TokenStream) {
    match child {
        SpineTree::Interior { .. } => (
            quote! {
                StackSymbolV2::rule_at(#cat, #spine_id, #child_id, Some(*outer_bp))
            },
            quote! {
                WpdaState::BinderRule {
                    result_src_idx: #cat,
                    rule_idx: #spine_id,
                    body_src_idx: *_body_src_idx,
                    outer_bp: *outer_bp,
                }
            },
        ),
        SpineTree::Leaf { member, .. } => match &member.commit {
            MemberCommit::Binder { rule_idx, resume_pos } => (
                quote! {
                    StackSymbolV2::rule_at(#cat, #rule_idx, #resume_pos, Some(*outer_bp))
                },
                quote! {
                    WpdaState::BinderRule {
                        result_src_idx: #cat,
                        rule_idx: #rule_idx,
                        body_src_idx: *_body_src_idx,
                        outer_bp: *outer_bp,
                    }
                },
            ),
            MemberCommit::Nullary { rule_idx, completed_idx, sub_pos } => (
                quote! {
                    StackSymbolV2::mixfix_marker(#cat, #rule_idx, 0u8, *outer_bp)
                },
                quote! {
                    WpdaState::MixfixLiteralRun {
                        result_src_idx: #cat,
                        rule_idx: #rule_idx,
                        completed_idx: #completed_idx,
                        kind: 2u8,
                        sub_pos: #sub_pos,
                    }
                },
            ),
            // F5-2: MixfixRun commits belong to the MIXFIX surface — their
            // branch formers live in the spliced MixfixLiteralRun prelude
            // (`mixfix_prelude_group_arms`), never in the prefix BinderRule
            // arm stream. Reaching here means a mixfix member leaked into a
            // prefix trie — fail codegen loudly.
            MemberCommit::MixfixRun { rule_idx, .. } => panic!(
                "S1-FACTORING F5-2: MixfixRun commit (cat {cat}, rule {rule_idx}) \
                 reached the prefix-surface branch former — mixfix members never \
                 join prefix tries",
            ),
        },
    }
}

/// One Fork BRANCH consuming a child edge (used by divergence arms and, as a
/// single-branch Fork, by chain Literal arms — the binder.rs Literal-arm
/// convention, Cluster 1 closure #5).
fn child_branch_tokens(cat: u16, spine_id: u16, child: &SpineTree, child_id: u8) -> TokenStream {
    let (sym, state) = child_target_tokens(cat, spine_id, child, child_id);
    match child.item() {
        SpineItem::Literal { text, required_top_cat } => {
            let req = match required_top_cat {
                Some(c) => quote! { Some(#c) },
                None => quote! { None },
            };
            quote! {
                mettail_prattail::wpda_transitions::factoring::child_literal(
                    || #sym, || #state, #text, #req, lex_one,
                )
            }
        },
        SpineItem::ParamParse { cat_src_idx, cur_bp } => {
            // The branch PUSHES the operand CategoryEntry; the marker
            // replacement rides the action kind (walker ReplaceAndPush
            // fork semantics — binder collection-arm precedent).
            quote! {
                mettail_prattail::wpda_transitions::factoring::parameter_replace_branch(
                    #cat_src_idx, _pos, #cur_bp, || #sym, lex_one,
                )
            }
        },
    }
}

/// Build the complete F1 emission bundle from the EMISSION-EFFECTIVE
/// partition. Call ONCE per language expansion (engine_impl assembly) and
/// thread the pieces to the consumers.
pub(crate) fn build_spine_emission(
    language: &LanguageDef,
    categories: &[String],
    per_cat: &[Vec<GrammarRule>],
) -> SpineEmission {
    let partition = emission_partition(language, categories, per_cat);
    // F5-2: the const-following mixfix partition (identity — zero groups —
    // unless `S1_FACTORING && S1F5_MIXFIX_COHORTS`).
    let mixfix_partition = mixfix_emission_partition(language, categories, per_cat);
    build_spine_emission_from_parts(&partition, &mixfix_partition, language, categories, per_cat)
}

/// The prefix-partition-explicit view of [`build_spine_emission`] — the
/// F0/F1/F5-1 pins' entry point, PRESERVED with an explicitly EMPTY mixfix
/// contribution so the prefix-surface pins stay stance-independent of
/// [`super::forks::S1F5_MIXFIX_COHORTS`]. Mixfix-aware tests use
/// [`build_spine_emission_from_parts`] with an explicit mixfix partition.
// dead_code: F0/F1/F5-1 pins' entry point, called only from the `#[cfg(test)]` suite.
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) fn build_spine_emission_from(
    partition: &[CategoryFactoring],
    language: &LanguageDef,
    categories: &[String],
    per_cat: &[Vec<GrammarRule>],
) -> SpineEmission {
    build_spine_emission_from_parts(partition, &[], language, categories, per_cat)
}

/// The fully-explicit core of [`build_spine_emission`] (both partitions
/// pinned by the caller — the F1 `build_spine_emission_from` precedent
/// extended to the F5-2 mixfix surface; tests pin BOTH stances without
/// const flips).
pub(crate) fn build_spine_emission_from_parts(
    partition: &[CategoryFactoring],
    mixfix_partition: &[MixfixFactoring],
    language: &LanguageDef,
    categories: &[String],
    per_cat: &[Vec<GrammarRule>],
) -> SpineEmission {
    use mettail_prattail::wpda_rule_analysis::factoring::emission::{
        try_build_factoring_emission_descriptors, FactoringEmissionDescriptors,
    };
    let FactoringEmissionDescriptors {
        dispositions,
        group_members,
        lex_alt,
        mixfix_groups,
    } = try_build_factoring_emission_descriptors(per_cat.len(), partition, mixfix_partition)
        .expect("original factoring partitions have valid category indexes and nonempty groups");
    // ★ #141 G8 — the model's refusals, rendered once, here, from BOTH
    // partitions. `emission_partition` / `mixfix_emission_partition` are the
    // only producers and this is their only consumer, so a refusal cannot be
    // recorded and then dropped.
    let refusal_items: Vec<TokenStream> = partition
        .iter()
        .flat_map(|cat_fact| cat_fact.refusals.iter())
        .chain(mixfix_partition.iter().flat_map(|mix| mix.refusals.iter()))
        .map(|message| quote! { compile_error!(#message); })
        .collect();
    let mut emission_refusals: Vec<String> = Vec::new();
    let mut binder_arms: Vec<TokenStream> = Vec::new();
    let mut owner_arms: Vec<TokenStream> = Vec::new();
    let mut member_arms: Vec<TokenStream> = Vec::new();
    let mut action_arms: Vec<TokenStream> = Vec::new();
    let mut lead_arms: Vec<TokenStream> = Vec::new();
    let mut span_arms: Vec<TokenStream> = Vec::new();
    let mut weight_arms: Vec<TokenStream> = Vec::new();
    let mut any_groups = false;

    for cat_fact in partition {
        let cat = cat_fact.category_src_idx;
        let cat_usize = cat as usize;
        let rules = &per_cat[cat_usize];
        for bucket in &cat_fact.buckets {
            for group in &bucket.groups {
                any_groups = true;
                let spine_id = group.spine_id;
                let members = group.member_rule_idxs(); // BTreeSet — min first
                let weight_rule_idx = *members
                    .iter()
                    .next()
                    .expect("an eligible group has members");
                // ── binder arms ──────────────────────────────────────────
                for node in flatten_forest(&group.roots, &mut emission_refusals) {
                    let node_id = node.node_id;
                    let branches: Vec<TokenStream> = node
                        .children
                        .iter()
                        .map(|(child, cid)| child_branch_tokens(cat, spine_id, child, *cid))
                        .collect();
                    let arm_body = if node.children.len() == 1 {
                        // Chain arm. Literal chains keep the single-branch
                        // Fork convention; ParamParse chains emit the plain
                        // ReplaceAndPush (binder.rs ParamParse-arm shape).
                        let (child, cid) = &node.children[0];
                        match child.item() {
                            SpineItem::Literal { .. } => {
                                let b = &branches[0];
                                quote! {
                                    return mettail_prattail::wpda_transitions::factoring::literal_chain(|| #b);
                                }
                            },
                            SpineItem::ParamParse { cat_src_idx, cur_bp } => {
                                let (sym, state) = child_target_tokens(cat, spine_id, child, *cid);
                                let _ = state; // param chains resume via PrefixDispatch
                                quote! {
                                    return mettail_prattail::wpda_transitions::factoring::parameter_replace(
                                        || #sym, #cat_src_idx, _pos, #cur_bp, lex_one,
                                    );
                                }
                            },
                        }
                    } else {
                        // Divergence arm: one branch per trie child; literal
                        // branches die on their guards (the shared
                        // evidence-prune, plan §2 item 3).
                        let branch_count = branches.len();
                        let branch_pushes = branches.iter().map(|branch| {
                            quote! {
                                __spine_branches.push(#branch);
                            }
                        });
                        quote! {
                            return mettail_prattail::wpda_transitions::factoring::divergence(
                                #branch_count,
                                |__spine_branches| { #( #branch_pushes )* },
                            );
                        }
                    };
                    binder_arms.push(quote! {
                        (#cat, #spine_id, #node_id) => { #arm_body }
                    });
                }
                // ── engine table rows ────────────────────────────────────
                for m in members.iter().copied() {
                    owner_arms.push(quote! {
                        (#cat, #m) => Some(#spine_id),
                    });
                }
                let member_list: Vec<u16> = members.iter().copied().collect();
                member_arms.push(quote! {
                    (#cat, #spine_id) => &[#(#member_list),*],
                });
                // action_for spine row (H9): expected_input_cats = the union
                // of the members' OWN expected_input_cats, derived EXACTLY as
                // `binder::emit_binder_action_entry` derives each member's row
                // (`shape.action_args`: `Term(cat)` → category index through the
                // SHARED resolver; every non-Term
                // slot → the ANY_CAT sentinel `u16::MAX`). ANY_CAT values are
                // kept in the union — faithful, and inert at both consumers
                // (`contains(&body_cat)` never matches `MAX` for a real
                // category; the single-hop-coercion probe on `MAX` hits the
                // engine table default `&[]`). Nullary members are
                // `NullaryLiteralRun` shapes whose entries are arity-0 `&[]`
                // (semantic_actions::emit_action_entry_arm) — they contribute
                // nothing. Arity = u8::MAX poison; action_fn = debug-trap
                // no-op (the H9 walker asserts fire first in debug; in
                // release the poison arity elides at every fire path).
                //
                // ★ #141 — sibling 3 of 7. The `Term(cat)` arm ended in
                // `.unwrap_or(0)`: an undeclared member category entered the SPINE's
                // union as index 0, the FIRST declared category, so the cohort
                // advertised an input category no member ever names.
                //
                // Unlike the two siblings above, DECLINING is not available here —
                // the members are already committed to this spine and the arm is
                // being emitted. It does not need to be: this is emitted code, and
                // the arm body is a BLOCK, so the refusal goes in as a token exactly
                // where it was discovered. `compile_error!` fires on expansion, not
                // on the arm being selected at run time, so an unresolvable category
                // fails the build with a message naming the category and the rule —
                // and no index at all enters the union.
                let mut union: Vec<u16> = Vec::new();
                let mut union_refusals: Vec<TokenStream> = Vec::new();
                for m in members.iter().copied() {
                    let member_rule = &rules[m as usize];
                    let Some(shape) = classify_binder_in(member_rule, language) else {
                        continue; // Nullary member: arity-0 entry, no cats.
                    };
                    for kind in &shape.action_args {
                        let ci = match kind {
                            ActionArgKind::Term(cat) => {
                                match super::binder::resolve_cat_idx(
                                    cat,
                                    categories,
                                    "a spine cohort's action entry",
                                    &member_rule.label.to_string(),
                                ) {
                                    Ok(idx) => idx,
                                    Err(unresolved) => {
                                        union_refusals.push(
                                            unresolved.compile_error(member_rule.label.span()),
                                        );
                                        continue;
                                    },
                                }
                            },
                            // binder.rs `any_cat_value` convention: non-Term
                            // slots (BinderName/BinderList/Predicate/...) are
                            // ANY_CAT in the member's own row.
                            _ => u16::MAX,
                        };
                        if !union.contains(&ci) {
                            union.push(ci);
                        }
                    }
                }
                action_arms.push(quote! {
                    (#cat, #spine_id) => {
                        #(#union_refusals;)*
                        static SPINE_ENTRY: mettail_prattail::wpda_runtime::ActionEntry =
                            mettail_prattail::wpda_runtime::ActionEntry {
                                action_fn: |
                                    _b: &mut mettail_prattail::wpda_runtime::SemanticBuilder,
                                    _args: Vec<mettail_prattail::wpda_runtime::ActionArg>|
                                {
                                    // S1 H9: never fired — commit precedes
                                    // every fire; the walker consumption
                                    // sites debug-assert on spine ids.
                                    debug_assert!(
                                        false,
                                        "S1 H9: spine action_fn invoked",
                                    );
                                },
                                arity: u8::MAX,
                                expected_input_cats: &[#(#union),*],
                                output_cat: #cat,
                            };
                        return Some(&SPINE_ENTRY);
                    }
                });
                // A7: rule_has_leading_structural_trigger spine row =
                // CONJUNCTION over members, computed from the SAME per-rule
                // predicate the canonical lookup emits ("first syntax element
                // is a Literal", collection.rs::
                // emit_rule_has_leading_structural_trigger_lookup). All-true
                // is structurally guaranteed under F0 eligibility (binder
                // members require a leading `SyntaxExpr::Literal` trigger in
                // `discover_members`; NullaryLiteralRun implies one) —
                // ASSERTED so an F5-era eligibility change fails codegen
                // loudly instead of silently emitting a wrong row.
                let lead_conjunction = members.iter().copied().all(|m| {
                    rules[m as usize]
                        .syntax_pattern
                        .as_ref()
                        .map(|sp| matches!(sp.first(), Some(SyntaxExpr::Literal(_))))
                        .unwrap_or(false)
                });
                // ★ #141 G8 — emitter position: the refusal joins the same
                // `lead_arms` vector the row would have gone into.
                if !lead_conjunction {
                    let message = format!(
                        "{LIMIT_REFUSAL} the group at category index {cat}, spine id \
                         {spine_id:#06x}, has a member with no leading literal trigger, \
                         but every member of an eligible group is required to have one. \
                         The eligibility test and the emission disagree; this is a macro \
                         bug, not a grammar bug — please report it.",
                    );
                    lead_arms.push(quote! { compile_error!(#message); });
                }
                lead_arms.push(quote! {
                    (#cat, #spine_id) => return true,
                });
                // min_terminal_span: min over members' effective rows (0 =
                // absent = the default ⇒ omit the row when min is 0).
                let mut min_span: Option<u32> = None;
                for m in members.iter().copied() {
                    let v = member_min_span(&rules[m as usize]);
                    min_span = Some(match min_span {
                        Some(cur) => cur.min(v),
                        None => v,
                    });
                }
                if let Some(v) = min_span {
                    if v > 0 {
                        span_arms.push(quote! {
                            (#cat, #spine_id) => return #v,
                        });
                    }
                }
                weight_arms.push(quote! {
                    (#cat, #spine_id) => #weight_rule_idx,
                });
            }
        }
    }

    // ── F5-2: the mixfix send-cohort emission ─────────────────────────────
    let mut mixfix_fan_arm_streams: Vec<TokenStream> = Vec::new();
    let mut mixfix_prelude_arm_streams: Vec<TokenStream> = Vec::new();
    for fact in mixfix_partition {
        let dispatch_cat = fact.dispatch_cat_src_idx;
        for bucket in &fact.buckets {
            for group in &bucket.groups {
                any_groups = true;
                let result_src = group.result_src_idx;
                let spine_id = group.spine_id;
                let min_member = group.min_member_rule_idx;
                let members = group.member_rule_idxs();
                let rules = &per_cat[result_src as usize];
                // Engine-table rows (the F1 shapes, keyed in the RESULT
                // category's id space).
                for m in members.iter().copied() {
                    owner_arms.push(quote! {
                        (#result_src, #m) => Some(#spine_id),
                    });
                }
                member_arms.push(quote! {
                    (#result_src, #spine_id) => &[#(#members),*],
                });
                // H9 poison row: expected_input_cats = the first-seen-order
                // union of the members' OWN action-entry rows (the
                // semantic_actions mixfix derivation mirrored at model
                // build: `[dispatch_cat] ++ per part (operand | ANY_CAT)`;
                // nullary members contribute `[dispatch_cat]` only).
                let union = &group.expected_cats_union;
                action_arms.push(quote! {
                    (#result_src, #spine_id) => {
                        static SPINE_ENTRY: mettail_prattail::wpda_runtime::ActionEntry =
                            mettail_prattail::wpda_runtime::ActionEntry {
                                action_fn: |
                                    _b: &mut mettail_prattail::wpda_runtime::SemanticBuilder,
                                    _args: Vec<mettail_prattail::wpda_runtime::ActionArg>|
                                {
                                    // S1 H9: never fired — commit precedes
                                    // every fire; the walker consumption
                                    // sites debug-assert on spine ids.
                                    debug_assert!(
                                        false,
                                        "S1 H9: mixfix spine action_fn invoked",
                                    );
                                },
                                arity: u8::MAX,
                                expected_input_cats: &[#(#union),*],
                                output_cat: #result_src,
                            };
                        return Some(&SPINE_ENTRY);
                    }
                });
                // A7-mixfix (A-M5 flip of the F1 assert): members are
                // OPERAND-leading — the leading-trigger conjunction is
                // all-FALSE, so the spine row is OMITTED (the canonical
                // per-rule lookup's default arm is `false`). Asserted so an
                // eligibility drift fails codegen loudly.
                for m in members.iter().copied() {
                    let leads_with_literal = rules[m as usize]
                        .syntax_pattern
                        .as_ref()
                        .map(|sp| matches!(sp.first(), Some(SyntaxExpr::Literal(_))))
                        .unwrap_or(false);
                    // ★ #141 G8 — emitter position; see the prefix twin above.
                    if leads_with_literal {
                        let message = format!(
                            "{LIMIT_REFUSAL} the mixfix cohort at result category index \
                             {result_src}, spine id {spine_id:#06x}, has member rule \
                             index {m} LEADING with a literal, but mixfix cohort members \
                             are operand-leading by construction. The eligibility test \
                             and the emission disagree; this is a macro bug, not a \
                             grammar bug — please report it.",
                        );
                        lead_arms.push(quote! { compile_error!(#message); });
                    }
                }
                // min_terminal_span: min over members (honest computation;
                // 0 = the table default ⇒ row omitted — both real cohorts
                // carry an Op-bearing rep member ⇒ min 0).
                let mut min_span: Option<u32> = None;
                for m in members.iter().copied() {
                    let v = member_min_span(&rules[m as usize]);
                    min_span = Some(match min_span {
                        Some(cur) => cur.min(v),
                        None => v,
                    });
                }
                if let Some(v) = min_span {
                    if v > 0 {
                        span_arms.push(quote! {
                            (#result_src, #spine_id) => return #v,
                        });
                    }
                }
                // AV5-analog weight identity (also the A-M5 action-kind
                // redirect payload for the lex-alt surface).
                weight_arms.push(quote! {
                    (#result_src, #spine_id) => #min_member,
                });
                // The loop-v2 fan arm + the MLR spine prelude arms.
                let trigger = &bucket.trigger;
                mixfix_fan_arm_streams.push(mixfix_fan_group_arm(dispatch_cat, trigger, group));
                mixfix_prelude_arm_streams.push(mixfix_prelude_group_arms(group));
            }
        }
    }
    let mixfix_fan_arms = quote! { #(#mixfix_fan_arm_streams)* };
    let mixfix_prelude_arms = quote! { #(#mixfix_prelude_arm_streams)* };

    let binder_arms = quote! { #(#binder_arms)* };
    let trigger_spine_owner_fn = if any_groups {
        quote! {
            fn trigger_spine_owner(&self, src_idx: u16, rule_idx: u16) -> Option<u16> {
                match (src_idx, rule_idx) {
                    #(#owner_arms)*
                    _ => None,
                }
            }
        }
    } else {
        TokenStream::new()
    };
    let spine_members_fn = if any_groups {
        quote! {
            fn spine_members(&self, src_idx: u16, spine_id: u16) -> &[u16] {
                match (src_idx, spine_id) {
                    #(#member_arms)*
                    _ => &[],
                }
            }
        }
    } else {
        TokenStream::new()
    };
    let action_for_prelude = if any_groups {
        quote! {
            match (src_idx, rule_idx) {
                #(#action_arms)*
                _ => {},
            }
        }
    } else {
        TokenStream::new()
    };
    let leading_trigger_prelude = if any_groups {
        quote! {
            match (result_src_idx, rule_idx) {
                #(#lead_arms)*
                _ => {},
            }
        }
    } else {
        TokenStream::new()
    };
    let min_span_prelude = if span_arms.is_empty() {
        TokenStream::new()
    } else {
        quote! {
            match (src_idx, rule_idx) {
                #(#span_arms)*
                _ => {},
            }
        }
    };
    let spine_weight_rule_fn = if any_groups {
        quote! {
            #[allow(dead_code)]
            fn __s1_spine_weight_rule(cat: u16, rule: u16) -> u16 {
                match (cat, rule) {
                    #(#weight_arms)*
                    _ => rule,
                }
            }
        }
    } else {
        TokenStream::new()
    };
    let refusals = {
        let items: Vec<TokenStream> = refusal_items
            .into_iter()
            .chain(
                emission_refusals
                    .iter()
                    .map(|message| quote! { compile_error!(#message); }),
            )
            .collect();
        quote! { #(#items)* }
    };
    SpineEmission {
        dispositions,
        refusals,
        group_members,
        binder_arms,
        trigger_spine_owner_fn,
        spine_members_fn,
        action_for_prelude,
        leading_trigger_prelude,
        min_span_prelude,
        lex_alt,
        spine_weight_rule_fn,
        mixfix_groups,
        mixfix_fan_arms,
        mixfix_prelude_arms,
    }
}

/// F5-2: ONE loop-v2 group match arm for the InfixLoop mixfix tier. The
/// guard is the D-1 FULL-ADMISSION predicate: `min_l_bp >= cur_bp` (l_bp is
/// the only member-varying admission input) AND the member-uniform goal +
/// method-name gates — evaluated on the uniform `result_src` and (A-M4) a
/// MEMBER rule id (`min_member`; a spine id would hit the metadata-None
/// `(None, _) => true` silent always-keep). A failed guard falls through to
/// the `_` arm's verbatim per-member loop — the exact D-1 fallback (partial
/// floor windows, goal/method-name rejections, and the fallback-full case
/// all reproduce today's per-member behavior byte-for-byte).
fn mixfix_fan_group_arm(dispatch_cat: u16, trigger: &str, group: &MixfixGroup) -> TokenStream {
    let result_src = group.result_src_idx;
    let spine_id = group.spine_id;
    let min_l_bp = group.min_l_bp;
    let min_member = group.min_member_rule_idx;
    quote! {
        (#dispatch_cat, #trigger)
            if #min_l_bp >= *cur_bp
                && __goal_admits(#result_src)
                && (__mixfix_fallback_full
                    || __method_name_admits(#result_src, #min_member)) =>
        {
            __cands.push(
                mettail_prattail::wpda_transitions::factoring::mixfix_group_branch(
                    #result_src, #spine_id, *cur_bp, #min_member, lex_w,
                ),
            );
            __mixfix_spine_pushed = true;
        }
    }
}

/// F5-2: the spliced `MixfixLiteralRun` prelude arms for ONE mixfix group —
/// the pre-root arm (consumes the root edge from the fan-pushed
/// `(2, 0, 0)`) plus one arm per interior trie node (consumes the node's
/// CHILDREN's edges: chain step, divergence fork, or operand descent).
/// Every arm early-returns; commits replace the SPINE marker with the
/// member's own `mixfix_marker` and enter the member's generic machinery at
/// its recorded [`MemberCommit::MixfixRun`] coordinate (FS1: every commit
/// rides a consuming edge — literal commits ride `ConsumeAtAndReplace`;
/// operand-edge commits ride `ReplaceAndPush`, consuming via the
/// sub-parse).
fn mixfix_prelude_group_arms(group: &MixfixGroup) -> TokenStream {
    let result_src = group.result_src_idx;
    let spine_id = group.spine_id;
    let root = &group.roots[0];
    let arm_plan =
        mixfix_spine_arm_coords(root).expect("eligibility rejected colliding spine coordinates");
    let mut arms: Vec<TokenStream> = Vec::with_capacity(1 + arm_plan.len());
    // The PRE-ROOT arm: consume the root edge itself.
    let root_after = match root.item() {
        SpineItem::Literal { .. } => {
            let (k, c, s) = (2u8, 0u8, 1u8);
            (k, c, s)
        },
        SpineItem::ParamParse { .. } => (0u8, 0u8, 0u8),
    };
    arms.push(mixfix_spine_step_arm(
        result_src,
        spine_id,
        (2, 0, 0),
        std::slice::from_ref(&(root, root_after)),
    ));
    // Interior-node arms: each consumes its children's edges.
    for (arm_key, node) in &arm_plan {
        let SpineTree::Interior { children, .. } = node else {
            continue;
        };
        let child_entries: Vec<(&SpineTree, (u8, u8, u8))> = children
            .iter()
            .map(|child| {
                let after = match child.item() {
                    SpineItem::Literal { .. } => match *arm_key {
                        (2, c, s) => (2, c, s + 1),
                        (0, c, s) => (0, c, s + 1),
                        other => panic!(
                            "S1-FACTORING F5-2: spine arm at kind {} — only kinds \
                             2 and 0 occur on a spine path",
                            other.0,
                        ),
                    },
                    SpineItem::ParamParse { .. } => (0, 0, 0),
                };
                (child, after)
            })
            .collect();
        arms.push(mixfix_spine_step_arm(result_src, spine_id, *arm_key, &child_entries));
    }
    quote! { #(#arms)* }
}

/// F5-2: the `(symbol, new_state)` target tokens of ONE spine-arm child
/// edge. Interior children continue the SPINE (self-marker + the spine
/// coordinate after the edge); leaf children COMMIT (member marker at the
/// recorded [`MemberCommit::MixfixRun`] coordinate + the member's own
/// `MixfixLiteralRun` state).
fn mixfix_child_target_tokens(
    result_src: u16,
    spine_id: u16,
    child: &SpineTree,
    child_after: (u8, u8, u8),
) -> (TokenStream, TokenStream) {
    match child {
        SpineTree::Interior { .. } => {
            let (k, c, s) = child_after;
            (
                quote! {
                    StackSymbolV2::mixfix_marker(
                        #result_src, #spine_id, #c, __mixfix_continuation_bp,
                    )
                },
                quote! {
                    WpdaState::MixfixLiteralRun {
                        result_src_idx: #result_src,
                        rule_idx: #spine_id,
                        completed_idx: #c,
                        kind: #k,
                        sub_pos: #s,
                    }
                },
            )
        },
        SpineTree::Leaf { member, .. } => {
            let MemberCommit::MixfixRun { rule_idx, kind, completed_idx, sub_pos } = &member.commit
            else {
                panic!(
                    "S1-FACTORING F5-2: mixfix trie leaf (rule {}) carries a \
                     non-MixfixRun commit — the discovery kind drifted",
                    member.rule_idx,
                );
            };
            (
                quote! {
                    StackSymbolV2::mixfix_marker(
                        #result_src, #rule_idx, #completed_idx,
                        __mixfix_continuation_bp,
                    )
                },
                quote! {
                    WpdaState::MixfixLiteralRun {
                        result_src_idx: #result_src,
                        rule_idx: #rule_idx,
                        completed_idx: #completed_idx,
                        kind: #kind,
                        sub_pos: #sub_pos,
                    }
                },
            )
        },
    }
}

/// F5-2: ONE spine prelude arm — the arm at `arm_key` consumes the given
/// child edges. Shapes (structurally exhaustive for eligible mixfix tries —
/// a single child is always Interior; leaves appear only inside ≥2-child
/// divergences):
///
///   - 1 Literal child: the `__checked_literal_consume!` chain step
///     (0 targets → Error; 1 → self-replace `ConsumeAtAndReplace`; ≥2 →
///     Fork of self-replace CARs — the ROOT-A lattice-membership law).
///   - 1 ParamParse child: the operand descent pushes a strict
///     `CategoryEntry(goal)` before entering `PrefixDispatch`, exactly like
///     the unfactored mixfix machine. The frame is required even when source
///     and result categories coincide: it is the typed boundary that prevents
///     a nested cross-category continuation from escaping the operand.
///   - ≥2 children (divergence): literal children contribute one
///     `ConsumeAtAndReplace` branch per lattice target (commit or spine
///     continuation); a ParamParse child contributes one UNCONDITIONAL
///     branch (descent, or `ReplaceAndPush` commit for an operand-edge
///     leaf). Zero live branches → `Error`; exactly one → the equivalent
///     NON-FORK action (plan §2.2: "if only A, the single-target
///     ConsumeAtAndReplace; B alone, emit the strict Push"); otherwise a
///     `Fork { consume_trigger: false }` in trie child order.
fn mixfix_spine_step_arm(
    result_src: u16,
    spine_id: u16,
    arm_key: (u8, u8, u8),
    children: &[(&SpineTree, (u8, u8, u8))],
) -> TokenStream {
    let (ak, ac, asub) = arm_key;
    let key_pat = quote! { (#result_src, #spine_id, #ak, #ac, #asub) };
    // ── single-child chain forms ──────────────────────────────────────────
    if children.len() == 1 {
        let (child, child_after) = &children[0];
        // ★ #141 G8 — emitter position (this function returns the arm's
        // tokens), so the refusal simply IS the arm.
        if !matches!(child, SpineTree::Interior { .. }) {
            let message = format!(
                "{LIMIT_REFUSAL} the single spine-arm child at result category index \
                 {result_src}, spine id {spine_id:#06x}, is a leaf rather than an \
                 interior node, but a single-member part leafs out at its PARENT. The \
                 trie build and the arm emission disagree; this is a macro bug, not a \
                 grammar bug — please report it.",
            );
            return quote! { compile_error!(#message); };
        }
        match child.item() {
            SpineItem::Literal { text, .. } => {
                let (_, state) =
                    mixfix_child_target_tokens(result_src, spine_id, child, *child_after);
                return quote! {
                    #key_pat => {
                        return __checked_literal_consume!(#text, #state);
                    }
                };
            },
            SpineItem::ParamParse { cat_src_idx, cur_bp } => {
                return quote! {
                    #key_pat => {
                        return mettail_prattail::wpda_transitions::factoring::parameter_push(
                            #cat_src_idx, _pos, #cur_bp, lex_one,
                        );
                    }
                };
            },
        }
    }
    // ── divergence arm ────────────────────────────────────────────────────
    let mut target_lets: Vec<TokenStream> = Vec::new();
    let mut lit_len_terms: Vec<TokenStream> = Vec::new();
    let mut singleton_checks: Vec<TokenStream> = Vec::new();
    let mut push_stmts: Vec<TokenStream> = Vec::new();
    let mut uncond_nonforks: Vec<TokenStream> = Vec::new();
    let mut lit_idx: usize = 0;
    for (child, child_after) in children {
        let (sym, state) = mixfix_child_target_tokens(result_src, spine_id, child, *child_after);
        match child.item() {
            SpineItem::Literal { text, .. } => {
                let t_ident = quote::format_ident!("__spine_targets_{}", lit_idx);
                lit_idx += 1;
                target_lets.push(quote! {
                    let #t_ident: Vec<usize> =
                        __mixfix_literal_targets(tokens, _pos, #text);
                });
                lit_len_terms.push(quote! { #t_ident.len() });
                singleton_checks.push(quote! {
                    if let Some(__action) =
                        mettail_prattail::wpda_transitions::factoring::literal_singleton(
                            &#t_ident, || #sym, || #state, lex_one,
                        )
                    {
                        return Some(__action);
                    }
                });
                push_stmts.push(quote! {
                    mettail_prattail::wpda_transitions::factoring::append_literal_targets(
                        &#t_ident, || #sym, || #state, lex_one, __spine_branches,
                    );
                });
            },
            SpineItem::ParamParse { cat_src_idx, cur_bp } => {
                let (branch, nonfork) = match child {
                    SpineTree::Interior { .. } => (
                        quote! {
                            mettail_prattail::wpda_transitions::factoring::parameter_push_branch(
                                #cat_src_idx, _pos, #cur_bp, lex_one,
                            )
                        },
                        quote! {
                            return mettail_prattail::wpda_transitions::factoring::parameter_push(
                                #cat_src_idx, _pos, #cur_bp, lex_one,
                            );
                        },
                    ),
                    SpineTree::Leaf { .. } => {
                        // Operand-edge commit (FS1: consuming via the
                        // sub-parse): replace the SPINE marker with the
                        // member marker, push the operand entry.  The
                        // nonterminal occurrence is goal-bounded even when
                        // source and result categories coincide: a nested
                        // cross-category operator must not escape the typed
                        // operand merely because the first category matched.
                        (
                            quote! {
                                mettail_prattail::wpda_transitions::factoring::parameter_replace_branch(
                                    #cat_src_idx, _pos, #cur_bp, || #sym, lex_one,
                                )
                            },
                            quote! {
                                return mettail_prattail::wpda_transitions::factoring::parameter_replace(
                                    || #sym, #cat_src_idx, _pos, #cur_bp, lex_one,
                                );
                            },
                        )
                    },
                };
                uncond_nonforks.push(nonfork);
                push_stmts.push(quote! { __spine_branches.push(#branch); });
            },
        }
    }
    let n_uncond = uncond_nonforks.len();
    let lit_total_expr = if lit_len_terms.is_empty() {
        quote! { 0usize }
    } else {
        quote! { #(#lit_len_terms)+* }
    };
    // The zero-live and singleton short-circuits (plan §2.2).
    let zero_handler = match n_uncond {
        0 => quote! {
            if let Some(__action) =
                mettail_prattail::wpda_transitions::factoring::zero_literal_only(
                    __spine_lit_total, _pos, #result_src, #spine_id,
                )
            {
                return __action;
            }
        },
        1 => {
            let nonfork = &uncond_nonforks[0];
            quote! {
                if let Some(__action) =
                    mettail_prattail::wpda_transitions::factoring::zero_one_operand(
                        __spine_lit_total, || { #nonfork },
                    )
                {
                    return __action;
                }
            }
        },
        // ≥2 unconditional branches always fork.
        _ => TokenStream::new(),
    };
    let singleton_handler = if n_uncond == 0 {
        quote! {
            if let Some(__action) =
                mettail_prattail::wpda_transitions::factoring::singleton(
                    __spine_lit_total, || {
                        #(#singleton_checks)*
                        None
                    },
                )
            {
                return __action;
            }
        }
    } else {
        TokenStream::new()
    };
    let n_uncond_lit = n_uncond;
    quote! {
        #key_pat => {
            #(#target_lets)*
            let __spine_lit_total: usize = #lit_total_expr;
            #zero_handler
            #singleton_handler
            return mettail_prattail::wpda_transitions::factoring::mixfix_divergence(
                #n_uncond_lit, __spine_lit_total,
                |__spine_branches| { #(#push_stmts)* },
            );
        }
    }
}

/// Per-rule min_terminal_span replica (semantic_actions::
/// emit_min_terminal_span_body's row computation — kept in lockstep; the
/// table default is 0).
fn member_min_span(rule: &GrammarRule) -> u32 {
    let Some(sp) = rule.syntax_pattern.as_ref() else {
        return 0;
    };
    if sp.iter().any(|e| matches!(e, SyntaxExpr::Op(_))) {
        return 0;
    }
    let all_simple = rule
        .term_context
        .as_ref()
        .map(|tc| {
            tc.iter()
                .all(|p| matches!(p, mettail_ast::grammar::TermParam::Simple { .. }))
        })
        .unwrap_or(true);
    if !all_simple {
        return 0;
    }
    let mut seen_param = false;
    let mut n: u32 = 0;
    for e in sp.iter() {
        match e {
            SyntaxExpr::Param(_) => seen_param = true,
            SyntaxExpr::Literal(_) if seen_param => n += 1,
            _ => {},
        }
    }
    n
}

/// The spine TRIGGER branch for prefix.rs's multi-branch fork (one per
/// eligible group, at the first member's emission position).
pub(crate) fn emit_spine_trigger_branch(
    category_src_idx: u16,
    spine_id: u16,
    body_src_idx: u16,
    weight_rule_idx: u16,
) -> TokenStream {
    quote! {
        __pd_branches.push(mettail_prattail::wpda_transitions::factoring::prefix_spine_trigger(
            #category_src_idx, #spine_id, #body_src_idx, _outer_bp, #weight_rule_idx, lex_w,
        ));
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// #141 G8 RED — the encoding limits REFUSE, and say which limit
// ═══════════════════════════════════════════════════════════════════════════
//
// ⚠ No cell expects a panic: each reads the `Vec<String>` the sink collects.
#[cfg(test)]
mod limit_refusal_red {
    use super::*;

    fn leaf(rule_idx: u16) -> SpineTree {
        SpineTree::Leaf {
            item: SpineItem::Literal {
                text: "x".to_string(),
                required_top_cat: None,
            },
            member: GroupMember {
                kind: MemberKind::Nullary,
                rule_idx,
                leaf_depth: 1,
                commit: MemberCommit::Nullary { rule_idx, completed_idx: 0, sub_pos: 0 },
                pos_map: SpinePosMap::Nullary { sub_pos_at_depth: vec![0] },
                has_post_spine_remainder: false,
            },
        }
    }

    /// ★ THE MUTATION CELL. A forest that carries FEWER leaves than a group has
    /// members refuses, and the message says which invariant it crossed.
    #[test]
    fn a_one_leaf_forest_refuses_instead_of_asserting() {
        let mut refusals: Vec<String> = Vec::new();
        let roots = [leaf(0)];
        let _ = flatten_forest(&roots, &mut refusals);

        assert_eq!(
            refusals.len(),
            1,
            "exactly one invariant is crossed by a one-leaf forest — the ≥2-leaf floor. \
             Got: {refusals:?}",
        );
        let message = &refusals[0];
        assert!(
            message.starts_with(LIMIT_REFUSAL),
            "every G8 refusal opens with the shared prefix so a reader can tell at a \
             glance that the FACTORING, not their grammar, is what could not be \
             encoded. Got: {message}",
        );
        assert!(
            message.contains("1 leaf/leaves"),
            "the message must report the COUNT it saw, which is what distinguishes a \
             collapsed forest from a merely small one. Got: {message}",
        );
        assert!(
            message.contains("one leaf per member"),
            "and it must name the invariant, not merely report a number. Got: {message}",
        );
    }

    /// ★ THE MUTATION CELL for the EMPTY forest — a different invariant, so a
    /// different message, and BOTH are reported rather than only the first.
    #[test]
    fn an_empty_forest_reports_both_invariants_it_crosses() {
        let mut refusals: Vec<String> = Vec::new();
        let _ = flatten_forest(&[], &mut refusals);

        assert_eq!(
            refusals.len(),
            2,
            "an empty forest crosses BOTH the non-emptiness invariant and the ≥2-leaf \
             floor. An `assert!` reported one per build; a sink reports both. Got: \
             {refusals:?}",
        );
        assert!(
            refusals.iter().any(|m| m.contains("spine forest is empty")),
            "the non-emptiness refusal must be present: {refusals:?}",
        );
        assert!(
            refusals.iter().any(|m| m.contains("0 leaf/leaves")),
            "and so must the leaf-floor refusal: {refusals:?}",
        );
    }

    /// ★ THE CONTROL that must NOT discriminate: a well-formed two-leaf forest
    /// refuses NOTHING and still flattens to its pre-root arm.
    #[test]
    fn a_two_leaf_forest_refuses_nothing() {
        let mut refusals: Vec<String> = Vec::new();
        let roots = [leaf(0), leaf(1)];
        let flat = flatten_forest(&roots, &mut refusals);

        assert!(
            refusals.is_empty(),
            "a forest that satisfies both invariants must produce NO refusal — \
             otherwise the cells above prove only that this function refuses \
             everything. Got: {refusals:?}",
        );
        assert_eq!(
            flat.len(),
            1,
            "and it must still emit exactly the synthetic PRE-ROOT arm (node id 1); \
             two leaf roots carry no arms of their own",
        );
        assert_eq!(flat[0].node_id, 1, "the pre-root arm is node id 1");
    }

    /// ANTI-VACUITY for the shared prefix: it is not the empty string, so
    /// `starts_with` above is a real assertion.
    #[test]
    fn the_shared_refusal_prefix_says_what_could_not_be_encoded() {
        assert!(
            LIMIT_REFUSAL.contains("cannot be encoded"),
            "the prefix must say what went wrong, not merely tag the message",
        );
        assert!(!LIMIT_REFUSAL.is_empty(), "an empty prefix makes `starts_with` vacuous");
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use mettail_ast::grammar::{convert_term_context_to_items, rule_fixture, TermParam};
    use mettail_ast::language::{LangType, LanguageDef};
    use mettail_ast::types::{CollectionType, TypeExpr};
    use proc_macro2::Span;
    use syn::Ident;

    // ── real-grammar loading (the pinned trie is against the ACTUAL rholang
    //    source, run through the same pre-codegen pipeline as `language!`:
    //    parse → auto-inject → per-category materialization) ─────────────────

    fn parse_bundled_language(manifest_relative: &str) -> LanguageDef {
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join(manifest_relative);
        let source = std::fs::read_to_string(&path)
            .unwrap_or_else(|e| panic!("bundled language source {path:?} readable: {e}"));
        let file = syn::parse_file(&source).expect("bundled language source parses as a Rust file");
        let mac = file
            .items
            .iter()
            .find_map(|item| match item {
                syn::Item::Macro(m) if m.mac.path.is_ident("language") => Some(m.mac.clone()),
                _ => None,
            })
            .expect("a language! invocation is present");
        let mut def: LanguageDef =
            syn::parse2(mac.tokens).expect("language! body parses as a LanguageDef");
        assert!(
            def.extends_names.is_empty()
                && def.include_names.is_empty()
                && def.mixin_names.is_empty(),
            "the pin assumes no composition clauses; apply mettail_ast::merge first if this fires",
        );
        // Same augmentation `macros/src/lib.rs` applies before
        // `generate_wpda_engine_module` (auto-injected promotion rules are
        // APPENDED, so user rule indices are unchanged — asserted below
        // against the WPDA_RULES-pinned labels anyway).
        let injected =
            crate::gen::runtime::wpda_codegen::auto_inject::emit_auto_injection_rules(&def);
        def.terms.extend(injected.terms);
        def.rewrites.extend(injected.rewrites);
        def
    }

    fn rholang() -> LanguageDef {
        parse_bundled_language("../languages/src/rholang.rs")
    }

    fn calculator() -> LanguageDef {
        parse_bundled_language("../languages/src/calculator.rs")
    }

    fn cats_per_cat(def: &LanguageDef) -> (Vec<String>, Vec<Vec<GrammarRule>>) {
        let categories =
            crate::gen::runtime::wpda_codegen::collect_category_names_with_literals(def);
        let per_cat = crate::gen::runtime::wpda_codegen::synthetic::build_per_category_rules(
            def,
            &categories,
        );
        (categories, per_cat)
    }

    fn src_idx(categories: &[String], name: &str) -> u16 {
        categories
            .iter()
            .position(|c| c == name)
            .unwrap_or_else(|| panic!("category {name} present")) as u16
    }

    fn rule_idx(per_cat_rules: &[GrammarRule], label: &str) -> u16 {
        per_cat_rules
            .iter()
            .position(|r| r.label == label)
            .unwrap_or_else(|| panic!("rule {label} present")) as u16
    }

    /// The label of the probe rule [`rholang_with_one_extra_proc_rule`] injects.
    const SHIFT_PROBE_LABEL: &str = "ZzShiftProbeOutput";

    /// Rholang with **one extra `Proc` rule above the pinned ones**, standing in for
    /// `PParInternal` as it was *before* `8c946bff` deleted it from `Proc` index 3.
    ///
    /// The two grammars are read in the incident's own direction: this one is the OLD tree,
    /// [`rholang`] is the NEW tree the rule was deleted from. Modelling the DELETION rather
    /// than an insertion matters, because the two shift indices OPPOSITE WAYS — under a
    /// deletion a stale literal `N` selects the old `N + 1`, and in these cohorts the rule at
    /// `N + 1` is the PERSIST TWIN; under an insertion it selects the old `N - 1`, an
    /// unrelated predecessor that does not reproduce the hazard. The first version of this
    /// fixture got that backwards and its own anti-vacuity assertion rejected it.
    ///
    /// The probe rule is a CLONE of the rule at that position under a fresh label, so it
    /// perturbs exactly one thing: the positions.
    fn rholang_with_one_extra_proc_rule() -> LanguageDef {
        let mut def = rholang();
        let first_proc = def
            .terms
            .iter()
            .position(|t| t.category == "Proc")
            .expect("Rholang declares at least one `Proc` rule");
        // Three past the first `Proc` rule — the neighbourhood the real deletion occurred in —
        // rather than at the very front, so the shift is not trivially the first index.
        let at = (first_proc + 3).min(def.terms.len());
        let mut probe = def.terms[at].clone();
        probe.label = Ident::new(SHIFT_PROBE_LABEL, Span::call_site());
        def.terms.insert(at, probe);
        def
    }

    /// The `Proc` rules whose coordinates the pins in this module select.
    ///
    /// Every entry is resolved through [`rule_idx`], which panics on a label the grammar no
    /// longer declares — so this list cannot drift away from the grammar silently.
    const PINNED_PROC_LABELS: &[&str] = &[
        "POutput",
        "POutputEmpty",
        "POutput2Plus",
        "POutputNil",
        "POutputQuoted",
        "POutputShort",
        "POutputNilEmpty",
        "POutputNil2Plus",
    ];

    /// ★★ #152 — THE DISCRIMINATING CELL, MADE EXECUTABLE.
    ///
    /// A rule *index* is a coordinate into a list; a rule *name* is a property of a rule. This
    /// test is the difference, measured on the real grammar under the real perturbation.
    ///
    /// # What went wrong, and why it was silent
    ///
    /// `8c946bff` deleted `PParInternal` from `Proc` index 3. Five pins failed loudly, off by
    /// one, and were re-derived by dumping the regenerated rule list. A sixth — then named
    /// `rholang_commit_coordinates_rule15_nullary_and_rule20_2plus` — **did not fail**: after
    /// the shift its 15/20/10 selected `PPersistOutputNilEmpty`, `PPersistOutputNil2Plus` and
    /// `PPersistOutputNil`, the PERSIST TWINS of the intended rules. Every assertion still
    /// held, because a twin has the same kind, the same leaf edge, the same depth and the same
    /// commit shape. **The loud failure is the lucky case.**
    ///
    /// # The two cells
    ///
    /// | cell | claim |
    /// |---|---|
    /// | derived | `rule_idx(rules, "POutputNil")` **moves with its rule** across the deletion |
    /// | literal | the stale constant **selects a different rule**, and for most of these it is the persist twin — so a pin written with it keeps passing while describing something else |
    ///
    /// Neither cell can pass vacuously: the first fails if the probe shifts nothing, the second
    /// fails if the shift retargets nothing, and a third assertion fails if *too few* retargets
    /// land on a twin — which is what would mean the fixture had stopped reproducing the hazard
    /// rather than the hazard having gone away.
    #[test]
    fn a_derived_coordinate_tracks_its_rule_across_a_shift_and_a_literal_does_not() {
        // OLD: the tree that still carries the extra rule. NEW: the tree it was deleted from.
        let old = rholang_with_one_extra_proc_rule();
        let (_, old_per_cat) = cats_per_cat(&old);
        let new = rholang();
        let (_, new_per_cat) = cats_per_cat(&new);

        let deleted_at = rule_idx(&old_per_cat[0], SHIFT_PROBE_LABEL);
        assert_eq!(
            old_per_cat[0].len(),
            new_per_cat[0].len() + 1,
            "the probe rule did not reach the materialised `Proc` list, so nothing shifted and \
             every cell below is vacuous",
        );

        // ── CELL 1: a DERIVED coordinate moves with its rule. ──────────────
        for label in PINNED_PROC_LABELS {
            let before = rule_idx(&old_per_cat[0], label);
            let after = rule_idx(&new_per_cat[0], label);
            assert!(
                before > deleted_at,
                "`{label}` sits at {before}, at or above the deleted rule at {deleted_at} — it \
                 would not shift, so it is the wrong witness for this cell",
            );
            assert_eq!(
                after,
                before - 1,
                "`{label}` moved from {before} to {after} under a ONE-rule deletion above it. A \
                 derived coordinate must track its rule exactly.",
            );
            assert_eq!(
                new_per_cat[0][after as usize].label.to_string(),
                *label,
                "the derived coordinate must still name `{label}` after the deletion",
            );
        }

        // ── CELL 2: the STALE LITERAL retargets. ───────────────────────────
        // The silent failure, exhibited rather than described.
        let mut retargets: Vec<(String, String)> = Vec::with_capacity(PINNED_PROC_LABELS.len());
        for label in PINNED_PROC_LABELS {
            let stale = rule_idx(&old_per_cat[0], label);
            let now = new_per_cat[0][stale as usize].label.to_string();
            assert_ne!(
                now.as_str(),
                *label,
                "the stale constant {stale} still names `{label}` after the deletion, so this \
                 cell cannot demonstrate a retarget",
            );
            retargets.push(((*label).to_string(), now));
        }

        // ★ THE HAZARD QUANTIFIED: how many stale literals land on the intended rule's PERSIST
        // TWIN — a rule with the same kind, leaf edge, depth and commit shape, which keeps
        // every structural assertion true and is therefore what makes the retarget SILENT
        // rather than loud.
        //
        // The twin of `Pxxx` is `PPersistxxx`: the `Persist` is infixed after the category's
        // `P`, not prefixed to the whole label. (A first version of this predicate spelled it
        // `PPersist{intended}` and matched nothing — the assertion below rejected it.)
        let twin_of = |label: &str| format!("PPersist{}", label.strip_prefix('P').unwrap_or(label));
        let onto_a_twin: Vec<&(String, String)> = retargets
            .iter()
            .filter(|(intended, now)| *now == twin_of(intended))
            .collect();
        assert!(
            !onto_a_twin.is_empty(),
            "no stale literal retargeted onto a PERSIST TWIN ({retargets:?}). The twins are what \
             make the retarget SILENT — without one in this neighbourhood the fixture no longer \
             reproduces the hazard #152 is about, and the witnesses in `PINNED_PROC_LABELS` need \
             re-choosing.",
        );
        assert!(
            onto_a_twin.len() * 2 >= PINNED_PROC_LABELS.len(),
            "only {} of {} stale literals retargeted onto a persist twin: {onto_a_twin:?}. The \
             point of this cell is that the SILENT outcome is the COMMON one and not a corner \
             case; if it has become rare, say so rather than keeping a weakened claim.",
            onto_a_twin.len(),
            PINNED_PROC_LABELS.len(),
        );
    }

    fn bucket<'a>(model: &'a [CategoryFactoring], cat: u16, literal: &str) -> &'a FactoringBucket {
        model
            .iter()
            .find(|c| c.category_src_idx == cat)
            .expect("category present in the factoring model")
            .buckets
            .iter()
            .find(|b| b.leading_literal == literal)
            .unwrap_or_else(|| panic!("bucket (cat {cat}, {literal:?}) present"))
    }

    /// Compact deterministic rendering of a spine trie: `L(text)` /
    /// `P(cat,bp)` items, `[..]` interior children in build order,
    /// `=>rN` leaves. Pins the generated-arm SHAPES (red-team F0 residual:
    /// don't just count groups). Repeated items across siblings (F5-1
    /// accept leaves / twins) render natively — position in the child list
    /// IS the emitted branch order.
    fn render(tree: &SpineTree) -> String {
        use std::fmt::Write as _;

        enum Task<'tree> {
            Visit(&'tree SpineTree),
            Text(&'static str),
        }

        fn write_item(out: &mut String, item: &SpineItem) {
            match item {
                SpineItem::Literal { text, .. } => {
                    write!(out, "L({text})").expect("writing into String cannot fail");
                },
                SpineItem::ParamParse { cat_src_idx, cur_bp } => {
                    write!(out, "P({cat_src_idx},{cur_bp})")
                        .expect("writing into String cannot fail");
                },
            }
        }

        let mut out = String::new();
        let mut tasks = vec![Task::Visit(tree)];
        while let Some(task) = tasks.pop() {
            match task {
                Task::Text(text) => out.push_str(text),
                Task::Visit(SpineTree::Leaf { item, member }) => {
                    write_item(&mut out, item);
                    write!(&mut out, "=>r{}", member.rule_idx)
                        .expect("writing into String cannot fail");
                },
                Task::Visit(SpineTree::Interior { item, children }) => {
                    write_item(&mut out, item);
                    out.push('[');
                    tasks.push(Task::Text("]"));
                    for (index, child) in children.iter().enumerate().rev() {
                        tasks.push(Task::Visit(child));
                        if index > 0 {
                            tasks.push(Task::Text(" "));
                        }
                    }
                },
            }
        }
        out
    }

    /// Forest rendering in the normative A1 root order — a single-root
    /// forest renders exactly as its root (the pre-F5-1 pin strings hold
    /// verbatim); multi-root forests join with ` ++ `.
    fn render_forest(roots: &[SpineTree]) -> String {
        roots.iter().map(render).collect::<Vec<_>>().join(" ++ ")
    }

    // ── tiny positive-AST builders for the synthetic witnesses (same idiom
    //    as grammar_generality_prop.rs) ─────────────────────────────────────

    fn id(s: &str) -> Ident {
        Ident::new(s, Span::call_site())
    }

    fn simple(name: &str, cat: &str) -> TermParam {
        TermParam::Simple {
            name: id(name),
            ty: TypeExpr::Base(id(cat)),
        }
    }

    fn simple_coll(name: &str, coll: CollectionType, elem: &str) -> TermParam {
        TermParam::Simple {
            name: id(name),
            ty: TypeExpr::Collection {
                coll_type: coll,
                element: Box::new(TypeExpr::Base(id(elem))),
            },
        }
    }

    fn param(name: &str) -> SyntaxExpr {
        SyntaxExpr::Param(id(name))
    }

    fn lit(s: &str) -> SyntaxExpr {
        SyntaxExpr::Literal(s.to_string())
    }

    fn sep(coll: &str, separator: &str) -> SyntaxExpr {
        SyntaxExpr::Op(mettail_ast::grammar::PatternOp::Sep {
            collection: id(coll),
            separator: separator.to_string(),
            source: None,
        })
    }

    fn jrule(label: &str, category: &str, tc: Vec<TermParam>, sp: Vec<SyntaxExpr>) -> GrammarRule {
        let (items, bindings) = convert_term_context_to_items(&tc);
        GrammarRule {
            items,
            bindings,
            term_context: Some(tc),
            syntax_pattern: Some(sp),
            ..rule_fixture(id(label), id(category))
        }
    }

    fn mk_language(name: &str, types: Vec<LangType>, terms: Vec<GrammarRule>) -> LanguageDef {
        LanguageDef {
            name: id(name),
            options: Default::default(),
            extends_names: Vec::new(),
            include_names: Vec::new(),
            mixin_names: Vec::new(),
            types,
            refinement_types: Vec::new(),
            token_defs: Vec::new(),
            mode_defs: Vec::new(),
            sync_constraints: Vec::new(),
            tree_invariants: Vec::new(),
            terms,
            equations: Vec::new(),
            rewrites: Vec::new(),
            logic: None,
            guard_config: None,
        }
    }

    fn lang_type(name: &str, native: Option<&str>) -> LangType {
        LangType {
            name: id(name),
            role: Default::default(),
            native_type: native.map(|t| syn::parse_str::<syn::Type>(t).expect("type parses")),
            collection_kind: None,
        }
    }

    // ═══════════════════════════════════════════════════════════════════════
    // The rholang `@`-cohort pins (F0 gate, plan §5).
    // ═══════════════════════════════════════════════════════════════════════

    /// Proc@ = 3 groups with 6/3/6 leaves: Nil {9,10,14,15,19,20} (incl. the
    /// two NULLARY members 14/15), Quoted {11,16,21}, Short {12,13,17,18,
    /// 22,23}. Rule indices are pinned against the generated WPDA_RULES
    /// table (labels asserted first, so drift fails loudly and precisely).
    ///
    /// ⚠ THESE INDICES ARE ABSOLUTE POSITIONS IN THE `Proc` RULE LIST, so any
    /// rule added or removed ANYWHERE ABOVE THEM shifts all of them. They were
    /// last re-derived on 2026-07-29, when deleting `PParInternal` (which sat
    /// at `Proc` index 3) shifted every index from 3 upward down by one. They
    /// were re-derived by DUMPING the regenerated rule list, not by
    /// decrementing the previous numbers — an arithmetic shortcut is right only
    /// until one pin moves for an unrelated reason. If you are updating them
    /// again, dump the list again; `rule_idx(&per_cat[0], "Label")` in this
    /// module is the helper that resolves a label to its current index.
    #[test]
    fn rholang_proc_at_cohort_pins_three_groups_6_3_6() {
        let def = rholang();
        let (categories, per_cat) = cats_per_cat(&def);
        assert_eq!(categories[0], "Proc", "Proc is the primary category");
        let name_src = src_idx(&categories, "Name");
        assert_eq!(name_src, 3, "Name src_idx pinned by WPDA_CATEGORIES");
        // WPDA_RULES parity for the 15-rule cohort.
        let pinned_labels = [
            (9u16, "POutputNil"),
            (10, "PPersistOutputNil"),
            (11, "POutputQuoted"),
            (12, "POutputShort"),
            (13, "PPersistOutputShort"),
            (14, "POutputNilEmpty"),
            (15, "PPersistOutputNilEmpty"),
            (16, "POutputQuotedEmpty"),
            (17, "POutputShortEmpty"),
            (18, "PPersistOutputShortEmpty"),
            (19, "POutputNil2Plus"),
            (20, "PPersistOutputNil2Plus"),
            (21, "POutputQuoted2Plus"),
            (22, "POutputShort2Plus"),
            (23, "PPersistOutputShort2Plus"),
        ];
        for (idx, label) in pinned_labels {
            assert_eq!(
                per_cat[0][idx as usize].label.to_string(),
                label,
                "Proc rule {idx} must be {label} (WPDA_RULES parity)",
            );
        }

        let model = build_prefix_factoring(&def, &categories, &per_cat);
        let proc_at = bucket(&model, 0, "@");
        assert_eq!(proc_at.cohort_size, 15, "the @-cohort has 15 members");
        assert_eq!(proc_at.groups.len(), 3, "Proc@ factors into exactly 3 groups");
        assert!(
            proc_at.ineligible.is_empty(),
            "no Proc@ group is F5-deferred: {:?}",
            proc_at.ineligible,
        );
        assert!(
            proc_at.singletons.is_empty(),
            "every Proc@ member joins a group: {:?}",
            proc_at.singletons,
        );

        let nil = &proc_at.groups[0];
        let quoted = &proc_at.groups[1];
        let short = &proc_at.groups[2];

        assert_eq!(nil.spine_id, SPINE_RULE_BASE);
        assert_eq!(quoted.spine_id, SPINE_RULE_BASE + 1);
        assert_eq!(short.spine_id, SPINE_RULE_BASE + 2);

        assert_eq!(nil.leaf_count(), 6);
        assert_eq!(quoted.leaf_count(), 3);
        assert_eq!(short.leaf_count(), 6);

        assert_eq!(nil.member_rule_idxs(), BTreeSet::from([9, 10, 14, 15, 19, 20]));
        assert_eq!(quoted.member_rule_idxs(), BTreeSet::from([11, 16, 21]));
        assert_eq!(short.member_rule_idxs(), BTreeSet::from([12, 13, 17, 18, 22, 23]));

        // Divergence-only cohorts stay SINGLE-ROOT forests (F5-1 invariant:
        // multiple roots require a root accept, which Proc@ has none of).
        for group in [nil, quoted, short] {
            assert_eq!(group.roots.len(), 1, "Proc@ groups are single-root");
        }

        // Group roots = the first post-trigger emitted-action shapes.
        assert!(
            matches!(nil.roots[0].item(), SpineItem::Literal { text, .. } if text == "Nil"),
            "Nil group root: {:?}",
            nil.roots[0].item(),
        );
        assert_eq!(
            quoted.roots[0].item(),
            &SpineItem::ParamParse { cat_src_idx: name_src, cur_bp: 0 },
            "Quoted group root pushes CategoryEntry(Name) at cur_bp 0",
        );
        // Red-team AV2 receipt: the spec-level `prefix(220)` on the Short
        // rules does NOT surface — the shared pos-1 action is
        // ReplaceAndPush{CategoryEntry(0), cur_bp: 0}, byte-equal across all
        // six members.
        assert_eq!(
            short.roots[0].item(),
            &SpineItem::ParamParse { cat_src_idx: 0, cur_bp: 0 },
            "Short group root pushes CategoryEntry(Proc) at cur_bp 0 (NOT 220)",
        );

        // BinderRule body categories are uniform per group.
        assert_eq!(nil.body_src_idx, 0, "Nil group bodies are Proc");
        assert_eq!(quoted.body_src_idx, name_src, "Quoted group bodies are Name");
        assert_eq!(short.body_src_idx, 0, "Short group bodies are Proc");
    }

    /// The divergence STRUCTURE (not just counts): Nil diverges at `!`/`!!`,
    /// then inside the parens `)`-vs-operand, then `)`-vs-`,`; Short is the
    /// same two-level `{!,!!}` × `( { ), PP { ), , } }` lattice over the
    /// shared leading Proc operand; Quoted is the single-`!` column.
    #[test]
    fn rholang_at_cohort_divergence_structure_pins() {
        let def = rholang();
        let (categories, per_cat) = cats_per_cat(&def);
        let model = build_prefix_factoring(&def, &categories, &per_cat);
        let proc_at = bucket(&model, 0, "@");
        let name_src = src_idx(&categories, "Name");

        assert_eq!(
            render_forest(&proc_at.groups[0].roots),
            "L(Nil)[L(!)[L(()[P(0,0)[L())=>r9 L(,)=>r19] L())=>r14]] \
             L(!!)[L(()[P(0,0)[L())=>r10 L(,)=>r20] L())=>r15]]]",
            "Nil group divergence structure",
        );
        assert_eq!(
            render_forest(&proc_at.groups[1].roots),
            format!("P({name_src},0)[L(!)[L(()[P(0,0)[L())=>r11 L(,)=>r21] L())=>r16]]]"),
            "Quoted group divergence structure",
        );
        assert_eq!(
            render_forest(&proc_at.groups[2].roots),
            "P(0,0)[L(!)[L(()[P(0,0)[L())=>r12 L(,)=>r22] L())=>r17]] \
             L(!!)[L(()[P(0,0)[L())=>r13 L(,)=>r23] L())=>r18]]]",
            "Short group divergence structure",
        );
    }

    /// Commit-coordinate pins (amendment A4): rule 14 = `POutputNilEmpty`
    /// (nullary — full `@ Nil ! (` spine shared, commit into the literal tail
    /// at sub_pos 4 = parts_len, the tail-complete pop-and-fire arm) and rule
    /// 19 = `POutputNil2Plus` (2Plus — commit at the `,` leaf into BinderRule
    /// pos 6, collection remainder in its own machinery); rule 9 =
    /// `POutputNil` as the no-remainder control.
    ///
    /// ⚠ THIS TEST WAS SILENTLY RETARGETED BY A RULE DELETION AND DID NOT
    /// FAIL (2026-07-29). It named rules 15/20/10; removing `PParInternal`
    /// from `Proc` index 3 shifted every later index down by one, so those
    /// three numbers came to select `PPersistOutputNilEmpty`,
    /// `PPersistOutputNil2Plus` and `PPersistOutputNil` — the PERSIST TWINS of
    /// the intended rules. Every assertion still passed, because a twin has
    /// the same kind, the same leaf edge, the same depth and the same commit
    /// shape. The test was green while testing rules its own name did not
    /// describe.
    ///
    /// That is the sharper hazard of an absolute rule index: the loud failure
    /// is the lucky case. The labels are now asserted FIRST, so a future shift
    /// reports as "rule 14 is X, expected POutputNilEmpty" instead of passing
    /// quietly on a neighbour.
    #[test]
    fn rholang_commit_coordinates_nullary_and_2plus() {
        let def = rholang();
        let (categories, per_cat) = cats_per_cat(&def);
        let model = build_prefix_factoring(&def, &categories, &per_cat);

        // ★ The anti-retarget guard: bind the indices to their LABELS before
        // using them as coordinates. Without this, a shift selects a twin and
        // every assertion below still holds.
        const NULLARY_IDX: u16 = 14;
        const TWO_PLUS_IDX: u16 = 19;
        const CONTROL_IDX: u16 = 9;
        for (idx, label) in [
            (NULLARY_IDX, "POutputNilEmpty"),
            (TWO_PLUS_IDX, "POutputNil2Plus"),
            (CONTROL_IDX, "POutputNil"),
        ] {
            assert_eq!(
                per_cat[0][idx as usize].label.to_string(),
                label,
                "rule {idx} must be {label} — if this fails the indices below have shifted \
                 and are now selecting a different rule (probably its persist twin)",
            );
        }

        let nil = &bucket(&model, 0, "@").groups[0];

        let (edge_nullary, m_nullary) = nil.leaf_for(NULLARY_IDX).expect("POutputNilEmpty leaf");
        assert_eq!(m_nullary.kind, MemberKind::Nullary);
        assert!(
            matches!(
                edge_nullary,
                SpineItem::Literal { text, required_top_cat: None } if text == ")"
            ),
            "POutputNilEmpty commits on the `)` leaf edge: {edge_nullary:?}",
        );
        assert_eq!(m_nullary.leaf_depth, 4, "spine consumed Nil ! ( ) for POutputNilEmpty",);
        assert_eq!(
            m_nullary.commit,
            MemberCommit::Nullary {
                rule_idx: NULLARY_IDX,
                completed_idx: 0,
                sub_pos: 4
            },
            "nullary commit lands at sub_pos == parts_len (tail complete)",
        );
        assert_eq!(
            m_nullary.pos_map,
            SpinePosMap::Nullary { sub_pos_at_depth: vec![0, 1, 2, 3, 4] },
        );
        assert!(!m_nullary.has_post_spine_remainder);

        let (edge_2plus, m_2plus) = nil.leaf_for(TWO_PLUS_IDX).expect("POutputNil2Plus leaf");
        assert_eq!(m_2plus.kind, MemberKind::Binder);
        assert!(
            matches!(edge_2plus, SpineItem::Literal { text, .. } if text == ","),
            "POutputNil2Plus commits on the `,` leaf edge: {edge_2plus:?}",
        );
        assert_eq!(m_2plus.leaf_depth, 5, "spine consumed Nil ! ( <a> , for POutputNil2Plus",);
        assert_eq!(
            m_2plus.commit,
            MemberCommit::Binder { rule_idx: TWO_PLUS_IDX, resume_pos: 6 },
            "2Plus commit resumes BinderRule at pos 6 (the collection slot)",
        );
        assert_eq!(m_2plus.pos_map, SpinePosMap::Binder { pos_at_depth: vec![1, 2, 3, 4, 5, 6] },);
        assert!(
            m_2plus.has_post_spine_remainder,
            "the 2Plus collection tail runs in the member's own machinery",
        );

        let (edge_control, m_control) = nil.leaf_for(CONTROL_IDX).expect("POutputNil leaf");
        assert!(matches!(edge_control, SpineItem::Literal { text, .. } if text == ")"));
        assert_eq!(
            m_control.commit,
            MemberCommit::Binder { rule_idx: CONTROL_IDX, resume_pos: 6 },
            "POutputNil's commit position IS its final-pos Pop → fire arm",
        );
        assert!(!m_control.has_post_spine_remainder);
    }

    /// Name@ and InputBind@ cohorts under the F0/legacy stance
    /// (`accept_continue == false`, pinned explicitly so this test holds at
    /// BOTH values of the `S1F5_ACCEPT_CONTINUE` const): Name@ carries
    /// NQuote (`@ ( p )`) and NQuoteNil (`@ Nil`) which diverge at the root
    /// (singletons; NQuoteShort `@ p` is a CrossCatPrefixUnary and never a
    /// member); InputBind@'s three rows share the `pat <-/<= n` spine but
    /// `InputBindQuoted` is a proper PREFIX of the query row — an interior
    /// accept-node — so the whole group defers. The F5-1 admission of this
    /// exact cohort is pinned by
    /// `rholang_inputbind_at_cohort_factors_with_accept_continue`; the
    /// const coupling by `inputbind_at_stance_follows_the_s1f5_const`.
    #[test]
    fn rholang_name_and_inputbind_at_cohorts_excluded_or_singleton() {
        let def = rholang();
        let (categories, per_cat) = cats_per_cat(&def);
        let model = build_prefix_factoring_with(&def, &categories, &per_cat, false);
        let name_src = src_idx(&categories, "Name");
        let ib_src = src_idx(&categories, "InputBind");

        let name_at = bucket(&model, name_src, "@");
        assert!(name_at.groups.is_empty(), "no factored Name@ group");
        assert!(name_at.ineligible.is_empty());
        assert_eq!(name_at.cohort_size, 2, "NQuote + NQuoteNil");
        let nquote = rule_idx(&per_cat[name_src as usize], "NQuote");
        let nquote_nil = rule_idx(&per_cat[name_src as usize], "NQuoteNil");
        for s in &name_at.singletons {
            assert_eq!(
                s.reason,
                SingletonReason::LoneRootChild,
                "Name@ members are root-divergent singletons: {s:?}",
            );
        }
        let singleton_idxs: BTreeSet<u16> = name_at.singletons.iter().map(|s| s.rule_idx).collect();
        assert_eq!(singleton_idxs, BTreeSet::from([nquote, nquote_nil]));

        let ib_at = bucket(&model, ib_src, "@");
        assert!(ib_at.groups.is_empty(), "no factored InputBind@ group in F0");
        assert_eq!(ib_at.ineligible.len(), 1, "one F5-deferred InputBind@ group");
        assert_eq!(ib_at.cohort_size, 3);
        let deferred = &ib_at.ineligible[0];
        assert_eq!(deferred.member_rule_idxs.len(), 3);
        let quoted = rule_idx(&per_cat[ib_src as usize], "InputBindQuoted");
        match &deferred.reason {
            IneligibleReason::InteriorAccept { accepting_rule_idxs } => {
                assert_eq!(
                    accepting_rule_idxs,
                    &vec![quoted],
                    "InputBindQuoted is the proper-prefix (interior accept) member",
                );
            },
            other => panic!("InputBind@ must defer on InteriorAccept, got {other:?}"),
        }
    }

    /// F5-1 — the ONLY real accept+continue cohort, admitted under
    /// `accept_continue == true` (explicit stance; green at both const
    /// values): rholang `(InputBind, "@")` = {InputBindQuotedQuery=2,
    /// InputBindQuoted=3 (the accept), InputBindQuotedPersistent=6} —
    /// index re-pin per plan §1/P1. Pins the sibling-leaf trie (the accept
    /// leaf SHARES its `P(Name)` edge item with the continuation subtree),
    /// the ★A1 normative child order (interior-continue FIRST, accept
    /// LAST), the A4 commit coordinates (the accept's resume_pos =
    /// positions.len()+1 = its final-pos Pop → fire arm), and the A2
    /// per-category spine-ordinal isolation (InputBind's first group takes
    /// 0xF800 in its OWN category; Proc@ ids unshifted).
    #[test]
    fn rholang_inputbind_at_cohort_factors_with_accept_continue() {
        let def = rholang();
        let (categories, per_cat) = cats_per_cat(&def);
        let ib_src = src_idx(&categories, "InputBind");
        let name_src = src_idx(&categories, "Name");
        let ib_rules = &per_cat[ib_src as usize];
        assert_eq!(rule_idx(ib_rules, "InputBindQuotedQuery"), 2, "P1 index re-pin");
        assert_eq!(rule_idx(ib_rules, "InputBindQuoted"), 3, "P1 index re-pin");
        assert_eq!(rule_idx(ib_rules, "InputBindQuotedPersistent"), 6, "P1 index re-pin");

        let model = build_prefix_factoring_with(&def, &categories, &per_cat, true);
        let ib_at = bucket(&model, ib_src, "@");
        assert_eq!(ib_at.cohort_size, 3);
        assert!(ib_at.ineligible.is_empty(), "the InteriorAccept deferral is absorbed");
        assert!(ib_at.singletons.is_empty());
        assert_eq!(ib_at.groups.len(), 1, "ONE accept+continue group");

        let group = &ib_at.groups[0];
        assert_eq!(group.spine_id, SPINE_RULE_BASE, "InputBind's FIRST per-category ordinal");
        assert_eq!(group.body_src_idx, 0, "the shared `pat` operand is Proc");
        assert_eq!(group.member_rule_idxs(), BTreeSet::from([2, 3, 6]));
        assert_eq!(group.leaf_count(), 3, "leaves ↔ members bijection incl. the accept");
        assert_eq!(group.roots.len(), 1, "no root accept — single-root forest");
        // The full sibling-leaf trie, ★A1 order pinned by position: the
        // `L(<-)` node lists the interior continuation BEFORE the r3 accept
        // leaf, both carrying the SAME `P(Name)` edge item.
        assert_eq!(
            render_forest(&group.roots),
            format!("P(0,0)[L(<-)[P({name_src},0)[L(!)=>r2] P({name_src},0)=>r3] L(<=)=>r6]"),
            "InputBind@ sibling-leaf trie (A1: remainder before accepts)",
        );

        // A4 commit coordinates. The accept (r3): a TRUE accept — untruncated,
        // total_positions == leaf_depth — so resume_pos = positions.len()+1 =
        // 4 = the member's existing final-pos Pop → fire arm.
        let (edge3, m3) = group.leaf_for(3).expect("rule 3 accept leaf");
        assert_eq!(
            edge3,
            &SpineItem::ParamParse { cat_src_idx: name_src, cur_bp: 0 },
            "the accept leaf's edge item IS the shared Name operand",
        );
        assert_eq!(m3.kind, MemberKind::Binder);
        assert_eq!(m3.leaf_depth, 3, "spine consumed pat <- n for rule 3");
        assert_eq!(m3.commit, MemberCommit::Binder { rule_idx: 3, resume_pos: 4 });
        assert_eq!(m3.pos_map, SpinePosMap::Binder { pos_at_depth: vec![1, 2, 3, 4] });
        assert!(!m3.has_post_spine_remainder, "a true accept has NO member-side remainder",);

        // r6: ordinary earliest-uniqueness leaf at the `L(<=)` divergence.
        let (edge6, m6) = group.leaf_for(6).expect("rule 6 leaf");
        assert!(matches!(edge6, SpineItem::Literal { text, .. } if text == "<="));
        assert_eq!(m6.leaf_depth, 2);
        assert_eq!(m6.commit, MemberCommit::Binder { rule_idx: 6, resume_pos: 3 });
        assert!(m6.has_post_spine_remainder, "the trailing `n` stays member-side");

        // r2: continues past the accept edge, committing on the `!` guard
        // (truncated at its `args.*sep(",")` collection).
        let (edge2, m2) = group.leaf_for(2).expect("rule 2 leaf");
        assert!(matches!(edge2, SpineItem::Literal { text, .. } if text == "!"));
        assert_eq!(m2.leaf_depth, 4);
        assert_eq!(m2.commit, MemberCommit::Binder { rule_idx: 2, resume_pos: 5 });
        assert!(m2.has_post_spine_remainder);

        // A2 — F0-eligible groups are untouched by the admission (per-
        // category ordinals; exclusions precede partition): the Proc@ trio
        // is byte-invariant across stances, ids unshifted.
        let legacy = build_prefix_factoring_with(&def, &categories, &per_cat, false);
        let proc_at_on = bucket(&model, 0, "@");
        let proc_at_off = bucket(&legacy, 0, "@");
        assert_eq!(proc_at_on.groups.len(), 3);
        for (on, off) in proc_at_on.groups.iter().zip(proc_at_off.groups.iter()) {
            assert_eq!(on.spine_id, off.spine_id, "Proc@ spine ids unshifted");
            assert_eq!(on.body_src_idx, off.body_src_idx);
            assert_eq!(
                render_forest(&on.roots),
                render_forest(&off.roots),
                "Proc@ tries byte-invariant across the F5-1 stances",
            );
        }
    }

    /// The const-following coupling (A3 discipline — green at BOTH stances):
    /// `build_prefix_factoring` == `build_prefix_factoring_with(const)`, and
    /// the InputBind@ disposition tracks `S1F5_ACCEPT_CONTINUE` exactly —
    /// grouped when on, InteriorAccept-deferred when off.
    #[test]
    fn inputbind_at_stance_follows_the_s1f5_const() {
        let s1f5 = crate::gen::runtime::wpda_codegen::forks::S1F5_ACCEPT_CONTINUE;
        let def = rholang();
        let (categories, per_cat) = cats_per_cat(&def);
        let ib_src = src_idx(&categories, "InputBind");
        let const_model = build_prefix_factoring(&def, &categories, &per_cat);
        let stance_model = build_prefix_factoring_with(&def, &categories, &per_cat, s1f5);
        let ib_const = bucket(&const_model, ib_src, "@");
        let ib_stance = bucket(&stance_model, ib_src, "@");
        assert_eq!(ib_const.groups.len(), ib_stance.groups.len());
        assert_eq!(ib_const.ineligible.len(), ib_stance.ineligible.len());
        if s1f5 {
            assert_eq!(ib_const.groups.len(), 1, "const ON ⇒ InputBind@ grouped");
            assert!(ib_const.ineligible.is_empty());
            // #152: the members are NAMED, not numbered. A bare `[2, 3, 6]` here would keep
            // passing after a rule was added or removed above them while describing three
            // different rules — the failure mode that hit
            // `rholang_commit_coordinates_nullary_and_2plus`.
            let ib_rules = &per_cat[ib_src as usize];
            assert_eq!(
                ib_const.groups[0].member_rule_idxs(),
                BTreeSet::from([
                    rule_idx(ib_rules, "InputBindQuotedQuery"),
                    rule_idx(ib_rules, "InputBindQuoted"),
                    rule_idx(ib_rules, "InputBindQuotedPersistent"),
                ]),
                "the InputBind@ cohort is exactly the three quoted binds",
            );
        } else {
            assert!(ib_const.groups.is_empty(), "const OFF ⇒ InputBind@ deferred");
            assert_eq!(ib_const.ineligible.len(), 1);
            assert!(matches!(
                ib_const.ineligible[0].reason,
                IneligibleReason::InteriorAccept { .. },
            ));
        }
    }

    /// ★A2 receipts — Rholang: the binary object casts (`int(a,w) : Proc`
    /// family) are numeric-cast-adapter rows and excluded; the `@`-cohort
    /// sends (incl. the arity-1 `POutputNil`/`POutputQuotedEmpty`) are NOT
    /// cast rows and stay grouped (pinned above).
    #[test]
    fn rholang_cast_rules_excluded_from_factoring_a2() {
        let def = rholang();
        let (categories, per_cat) = cats_per_cat(&def);
        let model = build_prefix_factoring(&def, &categories, &per_cat);

        for label in ["IntBinProc", "UIntBinProc", "FloatBinProc", "FixedBinProc"] {
            let idx = rule_idx(&per_cat[0], label);
            let trigger = match per_cat[0][idx as usize]
                .syntax_pattern
                .as_ref()
                .and_then(|sp| sp.first())
            {
                Some(SyntaxExpr::Literal(t)) => t.clone(),
                other => panic!("{label} leads with a literal, got {other:?}"),
            };
            let b = bucket(&model, 0, &trigger);
            let s = b
                .singletons
                .iter()
                .find(|s| s.rule_idx == idx)
                .unwrap_or_else(|| panic!("{label} must be a singleton in {trigger:?}"));
            assert_eq!(
                s.reason,
                SingletonReason::CastMachinery,
                "{label} is a numeric-cast-adapter row (A2)",
            );
            assert!(
                b.groups
                    .iter()
                    .all(|g| !g.member_rule_idxs().contains(&idx)),
                "{label} must not ride a spine",
            );
        }

        // Receipts to stderr for the campaign log.
        eprintln!("A2 cast-machinery exclusion receipts (rholang):");
        for cat in &model {
            for b in &cat.buckets {
                for s in &b.singletons {
                    if s.reason == SingletonReason::CastMachinery {
                        eprintln!(
                            "  cat {} bucket {:?}: rule {} ({})",
                            cat.category_src_idx,
                            b.leading_literal,
                            s.rule_idx,
                            per_cat[cat.category_src_idx as usize][s.rule_idx as usize].label,
                        );
                    }
                }
            }
        }
    }

    /// ★A2 receipts — Calculator: the flagship RC-B casts (`int(<Bool>)` /
    /// `int(<Float>)` / `int(<Str>)`), the same-cat `IntId` (`int(<Int>)`,
    /// a numeric-domain wrapper row) AND the binary object cast `IntBin`
    /// (`int(a, w)` — CastMachinery via `recognize_cast_fold` clause (b);
    /// delta red-team A-3: the fifth `(Int, "int")` PrefixDispatch fork
    /// branch) are all excluded, dissolving the (Int, "int") bucket into
    /// singletons — `int(...)` NEVER rides a spine, so
    /// `try_park_direct_prefix_cast_waiter` keeps seeing real rule ids AND
    /// the R-D budget pin (`actual = 5` @languages/tests/calculator.rs:674,
    /// the PrefixDispatch fork width) survives S1-ON untouched. The
    /// (Float, "float") bucket is pinned the same way (A-3: the SECOND
    /// budget test — `float(float(10,64),64)`, `actual > budget` — was
    /// half-unpinned without it).
    #[test]
    fn calculator_cast_rules_excluded_from_factoring_a2() {
        let def = calculator();
        let (categories, per_cat) = cats_per_cat(&def);
        let model = build_prefix_factoring(&def, &categories, &per_cat);
        let int_src = src_idx(&categories, "Int");

        let int_bucket = bucket(&model, int_src, "int");
        assert!(
            int_bucket.groups.is_empty(),
            "the (Int, \"int\") cohort must not factor (all cast rows): {:?}",
            int_bucket
                .groups
                .iter()
                .map(|g| g.member_rule_idxs())
                .collect::<Vec<_>>(),
        );
        for label in ["FloatToInt", "BoolToInt", "StrToInt", "IntId", "IntBin"] {
            let idx = rule_idx(&per_cat[int_src as usize], label);
            let s = int_bucket
                .singletons
                .iter()
                .find(|s| s.rule_idx == idx)
                .unwrap_or_else(|| panic!("{label} present as an (Int, \"int\") singleton"));
            assert_eq!(
                s.reason,
                SingletonReason::CastMachinery,
                "{label} participates in cast machinery (A2)",
            );
        }

        // A-3 (delta red-team, 2026-07-12): the (Float, "float") cohort —
        // IntToFloat / BoolToFloat / StrToFloat / FloatId / FloatBin, 5/5
        // CastMachinery — must dissolve into singletons exactly like Int's,
        // protecting the second calculator budget test's fan width.
        let float_src = src_idx(&categories, "Float");
        let float_bucket = bucket(&model, float_src, "float");
        assert!(
            float_bucket.groups.is_empty(),
            "the (Float, \"float\") cohort must not factor (all cast rows): {:?}",
            float_bucket
                .groups
                .iter()
                .map(|g| g.member_rule_idxs())
                .collect::<Vec<_>>(),
        );
        for label in ["IntToFloat", "BoolToFloat", "StrToFloat", "FloatId", "FloatBin"] {
            let idx = rule_idx(&per_cat[float_src as usize], label);
            let s = float_bucket
                .singletons
                .iter()
                .find(|s| s.rule_idx == idx)
                .unwrap_or_else(|| panic!("{label} present as a (Float, \"float\") singleton"));
            assert_eq!(
                s.reason,
                SingletonReason::CastMachinery,
                "{label} participates in cast machinery (A2)",
            );
        }

        eprintln!("A2 cast-machinery exclusion receipts (calculator):");
        for cat in &model {
            for b in &cat.buckets {
                for s in &b.singletons {
                    if s.reason == SingletonReason::CastMachinery {
                        eprintln!(
                            "  cat {} bucket {:?}: rule {} ({})",
                            cat.category_src_idx,
                            b.leading_literal,
                            s.rule_idx,
                            per_cat[cat.category_src_idx as usize][s.rule_idx as usize].label,
                        );
                    }
                }
            }
        }
    }

    /// Rholang `PNew` (`new xs... in { p }` — the official-Rholang paren-free
    /// declaration list, 2026-07-24): it stays an UNFACTORED SINGLETON in the
    /// `new` bucket, exactly as before the paren-drop. No sibling shares the
    /// `new` trigger, so it never factors.
    ///
    /// ★ The singleton REASON moved, and the move is the paren-drop's direct
    /// consequence:
    ///
    /// | production | post-trigger items | mergeable prefix | reason |
    /// |---|---|---|---|
    /// | before | `"(" · xs.*sep · ")" · "in" · "{" · p · "}"` | the lone `"("`, then the binder-list terminates mergeability | [`SingletonReason::LoneRootChild`] |
    /// | after | `xs.*sep · "in" · "{" · p · "}"` | EMPTY — the binder-list is now item 0 | [`SingletonReason::EmptySequence`] |
    ///
    /// [`SingletonReason::EmptySequence`]'s own doc names this exact case ("its
    /// first item already terminates mergeability — e.g. Rholang `PNew`'s
    /// leading binder-list"), so the new label is the semantically correct one
    /// rather than a weakened assertion. The EMISSION is unchanged: still a
    /// singleton, still committing at the trigger, still zero groups.
    #[test]
    fn rholang_pnew_stays_a_singleton() {
        let def = rholang();
        let (categories, per_cat) = cats_per_cat(&def);
        let model = build_prefix_factoring(&def, &categories, &per_cat);
        let pnew = rule_idx(&per_cat[0], "PNew");
        let new_bucket = bucket(&model, 0, "new");
        assert!(new_bucket.groups.is_empty(), "PNew never factors");
        let s = new_bucket
            .singletons
            .iter()
            .find(|s| s.rule_idx == pnew)
            .expect("PNew is a singleton");
        assert_eq!(
            s.reason,
            SingletonReason::EmptySequence,
            "the paren-free `new` puts the binder-list at post-trigger item 0, so the \
             mergeable prefix is empty",
        );
    }

    /// The emission-effective partition under the SHIPPED const
    /// (`S1_FACTORING == true` — the F4 flip, 2026-07-12) IS the factoring
    /// model: `emission_partition` no longer degenerates to the identity but
    /// returns `build_prefix_factoring`'s groups/singletons/ineligible
    /// verbatim. This is the ON-stance twin of the retired F0/F1 dormancy
    /// pin `emission_partition_is_identity_while_const_off` (which asserted
    /// `!S1_FACTORING` + all-`FactoringDisabled`); the two pins were
    /// designed to flip WITH the F4 commit. The kill-switch const is
    /// RETAINED — one `false` revert restores the dormant stance (and this
    /// pin plus its emission twin below flip back with it).
    #[test]
    fn emission_partition_is_the_factoring_model_while_const_on() {
        assert!(
            crate::gen::runtime::wpda_codegen::forks::S1_FACTORING,
            "F4 ships with the factoring const ON (kill-switch retained)",
        );
        let def = rholang();
        let (categories, per_cat) = cats_per_cat(&def);
        let effective = emission_partition(&def, &categories, &per_cat);
        let model = build_prefix_factoring(&def, &categories, &per_cat);
        assert_eq!(effective.len(), model.len());
        for (e_cat, m_cat) in effective.iter().zip(model.iter()) {
            assert_eq!(e_cat.category_src_idx, m_cat.category_src_idx);
            assert_eq!(e_cat.buckets.len(), m_cat.buckets.len());
            for (eb, mb) in e_cat.buckets.iter().zip(m_cat.buckets.iter()) {
                assert_eq!(eb.leading_literal, mb.leading_literal);
                assert_eq!(eb.cohort_size, mb.cohort_size);
                assert_eq!(eb.groups.len(), mb.groups.len());
                for (eg, mg) in eb.groups.iter().zip(mb.groups.iter()) {
                    assert_eq!(eg.spine_id, mg.spine_id);
                    assert_eq!(eg.body_src_idx, mg.body_src_idx);
                    assert_eq!(eg.member_rule_idxs(), mg.member_rule_idxs());
                    assert_eq!(eg.leaf_count(), mg.leaf_count());
                }
                assert_eq!(eb.singletons.len(), mb.singletons.len());
                for (es, ms_) in eb.singletons.iter().zip(mb.singletons.iter()) {
                    assert_eq!(es.rule_idx, ms_.rule_idx);
                    assert_eq!(es.reason, ms_.reason);
                }
                assert_eq!(eb.ineligible.len(), mb.ineligible.len());
                // The ON const makes the disabled reason unreachable.
                for s in &eb.singletons {
                    assert_ne!(
                        s.reason,
                        SingletonReason::FactoringDisabled,
                        "const ON ⇒ FactoringDisabled is unreachable",
                    );
                }
            }
        }
        // The rholang @-cohort ships factored: 3 groups, 6/3/6 leaves
        // (the F0-pinned trie, now emission-effective).
        let at = bucket(&effective, 0, "@");
        assert_eq!(at.groups.len(), 3);
        assert_eq!(at.groups[0].leaf_count(), 6);
        assert_eq!(at.groups[1].leaf_count(), 3);
        assert_eq!(at.groups[2].leaf_count(), 6);
    }

    /// ★A9: the spine id space sits below RECOVERY_BASE and u16::MAX with
    /// generous headroom (0x600 groups per category).
    #[test]
    fn spine_id_space_clear_of_recovery_base_a9() {
        assert!(SPINE_RULE_BASE < crate::gen::runtime::wpda_codegen::forks::RECOVERY_BASE);
        assert_eq!(
            crate::gen::runtime::wpda_codegen::forks::RECOVERY_BASE - SPINE_RULE_BASE,
            0x600,
            "1536 spine ids per category before the A9 assert fires",
        );
    }

    // ═══════════════════════════════════════════════════════════════════════
    // Synthetic eligibility witnesses (non-rholang alphabet).
    // ═══════════════════════════════════════════════════════════════════════

    fn expr_num_types() -> Vec<LangType> {
        vec![lang_type("Expr", None), lang_type("Tee", None)]
    }

    /// Red-team AV2 gap (a): the trie alphabet spans BOTH classifier sources
    /// — a NullaryLiteralRun member (`unit « »`) merges with a BinderPrefix
    /// member (`unit « a »`) on the shared `«` literal and commits with
    /// TYPED coordinates on each side of the divergence.
    #[test]
    fn nullary_and_binder_members_merge_across_classifier_sources() {
        let lang = mk_language(
            "MixedSrc",
            expr_num_types(),
            vec![
                jrule("NUnit", "Expr", vec![], vec![lit("unit"), lit("«"), lit("»")]),
                jrule(
                    "BUnit",
                    "Expr",
                    vec![simple("a", "Tee")],
                    vec![lit("unit"), lit("«"), param("a"), lit("»")],
                ),
                // Inhabit Tee so classifiers see a live category.
                jrule("TAtom", "Tee", vec![], vec![lit("tatom")]),
            ],
        );
        let (categories, per_cat) = cats_per_cat(&lang);
        let model = build_prefix_factoring(&lang, &categories, &per_cat);
        let b = bucket(&model, 0, "unit");
        assert_eq!(b.cohort_size, 2);
        assert_eq!(b.groups.len(), 1);
        let g = &b.groups[0];
        let tee_src = src_idx(&categories, "Tee");
        assert_eq!(
            render_forest(&g.roots),
            format!("L(«)[L(»)=>r0 P({tee_src},0)=>r1]"),
            "one shared literal edge, then nullary-vs-binder divergence",
        );
        let (_, nullary) = g.leaf_for(0).expect("nullary leaf");
        assert_eq!(
            nullary.commit,
            MemberCommit::Nullary {
                rule_idx: 0,
                completed_idx: 0,
                sub_pos: 2
            },
        );
        let (_, binder) = g.leaf_for(1).expect("binder leaf");
        assert_eq!(binder.commit, MemberCommit::Binder { rule_idx: 1, resume_pos: 3 });
        assert!(binder.has_post_spine_remainder, "the trailing » stays member-side");
    }

    /// The PrefixAccept synthetic (plan P3(a)): Short `quo « a` is a proper
    /// prefix of Long `quo « a »` — the minimal interior-accept pair.
    fn prefix_accept_lang() -> LanguageDef {
        mk_language(
            "PrefixAccept",
            expr_num_types(),
            vec![
                jrule(
                    "Short",
                    "Expr",
                    vec![simple("a", "Tee")],
                    vec![lit("quo"), lit("«"), param("a")],
                ),
                jrule(
                    "Long",
                    "Expr",
                    vec![simple("a", "Tee")],
                    vec![lit("quo"), lit("«"), param("a"), lit("»")],
                ),
                jrule("TAtom", "Tee", vec![], vec![lit("tatom")]),
            ],
        )
    }

    /// A proper-prefix member (interior accept-node) defers the WHOLE group
    /// under the F0 stance (`accept_continue == false` — explicit, so this
    /// holds at both const values), preserving today's emission for all
    /// members.
    #[test]
    fn interior_accept_defers_group_to_f5() {
        let lang = prefix_accept_lang();
        let (categories, per_cat) = cats_per_cat(&lang);
        let model = build_prefix_factoring_with(&lang, &categories, &per_cat, false);
        let b = bucket(&model, 0, "quo");
        assert!(b.groups.is_empty());
        assert_eq!(b.ineligible.len(), 1);
        assert!(matches!(
            &b.ineligible[0].reason,
            IneligibleReason::InteriorAccept { accepting_rule_idxs } if accepting_rule_idxs == &vec![0],
        ));
    }

    /// F5-1 ON stance of the same pair: the exhausted Short member becomes a
    /// SIBLING LEAF sharing the `P(Tee)` edge item with Long's continuation
    /// subtree — ★A1 order (interior first, accept last), the true-accept
    /// commit arithmetic (resume_pos = positions.len()+1), and the
    /// leaves ↔ members bijection.
    #[test]
    fn interior_accept_becomes_sibling_leaf_with_accept_continue() {
        let lang = prefix_accept_lang();
        let (categories, per_cat) = cats_per_cat(&lang);
        let model = build_prefix_factoring_with(&lang, &categories, &per_cat, true);
        let b = bucket(&model, 0, "quo");
        assert!(b.ineligible.is_empty(), "the deferral is absorbed");
        assert_eq!(b.groups.len(), 1);
        let g = &b.groups[0];
        let tee_src = src_idx(&categories, "Tee");
        assert_eq!(g.member_rule_idxs(), BTreeSet::from([0, 1]));
        assert_eq!(g.roots.len(), 1, "the accept is at depth 2 — no root accept");
        assert_eq!(
            render_forest(&g.roots),
            format!("L(«)[P({tee_src},0)[L(»)=>r1] P({tee_src},0)=>r0]"),
            "sibling-leaf trie: continuation subtree FIRST, accept LAST (A1)",
        );
        let (edge0, short) = g.leaf_for(0).expect("the Short accept leaf");
        assert_eq!(edge0, &SpineItem::ParamParse { cat_src_idx: tee_src, cur_bp: 0 });
        assert_eq!(short.leaf_depth, 2);
        assert_eq!(
            short.commit,
            MemberCommit::Binder { rule_idx: 0, resume_pos: 3 },
            "true accept: resume_pos = positions.len()+1 = the final-pos Pop arm",
        );
        assert!(!short.has_post_spine_remainder);
        let (_, long) = g.leaf_for(1).expect("the Long leaf");
        assert_eq!(long.commit, MemberCommit::Binder { rule_idx: 1, resume_pos: 4 });
        assert!(!long.has_post_spine_remainder, "Long's » IS its last item");
    }

    /// F5-1 root accept (multi-root forest): a nullary member whose whole
    /// item list is the root edge (`quo «` inside `quo « »`) becomes a LEAF
    /// ROOT — the pre-root arm itself becomes the accept fork. The nullary
    /// accept commits tail-complete (`sub_pos == parts_len`).
    #[test]
    fn root_accept_yields_multi_root_forest() {
        let lang = mk_language(
            "RootAccept",
            expr_num_types(),
            vec![
                jrule("TShort", "Expr", vec![], vec![lit("quo"), lit("«")]),
                jrule("TLong", "Expr", vec![], vec![lit("quo"), lit("«"), lit("»")]),
            ],
        );
        let (categories, per_cat) = cats_per_cat(&lang);
        // The F0 stance defers on the same pair (both-stance dormancy pin).
        let legacy = build_prefix_factoring_with(&lang, &categories, &per_cat, false);
        let lb = bucket(&legacy, 0, "quo");
        assert!(lb.groups.is_empty());
        assert!(matches!(
            &lb.ineligible[0].reason,
            IneligibleReason::InteriorAccept { accepting_rule_idxs } if accepting_rule_idxs == &vec![0],
        ));

        let model = build_prefix_factoring_with(&lang, &categories, &per_cat, true);
        let b = bucket(&model, 0, "quo");
        assert!(b.ineligible.is_empty());
        assert_eq!(b.groups.len(), 1);
        let g = &b.groups[0];
        assert_eq!(g.roots.len(), 2, "root accept ⇒ MULTI-ROOT forest");
        assert_eq!(
            render_forest(&g.roots),
            "L(«)[L(»)=>r1] ++ L(«)=>r0",
            "A1 at the roots: the remainder tree FIRST, the accept root LAST",
        );
        let (edge0, short) = g.leaf_for(0).expect("the TShort accept root");
        assert!(
            matches!(edge0, SpineItem::Literal { text, required_top_cat: None } if text == "«")
        );
        assert_eq!(short.kind, MemberKind::Nullary);
        assert_eq!(
            short.commit,
            MemberCommit::Nullary {
                rule_idx: 0,
                completed_idx: 0,
                sub_pos: 1
            },
            "nullary accept lands tail-complete (sub_pos == parts_len == 1)",
        );
        assert!(!short.has_post_spine_remainder);
        // The all-nullary group carries the owning category as body.
        assert_eq!(g.body_src_idx, 0);
    }

    /// F5-1 truncated accept (collection tail): a member CUT at its
    /// collection whose cut prefix exhausts at an interior node commits at
    /// its own MID-RULE arm (the rule-20 precedent) with
    /// `has_post_spine_remainder` set.
    #[test]
    fn truncated_accept_commits_mid_rule_with_remainder() {
        let lang = mk_language(
            "TruncAccept",
            expr_num_types(),
            vec![
                jrule(
                    "WithColl",
                    "Expr",
                    vec![simple("t", "Tee"), simple_coll("xs", CollectionType::Vec, "Tee")],
                    vec![lit("quo"), lit("«"), param("t"), sep("xs", ","), lit("»")],
                ),
                jrule(
                    "Plain",
                    "Expr",
                    vec![simple("t", "Tee"), simple("u", "Tee")],
                    vec![lit("quo"), lit("«"), param("t"), lit("·"), param("u")],
                ),
                jrule("TAtom", "Tee", vec![], vec![lit("tatom")]),
            ],
        );
        let (categories, per_cat) = cats_per_cat(&lang);
        let model = build_prefix_factoring_with(&lang, &categories, &per_cat, true);
        let b = bucket(&model, 0, "quo");
        assert!(b.ineligible.is_empty());
        assert_eq!(b.groups.len(), 1);
        let g = &b.groups[0];
        let tee_src = src_idx(&categories, "Tee");
        assert_eq!(
            render_forest(&g.roots),
            format!("L(«)[P({tee_src},0)[L(·)=>r1] P({tee_src},0)=>r0]"),
        );
        let (_, with_coll) = g.leaf_for(0).expect("the truncated accept leaf");
        assert_eq!(with_coll.leaf_depth, 2, "cut prefix « Tee exhausted at depth 2");
        assert_eq!(
            with_coll.commit,
            MemberCommit::Binder { rule_idx: 0, resume_pos: 3 },
            "truncated accept resumes at its OWN collection arm (mid-rule)",
        );
        assert!(
            with_coll.has_post_spine_remainder,
            "the collection tail runs in the member's own machinery",
        );
    }

    /// Red-team F-10: all-twins parts return an accepts-only forest — never
    /// `Interior { children: [] }`. Both shapes pinned: twins at the ROOT
    /// (an all-leaf multi-root forest — the pre-root arm is all commits) and
    /// twins spliced deeper (leaf children repeating an item under one
    /// interior node). Under the F0 stance both pairs defer with BOTH
    /// members listed as accepting.
    #[test]
    fn all_twins_part_yields_accepts_only_forest() {
        // Root-level twins: two nullary rules with the identical `quo «`.
        let root_twins = mk_language(
            "RootTwins",
            expr_num_types(),
            vec![
                jrule("T1", "Expr", vec![], vec![lit("quo"), lit("«")]),
                jrule("T2", "Expr", vec![], vec![lit("quo"), lit("«")]),
            ],
        );
        let (categories, per_cat) = cats_per_cat(&root_twins);
        let legacy = build_prefix_factoring_with(&root_twins, &categories, &per_cat, false);
        let lb = bucket(&legacy, 0, "quo");
        assert!(matches!(
            &lb.ineligible[0].reason,
            IneligibleReason::InteriorAccept { accepting_rule_idxs }
                if accepting_rule_idxs == &vec![0, 1],
        ));
        let model = build_prefix_factoring_with(&root_twins, &categories, &per_cat, true);
        let b = bucket(&model, 0, "quo");
        assert_eq!(b.groups.len(), 1);
        let g = &b.groups[0];
        assert_eq!(g.roots.len(), 2, "accepts-only forest at the root");
        assert!(
            g.roots.iter().all(|r| matches!(r, SpineTree::Leaf { .. })),
            "never Interior {{ children: [] }} — every root is an accept leaf",
        );
        assert_eq!(render_forest(&g.roots), "L(«)=>r0 ++ L(«)=>r1");
        assert_eq!(g.leaf_count(), 2);

        // Spliced twins: two binder rules with the identical `quo « a`.
        let spliced_twins = mk_language(
            "SplicedTwins",
            expr_num_types(),
            vec![
                jrule(
                    "S1",
                    "Expr",
                    vec![simple("a", "Tee")],
                    vec![lit("quo"), lit("«"), param("a")],
                ),
                jrule(
                    "S2",
                    "Expr",
                    vec![simple("b", "Tee")],
                    vec![lit("quo"), lit("«"), param("b")],
                ),
                jrule("TAtom", "Tee", vec![], vec![lit("tatom")]),
            ],
        );
        let (categories, per_cat) = cats_per_cat(&spliced_twins);
        let model = build_prefix_factoring_with(&spliced_twins, &categories, &per_cat, true);
        let b = bucket(&model, 0, "quo");
        assert_eq!(b.groups.len(), 1);
        let g = &b.groups[0];
        let tee_src = src_idx(&categories, "Tee");
        assert_eq!(g.roots.len(), 1);
        assert_eq!(
            render_forest(&g.roots),
            format!("L(«)[P({tee_src},0)=>r0 P({tee_src},0)=>r1]"),
            "twin accept leaves REPEAT their edge item under one interior node",
        );
        assert_eq!(g.leaf_count(), 2, "leaf per member holds for twins");
    }

    /// A collection item terminates mergeability LEAF-SIDE only: the member
    /// still shares the pre-collection spine and commits at its divergence
    /// leaf with the collection remainder in its own machinery.
    #[test]
    fn collection_item_terminates_mergeability_leaf_side_only() {
        let lang = mk_language(
            "CollTail",
            expr_num_types(),
            vec![
                jrule(
                    "WithColl",
                    "Expr",
                    vec![simple("t", "Tee"), simple_coll("xs", CollectionType::Vec, "Tee")],
                    vec![lit("quo"), lit("«"), param("t"), lit("·"), sep("xs", ","), lit("»")],
                ),
                jrule(
                    "Plain",
                    "Expr",
                    vec![simple("t", "Tee")],
                    vec![lit("quo"), lit("«"), param("t"), lit("»")],
                ),
                jrule("TAtom", "Tee", vec![], vec![lit("tatom")]),
            ],
        );
        let (categories, per_cat) = cats_per_cat(&lang);
        let model = build_prefix_factoring(&lang, &categories, &per_cat);
        let b = bucket(&model, 0, "quo");
        assert_eq!(b.groups.len(), 1, "shared « + Tee spine factors");
        let g = &b.groups[0];
        let tee_src = src_idx(&categories, "Tee");
        assert_eq!(render_forest(&g.roots), format!("L(«)[P({tee_src},0)[L(·)=>r0 L(»)=>r1]]"),);
        let (_, with_coll) = g.leaf_for(0).expect("collection member leaf");
        assert!(
            with_coll.has_post_spine_remainder,
            "the collection tail is member-side (never a spine edge)",
        );
        assert_eq!(with_coll.commit, MemberCommit::Binder { rule_idx: 0, resume_pos: 4 });
    }

    /// Red-team AV2 gap (b): binder members disagreeing on the initial
    /// BinderRule body category make the spine state ill-defined — the
    /// group is deferred with NonUniformBodySrc.
    #[test]
    fn non_uniform_body_src_defers_group() {
        // Both operand categories are NON-native (a native source would be
        // A2-excluded as a numeric-domain wrapper before grouping — that
        // path is covered by the calculator receipts test).
        let lang = mk_language(
            "BodySplit",
            vec![lang_type("Expr", None), lang_type("Tee", None), lang_type("Zed", None)],
            vec![
                jrule(
                    "FromTee",
                    "Expr",
                    vec![simple("a", "Tee")],
                    vec![lit("quo"), lit("«"), param("a"), lit("»")],
                ),
                jrule(
                    "FromZed",
                    "Expr",
                    vec![simple("z", "Zed")],
                    vec![lit("quo"), lit("«"), param("z"), lit("»")],
                ),
                jrule("TAtom", "Tee", vec![], vec![lit("tatom")]),
                jrule("ZAtom", "Zed", vec![], vec![lit("zatom")]),
            ],
        );
        let (categories, per_cat) = cats_per_cat(&lang);
        let model = build_prefix_factoring(&lang, &categories, &per_cat);
        let b = bucket(&model, 0, "quo");
        assert!(b.groups.is_empty());
        assert_eq!(b.ineligible.len(), 1);
        assert!(matches!(
            &b.ineligible[0].reason,
            IneligibleReason::NonUniformBodySrc { body_src_idxs } if body_src_idxs.len() == 2,
        ));
    }

    /// `binder_items` truncation semantics on a hand-built position list:
    /// a leading binder-list yields an EMPTY mergeable sequence.
    #[test]
    fn binder_items_cut_at_first_non_mergeable_position() {
        let positions = vec![BinderPosition::BinderListLoop {
            separator: ",".to_string(),
            close: ".".to_string(),
            inner_positions: vec![BinderPosition::BinderIdent],
            collection_param_cat: None,
            allow_empty: true,
            allow_multi: true,
            slot_idx: 0,
        }];
        let categories = vec!["Expr".to_string()];
        let bp = std::collections::HashMap::new();
        let (items, truncated) = binder_items(&positions, 0, 0, &categories, &bp);
        assert!(items.is_empty());
        assert!(truncated);
    }

    // ═══════════════════════════════════════════════════════════════════════
    // F1 emission pins (2026-07-12). The ON-shape pins go through
    // `build_spine_emission_from(build_prefix_factoring(..))` so the tree
    // keeps `S1_FACTORING = false` (dormant-const discipline) while the
    // emission logic is exercised at full strength.
    // ═══════════════════════════════════════════════════════════════════════

    /// Whitespace-insensitive TokenStream text (token spacing in
    /// `TokenStream::to_string` is not load-bearing).
    fn shared_transition_body(name: &str) -> String {
        let source = syn::parse_file(include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../prattail/src/wpda_transitions/factoring.rs",
        )))
        .expect("shared factoring source parses");
        let body = source
            .items
            .into_iter()
            .find_map(|item| match item {
                syn::Item::Fn(function) if function.sig.ident == name => Some(function.block),
                _ => None,
            })
            .expect("original factoring transition body exists");
        normalized(&quote! { #body })
    }

    fn normalized(ts: &proc_macro2::TokenStream) -> String {
        ts.to_string()
            .chars()
            .filter(|c| !c.is_whitespace())
            .collect()
    }

    /// The window of `s` between `from` (inclusive of content after it) and
    /// the next occurrence of `to` (or the end).
    fn window<'s>(s: &'s str, from: &str, to: &str) -> &'s str {
        let start = s.find(from).unwrap_or_else(|| panic!("{from} present"));
        let rest = &s[start + from.len()..];
        match rest.find(to) {
            Some(end) => &rest[..end],
            None => rest,
        }
    }

    /// The F4 flip stance expressed on the F1 bundle: with the shipped
    /// `S1_FACTORING == true` (2026-07-12), `build_spine_emission` (through
    /// `emission_partition`) is LIVE — the const-gated bundle carries the
    /// groups and is byte-identical to the explicit-model bundle
    /// (`build_spine_emission_from(build_prefix_factoring(..))`), so every
    /// wired consumer (prefix.rs multi-branch fork, binder.rs match,
    /// kind_dispatch lex-alt surface, the engine_impl preludes/overrides,
    /// the forks.rs weight wrap) emits the FACTORED engine. ON-stance twin
    /// of the retired F1 dormancy pin `spine_emission_off_is_inert_while_
    /// const_off` (designed to flip WITH the F4 commit); the kill-switch
    /// const is retained — one `false` revert restores byte-identical
    /// dormant emission and flips this pin back.
    #[test]
    fn spine_emission_live_while_const_on() {
        assert!(
            crate::gen::runtime::wpda_codegen::forks::S1_FACTORING,
            "F4 ships with the factoring const ON (kill-switch retained)",
        );
        let def = rholang();
        let (categories, per_cat) = cats_per_cat(&def);
        let gated = build_spine_emission(&def, &categories, &per_cat);
        assert!(gated.any_groups(), "const ON ⇒ the factored emission is LIVE");
        assert!(!gated.binder_arms.is_empty());
        assert!(!gated.trigger_spine_owner_fn.is_empty());
        assert!(!gated.spine_members_fn.is_empty());
        assert!(!gated.action_for_prelude.is_empty());
        assert!(!gated.leading_trigger_prelude.is_empty());
        // A3-corrected (F4 round-1 RED-1; f5_accept_continue_plan §RED-TEAM
        // item 3, 2026-07-12): min_terminal_span rows are emitted exactly
        // when a group's derived minimum is positive. Closed data categories
        // may add independent positive-span groups, so the invariant is
        // checked per group below instead of assuming the whole Rholang table
        // is empty.
        assert!(!gated.spine_weight_rule_fn.is_empty());
        // The const-gated bundle IS the explicit-model bundle — the same
        // wiring fact the dormant pin guarded, inverted. (Streams compare by
        // rendering: TokenStream has no PartialEq.)
        let model = build_prefix_factoring(&def, &categories, &per_cat);
        // Per-group re-derivation of the A3 emptiness fact, mirroring the
        // emission loop's own `min over member_min_span(&rules[m])`
        // (self-adjudicating: an F5-era group with min > 0 would emit a span
        // row — this loop fails FIRST naming the exact group, so the
        // emptiness assert above can never go stale silently).
        let proc_src = src_idx(&categories, "Proc");
        let input_bind_src = src_idx(&categories, "InputBind");
        let min_span_rows = normalized(&gated.min_span_prelude);
        let mut legacy_groups_seen = 0usize;
        for cat_fact in &model {
            let rules = &per_cat[cat_fact.category_src_idx as usize];
            for bucket in &cat_fact.buckets {
                for group in &bucket.groups {
                    if matches!(cat_fact.category_src_idx, c if c == proc_src || c == input_bind_src)
                    {
                        legacy_groups_seen += 1;
                    }
                    let min = group
                        .member_rule_idxs()
                        .iter()
                        .map(|&m| member_min_span(&rules[m as usize]))
                        .min()
                        .expect("an eligible group has members");
                    let row = format!(
                        "({}u16,{}u16)=>return{}u32",
                        cat_fact.category_src_idx, group.spine_id, min,
                    );
                    if min == 0 {
                        let key =
                            format!("({}u16,{}u16)=>", cat_fact.category_src_idx, group.spine_id,);
                        assert!(
                            !min_span_rows.contains(&key),
                            "zero-span group must omit its table row: {key} in {min_span_rows}",
                        );
                    } else {
                        assert!(
                            min_span_rows.contains(&row),
                            "positive-span group must emit its exact row {row}: {min_span_rows}",
                        );
                    }
                }
            }
        }
        // A3/F5-1 stance-follow: the const-gated model gains the InputBind@
        // accept+continue group when `S1F5_ACCEPT_CONTINUE` is on (3 Proc@
        // groups + 1 InputBind@), and stays at the Proc@ trio when off —
        // green at BOTH stances; the min re-derivation loop above already
        // covered the new group (r2's Op-bearing pattern ⇒ min 0 ⇒ its span
        // row is ABSENT and the prelude stays empty).
        let expected_groups = if crate::gen::runtime::wpda_codegen::forks::S1F5_ACCEPT_CONTINUE {
            4
        } else {
            3
        };
        assert_eq!(
            legacy_groups_seen, expected_groups,
            "legacy Proc/InputBind group census follows the S1F5_ACCEPT_CONTINUE stance",
        );
        // F5-2 stance-follow (A3 discipline — no pin edits ride the flip):
        // the const-gated bundle gains the two Name-dispatched send cohorts
        // (`!` {4,6,8} spine 0xF803, `!!` {5,7,9} spine 0xF804) when
        // `S1F5_MIXFIX_COHORTS` is on, and stays mixfix-empty when off.
        // The min_span emptiness re-derivation extends to the mixfix groups
        // (self-adjudicating: rules 8/9 are Op-bearing ⇒ min 0 ⇒ every
        // mixfix span row OMITTED and the prelude stays empty).
        let mixfix_model = mixfix_emission_partition(&def, &categories, &per_cat);
        let mut mixfix_groups_seen = 0usize;
        for fact in &mixfix_model {
            for bucket in &fact.buckets {
                for group in &bucket.groups {
                    mixfix_groups_seen += 1;
                    let rules = &per_cat[group.result_src_idx as usize];
                    let min = group
                        .member_rule_idxs()
                        .iter()
                        .map(|&m| member_min_span(&rules[m as usize]))
                        .min()
                        .expect("an eligible mixfix group has members");
                    let key = format!("({}u16,{}u16)=>", group.result_src_idx, group.spine_id);
                    if min == 0 {
                        assert!(
                            !min_span_rows.contains(&key),
                            "zero-span mixfix group must omit its row: {key} in {min_span_rows}",
                        );
                    } else {
                        let row = format!("{key}return{min}u32");
                        assert!(
                            min_span_rows.contains(&row),
                            "positive-span mixfix group must emit {row}: {min_span_rows}",
                        );
                    }
                }
            }
        }
        let expected_mixfix_groups =
            if crate::gen::runtime::wpda_codegen::forks::S1F5_MIXFIX_COHORTS {
                2
            } else {
                0
            };
        assert_eq!(
            mixfix_groups_seen, expected_mixfix_groups,
            "rholang mixfix cohort census follows the S1F5_MIXFIX_COHORTS stance",
        );
        assert_eq!(
            gated.mixfix_groups.len(),
            expected_mixfix_groups,
            "the const-gated bundle's mixfix groups follow the stance",
        );
        let explicit =
            build_spine_emission_from_parts(&model, &mixfix_model, &def, &categories, &per_cat);
        assert_eq!(gated.dispositions, explicit.dispositions);
        assert_eq!(gated.binder_arms.to_string(), explicit.binder_arms.to_string());
        assert_eq!(
            gated.trigger_spine_owner_fn.to_string(),
            explicit.trigger_spine_owner_fn.to_string(),
        );
        assert_eq!(gated.spine_members_fn.to_string(), explicit.spine_members_fn.to_string());
        assert_eq!(gated.action_for_prelude.to_string(), explicit.action_for_prelude.to_string(),);
        assert_eq!(
            gated.leading_trigger_prelude.to_string(),
            explicit.leading_trigger_prelude.to_string(),
        );
        assert_eq!(gated.min_span_prelude.to_string(), explicit.min_span_prelude.to_string());
        assert_eq!(
            gated.spine_weight_rule_fn.to_string(),
            explicit.spine_weight_rule_fn.to_string(),
        );
        // F5-2: the mixfix streams agree between the const-gated and the
        // explicit bundles at BOTH stances (empty == empty when off).
        assert_eq!(gated.mixfix_groups, explicit.mixfix_groups);
        assert_eq!(gated.mixfix_fan_arms.to_string(), explicit.mixfix_fan_arms.to_string());
        assert_eq!(gated.mixfix_prelude_arms.to_string(), explicit.mixfix_prelude_arms.to_string(),);
        let grouped_alts: usize = gated.lex_alt.iter().map(|alt| alt.grouped.len()).sum();
        assert!(grouped_alts > 0, "const ON ⇒ lex-alt group entries present");
    }

    /// ON-shape pins over the rholang `@`-cohort: dispositions (GroupFirst at
    /// the min member with the AV5 weight identity, GroupRest for the rest),
    /// the ROOT-EDGE arm (F1 root-edge fix: the pre-root arm at node id 1 —
    /// the coordinate the trigger branch pushes — consumes the group's FIRST
    /// post-trigger item; without it `@ Nil !…` would dispatch the `!`/`!!`
    /// guards against the `Nil` token), typed commit coordinates on the arm
    /// stream, and the engine-table rows (owner, A-1 members, H9 poison
    /// union, A7, min-span).
    #[test]
    fn fork_emission_table_is_value_identical_to_the_trait_default_per_grammar() {
        // Task #10 item 1 F1 (coordinator decision 2026-07-14): the
        // generated `WPDA_FORK_EMISSION_ORDINAL` is ELECTION-INERT —
        // value-identical to the walker-trait default (`0|2 => 0,
        // 1|3 => 1, _ => MAX`) on every input. Pinned here over the FULL
        // per-grammar census domain (every (cat, rule) the emitters
        // recorded — derived rows ∪ ambiguous keys — per the requirement:
        // derive the domain from the census, don't sample blindly), for
        // both collision-bearing bundled grammars, by rebuilding the model
        // through the SAME threading `emit_engine_impl_full` uses.
        let trait_default = |site_kind: u8| -> u16 {
            match site_kind {
                0 | 2 => 0,
                1 | 3 => 1,
                _ => u16::MAX,
            }
        };
        for (name, def) in [("rholang", rholang()), ("calculator", calculator())] {
            let (categories, per_cat) = cats_per_cat(&def);
            let bundle = build_spine_emission(&def, &categories, &per_cat);
            let empty_disp: HashMap<u16, SpineDisposition> = HashMap::new();
            let empty_members: HashMap<u16, Vec<u16>> = HashMap::new();
            let mut fork_model =
                crate::gen::runtime::wpda_codegen::fork_emission::ForkEmissionOrdinalModel::new();
            for (i, _cat) in categories.iter().enumerate() {
                let indexed: Vec<(u16, &GrammarRule)> = per_cat[i]
                    .iter()
                    .enumerate()
                    .map(|(r, rule)| (r as u16, rule))
                    .collect();
                let _ = crate::gen::runtime::wpda_codegen::prefix::emit_prefix_arms_for_category(
                    &def,
                    i as u16,
                    &categories[i],
                    &indexed,
                    bundle.dispositions.get(i).unwrap_or(&empty_disp),
                    bundle.group_members.get(i).unwrap_or(&empty_members),
                    &mut fork_model,
                );
            }
            let _ = crate::gen::runtime::wpda_codegen::prefix::emit_paren_dispatch_arms(
                &categories,
                &def,
                &per_cat,
                &mut fork_model,
            );
            let domain = fork_model.census_keys();
            assert!(
                !domain.is_empty(),
                "{name}: the census domain is non-empty (the emitters record rows)",
            );
            for &(cat, rule) in &domain {
                for site_kind in [0u8, 1, 2, 3, 4, 255] {
                    assert_eq!(
                        fork_model.emitted_value(site_kind, cat, rule),
                        trait_default(site_kind),
                        "{name}: F1 value-identity at site {site_kind}, \
                         (cat {cat}, rule {rule})",
                    );
                }
            }
        }
    }

    #[test]
    fn fork_emission_rows_share_the_spine_trigger_position_per_group() {
        // Task #10 item 1 (real-grammar value pin): under the committed
        // S1-ON emission, EVERY member of a spine group derives its site-2
        // fork-emission ordinal AT ITS GROUP'S spine-trigger declaration
        // position — the GroupFirst branch is every member's initiating
        // branch, so all members of one group share ONE ordinal in the
        // generated table.
        let def = rholang();
        let (categories, per_cat) = cats_per_cat(&def);
        let bundle = build_spine_emission(&def, &categories, &per_cat);
        let proc_dispositions = &bundle.dispositions[0];
        let proc_members = &bundle.group_members[0];
        assert!(
            !proc_members.is_empty(),
            "rholang Proc carries S1 spine groups under the committed ON stance",
        );
        let mut fork_model =
            crate::gen::runtime::wpda_codegen::fork_emission::ForkEmissionOrdinalModel::new();
        let indexed: Vec<(u16, &GrammarRule)> = per_cat[0]
            .iter()
            .enumerate()
            .map(|(i, r)| (i as u16, r))
            .collect();
        let _ = crate::gen::runtime::wpda_codegen::prefix::emit_prefix_arms_for_category(
            &def,
            0,
            &categories[0],
            &indexed,
            proc_dispositions,
            proc_members,
            &mut fork_model,
        );
        for (first_member, members) in proc_members {
            let group_ordinal = fork_model.site2_ordinal(0, *first_member);
            assert!(group_ordinal.is_some(), "GroupFirst member {first_member} derives a row",);
            for member in members {
                assert_eq!(
                    fork_model.site2_ordinal(0, *member),
                    group_ordinal,
                    "member {member} shares its group's spine-trigger position",
                );
            }
        }
    }

    #[test]
    fn spine_emission_on_rholang_pins_dispositions_root_edge_and_tables() {
        let def = rholang();
        let (categories, per_cat) = cats_per_cat(&def);
        let model = build_prefix_factoring(&def, &categories, &per_cat);
        let bundle = build_spine_emission_from(&model, &def, &categories, &per_cat);
        assert!(bundle.any_groups());

        // Task #10 item 1: `group_members` mirrors the dispositions — one
        // entry per group, keyed at the GroupFirst (min) member, listing
        // every member in the same ordered walk the dispositions use.
        let proc_group_members = &bundle.group_members[0];
        let n_first = bundle.dispositions[0]
            .values()
            .filter(|d| matches!(d, SpineDisposition::GroupFirst { .. }))
            .count();
        assert_eq!(proc_group_members.len(), n_first, "one members entry per GroupFirst",);
        let member_total: usize = proc_group_members.values().map(Vec::len).sum();
        assert_eq!(
            member_total,
            bundle.dispositions[0].len(),
            "every dispositioned member appears in exactly one group list",
        );

        // ── dispositions: the Nil group 0xF800, keyed at its MIN member ────
        //
        // ★ #152: every coordinate below is DERIVED from a rule LABEL. It used to read
        // `.get(&9)` / `weight_rule_idx: 9` under a comment stating the numbers had been
        // "re-derived 2026-07-29 after `PParInternal` was deleted from `Proc` index 3".
        // A comment cannot fail. `rule_idx` resolves a label to its CURRENT position, so a
        // `Proc` rule added or removed above these cannot retarget the pin onto a neighbour —
        // and a neighbour here is a PERSIST TWIN with the same kind, the same leaf edge, the
        // same depth and the same commit shape, i.e. one that keeps every assertion below true
        // while describing a different rule.
        let proc_rules = &per_cat[0];
        let nil = rule_idx(proc_rules, "POutputNil");
        let quoted = rule_idx(proc_rules, "POutputQuoted");
        let short = rule_idx(proc_rules, "POutputShort");
        let proc_dispositions = &bundle.dispositions[0];
        assert_eq!(
            proc_dispositions.get(&nil),
            Some(&SpineDisposition::GroupFirst {
                spine_id: SPINE_RULE_BASE,
                body_src_idx: 0,
                weight_rule_idx: nil, // AV5: MIN member, never SPINE_ID
            }),
        );
        for rest in [
            "PPersistOutputNil",
            "POutputNilEmpty",
            "PPersistOutputNilEmpty",
            "POutputNil2Plus",
            "PPersistOutputNil2Plus",
        ] {
            assert_eq!(
                proc_dispositions.get(&rule_idx(proc_rules, rest)),
                Some(&SpineDisposition::GroupRest),
                "Nil-group member {rest} is GroupRest",
            );
        }
        assert_eq!(
            proc_dispositions.get(&quoted),
            Some(&SpineDisposition::GroupFirst {
                spine_id: SPINE_RULE_BASE + 1,
                body_src_idx: 3,
                weight_rule_idx: quoted,
            }),
            "the Quoted group leads at `POutputQuoted` with the Name body",
        );
        assert_eq!(
            proc_dispositions.get(&short),
            Some(&SpineDisposition::GroupFirst {
                spine_id: SPINE_RULE_BASE + 2,
                body_src_idx: 0,
                weight_rule_idx: short,
            }),
        );
        // The lex-alt surface mirrors the dispositions (A3).
        assert_eq!(bundle.lex_alt[0].grouped.len(), 15, "all 15 @-cohort members");

        // ── the ROOT-EDGE arm (the F1 root-edge fix pin) ───────────────────
        let arms = normalized(&bundle.binder_arms);
        let literal_body = shared_transition_body("child_literal");
        assert!(literal_body.contains("ForkActionKind::GuardedConsumeAndReplace"));
        assert!(literal_body.contains("expected_text:text.to_string()"));
        assert!(literal_body.contains("required_top_cat"));
        assert!(arms.contains("factoring::child_literal("));
        let parameter_body = shared_transition_body("parameter_replace");
        assert!(parameter_body.contains("WpdaStepAction::ReplaceAndPush"));
        assert!(
            parameter_body.contains("push_symbol:StackSymbolV2::category_entry_goal(cat_src_idx)")
        );
        // Pre-root arm (node 1) consumes the Nil-group's root item `Nil` —
        // and does NOT dispatch the divergence guards `!`/`!!` (those live
        // on the root node's own arm, id 2, which directly follows).
        let arm1 = window(&arms, "(0u16,63488u16,1u8)=>", "(0u16,63488u16,2u8)=>");
        assert!(arm1.contains("\"Nil\","), "pre-root arm consumes the root edge item: {arm1}",);
        assert!(
            !arm1.contains("\"!\","),
            "divergence guards must NOT be on the pre-root arm: {arm1}",
        );
        let arm2 = window(&arms, "(0u16,63488u16,2u8)=>", "(0u16,63488u16,3u8)=>");
        assert!(
            arm2.contains("\"!\",") && arm2.contains("\"!!\","),
            "root-node arm forks the !/!! divergence: {arm2}",
        );
        // Quoted group's pre-root arm is the ParamParse chain form: replace
        // the spine marker to node 2 and push CategoryEntry(Name).
        let quoted_arm1 = window(&arms, "(0u16,63489u16,1u8)=>", "(0u16,63489u16,2u8)=>");
        assert!(
            quoted_arm1.contains("factoring::parameter_replace(")
                && quoted_arm1.contains(",3u16,_pos,0u8,lex_one,")
                && quoted_arm1.contains("rule_at(0u16,63489u16,2u8"),
            "Quoted pre-root arm pushes the Name operand: {quoted_arm1}",
        );
        // Typed commits (A4): rule 9 (`POutputNil`) binder-resumes at its final
        // pos 6; rule 14 (`POutputNilEmpty`) nullary-commits into its
        // MixfixLiteralRun tail complete.
        assert!(arms.contains("rule_at(0u16,9u16,6u8"), "rule 9 commit coordinate present",);
        assert!(
            arms.contains("mixfix_marker(0u16,14u16,0u8,*outer_bp)")
                && arms.contains("sub_pos:4u8"),
            "rule 14 nullary commit coordinate present",
        );

        // ── engine-table rows ──────────────────────────────────────────────
        // Indices re-derived 2026-07-29 (post-`PParInternal` deletion): the Nil
        // group is {9,10,14,15,19,20}, Quoted {11,16,21}, Short
        // {12,13,17,18,22,23}.
        let owners = normalized(&bundle.trigger_spine_owner_fn);
        assert!(owners.contains("(0u16,9u16)=>Some(63488u16)"));
        assert!(owners.contains("(0u16,14u16)=>Some(63488u16)"));
        assert!(owners.contains("(0u16,11u16)=>Some(63489u16)"));
        assert!(owners.contains("(0u16,23u16)=>Some(63490u16)"));
        let members = normalized(&bundle.spine_members_fn);
        assert!(members.contains("(0u16,63488u16)=>&[9u16,10u16,14u16,15u16,19u16,20u16]"));
        assert!(members.contains("(0u16,63489u16)=>&[11u16,16u16,21u16]"));
        assert!(members.contains("(0u16,63490u16)=>&[12u16,13u16,17u16,18u16,22u16,23u16]"));
        // H9 poison rows: union = the members' canonical expected_input_cats
        // (Term slots per category; CollectionDrain/other slots = ANY_CAT
        // 65535), arity = the u8::MAX poison.
        let actions = normalized(&bundle.action_for_prelude);
        assert!(actions.contains("arity:u8::MAX"));
        assert!(
            actions.contains("expected_input_cats:&[0u16,65535u16]"),
            "Nil/Short union rows (Proc + CollectionDrain): {actions}",
        );
        assert!(
            actions.contains("expected_input_cats:&[3u16,0u16,65535u16]"),
            "Quoted union row (Name first, then Proc + drain): {actions}",
        );
        // A7 rows: conjunction over members (all-true, asserted at build).
        let leads = normalized(&bundle.leading_trigger_prelude);
        for spine in ["63488u16", "63489u16", "63490u16"] {
            assert!(leads.contains(&format!("(0u16,{spine})=>returntrue")));
        }
    }

    /// The spine trigger branch mirrors the per-rule BinderPrefix fork
    /// branch except for its factored SPINE_ID coordinates and group body.
    /// Scalar cost remains independent of the selected member identity.
    #[test]
    fn spine_trigger_branch_shape_pin() {
        let ts = emit_spine_trigger_branch(0, SPINE_RULE_BASE, 0, 10);
        let s = normalized(&ts);
        assert!(s.contains("__pd_branches.push"));
        assert!(
            s.contains(
                "factoring::prefix_spine_trigger(0u16,63488u16,0u16,_outer_bp,10u16,lex_w,)"
            ),
            "{s}"
        );
        let body = shared_transition_body("prefix_spine_trigger");
        assert!(body.contains("rule_at(category_src_idx,spine_id,1u8,Some(_outer_bp))"));
        assert!(
            body.contains("lex_w(0.0,category_src_idx,weight_rule_idx)"),
            "AV5 weight stamp: {body}"
        );
        assert!(body.contains("ConsumeAsTriggerOnly"));
        assert!(
            body.contains("rule_idx:spine_id"),
            "BinderRule state carries the SPINE_ID: {body}"
        );
    }

    // ═══════════════════════════════════════════════════════════════════════
    // F5-1 emission pins (2026-07-13; plan f5_accept_continue_plan.md §2.2 +
    // amendments A1/A2/A3). Full-strength through
    // `build_spine_emission_from(build_prefix_factoring_with(.., true))` —
    // no const flip needed, green at both stances (the F1 discipline).
    // ═══════════════════════════════════════════════════════════════════════

    /// P3(b) — the rholang InputBind@ accept+continue emission, hand-derived
    /// in plan §2.2 and pinned arm-by-arm: pre-root Proc push (arm 1), the
    /// `<-`/`<=` divergence with the r6 commit (arm 2), ★THE
    /// ACCEPT+CONTINUE FORK (arm 3 — two `ReplaceAndPush` branches BOTH
    /// pushing `CategoryEntry(Name)`, spine-continue FIRST and the r3
    /// accept commit LAST per A1; the branches are action-identical to
    /// F1-emitted constructs, distinguished only by their replace symbols),
    /// the r2 commit on the `!` guard (arm 4), the A2 dispositions
    /// (2 → GroupFirst{0xF800, Proc, weight_rule 2}, 3/6 → GroupRest),
    /// and the engine-table rows incl. the A3 span-row ABSENCE.
    #[test]
    fn spine_emission_on_inputbind_accept_fork_pins() {
        let def = rholang();
        let (categories, per_cat) = cats_per_cat(&def);
        let ib = src_idx(&categories, "InputBind");
        let name_src = src_idx(&categories, "Name");
        let model = build_prefix_factoring_with(&def, &categories, &per_cat, true);
        let bundle = build_spine_emission_from(&model, &def, &categories, &per_cat);
        assert!(bundle.any_groups());

        // ── A2 dispositions: GroupFirst at the MIN member with the AV5 weight
        //    identity; per-category ordinal keeps the ib spine at 0xF800. ──
        //    #152: the coordinates are derived from labels, not written down.
        let ib_rules = &per_cat[ib as usize];
        let min_member = rule_idx(ib_rules, "InputBindQuotedQuery");
        let ib_dispositions = &bundle.dispositions[ib as usize];
        assert_eq!(
            ib_dispositions.get(&min_member),
            Some(&SpineDisposition::GroupFirst {
                spine_id: SPINE_RULE_BASE,
                body_src_idx: 0,
                weight_rule_idx: min_member,
            }),
        );
        for rest in ["InputBindQuoted", "InputBindQuotedPersistent"] {
            assert_eq!(
                ib_dispositions.get(&rule_idx(ib_rules, rest)),
                Some(&SpineDisposition::GroupRest),
                "InputBind@ member {rest} is GroupRest",
            );
        }
        assert_eq!(bundle.lex_alt[ib as usize].grouped.len(), 3);
        // Proc@ dispositions unshifted (A2: per-category ordinals).
        assert_eq!(bundle.dispositions[0].len(), 15, "the Proc@ cohort is untouched");

        let arms = normalized(&bundle.binder_arms);
        let parameter_branch = shared_transition_body("parameter_replace_branch");
        assert!(parameter_branch.contains("symbol:StackSymbolV2::category_entry_goal(cat_src_idx)"));
        assert!(parameter_branch.contains("ForkActionKind::ReplaceAndPush{replace_symbol:symbol()"));
        assert!(arms.contains("factoring::divergence(2usize,"));
        let spine = SPINE_RULE_BASE; // 63488
                                     // Arm 1 (pre-root): the shared `pat` Proc operand — ONE push where
                                     // OFF ran three (the actual fan win).
        let arm1 = window(
            &arms,
            &format!("({ib}u16,{spine}u16,1u8)=>"),
            &format!("({ib}u16,{spine}u16,2u8)=>"),
        );
        assert!(
            arm1.contains("factoring::parameter_replace(")
                && arm1.contains(",0u16,_pos,0u8,lex_one,")
                && arm1.contains(&format!("rule_at({ib}u16,{spine}u16,2u8")),
            "pre-root arm pushes the shared Proc operand: {arm1}",
        );
        // Arm 2: the <-/<= divergence; the <= branch IS the r6 commit.
        let arm2 = window(
            &arms,
            &format!("({ib}u16,{spine}u16,2u8)=>"),
            &format!("({ib}u16,{spine}u16,3u8)=>"),
        );
        assert!(
            arm2.contains("\"<-\",") && arm2.contains(&format!("rule_at({ib}u16,{spine}u16,3u8")),
            "arm 2 continues the spine on <-: {arm2}",
        );
        assert!(
            arm2.contains("\"<=\",") && arm2.contains(&format!("rule_at({ib}u16,6u16,3u8")),
            "arm 2 commits r6 on <=: {arm2}",
        );
        // ★Arm 3 — THE ACCEPT+CONTINUE FORK: two same-push branches.
        let arm3 = window(
            &arms,
            &format!("({ib}u16,{spine}u16,3u8)=>"),
            &format!("({ib}u16,{spine}u16,4u8)=>"),
        );
        assert_eq!(
            arm3.matches("factoring::parameter_replace_branch(").count(),
            2,
            "arm 3 is the two-branch accept fork: {arm3}",
        );
        assert_eq!(
            arm3.matches(&format!("parameter_replace_branch({name_src}u16,_pos,0u8,"))
                .count(),
            2,
            "BOTH branches push the shared CategoryEntry(Name): {arm3}",
        );
        let continue_sym = format!("rule_at({ib}u16,{spine}u16,4u8");
        let accept_sym = format!("rule_at({ib}u16,3u16,4u8");
        let continue_at = arm3
            .find(&continue_sym)
            .expect("spine-continue branch present");
        let accept_at = arm3
            .find(&accept_sym)
            .expect("accept commit branch present");
        assert!(
            continue_at < accept_at,
            "★A1: interior-continue FIRST, accept commit LAST: {arm3}",
        );
        // Arm 4: the chain `!` guard commits r2 — where the spine-continue
        // lineage dies on plain `for(@y <- z){…}` input (the shared
        // evidence-prune, exactly where OFF's QuotedQuery cursor dies).
        let arm4 = window(&arms, &format!("({ib}u16,{spine}u16,4u8)=>"), "];");
        assert!(
            arm4.contains("\"!\",") && arm4.contains(&format!("rule_at({ib}u16,2u16,5u8")),
            "arm 4 commits r2 on the ! guard: {arm4}",
        );

        // ── engine-table rows ──────────────────────────────────────────────
        let owners = normalized(&bundle.trigger_spine_owner_fn);
        for member in [2u16, 3, 6] {
            assert!(
                owners.contains(&format!("({ib}u16,{member}u16)=>Some({spine}u16)")),
                "owner row for ib member {member}",
            );
        }
        let members = normalized(&bundle.spine_members_fn);
        assert!(members.contains(&format!("({ib}u16,{spine}u16)=>&[2u16,3u16,6u16]")));
        // H9 poison row union: r2 contributes Proc + Name + the ANY_CAT
        // sentinel for its Vec slot; r3/r6 duplicate Proc/Name.
        let actions = normalized(&bundle.action_for_prelude);
        assert!(
            actions.contains(&format!("({ib}u16,{spine}u16)=>{{staticSPINE_ENTRY")),
            "ib spine action row present: {actions}",
        );
        assert!(
            actions.contains("expected_input_cats:&[0u16,3u16,65535u16]"),
            "ib union row (Proc, Name, ANY_CAT): {actions}",
        );
        let leads = normalized(&bundle.leading_trigger_prelude);
        assert!(leads.contains(&format!("({ib}u16,{spine}u16)=>returntrue")));
        // A3: r2's Op-bearing pattern short-circuits member_min_span to 0 ⇒
        // group min 0 ⇒ this specific (ib, spine) span row is absent.
        // Independent closed-data groups may legitimately contribute rows.
        let min_span_rows = normalized(&bundle.min_span_prelude);
        assert!(
            !min_span_rows.contains(&format!("({ib}u16,{spine}u16)=>")),
            "A3: the zero-span InputBind group must omit its row; got {min_span_rows}",
        );
        let weights = normalized(&bundle.spine_weight_rule_fn);
        assert!(
            weights.contains(&format!("({ib}u16,{spine}u16)=>2u16")),
            "AV5 weight identity = min member 2: {weights}",
        );
    }

    /// P3(a) — the PrefixAccept synthetic's emitted accept fork matches the
    /// hand-derivation: arm 2 forks {spine-continue → node 3, accept commit
    /// → r0's final-pos arm}, both pushing `CategoryEntry(Tee)`; arm 3
    /// chain-commits r1 on the `»` guard.
    #[test]
    fn prefix_accept_emission_pins_accept_fork() {
        let lang = prefix_accept_lang();
        let (categories, per_cat) = cats_per_cat(&lang);
        let tee = src_idx(&categories, "Tee");
        let model = build_prefix_factoring_with(&lang, &categories, &per_cat, true);
        let bundle = build_spine_emission_from(&model, &lang, &categories, &per_cat);
        let arms = normalized(&bundle.binder_arms);
        let spine = SPINE_RULE_BASE;
        let arm2 =
            window(&arms, &format!("(0u16,{spine}u16,2u8)=>"), &format!("(0u16,{spine}u16,3u8)=>"));
        assert_eq!(arm2.matches("factoring::parameter_replace_branch(").count(), 2, "{arm2}");
        assert_eq!(
            arm2.matches(&format!("parameter_replace_branch({tee}u16,_pos,0u8,"))
                .count(),
            2,
            "{arm2}",
        );
        let continue_at = arm2
            .find(&format!("rule_at(0u16,{spine}u16,3u8"))
            .expect("spine-continue branch");
        let accept_at = arm2
            .find("rule_at(0u16,0u16,3u8")
            .expect("Short accept commit branch");
        assert!(continue_at < accept_at, "A1 order: {arm2}");
        let arm3 = window(&arms, &format!("(0u16,{spine}u16,3u8)=>"), "];");
        assert!(
            arm3.contains("\"»\",") && arm3.contains("rule_at(0u16,1u16,4u8"),
            "arm 3 commits Long on the » guard: {arm3}",
        );
    }

    /// A root accept makes the PRE-ROOT arm the accept fork: both branches
    /// consume the root edge `«` — spine-continue to node 2 FIRST, the
    /// nullary tail-complete commit LAST (A1 applies to pre-root children).
    #[test]
    fn root_accept_emission_puts_accept_fork_on_pre_root_arm() {
        let lang = mk_language(
            "RootAccept",
            expr_num_types(),
            vec![
                jrule("TShort", "Expr", vec![], vec![lit("quo"), lit("«")]),
                jrule("TLong", "Expr", vec![], vec![lit("quo"), lit("«"), lit("»")]),
            ],
        );
        let (categories, per_cat) = cats_per_cat(&lang);
        let model = build_prefix_factoring_with(&lang, &categories, &per_cat, true);
        let bundle = build_spine_emission_from(&model, &lang, &categories, &per_cat);
        let arms = normalized(&bundle.binder_arms);
        let spine = SPINE_RULE_BASE;
        let arm1 =
            window(&arms, &format!("(0u16,{spine}u16,1u8)=>"), &format!("(0u16,{spine}u16,2u8)=>"));
        assert_eq!(
            arm1.matches("\"«\",").count(),
            2,
            "the pre-root arm forks BOTH consumers of the root edge: {arm1}",
        );
        let continue_at = arm1
            .find(&format!("rule_at(0u16,{spine}u16,2u8"))
            .expect("spine-continue branch");
        let accept_at = arm1
            .find("mixfix_marker(0u16,0u16,0u8,*outer_bp)")
            .expect("TShort nullary accept commit branch");
        assert!(continue_at < accept_at, "A1 order at the pre-root: {arm1}");
        assert!(
            arm1.contains("sub_pos:1u8"),
            "the accept lands tail-complete (sub_pos == parts_len): {arm1}",
        );
        let arm2 = window(&arms, &format!("(0u16,{spine}u16,2u8)=>"), "];");
        assert!(
            arm2.contains("\"»\",") && arm2.contains("mixfix_marker(0u16,1u16,0u8,*outer_bp)"),
            "arm 2 commits TLong on the » guard: {arm2}",
        );
    }
    // ═══════════════════════════════════════════════════════════════════════
    // F5-2 — mixfix send-cohort pins (plan f5_mixfix_cohorts_plan.md §1.3/
    // §2.2 + amendments A-M4/A-M5).
    // ═══════════════════════════════════════════════════════════════════════

    /// P1 (GO/STOP): the two real cohort tries against the ACTUAL rholang
    /// grammar — leaves {3,5,7}/{4,6,8}, divergences at depths 1 and 2,
    /// rules 7/8 truncated at their rep, NO interior accepts, whole-slice
    /// coverage, uniform result_src = 0, spine ids CONTINUING Proc's prefix
    /// ordinals (3 prefix groups ⇒ `!` = 0xF803, `!!` = 0xF804), the D-1
    /// floors (min l_bp 2/4), the AV5 identities (min member 3/4), the
    /// A-M4 Fix-B evidence (both cohorts share "("), and the typed
    /// MixfixRun commit coordinates.
    ///
    /// ⚠ The leaf numbers are ABSOLUTE `Proc` rule indices: `!` = {POutput,
    /// POutputEmpty, POutput2Plus} = {3,5,7} and `!!` = {PPersistOutput,
    /// PPersistOutputEmpty, PPersistOutput2Plus} = {4,6,8}. Re-derived
    /// 2026-07-29 by dumping the regenerated rule list after `PParInternal`
    /// was deleted from index 3; every index at or above 3 moved down one.
    #[test]
    fn rholang_mixfix_send_cohorts_pin_two_groups() {
        let def = rholang();
        let (categories, per_cat) = cats_per_cat(&def);
        let name_src = src_idx(&categories, "Name");
        let proc_src = src_idx(&categories, "Proc");
        let prefix = build_prefix_factoring(&def, &categories, &per_cat);
        let proc_prefix_groups: usize = prefix[proc_src as usize]
            .buckets
            .iter()
            .map(|b| b.groups.len())
            .sum();
        assert_eq!(proc_prefix_groups, 3, "Proc carries the three @-cohort groups");
        let model = build_mixfix_factoring(&def, &categories, &per_cat, &prefix);
        let name_fact = model
            .iter()
            .find(|f| f.dispatch_cat_src_idx == name_src)
            .expect("Name carries mixfix buckets");
        let bang = name_fact
            .buckets
            .iter()
            .find(|b| b.trigger == "!")
            .expect("the ! cohort exists");
        assert_eq!(
            bang.slice,
            vec![(2u8, 0u16, 3u16), (6u8, 0u16, 5u16), (10u8, 0u16, 7u16)],
            "the ! slice mirrors mixfix_bp_name",
        );
        assert_eq!(bang.groups.len(), 1);
        assert!(bang.ineligible.is_empty() && bang.singletons.is_empty());
        let g = &bang.groups[0];
        assert_eq!(g.spine_id, SPINE_RULE_BASE + 3, "continues Proc's prefix ordinals");
        assert_eq!(g.result_src_idx, 0);
        assert_eq!(g.min_l_bp, 2);
        assert_eq!(g.min_member_rule_idx, 3);
        assert_eq!(g.member_l_bps, vec![(2u8, 3u16), (6u8, 5u16), (10u8, 7u16)]);
        assert_eq!(g.fixb_literal.as_deref(), Some("("), "A-M4 shared Fix-B evidence");
        assert_eq!(
            g.expected_cats_union,
            vec![name_src, 0u16, u16::MAX],
            "H9 union: Name LHS + Proc operand + the rep's ANY_CAT",
        );
        assert_eq!(
            render(&g.roots[0]),
            "L(()[P(0,0)[L())=>r3 L(,)=>r7] L())=>r5]",
            "the §1.3 trie: divergence 1 = operand-vs-close, divergence 2 = close-vs-sep",
        );
        // Label-bound coordinates: a rule-index shift must fail HERE, loudly,
        // rather than silently selecting a neighbouring send rule.
        for (idx, label) in [(3u16, "POutput"), (5u16, "POutputEmpty"), (7u16, "POutput2Plus")] {
            assert_eq!(
                per_cat[0][idx as usize].label.to_string(),
                label,
                "the ! cohort's rule {idx} must be {label}",
            );
        }
        let (_, m4) = g.roots[0].leaf_for(3).expect("POutput leafs");
        assert_eq!(
            m4.commit,
            MemberCommit::MixfixRun {
                rule_idx: 3,
                kind: 0,
                completed_idx: 0,
                sub_pos: 1
            },
        );
        assert!(!m4.has_post_spine_remainder, "POutput's ) is its final item");
        let (_, m6) = g.roots[0].leaf_for(5).expect("POutputEmpty leafs");
        assert_eq!(
            m6.commit,
            MemberCommit::MixfixRun {
                rule_idx: 5,
                kind: 2,
                completed_idx: 0,
                sub_pos: 2
            },
        );
        assert!(!m6.has_post_spine_remainder);
        let (_, m8) = g.roots[0].leaf_for(7).expect("POutput2Plus leafs");
        assert_eq!(
            m8.commit,
            MemberCommit::MixfixRun {
                rule_idx: 7,
                kind: 0,
                completed_idx: 0,
                sub_pos: 1
            },
        );
        assert!(m8.has_post_spine_remainder, "POutput2Plus truncates at its rep");
        assert_eq!(
            m8.pos_map,
            SpinePosMap::Mixfix {
                coords_at_depth: vec![(2, 0, 0), (2, 0, 1), (0, 0, 0), (0, 0, 1)],
            },
            "the A4-analog member walk",
        );
        let bangbang = name_fact
            .buckets
            .iter()
            .find(|b| b.trigger == "!!")
            .expect("the !! cohort exists");
        assert_eq!(bangbang.slice, vec![(4u8, 0u16, 4u16), (8u8, 0u16, 6u16), (12u8, 0u16, 8u16)],);
        assert_eq!(bangbang.groups.len(), 1);
        let g2 = &bangbang.groups[0];
        assert_eq!(g2.spine_id, SPINE_RULE_BASE + 4);
        assert_eq!(g2.min_l_bp, 4);
        assert_eq!(g2.min_member_rule_idx, 4);
        for (idx, label) in [
            (4u16, "PPersistOutput"),
            (6u16, "PPersistOutputEmpty"),
            (8u16, "PPersistOutput2Plus"),
        ] {
            assert_eq!(
                per_cat[0][idx as usize].label.to_string(),
                label,
                "the !! cohort's rule {idx} must be {label}",
            );
        }
        assert_eq!(
            render(&g2.roots[0]),
            "L(()[P(0,0)[L())=>r4 L(,)=>r8] L())=>r6]",
            "the !! trie is isomorphic",
        );
    }

    /// A-M5 census errata pins: every OTHER bundled mixfix cohort stays
    /// unfactored with the recorded reason — Name `,` (rep-part-0 ⇒
    /// EmptySequence ×2), Name `<-` (1-member slice ⇒ LoneRootChild), the
    /// Proc `.` bucket (one generic method rule whose captured name terminates the literal spine
    /// ⇒ EmptySequence), and
    /// InputBind `&`/`where` (rep-part-0 ×2 / singleton).
    ///
    /// Census delta (2026-07-26): the trie-enumeration surface added
    /// `getPath()`, `toNextLeaf()` and `leafCount()` — three more nullary
    /// `z "." NAME "(" ")"` methods — so the Proc `.` cohort grows 40 → 43.
    /// The pinned PROPERTY is unchanged: each method name is distinct, so each
    /// remains its own `LoneRootChild` singleton and the cohort still yields
    /// zero factorable groups. Only the census count moves.
    ///
    /// Census delta (2026-07-28): `List.last()` — the FIPS-mandated projection
    /// onto a list's final element, `LLast . l:Proc |- l "." "last" "(" ")"` —
    /// is a fourth such nullary method, so the Proc `.` cohort grows 43 → 44.
    /// The pinned PROPERTY is again untouched, and that is the whole content of
    /// this pin: `last` is a name no other method shares, so it factors against
    /// nothing, stays its own `LoneRootChild` singleton, and leaves the cohort
    /// at zero factorable groups. The two assertions that carry the property —
    /// `dot.groups.is_empty()` and the all-`LoneRootChild` check — are unchanged
    /// and still assert exactly what they did; `slice.len()` and
    /// `singletons.len()` move TOGETHER, from 43 to 44, which is itself the
    /// evidence that the new method added a singleton rather than a group.
    ///
    /// Census delta (2026-07-30): the three BYTE-NAMED methods MeTTaIL lacked —
    /// `hexToBytes`, `bytesToHex` and `toUtf8Bytes`, upstream `method_table` keys
    /// at `reduce.rs:9346-9348` — grow the Proc `.` cohort 44 → 47. Each is a
    /// nullary `p "." NAME "(" ")"` form whose name no other method shares, so
    /// all three are `LoneRootChild` singletons and the cohort still yields ZERO
    /// factorable groups. As with `last`, `slice.len()` and `singletons.len()`
    /// move TOGETHER (44 → 47), which is the evidence that three singletons were
    /// added rather than a group; the property this pin exists for is untouched.
    ///
    /// Architecture delta (2026-08-04): all 47 name-specific rules collapsed into one
    /// `MethodCall(receiver, Ident, Vec(Proc))`. The dot bucket therefore has one rule and one
    /// `EmptySequence`: its first post-dot item is captured identifier text, not a mergeable
    /// literal. It still has zero factorable groups. Method names are data now, not 47
    /// grammar paths; retaining the former count here would reintroduce the deleted registry.
    #[test]
    fn rholang_mixfix_other_cohorts_stay_unfactored() {
        let def = rholang();
        let (categories, per_cat) = cats_per_cat(&def);
        let name_src = src_idx(&categories, "Name");
        let proc_src = src_idx(&categories, "Proc");
        let ib_src = src_idx(&categories, "InputBind");
        let prefix = build_prefix_factoring(&def, &categories, &per_cat);
        let model = build_mixfix_factoring(&def, &categories, &per_cat, &prefix);
        let bucket = |cat: u16, trigger: &str| -> &MixfixBucket {
            model
                .iter()
                .find(|f| f.dispatch_cat_src_idx == cat)
                .and_then(|f| f.buckets.iter().find(|b| b.trigger == trigger))
                .unwrap_or_else(|| panic!("bucket ({cat}, {trigger:?}) exists"))
        };
        let comma = bucket(name_src, ",");
        assert!(comma.groups.is_empty());
        assert_eq!(comma.singletons.len(), 2);
        assert!(comma
            .singletons
            .iter()
            .all(|s| s.reason == SingletonReason::EmptySequence));
        let query = bucket(name_src, "<-");
        assert!(query.groups.is_empty());
        assert_eq!(query.singletons.len(), 1);
        assert_eq!(query.singletons[0].reason, SingletonReason::LoneRootChild);
        let dot = bucket(proc_src, ".");
        assert!(dot.groups.is_empty());
        assert_eq!(dot.slice.len(), 1, "the single generic method-call rule");
        assert_eq!(dot.singletons.len(), 1);
        assert_eq!(dot.singletons[0].reason, SingletonReason::EmptySequence);
        let amp = bucket(ib_src, "&");
        assert!(amp.groups.is_empty());
        assert!(amp
            .singletons
            .iter()
            .all(|s| s.reason == SingletonReason::EmptySequence));
        // The whole-bundle headline: exactly TWO factorable groups.
        let total_groups: usize = model
            .iter()
            .flat_map(|f| f.buckets.iter())
            .map(|b| b.groups.len())
            .sum();
        assert_eq!(total_groups, 2, "exactly two factorable mixfix cohorts in rholang");
    }

    /// Dormancy pin (stance-adaptive on `S1F5_MIXFIX_COHORTS` — no pin edit
    /// rides the flip): with the const OFF the emission-effective mixfix
    /// partition is the identity, every mixfix stream in the const-gated
    /// bundle is EMPTY, and `mixfix_spine_parts_len_rows` contributes no
    /// rows (the byte-identity mechanism); with the const ON the partition
    /// is the model, the streams are live, and the rows carry exactly the
    /// two Proc-space spine ids.
    #[test]
    fn mixfix_emission_follows_the_s1f5_2_const() {
        let def = rholang();
        let (categories, per_cat) = cats_per_cat(&def);
        let gated = build_spine_emission(&def, &categories, &per_cat);
        let rows = mixfix_spine_parts_len_rows(&def, &categories, &per_cat);
        let partition = mixfix_emission_partition(&def, &categories, &per_cat);
        let partition_groups: usize = partition
            .iter()
            .flat_map(|f| f.buckets.iter())
            .map(|b| b.groups.len())
            .sum();
        if crate::gen::runtime::wpda_codegen::forks::S1_FACTORING
            && crate::gen::runtime::wpda_codegen::forks::S1F5_MIXFIX_COHORTS
        {
            assert_eq!(gated.mixfix_groups.len(), 2);
            assert!(!gated.mixfix_fan_arms.is_empty());
            assert!(!gated.mixfix_prelude_arms.is_empty());
            assert_eq!(rows, vec![(0u16, SPINE_RULE_BASE + 3), (0u16, SPINE_RULE_BASE + 4)],);
            assert_eq!(partition_groups, 2);
        } else {
            assert!(gated.mixfix_groups.is_empty());
            assert!(gated.mixfix_fan_arms.is_empty());
            assert!(gated.mixfix_prelude_arms.is_empty());
            assert!(rows.is_empty());
            assert_eq!(partition_groups, 0);
            // Identity twin: same cohort census (slice denominators), every
            // member a FactoringDisabled singleton.
            for fact in &partition {
                for bucket in &fact.buckets {
                    assert_eq!(bucket.singletons.len(), bucket.slice.len());
                    assert!(bucket
                        .singletons
                        .iter()
                        .all(|s| s.reason == SingletonReason::FactoringDisabled));
                }
            }
        }
    }

    /// The identity partition mirrors the model's cohort CENSUS exactly
    /// (same buckets, same slices — only the outcome differs). The INV-8
    /// denominators therefore agree across stances.
    #[test]
    fn mixfix_identity_partition_census_twin() {
        let def = rholang();
        let (categories, per_cat) = cats_per_cat(&def);
        let prefix = build_prefix_factoring(&def, &categories, &per_cat);
        let model = build_mixfix_factoring(&def, &categories, &per_cat, &prefix);
        let identity = mixfix_identity_partition(&def, &categories, &per_cat);
        let census = |m: &[MixfixFactoring]| -> Vec<(u16, String, Vec<(u8, u16, u16)>)> {
            m.iter()
                .flat_map(|f| {
                    f.buckets
                        .iter()
                        .map(move |b| (f.dispatch_cat_src_idx, b.trigger.clone(), b.slice.clone()))
                })
                .collect()
        };
        assert_eq!(census(&model), census(&identity));
    }

    /// ON-shape emission pins over the explicit-stance core (no const
    /// flips): the loop-v2 fan arm (D-1 guard on the A-M4 MEMBER id, the
    /// AV5 min-member weight, the spine push + flag), the three prelude
    /// arms per plan §2.2 (chain step via `__checked_literal_consume!`,
    /// divergence 1 = strict operand Push + rule-5 commit CAR with the
    /// B-alone/zero short-circuit, divergence 2 = rule-3/rule-7 commit CARs
    /// with the singleton short-circuits + the Error miss shape), and the
    /// engine-table rows (owner/members/H9 union/weight; A7 rows ABSENT).
    ///
    /// ⚠ Rule numbers here are ABSOLUTE `Proc` indices — 3 = `POutput`,
    /// 5 = `POutputEmpty`, 7 = `POutput2Plus` for the `!` cohort, and their
    /// persist twins 4/6/8 for `!!`. Re-derived 2026-07-29 by dumping the
    /// regenerated rule list after `PParInternal` was deleted from index 3.
    #[test]
    fn mixfix_emission_pins_fan_arm_prelude_and_tables() {
        let def = rholang();
        let (categories, per_cat) = cats_per_cat(&def);
        let prefix = build_prefix_factoring(&def, &categories, &per_cat);
        let mixfix = build_mixfix_factoring(&def, &categories, &per_cat, &prefix);
        let bundle = build_spine_emission_from_parts(&prefix, &mixfix, &def, &categories, &per_cat);
        assert_eq!(bundle.mixfix_groups.len(), 2);
        // ★ #152: the three `Proc` coordinates are DERIVED from their labels. The doc comment
        // above states "3 = `POutput`, 5 = `POutputEmpty`, 7 = `POutput2Plus` … and their
        // persist twins 4/6/8" — and a comment that has to name the twins is exactly the
        // situation in which a silent retarget lands on one.
        let proc_rules = &per_cat[0];
        let output = rule_idx(proc_rules, "POutput");
        let output_empty = rule_idx(proc_rules, "POutputEmpty");
        let output_2plus = rule_idx(proc_rules, "POutput2Plus");
        assert_eq!(
            bundle.mixfix_groups[0],
            MixfixGroupEmission {
                dispatch_cat_src_idx: 3,
                trigger: "!".to_string(),
                result_src_idx: 0,
                spine_id: SPINE_RULE_BASE + 3,
                min_l_bp: 2,
                min_member_rule_idx: output,
                member_rule_idxs: vec![output, output_empty, output_2plus],
            },
        );
        // ── the fan arm ────────────────────────────────────────────────────
        let fan = normalized(&bundle.mixfix_fan_arms);
        let group_body = shared_transition_body("mixfix_group_branch");
        assert!(group_body.contains("mixfix_marker(result_src,spine_id,0,cur_bp)"));
        assert!(group_body.contains("BP_TIER_MIXFIX,result_src,min_member"));
        assert!(group_body.contains("rule_idx:spine_id"));
        let bang_arm = window(&fan, "(3u16,\"!\")", "(3u16,\"!!\")");
        assert!(
            bang_arm.contains("if2u8>=*cur_bp")
                && bang_arm.contains("__goal_admits(0u16)")
                && bang_arm.contains("__method_name_admits(0u16,3u16)"),
            "D-1 full-admission guard on the MEMBER id (A-M4): {bang_arm}",
        );
        assert!(
            bang_arm.contains("factoring::mixfix_group_branch(0u16,63491u16,*cur_bp,3u16,lex_w,)")
                && bang_arm.contains("__mixfix_spine_pushed=true"),
            "spine push at the AV5 min-member weight: {bang_arm}",
        );
        assert!(
            fan.contains("(3u16,\"!!\")")
                && fan
                    .contains("factoring::mixfix_group_branch(0u16,63492u16,*cur_bp,4u16,lex_w,)")
        );
        // ── the prelude arms (the ! group; !! isomorphic) ─────────────────
        let prelude = normalized(&bundle.mixfix_prelude_arms);
        assert!(shared_transition_body("parameter_push").contains("WpdaStepAction::Push"));
        assert!(shared_transition_body("parameter_push_branch").contains("ForkActionKind::Push"));
        assert!(shared_transition_body("zero_one_operand").contains("if__spine_lit_total==0"));
        assert!(shared_transition_body("singleton").contains("if__spine_lit_total==1"));
        assert!(shared_transition_body("zero_literal_only").contains("WpdaStepAction::Error"));
        assert!(shared_transition_body("literal_singleton")
            .contains("WpdaStepAction::ConsumeAtAndReplace"));
        assert!(shared_transition_body("append_literal_targets").contains("for__spine_npintargets"));
        assert!(shared_transition_body("mixfix_divergence").contains("consume_trigger:false"));
        let chain =
            window(&prelude, "(0u16,63491u16,2u8,0u8,0u8)=>", "(0u16,63491u16,2u8,0u8,1u8)=>");
        assert!(
            chain.contains("__checked_literal_consume!(\"(\"") && chain.contains("sub_pos:1u8"),
            "pre-root chain step consumes the root edge: {chain}",
        );
        let div1 =
            window(&prelude, "(0u16,63491u16,2u8,0u8,1u8)=>", "(0u16,63491u16,0u8,0u8,0u8)=>");
        assert!(
            div1.contains("__mixfix_literal_targets(tokens,_pos,\")\")"),
            "divergence 1 gates the rule-5 commit on the close: {div1}",
        );
        assert!(
            div1.contains("factoring::zero_one_operand(__spine_lit_total,||{")
                && div1.contains("factoring::parameter_push(0u16,_pos,"),
            "divergence 1 B-alone short-circuit (descent when no close): {div1}",
        );
        assert!(
            div1.contains("factoring::parameter_push_branch(0u16,_pos,")
                && div1.contains("factoring::append_literal_targets(")
                && div1.contains("mixfix_marker(0u16,5u16,0u8,__mixfix_continuation_bp,)")
                && div1.contains("kind:2u8,sub_pos:2u8"),
            "divergence 1 fork = descent-first + rule-5 commit CAR: {div1}",
        );
        assert!(
            !div1.contains("factoring::singleton("),
            "divergence 1 has an unconditional branch — no literal-singleton \
             short-circuit: {div1}",
        );
        let div2 =
            window(&prelude, "(0u16,63491u16,0u8,0u8,0u8)=>", "(0u16,63492u16,2u8,0u8,0u8)=>");
        assert!(
            div2.contains("__mixfix_literal_targets(tokens,_pos,\")\")")
                && div2.contains("__mixfix_literal_targets(tokens,_pos,\",\")"),
            "divergence 2 gates both commits: {div2}",
        );
        assert!(
            div2.contains("factoring::singleton(__spine_lit_total,||{")
                && div2.contains("mixfix_marker(0u16,3u16,0u8,__mixfix_continuation_bp,)")
                && div2.contains("mixfix_marker(0u16,7u16,0u8,__mixfix_continuation_bp,)")
                && div2.contains("kind:0u8,sub_pos:1u8"),
            "divergence 2 = the two commit CARs with singleton short-circuits: {div2}",
        );
        assert!(
            div2.contains("factoring::zero_literal_only(__spine_lit_total,_pos,0u16,63491u16,)"),
            "divergence 2 zero-live miss shape: {div2}",
        );
        // ── engine-table rows ─────────────────────────────────────────────
        let owners = normalized(&bundle.trigger_spine_owner_fn);
        for (m, spine) in [
            (3, "63491"),
            (5, "63491"),
            (7, "63491"),
            (4, "63492"),
            (6, "63492"),
            (8, "63492"),
        ] {
            assert!(
                owners.contains(&format!("(0u16,{m}u16)=>Some({spine}u16)")),
                "owner row for member {m}: {owners}",
            );
        }
        let members = normalized(&bundle.spine_members_fn);
        assert!(members.contains("(0u16,63491u16)=>&[3u16,5u16,7u16]"));
        assert!(members.contains("(0u16,63492u16)=>&[4u16,6u16,8u16]"));
        let actions = normalized(&bundle.action_for_prelude);
        assert!(
            actions.contains("(0u16,63491u16)=>")
                && actions.contains("expected_input_cats:&[3u16,0u16,65535u16]"),
            "H9 poison union row (Name LHS + Proc + rep ANY_CAT): {actions}",
        );
        let weights = normalized(&bundle.spine_weight_rule_fn);
        assert!(weights.contains("(0u16,63491u16)=>3u16"));
        assert!(weights.contains("(0u16,63492u16)=>4u16"));
        // A7-mixfix (A-M5): rows OMITTED — the members are operand-leading.
        let leads = normalized(&bundle.leading_trigger_prelude);
        assert!(
            !leads.contains("63491") && !leads.contains("63492"),
            "mixfix spine ids must NOT appear on the leading-trigger surface: {leads}",
        );
        // These two rows stay absent (rules 7/8 are Op-bearing ⇒ min 0),
        // independently of positive-span groups in closed data categories.
        let min_spans = normalized(&bundle.min_span_prelude);
        assert!(!min_spans.contains("(0u16,63491u16)=>"));
        assert!(!min_spans.contains("(0u16,63492u16)=>"));
    }

    /// A-M5 operand-absorbability witness: a cohort whose post-operand
    /// divergence literal (`+`) is itself an infix operator of the operand
    /// category — the whole cohort degrades with
    /// `OperandAbsorbableDivergence` (next-token-disjoint does NOT imply
    /// span-disjoint; the min-member spine stamp would adjudicate an
    /// intra-cohort ⊕-tie OFF adjudicates with member stamps).
    #[test]
    fn mixfix_operand_absorbable_divergence_defers() {
        let types = vec![lang_type("Expr", None)];
        let terms = vec![
            jrule("EAtom", "Expr", vec![], vec![lit("e")]),
            jrule(
                "Plus",
                "Expr",
                vec![simple("a", "Expr"), simple("b", "Expr")],
                vec![param("a"), lit("+"), param("b")],
            ),
            jrule(
                "MPlusTail",
                "Expr",
                vec![simple("a", "Expr"), simple("b", "Expr"), simple("c", "Expr")],
                vec![param("a"), lit("!"), lit("«"), param("b"), lit("+"), param("c"), lit("»")],
            ),
            jrule(
                "MClose",
                "Expr",
                vec![simple("a", "Expr"), simple("b", "Expr")],
                vec![param("a"), lit("!"), lit("«"), param("b"), lit("»")],
            ),
        ];
        let def = mk_language("AbsorbLang", types, terms);
        let (categories, per_cat) = cats_per_cat(&def);
        let prefix = build_prefix_factoring(&def, &categories, &per_cat);
        let model = build_mixfix_factoring(&def, &categories, &per_cat, &prefix);
        let bucket = model
            .iter()
            .find(|f| f.dispatch_cat_src_idx == 0)
            .and_then(|f| f.buckets.iter().find(|b| b.trigger == "!"))
            .expect("the ! bucket exists");
        assert!(bucket.groups.is_empty(), "absorbable divergence must not factor");
        assert_eq!(bucket.ineligible.len(), 1);
        match &bucket.ineligible[0].reason {
            IneligibleReason::OperandAbsorbableDivergence { texts } => {
                assert!(texts.contains(&"+".to_string()), "the + literal is absorbable");
            },
            other => panic!("expected OperandAbsorbableDivergence, got {other:?}"),
        }
    }

    /// The coordinator-mandated exhaustion-at-interior check on the mixfix
    /// surface: a proper-prefix member routes the WHOLE cohort to
    /// `InteriorAccept` (accept_continue is ALWAYS false here — the F5-1
    /// sibling-leaf mechanism needs the typed mixfix commits and its own
    /// plan pass).
    #[test]
    fn mixfix_interior_accept_defers_whole_group() {
        let types = vec![lang_type("Expr", None)];
        let terms = vec![
            jrule("EAtom", "Expr", vec![], vec![lit("e")]),
            jrule(
                "MShort",
                "Expr",
                vec![simple("a", "Expr"), simple("b", "Expr")],
                vec![param("a"), lit("!"), lit("«"), param("b"), lit("»")],
            ),
            jrule(
                "MLong",
                "Expr",
                vec![simple("a", "Expr"), simple("b", "Expr"), simple("c", "Expr")],
                vec![
                    param("a"),
                    lit("!"),
                    lit("«"),
                    param("b"),
                    lit("»"),
                    lit("‹"),
                    param("c"),
                    lit("›"),
                ],
            ),
        ];
        let def = mk_language("InteriorLang", types, terms);
        let (categories, per_cat) = cats_per_cat(&def);
        let prefix = build_prefix_factoring(&def, &categories, &per_cat);
        let model = build_mixfix_factoring(&def, &categories, &per_cat, &prefix);
        let bucket = model
            .iter()
            .find(|f| f.dispatch_cat_src_idx == 0)
            .and_then(|f| f.buckets.iter().find(|b| b.trigger == "!"))
            .expect("the ! bucket exists");
        assert!(bucket.groups.is_empty());
        assert_eq!(bucket.ineligible.len(), 1);
        assert!(
            matches!(
                &bucket.ineligible[0].reason,
                IneligibleReason::InteriorAccept { accepting_rule_idxs }
                    if accepting_rule_idxs.len() == 1
            ),
            "the proper-prefix member is the interior accept: {:?}",
            bucket.ineligible[0],
        );
    }

    /// D-5 partial-slice witness: a 3-member slice whose root partition
    /// splits (two share `«`, one opens with `⟦`) degrades the WHOLE cohort
    /// — the pair records `PartialSliceCohort`, the loner `LoneRootChild`,
    /// zero groups.
    #[test]
    fn mixfix_partial_slice_cohort_degrades() {
        let types = vec![lang_type("Expr", None)];
        let terms = vec![
            jrule("EAtom", "Expr", vec![], vec![lit("e")]),
            jrule(
                "MOne",
                "Expr",
                vec![simple("a", "Expr"), simple("b", "Expr")],
                vec![param("a"), lit("!"), lit("«"), param("b"), lit("»")],
            ),
            jrule(
                "MEmpty",
                "Expr",
                vec![simple("a", "Expr")],
                vec![param("a"), lit("!"), lit("«"), lit("»")],
            ),
            jrule(
                "MOther",
                "Expr",
                vec![simple("a", "Expr"), simple("b", "Expr")],
                vec![param("a"), lit("!"), lit("⟦"), param("b"), lit("⟧")],
            ),
        ];
        let def = mk_language("PartialLang", types, terms);
        let (categories, per_cat) = cats_per_cat(&def);
        let prefix = build_prefix_factoring(&def, &categories, &per_cat);
        let model = build_mixfix_factoring(&def, &categories, &per_cat, &prefix);
        let bucket = model
            .iter()
            .find(|f| f.dispatch_cat_src_idx == 0)
            .and_then(|f| f.buckets.iter().find(|b| b.trigger == "!"))
            .expect("the ! bucket exists");
        assert!(bucket.groups.is_empty() && bucket.ineligible.is_empty());
        assert_eq!(bucket.slice.len(), 3);
        let mut partial = 0;
        let mut lone = 0;
        for s in &bucket.singletons {
            match s.reason {
                SingletonReason::PartialSliceCohort => partial += 1,
                SingletonReason::LoneRootChild => lone += 1,
                other => panic!("unexpected reason {other:?}"),
            }
        }
        assert_eq!((partial, lone), (2, 1));
    }

    /// Operand-edge commit witness (plan §8 FS1: "a hypothetical
    /// operand-vs-operand divergence uses the existing ReplaceAndPush fork
    /// kind, still consuming via the sub-parse"): a member whose leaf EDGE
    /// is the operand commits via `ReplaceAndPush { replace_symbol: the
    /// member marker }` in the emitted prelude.
    #[test]
    fn mixfix_param_leaf_commit_uses_replace_and_push() {
        let types = vec![lang_type("Expr", None)];
        let terms = vec![
            jrule("EAtom", "Expr", vec![], vec![lit("e")]),
            jrule(
                "MOne",
                "Expr",
                vec![simple("a", "Expr"), simple("b", "Expr")],
                vec![param("a"), lit("!"), lit("«"), param("b"), lit("»")],
            ),
            jrule(
                "MEmpty",
                "Expr",
                vec![simple("a", "Expr")],
                vec![param("a"), lit("!"), lit("«"), lit("»")],
            ),
        ];
        let def = mk_language("ParamLeafLang", types, terms);
        let (categories, per_cat) = cats_per_cat(&def);
        let prefix = build_prefix_factoring(&def, &categories, &per_cat);
        let mixfix = build_mixfix_factoring(&def, &categories, &per_cat, &prefix);
        let bucket = mixfix
            .iter()
            .find(|f| f.dispatch_cat_src_idx == 0)
            .and_then(|f| f.buckets.iter().find(|b| b.trigger == "!"))
            .expect("the ! bucket exists");
        assert_eq!(bucket.groups.len(), 1, "{:?}", bucket);
        let g = &bucket.groups[0];
        // MOne (rule 1) leafs on its OPERAND edge at depth 2 with remainder
        // (its » stays member-side); MEmpty (rule 2) on its » literal.
        let (leaf_item, m1) = g.roots[0].leaf_for(1).expect("MOne leafs");
        assert!(matches!(leaf_item, SpineItem::ParamParse { .. }));
        assert_eq!(
            m1.commit,
            MemberCommit::MixfixRun {
                rule_idx: 1,
                kind: 0,
                completed_idx: 0,
                sub_pos: 0
            },
        );
        assert!(m1.has_post_spine_remainder);
        let bundle = build_spine_emission_from_parts(&prefix, &mixfix, &def, &categories, &per_cat);
        let prelude = normalized(&bundle.mixfix_prelude_arms);
        assert!(
            prelude.contains("factoring::parameter_replace_branch(0u16,_pos,")
                && prelude.contains(
                    "||StackSymbolV2::mixfix_marker(0u16,1u16,0u8,__mixfix_continuation_bp,)"
                ),
            "the operand-edge commit rides ReplaceAndPush: {prelude}",
        );
    }

    /// Spine re-entry key uniqueness: two members sharing TWO operands on
    /// the spine path would re-enter at the same `(0, 0, 0)` — the cohort
    /// degrades with `MultiOperandSharedSpine` (loudly recorded, never
    /// silently mis-keyed).
    #[test]
    fn mixfix_multi_operand_shared_spine_defers() {
        let types = vec![lang_type("Expr", None)];
        let terms = vec![
            jrule("EAtom", "Expr", vec![], vec![lit("e")]),
            jrule(
                "MTwoX",
                "Expr",
                vec![simple("a", "Expr"), simple("b", "Expr"), simple("c", "Expr")],
                vec![
                    param("a"),
                    lit("!"),
                    lit("«"),
                    param("b"),
                    lit("»"),
                    lit("«"),
                    param("c"),
                    lit("»"),
                    lit("x"),
                ],
            ),
            jrule(
                "MTwoY",
                "Expr",
                vec![simple("a", "Expr"), simple("b", "Expr"), simple("c", "Expr")],
                vec![
                    param("a"),
                    lit("!"),
                    lit("«"),
                    param("b"),
                    lit("»"),
                    lit("«"),
                    param("c"),
                    lit("»"),
                    lit("y"),
                ],
            ),
        ];
        let def = mk_language("TwoOperandLang", types, terms);
        let (categories, per_cat) = cats_per_cat(&def);
        let prefix = build_prefix_factoring(&def, &categories, &per_cat);
        let model = build_mixfix_factoring(&def, &categories, &per_cat, &prefix);
        let bucket = model
            .iter()
            .find(|f| f.dispatch_cat_src_idx == 0)
            .and_then(|f| f.buckets.iter().find(|b| b.trigger == "!"))
            .expect("the ! bucket exists");
        assert!(bucket.groups.is_empty(), "{:?}", bucket.groups);
        assert_eq!(bucket.ineligible.len(), 1, "{:?}", bucket);
        assert!(matches!(bucket.ineligible[0].reason, IneligibleReason::MultiOperandSharedSpine,));
    }
}
