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
//! At `WpdaState::PrefixDispatch` on `@` in RhoCalc `Proc`, the generated
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
//! such as RhoCalc rules 15/16, whose whole tail is literals. Item equality:
//!
//!   - [`SpineItem::Literal`] — exact text plus the derived
//!     `required_top_cat` guard payload (equal by induction along a shared
//!     spine; carried in the key as defense against emission drift);
//!   - [`SpineItem::ParamParse`] — equal iff `(pushed category, cur_bp,
//!     collection = None)` equal, where `cur_bp` is the SAME
//!     `build_prefix_bp_map` lookup the `emit_binder_rule_body` ParamParse
//!     arm emits. Red-team AV2: the `prefix(220)` spec annotation does NOT
//!     surface here — `build_prefix_bp_map` only maps
//!     `classify_unary_prefix_shape` rules, so the six RhoCalc Short-group
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
//!     RhoCalc `POutputNil` and non-numeric wrappers such as
//!     `POutputQuotedEmpty` stay groupable — the pinned `@`-cohort trie
//!     depends on it).
//!   - Proper-prefix members (interior accept-nodes, e.g. RhoCalc
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

use std::collections::BTreeSet;

use mettail_ast::grammar::{GrammarRule, SyntaxExpr};
use mettail_ast::language::LanguageDef;

use super::binder::{
    binder_initial_body_cat, build_prefix_bp_map, classify_binder_in, lookup_src_idx,
    required_top_cat_after_position, BinderPosition,
};
use super::prefix::{classify_atomic, AtomicShape};

/// Base of the synthetic spine rule-index space: `SPINE_ID = SPINE_RULE_BASE +
/// group ordinal per category` (plan §2 item 1). Chosen clear of every real
/// per-category rule index and BELOW the recovery branch offset space
/// ([`super::forks::RECOVERY_BASE`] = `0xFE00`); amendment A9 asserts the
/// allocation never crosses either bound.
pub(crate) const SPINE_RULE_BASE: u16 = 0xF800;

// ═══════════════════════════════════════════════════════════════════════════
// Item model — the EMITTED-ACTION-SHAPE alphabet (plan §2 merge criterion).
// ═══════════════════════════════════════════════════════════════════════════

/// One post-trigger spine item, keyed by the shape of the action the per-rule
/// emission would produce for it. Equality of two items IS the merge
/// criterion (the red-team vindicated emitted-action-shape equality as the
/// only correct one — spec-level `prefix(N)` annotations do not reliably
/// surface in the emitted `cur_bp`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum SpineItem {
    /// A literal consume. Binder members emit it as the single-branch
    /// `GuardedConsumeAndReplace { expected_text, required_top_cat }` Fork
    /// (`emit_binder_rule_body`, binder.rs); nullary members consume the same
    /// text through the `MixfixLiteralRun{kind:2}` run with NO top-cat guard
    /// (`required_top_cat: None`). Along a shared spine the payloads agree by
    /// induction: a nullary member never follows a ParamParse edge (all its
    /// items are literals), and a binder literal following a literal (or the
    /// trigger) derives `None` exactly like the nullary source.
    Literal {
        text: String,
        required_top_cat: Option<u16>,
    },
    /// A plain sub-parse slot — emitted as `ReplaceAndPush {
    /// CategoryEntry(cat_src_idx), cur_bp }` (binder.rs ParamParse arm,
    /// `collection: None` only; collection slots terminate mergeability).
    ParamParse { cat_src_idx: u16, cur_bp: u8 },
}

/// Which state machine a member commits back into (red-team AV1).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum MemberKind {
    Binder,
    Nullary,
    /// F5-2 (2026-07-13, plan `f5_mixfix_cohorts_plan.md`): a member of an
    /// InfixLoop mixfix send cohort (rhocalc `!`/`!!`). Commits back into the
    /// member's OWN generic `MixfixLiteralRun` machinery at typed
    /// `(kind, completed_idx, sub_pos)` coordinates
    /// ([`MemberCommit::MixfixRun`], the A4-analog).
    Mixfix,
}

/// Amendment A4 — TYPED commit coordinates per member kind. The commit
/// happens AFTER the leaf edge is consumed (plan §2 items 3-4: divergence
/// children are `GuardedConsumeAndReplace`-style branches; COMMIT replaces
/// the spine marker with the member's own symbol at the member's own
/// numbering).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum MemberCommit {
    /// Resume as `rule_at(cat, rule_idx, resume_pos)` in `BinderRule`.
    Binder { rule_idx: u16, resume_pos: u8 },
    /// Resume inside the member's existing `MixfixLiteralRun { kind: 2 }`
    /// tail: mixfix-marker coordinates against the
    /// `mixfix_nullary_literals(cat, rule)` indexing.
    Nullary {
        rule_idx: u16,
        completed_idx: u8,
        sub_pos: u8,
    },
    /// F5-2 (A4-analog, plan §2.2): resume inside the member's existing
    /// generic `MixfixLiteralRun` machinery at the full
    /// `(kind, completed_idx, sub_pos)` coordinate — the commit CAR replaces
    /// the spine marker with `mixfix_marker(result, rule_idx, completed_idx)`
    /// and enters `MixfixLiteralRun { rule_idx, completed_idx, kind,
    /// sub_pos }`. The F0 `Nullary` variant is the `kind: 2, completed: 0`
    /// special case on the PREFIX surface; mixfix-cohort members (including
    /// their nullary members, e.g. rhocalc POutputEmpty) always use this
    /// variant so the coordinate law is stated once per surface.
    MixfixRun {
        rule_idx: u16,
        kind: u8,
        completed_idx: u8,
        sub_pos: u8,
    },
}

/// SPINE-POS → MEMBER-POS map (amendment A4, typed per member kind). Entry
/// `d` gives the member-side coordinate after consuming `d` post-trigger
/// spine items (`d ∈ 0..=leaf_depth`). Under F0 eligibility (Literal / plain
/// ParamParse only before divergence) every spine item corresponds to exactly
/// one member position, so the map is the arithmetic identity — stored
/// explicitly so F5 (optional groups, interior accepts) generalizes without
/// changing shape, and so the F3 FV lemmas (SpineSimulation) have a concrete
/// witness table.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum SpinePosMap {
    /// `pos_at_depth[d] = d + 1` — the 1-based BinderRule marker position.
    Binder { pos_at_depth: Vec<u8> },
    /// `sub_pos_at_depth[d] = d` — the MixfixLiteralRun literal cursor.
    Nullary { sub_pos_at_depth: Vec<u8> },
    /// F5-2 (A4-analog): `coords_at_depth[d]` = the member-side
    /// `(kind, completed_idx, sub_pos)` `MixfixLiteralRun` coordinate AFTER
    /// consuming `d` post-trigger items — recorded by the discovery walk
    /// that mirrors the generic arm's own transitions (kind-2 pre-operand
    /// literals; operand → `(0, completed, 0)` via Unwinding; kind-0
    /// following literals; kind-1 next-part preceding literals; operand k+1
    /// → `(0, k+1, 0)`).
    Mixfix { coords_at_depth: Vec<(u8, u8, u8)> },
}

/// A group member with its leaf assignment.
///
/// The `#[cfg_attr(not(test), allow(dead_code))]` fields below are INV-8 model
/// data: populated by member discovery and read only by the `#[cfg(test)]`
/// accounting assertions, so they are dead in the non-test lib build.
#[derive(Debug, Clone)]
pub(crate) struct GroupMember {
    #[cfg_attr(not(test), allow(dead_code))]
    pub kind: MemberKind,
    pub rule_idx: u16,
    /// Trie depth of the member's leaf: post-trigger items consumed on the
    /// spine INCLUDING the leaf edge.
    #[cfg_attr(not(test), allow(dead_code))]
    pub leaf_depth: u8,
    /// Typed commit coordinates (amendment A4).
    pub commit: MemberCommit,
    /// Spine-pos → member-pos map (amendment A4).
    #[cfg_attr(not(test), allow(dead_code))]
    pub pos_map: SpinePosMap,
    /// The member continues in its own machinery past the commit (collection
    /// tails, further literals/params) — as opposed to the leaf edge being
    /// its final item (where the commit position IS the final-pos
    /// Pop → fire arm).
    #[cfg_attr(not(test), allow(dead_code))]
    pub has_post_spine_remainder: bool,
}

/// One tree of a group's factored suffix FOREST. A root carries the group's
/// shared first post-trigger item; interior nodes are shared spine steps;
/// each leaf is exactly one member.
///
/// Child-item invariant (weakened by F5-1, red-team F-10 / FV-1(e′)): per
/// node, at most one INTERIOR child per item; leaf children may repeat an
/// item — an accept leaf shares its edge item with the continuation subtree
/// when one exists (and identical-sequence twins share theirs with each
/// other). Under the F0 stance (`S1F5_ACCEPT_CONTINUE == false`) no leaf
/// ever repeats an item because exhausted members are routed to
/// `interior_accepts` instead of leafing out.
#[derive(Debug)]
pub(crate) enum SpineTree {
    Interior {
        item: SpineItem,
        children: Vec<SpineTree>,
    },
    Leaf {
        item: SpineItem,
        member: GroupMember,
    },
}

impl SpineTree {
    pub(crate) fn item(&self) -> &SpineItem {
        match self {
            SpineTree::Interior { item, .. } | SpineTree::Leaf { item, .. } => item,
        }
    }

    pub(crate) fn leaf_count(&self) -> usize {
        match self {
            SpineTree::Leaf { .. } => 1,
            SpineTree::Interior { children, .. } => {
                children.iter().map(SpineTree::leaf_count).sum()
            },
        }
    }

    pub(crate) fn leaves(&self) -> Vec<&GroupMember> {
        match self {
            SpineTree::Leaf { member, .. } => vec![member],
            SpineTree::Interior { children, .. } => {
                let mut out = Vec::with_capacity(children.len());
                for child in children {
                    out.extend(child.leaves());
                }
                out
            },
        }
    }

    /// The leaf for `rule_idx` together with its leaf EDGE item, if present.
    // dead_code: model accessor, exercised only by the `#[cfg(test)]` INV-8 assertions.
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn leaf_for(&self, rule_idx: u16) -> Option<(&SpineItem, &GroupMember)> {
        match self {
            SpineTree::Leaf { item, member } if member.rule_idx == rule_idx => {
                Some((item, member))
            },
            SpineTree::Leaf { .. } => None,
            SpineTree::Interior { children, .. } => {
                children.iter().find_map(|child| child.leaf_for(rule_idx))
            },
        }
    }
}

/// An ELIGIBLE factored group: one spine branch replaces its members'
/// per-rule Fork branches (F1).
#[derive(Debug)]
pub(crate) struct SpineGroup {
    /// `SPINE_RULE_BASE + ordinal` within the owning category (plan §2 item
    /// 1; amendment A9 bounds asserted at allocation).
    pub spine_id: u16,
    /// Uniform initial `BinderRule.body_src_idx` across the group's binder
    /// members (eligibility assert, red-team AV2 gap b); the owning
    /// category's own src_idx for an all-nullary group (no BinderRule state
    /// consumes it before a commit in that case).
    pub body_src_idx: u16,
    /// The factored suffix FOREST (F5-1: [`build_tree`] returns sibling
    /// accept leaves alongside the interior remainder). Single-root while no
    /// member's whole item list is the root edge; multiple roots when a
    /// member accepts at depth 1 (root-accept — the pre-root arm itself
    /// becomes the accept fork). Root order is the NORMATIVE forest order
    /// (amendment A1, stated at [`build_tree`]): `remainder ++ accepts`.
    /// Under the F0 stance every eligible group is single-root.
    pub roots: Vec<SpineTree>,
}

impl SpineGroup {
    pub(crate) fn member_rule_idxs(&self) -> BTreeSet<u16> {
        self.leaves().iter().map(|m| m.rule_idx).collect()
    }

    // dead_code: model accessor, exercised only by the `#[cfg(test)]` INV-8 assertions.
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn leaf_count(&self) -> usize {
        self.roots.iter().map(SpineTree::leaf_count).sum()
    }

    pub(crate) fn leaves(&self) -> Vec<&GroupMember> {
        let mut out = Vec::with_capacity(self.roots.len());
        for root in &self.roots {
            out.extend(root.leaves());
        }
        out
    }

    /// The leaf for `rule_idx` together with its leaf EDGE item, if present
    /// (leaves ↔ members stay a bijection under F5-1 — accepts ARE leaves).
    // dead_code: model accessor, exercised only by the `#[cfg(test)]` INV-8 assertions.
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn leaf_for(&self, rule_idx: u16) -> Option<(&SpineItem, &GroupMember)> {
        self.roots.iter().find_map(|root| root.leaf_for(rule_idx))
    }
}

/// Why a bucket member is emitted as an ordinary (unfactored) singleton.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum SingletonReason {
    /// The member shares its first post-trigger item with no sibling.
    LoneRootChild,
    /// ★A2: the member participates in the `(cat, rule_idx)`-keyed cast
    /// machinery and must keep its own rule identity on every frame — see
    /// `numeric_cast_adapter::cast_machinery_participates`.
    CastMachinery,
    /// The member has no mergeable post-trigger item at all (its first item
    /// already terminates mergeability — e.g. RhoCalc `PNew`'s leading
    /// binder-list) — it commits at the trigger exactly as today.
    EmptySequence,
    /// [`super::forks::S1_FACTORING`] is `false`: the emission-effective
    /// partition degenerates to the identity (every member its own
    /// singleton).
    FactoringDisabled,
    /// F5-2 D-5 (whole-slice eligibility, mixfix surface only): the member
    /// belongs to a `(cat, trigger)` mixfix slice whose root partition did
    /// NOT cover the ENTIRE slice with one ≥2-member group (grouped +
    /// ungrouped members sharing the trigger) — the whole cohort degrades to
    /// unfactored per-member emission. Documented limitation; the loop-v2
    /// runtime shape stays trivial (spine pushed ⇒ skip the slice loop; else
    /// verbatim loop).
    PartialSliceCohort,
}

// dead_code: whole struct is INV-8 model data — constructed by discovery, read only by the `#[cfg(test)]` accounting assertions.
#[cfg_attr(not(test), allow(dead_code))]
#[derive(Debug, Clone)]
pub(crate) struct SingletonMember {
    pub rule_idx: u16,
    pub reason: SingletonReason,
}

/// Why a ≥2-member candidate group is NOT factored in F0 (emitted unfactored,
/// byte-identical to today; F5 territory).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum IneligibleReason {
    /// One or more members are proper prefixes of siblings (interior
    /// accept-nodes — e.g. RhoCalc `InputBindQuoted` inside the `@`-led
    /// query row). Modeled here, deferred to F5 (plan §5).
    InteriorAccept { accepting_rule_idxs: Vec<u16> },
    /// Binder members disagree on the initial `BinderRule.body_src_idx`
    /// (red-team AV2 gap b — the spine state would be ill-defined).
    NonUniformBodySrc { body_src_idxs: Vec<u16> },
    /// F5-2 (mixfix surface): members disagree on `result_src_idx` — the
    /// spine marker's category, the goal-gate check, and the fire output
    /// category all read it, so a mixed-result cohort cannot share one spine
    /// branch (`result_src`-uniformity is the mixfix analog of
    /// `body_src_idx`-uniformity).
    NonUniformResultSrc { result_src_idxs: Vec<u16> },
    /// F5-2 A-M5 (mitigant-(a) future-grammar guard): a literal item that a
    /// member consumes strictly AFTER its first operand is itself an
    /// operator trigger of the operand's category — the operand could ABSORB
    /// the divergence token, so two members could close on the SAME span and
    /// the min-member spine stamp would adjudicate an intra-cohort ⊕-tie
    /// that OFF adjudicates with distinct member stamps. Next-token-disjoint
    /// alone does NOT imply span-disjoint; the whole cohort degrades to
    /// unfactored.
    OperandAbsorbableDivergence { texts: Vec<String> },
    /// F5-2 spine-coordinate constraint: the SHARED spine path carries more
    /// than one operand item. The spine's post-operand re-entry coordinate
    /// is `(kind 0, marker.bp, 0)` via the Unwinding-MixfixMarker arm, and
    /// the width-1 spine keeps `marker.bp = 0` (no kind-1 bump runs on the
    /// spine), so a second shared operand would re-enter at the SAME
    /// `(0, 0, 0)` key as the first — an arm-key collision. The cohort
    /// degrades to unfactored (loudly recorded, never silently mis-keyed).
    MultiOperandSharedSpine,
}

// dead_code: whole struct is INV-8 model data — read only by the `#[cfg(test)]` accounting assertions.
#[cfg_attr(not(test), allow(dead_code))]
#[derive(Debug)]
pub(crate) struct IneligibleGroup {
    pub reason: IneligibleReason,
    pub member_rule_idxs: Vec<u16>,
}

/// One `(category, leading_literal)` prefix cohort.
///
/// `leading_literal` / `cohort_size` / `ineligible` / `singletons` are INV-8
/// model data read only by the `#[cfg(test)]` accounting assertions (dead in
/// the non-test lib build); only `groups` is consumed by emission.
#[derive(Debug)]
pub(crate) struct FactoringBucket {
    #[cfg_attr(not(test), allow(dead_code))]
    pub leading_literal: String,
    /// Total members discovered in this bucket BEFORE any exclusion — the
    /// INV-8 no-loss denominator (amendment A5): `Σ group leaves +
    /// Σ ineligible members + |singletons| == cohort_size`.
    #[cfg_attr(not(test), allow(dead_code))]
    pub cohort_size: usize,
    pub groups: Vec<SpineGroup>,
    #[cfg_attr(not(test), allow(dead_code))]
    pub ineligible: Vec<IneligibleGroup>,
    #[cfg_attr(not(test), allow(dead_code))]
    pub singletons: Vec<SingletonMember>,
}

#[derive(Debug)]
pub(crate) struct CategoryFactoring {
    pub category_src_idx: u16,
    pub buckets: Vec<FactoringBucket>,
}

// ═══════════════════════════════════════════════════════════════════════════
// Member discovery — mirrors the `prefix.rs` unified-bucket insertion
// conditions exactly (BinderPrefix / NullaryLiteralRun only).
// ═══════════════════════════════════════════════════════════════════════════

/// A bucket member before trie construction.
#[derive(Debug, Clone)]
struct CandidateMember {
    kind: MemberKind,
    rule_idx: u16,
    /// The member's MERGEABLE item prefix (cut at the first collection /
    /// binder-list / optional-group / guard item).
    items: Vec<SpineItem>,
    /// `true` iff the item sequence was cut (a non-mergeable item follows).
    truncated: bool,
    /// Total member-side positions (binder: `shape.positions.len()`;
    /// nullary: trailing-literal count) — for remainder detection.
    total_positions: usize,
    /// Binder members: the `binder_initial_body_cat`-derived src idx the
    /// per-rule dispatch arm carries (same `unwrap_or(category)` fallback
    /// as `prefix.rs`).
    body_src_idx: Option<u16>,
    /// F5-2 mixfix members ONLY: the member-side `MixfixLiteralRun`
    /// coordinate after each consumed item — `mixfix_coords[d]` = the state
    /// after `d` post-trigger consumes, `d ∈ 0..=items.len()` (entry 0 = the
    /// initial `(2, 0, 0)`). Empty for Binder/Nullary (prefix-surface)
    /// members.
    mixfix_coords: Vec<(u8, u8, u8)>,
}

/// Map a binder member's `BinderShape.positions` to its mergeable
/// [`SpineItem`] prefix. Returns `(items, truncated)`.
fn binder_items(
    positions: &[BinderPosition],
    category_src_idx: u16,
    rule_idx: u16,
    categories: &[String],
    prefix_bp_map: &std::collections::HashMap<(u16, u16), u8>,
) -> (Vec<SpineItem>, bool) {
    let mut items = Vec::with_capacity(positions.len());
    for (idx, position) in positions.iter().enumerate() {
        match position {
            BinderPosition::Literal(text) => {
                let previous = if idx > 0 { positions.get(idx - 1) } else { None };
                items.push(SpineItem::Literal {
                    text: text.clone(),
                    required_top_cat: required_top_cat_after_position(previous, categories),
                });
            },
            BinderPosition::ParamParse { cat, collection: None } => {
                let cat_src_idx = lookup_src_idx(cat, categories).unwrap_or(0);
                // The SAME lookup `emit_binder_rule_body` emits: per-(cat,
                // rule) — `classify_unary_prefix_shape` rules map to their
                // prefix bp, everything else falls back to 0 (red-team AV2:
                // this is why the six Short pos-1 arms are byte-equal).
                let cur_bp = prefix_bp_map
                    .get(&(category_src_idx, rule_idx))
                    .copied()
                    .unwrap_or(0u8);
                items.push(SpineItem::ParamParse { cat_src_idx, cur_bp });
            },
            // Collection ParamParse / binder-list / guard / optional-group:
            // terminates mergeability (leaf-side only, plan §2).
            BinderPosition::ParamParse { collection: Some(_), .. }
            | BinderPosition::BinderIdent
            | BinderPosition::BinderListLoop { .. }
            | BinderPosition::GuardSlot
            | BinderPosition::OptionalGroup { .. } => return (items, true),
        }
    }
    (items, false)
}

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
    let mut out = Vec::new();
    for (rule_i, rule) in rules.iter().enumerate() {
        let rule_idx = rule_i as u16;
        match classify_atomic(rule, language) {
            AtomicShape::CrossCatPrefixUnary { .. } => continue,
            AtomicShape::NullaryLiteralRun { trigger, trailing_literals, .. } => {
                let items: Vec<SpineItem> = trailing_literals
                    .iter()
                    .map(|text| SpineItem::Literal {
                        text: text.clone(),
                        required_top_cat: None,
                    })
                    .collect();
                let total_positions = items.len();
                out.push((
                    trigger.clone(),
                    CandidateMember {
                        kind: MemberKind::Nullary,
                        rule_idx,
                        items,
                        truncated: false,
                        total_positions,
                        body_src_idx: None,
                        mixfix_coords: Vec::new(),
                    },
                ));
                continue;
            },
            AtomicShape::CrossCatProjection { .. } => continue,
            _ => {},
        }
        let Some(shape) = classify_binder_in(rule, language) else {
            continue;
        };
        let Some(SyntaxExpr::Literal(trigger)) =
            rule.syntax_pattern.as_ref().and_then(|sp| sp.first())
        else {
            continue;
        };
        if trigger == "(" {
            continue;
        }
        let body_src_idx = binder_initial_body_cat(&shape)
            .and_then(|name| lookup_src_idx(name, categories))
            .unwrap_or(category_src_idx);
        let (items, truncated) = binder_items(
            &shape.positions,
            category_src_idx,
            rule_idx,
            categories,
            prefix_bp_map,
        );
        out.push((
            trigger.clone(),
            CandidateMember {
                kind: MemberKind::Binder,
                rule_idx,
                items,
                truncated,
                total_positions: shape.positions.len(),
                body_src_idx: Some(body_src_idx),
                mixfix_coords: Vec::new(),
            },
        ));
    }
    out
}

// ═══════════════════════════════════════════════════════════════════════════
// Trie build.
// ═══════════════════════════════════════════════════════════════════════════

/// Finalize a member's leaf at `leaf_depth` (post-trigger items consumed
/// INCLUDING the leaf edge) — typed commit coordinates + identity pos-map
/// (amendment A4).
fn finalize_leaf(member: CandidateMember, leaf_depth: usize) -> GroupMember {
    assert!(
        leaf_depth < u8::MAX as usize,
        "S1-FACTORING: leaf depth {leaf_depth} exceeds the u8 marker-position space",
    );
    let depth_u8 = leaf_depth as u8;
    let (commit, pos_map) = match member.kind {
        MemberKind::Binder => (
            MemberCommit::Binder {
                rule_idx: member.rule_idx,
                resume_pos: depth_u8 + 1,
            },
            SpinePosMap::Binder {
                pos_at_depth: (0..=depth_u8).map(|d| d + 1).collect(),
            },
        ),
        MemberKind::Nullary => (
            MemberCommit::Nullary {
                rule_idx: member.rule_idx,
                completed_idx: 0,
                sub_pos: depth_u8,
            },
            SpinePosMap::Nullary {
                sub_pos_at_depth: (0..=depth_u8).collect(),
            },
        ),
        MemberKind::Mixfix => {
            // F5-2 (A4-analog): the commit coordinate is the RECORDED
            // member-side state after consuming `leaf_depth` items — the
            // discovery walk mirrored the generic MixfixLiteralRun arm's own
            // transitions, so the commit lands exactly on the member's
            // machinery (nullary member at `(2, 0, depth)`; operand members
            // at `(0, completed, following-consumed)`; the FV-1 coordinate
            // law).
            assert!(
                member.mixfix_coords.len() > leaf_depth,
                "S1-FACTORING F5-2: mixfix member (rule {}) has {} recorded \
                 coords but leafs at depth {leaf_depth} — the discovery walk \
                 drifted from the item list",
                member.rule_idx,
                member.mixfix_coords.len(),
            );
            let (kind, completed_idx, sub_pos) = member.mixfix_coords[leaf_depth];
            (
                MemberCommit::MixfixRun {
                    rule_idx: member.rule_idx,
                    kind,
                    completed_idx,
                    sub_pos,
                },
                SpinePosMap::Mixfix {
                    coords_at_depth: member.mixfix_coords[..=leaf_depth].to_vec(),
                },
            )
        },
    };
    GroupMember {
        kind: member.kind,
        rule_idx: member.rule_idx,
        leaf_depth: depth_u8,
        commit,
        pos_map,
        has_post_spine_remainder: member.truncated || member.total_positions > leaf_depth,
    }
}

/// Recursive trie build, returning the FOREST for the node reached by
/// consuming `edge_item` at `depth` (`members` all matched `items[0..depth]`;
/// `edge_item == items[depth - 1]`). A single remaining member commits
/// immediately (earliest-uniqueness leaf).
///
/// Members whose sequence exhausts at an interior node while siblings
/// continue (proper-prefix members, interior accept-nodes) are stance-gated:
///
///   - `accept_continue == false` (the F0 stance): recorded in
///     `interior_accepts`; the caller marks the group ineligible and the
///     bucket emits unfactored — byte-identical to the pre-F5-1 shipped
///     model. Identical-twin members (equal full sequences) both land here,
///     so a multi-member leaf can never form below.
///   - `accept_continue == true` (F5-1,
///     [`super::forks::S1F5_ACCEPT_CONTINUE`]): the exhausted member becomes
///     an ORDINARY LEAF sharing `edge_item` with the continuation subtree —
///     a SIBLING of the interior node built here (the sibling-leaf form; the
///     ε-branch reading is refuted — no non-consuming marker-replace
///     `ForkActionKind` exists, plan §9-FS1). [`finalize_leaf`] at
///     `depth == items.len()` lands on the member's OWN completion
///     machinery: a true accept resumes at `positions.len() + 1` (its
///     final-pos Pop → fire arm) / a nullary accept at `sub_pos ==
///     parts_len` (its tail-complete arm); a truncated accept (collection
///     tail) resumes at its own mid-rule arm exactly like today's
///     `has_post_spine_remainder` leaves (the rule-20 precedent).
///
/// ★A1 — NORMATIVE FOREST ORDER: `remainder ++ accepts` — the
/// interior-continue subtree FIRST, accept leaves LAST. This is the single
/// normative statement of the branch order; parents splice child forests
/// into their `children` lists verbatim, [`flatten_forest`] applies the same
/// rule to multi-root pre-root children, and every emitted divergence fork
/// therefore puts the spine-continue branch before the accept commit
/// branches. The choice preserves OFF's relative branch order at the only
/// real cohort (rhocalc InputBind@ emits [QuotedQuery, Quoted]) and
/// minimizes `source_priority` order channels; the emission pins assert it.
///
/// A part whose members ALL exhaust here (identical-sequence twins) returns
/// an accepts-only forest — never `Interior { children: [] }` (red-team
/// F-10; the synthetic all-twins witnesses pin both the root-level and the
/// spliced form).
fn build_tree(
    depth: usize,
    edge_item: SpineItem,
    members: Vec<CandidateMember>,
    accept_continue: bool,
    interior_accepts: &mut Vec<u16>,
) -> Vec<SpineTree> {
    if members.len() == 1 {
        let member = members
            .into_iter()
            .next()
            .expect("a len()==1 vector yields its member");
        return vec![SpineTree::Leaf {
            item: edge_item,
            member: finalize_leaf(member, depth),
        }];
    }
    // ≥2 members: exhausted members leaf out (or defer, per the stance); the
    // rest partition by the next item, preserving first-occurrence order
    // (rule declaration order — deterministic).
    let mut order: Vec<SpineItem> = Vec::new();
    let mut parts: Vec<Vec<CandidateMember>> = Vec::new();
    let mut accepts: Vec<SpineTree> = Vec::new();
    for member in members {
        if member.items.len() == depth {
            if accept_continue {
                accepts.push(SpineTree::Leaf {
                    item: edge_item.clone(),
                    member: finalize_leaf(member, depth),
                });
            } else {
                interior_accepts.push(member.rule_idx);
            }
            continue;
        }
        let item = member.items[depth].clone();
        match order.iter().position(|existing| existing == &item) {
            Some(i) => parts[i].push(member),
            None => {
                order.push(item);
                parts.push(vec![member]);
            },
        }
    }
    let mut children: Vec<SpineTree> = Vec::with_capacity(parts.len());
    for (item, part) in order.into_iter().zip(parts) {
        children.extend(build_tree(depth + 1, item, part, accept_continue, interior_accepts));
    }
    if children.is_empty() {
        // Every member exhausted at this node (all-twins part, F-10):
        // accepts-only forest. Empty overall only under the F0 stance,
        // where the caller's `interior_accepts` check discards the forest.
        return accepts;
    }
    let mut forest = Vec::with_capacity(1 + accepts.len());
    forest.push(SpineTree::Interior { item: edge_item, children });
    forest.extend(accepts);
    forest
}

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
    build_prefix_factoring_with(
        language,
        categories,
        per_cat,
        super::forks::S1F5_ACCEPT_CONTINUE,
    )
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
    let mut out = Vec::with_capacity(per_cat.len());
    for (cat_i, rules) in per_cat.iter().enumerate() {
        let category_src_idx = cat_i as u16;
        let members =
            discover_members(language, categories, category_src_idx, rules, &prefix_bp_map);
        // Bucket by leading literal, first-seen order (mirrors the
        // `unified_order` insertion-order discipline in `prefix.rs`).
        let mut bucket_order: Vec<String> = Vec::new();
        let mut bucket_members: Vec<Vec<CandidateMember>> = Vec::new();
        for (trigger, member) in members {
            match bucket_order.iter().position(|t| t == &trigger) {
                Some(i) => bucket_members[i].push(member),
                None => {
                    bucket_order.push(trigger);
                    bucket_members.push(vec![member]);
                },
            }
        }
        let mut buckets = Vec::with_capacity(bucket_order.len());
        // SPINE_ID ordinals are per-category, over ELIGIBLE groups only, in
        // bucket-then-group discovery order (deterministic).
        let mut next_spine_ordinal: u16 = 0;
        for (leading_literal, bucket) in bucket_order.into_iter().zip(bucket_members) {
            let cohort_size = bucket.len();
            let mut groups: Vec<SpineGroup> = Vec::new();
            let mut ineligible: Vec<IneligibleGroup> = Vec::new();
            let mut singletons: Vec<SingletonMember> = Vec::new();
            // Member-level exclusions first (★A2 / empty sequence), then
            // root-partition of the remainder.
            let mut groupable: Vec<CandidateMember> = Vec::with_capacity(bucket.len());
            for member in bucket {
                let rule = &rules[member.rule_idx as usize];
                if crate::gen::runtime::numeric_cast_adapter::cast_machinery_participates(
                    language, rule,
                ) {
                    singletons.push(SingletonMember {
                        rule_idx: member.rule_idx,
                        reason: SingletonReason::CastMachinery,
                    });
                } else if member.items.is_empty() {
                    singletons.push(SingletonMember {
                        rule_idx: member.rule_idx,
                        reason: SingletonReason::EmptySequence,
                    });
                } else {
                    groupable.push(member);
                }
            }
            // Root partition = the groups (plan §2: partition by the first
            // post-trigger item's emitted-action shape).
            let mut root_order: Vec<SpineItem> = Vec::new();
            let mut root_parts: Vec<Vec<CandidateMember>> = Vec::new();
            for member in groupable {
                let item = member.items[0].clone();
                match root_order.iter().position(|existing| existing == &item) {
                    Some(i) => root_parts[i].push(member),
                    None => {
                        root_order.push(item);
                        root_parts.push(vec![member]);
                    },
                }
            }
            for (root_item, part) in root_order.into_iter().zip(root_parts) {
                if part.len() == 1 {
                    let lone = &part[0];
                    singletons.push(SingletonMember {
                        rule_idx: lone.rule_idx,
                        reason: SingletonReason::LoneRootChild,
                    });
                    continue;
                }
                let member_rule_idxs: Vec<u16> = part.iter().map(|m| m.rule_idx).collect();
                let body_src_idxs: Vec<u16> = {
                    let mut seen = BTreeSet::new();
                    part.iter()
                        .filter_map(|m| m.body_src_idx)
                        .filter(|b| seen.insert(*b))
                        .collect()
                };
                let mut interior_accepts: Vec<u16> = Vec::new();
                let roots =
                    build_tree(1, root_item, part, accept_continue, &mut interior_accepts);
                if !interior_accepts.is_empty() {
                    // Only reachable with `accept_continue == false` (F5-1
                    // dormant stance) — [`build_tree`] leafs exhausted
                    // members out otherwise.
                    ineligible.push(IneligibleGroup {
                        reason: IneligibleReason::InteriorAccept {
                            accepting_rule_idxs: interior_accepts,
                        },
                        member_rule_idxs,
                    });
                    continue;
                }
                if body_src_idxs.len() > 1 {
                    // Red-team AV2 gap b: the spine's single BinderRule
                    // body_src_idx would be ill-defined. Covers accept
                    // members' body_src too — `body_src_idxs` is computed
                    // over the whole part before the trie build.
                    ineligible.push(IneligibleGroup {
                        reason: IneligibleReason::NonUniformBodySrc { body_src_idxs },
                        member_rule_idxs,
                    });
                    continue;
                }
                // Eligible: every leaf carries exactly one rule by
                // construction (single-member recursion base; under the F0
                // stance twins and proper prefixes were routed to
                // interior_accepts above, under F5-1 they ARE leaves).
                let leaf_count: usize = roots.iter().map(SpineTree::leaf_count).sum();
                assert_eq!(
                    leaf_count,
                    member_rule_idxs.len(),
                    "S1-FACTORING: eligible group leaf count must equal its member count \
                     (cat {category_src_idx}, trigger {leading_literal:?})",
                );
                let body_src_idx = body_src_idxs
                    .first()
                    .copied()
                    // All-nullary group: no BinderRule state consumes the
                    // field before a commit; carry the owning category.
                    .unwrap_or(category_src_idx);
                groups.push(SpineGroup {
                    spine_id: SPINE_RULE_BASE + next_spine_ordinal,
                    body_src_idx,
                    roots,
                });
                next_spine_ordinal += 1;
            }
            buckets.push(FactoringBucket {
                leading_literal,
                cohort_size,
                groups,
                ineligible,
                singletons,
            });
        }
        // ★A9: the synthetic spine id space must stay clear of the recovery
        // branch offset space AND the u16 domain.
        let spine_id_end = SPINE_RULE_BASE as u32 + next_spine_ordinal as u32;
        assert!(
            spine_id_end < super::forks::RECOVERY_BASE as u32,
            "S1-FACTORING A9: category {category_src_idx} allocates {next_spine_ordinal} spine \
             ids ending at {spine_id_end:#06x}, colliding with RECOVERY_BASE {:#06x}",
            super::forks::RECOVERY_BASE,
        );
        assert!(
            spine_id_end < u16::MAX as u32,
            "S1-FACTORING A9: category {category_src_idx} spine id space end {spine_id_end:#06x} \
             overflows u16",
        );
        out.push(CategoryFactoring { category_src_idx, buckets });
    }
    out
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
    let mut out = Vec::with_capacity(per_cat.len());
    for (cat_i, rules) in per_cat.iter().enumerate() {
        let category_src_idx = cat_i as u16;
        let members =
            discover_members(language, categories, category_src_idx, rules, &prefix_bp_map);
        let mut bucket_order: Vec<String> = Vec::new();
        let mut bucket_singletons: Vec<Vec<SingletonMember>> = Vec::new();
        for (trigger, member) in members {
            let singleton = SingletonMember {
                rule_idx: member.rule_idx,
                reason: SingletonReason::FactoringDisabled,
            };
            match bucket_order.iter().position(|t| t == &trigger) {
                Some(i) => bucket_singletons[i].push(singleton),
                None => {
                    bucket_order.push(trigger);
                    bucket_singletons.push(vec![singleton]);
                },
            }
        }
        let buckets = bucket_order
            .into_iter()
            .zip(bucket_singletons)
            .map(|(leading_literal, singletons)| FactoringBucket {
                leading_literal,
                cohort_size: singletons.len(),
                groups: Vec::new(),
                ineligible: Vec::new(),
                singletons,
            })
            .collect();
        out.push(CategoryFactoring { category_src_idx, buckets });
    }
    out
}

// ═══════════════════════════════════════════════════════════════════════════
// F5-2 — MIXFIX SEND COHORTS: the SECOND factoring surface (plan
// `scratchpad/zz_probes/f5_mixfix_cohorts_plan.md` + its §RED-TEAM
// GO-WITH-AMENDMENTS A-M1..A-M5, 2026-07-13).
//
// The InfixLoop mixfix fan (engine_impl.rs `__mixfix_slice` loop) forks one
// `mixfix_marker` + `MixfixLiteralRun{kind:2}` branch per slice member; the
// bundled census has exactly TWO factorable cohorts — rhocalc Name `!`
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

/// One factorable mixfix cohort (an ELIGIBLE group covering its whole
/// `(dispatch category, trigger)` slice).
#[derive(Debug)]
pub(crate) struct MixfixGroup {
    /// `SPINE_RULE_BASE + ordinal` in the RESULT category's id space,
    /// CONTINUING after the category's prefix groups (amendment A9 bounds
    /// asserted at allocation; the pure sentinel family `u16::MAX-2..` and
    /// `RECOVERY_BASE` stay disjoint).
    pub spine_id: u16,
    /// Uniform member result category (eligibility) — the marker category,
    /// the goal-gate operand, and the fire output category all read it.
    pub result_src_idx: u16,
    /// D-1 full-admission floor: the spine branch is admitted iff
    /// `min_l_bp >= cur_bp` (all members pass — l_bp is the only
    /// member-varying admission input; goal/method-name gates are
    /// member-uniform by construction).
    pub min_l_bp: u8,
    /// AV5-analog weight/action identity: the MIN member rule idx (never the
    /// spine id) — stamps the trigger branch weight, the lex-alt `lex_w_alt`
    /// wrap, and the `LexAltMixfixOp.rule_idx` action-kind field (A-M5).
    pub min_member_rule_idx: u16,
    /// `(l_bp, rule_idx)` per member in slice order — receipts.
    pub member_l_bps: Vec<(u8, u16)>,
    /// First-seen-order union of the members' own action-entry
    /// `expected_input_cats` (mirrors `semantic_actions`' mixfix derivation:
    /// `[dispatch_cat] ++ per part (operand cat | ANY_CAT for a rep)`;
    /// nullary members contribute `[dispatch_cat]` only) — the H9 poison
    /// `action_for` row payload.
    pub expected_cats_union: Vec<u16>,
    /// Uniform Fix-B method-name-prune evidence across members (A-M4): the
    /// first post-trigger literal as `__method_name_admits` derives it
    /// (`part0.preceding.first()` / `nullary_literals.first()` / `None` for
    /// an operand-/rep-leading part-0). Uniform by the shared root item;
    /// asserted at build so spine-prune ≡ member-prune.
    // dead_code: model field read only by the `#[cfg(test)]` assertions.
    #[cfg_attr(not(test), allow(dead_code))]
    pub fixb_literal: Option<String>,
    /// The suffix trie — single-root by construction (the root partition IS
    /// the group criterion).
    pub roots: Vec<SpineTree>,
}

impl MixfixGroup {
    pub(crate) fn member_rule_idxs(&self) -> Vec<u16> {
        self.member_l_bps.iter().map(|&(_, r)| r).collect()
    }

    // dead_code: model accessor, exercised only by the `#[cfg(test)]` INV-8 assertions.
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn leaves(&self) -> Vec<&GroupMember> {
        let mut out = Vec::with_capacity(self.roots.len());
        for root in &self.roots {
            out.extend(root.leaves());
        }
        out
    }
}

/// One `(dispatch category, trigger)` mixfix slice with its factoring
/// outcome — the INV-8-mixfix accounting unit
/// (`Σ group leaves + Σ ineligible members + |singletons| == slice.len()`).
#[derive(Debug)]
pub(crate) struct MixfixBucket {
    pub trigger: String,
    /// The EMITTED slice tuples `(l_bp, result_src, rule_idx)` — mirrors
    /// `mixfix_bp_<cat>` exactly (same grouping, same `GEN1_MAX_SLICE`
    /// truncation).
    // dead_code: INV-8 model data (`slice`/`ineligible`/`singletons`) read only by `#[cfg(test)]` accounting.
    #[cfg_attr(not(test), allow(dead_code))]
    pub slice: Vec<(u8, u16, u16)>,
    pub groups: Vec<MixfixGroup>,
    #[cfg_attr(not(test), allow(dead_code))]
    pub ineligible: Vec<IneligibleGroup>,
    #[cfg_attr(not(test), allow(dead_code))]
    pub singletons: Vec<SingletonMember>,
}

#[derive(Debug)]
pub(crate) struct MixfixFactoring {
    pub dispatch_cat_src_idx: u16,
    pub buckets: Vec<MixfixBucket>,
}

/// A discovered mixfix slice member before trie construction.
struct MixfixCandidate {
    member: CandidateMember,
    l_bp: u8,
    result_src_idx: u16,
    expected_cats: Vec<u16>,
    fixb_literal: Option<String>,
}

/// Map one mixfix operator's post-trigger surface to its mergeable
/// [`SpineItem`] prefix PLUS the member-side `MixfixLiteralRun` coordinate
/// after each consume (the A4-analog walk — mirrors the generic arm's own
/// transitions). Returns `(items, coords, truncated)`;
/// `coords.len() == items.len() + 1` (entry 0 = the initial `(2, 0, 0)`).
fn mixfix_member_items(
    op: &mettail_prattail::binding_power::InfixOperator,
    categories: &[String],
) -> (Vec<SpineItem>, Vec<(u8, u8, u8)>, bool) {
    let lookup = |name: &str| -> u16 {
        categories
            .iter()
            .position(|c| c == name)
            .map(|i| i as u16)
            .unwrap_or(0)
    };
    let mut items: Vec<SpineItem> = Vec::new();
    let mut coords: Vec<(u8, u8, u8)> = vec![(2, 0, 0)];
    if op.mixfix_parts.is_empty() {
        // Nullary run (`parts_len == 0`): the whole tail is literals walked
        // at `(2, 0, sub_pos)` by the `(2, None) if parts_len == 0` arm.
        items.reserve_exact(op.nullary_literals.len());
        coords.reserve_exact(op.nullary_literals.len());
        for (d, text) in op.nullary_literals.iter().enumerate() {
            items.push(SpineItem::Literal {
                text: text.clone(),
                required_top_cat: None,
            });
            coords.push((2, 0, (d + 1) as u8));
        }
        return (items, coords, false);
    }
    for (part_i, part) in op.mixfix_parts.iter().enumerate() {
        if part.repetition.is_some() {
            // A `*sep` repetition terminates mergeability (leaf-side only):
            // the member commits at or before this depth and runs the rep in
            // its own CollectionLoop machinery.
            return (items, coords, true);
        }
        let completed = part_i as u8;
        // Preceding literals: part 0 runs at kind 2 (pre-operand run); later
        // parts at kind 1 with the marker still at `part_i - 1` (the
        // generic `(1, _)` arm bumps the marker only when preceding is
        // exhausted).
        for (j, text) in part.preceding_terminals.iter().enumerate() {
            items.push(SpineItem::Literal {
                text: text.clone(),
                required_top_cat: None,
            });
            if part_i == 0 {
                coords.push((2, 0, (j + 1) as u8));
            } else {
                coords.push((1, completed - 1, (j + 1) as u8));
            }
        }
        // The operand: always dispatched at `cur_bp: 0` (the mixfix machine
        // convention, engine_impl kind-2/kind-1 operand arms). Post-operand
        // the Unwinding-MixfixMarker arm reads `marker.bp == part_i` and
        // re-enters at `(0, part_i, 0)`.
        items.push(SpineItem::ParamParse {
            cat_src_idx: lookup(&part.operand_category),
            cur_bp: 0,
        });
        coords.push((0, completed, 0));
        for (j, text) in part.following_terminals.iter().enumerate() {
            items.push(SpineItem::Literal {
                text: text.clone(),
                required_top_cat: None,
            });
            coords.push((0, completed, (j + 1) as u8));
        }
    }
    (items, coords, false)
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
    // Operand-absorbability oracle (A-M5): every (category, terminal) that
    // carries ANY operator row — a post-operand divergence literal matching
    // one of these could be absorbed INTO the operand sub-parse.
    let operator_trigger_keys: BTreeSet<(u16, String)> =
        grouped.keys().cloned().collect();
    // Per-RESULT-category ordinal continuation after the prefix groups.
    let mut next_ordinal: Vec<u16> = vec![0; per_cat.len()];
    for cat_fact in prefix_partition {
        let groups: usize = cat_fact.buckets.iter().map(|b| b.groups.len()).sum();
        if let Some(slot) = next_ordinal.get_mut(cat_fact.category_src_idx as usize) {
            *slot = groups as u16;
        }
    }

    let mut per_dispatch: HashMap<u16, Vec<MixfixBucket>> = HashMap::new();
    // BTreeMap iteration order = deterministic (dispatch cat, terminal)
    // order — the allocation order for the continued ordinals.
    for ((dispatch_cat, terminal), ops) in &grouped {
        let mixfix_ops: Vec<&super::infix::GroupedOp<'_>> = ops
            .iter()
            .filter(|g| g.op.is_mixfix)
            .take(super::infix::GEN1_MAX_SLICE)
            .collect();
        if mixfix_ops.is_empty() {
            continue;
        }
        let slice: Vec<(u8, u16, u16)> = mixfix_ops
            .iter()
            .map(|g| (g.op.left_bp, g.result_src_idx, g.rule_idx))
            .collect();
        let mut candidates: Vec<MixfixCandidate> = Vec::with_capacity(mixfix_ops.len());
        for g in &mixfix_ops {
            let (member_items, coords, truncated) = mixfix_member_items(g.op, categories);
            let total_positions = member_items.len();
            // The member's own action-entry expected_input_cats (mirrors
            // semantic_actions' mixfix arm: LHS cat first, then per part).
            let lookup = |name: &str| -> u16 {
                categories
                    .iter()
                    .position(|c| c == name)
                    .map(|i| i as u16)
                    .unwrap_or(0)
            };
            let mut expected_cats: Vec<u16> =
                Vec::with_capacity(1 + g.op.mixfix_parts.len());
            expected_cats.push(*dispatch_cat);
            for part in &g.op.mixfix_parts {
                if part.repetition.is_some() {
                    expected_cats.push(u16::MAX);
                } else {
                    expected_cats.push(lookup(&part.operand_category));
                }
            }
            // Fix-B evidence, EXACTLY as `__method_name_admits` derives it.
            let fixb_literal = match g.op.mixfix_parts.first() {
                Some(part) if part.repetition.is_none() => {
                    part.preceding_terminals.first().cloned()
                },
                // Rep part-0: `mixfix_part(.., 0)` is None and
                // `mixfix_nullary_literals` has no row ⇒ None (always-keep).
                Some(_) => None,
                None => op_first_nullary_literal(g.op),
            };
            candidates.push(MixfixCandidate {
                member: CandidateMember {
                    kind: MemberKind::Mixfix,
                    rule_idx: g.rule_idx,
                    items: member_items,
                    truncated,
                    total_positions,
                    body_src_idx: None,
                    mixfix_coords: coords,
                },
                l_bp: g.op.left_bp,
                result_src_idx: g.result_src_idx,
                expected_cats,
                fixb_literal,
            });
        }

        // ── member-level exclusions (mirrored from F0) ─────────────────────
        let mut singletons: Vec<SingletonMember> = Vec::new();
        let mut groupable: Vec<MixfixCandidate> = Vec::with_capacity(candidates.len());
        for cand in candidates {
            let rule = per_cat
                .get(cand.result_src_idx as usize)
                .and_then(|rules| rules.get(cand.member.rule_idx as usize));
            let is_cast = rule
                .map(|r| {
                    crate::gen::runtime::numeric_cast_adapter::cast_machinery_participates(
                        language, r,
                    )
                })
                .unwrap_or(false);
            if is_cast {
                singletons.push(SingletonMember {
                    rule_idx: cand.member.rule_idx,
                    reason: SingletonReason::CastMachinery,
                });
            } else if cand.member.items.is_empty() {
                // Rep-part-0 members (rhocalc InputBindPolyadic `,`): no
                // mergeable post-trigger item at all.
                singletons.push(SingletonMember {
                    rule_idx: cand.member.rule_idx,
                    reason: SingletonReason::EmptySequence,
                });
            } else {
                groupable.push(cand);
            }
        }

        // ── root partition + D-5 whole-slice coverage ──────────────────────
        let mut root_order: Vec<SpineItem> = Vec::new();
        let mut root_parts: Vec<Vec<MixfixCandidate>> = Vec::new();
        for cand in groupable {
            let item = cand.member.items[0].clone();
            match root_order.iter().position(|existing| existing == &item) {
                Some(i) => root_parts[i].push(cand),
                None => {
                    root_order.push(item);
                    root_parts.push(vec![cand]);
                },
            }
        }
        let whole_slice_one_group = singletons.is_empty()
            && root_parts.len() == 1
            && root_parts[0].len() == slice.len()
            && slice.len() >= 2;
        let mut groups: Vec<MixfixGroup> = Vec::new();
        let mut ineligible: Vec<IneligibleGroup> = Vec::new();
        if whole_slice_one_group {
            let root_item = root_order
                .into_iter()
                .next()
                .expect("a single root part carries its item");
            let part = root_parts
                .into_iter()
                .next()
                .expect("a single root part exists");
            match build_mixfix_group(
                *dispatch_cat,
                terminal,
                root_item,
                part,
                &operator_trigger_keys,
                &mut next_ordinal,
            ) {
                Ok(group) => groups.push(group),
                Err(bad) => ineligible.push(bad),
            }
        } else {
            // D-5 degrade: the cohort stays unfactored. Lone root children
            // keep the F0 reason; members of a would-be group that does not
            // cover the whole slice record the partial-slice reason.
            for (part_i, part) in root_parts.into_iter().enumerate() {
                let lone = part.len() == 1;
                let _ = part_i;
                for cand in part {
                    singletons.push(SingletonMember {
                        rule_idx: cand.member.rule_idx,
                        reason: if lone {
                            SingletonReason::LoneRootChild
                        } else {
                            SingletonReason::PartialSliceCohort
                        },
                    });
                }
            }
        }

        per_dispatch
            .entry(*dispatch_cat)
            .or_default()
            .push(MixfixBucket {
                trigger: terminal.clone(),
                slice,
                groups,
                ineligible,
                singletons,
            });
    }

    // ★A9-analog: the CONTINUED per-category ordinal end must stay clear of
    // the recovery offset space and u16 (the prefix-side asserts covered the
    // prefix count; re-assert over the mixfix-extended end).
    for (cat_i, ordinal_end) in next_ordinal.iter().enumerate() {
        let spine_id_end = SPINE_RULE_BASE as u32 + *ordinal_end as u32;
        assert!(
            spine_id_end < super::forks::RECOVERY_BASE as u32,
            "S1-FACTORING F5-2 A9: category {cat_i} mixfix-extended spine ids end at \
             {spine_id_end:#06x}, colliding with RECOVERY_BASE {:#06x}",
            super::forks::RECOVERY_BASE,
        );
        assert!(
            spine_id_end < u16::MAX as u32,
            "S1-FACTORING F5-2 A9: category {cat_i} mixfix-extended spine id end \
             {spine_id_end:#06x} overflows u16",
        );
    }

    let mut out: Vec<MixfixFactoring> = Vec::with_capacity(per_dispatch.len());
    let mut dispatch_cats: Vec<u16> = per_dispatch.keys().copied().collect();
    dispatch_cats.sort_unstable();
    for cat in dispatch_cats {
        let buckets = per_dispatch
            .remove(&cat)
            .expect("dispatch cat key collected from the map");
        out.push(MixfixFactoring { dispatch_cat_src_idx: cat, buckets });
    }
    out
}

fn op_first_nullary_literal(
    op: &mettail_prattail::binding_power::InfixOperator,
) -> Option<String> {
    op.nullary_literals.first().cloned()
}

/// Eligibility + trie build for one whole-slice candidate group.
fn build_mixfix_group(
    dispatch_cat: u16,
    trigger: &str,
    root_item: SpineItem,
    part: Vec<MixfixCandidate>,
    operator_trigger_keys: &BTreeSet<(u16, String)>,
    next_ordinal: &mut [u16],
) -> Result<MixfixGroup, IneligibleGroup> {
    let member_rule_idxs: Vec<u16> = part.iter().map(|c| c.member.rule_idx).collect();
    let member_l_bps: Vec<(u8, u16)> =
        part.iter().map(|c| (c.l_bp, c.member.rule_idx)).collect();
    // Uniform result_src (the mixfix analog of body_src uniformity).
    let result_src_idxs: Vec<u16> = {
        let mut seen = BTreeSet::new();
        part.iter()
            .map(|c| c.result_src_idx)
            .filter(|r| seen.insert(*r))
            .collect()
    };
    if result_src_idxs.len() > 1 {
        return Err(IneligibleGroup {
            reason: IneligibleReason::NonUniformResultSrc { result_src_idxs },
            member_rule_idxs,
        });
    }
    let result_src_idx = result_src_idxs[0];
    // A-M5 operand-absorbability guard (mitigant (a) is corpus-scoped —
    // next-token-disjoint does NOT imply span-disjoint for arbitrary
    // grammars): a literal consumed strictly AFTER an operand must not be an
    // operator trigger of that operand's category.
    let mut absorbable: Vec<String> = Vec::new();
    for cand in &part {
        let mut operand_cat: Option<u16> = None;
        for item in &cand.member.items {
            match item {
                SpineItem::ParamParse { cat_src_idx, .. } => {
                    operand_cat = Some(*cat_src_idx);
                },
                SpineItem::Literal { text, .. } => {
                    if let Some(cat) = operand_cat {
                        if operator_trigger_keys.contains(&(cat, text.clone()))
                            && !absorbable.contains(text)
                        {
                            absorbable.push(text.clone());
                        }
                    }
                },
            }
        }
    }
    if !absorbable.is_empty() {
        return Err(IneligibleGroup {
            reason: IneligibleReason::OperandAbsorbableDivergence { texts: absorbable },
            member_rule_idxs,
        });
    }
    // A-M4: the Fix-B method-name-prune evidence is member-uniform (implied
    // by the shared root item: a Literal root IS every operand-bearing
    // member's `part0.preceding[0]` and every nullary member's
    // `nullary_literals[0]`; a ParamParse root ⇒ None for all). Drift =
    // codegen panic, never a silent spine-vs-member prune divergence.
    let fixb_literal = part[0].fixb_literal.clone();
    for cand in &part {
        assert_eq!(
            cand.fixb_literal, fixb_literal,
            "S1-FACTORING F5-2 A-M4: mixfix cohort (dispatch cat {dispatch_cat}, \
             trigger {trigger:?}) has non-uniform Fix-B first-literal evidence — \
             spine-prune would diverge from member-prune",
        );
    }
    // Trie build — accept_continue is ALWAYS false on the mixfix surface
    // (interior accepts route the WHOLE group to ineligible, F0-style).
    let min_l_bp = part
        .iter()
        .map(|c| c.l_bp)
        .min()
        .expect("a ≥2-member part has members");
    let min_member_rule_idx = part
        .iter()
        .map(|c| c.member.rule_idx)
        .min()
        .expect("a ≥2-member part has members");
    // First-seen-order union of the members' expected_input_cats.
    let mut expected_cats_union: Vec<u16> = Vec::new();
    for cand in &part {
        for cat in &cand.expected_cats {
            if !expected_cats_union.contains(cat) {
                expected_cats_union.push(*cat);
            }
        }
    }
    let members: Vec<CandidateMember> = part.into_iter().map(|c| c.member).collect();
    let mut interior_accepts: Vec<u16> = Vec::new();
    let roots = build_tree(
        1,
        root_item,
        members,
        /* accept_continue = */ false,
        &mut interior_accepts,
    );
    if !interior_accepts.is_empty() {
        return Err(IneligibleGroup {
            reason: IneligibleReason::InteriorAccept {
                accepting_rule_idxs: interior_accepts,
            },
            member_rule_idxs,
        });
    }
    let leaf_count: usize = roots.iter().map(SpineTree::leaf_count).sum();
    assert_eq!(
        leaf_count,
        member_rule_idxs.len(),
        "S1-FACTORING F5-2: eligible mixfix group leaf count must equal its member \
         count (dispatch cat {dispatch_cat}, trigger {trigger:?})",
    );
    assert_eq!(
        roots.len(),
        1,
        "S1-FACTORING F5-2: a mixfix group is single-root by construction (the root \
         partition IS the group criterion; dispatch cat {dispatch_cat}, trigger \
         {trigger:?})",
    );
    // Spine re-entry key uniqueness: the width-1 spine keeps marker.bp = 0,
    // so ≥2 operands on the SHARED path would collide at `(0, 0, 0)`.
    // Computed directly on the interior coordinates (see
    // `mixfix_spine_arm_coords`); duplicate ⇒ degrade, loudly recorded.
    if mixfix_spine_arm_coords(&roots[0]).is_none() {
        return Err(IneligibleGroup {
            reason: IneligibleReason::MultiOperandSharedSpine,
            member_rule_idxs,
        });
    }
    let ordinal = next_ordinal
        .get_mut(result_src_idx as usize)
        .expect("result category index in range");
    let spine_id = SPINE_RULE_BASE + *ordinal;
    *ordinal += 1;
    Ok(MixfixGroup {
        spine_id,
        result_src_idx,
        min_l_bp,
        min_member_rule_idx,
        member_l_bps,
        expected_cats_union,
        fixb_literal,
        roots,
    })
}

/// The SPINE-side arm plan of a single-root mixfix trie: the PRE-ROOT arm
/// key `(2, 0, 0)` (the state the fan pushes — its arm consumes the ROOT
/// EDGE itself, the F1 pre-root convention transported to mixfix
/// coordinates) plus, per INTERIOR node `n` in preorder, the arm key = the
/// spine state AFTER consuming `n`'s edge item — that arm consumes `n`'s
/// CHILDREN's edges (chain step or divergence fork). Returns `None` when
/// two arms would collide on a key (a second shared operand re-enters at
/// the same `(0, 0, 0)` via the width-1 spine's un-bumped `marker.bp == 0`
/// — the [`IneligibleReason::MultiOperandSharedSpine`] condition).
fn mixfix_spine_arm_coords(root: &SpineTree) -> Option<Vec<((u8, u8, u8), &SpineTree)>> {
    /// The spine state after consuming `item` from `state` (spine
    /// coordinates use kinds 2 and 0 only — post-operand literals are all
    /// kind-0; the spine never runs kind 1 because its marker never bumps).
    fn advance(state: (u8, u8, u8), item: &SpineItem) -> (u8, u8, u8) {
        match item {
            SpineItem::Literal { .. } => match state {
                (2, c, s) => (2, c, s + 1),
                (0, c, s) => (0, c, s + 1),
                other => panic!(
                    "S1-FACTORING F5-2: spine coordinate walk reached kind {} — \
                     only kinds 2 and 0 occur on a spine path",
                    other.0,
                ),
            },
            // The descent keeps the SPINE marker (bp = 0) on top; the
            // Unwinding-MixfixMarker arm re-enters at (0, marker.bp = 0, 0).
            SpineItem::ParamParse { .. } => (0, 0, 0),
        }
    }
    let mut out: Vec<((u8, u8, u8), &SpineTree)> = Vec::new();
    let mut seen: BTreeSet<(u8, u8, u8)> = BTreeSet::new();
    seen.insert((2, 0, 0)); // the pre-root arm key
    // (interior node, state BEFORE consuming its edge item).
    let mut stack: Vec<(&SpineTree, (u8, u8, u8))> = vec![(root, (2, 0, 0))];
    while let Some((node, state_before)) = stack.pop() {
        let SpineTree::Interior { item, children } = node else {
            continue;
        };
        let arm_key = advance(state_before, item);
        if !seen.insert(arm_key) {
            return None;
        }
        out.push((arm_key, node));
        for child in children.iter().rev() {
            stack.push((child, arm_key));
        }
    }
    Some(out)
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
    let mut per_dispatch: HashMap<u16, Vec<MixfixBucket>> = HashMap::new();
    for ((dispatch_cat, terminal), ops) in &grouped {
        let mixfix_ops: Vec<&super::infix::GroupedOp<'_>> = ops
            .iter()
            .filter(|g| g.op.is_mixfix)
            .take(super::infix::GEN1_MAX_SLICE)
            .collect();
        if mixfix_ops.is_empty() {
            continue;
        }
        let slice: Vec<(u8, u16, u16)> = mixfix_ops
            .iter()
            .map(|g| (g.op.left_bp, g.result_src_idx, g.rule_idx))
            .collect();
        let singletons: Vec<SingletonMember> = mixfix_ops
            .iter()
            .map(|g| SingletonMember {
                rule_idx: g.rule_idx,
                reason: SingletonReason::FactoringDisabled,
            })
            .collect();
        per_dispatch
            .entry(*dispatch_cat)
            .or_default()
            .push(MixfixBucket {
                trigger: terminal.clone(),
                slice,
                groups: Vec::new(),
                ineligible: Vec::new(),
                singletons,
            });
    }
    let mut out: Vec<MixfixFactoring> = Vec::with_capacity(per_dispatch.len());
    let mut dispatch_cats: Vec<u16> = per_dispatch.keys().copied().collect();
    dispatch_cats.sort_unstable();
    for cat in dispatch_cats {
        let buckets = per_dispatch
            .remove(&cat)
            .expect("dispatch cat key collected from the map");
        out.push(MixfixFactoring { dispatch_cat_src_idx: cat, buckets });
    }
    out
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
    let mut rows: Vec<(u16, u16)> = Vec::new();
    for fact in &partition {
        for bucket in &fact.buckets {
            for group in &bucket.groups {
                rows.push((group.result_src_idx, group.spine_id));
            }
        }
    }
    rows
}

// ═══════════════════════════════════════════════════════════════════════════
// Tests — the F0 gate's rhocalc trie pins (real grammar, real indices),
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

/// How a BinderPrefix/NullaryLiteralRun descriptor is emitted under the
/// factored partition (absent from the map = ordinary singleton emission,
/// byte-identical to today).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum SpineDisposition {
    /// First member (bucket discovery order) of an eligible group: emit the
    /// group's ONE spine trigger branch at this member's position.
    GroupFirst {
        spine_id: u16,
        body_src_idx: u16,
        /// AV5 weight identity: the MIN member rule idx (never SPINE_ID).
        weight_rule_idx: u16,
    },
    /// Non-first member of an eligible group: emit nothing (the spine branch
    /// at the first member's position covers it).
    GroupRest,
}

/// Per-category lex-alt surface adjustments (A3).
#[derive(Debug, Default)]
pub(crate) struct SpineLexAlt {
    /// Grouped member rule idxs whose per-member PrefixOp/NullaryPrefixRun
    /// entries are REPLACED by group entries (assert: no per-member entries
    /// for these under the const).
    pub grouped: HashMap<u16, SpineDisposition>,
}

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

/// F5-2: one factored mixfix cohort's emission coordinates.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct MixfixGroupEmission {
    /// The InfixLoop dispatch category (rhocalc Name = 3).
    pub dispatch_cat_src_idx: u16,
    /// The trigger terminal (`"!"` / `"!!"`).
    pub trigger: String,
    /// Uniform member result category (rhocalc Proc = 0).
    pub result_src_idx: u16,
    pub spine_id: u16,
    /// D-1 full-admission floor (min over member l_bps).
    pub min_l_bp: u8,
    /// AV5-analog identity (min member rule idx — weight stamps + the
    /// `LexAltMixfixOp.rule_idx` action-kind field, A-M5).
    pub min_member_rule_idx: u16,
    pub member_rule_idxs: Vec<u16>,
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

/// One flattened spine node during emission.
struct FlatNode<'t> {
    node_id: u8,
    children: Vec<(&'t SpineTree, u8)>, // child tree + child node id
}

/// Preorder node-id assignment over a group FOREST (F5-1). Interior nodes
/// get arm ids; leaves are consumed as EDGES of their parent's arm (no own
/// arm).
///
/// EDGE CONVENTION (F1 root-edge fix, 2026-07-12): every `SpineTree` node
/// carries the item on the edge INTO it (a root's item = the group's FIRST
/// post-trigger item), and an ARM consumes EDGES — so the arm at node `n`
/// emits the actions consuming `n`'s CHILDREN's items. The root edges
/// therefore need a SYNTHETIC PRE-ROOT arm: node id 1 (the coordinate the
/// spine trigger branch pushes, `rule_at(cat, SPINE_ID, 1)`) consumes the
/// forest roots' items — mirroring the member-side convention where arm
/// position `p` consumes `positions[p-1]` (the original arm 1 consumes the
/// first post-trigger item). Without the pre-root arm the first
/// post-trigger item would never be consumed (arm 1 would fork over the
/// root's CHILDREN edges — e.g. `@ Nil !…` dispatching `!`/`!!` guards
/// against the `Nil` token).
///
/// The pre-root children ARE the forest roots in the normative A1 order
/// (`remainder ++ accepts`, see [`build_tree`]) — a multi-root forest
/// (root accepts / root twins) makes the pre-root arm itself the accept
/// fork. Interior roots take ids from 2 in forest order, so a single-root
/// forest reproduces the F1 id assignment exactly (root = 2, descendants
/// from 3, preorder).
fn flatten_forest(roots: &[SpineTree]) -> Vec<FlatNode<'_>> {
    let mut out: Vec<FlatNode<'_>> = Vec::new();
    // The F1 "root must be Interior" assert generalizes (plan §6): the
    // forest is non-empty and carries one leaf per member of a ≥2-member
    // group (the leaf/member equality itself is asserted at build).
    assert!(
        !roots.is_empty(),
        "S1-FACTORING F5-1: an eligible group's forest must be non-empty",
    );
    assert!(
        roots.iter().map(SpineTree::leaf_count).sum::<usize>() >= 2,
        "S1-FACTORING F5-1: an eligible group's forest must carry ≥2 leaves \
         (one per member of a ≥2-member group)",
    );
    // Pre-root arm: node 1 consumes the root EDGES; interior roots land on
    // their own arms at ids assigned from 2, leaf roots commit (id 0).
    let mut next_id: u8 = 2;
    let mut pre_root_children: Vec<(&SpineTree, u8)> = Vec::with_capacity(roots.len());
    for root in roots {
        let cid = match root {
            SpineTree::Interior { .. } => {
                let cid = next_id;
                assert!(
                    next_id < 250,
                    "S1-FACTORING F1: spine node-id space exceeded (u8 marker positions)",
                );
                next_id += 1;
                cid
            },
            SpineTree::Leaf { .. } => 0,
        };
        pre_root_children.push((root, cid));
    }
    // (tree, assigned id) worklist — preorder, root-major.
    let mut stack: Vec<(&SpineTree, u8)> = Vec::with_capacity(roots.len());
    for (root, cid) in pre_root_children.iter().rev() {
        if *cid != 0 {
            stack.push((root, *cid));
        }
    }
    out.push(FlatNode { node_id: 1, children: pre_root_children });
    while let Some((node, node_id)) = stack.pop() {
        let SpineTree::Interior { children, .. } = node else {
            continue;
        };
        let mut child_entries = Vec::with_capacity(children.len());
        for child in children {
            let cid = match child {
                SpineTree::Interior { .. } => {
                    let cid = next_id;
                    assert!(
                        next_id < 250,
                        "S1-FACTORING F1: spine node-id space exceeded (u8 marker positions)",
                    );
                    next_id += 1;
                    cid
                },
                // Leaves carry no arm of their own — the parent's arm
                // consumes the leaf edge and COMMITS.
                SpineTree::Leaf { .. } => 0,
            };
            child_entries.push((child, cid));
        }
        // Push interior children for preorder continuation.
        for (child, cid) in child_entries.iter().rev() {
            if *cid != 0 {
                stack.push((child, *cid));
            }
        }
        out.push(FlatNode { node_id, children: child_entries });
    }
    out
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
                    StackSymbolV2::mixfix_marker(#cat, #rule_idx, 0u8)
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
                mettail_prattail::wpda_walker::ForkBranch {
                    symbol: #sym,
                    weight: lex_one(),
                    new_state: #state,
                    action_kind:
                        mettail_prattail::wpda_walker::ForkActionKind::GuardedConsumeAndReplace {
                            expected_text: #text.to_string(),
                            required_top_cat: #req,
                        },
                }
            }
        },
        SpineItem::ParamParse { cat_src_idx, cur_bp } => {
            // The branch PUSHES the operand CategoryEntry; the marker
            // replacement rides the action kind (walker ReplaceAndPush
            // fork semantics — binder collection-arm precedent).
            quote! {
                mettail_prattail::wpda_walker::ForkBranch {
                    symbol: StackSymbolV2::category_entry(#cat_src_idx),
                    weight: lex_one(),
                    new_state: WpdaState::PrefixDispatch {
                        pos: _pos,
                        cur_bp: #cur_bp,
                    },
                    action_kind:
                        mettail_prattail::wpda_walker::ForkActionKind::ReplaceAndPush {
                            replace_symbol: #sym,
                        },
                }
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
    build_spine_emission_from_parts(
        &partition,
        &mixfix_partition,
        language,
        categories,
        per_cat,
    )
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
    let mut dispositions: Vec<HashMap<u16, SpineDisposition>> =
        (0..per_cat.len()).map(|_| HashMap::new()).collect();
    // Task #10 item 1: `GroupFirst rule -> ordered members` per cat (see the
    // SpineEmission field doc) — filled in the SAME loop that assigns
    // dispositions, from the SAME `ordered` list.
    let mut group_members: Vec<HashMap<u16, Vec<u16>>> =
        (0..per_cat.len()).map(|_| HashMap::new()).collect();
    let mut lex_alt: Vec<SpineLexAlt> =
        (0..per_cat.len()).map(|_| SpineLexAlt::default()).collect();
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
                let body_src_idx = group.body_src_idx;
                let members = group.member_rule_idxs(); // BTreeSet — min first
                let weight_rule_idx = *members
                    .iter()
                    .next()
                    .expect("an eligible group has members");
                // Dispositions: first member in BUCKET DISCOVERY ORDER (the
                // emission order of the per-rule branches) carries the spine
                // branch; the rest are silent. Discovery order = leaf order
                // of the tree restricted to... members were bucketed in rule
                // declaration order, so min rule_idx = the first-emitted
                // member.
                let mut first = true;
                let mut ordered: Vec<u16> = members.iter().copied().collect();
                ordered.sort_unstable();
                // Task #10 item 1: the GroupFirst member keys the group's
                // ORDERED member list (the same list the disposition loop
                // walks) for the fork-emission ordinal derivation.
                if let Some(&first_member) = ordered.first() {
                    group_members[cat_usize].insert(first_member, ordered.clone());
                }
                for m in ordered {
                    let d = if first {
                        first = false;
                        SpineDisposition::GroupFirst { spine_id, body_src_idx, weight_rule_idx }
                    } else {
                        SpineDisposition::GroupRest
                    };
                    dispositions[cat_usize].insert(m, d);
                    lex_alt[cat_usize].grouped.insert(m, d);
                }
                // ── binder arms ──────────────────────────────────────────
                for node in flatten_forest(&group.roots) {
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
                                    return WpdaStepAction::Fork {
                                        branches: vec![#b],
                                        consume_trigger: false,
                                    };
                                }
                            },
                            SpineItem::ParamParse { cat_src_idx, cur_bp } => {
                                let (sym, state) =
                                    child_target_tokens(cat, spine_id, child, *cid);
                                let _ = state; // param chains resume via PrefixDispatch
                                quote! {
                                    return WpdaStepAction::ReplaceAndPush {
                                        replace_symbol: #sym,
                                        push_symbol: StackSymbolV2::category_entry(#cat_src_idx),
                                        weight: lex_one(),
                                        new_state: WpdaState::PrefixDispatch {
                                            pos: _pos,
                                            cur_bp: #cur_bp,
                                        },
                                    };
                                }
                            },
                        }
                    } else {
                        // Divergence arm: one branch per trie child; literal
                        // branches die on their guards (the shared
                        // evidence-prune, plan §2 item 3).
                        quote! {
                            return WpdaStepAction::Fork {
                                branches: vec![#(#branches),*],
                                consume_trigger: false,
                            };
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
                // (`shape.action_args`: `Term(cat)` → category index with the
                // same `.position(..).unwrap_or(0)` lookup; every non-Term
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
                let mut union: Vec<u16> = Vec::new();
                for m in members.iter().copied() {
                    let Some(shape) = classify_binder_in(&rules[m as usize], language) else {
                        continue; // Nullary member: arity-0 entry, no cats.
                    };
                    for kind in &shape.action_args {
                        let ci = match kind {
                            ActionArgKind::Term(cat) => categories
                                .iter()
                                .position(|c| c == cat)
                                .map(|i| i as u16)
                                .unwrap_or(0),
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
                assert!(
                    lead_conjunction,
                    "S1-FACTORING A7: group (cat {cat}, spine {spine_id:#06x}) has a member \
                     without a leading literal trigger — eligibility drifted",
                );
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
    let mut mixfix_groups: Vec<MixfixGroupEmission> = Vec::new();
    let mut mixfix_fan_arm_streams: Vec<TokenStream> = Vec::new();
    let mut mixfix_prelude_arm_streams: Vec<TokenStream> = Vec::new();
    for fact in mixfix_partition {
        let dispatch_cat = fact.dispatch_cat_src_idx;
        for bucket in &fact.buckets {
            for group in &bucket.groups {
                any_groups = true;
                let result_src = group.result_src_idx;
                let spine_id = group.spine_id;
                let min_l_bp = group.min_l_bp;
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
                    assert!(
                        !leads_with_literal,
                        "S1-FACTORING F5-2 A7-mixfix: group (result {result_src}, spine \
                         {spine_id:#06x}) member {m} LEADS with a literal — mixfix \
                         cohort members are operand-leading by construction",
                    );
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
                mixfix_fan_arm_streams.push(mixfix_fan_group_arm(
                    dispatch_cat,
                    trigger,
                    group,
                ));
                mixfix_prelude_arm_streams.push(mixfix_prelude_group_arms(group));
                mixfix_groups.push(MixfixGroupEmission {
                    dispatch_cat_src_idx: dispatch_cat,
                    trigger: trigger.clone(),
                    result_src_idx: result_src,
                    spine_id,
                    min_l_bp,
                    min_member_rule_idx: min_member,
                    member_rule_idxs: members,
                });
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
    SpineEmission {
        dispositions,
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
fn mixfix_fan_group_arm(
    dispatch_cat: u16,
    trigger: &str,
    group: &MixfixGroup,
) -> TokenStream {
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
                mettail_prattail::wpda_walker::ForkBranch {
                    symbol: StackSymbolV2::mixfix_marker(
                        #result_src, #spine_id, 0,
                    ),
                    weight: lex_w(
                        mettail_prattail::automata::lex_weight::BP_TIER_MIXFIX,
                        #result_src, #min_member,
                    ),
                    new_state: WpdaState::MixfixLiteralRun {
                        result_src_idx: #result_src,
                        rule_idx: #spine_id,
                        completed_idx: 0,
                        kind: 2,
                        sub_pos: 0,
                    },
                    action_kind:
                        mettail_prattail::wpda_walker::ForkActionKind::Push,
                },
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
    let arm_plan = mixfix_spine_arm_coords(root)
        .expect("eligibility rejected colliding spine coordinates");
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
        arms.push(mixfix_spine_step_arm(
            result_src,
            spine_id,
            *arm_key,
            &child_entries,
        ));
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
                quote! { StackSymbolV2::mixfix_marker(#result_src, #spine_id, #c) },
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
            let MemberCommit::MixfixRun { rule_idx, kind, completed_idx, sub_pos } =
                &member.commit
            else {
                panic!(
                    "S1-FACTORING F5-2: mixfix trie leaf (rule {}) carries a \
                     non-MixfixRun commit — the discovery kind drifted",
                    member.rule_idx,
                );
            };
            (
                quote! {
                    StackSymbolV2::mixfix_marker(#result_src, #rule_idx, #completed_idx)
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
///   - 1 ParamParse child: the operand descent — same-cat `Advance` into
///     `PrefixDispatch` under the SPINE marker (the part-0-under-marker
///     convention) / cross-cat `Push(category_entry_goal)`.
///   - ≥2 children (divergence): literal children contribute one
///     `ConsumeAtAndReplace` branch per lattice target (commit or spine
///     continuation); a ParamParse child contributes one UNCONDITIONAL
///     branch (descent, or `ReplaceAndPush` commit for an operand-edge
///     leaf). Zero live branches → `Error`; exactly one → the equivalent
///     NON-FORK action (plan §2.2: "if only A, the single-target
///     ConsumeAtAndReplace; B alone, emit the Advance"); otherwise a
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
        assert!(
            matches!(child, SpineTree::Interior { .. }),
            "S1-FACTORING F5-2: a single spine-arm child is Interior by \
             construction (single-member parts leaf out at the parent)",
        );
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
                let descent = if *cat_src_idx == result_src {
                    quote! {
                        return WpdaStepAction::Advance(WpdaState::PrefixDispatch {
                            pos: _pos,
                            cur_bp: #cur_bp,
                        });
                    }
                } else {
                    quote! {
                        return WpdaStepAction::Push {
                            symbol: StackSymbolV2::category_entry_goal(#cat_src_idx),
                            weight: lex_one(),
                            new_state: WpdaState::PrefixDispatch {
                                pos: _pos,
                                cur_bp: #cur_bp,
                            },
                        };
                    }
                };
                return quote! { #key_pat => { #descent } };
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
        let (sym, state) =
            mixfix_child_target_tokens(result_src, spine_id, child, *child_after);
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
                    if let Some(&__spine_np) = #t_ident.first() {
                        return WpdaStepAction::ConsumeAtAndReplace {
                            symbol: #sym,
                            weight: lex_one(),
                            new_state: #state,
                            next_pos: __spine_np,
                        };
                    }
                });
                push_stmts.push(quote! {
                    for __spine_np in &#t_ident {
                        __spine_branches.push(
                            mettail_prattail::wpda_walker::ForkBranch {
                                symbol: #sym,
                                weight: lex_one(),
                                new_state: #state,
                                action_kind:
                                    mettail_prattail::wpda_walker::ForkActionKind::ConsumeAtAndReplace {
                                        next_pos: *__spine_np,
                                    },
                            },
                        );
                    }
                });
            },
            SpineItem::ParamParse { cat_src_idx, cur_bp } => {
                let (branch, nonfork) = match child {
                    SpineTree::Interior { .. } => {
                        if *cat_src_idx == result_src {
                            (
                                quote! {
                                    mettail_prattail::wpda_walker::ForkBranch {
                                        symbol: #sym,
                                        weight: lex_one(),
                                        new_state: WpdaState::PrefixDispatch {
                                            pos: _pos,
                                            cur_bp: #cur_bp,
                                        },
                                        action_kind:
                                            mettail_prattail::wpda_walker::ForkActionKind::Advance,
                                    }
                                },
                                quote! {
                                    return WpdaStepAction::Advance(
                                        WpdaState::PrefixDispatch {
                                            pos: _pos,
                                            cur_bp: #cur_bp,
                                        },
                                    );
                                },
                            )
                        } else {
                            (
                                quote! {
                                    mettail_prattail::wpda_walker::ForkBranch {
                                        symbol: StackSymbolV2::category_entry_goal(#cat_src_idx),
                                        weight: lex_one(),
                                        new_state: WpdaState::PrefixDispatch {
                                            pos: _pos,
                                            cur_bp: #cur_bp,
                                        },
                                        action_kind:
                                            mettail_prattail::wpda_walker::ForkActionKind::Push,
                                    }
                                },
                                quote! {
                                    return WpdaStepAction::Push {
                                        symbol: StackSymbolV2::category_entry_goal(#cat_src_idx),
                                        weight: lex_one(),
                                        new_state: WpdaState::PrefixDispatch {
                                            pos: _pos,
                                            cur_bp: #cur_bp,
                                        },
                                    };
                                },
                            )
                        }
                    },
                    SpineTree::Leaf { .. } => {
                        // Operand-edge commit (FS1: consuming via the
                        // sub-parse): replace the SPINE marker with the
                        // member marker, push the operand entry. Same-cat
                        // uses the goal-free entry (mirrors the generic
                        // part-0 Advance admission); cross-cat the strict
                        // goal entry (the generic kind-1 form).
                        let entry = if *cat_src_idx == result_src {
                            quote! { StackSymbolV2::category_entry(#cat_src_idx) }
                        } else {
                            quote! { StackSymbolV2::category_entry_goal(#cat_src_idx) }
                        };
                        (
                            quote! {
                                mettail_prattail::wpda_walker::ForkBranch {
                                    symbol: #entry,
                                    weight: lex_one(),
                                    new_state: WpdaState::PrefixDispatch {
                                        pos: _pos,
                                        cur_bp: #cur_bp,
                                    },
                                    action_kind:
                                        mettail_prattail::wpda_walker::ForkActionKind::ReplaceAndPush {
                                            replace_symbol: #sym,
                                        },
                                }
                            },
                            quote! {
                                return WpdaStepAction::ReplaceAndPush {
                                    replace_symbol: #sym,
                                    push_symbol: #entry,
                                    weight: lex_one(),
                                    new_state: WpdaState::PrefixDispatch {
                                        pos: _pos,
                                        cur_bp: #cur_bp,
                                    },
                                };
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
            if __spine_lit_total == 0 {
                return WpdaStepAction::Error(format!(
                    "mixfix spine divergence mismatch at pos {} (spine {}:{}) — \
                     no lattice edge matches any commit literal",
                    _pos, #result_src, #spine_id,
                ));
            }
        },
        1 => {
            let nonfork = &uncond_nonforks[0];
            quote! {
                if __spine_lit_total == 0 {
                    #nonfork
                }
            }
        },
        // ≥2 unconditional branches always fork.
        _ => TokenStream::new(),
    };
    let singleton_handler = if n_uncond == 0 {
        quote! {
            if __spine_lit_total == 1 {
                #(#singleton_checks)*
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
            let mut __spine_branches: Vec<
                mettail_prattail::wpda_walker::ForkBranch<__DwW>,
            > = Vec::with_capacity(#n_uncond_lit + __spine_lit_total);
            #(#push_stmts)*
            return WpdaStepAction::Fork {
                branches: __spine_branches,
                consume_trigger: false,
            };
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
        __pd_branches.push(mettail_prattail::wpda_walker::ForkBranch {
            symbol: StackSymbolV2::rule_at(
                #category_src_idx, #spine_id, 1u8, Some(_outer_bp),
            ),
            weight: lex_w(0.0, #category_src_idx, #weight_rule_idx),
            new_state: WpdaState::BinderRule {
                result_src_idx: #category_src_idx,
                rule_idx: #spine_id,
                body_src_idx: #body_src_idx,
                outer_bp: _outer_bp,
            },
            action_kind:
                mettail_prattail::wpda_walker::ForkActionKind::ConsumeAndPush {
                    trigger_mode:
                        mettail_prattail::wpda_walker::TriggerMode::ConsumeAsTriggerOnly,
                },
        });
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use mettail_ast::grammar::{convert_term_context_to_items, TermParam};
    use mettail_ast::language::{LangType, LanguageDef};
    use mettail_ast::types::{CollectionType, TypeExpr};
    use proc_macro2::Span;
    use syn::Ident;

    // ── real-grammar loading (the pinned trie is against the ACTUAL rhocalc
    //    source, run through the same pre-codegen pipeline as `language!`:
    //    parse → auto-inject → per-category materialization) ─────────────────

    fn parse_bundled_language(manifest_relative: &str) -> LanguageDef {
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join(manifest_relative);
        let source = std::fs::read_to_string(&path)
            .unwrap_or_else(|e| panic!("bundled language source {path:?} readable: {e}"));
        let file =
            syn::parse_file(&source).expect("bundled language source parses as a Rust file");
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

    fn rhocalc() -> LanguageDef {
        parse_bundled_language("../languages/src/rhocalc.rs")
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
            .unwrap_or_else(|| panic!("category {name} present"))
            as u16
    }

    fn rule_idx(per_cat_rules: &[GrammarRule], label: &str) -> u16 {
        per_cat_rules
            .iter()
            .position(|r| r.label == label)
            .unwrap_or_else(|| panic!("rule {label} present"))
            as u16
    }

    fn bucket<'a>(
        model: &'a [CategoryFactoring],
        cat: u16,
        literal: &str,
    ) -> &'a FactoringBucket {
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
        fn item(it: &SpineItem) -> String {
            match it {
                SpineItem::Literal { text, .. } => format!("L({text})"),
                SpineItem::ParamParse { cat_src_idx, cur_bp } => {
                    format!("P({cat_src_idx},{cur_bp})")
                },
            }
        }
        match tree {
            SpineTree::Leaf { item: it, member } => {
                format!("{}=>r{}", item(it), member.rule_idx)
            },
            SpineTree::Interior { item: it, children } => {
                let inner: Vec<String> = children.iter().map(render).collect();
                format!("{}[{}]", item(it), inner.join(" "))
            },
        }
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
        TermParam::Simple { name: id(name), ty: TypeExpr::Base(id(cat)) }
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
            label: id(label),
            category: id(category),
            items,
            bindings,
            term_context: Some(tc),
            syntax_pattern: Some(sp),
            rust_code: None,
            eval_mode: None,
            is_right_assoc: false,
            prefix_bp: None,
            tier_directive: None,
            is_auto_injected: false,
            doc_comment: None,
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
            native_type: native.map(|t| syn::parse_str::<syn::Type>(t).expect("type parses")),
            collection_kind: None,
        }
    }

    // ═══════════════════════════════════════════════════════════════════════
    // The rhocalc `@`-cohort pins (F0 gate, plan §5).
    // ═══════════════════════════════════════════════════════════════════════

    /// Proc@ = 3 groups with 6/3/6 leaves: Nil {10,11,15,16,20,21} (incl. the
    /// two NULLARY members 15/16), Quoted {12,17,22}, Short {13,14,18,19,
    /// 23,24}. Rule indices are pinned against the generated WPDA_RULES
    /// table (labels asserted first, so drift fails loudly and precisely).
    #[test]
    fn rhocalc_proc_at_cohort_pins_three_groups_6_3_6() {
        let def = rhocalc();
        let (categories, per_cat) = cats_per_cat(&def);
        assert_eq!(categories[0], "Proc", "Proc is the primary category");
        let name_src = src_idx(&categories, "Name");
        assert_eq!(name_src, 3, "Name src_idx pinned by WPDA_CATEGORIES");
        // WPDA_RULES parity for the 15-rule cohort.
        let pinned_labels = [
            (10u16, "POutputNil"),
            (11, "PPersistOutputNil"),
            (12, "POutputQuoted"),
            (13, "POutputShort"),
            (14, "PPersistOutputShort"),
            (15, "POutputNilEmpty"),
            (16, "PPersistOutputNilEmpty"),
            (17, "POutputQuotedEmpty"),
            (18, "POutputShortEmpty"),
            (19, "PPersistOutputShortEmpty"),
            (20, "POutputNil2Plus"),
            (21, "PPersistOutputNil2Plus"),
            (22, "POutputQuoted2Plus"),
            (23, "POutputShort2Plus"),
            (24, "PPersistOutputShort2Plus"),
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

        assert_eq!(nil.member_rule_idxs(), BTreeSet::from([10, 11, 15, 16, 20, 21]));
        assert_eq!(quoted.member_rule_idxs(), BTreeSet::from([12, 17, 22]));
        assert_eq!(short.member_rule_idxs(), BTreeSet::from([13, 14, 18, 19, 23, 24]));

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
    fn rhocalc_at_cohort_divergence_structure_pins() {
        let def = rhocalc();
        let (categories, per_cat) = cats_per_cat(&def);
        let model = build_prefix_factoring(&def, &categories, &per_cat);
        let proc_at = bucket(&model, 0, "@");
        let name_src = src_idx(&categories, "Name");

        assert_eq!(
            render_forest(&proc_at.groups[0].roots),
            "L(Nil)[L(!)[L(()[P(0,0)[L())=>r10 L(,)=>r20] L())=>r15]] \
             L(!!)[L(()[P(0,0)[L())=>r11 L(,)=>r21] L())=>r16]]]",
            "Nil group divergence structure",
        );
        assert_eq!(
            render_forest(&proc_at.groups[1].roots),
            format!(
                "P({name_src},0)[L(!)[L(()[P(0,0)[L())=>r12 L(,)=>r22] L())=>r17]]]"
            ),
            "Quoted group divergence structure",
        );
        assert_eq!(
            render_forest(&proc_at.groups[2].roots),
            "P(0,0)[L(!)[L(()[P(0,0)[L())=>r13 L(,)=>r23] L())=>r18]] \
             L(!!)[L(()[P(0,0)[L())=>r14 L(,)=>r24] L())=>r19]]]",
            "Short group divergence structure",
        );
    }

    /// Commit-coordinate pins (amendment A4): rule 15 (nullary — full
    /// `@ Nil ! (` spine shared, commit into the literal tail at sub_pos 4 =
    /// parts_len, the tail-complete pop-and-fire arm) and rule 20 (2Plus —
    /// commit at the `,` leaf into BinderRule pos 6, collection remainder in
    /// its own machinery); rule 10 as the no-remainder control.
    #[test]
    fn rhocalc_commit_coordinates_rule15_nullary_and_rule20_2plus() {
        let def = rhocalc();
        let (categories, per_cat) = cats_per_cat(&def);
        let model = build_prefix_factoring(&def, &categories, &per_cat);
        let nil = &bucket(&model, 0, "@").groups[0];

        let (edge15, m15) = nil.leaf_for(15).expect("rule 15 leaf");
        assert_eq!(m15.kind, MemberKind::Nullary);
        assert!(
            matches!(edge15, SpineItem::Literal { text, required_top_cat: None } if text == ")"),
            "rule 15 commits on the `)` leaf edge: {edge15:?}",
        );
        assert_eq!(m15.leaf_depth, 4, "spine consumed Nil ! ( ) for rule 15");
        assert_eq!(
            m15.commit,
            MemberCommit::Nullary { rule_idx: 15, completed_idx: 0, sub_pos: 4 },
            "nullary commit lands at sub_pos == parts_len (tail complete)",
        );
        assert_eq!(
            m15.pos_map,
            SpinePosMap::Nullary { sub_pos_at_depth: vec![0, 1, 2, 3, 4] },
        );
        assert!(!m15.has_post_spine_remainder);

        let (edge20, m20) = nil.leaf_for(20).expect("rule 20 leaf");
        assert_eq!(m20.kind, MemberKind::Binder);
        assert!(
            matches!(edge20, SpineItem::Literal { text, .. } if text == ","),
            "rule 20 commits on the `,` leaf edge: {edge20:?}",
        );
        assert_eq!(m20.leaf_depth, 5, "spine consumed Nil ! ( <a> , for rule 20");
        assert_eq!(
            m20.commit,
            MemberCommit::Binder { rule_idx: 20, resume_pos: 6 },
            "2Plus commit resumes BinderRule at pos 6 (the collection slot)",
        );
        assert_eq!(
            m20.pos_map,
            SpinePosMap::Binder { pos_at_depth: vec![1, 2, 3, 4, 5, 6] },
        );
        assert!(
            m20.has_post_spine_remainder,
            "the 2Plus collection tail runs in the member's own machinery",
        );

        let (edge10, m10) = nil.leaf_for(10).expect("rule 10 leaf");
        assert!(matches!(edge10, SpineItem::Literal { text, .. } if text == ")"));
        assert_eq!(
            m10.commit,
            MemberCommit::Binder { rule_idx: 10, resume_pos: 6 },
            "rule 10 commit position IS its final-pos Pop → fire arm",
        );
        assert!(!m10.has_post_spine_remainder);
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
    /// `rhocalc_inputbind_at_cohort_factors_with_accept_continue`; the
    /// const coupling by `inputbind_at_stance_follows_the_s1f5_const`.
    #[test]
    fn rhocalc_name_and_inputbind_at_cohorts_excluded_or_singleton() {
        let def = rhocalc();
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
        let singleton_idxs: BTreeSet<u16> =
            name_at.singletons.iter().map(|s| s.rule_idx).collect();
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
    /// values): rhocalc `(InputBind, "@")` = {InputBindQuotedQuery=2,
    /// InputBindQuoted=3 (the accept), InputBindQuotedPersistent=6} —
    /// index re-pin per plan §1/P1. Pins the sibling-leaf trie (the accept
    /// leaf SHARES its `P(Name)` edge item with the continuation subtree),
    /// the ★A1 normative child order (interior-continue FIRST, accept
    /// LAST), the A4 commit coordinates (the accept's resume_pos =
    /// positions.len()+1 = its final-pos Pop → fire arm), and the A2
    /// per-category spine-ordinal isolation (InputBind's first group takes
    /// 0xF800 in its OWN category; Proc@ ids unshifted).
    #[test]
    fn rhocalc_inputbind_at_cohort_factors_with_accept_continue() {
        let def = rhocalc();
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
        assert!(
            !m3.has_post_spine_remainder,
            "a true accept has NO member-side remainder",
        );

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
        let def = rhocalc();
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
            assert_eq!(ib_const.groups[0].member_rule_idxs(), BTreeSet::from([2, 3, 6]));
        } else {
            assert!(ib_const.groups.is_empty(), "const OFF ⇒ InputBind@ deferred");
            assert_eq!(ib_const.ineligible.len(), 1);
            assert!(matches!(
                ib_const.ineligible[0].reason,
                IneligibleReason::InteriorAccept { .. },
            ));
        }
    }

    /// ★A2 receipts — RhoCalc: the binary object casts (`int(a,w) : Proc`
    /// family) are numeric-cast-adapter rows and excluded; the `@`-cohort
    /// sends (incl. the arity-1 `POutputNil`/`POutputQuotedEmpty`) are NOT
    /// cast rows and stay grouped (pinned above).
    #[test]
    fn rhocalc_cast_rules_excluded_from_factoring_a2() {
        let def = rhocalc();
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
                b.groups.iter().all(|g| !g.member_rule_idxs().contains(&idx)),
                "{label} must not ride a spine",
            );
        }

        // Receipts to stderr for the campaign log.
        eprintln!("A2 cast-machinery exclusion receipts (rhocalc):");
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
            int_bucket.groups.iter().map(|g| g.member_rule_idxs()).collect::<Vec<_>>(),
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
            float_bucket.groups.iter().map(|g| g.member_rule_idxs()).collect::<Vec<_>>(),
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

    /// RhoCalc `PNew` (`new ( xs... ) in { p }`): its mergeable prefix is
    /// the lone `(` literal — the binder-list at position 2 terminates
    /// mergeability — and no sibling shares the `new` trigger, so it stays
    /// an unfactored LoneRootChild singleton (today's emission).
    #[test]
    fn rhocalc_pnew_stays_a_singleton() {
        let def = rhocalc();
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
        assert_eq!(s.reason, SingletonReason::LoneRootChild);
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
        let def = rhocalc();
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
        // The rhocalc @-cohort ships factored: 3 groups, 6/3/6 leaves
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
    // Synthetic eligibility witnesses (non-rhocalc alphabet).
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
            MemberCommit::Nullary { rule_idx: 0, completed_idx: 0, sub_pos: 2 },
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
        assert!(matches!(edge0, SpineItem::Literal { text, required_top_cat: None } if text == "«"));
        assert_eq!(short.kind, MemberKind::Nullary);
        assert_eq!(
            short.commit,
            MemberCommit::Nullary { rule_idx: 0, completed_idx: 0, sub_pos: 1 },
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
                    vec![
                        lit("quo"),
                        lit("«"),
                        param("t"),
                        lit("·"),
                        sep("xs", ","),
                        lit("»"),
                    ],
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
        assert_eq!(
            render_forest(&g.roots),
            format!("L(«)[P({tee_src},0)[L(·)=>r0 L(»)=>r1]]"),
        );
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
            vec![
                lang_type("Expr", None),
                lang_type("Tee", None),
                lang_type("Zed", None),
            ],
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
    fn normalized(ts: &proc_macro2::TokenStream) -> String {
        ts.to_string().chars().filter(|c| !c.is_whitespace()).collect()
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
        let def = rhocalc();
        let (categories, per_cat) = cats_per_cat(&def);
        let gated = build_spine_emission(&def, &categories, &per_cat);
        assert!(gated.any_groups(), "const ON ⇒ the factored emission is LIVE");
        assert!(!gated.binder_arms.is_empty());
        assert!(!gated.trigger_spine_owner_fn.is_empty());
        assert!(!gated.spine_members_fn.is_empty());
        assert!(!gated.action_for_prelude.is_empty());
        assert!(!gated.leading_trigger_prelude.is_empty());
        // A3-corrected (F4 round-1 RED-1; f5_accept_continue_plan §RED-TEAM
        // item 3, 2026-07-12): min_terminal_span rows are emitted ONLY when
        // the group min is > 0 (the `if v > 0` row-omission in
        // `build_spine_emission_from`; 0 = the table default = absent), and
        // `member_min_span` returns 0 for EVERY member of EVERY current
        // rhocalc group — each `@`-cohort member's pattern is Op-bearing
        // (`SyntaxExpr::Op` short-circuits to 0 before literal counting) —
        // so min = 0 per group ⇒ every span row OMITTED ⇒ the CORRECT
        // ON-stance `min_span_prelude` is EMPTY (the engine falls through to
        // the per-rule `min_terminal_span` table default). Re-derived
        // per-group below once `model` is built (self-adjudicating). The
        // pre-A3 `!is_empty()` expectation was the F4 round-1 GATE-RED.
        assert!(
            gated.min_span_prelude.is_empty(),
            "min=0 groups must OMIT their span rows (A3); got: {}",
            gated.min_span_prelude,
        );
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
        let mut groups_seen = 0usize;
        for cat_fact in &model {
            let rules = &per_cat[cat_fact.category_src_idx as usize];
            for bucket in &cat_fact.buckets {
                for group in &bucket.groups {
                    groups_seen += 1;
                    let min = group
                        .member_rule_idxs()
                        .iter()
                        .map(|&m| member_min_span(&rules[m as usize]))
                        .min()
                        .expect("an eligible group has members");
                    assert_eq!(
                        min,
                        0,
                        "group (cat {}, spine {:#06x}) has min_terminal_span > 0 — \
                         it emits a span row; re-derive the min_span_prelude \
                         expectation (A3)",
                        cat_fact.category_src_idx,
                        group.spine_id,
                    );
                }
            }
        }
        // A3/F5-1 stance-follow: the const-gated model gains the InputBind@
        // accept+continue group when `S1F5_ACCEPT_CONTINUE` is on (3 Proc@
        // groups + 1 InputBind@), and stays at the Proc@ trio when off —
        // green at BOTH stances; the min re-derivation loop above already
        // covered the new group (r2's Op-bearing pattern ⇒ min 0 ⇒ its span
        // row is ABSENT and the prelude stays empty).
        let expected_groups =
            if crate::gen::runtime::wpda_codegen::forks::S1F5_ACCEPT_CONTINUE { 4 } else { 3 };
        assert_eq!(
            groups_seen, expected_groups,
            "rhocalc group census follows the S1F5_ACCEPT_CONTINUE stance",
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
                    assert_eq!(
                        min,
                        0,
                        "mixfix group (result {}, spine {:#06x}) has \
                         min_terminal_span > 0 — it emits a span row; re-derive \
                         the min_span_prelude expectation (A3)",
                        group.result_src_idx,
                        group.spine_id,
                    );
                }
            }
        }
        let expected_mixfix_groups =
            if crate::gen::runtime::wpda_codegen::forks::S1F5_MIXFIX_COHORTS { 2 } else { 0 };
        assert_eq!(
            mixfix_groups_seen, expected_mixfix_groups,
            "rhocalc mixfix cohort census follows the S1F5_MIXFIX_COHORTS stance",
        );
        assert_eq!(
            gated.mixfix_groups.len(),
            expected_mixfix_groups,
            "the const-gated bundle's mixfix groups follow the stance",
        );
        let explicit = build_spine_emission_from_parts(
            &model,
            &mixfix_model,
            &def,
            &categories,
            &per_cat,
        );
        assert_eq!(gated.dispositions, explicit.dispositions);
        assert_eq!(gated.binder_arms.to_string(), explicit.binder_arms.to_string());
        assert_eq!(
            gated.trigger_spine_owner_fn.to_string(),
            explicit.trigger_spine_owner_fn.to_string(),
        );
        assert_eq!(gated.spine_members_fn.to_string(), explicit.spine_members_fn.to_string());
        assert_eq!(
            gated.action_for_prelude.to_string(),
            explicit.action_for_prelude.to_string(),
        );
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
        assert_eq!(
            gated.mixfix_prelude_arms.to_string(),
            explicit.mixfix_prelude_arms.to_string(),
        );
        let grouped_alts: usize = gated.lex_alt.iter().map(|alt| alt.grouped.len()).sum();
        assert!(grouped_alts > 0, "const ON ⇒ lex-alt group entries present");
    }

    /// ON-shape pins over the rhocalc `@`-cohort: dispositions (GroupFirst at
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
        for (name, def) in [("rhocalc", rhocalc()), ("calculator", calculator())] {
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
        let def = rhocalc();
        let (categories, per_cat) = cats_per_cat(&def);
        let bundle = build_spine_emission(&def, &categories, &per_cat);
        let proc_dispositions = &bundle.dispositions[0];
        let proc_members = &bundle.group_members[0];
        assert!(
            !proc_members.is_empty(),
            "rhocalc Proc carries S1 spine groups under the committed ON stance",
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
            assert!(
                group_ordinal.is_some(),
                "GroupFirst member {first_member} derives a row",
            );
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
    fn spine_emission_on_rhocalc_pins_dispositions_root_edge_and_tables() {
        let def = rhocalc();
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
        assert_eq!(
            proc_group_members.len(),
            n_first,
            "one members entry per GroupFirst",
        );
        let member_total: usize = proc_group_members.values().map(Vec::len).sum();
        assert_eq!(
            member_total,
            bundle.dispositions[0].len(),
            "every dispositioned member appears in exactly one group list",
        );

        // ── dispositions: Nil group 0xF800 keyed at min member 10 ─────────
        let proc_dispositions = &bundle.dispositions[0];
        assert_eq!(
            proc_dispositions.get(&10),
            Some(&SpineDisposition::GroupFirst {
                spine_id: SPINE_RULE_BASE,
                body_src_idx: 0,
                weight_rule_idx: 10, // AV5: MIN member, never SPINE_ID
            }),
        );
        for rest in [11u16, 15, 16, 20, 21] {
            assert_eq!(
                proc_dispositions.get(&rest),
                Some(&SpineDisposition::GroupRest),
                "Nil-group member {rest} is GroupRest",
            );
        }
        assert_eq!(
            proc_dispositions.get(&12),
            Some(&SpineDisposition::GroupFirst {
                spine_id: SPINE_RULE_BASE + 1,
                body_src_idx: 3,
                weight_rule_idx: 12,
            }),
            "Quoted group leads at rule 12 with the Name body",
        );
        assert_eq!(
            proc_dispositions.get(&13),
            Some(&SpineDisposition::GroupFirst {
                spine_id: SPINE_RULE_BASE + 2,
                body_src_idx: 0,
                weight_rule_idx: 13,
            }),
        );
        // The lex-alt surface mirrors the dispositions (A3).
        assert_eq!(bundle.lex_alt[0].grouped.len(), 15, "all 15 @-cohort members");

        // ── the ROOT-EDGE arm (the F1 root-edge fix pin) ───────────────────
        let arms = normalized(&bundle.binder_arms);
        // Pre-root arm (node 1) consumes the Nil-group's root item `Nil` —
        // and does NOT dispatch the divergence guards `!`/`!!` (those live
        // on the root node's own arm, id 2, which directly follows).
        let arm1 = window(&arms, "(0u16,63488u16,1u8)=>", "(0u16,63488u16,2u8)=>");
        assert!(
            arm1.contains("expected_text:\"Nil\""),
            "pre-root arm consumes the root edge item: {arm1}",
        );
        assert!(
            !arm1.contains("expected_text:\"!\""),
            "divergence guards must NOT be on the pre-root arm: {arm1}",
        );
        let arm2 = window(&arms, "(0u16,63488u16,2u8)=>", "(0u16,63488u16,3u8)=>");
        assert!(
            arm2.contains("expected_text:\"!\"") && arm2.contains("expected_text:\"!!\""),
            "root-node arm forks the !/!! divergence: {arm2}",
        );
        // Quoted group's pre-root arm is the ParamParse chain form: replace
        // the spine marker to node 2 and push CategoryEntry(Name).
        let quoted_arm1 = window(&arms, "(0u16,63489u16,1u8)=>", "(0u16,63489u16,2u8)=>");
        assert!(
            quoted_arm1.contains("ReplaceAndPush")
                && quoted_arm1.contains("category_entry(3u16)")
                && quoted_arm1.contains("rule_at(0u16,63489u16,2u8"),
            "Quoted pre-root arm pushes the Name operand: {quoted_arm1}",
        );
        // Typed commits (A4): rule 10 binder-resumes at its final pos 6;
        // rule 15 nullary-commits into its MixfixLiteralRun tail complete.
        assert!(
            arms.contains("rule_at(0u16,10u16,6u8"),
            "rule 10 commit coordinate present",
        );
        assert!(
            arms.contains("mixfix_marker(0u16,15u16,0u8)") && arms.contains("sub_pos:4u8"),
            "rule 15 nullary commit coordinate present",
        );

        // ── engine-table rows ──────────────────────────────────────────────
        let owners = normalized(&bundle.trigger_spine_owner_fn);
        assert!(owners.contains("(0u16,10u16)=>Some(63488u16)"));
        assert!(owners.contains("(0u16,15u16)=>Some(63488u16)"));
        assert!(owners.contains("(0u16,12u16)=>Some(63489u16)"));
        assert!(owners.contains("(0u16,24u16)=>Some(63490u16)"));
        let members = normalized(&bundle.spine_members_fn);
        assert!(members.contains("(0u16,63488u16)=>&[10u16,11u16,15u16,16u16,20u16,21u16]"));
        assert!(members.contains("(0u16,63489u16)=>&[12u16,17u16,22u16]"));
        assert!(members.contains("(0u16,63490u16)=>&[13u16,14u16,18u16,19u16,23u16,24u16]"));
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
    /// branch byte-for-byte except the three factored fields: SPINE_ID
    /// coordinates, the group body, and the AV5 min-member weight stamp.
    #[test]
    fn spine_trigger_branch_shape_pin() {
        let ts = emit_spine_trigger_branch(0, SPINE_RULE_BASE, 0, 10);
        let s = normalized(&ts);
        assert!(s.contains("__pd_branches.push"));
        // NOTE the trailing comma inside the call — token-exact mirror of the
        // per-rule BinderPrefix branch's own rendering.
        assert!(s.contains("rule_at(0u16,63488u16,1u8,Some(_outer_bp),)"), "{s}");
        assert!(s.contains("lex_w(0.0,0u16,10u16)"), "AV5 weight stamp: {s}");
        assert!(s.contains("ConsumeAsTriggerOnly"));
        assert!(s.contains("rule_idx:63488u16"), "BinderRule state carries the SPINE_ID: {s}");
    }

    // ═══════════════════════════════════════════════════════════════════════
    // F5-1 emission pins (2026-07-13; plan f5_accept_continue_plan.md §2.2 +
    // amendments A1/A2/A3). Full-strength through
    // `build_spine_emission_from(build_prefix_factoring_with(.., true))` —
    // no const flip needed, green at both stances (the F1 discipline).
    // ═══════════════════════════════════════════════════════════════════════

    /// P3(b) — the rhocalc InputBind@ accept+continue emission, hand-derived
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
        let def = rhocalc();
        let (categories, per_cat) = cats_per_cat(&def);
        let ib = src_idx(&categories, "InputBind");
        let name_src = src_idx(&categories, "Name");
        let model = build_prefix_factoring_with(&def, &categories, &per_cat, true);
        let bundle = build_spine_emission_from(&model, &def, &categories, &per_cat);
        assert!(bundle.any_groups());

        // ── A2 dispositions: GroupFirst at min member 2 with the AV5 weight
        //    identity; per-category ordinal keeps the ib spine at 0xF800. ──
        let ib_dispositions = &bundle.dispositions[ib as usize];
        assert_eq!(
            ib_dispositions.get(&2),
            Some(&SpineDisposition::GroupFirst {
                spine_id: SPINE_RULE_BASE,
                body_src_idx: 0,
                weight_rule_idx: 2,
            }),
        );
        for rest in [3u16, 6] {
            assert_eq!(
                ib_dispositions.get(&rest),
                Some(&SpineDisposition::GroupRest),
                "InputBind@ member {rest} is GroupRest",
            );
        }
        assert_eq!(bundle.lex_alt[ib as usize].grouped.len(), 3);
        // Proc@ dispositions unshifted (A2: per-category ordinals).
        assert_eq!(bundle.dispositions[0].len(), 15, "the Proc@ cohort is untouched");

        let arms = normalized(&bundle.binder_arms);
        let spine = SPINE_RULE_BASE; // 63488
        // Arm 1 (pre-root): the shared `pat` Proc operand — ONE push where
        // OFF ran three (the actual fan win).
        let arm1 = window(
            &arms,
            &format!("({ib}u16,{spine}u16,1u8)=>"),
            &format!("({ib}u16,{spine}u16,2u8)=>"),
        );
        assert!(
            arm1.contains("ReplaceAndPush")
                && arm1.contains("category_entry(0u16)")
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
            arm2.contains("expected_text:\"<-\"")
                && arm2.contains(&format!("rule_at({ib}u16,{spine}u16,3u8")),
            "arm 2 continues the spine on <-: {arm2}",
        );
        assert!(
            arm2.contains("expected_text:\"<=\"")
                && arm2.contains(&format!("rule_at({ib}u16,6u16,3u8")),
            "arm 2 commits r6 on <=: {arm2}",
        );
        // ★Arm 3 — THE ACCEPT+CONTINUE FORK: two same-push branches.
        let arm3 = window(
            &arms,
            &format!("({ib}u16,{spine}u16,3u8)=>"),
            &format!("({ib}u16,{spine}u16,4u8)=>"),
        );
        assert_eq!(
            arm3.matches("ReplaceAndPush").count(),
            2,
            "arm 3 is the two-branch accept fork: {arm3}",
        );
        assert_eq!(
            arm3.matches(&format!("category_entry({name_src}u16)")).count(),
            2,
            "BOTH branches push the shared CategoryEntry(Name): {arm3}",
        );
        let continue_sym = format!("rule_at({ib}u16,{spine}u16,4u8");
        let accept_sym = format!("rule_at({ib}u16,3u16,4u8");
        let continue_at = arm3.find(&continue_sym).expect("spine-continue branch present");
        let accept_at = arm3.find(&accept_sym).expect("accept commit branch present");
        assert!(
            continue_at < accept_at,
            "★A1: interior-continue FIRST, accept commit LAST: {arm3}",
        );
        // Arm 4: the chain `!` guard commits r2 — where the spine-continue
        // lineage dies on plain `for(@y <- z){…}` input (the shared
        // evidence-prune, exactly where OFF's QuotedQuery cursor dies).
        let arm4 = window(&arms, &format!("({ib}u16,{spine}u16,4u8)=>"), "];");
        assert!(
            arm4.contains("expected_text:\"!\"")
                && arm4.contains(&format!("rule_at({ib}u16,2u16,5u8")),
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
            actions.contains(&format!(
                "({ib}u16,{spine}u16)=>{{staticSPINE_ENTRY"
            )),
            "ib spine action row present: {actions}",
        );
        assert!(
            actions.contains("expected_input_cats:&[0u16,3u16,65535u16]"),
            "ib union row (Proc, Name, ANY_CAT): {actions}",
        );
        let leads = normalized(&bundle.leading_trigger_prelude);
        assert!(leads.contains(&format!("({ib}u16,{spine}u16)=>returntrue")));
        // A3: r2's Op-bearing pattern short-circuits member_min_span to 0 ⇒
        // group min 0 ⇒ the (ib, spine) span row is ABSENT — and since every
        // rhocalc group is min-0, the whole prelude is EMPTY.
        assert!(
            bundle.min_span_prelude.is_empty(),
            "A3: min=0 ⇒ the span row is omitted; got {}",
            bundle.min_span_prelude,
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
        let arm2 = window(
            &arms,
            &format!("(0u16,{spine}u16,2u8)=>"),
            &format!("(0u16,{spine}u16,3u8)=>"),
        );
        assert_eq!(arm2.matches("ReplaceAndPush").count(), 2, "{arm2}");
        assert_eq!(arm2.matches(&format!("category_entry({tee}u16)")).count(), 2, "{arm2}");
        let continue_at = arm2
            .find(&format!("rule_at(0u16,{spine}u16,3u8"))
            .expect("spine-continue branch");
        let accept_at = arm2
            .find("rule_at(0u16,0u16,3u8")
            .expect("Short accept commit branch");
        assert!(continue_at < accept_at, "A1 order: {arm2}");
        let arm3 = window(&arms, &format!("(0u16,{spine}u16,3u8)=>"), "];");
        assert!(
            arm3.contains("expected_text:\"»\"") && arm3.contains("rule_at(0u16,1u16,4u8"),
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
        let arm1 = window(
            &arms,
            &format!("(0u16,{spine}u16,1u8)=>"),
            &format!("(0u16,{spine}u16,2u8)=>"),
        );
        assert_eq!(
            arm1.matches("expected_text:\"«\"").count(),
            2,
            "the pre-root arm forks BOTH consumers of the root edge: {arm1}",
        );
        let continue_at = arm1
            .find(&format!("rule_at(0u16,{spine}u16,2u8"))
            .expect("spine-continue branch");
        let accept_at = arm1
            .find("mixfix_marker(0u16,0u16,0u8)")
            .expect("TShort nullary accept commit branch");
        assert!(continue_at < accept_at, "A1 order at the pre-root: {arm1}");
        assert!(
            arm1.contains("sub_pos:1u8"),
            "the accept lands tail-complete (sub_pos == parts_len): {arm1}",
        );
        let arm2 = window(&arms, &format!("(0u16,{spine}u16,2u8)=>"), "];");
        assert!(
            arm2.contains("expected_text:\"»\"") && arm2.contains("mixfix_marker(0u16,1u16,0u8)"),
            "arm 2 commits TLong on the » guard: {arm2}",
        );
    }
    // ═══════════════════════════════════════════════════════════════════════
    // F5-2 — mixfix send-cohort pins (plan f5_mixfix_cohorts_plan.md §1.3/
    // §2.2 + amendments A-M4/A-M5).
    // ═══════════════════════════════════════════════════════════════════════

    /// P1 (GO/STOP): the two real cohort tries against the ACTUAL rhocalc
    /// grammar — leaves {4,6,8}/{5,7,9}, divergences at depths 1 and 2,
    /// rules 8/9 truncated at their rep, NO interior accepts, whole-slice
    /// coverage, uniform result_src = 0, spine ids CONTINUING Proc's prefix
    /// ordinals (3 prefix groups ⇒ `!` = 0xF803, `!!` = 0xF804), the D-1
    /// floors (min l_bp 2/4), the AV5 identities (min member 4/5), the
    /// A-M4 Fix-B evidence (both cohorts share "("), and the typed
    /// MixfixRun commit coordinates.
    #[test]
    fn rhocalc_mixfix_send_cohorts_pin_two_groups() {
        let def = rhocalc();
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
            vec![(2u8, 0u16, 4u16), (6u8, 0u16, 6u16), (10u8, 0u16, 8u16)],
            "the ! slice mirrors mixfix_bp_name",
        );
        assert_eq!(bang.groups.len(), 1);
        assert!(bang.ineligible.is_empty() && bang.singletons.is_empty());
        let g = &bang.groups[0];
        assert_eq!(g.spine_id, SPINE_RULE_BASE + 3, "continues Proc's prefix ordinals");
        assert_eq!(g.result_src_idx, 0);
        assert_eq!(g.min_l_bp, 2);
        assert_eq!(g.min_member_rule_idx, 4);
        assert_eq!(g.member_l_bps, vec![(2u8, 4u16), (6u8, 6u16), (10u8, 8u16)]);
        assert_eq!(g.fixb_literal.as_deref(), Some("("), "A-M4 shared Fix-B evidence");
        assert_eq!(
            g.expected_cats_union,
            vec![name_src, 0u16, u16::MAX],
            "H9 union: Name LHS + Proc operand + the rep's ANY_CAT",
        );
        assert_eq!(
            render(&g.roots[0]),
            "L(()[P(0,0)[L())=>r4 L(,)=>r8] L())=>r6]",
            "the §1.3 trie: divergence 1 = operand-vs-close, divergence 2 = close-vs-sep",
        );
        let (_, m4) = g.roots[0].leaf_for(4).expect("rule 4 leafs");
        assert_eq!(
            m4.commit,
            MemberCommit::MixfixRun { rule_idx: 4, kind: 0, completed_idx: 0, sub_pos: 1 },
        );
        assert!(!m4.has_post_spine_remainder, "rule 4's ) is its final item");
        let (_, m6) = g.roots[0].leaf_for(6).expect("rule 6 leafs");
        assert_eq!(
            m6.commit,
            MemberCommit::MixfixRun { rule_idx: 6, kind: 2, completed_idx: 0, sub_pos: 2 },
        );
        assert!(!m6.has_post_spine_remainder);
        let (_, m8) = g.roots[0].leaf_for(8).expect("rule 8 leafs");
        assert_eq!(
            m8.commit,
            MemberCommit::MixfixRun { rule_idx: 8, kind: 0, completed_idx: 0, sub_pos: 1 },
        );
        assert!(m8.has_post_spine_remainder, "rule 8 truncates at its rep");
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
        assert_eq!(
            bangbang.slice,
            vec![(4u8, 0u16, 5u16), (8u8, 0u16, 7u16), (12u8, 0u16, 9u16)],
        );
        assert_eq!(bangbang.groups.len(), 1);
        let g2 = &bangbang.groups[0];
        assert_eq!(g2.spine_id, SPINE_RULE_BASE + 4);
        assert_eq!(g2.min_l_bp, 4);
        assert_eq!(g2.min_member_rule_idx, 5);
        assert_eq!(
            render(&g2.roots[0]),
            "L(()[P(0,0)[L())=>r5 L(,)=>r9] L())=>r7]",
            "the !! trie is isomorphic",
        );
    }

    /// A-M5 census errata pins: every OTHER bundled mixfix cohort stays
    /// unfactored with the recorded reason — Name `,` (rep-part-0 ⇒
    /// EmptySequence ×2), Name `<-` (1-member slice ⇒ LoneRootChild), the
    /// Proc `.` cohort (40 distinct method names ⇒ 40 LoneRootChild), and
    /// InputBind `&`/`where` (rep-part-0 ×2 / singleton).
    #[test]
    fn rhocalc_mixfix_other_cohorts_stay_unfactored() {
        let def = rhocalc();
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
        assert_eq!(dot.slice.len(), 40, "the 40-method cohort");
        assert_eq!(dot.singletons.len(), 40);
        assert!(dot
            .singletons
            .iter()
            .all(|s| s.reason == SingletonReason::LoneRootChild));
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
        assert_eq!(total_groups, 2, "exactly two factorable mixfix cohorts in rhocalc");
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
        let def = rhocalc();
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
            assert_eq!(
                rows,
                vec![(0u16, SPINE_RULE_BASE + 3), (0u16, SPINE_RULE_BASE + 4)],
            );
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
        let def = rhocalc();
        let (categories, per_cat) = cats_per_cat(&def);
        let prefix = build_prefix_factoring(&def, &categories, &per_cat);
        let model = build_mixfix_factoring(&def, &categories, &per_cat, &prefix);
        let identity = mixfix_identity_partition(&def, &categories, &per_cat);
        let census = |m: &[MixfixFactoring]| -> Vec<(u16, String, Vec<(u8, u16, u16)>)> {
            m.iter()
                .flat_map(|f| {
                    f.buckets.iter().map(move |b| {
                        (f.dispatch_cat_src_idx, b.trigger.clone(), b.slice.clone())
                    })
                })
                .collect()
        };
        assert_eq!(census(&model), census(&identity));
    }

    /// ON-shape emission pins over the explicit-stance core (no const
    /// flips): the loop-v2 fan arm (D-1 guard on the A-M4 MEMBER id, the
    /// AV5 min-member weight, the spine push + flag), the three prelude
    /// arms per plan §2.2 (chain step via `__checked_literal_consume!`,
    /// divergence 1 = descent-Advance + rule-6 commit CAR with the
    /// B-alone/zero short-circuit, divergence 2 = rule-4/rule-8 commit CARs
    /// with the singleton short-circuits + the Error miss shape), and the
    /// engine-table rows (owner/members/H9 union/weight; A7 rows ABSENT).
    #[test]
    fn mixfix_emission_pins_fan_arm_prelude_and_tables() {
        let def = rhocalc();
        let (categories, per_cat) = cats_per_cat(&def);
        let prefix = build_prefix_factoring(&def, &categories, &per_cat);
        let mixfix = build_mixfix_factoring(&def, &categories, &per_cat, &prefix);
        let bundle =
            build_spine_emission_from_parts(&prefix, &mixfix, &def, &categories, &per_cat);
        assert_eq!(bundle.mixfix_groups.len(), 2);
        assert_eq!(
            bundle.mixfix_groups[0],
            MixfixGroupEmission {
                dispatch_cat_src_idx: 3,
                trigger: "!".to_string(),
                result_src_idx: 0,
                spine_id: SPINE_RULE_BASE + 3,
                min_l_bp: 2,
                min_member_rule_idx: 4,
                member_rule_idxs: vec![4, 6, 8],
            },
        );
        // ── the fan arm ────────────────────────────────────────────────────
        let fan = normalized(&bundle.mixfix_fan_arms);
        let bang_arm = window(&fan, "(3u16,\"!\")", "(3u16,\"!!\")");
        assert!(
            bang_arm.contains("if2u8>=*cur_bp")
                && bang_arm.contains("__goal_admits(0u16)")
                && bang_arm.contains("__method_name_admits(0u16,4u16)"),
            "D-1 full-admission guard on the MEMBER id (A-M4): {bang_arm}",
        );
        assert!(
            bang_arm.contains("mixfix_marker(0u16,63491u16,0,)")
                && bang_arm.contains("BP_TIER_MIXFIX,0u16,4u16")
                && bang_arm.contains("rule_idx:63491u16")
                && bang_arm.contains("__mixfix_spine_pushed=true"),
            "spine push at the AV5 min-member weight: {bang_arm}",
        );
        assert!(fan.contains("(3u16,\"!!\")") && fan.contains("mixfix_marker(0u16,63492u16,0,)"));
        // ── the prelude arms (the ! group; !! isomorphic) ─────────────────
        let prelude = normalized(&bundle.mixfix_prelude_arms);
        let chain = window(
            &prelude,
            "(0u16,63491u16,2u8,0u8,0u8)=>",
            "(0u16,63491u16,2u8,0u8,1u8)=>",
        );
        assert!(
            chain.contains("__checked_literal_consume!(\"(\"") && chain.contains("sub_pos:1u8"),
            "pre-root chain step consumes the root edge: {chain}",
        );
        let div1 = window(
            &prelude,
            "(0u16,63491u16,2u8,0u8,1u8)=>",
            "(0u16,63491u16,0u8,0u8,0u8)=>",
        );
        assert!(
            div1.contains("__mixfix_literal_targets(tokens,_pos,\")\")"),
            "divergence 1 gates the rule-6 commit on the close: {div1}",
        );
        assert!(
            div1.contains("if__spine_lit_total==0{returnWpdaStepAction::Advance(WpdaState::PrefixDispatch"),
            "divergence 1 B-alone short-circuit (descent when no close): {div1}",
        );
        assert!(
            div1.contains("ForkActionKind::Advance")
                && div1.contains("mixfix_marker(0u16,6u16,0u8)")
                && div1.contains("kind:2u8,sub_pos:2u8"),
            "divergence 1 fork = descent-first + rule-6 commit CAR: {div1}",
        );
        assert!(
            !div1.contains("__spine_lit_total==1"),
            "divergence 1 has an unconditional branch — no literal-singleton \
             short-circuit: {div1}",
        );
        let div2 = window(&prelude, "(0u16,63491u16,0u8,0u8,0u8)=>", "(0u16,63492u16,2u8,0u8,0u8)=>");
        assert!(
            div2.contains("__mixfix_literal_targets(tokens,_pos,\")\")")
                && div2.contains("__mixfix_literal_targets(tokens,_pos,\",\")"),
            "divergence 2 gates both commits: {div2}",
        );
        assert!(
            div2.contains("if__spine_lit_total==1")
                && div2.contains("mixfix_marker(0u16,4u16,0u8)")
                && div2.contains("mixfix_marker(0u16,8u16,0u8)")
                && div2.contains("kind:0u8,sub_pos:1u8"),
            "divergence 2 = the two commit CARs with singleton short-circuits: {div2}",
        );
        assert!(
            div2.contains("WpdaStepAction::Error"),
            "divergence 2 zero-live miss shape: {div2}",
        );
        // ── engine-table rows ─────────────────────────────────────────────
        let owners = normalized(&bundle.trigger_spine_owner_fn);
        for (m, spine) in [(4, "63491"), (6, "63491"), (8, "63491"), (5, "63492"), (7, "63492"), (9, "63492")] {
            assert!(
                owners.contains(&format!("(0u16,{m}u16)=>Some({spine}u16)")),
                "owner row for member {m}: {owners}",
            );
        }
        let members = normalized(&bundle.spine_members_fn);
        assert!(members.contains("(0u16,63491u16)=>&[4u16,6u16,8u16]"));
        assert!(members.contains("(0u16,63492u16)=>&[5u16,7u16,9u16]"));
        let actions = normalized(&bundle.action_for_prelude);
        assert!(
            actions.contains("(0u16,63491u16)=>")
                && actions.contains("expected_input_cats:&[3u16,0u16,65535u16]"),
            "H9 poison union row (Name LHS + Proc + rep ANY_CAT): {actions}",
        );
        let weights = normalized(&bundle.spine_weight_rule_fn);
        assert!(weights.contains("(0u16,63491u16)=>4u16"));
        assert!(weights.contains("(0u16,63492u16)=>5u16"));
        // A7-mixfix (A-M5): rows OMITTED — the members are operand-leading.
        let leads = normalized(&bundle.leading_trigger_prelude);
        assert!(
            !leads.contains("63491") && !leads.contains("63492"),
            "mixfix spine ids must NOT appear on the leading-trigger surface: {leads}",
        );
        // min_span stays EMPTY for rhocalc (rules 8/9 are Op-bearing ⇒ min 0).
        assert!(bundle.min_span_prelude.is_empty());
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
            MemberCommit::MixfixRun { rule_idx: 1, kind: 0, completed_idx: 0, sub_pos: 0 },
        );
        assert!(m1.has_post_spine_remainder);
        let bundle =
            build_spine_emission_from_parts(&prefix, &mixfix, &def, &categories, &per_cat);
        let prelude = normalized(&bundle.mixfix_prelude_arms);
        assert!(
            prelude.contains("ForkActionKind::ReplaceAndPush")
                && prelude.contains("replace_symbol:StackSymbolV2::mixfix_marker(0u16,1u16,0u8)"),
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
                vec![
                    simple("a", "Expr"),
                    simple("b", "Expr"),
                    simple("c", "Expr"),
                ],
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
                vec![
                    simple("a", "Expr"),
                    simple("b", "Expr"),
                    simple("c", "Expr"),
                ],
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
        assert!(matches!(
            bucket.ineligible[0].reason,
            IneligibleReason::MultiOperandSharedSpine,
        ));
    }

}
