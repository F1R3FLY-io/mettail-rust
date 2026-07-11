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
//!     `InputBindQuoted` inside the `@`-led query row): MODELED (recorded on
//!     the ineligible group) but DEFERRED to F5 — the whole group falls back
//!     to unfactored emission. Consequently every leaf of an ELIGIBLE group
//!     carries exactly one rule (asserted).
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

#![allow(dead_code)] // F0: consumed by tests + INV-8 only; F1 wires emission.

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
}

/// A group member with its leaf assignment.
#[derive(Debug, Clone)]
pub(crate) struct GroupMember {
    pub kind: MemberKind,
    pub rule_idx: u16,
    /// Trie depth of the member's leaf: post-trigger items consumed on the
    /// spine INCLUDING the leaf edge.
    pub leaf_depth: u8,
    /// Typed commit coordinates (amendment A4).
    pub commit: MemberCommit,
    /// Spine-pos → member-pos map (amendment A4).
    pub pos_map: SpinePosMap,
    /// The member continues in its own machinery past the commit (collection
    /// tails, further literals/params) — as opposed to the leaf edge being
    /// its final item (where the commit position IS the final-pos
    /// Pop → fire arm).
    pub has_post_spine_remainder: bool,
}

/// The factored suffix trie of one group. The root carries the group's
/// shared first post-trigger item; interior nodes are shared spine steps;
/// each leaf is exactly one member.
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
    pub tree: SpineTree,
}

impl SpineGroup {
    pub(crate) fn member_rule_idxs(&self) -> BTreeSet<u16> {
        self.tree.leaves().iter().map(|m| m.rule_idx).collect()
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
}

#[derive(Debug, Clone)]
pub(crate) struct SingletonMember {
    pub rule_idx: u16,
    pub kind: MemberKind,
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
}

#[derive(Debug)]
pub(crate) struct IneligibleGroup {
    pub reason: IneligibleReason,
    pub member_rule_idxs: Vec<u16>,
}

/// One `(category, leading_literal)` prefix cohort.
#[derive(Debug)]
pub(crate) struct FactoringBucket {
    pub leading_literal: String,
    /// Total members discovered in this bucket BEFORE any exclusion — the
    /// INV-8 no-loss denominator (amendment A5): `Σ group leaves +
    /// Σ ineligible members + |singletons| == cohort_size`.
    pub cohort_size: usize,
    pub groups: Vec<SpineGroup>,
    pub ineligible: Vec<IneligibleGroup>,
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

/// Recursive trie build. `edge_item` is the item that led INTO this node
/// (`members` all matched `items[0..depth]`; `edge_item == items[depth - 1]`).
/// A single remaining member commits immediately (earliest-uniqueness leaf);
/// members whose sequence exhausts at an interior node are recorded as
/// interior accepts (F5) — the caller marks the group ineligible.
fn build_tree(
    depth: usize,
    edge_item: SpineItem,
    members: Vec<CandidateMember>,
    interior_accepts: &mut Vec<u16>,
) -> SpineTree {
    if members.len() == 1 {
        let member = members
            .into_iter()
            .next()
            .expect("a len()==1 vector yields its member");
        return SpineTree::Leaf {
            item: edge_item,
            member: finalize_leaf(member, depth),
        };
    }
    // ≥2 members: partition by the next item, preserving first-occurrence
    // order (rule declaration order — deterministic).
    let mut order: Vec<SpineItem> = Vec::new();
    let mut parts: Vec<Vec<CandidateMember>> = Vec::new();
    for member in members {
        if member.items.len() == depth {
            // Exhausted at an interior node while siblings continue — a
            // proper-prefix member (interior accept-node). Recorded; the
            // group becomes ineligible (F5). Identical-twin members (equal
            // full sequences) both land here, so a multi-member leaf can
            // never form below.
            interior_accepts.push(member.rule_idx);
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
    let children: Vec<SpineTree> = order
        .into_iter()
        .zip(parts)
        .map(|(item, part)| build_tree(depth + 1, item, part, interior_accepts))
        .collect();
    SpineTree::Interior { item: edge_item, children }
}

// ═══════════════════════════════════════════════════════════════════════════
// The factoring computation.
// ═══════════════════════════════════════════════════════════════════════════

/// Build the full prefix-factoring model for every category: buckets, groups
/// (spine tries, SPINE_IDs, typed commit maps), ineligible groups, and
/// singletons. PURE — consumes the same classifier outputs as the emission
/// and produces no tokens. `per_cat` must be the SAME
/// `synthetic::build_per_category_rules` product the emission uses so
/// `rule_idx` values agree.
pub(crate) fn build_prefix_factoring(
    language: &LanguageDef,
    categories: &[String],
    per_cat: &[Vec<GrammarRule>],
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
                        kind: member.kind,
                        reason: SingletonReason::CastMachinery,
                    });
                } else if member.items.is_empty() {
                    singletons.push(SingletonMember {
                        rule_idx: member.rule_idx,
                        kind: member.kind,
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
                        kind: lone.kind,
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
                let tree = build_tree(1, root_item, part, &mut interior_accepts);
                if !interior_accepts.is_empty() {
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
                    // body_src_idx would be ill-defined.
                    ineligible.push(IneligibleGroup {
                        reason: IneligibleReason::NonUniformBodySrc { body_src_idxs },
                        member_rule_idxs,
                    });
                    continue;
                }
                // Eligible: every leaf carries exactly one rule by
                // construction (single-member recursion base; twins and
                // proper prefixes were routed to interior_accepts above).
                assert_eq!(
                    tree.leaf_count(),
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
                    tree,
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
                kind: member.kind,
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
// Tests — the F0 gate's rhocalc trie pins (real grammar, real indices),
// the A2 exclusion receipts, and the synthetic eligibility witnesses.
// ═══════════════════════════════════════════════════════════════════════════

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
    /// don't just count groups).
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

        assert_eq!(nil.tree.leaf_count(), 6);
        assert_eq!(quoted.tree.leaf_count(), 3);
        assert_eq!(short.tree.leaf_count(), 6);

        assert_eq!(nil.member_rule_idxs(), BTreeSet::from([10, 11, 15, 16, 20, 21]));
        assert_eq!(quoted.member_rule_idxs(), BTreeSet::from([12, 17, 22]));
        assert_eq!(short.member_rule_idxs(), BTreeSet::from([13, 14, 18, 19, 23, 24]));

        // Group roots = the first post-trigger emitted-action shapes.
        assert!(
            matches!(nil.tree.item(), SpineItem::Literal { text, .. } if text == "Nil"),
            "Nil group root: {:?}",
            nil.tree.item(),
        );
        assert_eq!(
            quoted.tree.item(),
            &SpineItem::ParamParse { cat_src_idx: name_src, cur_bp: 0 },
            "Quoted group root pushes CategoryEntry(Name) at cur_bp 0",
        );
        // Red-team AV2 receipt: the spec-level `prefix(220)` on the Short
        // rules does NOT surface — the shared pos-1 action is
        // ReplaceAndPush{CategoryEntry(0), cur_bp: 0}, byte-equal across all
        // six members.
        assert_eq!(
            short.tree.item(),
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
            render(&proc_at.groups[0].tree),
            "L(Nil)[L(!)[L(()[P(0,0)[L())=>r10 L(,)=>r20] L())=>r15]] \
             L(!!)[L(()[P(0,0)[L())=>r11 L(,)=>r21] L())=>r16]]]",
            "Nil group divergence structure",
        );
        assert_eq!(
            render(&proc_at.groups[1].tree),
            format!(
                "P({name_src},0)[L(!)[L(()[P(0,0)[L())=>r12 L(,)=>r22] L())=>r17]]]"
            ),
            "Quoted group divergence structure",
        );
        assert_eq!(
            render(&proc_at.groups[2].tree),
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

        let (edge15, m15) = nil.tree.leaf_for(15).expect("rule 15 leaf");
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

        let (edge20, m20) = nil.tree.leaf_for(20).expect("rule 20 leaf");
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

        let (edge10, m10) = nil.tree.leaf_for(10).expect("rule 10 leaf");
        assert!(matches!(edge10, SpineItem::Literal { text, .. } if text == ")"));
        assert_eq!(
            m10.commit,
            MemberCommit::Binder { rule_idx: 10, resume_pos: 6 },
            "rule 10 commit position IS its final-pos Pop → fire arm",
        );
        assert!(!m10.has_post_spine_remainder);
    }

    /// Name@ and InputBind@ cohorts: correctly excluded-or-singleton. Name@
    /// carries NQuote (`@ ( p )`) and NQuoteNil (`@ Nil`) which diverge at
    /// the root (singletons; NQuoteShort `@ p` is a CrossCatPrefixUnary and
    /// never a member); InputBind@'s three rows share the `pat <-/<= n`
    /// spine but `InputBindQuoted` is a proper PREFIX of the query row —
    /// an interior accept-node — so the whole group is F5-deferred.
    #[test]
    fn rhocalc_name_and_inputbind_at_cohorts_excluded_or_singleton() {
        let def = rhocalc();
        let (categories, per_cat) = cats_per_cat(&def);
        let model = build_prefix_factoring(&def, &categories, &per_cat);
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
    /// `int(<Float>)` / `int(<Str>)`) and the same-cat `IntId` (`int(<Int>)`,
    /// a numeric-domain wrapper row) are all excluded, dissolving the
    /// (Int, "int") bucket into singletons — `int(...)` NEVER rides a spine,
    /// so `try_park_direct_prefix_cast_waiter` keeps seeing real rule ids.
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
        for label in ["FloatToInt", "BoolToInt", "StrToInt", "IntId"] {
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
    /// (`S1_FACTORING == false`) is the identity: zero groups anywhere,
    /// every member a `FactoringDisabled` singleton — the F0 byte-identity
    /// stance expressed as data.
    #[test]
    fn emission_partition_is_identity_while_const_off() {
        assert!(
            !crate::gen::runtime::wpda_codegen::forks::S1_FACTORING,
            "F0 ships with the kill-switch OFF",
        );
        let def = rhocalc();
        let (categories, per_cat) = cats_per_cat(&def);
        let effective = emission_partition(&def, &categories, &per_cat);
        for cat in &effective {
            for b in &cat.buckets {
                assert!(b.groups.is_empty(), "const OFF ⇒ no factored groups");
                assert!(b.ineligible.is_empty(), "const OFF ⇒ no deferred groups");
                assert_eq!(b.singletons.len(), b.cohort_size);
                for s in &b.singletons {
                    assert_eq!(s.reason, SingletonReason::FactoringDisabled);
                }
            }
        }
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
            render(&g.tree),
            format!("L(«)[L(»)=>r0 P({tee_src},0)=>r1]"),
            "one shared literal edge, then nullary-vs-binder divergence",
        );
        let (_, nullary) = g.tree.leaf_for(0).expect("nullary leaf");
        assert_eq!(
            nullary.commit,
            MemberCommit::Nullary { rule_idx: 0, completed_idx: 0, sub_pos: 2 },
        );
        let (_, binder) = g.tree.leaf_for(1).expect("binder leaf");
        assert_eq!(binder.commit, MemberCommit::Binder { rule_idx: 1, resume_pos: 3 });
        assert!(binder.has_post_spine_remainder, "the trailing » stays member-side");
    }

    /// A proper-prefix member (interior accept-node) defers the WHOLE group
    /// (F5), preserving today's emission for all members.
    #[test]
    fn interior_accept_defers_group_to_f5() {
        let lang = mk_language(
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
        );
        let (categories, per_cat) = cats_per_cat(&lang);
        let model = build_prefix_factoring(&lang, &categories, &per_cat);
        let b = bucket(&model, 0, "quo");
        assert!(b.groups.is_empty());
        assert_eq!(b.ineligible.len(), 1);
        assert!(matches!(
            &b.ineligible[0].reason,
            IneligibleReason::InteriorAccept { accepting_rule_idxs } if accepting_rule_idxs == &vec![0],
        ));
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
            render(&g.tree),
            format!("L(«)[P({tee_src},0)[L(·)=>r0 L(»)=>r1]]"),
        );
        let (_, with_coll) = g.tree.leaf_for(0).expect("collection member leaf");
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
}
