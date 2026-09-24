//! Original shared-prefix factoring descriptors and iterative tree builder.
//!
//! Callers pass the original owned descriptors; this module relocates the
//! original `wpda_codegen::factoring` tree machinery
//! without introducing another grouping algorithm. Caller discovery retains
//! responsibility for eligibility, member-prefix invariants and encoding bounds.
//! In particular, the original depth refusal does not short-circuit finalization:
//! callers must not treat it as admission of arbitrary untrusted depths.
//!
//! `FactoringTreeRelocation.v` models the unchanged Enter/Assemble transitions,
//! exact descriptor payloads, ordering and refusal effects. Its scope is module
//! relocation, not unrestricted input safety. Iterative tree walking, formatting
//! and destruction are retained alongside the original builder.

use indexmap::IndexMap;
use std::collections::BTreeSet;

pub mod emission;

#[cfg(test)]
#[path = "factoring_fallible_tests.rs"]
mod fallible_tests;

use super::binder::{
    binder_initial_body_cat, lookup_src_idx, required_top_cat_after_position, BinderPosition,
    BinderShape,
};

/// The four observations member discovery makes of an existing atomic classifier.
///
/// This is a projection of the classifier's result, not another classifier.
/// Retain the original classifier call even for ignored result kinds; its
/// internal callbacks and errors are part of the existing derivation boundary.
pub enum PrefixAtomicObservation {
    /// A cross-category prefix is handled by its own dispatch path.
    CrossCatPrefixUnary,
    /// The original trigger and trailing literals of a nullary run.
    NullaryLiteralRun {
        trigger: String,
        trailing_literals: Vec<String>,
    },
    /// A cross-category projection is handled by its own dispatch path.
    CrossCatProjection,
    /// Continue with the existing binder classifier.
    Other,
}

/// Discover original prefix members in rule order through borrowed rule views.
///
/// Atomic classification runs first. Nullary success bypasses binder and
/// leading-literal callbacks; only a successful binder classification reads
/// the leading literal and applies the original parenthesis exclusion.
/// Category selection and spine items reuse the original shared helpers.
/// `PrefixDiscoveryProjection.v` verifies this callback schedule and complete
/// member outputs. Callers retain admission and classifier responsibilities.
pub fn discover_prefix_members_with<R>(
    categories: &[String],
    category_src_idx: u16,
    rules: &[R],
    prefix_bp_map: &std::collections::HashMap<(u16, u16), u8>,
    mut classify_atomic: impl FnMut(&R) -> PrefixAtomicObservation,
    mut classify_binder: impl FnMut(&R) -> Option<BinderShape>,
    mut leading_literal: impl for<'a> FnMut(&'a R) -> Option<&'a str>,
) -> Vec<(String, CandidateMember)> {
    match try_discover_prefix_members_with(
        categories,
        category_src_idx,
        rules,
        prefix_bp_map,
        |rule| Ok::<_, std::convert::Infallible>(classify_atomic(rule)),
        |rule| Ok(classify_binder(rule)),
        |rule| Ok(leading_literal(rule)),
    ) {
        Ok(value) => value,
        Err(never) => match never {},
    }
}

/// The original discovery loop with first-error propagation at callback sites.
/// Successful absence retains the original fallback; failure publishes no prefix.
pub fn try_discover_prefix_members_with<'rules, R, E>(
    categories: &[String],
    category_src_idx: u16,
    rules: &'rules [R],
    prefix_bp_map: &std::collections::HashMap<(u16, u16), u8>,
    mut classify_atomic: impl FnMut(&R) -> Result<PrefixAtomicObservation, E>,
    mut classify_binder: impl FnMut(&R) -> Result<Option<BinderShape>, E>,
    mut leading_literal: impl FnMut(&'rules R) -> Result<Option<&'rules str>, E>,
) -> Result<Vec<(String, CandidateMember)>, E> {
    let mut out = Vec::new();
    for (rule_i, rule) in rules.iter().enumerate() {
        let rule_idx = rule_i as u16;
        match classify_atomic(rule)? {
            PrefixAtomicObservation::CrossCatPrefixUnary => continue,
            PrefixAtomicObservation::NullaryLiteralRun { trigger, trailing_literals, .. } => {
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
            PrefixAtomicObservation::CrossCatProjection => continue,
            _ => {},
        }
        let Some(shape) = classify_binder(rule)? else {
            continue;
        };
        let Some(trigger) = leading_literal(rule)? else {
            continue;
        };
        if trigger == "(" {
            continue;
        }
        let body_src_idx = binder_initial_body_cat(&shape)
            .and_then(|name| lookup_src_idx(name, categories))
            .unwrap_or(category_src_idx);
        let (items, truncated) =
            binder_items(&shape.positions, category_src_idx, rule_idx, categories, prefix_bp_map);
        out.push((
            trigger.to_owned(),
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
    Ok(out)
}

/// Map a binder member's `BinderShape.positions` to its mergeable
/// [`SpineItem`] prefix. Returns `(items, truncated)`.
pub fn binder_items(
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
                let previous = if idx > 0 {
                    positions.get(idx - 1)
                } else {
                    None
                };
                items.push(SpineItem::Literal {
                    text: text.clone(),
                    required_top_cat: required_top_cat_after_position(previous, categories),
                });
            },
            BinderPosition::ParamParse { cat, collection: None } => {
                // ★ #141 G1 — the FOURTH copy of the #133 `ParamParse` message stood here
                // and it has been DELETED rather than routed, because at THIS site the
                // refusal was worse than useless.
                //
                // Two measurements decide it. (1) Under this workspace's cranelift dev
                // backend a `panic!` inside the proc macro prints NOTHING — the payload
                // never appears and rustc dies with `fatal runtime error: Rust cannot
                // catch foreign exceptions` (task #141 RED-0, 2026-07-29). (2) This
                // module runs FIRST: `engine_impl.rs` calls `build_spine_emission`
                // before `emit_binder_rule_body`, `emit_binder_list_loop_body` and
                // `emit_optional_group_body`. So the panic here silently pre-empted the
                // three sibling ParamParse sites that — as of #141 — refuse READABLY,
                // through `binder::cat_idx_tokens`, naming the category and the rule.
                //
                // The right behaviour is therefore to DECLINE TO MERGE, which is this
                // module's own documented escape for a position the shared spine trie
                // has no node for (the identical `return (items, true)` below covers
                // `TokenKindCapture`, `IdentTextCapture`, `BinderIdent`, `GuardSlot`,
                // `OptionalGroup` and collection `ParamParse`). A category with no index
                // is more reason to decline merging, not less.
                //
                // ⚠ This is NOT the fails-open shape the comment further down this file
                // warns about, and the difference is worth stating precisely: declining
                // routes the member to its OWN un-factored emission, which is
                // `binder::emit_binder_rule_body`, which refuses with a `compile_error!`
                // for this exact position class. The build cannot succeed with a wrong
                // index; it fails with a message that names the category and the rule.
                let Some(cat_src_idx) = lookup_src_idx(cat, categories) else {
                    return (items, true);
                };
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
            // Collection ParamParse / binder-list / guard / optional-group /
            // L9-3 token-kind capture: terminate mergeability (leaf-side only,
            // plan §2). A custom-kind capture consumes a distinct kind, so a
            // rule carrying one does not merge into the shared spine trie.
            // `IdentTextCapture` terminates mergeability for the SAME reason
            // `TokenKindCapture` does — it consumes a token the shared spine trie has no
            // node for. It is listed explicitly rather than folded into a wildcard so a
            // future position variant still fails this match loudly.
            BinderPosition::ParamParse { collection: Some(_), .. }
            | BinderPosition::TokenKindCapture { .. }
            | BinderPosition::IdentTextCapture { .. }
            | BinderPosition::GuestBodyCapture { .. }
            | BinderPosition::BinderIdent
            | BinderPosition::BinderListLoop { .. }
            | BinderPosition::GuardSlot
            | BinderPosition::OptionalGroup { .. } => return (items, true),
        }
    }
    (items, false)
}

/// One post-trigger spine item, keyed by the shape of the action the per-rule
/// emission would produce for it. Equality of two items IS the merge
/// criterion (the red-team vindicated emitted-action-shape equality as the
/// only correct one — spec-level `prefix(N)` annotations do not reliably
/// surface in the emitted `cur_bp`).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum SpineItem {
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
pub enum MemberKind {
    Binder,
    Nullary,
    /// F5-2 (2026-07-13, plan `f5_mixfix_cohorts_plan.md`): a member of an
    /// InfixLoop mixfix send cohort (rholang `!`/`!!`). Commits back into the
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
pub enum MemberCommit {
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
    /// the spine marker with
    /// `mixfix_marker(result, rule_idx, completed_idx, continuation_bp)`
    /// and enters `MixfixLiteralRun { rule_idx, completed_idx, kind,
    /// sub_pos }`. The F0 `Nullary` variant is the `kind: 2, completed: 0`
    /// special case on the PREFIX surface; mixfix-cohort members (including
    /// their nullary members, e.g. rholang POutputEmpty) always use this
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
pub enum SpinePosMap {
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
pub struct GroupMember {
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
pub enum SpineTree {
    Interior {
        item: SpineItem,
        children: Vec<SpineTree>,
    },
    Leaf {
        item: SpineItem,
        member: GroupMember,
    },
}

#[path = "factoring/spine_tree_lifecycle.rs"]
mod spine_tree_lifecycle;

impl SpineTree {
    pub fn item(&self) -> &SpineItem {
        match self {
            SpineTree::Interior { item, .. } | SpineTree::Leaf { item, .. } => item,
        }
    }

    pub fn leaf_count(&self) -> usize {
        let mut count = 0usize;
        let mut work = vec![self];
        while let Some(node) = work.pop() {
            match node {
                SpineTree::Leaf { .. } => count += 1,
                SpineTree::Interior { children, .. } => work.extend(children.iter().rev()),
            }
        }
        count
    }

    pub fn leaves(&self) -> Vec<&GroupMember> {
        let mut out = Vec::new();
        let mut work = vec![self];
        while let Some(node) = work.pop() {
            match node {
                SpineTree::Leaf { member, .. } => out.push(member),
                SpineTree::Interior { children, .. } => work.extend(children.iter().rev()),
            }
        }
        out
    }

    /// The leaf for `rule_idx` together with its leaf EDGE item, if present.
    // dead_code: model accessor, exercised only by the `#[cfg(test)]` INV-8 assertions.
    #[cfg_attr(not(test), allow(dead_code))]
    pub fn leaf_for(&self, rule_idx: u16) -> Option<(&SpineItem, &GroupMember)> {
        let mut work = vec![self];
        while let Some(node) = work.pop() {
            match node {
                SpineTree::Leaf { item, member } if member.rule_idx == rule_idx => {
                    return Some((item, member));
                },
                SpineTree::Leaf { .. } => {},
                SpineTree::Interior { children, .. } => work.extend(children.iter().rev()),
            }
        }
        None
    }
}

/// A bucket member before trie construction.
#[derive(Debug, Clone)]
pub struct CandidateMember {
    pub kind: MemberKind,
    pub rule_idx: u16,
    /// The member's MERGEABLE item prefix (cut at the first collection /
    /// binder-list / optional-group / guard item).
    pub items: Vec<SpineItem>,
    /// `true` iff the item sequence was cut (a non-mergeable item follows).
    pub truncated: bool,
    /// Total member-side positions (binder: `shape.positions.len()`;
    /// nullary: trailing-literal count) — for remainder detection.
    pub total_positions: usize,
    /// Binder members: the `binder_initial_body_cat`-derived src idx the
    /// per-rule dispatch arm carries (same `unwrap_or(category)` fallback
    /// as `prefix.rs`).
    pub body_src_idx: Option<u16>,
    /// F5-2 mixfix members ONLY: the member-side `MixfixLiteralRun`
    /// coordinate after each consumed item — `mixfix_coords[d]` = the state
    /// after `d` post-trigger consumes, `d ∈ 0..=items.len()` (entry 0 = the
    /// initial `(2, 0, 0)`). Empty for Binder/Nullary (prefix-surface)
    /// members.
    pub mixfix_coords: Vec<(u8, u8, u8)>,
}

/// The opening of every #141 G8 refusal message.
///
/// # Why these are refusals and not asserts
///
/// The seventeen `assert!`/`assert_eq!` sites this constant now heads encoded
/// two things: REAL ENCODING LIMITS of the factored spine (`spine_id_end <
/// RECOVERY_BASE`, `next_id < 250`, `leaf_depth < u8::MAX`) — which a large
/// grammar CAN reach — and internal agreements between the discovery walk and
/// the emission. Both were `assert!`s on the belief that they were unreachable,
/// and both were MUTE: under this workspace's cranelift dev backend a panic
/// inside a proc macro prints nothing at all; `rustc` dies with `fatal runtime
/// error: Rust cannot catch foreign exceptions` (#141 RED-0, 2026-07-29). A
/// grammar author who hit a spine-id ceiling saw a compiler crash with no
/// message.
///
/// The messages now travel as `String`s in `CategoryFactoring::refusals` /
/// `MixfixFactoring::refusals`, are turned into `compile_error!` tokens by
/// `build_spine_emission_from_parts`, and are spliced into the generated engine
/// module through `SpineEmission::refusals`. `compile_error!` is a TOKEN,
/// rendered by `rustc`, so the backend cannot swallow it.
pub const LIMIT_REFUSAL: &str = "mettail: the S1 spine factoring cannot be encoded —";

// ═══════════════════════════════════════════════════════════════════════════
// Trie build.
// ═══════════════════════════════════════════════════════════════════════════

/// Finalize a member's leaf at `leaf_depth` (post-trigger items consumed
/// INCLUDING the leaf edge) — typed commit coordinates + identity pos-map
/// (amendment A4).
pub fn finalize_leaf(
    member: CandidateMember,
    leaf_depth: usize,
    refusals: &mut Vec<String>,
) -> GroupMember {
    // ★ #141 G8. A REAL ENCODING LIMIT: marker positions are `u8`, so a spine
    // deeper than 254 post-trigger items cannot be addressed. A large grammar
    // CAN reach it. `refusals` is the same `&mut` sink idiom this function's
    // caller already uses for `interior_accepts`; the message reaches the user
    // as a `compile_error!` in the generated engine module, which a `panic!`
    // inside a cranelift-compiled proc macro never could (#141 RED-0).
    if leaf_depth >= u8::MAX as usize {
        refusals.push(format!(
            "{LIMIT_REFUSAL} the spine leaf for rule index {} sits at depth {leaf_depth}, \
             but a marker position is a `u8`, so the addressable depth is {} — the \
             factored spine cannot be encoded. Split the rule's shared prefix, or shorten \
             the surface it factors through.",
            member.rule_idx,
            u8::MAX as usize - 1,
        ));
    }
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
            // ★ #141 G8. Model drift, not a grammar limit — but the same
            // treatment, because a `panic!` here is mute and the index below
            // would panic anyway with no message at all.
            let (kind, completed_idx, sub_pos) = match member.mixfix_coords.get(leaf_depth) {
                Some(&coord) => coord,
                None => {
                    refusals.push(format!(
                        "{LIMIT_REFUSAL} the mixfix member at rule index {} recorded {} spine \
                     coordinates but leafs at depth {leaf_depth}, so the discovery walk and \
                     the item list disagree. This is a macro bug, not a grammar bug — \
                     please report it.",
                        member.rule_idx,
                        member.mixfix_coords.len(),
                    ));
                    (0u8, 0u8, 0u8)
                },
            };
            (
                MemberCommit::MixfixRun {
                    rule_idx: member.rule_idx,
                    kind,
                    completed_idx,
                    sub_pos,
                },
                SpinePosMap::Mixfix {
                    // `get(..=)` rather than indexing: the refusal above has
                    // already recorded the disagreement, and a second panic on
                    // the same condition would say nothing new and print nothing
                    // at all.
                    coords_at_depth: member
                        .mixfix_coords
                        .get(..=leaf_depth)
                        .unwrap_or(&[])
                        .to_vec(),
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

/// Stack-safe trie build, returning the FOREST for the node reached by
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
///     the macro's `wpda_codegen::forks::S1F5_ACCEPT_CONTINUE`): the exhausted member becomes
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
/// into their `children` lists verbatim, the macro's `wpda_codegen::factoring::flatten_forest` applies the same
/// rule to multi-root pre-root children, and every emitted divergence fork
/// therefore puts the spine-continue branch before the accept commit
/// branches. The choice preserves OFF's relative branch order at the only
/// real cohort (rholang InputBind@ emits [QuotedQuery, Quoted]) and
/// minimizes `source_priority` order channels; the emission pins assert it.
///
/// A part whose members ALL exhaust here (identical-sequence twins) returns
/// an accepts-only forest — never `Interior { children: [] }` (red-team
/// F-10; the synthetic all-twins witnesses pin both the root-level and the
/// spliced form).
pub fn build_tree(
    depth: usize,
    edge_item: SpineItem,
    members: Vec<CandidateMember>,
    accept_continue: bool,
    interior_accepts: &mut Vec<u16>,
    refusals: &mut Vec<String>,
) -> Vec<SpineTree> {
    enum Task {
        Enter {
            depth: usize,
            edge_item: SpineItem,
            members: Vec<CandidateMember>,
        },
        Assemble {
            edge_item: SpineItem,
            accepts: Vec<SpineTree>,
            value_base: usize,
        },
    }

    let mut tasks = vec![Task::Enter { depth, edge_item, members }];
    let mut values: Vec<Vec<SpineTree>> = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            Task::Enter { depth, edge_item, members } if members.len() == 1 => {
                let member = members
                    .into_iter()
                    .next()
                    .expect("a len()==1 vector yields its member");
                values.push(vec![SpineTree::Leaf {
                    item: edge_item,
                    member: finalize_leaf(member, depth, refusals),
                }]);
            },
            Task::Enter { depth, edge_item, members } => {
                // ≥2 members: exhausted members leaf out (or defer, per the
                // stance); the rest partition by the next item, preserving
                // first-occurrence order (rule declaration order).
                let mut parts: IndexMap<SpineItem, Vec<CandidateMember>> = IndexMap::new();
                let mut accepts: Vec<SpineTree> = Vec::new();
                for member in members {
                    if member.items.len() == depth {
                        if accept_continue {
                            accepts.push(SpineTree::Leaf {
                                item: edge_item.clone(),
                                member: finalize_leaf(member, depth, refusals),
                            });
                        } else {
                            interior_accepts.push(member.rule_idx);
                        }
                        continue;
                    }
                    let item = member.items[depth].clone();
                    parts.entry(item).or_default().push(member);
                }

                if parts.is_empty() {
                    // Every member exhausted at this node (all-twins part,
                    // F-10): accepts-only forest. Empty overall only under
                    // the F0 stance, where interior_accepts discards it.
                    values.push(accepts);
                    continue;
                }

                let value_base = values.len();
                tasks.push(Task::Assemble { edge_item, accepts, value_base });
                for (item, part) in parts.into_iter().rev() {
                    tasks.push(Task::Enter {
                        depth: depth + 1,
                        edge_item: item,
                        members: part,
                    });
                }
            },
            Task::Assemble { edge_item, accepts, value_base } => {
                let mut children = Vec::new();
                children.extend(values.drain(value_base..).flatten());
                debug_assert!(!children.is_empty());
                let mut forest = Vec::with_capacity(1 + accepts.len());
                forest.push(SpineTree::Interior { item: edge_item, children });
                forest.extend(accepts);
                values.push(forest);
            },
        }
    }
    debug_assert_eq!(values.len(), 1);
    values.pop().expect("spine-tree PDA produced no forest")
}

/// One flattened spine node during emission.
pub struct FlatNode<'t> {
    pub node_id: u8,
    pub children: Vec<(&'t SpineTree, u8)>, // child tree + child node id
}

/// Borrowed arm plan over a group FOREST (F5-1). Allocate all interior root
/// IDs first, then each visited node's immediate interior-child IDs before
/// descending. Output rows use preorder; ID allocation is not generic preorder.
/// Leaves are consumed as EDGES of their parent's arm and have no own arm.
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
/// from 3, allocated in immediate-child batches during preorder traversal).
///
/// ★ #141 G8 — `refusals` is the same `&mut` sink the trie build uses. The three
/// invariants below (non-empty forest, ≥2 leaves, and the `u8` node-id ceiling)
/// were `assert!`s; the last of them is a REAL ENCODING LIMIT a wide group
/// reaches. See [`LIMIT_REFUSAL`].
pub fn flatten_forest<'a>(roots: &'a [SpineTree], refusals: &mut Vec<String>) -> Vec<FlatNode<'a>> {
    let mut out: Vec<FlatNode<'a>> = Vec::new();
    // The F1 "root must be Interior" invariant generalizes (plan §6): the
    // forest is non-empty and carries one leaf per member of a ≥2-member
    // group (the leaf/member equality itself is checked at build).
    if roots.is_empty() {
        refusals.push(format!(
            "{LIMIT_REFUSAL} an eligible group's spine forest is empty, so there is no \
             arm for its trigger branch to enter. This is a macro bug, not a grammar bug \
             — please report it.",
        ));
    }
    let forest_leaves = roots.iter().map(SpineTree::leaf_count).sum::<usize>();
    if forest_leaves < 2 {
        refusals.push(format!(
            "{LIMIT_REFUSAL} an eligible group's spine forest carries {forest_leaves} \
             leaf/leaves, but a group has ≥2 members and one leaf per member. This is a \
             macro bug, not a grammar bug — please report it.",
        ));
    }
    // Pre-root arm: node 1 consumes the root EDGES; interior roots land on
    // their own arms at ids assigned from 2, leaf roots commit (id 0).
    let mut next_id: u8 = 2;
    let mut pre_root_children: Vec<(&SpineTree, u8)> = Vec::with_capacity(roots.len());
    for root in roots {
        let cid = match root {
            SpineTree::Interior { .. } => {
                let cid = next_id;
                // ★ #141 G8 — a REAL ENCODING LIMIT: marker positions are `u8`
                // and the id space above 250 is reserved. A wide group reaches
                // it, and what it deserves is a message rather than a mute abort.
                if next_id >= 250 {
                    refusals.push(format!(
                        "{LIMIT_REFUSAL} a group's spine needs more than 250 interior \
                         node ids, but a marker position is a `u8` and ids at or above \
                         250 are reserved. Reduce the number of members sharing this \
                         prefix, or shorten the surface they share.",
                    ));
                }
                next_id = next_id.saturating_add(1);
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
                    // ★ #141 G8 — the descendant twin of the pre-root ceiling
                    // above; same `u8` marker-position limit, same message.
                    if next_id >= 250 {
                        refusals.push(format!(
                            "{LIMIT_REFUSAL} a group's spine needs more than 250 interior \
                             node ids, but a marker position is a `u8` and ids at or \
                             above 250 are reserved. Reduce the number of members sharing \
                             this prefix, or shorten the surface they share.",
                        ));
                    }
                    next_id = next_id.saturating_add(1);
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

/// The SPINE-side arm plan of a single-root mixfix trie: the PRE-ROOT arm
/// key `(2, 0, 0)` (the state the fan pushes — its arm consumes the ROOT
/// EDGE itself, the F1 pre-root convention transported to mixfix
/// coordinates) is reserved but omitted from the returned rows. For each
/// INTERIOR node `n` in preorder, the arm key is the
/// spine state AFTER consuming `n`'s edge item — that arm consumes `n`'s
/// CHILDREN's edges (chain step or divergence fork). Returns `None` when
/// two arms would collide on a key (a second shared operand re-enters at
/// the same `(0, 0, 0)` via the width-1 spine's un-bumped `marker.bp == 0`
/// — the macro's `IneligibleReason::MultiOperandSharedSpine` condition).
pub fn mixfix_spine_arm_coords(root: &SpineTree) -> Option<Vec<((u8, u8, u8), &SpineTree)>> {
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

/// Base of the synthetic spine rule-index space: `SPINE_ID = SPINE_RULE_BASE +
/// group ordinal per category` (plan §2 item 1). Chosen clear of every real
/// per-category rule index and BELOW the recovery branch offset space
/// (the macro's `wpda_codegen::forks::RECOVERY_BASE` = `0xFE00`); amendment A9 asserts the
/// allocation never crosses either bound.
pub const SPINE_RULE_BASE: u16 = 0xF800;

/// Allocate at the original emission site, publishing no wrapped identifier.
/// On failure the caller must append a hard encoding refusal. The unchanged
/// ordinal makes failure explicit rather than manufacturing an unused ID.
/// `FactoringOrdinalAdmission.v` proves exact representable behavior.
pub(super) fn allocate_spine_id(ordinal: &mut u16) -> Option<u16> {
    let spine_id = SPINE_RULE_BASE.checked_add(*ordinal)?;
    let next = ordinal.checked_add(1)?;
    *ordinal = next;
    Some(spine_id)
}

#[cfg(test)]
#[path = "factoring/ordinal_tests.rs"]
mod ordinal_tests;

/// An ELIGIBLE factored group: one spine branch replaces its members'
/// per-rule Fork branches (F1).
#[derive(Debug)]
pub struct SpineGroup {
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
    pub fn member_rule_idxs(&self) -> BTreeSet<u16> {
        self.leaves().iter().map(|m| m.rule_idx).collect()
    }

    // dead_code: model accessor, exercised only by the `#[cfg(test)]` INV-8 assertions.
    #[cfg_attr(not(test), allow(dead_code))]
    pub fn leaf_count(&self) -> usize {
        self.roots.iter().map(SpineTree::leaf_count).sum()
    }

    pub fn leaves(&self) -> Vec<&GroupMember> {
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
    pub fn leaf_for(&self, rule_idx: u16) -> Option<(&SpineItem, &GroupMember)> {
        self.roots.iter().find_map(|root| root.leaf_for(rule_idx))
    }
}

/// Why a bucket member is emitted as an ordinary (unfactored) singleton.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SingletonReason {
    /// The member shares its first post-trigger item with no sibling.
    LoneRootChild,
    /// ★A2: the member participates in the `(cat, rule_idx)`-keyed cast
    /// machinery and must keep its own rule identity on every frame — see
    /// `numeric_cast_adapter::cast_machinery_participates`.
    CastMachinery,
    /// The member has no mergeable post-trigger item at all (its first item
    /// already terminates mergeability — e.g. Rholang `PNew`'s leading
    /// binder-list) — it commits at the trigger exactly as today.
    EmptySequence,
    /// The macro's `wpda_codegen::forks::S1_FACTORING` is `false`: the emission-effective
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
pub struct SingletonMember {
    pub rule_idx: u16,
    pub reason: SingletonReason,
}

/// Why a ≥2-member candidate group is NOT factored in F0 (emitted unfactored,
/// byte-identical to today; F5 territory).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IneligibleReason {
    /// One or more members are proper prefixes of siblings (interior
    /// accept-nodes — e.g. Rholang `InputBindQuoted` inside the `@`-led
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
pub struct IneligibleGroup {
    pub reason: IneligibleReason,
    pub member_rule_idxs: Vec<u16>,
}

/// One `(category, leading_literal)` prefix cohort.
///
/// `leading_literal` / `cohort_size` / `ineligible` / `singletons` are INV-8
/// model data read only by the `#[cfg(test)]` accounting assertions (dead in
/// the non-test lib build); only `groups` is consumed by emission.
#[derive(Debug)]
pub struct FactoringBucket {
    #[cfg_attr(not(test), allow(dead_code))]
    pub leading_literal: String,
    /// Total members discovered in this bucket BEFORE any exclusion — the
    /// INV-8 no-loss denominator (amendment A5): group leaves plus ineligible
    /// members plus singletons equal `cohort_size`.
    #[cfg_attr(not(test), allow(dead_code))]
    pub cohort_size: usize,
    pub groups: Vec<SpineGroup>,
    #[cfg_attr(not(test), allow(dead_code))]
    pub ineligible: Vec<IneligibleGroup>,
    #[cfg_attr(not(test), allow(dead_code))]
    pub singletons: Vec<SingletonMember>,
}

#[derive(Debug)]
pub struct CategoryFactoring {
    pub category_src_idx: u16,
    pub buckets: Vec<FactoringBucket>,
    /// ★ #141 G8 — the ENCODING-LIMIT refusals discovered while building this
    /// category's partition, rendered by `build_spine_emission_from_parts` into
    /// `SpineEmission::refusals` and spliced into the generated engine module as
    /// `compile_error!`s. See [`LIMIT_REFUSAL`].
    pub refusals: Vec<String>,
}

/// Original enabled prefix partition over authored per-category rule rows.
///
/// Discovery runs once per category. Cast checks retain the original bucket
/// and member order, after indexed rule lookup and before empty-item exclusion.
/// The callbacks borrow original rules; they must not eagerly reorder discovery
/// or normalize descriptors. The caller retains the original encoding/input
/// preconditions and supplies its unchanged recovery-branch base.
///
/// `PrefixFactoringProjection.v` models the callback and tree-call boundary,
/// including the original arithmetic domain and diagnostic effects.
pub fn build_prefix_factoring_with<R>(
    per_cat: &[Vec<R>],
    accept_continue: bool,
    recovery_base: u16,
    mut discover: impl FnMut(u16, &[R]) -> Vec<(String, CandidateMember)>,
    mut cast_participates: impl FnMut(&R) -> bool,
) -> Vec<CategoryFactoring> {
    match try_build_prefix_factoring_with(
        per_cat,
        accept_continue,
        recovery_base,
        |category, rules| Ok::<_, std::convert::Infallible>(discover(category, rules)),
        |rule| Ok(cast_participates(rule)),
    ) {
        Ok(value) => value,
        Err(never) => match never {},
    }
}

/// Original factoring with fallible discovery and cast observations.
/// Callback errors stop at their original site, without exposing partial groups.
pub fn try_build_prefix_factoring_with<'rules, R, E>(
    per_cat: &'rules [Vec<R>],
    accept_continue: bool,
    recovery_base: u16,
    mut discover: impl FnMut(u16, &'rules [R]) -> Result<Vec<(String, CandidateMember)>, E>,
    mut cast_participates: impl FnMut(&R) -> Result<bool, E>,
) -> Result<Vec<CategoryFactoring>, E> {
    let mut out = Vec::with_capacity(per_cat.len());
    // ★ #141 G8 — one sink per category, drained into that category's
    // `CategoryFactoring` (`std::mem::take` at the push below).
    let mut refusals: Vec<String> = Vec::new();
    for (cat_i, rules) in per_cat.iter().enumerate() {
        let category_src_idx = cat_i as u16;
        let members = discover(category_src_idx, rules)?;
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
                if cast_participates(rule)? {
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
                let roots = build_tree(
                    1,
                    root_item,
                    part,
                    accept_continue,
                    &mut interior_accepts,
                    &mut refusals,
                );
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
                // construction (single-member base; under the F0
                // stance twins and proper prefixes were routed to
                // interior_accepts above, under F5-1 they ARE leaves).
                let leaf_count: usize = roots.iter().map(SpineTree::leaf_count).sum();
                if leaf_count != member_rule_idxs.len() {
                    refusals.push(format!(
                        "{LIMIT_REFUSAL} the eligible group for category index \
                         {category_src_idx} at trigger {leading_literal:?} built \
                         {leaf_count} spine leaves for {} members. Every member commits at \
                         exactly one leaf by construction, so the trie build and the member \
                         list disagree. This is a macro bug, not a grammar bug — please \
                         report it.",
                        member_rule_idxs.len(),
                    ));
                }
                let body_src_idx = body_src_idxs
                    .first()
                    .copied()
                    // All-nullary group: no BinderRule state consumes the
                    // field before a commit; carry the owning category.
                    .unwrap_or(category_src_idx);
                let Some(spine_id) = allocate_spine_id(&mut next_spine_ordinal) else {
                    refusals.push(format!(
                        "{LIMIT_REFUSAL} category index {category_src_idx}, trigger \
                         {leading_literal:?}, cannot allocate spine ordinal \
                         {next_spine_ordinal}: base {SPINE_RULE_BASE:#06x} plus ordinal \
                         exceeds the u16 rule-index encoding."
                    ));
                    continue;
                };
                groups.push(SpineGroup { spine_id, body_src_idx, roots });
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
        // ★ #141 G8 — the two A9 ceilings, and the clearest case in the file for
        // refusing rather than asserting: a grammar with enough factorable
        // prefixes in ONE category reaches them, and what it deserves is a
        // message naming the category and the ceiling it crossed.
        if spine_id_end >= recovery_base as u32 {
            refusals.push(format!(
                "{LIMIT_REFUSAL} category index {category_src_idx} allocates \
                 {next_spine_ordinal} synthetic spine ids, ending at {spine_id_end:#06x}, \
                 which collides with the recovery-branch id space that begins at {:#06x}. \
                 Reduce the number of distinct factorable prefixes declared in this \
                 category.",
                recovery_base,
            ));
        }
        if spine_id_end >= u16::MAX as u32 {
            refusals.push(format!(
                "{LIMIT_REFUSAL} category index {category_src_idx} ends its synthetic spine \
                 id space at {spine_id_end:#06x}, which overflows the `u16` a rule index \
                 is encoded in. Reduce the number of distinct factorable prefixes declared \
                 in this category.",
            ));
        }
        out.push(CategoryFactoring {
            category_src_idx,
            buckets,
            refusals: std::mem::take(&mut refusals),
        });
    }
    Ok(out)
}

/// Original disabled factoring path: every discovered member is a singleton.
///
/// Retains empty categories and first-seen trigger/member order. This path does
/// not index rule rows, consult cast machinery, build trees or check spine IDs.
pub fn prefix_identity_partition<R>(
    per_cat: &[Vec<R>],
    mut discover: impl FnMut(u16, &[R]) -> Vec<(String, CandidateMember)>,
) -> Vec<CategoryFactoring> {
    match try_prefix_identity_partition(per_cat, |category, rules| {
        Ok::<_, std::convert::Infallible>(discover(category, rules))
    }) {
        Ok(value) => value,
        Err(never) => match never {},
    }
}

/// Disabled factoring still observes discovery and propagates its first error.
/// It never observes cast machinery or constructs a factoring tree.
pub fn try_prefix_identity_partition<'rules, R, E>(
    per_cat: &'rules [Vec<R>],
    mut discover: impl FnMut(u16, &'rules [R]) -> Result<Vec<(String, CandidateMember)>, E>,
) -> Result<Vec<CategoryFactoring>, E> {
    let mut out = Vec::with_capacity(per_cat.len());
    for (cat_i, rules) in per_cat.iter().enumerate() {
        let category_src_idx = cat_i as u16;
        let members = discover(category_src_idx, rules)?;
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
        out.push(CategoryFactoring {
            category_src_idx,
            buckets,
            refusals: Vec::new(),
        });
    }
    Ok(out)
}
