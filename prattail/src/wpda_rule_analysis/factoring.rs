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
