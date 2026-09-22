//! Original mixfix grouping, factoring descriptors and discovery loops.
//!
//! These functions relocate the macro implementation over its existing
//! binding-power descriptions. The source operator borrow, category/rule
//! coordinates, slice ordering, eligibility, diagnostics and iterative tree
//! helpers remain unchanged. Callers prepare the original binding-power table
//! and label index, and supply the original lazy category resolver and cast
//! predicate. No grammar classifier or recognizer is introduced here.
//!
//! `MixfixDescriptorProjection.v` models the source-correspondence boundary.
//! This is not admission of arbitrary untrusted images: callers must preserve
//! the executed arithmetic and indexing domain, including the original narrow
//! coordinate casts, checked-build subtraction and late encoding ceilings.
//! Tree construction, coordinate walking and tree lifecycle use the shared
//! original implementations rather than new recursive traversals.

use std::collections::{BTreeSet, HashMap};

use super::factoring::{
    build_tree, mixfix_spine_arm_coords, CandidateMember, CategoryFactoring, GroupMember,
    IneligibleGroup, IneligibleReason, MemberKind, SingletonMember, SingletonReason, SpineItem,
    SpineTree, LIMIT_REFUSAL, SPINE_RULE_BASE,
};
use crate::binding_power::{BindingPowerTable, InfixOperator};

/// One operator resolved to its global packing coordinates, retaining a borrow of
/// the source [`InfixOperator`] for its tier flags and binding powers. Produced by
/// [`group_ops_by_cat_terminal`].
pub struct GroupedOp<'a> {
    /// The source operator (tier flags `is_postfix` / `is_mixfix`, `left_bp`,
    /// `right_bp`, `terminal`, ...).
    pub op: &'a InfixOperator,
    /// Result-category source index (the packing's category).
    pub result_src_idx: u16,
    /// Local rule index within the result category.
    pub rule_idx: u16,
}

/// B-2 (Stage S0) NO-LOSS foundation: group EVERY operator by
/// `(operand cat_src_idx, terminal)`, preserving the canonical
/// `bp_table.operators` order within each group (category-alphabetical ×
/// infix/mixfix-then-postfix, each in declaration order — see
/// `analyze_binding_powers`).
///
/// This single grouping feeds BOTH the per-tier slice emitters
/// (`emit_{infix,postfix,mixfix}_bp_fn`) AND the lattice lex-alt emitter
/// (`emit_infix_lex_alt_rule_arms`, `kind_dispatch.rs`), so the per-(cat,terminal)
/// rule multiset is IDENTICAL across the two dispatch surfaces by construction —
/// the GEN-1 NO-LOSS invariant. Operators whose operand category or
/// `(result_category, label)` packing coordinates cannot be resolved are skipped
/// (matching the legacy emitters' defensive `filter_map` / `continue`).
pub fn group_ops_by_cat_terminal<'a>(
    bp_table: &'a BindingPowerTable,
    categories: &[String],
    label_index: &std::collections::HashMap<(String, String), (u16, u16)>,
) -> std::collections::BTreeMap<(u16, String), Vec<GroupedOp<'a>>> {
    let mut grouped: std::collections::BTreeMap<(u16, String), Vec<GroupedOp<'a>>> =
        std::collections::BTreeMap::new();
    for op in &bp_table.operators {
        let Some(cat_src_idx) = categories
            .iter()
            .position(|cat| cat == &op.category)
            .map(|idx| idx as u16)
        else {
            continue;
        };
        let Some(&(result_src_idx, rule_idx)) =
            label_index.get(&(op.result_category.clone(), op.label.clone()))
        else {
            continue;
        };
        grouped
            .entry((cat_src_idx, op.terminal.clone()))
            .or_default()
            .push(GroupedOp { op, result_src_idx, rule_idx });
    }
    grouped
}

/// One factorable mixfix cohort (an ELIGIBLE group covering its whole
/// `(dispatch category, trigger)` slice).
#[derive(Debug)]
pub struct MixfixGroup {
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
    /// spine id) — stamps the trigger branch cost, the lex-alt action
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
    pub fn member_rule_idxs(&self) -> Vec<u16> {
        self.member_l_bps.iter().map(|&(_, r)| r).collect()
    }

    // dead_code: model accessor, exercised only by the `#[cfg(test)]` INV-8 assertions.
    #[cfg_attr(not(test), allow(dead_code))]
    pub fn leaves(&self) -> Vec<&GroupMember> {
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
pub struct MixfixBucket {
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
pub struct MixfixFactoring {
    pub dispatch_cat_src_idx: u16,
    pub buckets: Vec<MixfixBucket>,
    /// ★ #141 G8 — see [`CategoryFactoring::refusals`].
    pub refusals: Vec<String>,
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
pub fn mixfix_member_items_with<E>(
    op: &InfixOperator,
    categories: &[String],
    resolve_category: &mut impl FnMut(&str, &[String], &'static str, &str) -> Result<u16, E>,
) -> (Vec<SpineItem>, Vec<(u8, u8, u8)>, bool) {
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
        // ★ #131 — SIBLING OF THE ROOT, IN THE FACTORING SPINE. A CAPTURE part
        // terminates mergeability for exactly the reason a `*sep` repetition does
        // above, and the same reason `BinderPosition::IdentTextCapture` terminates
        // it on the binder side (see `spine_position_mergeable`): the shared spine
        // trie has NO node for a token consumption — it merges literal runs and
        // category sub-parses, and a capture is neither. The member commits at or
        // before this depth and runs its capture in its own `MixfixLiteralRun`.
        //
        // ⚠ WITHOUT THIS the loop would fall through to `SpineItem::ParamParse`
        // below, whose `lookup` ends in `.unwrap_or(0)` — so the non-category
        // `Ident` would become category 0, the FIRST declared category, and a
        // factored cohort would SUB-PARSE THE WRONG CATEGORY with no diagnostic.
        // That is the identical fails-open shape root-caused three times over on
        // this path (`semantic_actions`' `lookup_cat_idx`, `emit_mixfix_parts_fn`'s
        // `position(..).unwrap_or(0)`), reached here through a different door.
        if part.capture_kind.is_some() {
            return (items, coords, true);
        }
        // The operand: always dispatched at `cur_bp: 0` (the mixfix machine
        // convention, engine_impl kind-2/kind-1 operand arms). Post-operand
        // the Unwinding-MixfixMarker arm reads `marker.bp == part_i` and
        // re-enters at `(0, part_i, 0)`.
        //
        // ★ #141 — sibling 1 of 7. This lookup ended in `.unwrap_or(0)`, exactly
        // as the comment fifteen lines above warns: an undeclared operand category
        // became index 0, the FIRST declared category, and the factored cohort
        // SUB-PARSED THE WRONG CATEGORY with no diagnostic.
        //
        // This is a macro-time VALUE position (`SpineItem::ParamParse` is consumed
        // later in the same expansion), so it takes the discipline `binder_items`
        // established for its own `ParamParse` arm rather than a token refusal:
        // DECLINE TO MERGE. `return (…, true)` routes this member to its OWN
        // un-factored emission, and that emission — `infix::emit_mixfix_parts_fn`,
        // #141 G3 — resolves the SAME `part.operand_category` through
        // `binder::cat_idx_tokens` and substitutes a spanned `compile_error!`
        // naming the category and the rule. The build therefore cannot succeed
        // with a wrong index; it fails with a message. A category with no index is
        // more reason to decline merging, not less.
        let Ok(cat_src_idx) = resolve_category(
            &part.operand_category,
            categories,
            "a mixfix cohort's operand position",
            &op.label,
        ) else {
            return (items, coords, true);
        };
        items.push(SpineItem::ParamParse { cat_src_idx, cur_bp: 0 });
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
#[allow(clippy::too_many_arguments)]
pub fn build_mixfix_factoring_with<R, E>(
    categories: &[String],
    per_cat: &[Vec<R>],
    prefix_partition: &[CategoryFactoring],
    grouped: &std::collections::BTreeMap<(u16, String), Vec<GroupedOp<'_>>>,
    max_slice: usize,
    recovery_base: u16,
    mut resolve_category: impl FnMut(&str, &[String], &'static str, &str) -> Result<u16, E>,
    mut cast_participates: impl FnMut(&R) -> bool,
) -> Vec<MixfixFactoring> {
    // Operand-absorbability oracle (A-M5): every (category, terminal) that
    // carries ANY operator row — a post-operand divergence literal matching
    // one of these could be absorbed INTO the operand sub-parse.
    let operator_trigger_keys: BTreeSet<(u16, String)> = grouped.keys().cloned().collect();
    // ★ #141 G8 — the builder-wide encoding-limit sink; see `LIMIT_REFUSAL`.
    let mut refusals: Vec<String> = Vec::new();
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
    for ((dispatch_cat, terminal), ops) in grouped {
        let mixfix_ops: Vec<&GroupedOp<'_>> = ops
            .iter()
            .filter(|g| g.op.is_mixfix)
            .take(max_slice)
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
            let (member_items, coords, truncated) =
                mixfix_member_items_with(g.op, categories, &mut resolve_category);
            let total_positions = member_items.len();
            // The member's own action-entry expected_input_cats (mirrors
            // semantic_actions' mixfix arm: LHS cat first, then per part).
            //
            // ★ #141 — sibling 2 of 7. The `lookup` closure that stood here ended in
            // `.unwrap_or(0)`, so an undeclared operand category entered the
            // cohort's `action_for` row as index 0 — the FIRST declared category —
            // and the arg-shape gate then admitted or rejected readings against a
            // category the rule never named. Same discipline as the operand lookup
            // in `mixfix_member_items` above: this is a macro-time VALUE position,
            // so it DECLINES rather than substituting. Dropping the candidate means
            // no cohort is formed for this operator, it emits itself, and
            // `infix::emit_mixfix_parts_fn` (#141 G3) refuses on the same category
            // with a spanned `compile_error!` naming the rule.
            let mut expected_cats: Vec<u16> = Vec::with_capacity(1 + g.op.mixfix_parts.len());
            expected_cats.push(*dispatch_cat);
            let mut unresolved_operand = false;
            for part in &g.op.mixfix_parts {
                // #131: a CAPTURE part's arg is token TEXT, so its expected category is
                // ANY_CAT — mirroring the repetition arg above and, critically, mirroring
                // `semantic_actions`' derivation EXACTLY. The two must agree: this vector
                // becomes the cohort's `action_for` row while that one becomes the
                // member's, and a disagreement makes the arg-shape gate reject readings
                // in one emission mode and accept them in the other.
                if part.repetition.is_some() || part.capture_kind.is_some() {
                    expected_cats.push(u16::MAX);
                } else {
                    match resolve_category(
                        &part.operand_category,
                        categories,
                        "a mixfix cohort's action entry",
                        &g.op.label,
                    ) {
                        Ok(idx) => expected_cats.push(idx),
                        Err(_) => {
                            unresolved_operand = true;
                            break;
                        },
                    }
                }
            }
            if unresolved_operand {
                continue;
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
            let is_cast = rule.map(&mut cast_participates).unwrap_or(false);
            if is_cast {
                singletons.push(SingletonMember {
                    rule_idx: cand.member.rule_idx,
                    reason: SingletonReason::CastMachinery,
                });
            } else if cand.member.items.is_empty() {
                // Rep-part-0 members (rholang InputBindPolyadic `,`): no
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
                &mut refusals,
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
        // ★ #141 G8 — the mixfix-extended twins of the two A9 ceilings above.
        // Same real limit, same reachability by a large grammar.
        if spine_id_end >= recovery_base as u32 {
            refusals.push(format!(
                "{LIMIT_REFUSAL} category index {cat_i} ends its mixfix-extended spine id \
                 space at {spine_id_end:#06x}, which collides with the recovery-branch id \
                 space that begins at {:#06x}. Reduce the number of distinct factorable \
                 mixfix cohorts declared in this category.",
                recovery_base,
            ));
        }
        if spine_id_end >= u16::MAX as u32 {
            refusals.push(format!(
                "{LIMIT_REFUSAL} category index {cat_i} ends its mixfix-extended spine id \
                 space at {spine_id_end:#06x}, which overflows the `u16` a rule index is \
                 encoded in. Reduce the number of distinct factorable mixfix cohorts \
                 declared in this category.",
            ));
        }
    }

    let mut out: Vec<MixfixFactoring> = Vec::with_capacity(per_dispatch.len());
    let mut dispatch_cats: Vec<u16> = per_dispatch.keys().copied().collect();
    dispatch_cats.sort_unstable();
    for cat in dispatch_cats {
        let buckets = per_dispatch
            .remove(&cat)
            .expect("dispatch cat key collected from the map");
        out.push(MixfixFactoring {
            dispatch_cat_src_idx: cat,
            buckets,
            refusals: Vec::new(),
        });
    }
    // ★ #141 G8 — the sink is builder-wide (its ceilings are computed over the
    // SHARED `next_ordinal` allocation, not per dispatch category), so it is
    // drained onto the FIRST partition entry. When there is none, the refusals
    // still have to reach the user, so an entry is created to carry them —
    // `buckets` empty, which every consumer already treats as "no cohorts".
    if !refusals.is_empty() {
        match out.first_mut() {
            Some(first) => first.refusals = refusals,
            None => out.push(MixfixFactoring {
                dispatch_cat_src_idx: 0,
                buckets: Vec::new(),
                refusals,
            }),
        }
    }
    out
}

fn op_first_nullary_literal(op: &InfixOperator) -> Option<String> {
    op.nullary_literals.first().cloned()
}

/// Eligibility + trie build for one whole-slice candidate group.
#[allow(clippy::too_many_arguments)]
fn build_mixfix_group(
    dispatch_cat: u16,
    trigger: &str,
    root_item: SpineItem,
    part: Vec<MixfixCandidate>,
    operator_trigger_keys: &BTreeSet<(u16, String)>,
    next_ordinal: &mut [u16],
    refusals: &mut Vec<String>,
) -> Result<MixfixGroup, IneligibleGroup> {
    let member_rule_idxs: Vec<u16> = part.iter().map(|c| c.member.rule_idx).collect();
    let member_l_bps: Vec<(u8, u16)> = part.iter().map(|c| (c.l_bp, c.member.rule_idx)).collect();
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
        if cand.fixb_literal != fixb_literal {
            refusals.push(format!(
                "{LIMIT_REFUSAL} the mixfix cohort at dispatch category index \
                 {dispatch_cat}, trigger {trigger:?}, has non-uniform Fix-B \
                 first-literal evidence ({:?} for rule index {} against {fixb_literal:?} \
                 for the cohort), so the spine's method-name prune would diverge from its \
                 members'. Uniformity is implied by the shared root item, so this is a \
                 macro bug, not a grammar bug — please report it.",
                cand.fixb_literal, cand.member.rule_idx,
            ));
        }
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
        refusals,
    );
    if !interior_accepts.is_empty() {
        return Err(IneligibleGroup {
            reason: IneligibleReason::InteriorAccept { accepting_rule_idxs: interior_accepts },
            member_rule_idxs,
        });
    }
    let leaf_count: usize = roots.iter().map(SpineTree::leaf_count).sum();
    if leaf_count != member_rule_idxs.len() {
        refusals.push(format!(
            "{LIMIT_REFUSAL} the eligible mixfix group at dispatch category index \
             {dispatch_cat}, trigger {trigger:?}, built {leaf_count} spine leaves for {} \
             members. Every member commits at exactly one leaf by construction, so the \
             trie build and the member list disagree. This is a macro bug, not a grammar \
             bug — please report it.",
            member_rule_idxs.len(),
        ));
    }
    if roots.len() != 1 {
        refusals.push(format!(
            "{LIMIT_REFUSAL} the mixfix group at dispatch category index {dispatch_cat}, \
             trigger {trigger:?}, has {} spine roots. A mixfix group is single-root by \
             construction — the root partition IS the group criterion — so the partition \
             and the trie build disagree. This is a macro bug, not a grammar bug — please \
             report it.",
            roots.len(),
        ));
    }
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

/// The identity mixfix partition: the same cohort census (slice membership),
/// zero groups, every member a `FactoringDisabled` singleton — the INV-8
/// OFF-branch shape.
pub fn mixfix_identity_partition(
    grouped: &std::collections::BTreeMap<(u16, String), Vec<GroupedOp<'_>>>,
    max_slice: usize,
) -> Vec<MixfixFactoring> {
    let mut per_dispatch: HashMap<u16, Vec<MixfixBucket>> = HashMap::new();
    for ((dispatch_cat, terminal), ops) in grouped {
        let mixfix_ops: Vec<&GroupedOp<'_>> = ops
            .iter()
            .filter(|g| g.op.is_mixfix)
            .take(max_slice)
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
        out.push(MixfixFactoring {
            dispatch_cat_src_idx: cat,
            buckets,
            refusals: Vec::new(),
        });
    }
    out
}

/// Project the original ordered partition to its mixfix-parts presence rows.
pub fn mixfix_spine_parts_len_rows(partition: &[MixfixFactoring]) -> Vec<(u16, u16)> {
    let mut rows: Vec<(u16, u16)> = Vec::new();
    for fact in partition {
        for bucket in &fact.buckets {
            for group in &bucket.groups {
                rows.push((group.result_src_idx, group.spine_id));
            }
        }
    }
    rows
}
