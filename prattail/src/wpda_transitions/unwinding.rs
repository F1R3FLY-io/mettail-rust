use crate::automata::semiring::SemiringRef;
use crate::gss::WpdaGssNode;
use crate::wpda_runtime::{StackSymbolV2, WpdaState, WpdaTokenSource};
use crate::wpda_walker::{WpdaEngine, WpdaStepAction};

#[allow(clippy::too_many_arguments)]
pub fn unwinding_step<W, E, P>(
    engine: &E,
    frontier_top: Option<&WpdaGssNode>,
    _pos: usize,
    tokens: &dyn WpdaTokenSource,
    mut lex_one: impl FnMut() -> W,
    mut category_recognizes_token: impl FnMut(u16, &str) -> bool,
    mut mixfix_parts_len: impl FnMut(u16, u16) -> Option<u8>,
    mixfix_part: P,
    mut binder_marker_metadata: impl FnMut(u32) -> Option<(u16, u16, u32, u32)>,
    mut binderlist_inner_post_splice: impl FnMut(u16, u16, u32, u32) -> Option<u8>,
    mut optional_marker_metadata: impl FnMut(u32) -> Option<(u16, u16, u32, u32)>,
) -> WpdaStepAction<W>
where
    W: SemiringRef,
    E: WpdaEngine<W> + ?Sized,
{
    if let Some(node) = frontier_top {
        match node.symbol.kind {
            crate::wpda_runtime::SymbolKind::Return => {
                // After a Return pop, transition to InfixLoop
                // with cur_bp = the bp encoded in the popped
                // symbol. The Return's bp was set at
                // ConsumeAndPush time to the outer cur_bp.
                //
                // Stage 3.16 invariant (Cluster 4, Mechanism γ,
                // 2026-05-06): Return symbols ALWAYS carry
                // `bp = Some(outer_bp)` per codegen invariant
                // (constructed via with_kind_return on a
                // RuleAt that itself had Some(*cur_bp) at the
                // ConsumeAndPush site). Use expect() to surface
                // any codegen-invariant violation instead of
                // silently substituting 0.
                let outer_bp = node.symbol.bp.expect(
                    "Return symbol invariant: bp must be Some(outer_bp) \
                     set at the originating ConsumeAndPush site",
                );
                WpdaStepAction::Pop {
                    weight: lex_one(),
                    new_state: WpdaState::InfixLoop { cur_bp: outer_bp },
                }
            },
            crate::wpda_runtime::SymbolKind::CategoryEntry => {
                // Plan A (paren+postfix redesign, 2026-05-11):
                // compute only the local lookahead fact for
                // cross-cat-LHS inside parens. The walker
                // resolves the final post-pop state from
                // the cursor's exact predecessor edge; the
                // generated engine must not inspect the
                // shared GSS node and guess with
                // `edges_from(...).first()`, because a
                // Tomita/GSS node may have multiple
                // predecessor contexts.
                let inner_cat = node.symbol.category_src_idx;
                let new_state = if tokens.peek_text(_pos) == Some(")") {
                    // Plan A: if the token AFTER `)` is
                    // recognized by the inner cat, request
                    // inner-cat preservation. This is only
                    // a request: after the pop, the walker
                    // checks the cursor's concrete
                    // predecessor. Non-grouping predecessors
                    // override this to their own exact
                    // transition.
                    let close_hi = tokens.next_pos(_pos, 0).unwrap_or(_pos + 1);
                    let next_tok = tokens.peek_text(close_hi).unwrap_or("");
                    let inner_matches: bool = category_recognizes_token(inner_cat, next_tok);
                    if inner_matches {
                        // D8 fix (2026-05-13): emit sentinel
                        // `u16::MAX`. The walker resolves the
                        // ACTUAL inner-expression RESULT cat
                        // from cursor evidence.
                        let _ = inner_cat;
                        WpdaState::GroupingClosePreservingInner { inner_cat_src_idx: u16::MAX }
                    } else {
                        WpdaState::Unwinding
                    }
                } else {
                    WpdaState::Unwinding
                };
                // Phase 5 fix: when no special transition
                // applies, pop CategoryEntry but stay in
                // Unwinding so we continue unwinding into
                // any enclosing markers (binder rule_at,
                // collection marker). When the GSS is fully
                // unwound, frontier_top is None and the
                // outer Unwinding arm emits Accept.
                WpdaStepAction::Pop { weight: lex_one(), new_state }
            },
            crate::wpda_runtime::SymbolKind::CollectionMarker => {
                // Phase 4: just unwound to a marker (i.e., an
                // element just returned). Transition to
                // CollectionLoop to dispatch on close/sep.
                let result_src_idx = node.symbol.category_src_idx;
                let rule_idx = node.symbol.rule_index_in_category;
                // B8 / Issue C followup (2026-05-09); Phase 4 #2
                // (2026-05-12): for Class-3 binder rules, the
                // CollectionMarker for the names accumulator
                // never runs through CollectionLoop —
                // BinderListLoop handles iterations. After
                // the outer rule's terminal action fires,
                // the marker is left dangling at top. Pop
                // it transparently when the per-(src, rule,
                // slot_idx) `is_class3_collection_per_slot`
                // predicate confirms (not Class-2 sibling
                // slots which pop via ConsumeAndPop in
                // CollectionLoop's close branch).
                //
                // Phase 4 #2 multi-slot fix: pre-fix this
                // was a per-rule predicate. Rules with a
                // Class-3 BinderListLoop + Class-2 sibling
                // SimpleCollection (e.g. PInputsTagged)
                // incorrectly transparently-popped the
                // Class-2 sibling's marker. slot_idx is
                // recovered from `symbol.bp` (Phase 4 #1
                // preserves codegen-stamped slot_idx).
                let slot_idx_for_class3 = node.symbol.bp.unwrap_or(0);
                if engine.is_class3_collection_per_slot(
                    result_src_idx,
                    rule_idx,
                    slot_idx_for_class3,
                ) {
                    return WpdaStepAction::Pop {
                        weight: lex_one(),
                        new_state: WpdaState::Unwinding,
                    };
                }
                // CollectionMarker symbols carry the
                // codegen-stamped static slot_idx in bp.
                // Runtime accumulator identity is
                // cursor-local and recovered by the
                // walker from active collection depth
                // when it needs to splice or push a
                // CollectionId.
                let slot_idx = node.symbol.bp.expect(
                    "CollectionMarker invariant: bp must be \
                     Some(slot_idx) set at construction",
                );
                // The CollectionLoop field remains for
                // compatibility with existing state
                // constructors; cursor-aware walker
                // paths treat it as non-authoritative.
                let accumulator_id = slot_idx;
                let element_src_lookup: Option<u16> = engine
                    .collection_spec(result_src_idx, rule_idx, slot_idx)
                    .and_then(|__s| __s.element_src_idx);
                let element_src_idx = element_src_lookup.unwrap_or(result_src_idx);
                // str-cast collection-infix fix (2026-06-18):
                // recover the Pratt dispatch bp captured on the
                // CollectionMarker at open (continuation_bp =
                // Some(cur_bp) for Class-5 literals, Some(0) for
                // binder-internal collections). It feeds
                // CollectionLoop.outer_bp so the G1 close branch
                // resumes InfixLoop { cur_bp: outer_bp } — a
                // finalized collection joins the enclosing Pratt
                // loop exactly as an atomic primary does.
                // unwrap_or(0) degrades to the pre-fix behavior.
                let dispatch_bp = node.symbol.continuation_bp.unwrap_or(0);
                // Phase 4 #5b (2026-05-12): emit
                // `kv_phase: 0` as the default; the
                // walker's `set_cursor_inner_state`
                // patches it to 1 (key just parsed)
                // for HashMap slots whose cursor
                // collection_stack[acc_id].len() is
                // odd. For non-HashMap slots, this
                // 0 survives and dispatch routes
                // through the existing 3-branch
                // Fork (close / sep / bare-element).
                WpdaStepAction::Advance(WpdaState::CollectionLoop {
                    result_src_idx,
                    rule_idx,
                    element_src_idx,
                    outer_bp: dispatch_bp,
                    accumulator_id,
                    slot_idx,
                    kv_phase: 0u8,
                })
            },
            crate::wpda_runtime::SymbolKind::RuleAt(position) => {
                // Phase 5 + Stage 4: a multi-step rule's
                // marker is on top after a sub-parse
                // returned. Transition into BinderRule for
                // the marker's current position so the
                // remaining literals (e.g., closing `)` of
                // `bool(arg)`) and follow-on params get
                // consumed. The position-N arm in
                // emit_binder_rule_body decides whether
                // to advance (ConsumeAndReplace),
                // sub-parse another arg (ReplaceAndPush),
                // or finalize (ConsumeAndPop, which fires
                // the action). Without this, the engine
                // would prematurely Pop+InfixLoop after
                // the first sub-parse and the closing
                // delimiters would remain in the input.
                //
                // Stage 3.16 invariant (Cluster 4, Mechanism γ,
                // 2026-05-06): RuleAt's `bp: Option<u8>` is
                // genuinely Optional per
                // `StackSymbolV2::rule_at(.., bp: Option<u8>)`.
                // Some callers thread `Some(*outer_bp)` (when
                // a precedenced parent context exists);
                // others pass `None` (top-level RuleAt where
                // no outer_bp is tracked). The `unwrap_or(0)`
                // fallback is the legitimate Optional
                // handling: `0` is the canonical "top-level
                // cur_bp" sentinel used everywhere a Pratt
                // dispatch starts fresh.
                let outer_bp = node.symbol.bp.unwrap_or(0);
                let result_src_idx = node.symbol.category_src_idx;
                let rule_idx = node.symbol.rule_index_in_category;
                // body_src_idx isn't recoverable from the
                // RuleAt symbol alone; threading it
                // through is unnecessary because each
                // BinderRule arm reads category info
                // from the rule_idx via static lookups.
                // Pass 0 as a sentinel; the per-position
                // arms only use it for sub-parse Push
                // actions, which always re-read the
                // category from the rule's syntax
                // pattern at codegen time.
                let _ = position;
                WpdaStepAction::Advance(WpdaState::BinderRule {
                    result_src_idx,
                    rule_idx,
                    body_src_idx: 0u16,
                    outer_bp,
                })
            },
            crate::wpda_runtime::SymbolKind::GroupingMarker => {
                // B7 Pattern 2: inner expression of a
                // grouping just returned. Demand the
                // closing `)`. If the token after `)` is
                // recognized by the marker's category,
                // preserve that category by replacing the
                // marker with a CategoryEntry; otherwise
                // pop the marker and resume in the
                // predecessor context. This mirrors the
                // CategoryEntry-above-GroupingMarker
                // preserving path and is required when a
                // grouping was opened directly in a
                // delegated source category.
                //
                // Stage 3.16 invariant (Cluster 4, Mechanism γ,
                // 2026-05-06): GroupingMarker symbols ALWAYS
                // carry `bp = Some(outer_bp)` per the codegen
                // invariant in StackSymbolV2::grouping_marker.
                // expect() surfaces invariant violations.
                let outer_bp = node.symbol.bp.expect(
                    "GroupingMarker invariant: bp must be \
                     Some(outer_bp) — saved cur_bp at the open paren",
                );
                match tokens.peek_text(_pos) {
                    Some(")") => {
                        let inner_cat = node.symbol.category_src_idx;
                        let close_hi = tokens.next_pos(_pos, 0).unwrap_or(_pos + 1);
                        let next_tok = tokens.peek_text(close_hi).unwrap_or("");
                        let inner_matches: bool = category_recognizes_token(inner_cat, next_tok);
                        if inner_matches {
                            WpdaStepAction::ConsumeAndReplace {
                                symbol: StackSymbolV2::category_entry(inner_cat),
                                weight: lex_one(),
                                new_state: WpdaState::InfixLoop { cur_bp: outer_bp },
                            }
                        } else {
                            WpdaStepAction::ConsumeAndPop {
                                weight: lex_one(),
                                new_state: WpdaState::InfixLoop { cur_bp: outer_bp },
                            }
                        }
                    },
                    other => WpdaStepAction::Error(format!(
                        "expected `)` to close grouping at pos {}, found {:?}",
                        _pos, other
                    )),
                }
            },
            crate::wpda_runtime::SymbolKind::MixfixMarker => {
                // B7 Pattern 1: inner operand just returned
                // to the mixfix marker. Read marker.bp =
                // index of just-completed inner operand,
                // look up parts metadata, demand the
                // following separator (or fire action on
                // the last operand).
                let result_src_idx = node.symbol.category_src_idx;
                let rule_idx = node.symbol.rule_index_in_category;
                // Stage 3.16 invariant (Cluster 4, Mechanism γ,
                // 2026-05-06): MixfixMarker symbols ALWAYS
                // carry `bp = Some(operands_completed)` per
                // the codegen invariant in
                // StackSymbolV2::mixfix_marker. expect()
                // surfaces invariant violations.
                let completed_idx = node.symbol.bp.expect(
                    "MixfixMarker invariant: bp must be \
                     Some(operands_completed) set at construction",
                );
                // Stage 3.16 invariant (Cluster 4, Mechanism γ,
                // 2026-05-06): mixfix_parts_len returning None
                // means the (result_src_idx, rule_idx) pair
                // is missing from the codegen-time mixfix-parts
                // table — a hard codegen invariant violation,
                // not a parse-time choice. Surface as Error
                // with a precise message instead of silently
                // substituting 0 (which would skip the mixfix
                // dispatch entirely).
                let parts_len = match mixfix_parts_len(result_src_idx, rule_idx) {
                    Some(n) => n,
                    None => {
                        return WpdaStepAction::Error(format!(
                            "mixfix_parts_len(result={}, rule={}) returned None — \
                         codegen invariant violated: every MixfixMarker symbol \
                         must have a mixfix-parts table entry",
                            result_src_idx, rule_idx,
                        ))
                    },
                };
                // L12 follow-up B6 (2026-05-07): widened metadata.
                // mixfix_part returns
                //   Option<(operand_src, &[&str] preceding,
                //                        &[&str] following)>.
                // For traditional Tern-style mixfix the
                // following slice has 0 or 1 element and
                // preceding is empty; the existing single-
                // separator Fork emission below handles
                // those cases by reading following.first().
                // Postfix-mixfix shapes (POutput-class)
                // with multi-element preceding/following
                // are dispatched via the new
                // WpdaState::MixfixLiteralRun state machine
                // (see arm below).
                // L12 follow-up B6 step 3 (2026-05-07):
                // route to MixfixLiteralRun to walk
                // following_terminals + (next operand's)
                // preceding_terminals before deciding
                // whether to Pop or transition to the
                // next operand's CategoryEntry.
                //
                // Single-literal Tern-style mixfix
                // (following.len()==1, preceding.len()==0)
                // walks through MixfixLiteralRun
                // {kind=0, sub_pos=0..=1} with one
                // ConsumeAndReplace per literal —
                // semantically equivalent to the prior
                // single-Consume Fork, but operates on
                // the widened metadata vectors. The G2
                // last-operand-elision path is removed;
                // it can be reintroduced as a Fork
                // option in MixfixLiteralRun's kind=0
                // arm if a future grammar requires it.
                let _ = parts_len; // suppress unused warning
                let _ = mixfix_part; // path used in arm below
                return WpdaStepAction::Advance(WpdaState::MixfixLiteralRun {
                    result_src_idx,
                    rule_idx,
                    completed_idx,
                    kind: 0,
                    sub_pos: 0,
                });
            },
            crate::wpda_runtime::SymbolKind::BinderListLoopAt => {
                // Class-3 binder-list inner ParamParse /
                // Literal / BinderIdent just returned to
                // the binder-list marker. This is
                // intentionally distinct from
                // OptionalGroupAt because rules can contain
                // both a Class-3 binder loop and a real
                // `*opt(...)` whose sub_pos values overlap.
                let marker_id = match node.symbol.traversal_marker_id() {
                    Some(id) => id,
                    None => {
                        return WpdaStepAction::Error(
                            "BinderListLoopAt lacks traversal marker identity".to_string(),
                        )
                    },
                };
                let Some((result_src_idx, rule_idx, frame_idx, sub_pos)) =
                    binder_marker_metadata(marker_id)
                else {
                    return WpdaStepAction::Error(format!(
                        "unknown binder traversal marker {}",
                        marker_id,
                    ));
                };
                let outer_bp = node.symbol.bp.expect(
                    "BinderListLoopAt invariant: bp must be \
                     Some(outer_bp) — preserved across the binder-list walk",
                );
                let new_state = WpdaState::BinderListLoop {
                    result_src_idx,
                    rule_idx,
                    frame_idx,
                    outer_bp,
                    sub_pos,
                };
                // B8 / Issue C (2026-05-09): when the
                // just-completed inner step was a
                // ParamParse{collection:Some}, splice
                // the parsed term into the Names
                // accumulator.
                let splice_id: Option<u8> =
                    binderlist_inner_post_splice(result_src_idx, rule_idx, frame_idx, sub_pos);
                if let Some(id) = splice_id {
                    return WpdaStepAction::AdvanceWithEffect {
                        new_state,
                        effect: crate::wpda_walker::BuilderDelta::SpliceIntoCollection { id },
                    };
                }
                return WpdaStepAction::Advance(new_state);
            },
            crate::wpda_runtime::SymbolKind::OptionalGroupAt => {
                // Opt-Group: inner ParamParse / Literal /
                // BinderIdent / GuardSlot just returned to
                // a real optional-group marker.
                let marker_id = match node.symbol.traversal_marker_id() {
                    Some(id) => id,
                    None => {
                        return WpdaStepAction::Error(
                            "OptionalGroupAt lacks traversal marker identity".to_string(),
                        )
                    },
                };
                let Some((result_src_idx, rule_idx, group_idx, sub_pos)) =
                    optional_marker_metadata(marker_id)
                else {
                    return WpdaStepAction::Error(format!(
                        "unknown optional traversal marker {}",
                        marker_id,
                    ));
                };
                let outer_bp = node.symbol.bp.expect(
                    "OptionalGroupAt invariant: bp must be \
                     Some(outer_bp) — preserved across the group",
                );
                return WpdaStepAction::Advance(WpdaState::OptionalGroup {
                    result_src_idx,
                    rule_idx,
                    group_idx,
                    sub_pos,
                    outer_bp,
                });
            },
            other => WpdaStepAction::Error(format!(
                "Unwinding: unrecognized symbol kind {:?} at pos {} \
                 (expected CollectionMarker / RuleAt / GroupingMarker / \
                 MixfixMarker / OptionalGroupAt / BinderListLoopAt) — codegen invariant violated",
                other, _pos,
            )),
        }
    } else {
        WpdaStepAction::Accept
    }
}
