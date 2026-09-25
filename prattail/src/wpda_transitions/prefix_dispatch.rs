//! Original PrefixDispatch observations and recovery body from engine_impl.rs at cc139b1c.
//!
//! Lexical dispatch runs first. A returned action skips all later observations;
//! fallthrough continues with the same token source and callback state. Both
//! collection-spec lookups, repeated token reads, short-circuit predicates, and
//! close/redirect/empty branch order are retained. The final callback contains
//! the original generated grouping, collection, and category match arms.
//! Recovery retains the active configuration lookup, cache attempt, and uncached
//! fallback. No callback is replayed to reconstruct an earlier observation.
//!
//! Source obligations: TransitionBodyRelocation.v's unchanged-body and observed
//! state continuation laws; no equality of different readers/weights is assumed.

use crate::automata::lex_weight::LexicographicWeight;
use crate::automata::semiring::SemiringRef;
use crate::automata::TokenKind;
use crate::gss::{WpdaGss, WpdaGssNode};
use crate::recovery_dispatch::RecoveryInfra;
use crate::wpda_runtime::{CollectionSpec, StackSymbolV2, WpdaState, WpdaTokenSource};
use crate::wpda_walker::WpdaStepAction;

#[allow(clippy::too_many_arguments)]
pub fn prefix_dispatch<W: SemiringRef>(
    primary_src_idx: u16,
    pos: &usize,
    cur_bp: &u8,
    frontier_top: Option<&WpdaGssNode>,
    tokens: &dyn WpdaTokenSource,
    lex_fork: impl FnOnce() -> Option<WpdaStepAction<W>>,
    mut lookup_collection_spec: impl FnMut(u16, u16, u8) -> Option<CollectionSpec>,
    mut collection_element_can_start: impl FnMut(u16, &TokenKind) -> bool,
    mut lex_w: impl FnMut(f64, u16, u16) -> W,
    dispatch: impl FnOnce(u16, u8, Option<TokenKind>) -> WpdaStepAction<W>,
) -> WpdaStepAction<W> {
    // L-substrate Piece #6 (2026-05-13): lex-fork
    // dispatch BEFORE any other PrefixDispatch
    // logic. Emits a Fork over `peek_alternatives(*pos)`
    // when the active token source detected lex
    // ambiguity (multi-length-accept points along
    // the DFA walk — e.g., for input `-3` the
    // scanner visits both `Minus@end=1` and
    // `Integer@end=2`, surfacing as 2 alternatives
    // in `entries[0]`). The default
    // `SliceTokenSource::peek_alternatives` returns
    // `&[]` so this dispatch is inert without a
    // `MutableMultiTokenSource` attached (Pieces
    // #3/#7 facade glue gates the source
    // selection).
    if let Some(__action) = lex_fork() {
        return __action;
    }
    // Stage 3.16 invariant (Cluster 1, Mechanism γ,
    // 2026-05-05): Fork over close + cross-cat-redirect
    // branches. For shipped grammars the conditions
    // are mutually-exclusive on token (the Fork
    // degenerates to one surviving cursor — the other
    // drops via Idle on its next step). For G3-style
    // future grammars where the close-token equals an
    // element-start token, lex-min + source-order
    // tiebreak picks close (branch_idx 0 < redirect's
    // branch_idx 1; weight 0.0 < SKIP_BIAS).
    //
    // Walker companion: the apply_action::Fork dispatch
    // (wpda_walker.rs:2188) transfers the live builder's
    // open collection_stack to the parent cursor on
    // Lazy→Strict promotion, fixing the LIFO invariant
    // for empty cross-cat collections. See
    // `feedback_use_wpds_disambiguation_not_heuristics.md`.
    if let Some(node) = frontier_top {
        if node.symbol.kind == crate::wpda_runtime::SymbolKind::CollectionMarker {
            let result_src_idx = node.symbol.category_src_idx;
            let rule_idx = node.symbol.rule_index_in_category;
            // Phase 4 #1.B (2026-05-11): the
            // CollectionMarker's `bp` field carries
            // the slot identifier. For Class-5
            // collection rules and Phase-4-#1's
            // top-level Class-2 multi-slot rules
            // (no outer collection nesting), the
            // marker bp is the codegen-stamped slot_idx;
            // runtime accumulator ids flow separately
            // through the CollectionId action argument.
            let slot_idx = node.symbol.bp.unwrap_or(0u8);
            let collection_spec = lookup_collection_spec(result_src_idx, rule_idx, slot_idx);
            let close_lookup: Option<&'static str> = collection_spec.map(|__s| __s.close);
            let token_text = tokens.peek_text(*pos).unwrap_or("");
            // #307 ROOT-F G1 site-2 (2026-06-11): the
            // empty-collection close detection is edge
            // MEMBERSHIP (primary + alternatives), not
            // primary-only text equality (the ROOT-A
            // primary_equality_loses trap — live for
            // multi-char closes like the Bag "}#").
            let token_is_close = close_lookup.is_some_and(|cl| {
                !cl.is_empty()
                    && (token_text == cl || {
                        tokens.peek_alternatives(*pos).iter().any(|a| a.text == cl)
                    })
            });
            let element_src_lookup: Option<u16> =
                lookup_collection_spec(result_src_idx, rule_idx, slot_idx)
                    .and_then(|__s| __s.element_src_idx);
            let redirect_src_idx = element_src_lookup.filter(|&esi| esi != result_src_idx);
            let element_can_start = element_src_lookup.is_some_and(|esi| {
                tokens
                    .peek_kind(*pos)
                    .as_ref()
                    .is_some_and(|kind| collection_element_can_start(esi, kind))
                    || tokens
                        .peek_alternatives(*pos)
                        .iter()
                        .any(|alternative| collection_element_can_start(esi, &alternative.kind))
            });
            let can_stop_empty =
                collection_spec.is_some_and(|spec| spec.close.is_empty() && spec.min_elements == 0);
            let redirect_should_parse =
                redirect_src_idx.is_some() && (!can_stop_empty || element_can_start);
            if token_is_close || redirect_should_parse || can_stop_empty {
                let mut __branches: Vec<crate::wpda_walker::ForkBranch<W>> = Vec::with_capacity(2);
                if token_is_close {
                    // #307 ROOT-F G1 site-2: one
                    // ConsumeAtAndPop per matched close
                    // edge (deduped by target), never the
                    // alt-0 ConsumeAndPop advance.
                    let cl = close_lookup.unwrap_or("");
                    let mut __targets: Vec<usize> = Vec::with_capacity(2);
                    if token_text == cl {
                        if let Some(np) = tokens.next_pos(*pos, 0) {
                            __targets.push(np);
                        }
                    }
                    for (__i, __alt) in tokens.peek_alternatives(*pos).iter().enumerate() {
                        if __alt.text == cl {
                            if let Some(np) = tokens.next_pos(*pos, __i + 1) {
                                if !__targets.contains(&np) {
                                    __targets.push(np);
                                }
                            }
                        }
                    }
                    for np in __targets {
                        __branches.push(crate::wpda_walker::ForkBranch {
                            symbol: StackSymbolV2::category_entry(0),
                            weight: lex_w(0.0, result_src_idx, rule_idx),
                            new_state: WpdaState::Unwinding,
                            action_kind: crate::wpda_walker::ForkActionKind::ConsumeAtAndPop {
                                next_pos: np,
                            },
                        });
                    }
                }
                if let Some(element_src_idx) = redirect_src_idx {
                    if !can_stop_empty || element_can_start {
                        __branches.push(crate::wpda_walker::ForkBranch {
                            // GEN-1 goal-gate G2 (2026-06-28):
                            // strict GOAL = the collection
                            // element's category. For a
                            // polyadic bind `a,b,c <- x`
                            // (Vec<Name> elements, result
                            // InputBind) each element parses
                            // with goal=Name, so the
                            // InputBindPolyadic `,`
                            // (Name→InputBind) is dropped and
                            // the CollectionLoop owns the
                            // separator — enabling 3+ elems.
                            symbol: StackSymbolV2::category_entry_goal(element_src_idx),
                            weight: lex_w(
                                crate::automata::lex_weight::EPSILON_OPT_SKIP,
                                result_src_idx,
                                rule_idx,
                            ),
                            new_state: WpdaState::PrefixDispatch { pos: *pos, cur_bp: *cur_bp },
                            action_kind: crate::wpda_walker::ForkActionKind::Push,
                        });
                    }
                }
                if can_stop_empty
                    && redirect_src_idx.is_none()
                    && element_src_lookup.is_some()
                    && element_can_start
                {
                    let element_src_idx = element_src_lookup.unwrap_or(0);
                    __branches.push(crate::wpda_walker::ForkBranch {
                        symbol: StackSymbolV2::category_entry_goal(element_src_idx),
                        weight: lex_w(
                            crate::automata::lex_weight::EPSILON_OPT_SKIP,
                            result_src_idx,
                            rule_idx,
                        ),
                        new_state: WpdaState::PrefixDispatch { pos: *pos, cur_bp: *cur_bp },
                        action_kind: crate::wpda_walker::ForkActionKind::Push,
                    });
                }
                if can_stop_empty {
                    let resumes_via_unwinding =
                        collection_spec.is_some_and(|spec| spec.close_resumes_via_unwinding);
                    __branches.push(crate::wpda_walker::ForkBranch {
                        symbol: StackSymbolV2::category_entry(0),
                        weight: lex_w(0.0, result_src_idx, rule_idx),
                        new_state: if resumes_via_unwinding {
                            WpdaState::Unwinding
                        } else {
                            WpdaState::InfixLoop { cur_bp: *cur_bp }
                        },
                        action_kind: crate::wpda_walker::ForkActionKind::Pop,
                    });
                }
                return WpdaStepAction::Fork {
                    branches: __branches,
                    consume_trigger: false,
                };
            }
        }
    }
    // Phase A.2: dispatch on the current category (derived
    // from the frontier top's src_idx) and the peek'd token.
    let state_cat_src_idx: u16 = frontier_top
        .map(|n| n.symbol.category_src_idx)
        .unwrap_or(primary_src_idx);
    let _outer_bp: u8 = *cur_bp;
    let peek = tokens.peek_kind(*pos);
    let _ = frontier_top; // suppress unused warning
    dispatch(state_cat_src_idx, _outer_bp, peek)
}

pub fn recover<'a, W>(
    _gss: &WpdaGss<W>,
    frontier_top: Option<&WpdaGssNode>,
    pos: &usize,
    cur_bp: &u8,
    state_cat_src_idx: u16,
    tokens: &dyn WpdaTokenSource,
    recovery_infra_for: impl FnOnce(u16) -> Option<&'a RecoveryInfra>,
) -> WpdaStepAction<W>
where
    W: SemiringRef + Clone + From<LexicographicWeight>,
{
    match recovery_infra_for(state_cat_src_idx) {
        Some(infra) => {
            let active_recovery_config =
                crate::recovery_cohort::with_active_recovery_config(|config| config.clone());
            let recovery_config = active_recovery_config.as_ref().unwrap_or(&infra.config);
            // Phase F.13 Task #117 (2026-05-23):
            // try cohort-cached path first via
            // the walker's pinned TLS pointer.
            // Falls through to the uncached path
            // when the cache pointer is null
            // (engine.step called outside a
            // walker parse loop).
            let cached: Option<crate::wpda_walker::WpdaStepAction<W>> =
                crate::recovery_cohort::with_active_cache_typed::<W, _, _>(|cache| {
                    let view = crate::recovery_dispatch::WalkerRuntimeView::new(
                        _gss,
                        frontier_top,
                        *pos,
                        state_cat_src_idx,
                        *cur_bp,
                    );
                    crate::recovery_dispatch::emit_recovery_fork_cached_with_config(
                        view,
                        tokens,
                        infra,
                        recovery_config,
                        cache,
                    )
                });
            match cached {
                Some(action) => action,
                None => {
                    let view = crate::recovery_dispatch::WalkerRuntimeView::new(
                        _gss,
                        frontier_top,
                        *pos,
                        state_cat_src_idx,
                        *cur_bp,
                    );
                    crate::recovery_dispatch::emit_recovery_fork_with_config(
                        view,
                        tokens,
                        infra,
                        recovery_config,
                    )
                },
            }
        },
        None => WpdaStepAction::Error(format!(
            "no recovery infra for category src_idx {} at pos {} — \
             codegen invariant violated (recovery_infra_for is exhaustive)",
            state_cat_src_idx, *pos,
        )),
    }
}
