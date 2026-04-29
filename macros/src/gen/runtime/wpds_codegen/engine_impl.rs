//! Emits the per-language `impl WpdsStepEngine` body.
//!
//! Covers all WpdsState dispatch: Ready → PrefixDispatch seed, prefix arms
//! per atomic/binder/cross-cat rule, InfixLoop with Pratt BP, CollectionLoop
//! for sep/close, BinderRule per-position dispatch, CrossCatDelegate for
//! cross-cat projections, Unwinding for Pop chains, terminal Accepted/Error.
//! AmbiguityFanout is `unreachable!` — the walker drives it via `step_fanout`,
//! never `engine.step`.

use mettail_ast::grammar::GrammarRule;
use mettail_ast::language::LanguageDef;
use proc_macro2::{Ident, TokenStream};
use quote::quote;

use super::{prefix, semantic_actions};

/// Emit the `impl WpdsStepEngine<LexicographicWeight> for <engine_ident>`
/// block, including Phase A.2 prefix-dispatch arms and the `action_for`
/// semantic action lookup.
///
/// `per_cat` is the pre-built combined user + synthetic rule list per
/// category (see `synthetic::build_per_category_rules`). Each rule's
/// index in its per-category Vec is its stable `rule_idx`.
pub(crate) fn emit_engine_impl_full(
    engine_ident: &Ident,
    language: &LanguageDef,
    categories: &[String],
    per_cat: &[Vec<GrammarRule>],
    primary_src_idx: u16,
) -> TokenStream {
    // Build the indexed view expected by prefix/semantic_actions.
    let per_cat_indexed: Vec<Vec<(u16, &GrammarRule)>> = per_cat
        .iter()
        .map(|rules| {
            rules
                .iter()
                .enumerate()
                .map(|(i, r)| (i as u16, r))
                .collect()
        })
        .collect();

    // Aggregate Phase A.2 prefix arms across all categories. Each arm
    // guards on `state_cat_src_idx` so the same token can produce
    // different AST depending on which category is being parsed.
    let mut all_prefix_arms = TokenStream::new();
    for (i, rules) in per_cat_indexed.iter().enumerate() {
        let arms = prefix::emit_prefix_arms_for_category(
            language,
            i as u16,
            categories.get(i).map(String::as_str).unwrap_or(""),
            rules,
        );
        all_prefix_arms.extend(arms);
    }
    // Phase 4: prepend collection open-delimiter arms so they run before
    // generic prefix arms. Open delimiters are typically `Fixed("{")` /
    // `Fixed("[")` which are unambiguous in PrefixDispatch context.
    let collection_arms =
        super::collection::emit_collection_prefix_arms(language, categories, per_cat);
    // Phase 4: CollectionLoop arm body, close-lookup for empty-collection
    // bootstrap, and element_src_idx lookup for Unwinding-CollectionMarker.
    let collection_loop_body =
        super::collection::emit_collection_loop_arm(language, categories, per_cat);
    let collection_close_lookup =
        super::collection::emit_collection_close_lookup(language, per_cat);
    let collection_element_src_lookup =
        super::collection::emit_collection_element_src_lookup(language, categories, per_cat);
    // Phase 5: binder rule prefix arms (recognize trigger literal of binder
    // rules) + BinderRule state body (multi-step state machine per rule).
    let binder_arms = super::binder::emit_binder_prefix_arms(language, categories, per_cat);
    let binder_rule_body = super::binder::emit_binder_rule_body(categories, per_cat);
    // Phase 5b: BinderListLoop body for multi-binder list (^[xs]).
    let binder_list_loop_body = super::binder::emit_binder_list_loop_body(per_cat);
    // Opt-Group (2026-04-29): per-rule per-group OptionalGroup state
    // dispatch — FIRST-set peek + inner-position walk + finalize.
    let optional_group_body =
        super::binder::emit_optional_group_body(categories, per_cat);
    // B7 Pattern 2: paren-grouping arms in PrefixDispatch — backend
    // emission of `(`-grouping for every parseable category, satisfying
    // the user mandate "no per-grammar order; backend change". Emitted
    // BEFORE generic prefix_arms so `(` matches grouping rather than
    // any rule that happens to start with `(`.
    let grouping_arms = super::prefix::emit_grouping_arms(categories);

    let action_for_body =
        semantic_actions::emit_action_for_body(language, categories, &per_cat_indexed);

    // Phase 3: InfixLoop dispatch arm. Per-category match on
    // `state_cat_src_idx` calling the emitted `infix_bp_<cat>` lookup
    // helpers.
    let infix_loop_dispatch = emit_infix_loop_dispatch(categories);
    let postfix_dispatch = emit_postfix_dispatch(categories);
    let mixfix_dispatch = emit_mixfix_dispatch(categories);

    quote! {
        impl mettail_prattail::wpds_walker::WpdsStepEngine<
            mettail_prattail::automata::lex_weight::LexicographicWeight,
        > for #engine_ident
        {
            fn step(
                &self,
                state: &mettail_prattail::wpds_runtime::WpdsState,
                _gss: &mettail_prattail::gss::WpdsGss<
                    mettail_prattail::automata::lex_weight::LexicographicWeight,
                >,
                frontier_top: Option<&mettail_prattail::gss::WpdsGssNode>,
                _pos: usize,
                tokens: &dyn mettail_prattail::wpds_runtime::WpdsTokenSource,
            ) -> mettail_prattail::wpds_walker::WpdsStepAction<
                mettail_prattail::automata::lex_weight::LexicographicWeight,
            > {
                use mettail_prattail::wpds_runtime::{
                    StackSymbolV2, WpdsState,
                };
                use mettail_prattail::wpds_walker::WpdsStepAction;
                use mettail_prattail::automata::lex_weight::LexicographicWeight;
                use mettail_prattail::automata::semiring::Semiring;

                match state {
                    WpdsState::Ready { min_bp } => {
                        let primary = StackSymbolV2::category_entry(#primary_src_idx);
                        WpdsStepAction::Push {
                            symbol: primary,
                            weight: LexicographicWeight::from_cost(0.0, #primary_src_idx, 0),
                            new_state: WpdsState::PrefixDispatch {
                                pos: 0,
                                cur_bp: *min_bp,
                            },
                        }
                    }
                    WpdsState::PrefixDispatch { pos, cur_bp } => {
                        // Phase 4: empty-collection bootstrap. If frontier_top
                        // is a CollectionMarker AND the next token is the
                        // close delim, emit ConsumeAndPop directly so the
                        // empty-collection finalize action fires.
                        if let Some(node) = frontier_top {
                            if node.symbol.kind
                                == mettail_prattail::wpds_runtime::SymbolKind::CollectionMarker
                            {
                                let result_src_idx = node.symbol.category_src_idx;
                                let rule_idx = node.symbol.rule_index_in_category;
                                let close_lookup: Option<&'static str> = #collection_close_lookup;
                                let token_text = tokens.peek_text(*pos).unwrap_or("");
                                if Some(token_text) == close_lookup {
                                    return WpdsStepAction::ConsumeAndPop {
                                        weight: LexicographicWeight::from_cost(
                                            0.0, result_src_idx, rule_idx,
                                        ),
                                        new_state: WpdsState::Unwinding,
                                    };
                                }
                                // B7 cross-cat element redirect: when
                                // element_src_idx ≠ result_src_idx, the
                                // result category's prefix arms cannot
                                // match the element token (e.g. List's
                                // arms won't match a Proc literal). Push
                                // CategoryEntry(element_src) on top so
                                // dispatch routes to the element category.
                                let element_src_lookup: Option<u16> = {
                                    let result_src_idx = result_src_idx;
                                    let rule_idx = rule_idx;
                                    #collection_element_src_lookup
                                };
                                if let Some(element_src_idx) = element_src_lookup {
                                    if element_src_idx != result_src_idx {
                                        return WpdsStepAction::Push {
                                            symbol: StackSymbolV2::category_entry(
                                                element_src_idx,
                                            ),
                                            weight: LexicographicWeight::one(),
                                            new_state: WpdsState::PrefixDispatch {
                                                pos: *pos,
                                                cur_bp: *cur_bp,
                                            },
                                        };
                                    }
                                }
                            }
                        }
                        // Phase A.2: dispatch on the current category (derived
                        // from the frontier top's src_idx) and the peek'd token.
                        let state_cat_src_idx: u16 = frontier_top
                            .map(|n| n.symbol.category_src_idx)
                            .unwrap_or(#primary_src_idx);
                        let _outer_bp: u8 = *cur_bp;
                        let peek = tokens.peek_kind(*pos);
                        let _ = frontier_top; // suppress unused warning
                        match peek {
                            // B7 Pattern 2: paren-grouping `(` arms — match
                            // first so `(` doesn't fall through to a rule's
                            // `(`-prefixed pattern (none exist in shipped
                            // grammars; the synthetic-collection paren is
                            // consumed via CollectionOpenParen, never here).
                            #grouping_arms
                            // Phase 4: collection open-delim arms run before
                            // generic prefix arms. Open delimiters are
                            // typically `Fixed("{")` / `Fixed("[")` /
                            // `Fixed("list")` — unambiguous in PrefixDispatch
                            // context.
                            #collection_arms
                            // Phase 5: binder-rule trigger-literal arms.
                            #binder_arms
                            #all_prefix_arms
                            _ => WpdsStepAction::Idle,
                        }
                    }
                    WpdsState::Unwinding => {
                        if let Some(node) = frontier_top {
                            match node.symbol.kind {
                                mettail_prattail::wpds_runtime::SymbolKind::Return => {
                                    // After a Return pop, transition to InfixLoop
                                    // with cur_bp = the bp encoded in the popped
                                    // symbol. The Return's bp was set at
                                    // ConsumeAndPush time to the outer cur_bp.
                                    let outer_bp = node.symbol.bp.unwrap_or(0);
                                    WpdsStepAction::Pop {
                                        weight: LexicographicWeight::one(),
                                        new_state: WpdsState::InfixLoop { cur_bp: outer_bp },
                                    }
                                }
                                mettail_prattail::wpds_runtime::SymbolKind::CategoryEntry => {
                                    // Phase 5 fix: pop CategoryEntry, but stay
                                    // in Unwinding so we continue unwinding into
                                    // any enclosing markers (binder rule_at,
                                    // collection marker). When the GSS is fully
                                    // unwound, frontier_top is None and the
                                    // outer Unwinding arm emits Accept.
                                    WpdsStepAction::Pop {
                                        weight: LexicographicWeight::one(),
                                        new_state: WpdsState::Unwinding,
                                    }
                                }
                                mettail_prattail::wpds_runtime::SymbolKind::CollectionMarker => {
                                    // Phase 4: just unwound to a marker (i.e., an
                                    // element just returned). Transition to
                                    // CollectionLoop to dispatch on close/sep.
                                    let result_src_idx = node.symbol.category_src_idx;
                                    let rule_idx = node.symbol.rule_index_in_category;
                                    let accumulator_id = node.symbol.bp.unwrap_or(0);
                                    let element_src_lookup: Option<u16> = {
                                        let result_src_idx = result_src_idx;
                                        let rule_idx = rule_idx;
                                        #collection_element_src_lookup
                                    };
                                    let element_src_idx = element_src_lookup.unwrap_or(result_src_idx);
                                    WpdsStepAction::Advance(WpdsState::CollectionLoop {
                                        result_src_idx,
                                        rule_idx,
                                        element_src_idx,
                                        outer_bp: 0,
                                        accumulator_id,
                                    })
                                }
                                mettail_prattail::wpds_runtime::SymbolKind::RuleAt(position) => {
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
                                    WpdsStepAction::Advance(WpdsState::BinderRule {
                                        result_src_idx,
                                        rule_idx,
                                        body_src_idx: 0u16,
                                        outer_bp,
                                    })
                                }
                                mettail_prattail::wpds_runtime::SymbolKind::GroupingMarker => {
                                    // B7 Pattern 2: inner expression of a
                                    // grouping just returned. Demand the
                                    // closing `)`, ConsumeAndPop the marker,
                                    // and resume InfixLoop at the saved outer
                                    // cur_bp so surrounding operators continue
                                    // at the original precedence. The marker
                                    // is transparent (no AST node, no action);
                                    // the inner Term remains on the builder
                                    // as the result.
                                    let outer_bp = node.symbol.bp.unwrap_or(0);
                                    match tokens.peek_text(_pos) {
                                        Some(")") => WpdsStepAction::ConsumeAndPop {
                                            weight: LexicographicWeight::one(),
                                            new_state: WpdsState::InfixLoop {
                                                cur_bp: outer_bp,
                                            },
                                        },
                                        other => WpdsStepAction::Error(format!(
                                            "expected `)` to close grouping at pos {}, found {:?}",
                                            _pos, other
                                        )),
                                    }
                                }
                                mettail_prattail::wpds_runtime::SymbolKind::MixfixMarker => {
                                    // B7 Pattern 1: inner operand just returned
                                    // to the mixfix marker. Read marker.bp =
                                    // index of just-completed inner operand,
                                    // look up parts metadata, demand the
                                    // following separator (or fire action on
                                    // the last operand).
                                    let result_src_idx = node.symbol.category_src_idx;
                                    let rule_idx = node.symbol.rule_index_in_category;
                                    let completed_idx = node.symbol.bp.unwrap_or(0);
                                    let parts_len = mixfix_parts_len(
                                        result_src_idx, rule_idx,
                                    ).unwrap_or(0);
                                    let part = mixfix_part(
                                        result_src_idx, rule_idx, completed_idx,
                                    );
                                    let following = part.and_then(|(_, t)| t);
                                    if completed_idx + 1 == parts_len {
                                        // Last inner operand: pop the marker
                                        // (auto-fires the rule's action with
                                        // arity 1+parts.len) and resume the
                                        // outer InfixLoop. outer_bp=0 is a
                                        // pragmatic choice for top-level
                                        // mixfix; if a future grammar nests
                                        // mixfix inside a precedenced context,
                                        // thread outer_bp via a dedicated
                                        // marker field or state variant.
                                        return WpdsStepAction::Pop {
                                            weight: LexicographicWeight::one(),
                                            new_state: WpdsState::InfixLoop { cur_bp: 0 },
                                        };
                                    }
                                    // Not the last: demand the separator,
                                    // consume it, then transition to
                                    // MixfixContinuation which will
                                    // ReplaceAndPush the next operand entry.
                                    match (following, tokens.peek_text(_pos)) {
                                        (Some(t), Some(actual)) if actual == t => {
                                            WpdsStepAction::Consume {
                                                weight: LexicographicWeight::one(),
                                                new_state: WpdsState::MixfixContinuation {
                                                    result_src_idx,
                                                    rule_idx,
                                                    completed_idx: completed_idx + 1,
                                                },
                                            }
                                        }
                                        (Some(t), other) => WpdsStepAction::Error(format!(
                                            "expected `{}` separator in mixfix at pos {}, found {:?}",
                                            t, _pos, other
                                        )),
                                        (None, _) => {
                                            // Inner operand without trailing
                                            // separator and not the last —
                                            // codegen invariant violation.
                                            WpdsStepAction::Error(format!(
                                                "mixfix part {} for (result={}, rule={}) has no following terminal but isn't last (parts_len={})",
                                                completed_idx, result_src_idx, rule_idx, parts_len
                                            ))
                                        }
                                    }
                                }
                                mettail_prattail::wpds_runtime::SymbolKind::OptionalGroupAt(sub_pos) => {
                                    // Opt-Group: inner ParamParse / Literal /
                                    // BinderIdent / GuardSlot just returned to
                                    // the optional-group marker. The marker's
                                    // sub_pos was advanced when the inner step
                                    // executed (Replace/ConsumeAndReplace set
                                    // OptionalGroupAt(next_sub_pos)). Resume
                                    // the OptionalGroup state at that sub_pos.
                                    let result_src_idx = node.symbol.category_src_idx;
                                    let rule_idx = node.symbol.rule_index_in_category;
                                    let outer_bp = node.symbol.bp.unwrap_or(0);
                                    return WpdsStepAction::Advance(
                                        WpdsState::OptionalGroup {
                                            result_src_idx,
                                            rule_idx,
                                            // group_idx isn't carried in the
                                            // marker (the synthetic
                                            // dispatch keys on (result, rule,
                                            // group, sub_pos) but only one
                                            // OptionalGroup can be live at any
                                            // outer position). For pilot
                                            // grammars with a single group per
                                            // rule, group_idx=0; for
                                            // multi-group rules the body
                                            // dispatcher resolves group_idx
                                            // from sub_pos via the per-rule
                                            // table.
                                            group_idx: 0,
                                            sub_pos,
                                            outer_bp,
                                        },
                                    );
                                }
                                _ => WpdsStepAction::Idle,
                            }
                        } else {
                            WpdsStepAction::Accept
                        }
                    }
                    WpdsState::InfixLoop { cur_bp } => {
                        // Phase 4/5/B7: if frontier_top is a marker symbol
                        // (CollectionMarker / RuleAt / MixfixMarker), skip
                        // infix dispatch and fall through to Unwinding. Each
                        // marker has its own Unwinding handler.
                        if let Some(node) = frontier_top {
                            match node.symbol.kind {
                                mettail_prattail::wpds_runtime::SymbolKind::CollectionMarker
                                | mettail_prattail::wpds_runtime::SymbolKind::RuleAt(_)
                                | mettail_prattail::wpds_runtime::SymbolKind::MixfixMarker
                                | mettail_prattail::wpds_runtime::SymbolKind::OptionalGroupAt(_) => {
                                    // Opt-Group: an OptionalGroupAt marker
                                    // indicates we're mid-group; defer to
                                    // Unwinding so the OptionalGroup state
                                    // resumes at the recorded sub_pos.
                                    return WpdsStepAction::Advance(WpdsState::Unwinding);
                                }
                                _ => {}
                            }
                        }
                        // Phase 3: peek for an infix or postfix operator on
                        // the current category. If the operator's left_bp >=
                        // cur_bp, consume the token and push an
                        // InfixContinuation Return (rule_idx targets the
                        // operator's arity-2 action). Otherwise fall through
                        // to Unwinding to pop the next frame.
                        let state_cat_src_idx: u16 = frontier_top
                            .map(|n| n.symbol.category_src_idx)
                            .unwrap_or(#primary_src_idx);
                        let token_text = tokens.peek_text(_pos).unwrap_or("");
                        // Try infix.
                        if let Some((l_bp, r_bp, result_src, rule_idx)) =
                            #infix_loop_dispatch
                        {
                            if l_bp >= *cur_bp {
                                // Stage 1.2: cross-category infix (operand_cat ≠ result_cat,
                                // e.g. EqInt: Int×Int→Bool). Push Return marker carrying
                                // result_cat (so action_for dispatches to result_cat's
                                // wrapper), then transition to CrossCatDelegate which
                                // pushes a CategoryEntry for the operand_cat so the RHS
                                // sub-parse runs against operand rules. After RHS returns,
                                // the cross-cat Return pops and its arity-2 action fires.
                                let new_state =
                                    if result_src != state_cat_src_idx {
                                        WpdsState::CrossCatDelegate {
                                            source_src_idx: state_cat_src_idx,
                                            outer_bp: r_bp,
                                        }
                                    } else {
                                        WpdsState::PrefixDispatch {
                                            pos: _pos + 1,
                                            cur_bp: r_bp,
                                        }
                                    };
                                return WpdsStepAction::ConsumeAndPush {
                                    symbol: StackSymbolV2::rule_at(
                                        result_src, rule_idx, 0, Some(*cur_bp),
                                    )
                                    .with_kind_return(),
                                    weight: LexicographicWeight::from_cost(
                                        0.0, result_src, rule_idx,
                                    ),
                                    new_state,
                                    // Infix operator token isn't pushed to
                                    // builder — only LHS+RHS terms.
                                    capture_token: false,
                                };
                            }
                        }
                        // Try postfix.
                        if let Some((l_bp, result_src, rule_idx)) =
                            #postfix_dispatch
                        {
                            if l_bp >= *cur_bp {
                                return WpdsStepAction::ConsumeAndPush {
                                    symbol: StackSymbolV2::rule_at(
                                        result_src, rule_idx, 0, Some(*cur_bp),
                                    )
                                    .with_kind_return(),
                                    weight: LexicographicWeight::from_cost(
                                        0.0, result_src, rule_idx,
                                    ),
                                    new_state: WpdsState::InfixLoop { cur_bp: *cur_bp },
                                    capture_token: false,
                                };
                            }
                        }
                        // B7 Pattern 1: try mixfix. Mixfix triggers (e.g.
                        // ternary `?`) consume the trigger token, push a
                        // MixfixMarker (auto-fire on final pop), and
                        // transition to PrefixDispatch{cur_bp:0} to parse
                        // the first inner operand. Subsequent operands and
                        // separators are driven by Unwinding-MixfixMarker
                        // and MixfixContinuation.
                        if let Some((l_bp, result_src, rule_idx)) =
                            #mixfix_dispatch
                        {
                            if l_bp >= *cur_bp {
                                return WpdsStepAction::ConsumeAndPush {
                                    symbol: StackSymbolV2::mixfix_marker(
                                        result_src, rule_idx, 0,
                                    ),
                                    weight: LexicographicWeight::from_cost(
                                        0.0, result_src, rule_idx,
                                    ),
                                    new_state: WpdsState::PrefixDispatch {
                                        pos: _pos + 1,
                                        cur_bp: 0,
                                    },
                                    capture_token: false,
                                };
                            }
                        }
                        // No operator matched — fall through to Unwinding.
                        WpdsStepAction::Advance(WpdsState::Unwinding)
                    }
                    WpdsState::CollectionLoop {
                        result_src_idx,
                        rule_idx,
                        element_src_idx: _element_src_idx,
                        outer_bp: _outer_bp,
                        accumulator_id: _accumulator_id,
                    } => {
                        // Phase 4: dispatch on close / sep / element.
                        #collection_loop_body
                    }
                    WpdsState::MixfixContinuation {
                        result_src_idx,
                        rule_idx,
                        completed_idx,
                    } => {
                        // B7 Pattern 1: between-operand transition. The
                        // separator was consumed in Unwinding-MixfixMarker;
                        // now ReplaceAndPush so the marker's bp updates to
                        // `completed_idx` (= next operand index) AND a new
                        // CategoryEntry(operand_src_idx) goes on top to
                        // route the sub-parse to the correct element cat.
                        match mixfix_part(*result_src_idx, *rule_idx, *completed_idx) {
                            Some((operand_src_idx, _following)) => {
                                WpdsStepAction::ReplaceAndPush {
                                    replace_symbol: StackSymbolV2::mixfix_marker(
                                        *result_src_idx,
                                        *rule_idx,
                                        *completed_idx,
                                    ),
                                    push_symbol: StackSymbolV2::category_entry(
                                        operand_src_idx,
                                    ),
                                    weight: LexicographicWeight::one(),
                                    new_state: WpdsState::PrefixDispatch {
                                        pos: _pos,
                                        cur_bp: 0,
                                    },
                                }
                            }
                            None => WpdsStepAction::Error(format!(
                                "mixfix part {} not found for (result={}, rule={})",
                                completed_idx, result_src_idx, rule_idx
                            )),
                        }
                    }
                    WpdsState::CollectionOpenParen {
                        result_src_idx,
                        rule_idx,
                        element_src_idx,
                        outer_bp,
                    } => {
                        // B7: 2-token open delimiter — the prefix arm
                        // already consumed `list` (or `bag` / `map`) and
                        // pushed the CollectionMarker. Demand `(` next,
                        // consume it, and transition to PrefixDispatch
                        // with the CollectionMarker still on top.
                        // PrefixDispatch then handles three sub-cases:
                        //   (a) empty-collection — peek == close delim →
                        //       ConsumeAndPop (existing close_lookup path);
                        //   (b) cross-cat element (result_src ≠ element_src)
                        //       → Push CategoryEntry(element_src) and
                        //       recurse PrefixDispatch (handled in
                        //       PrefixDispatch's CollectionMarker branch);
                        //   (c) self-collection — fall through to normal
                        //       per-category prefix dispatch.
                        let _ = (result_src_idx, rule_idx, element_src_idx, outer_bp);
                        match tokens.peek_text(_pos) {
                            Some("(") => WpdsStepAction::Consume {
                                weight: LexicographicWeight::one(),
                                new_state: WpdsState::PrefixDispatch {
                                    pos: _pos + 1,
                                    cur_bp: 0,
                                },
                            },
                            other => WpdsStepAction::Error(format!(
                                "expected `(` after collection-open keyword at pos {}, found {:?}",
                                _pos, other
                            )),
                        }
                    }
                    WpdsState::BinderRule {
                        result_src_idx,
                        rule_idx,
                        body_src_idx: _body_src_idx,
                        outer_bp,
                    } => {
                        // Phase 5: per-position dispatch for binder rules.
                        #binder_rule_body
                    }
                    WpdsState::BinderListLoop {
                        result_src_idx,
                        rule_idx,
                        body_src_idx,
                        outer_bp,
                        marker_pos,
                        next_pos,
                    } => {
                        // Phase 5b: ^[xs] binder list loop.
                        #binder_list_loop_body
                    }
                    WpdsState::CrossCatDelegate {
                        source_src_idx,
                        outer_bp,
                    } => {
                        // Stage 1.1: cross-cat projection delegation.
                        // Push a CategoryEntry for the source category;
                        // PrefixDispatch will route the engine to source's
                        // rules. After source parses + its Return pops +
                        // its action fires (pushing source Term to
                        // builder), the cross-cat Return (already on the
                        // stack below the source CategoryEntry) becomes
                        // top → its wrap-action fires, wrapping the
                        // source Term as `Cat::Wrapper(Box::new(t))`.
                        WpdsStepAction::Push {
                            symbol: StackSymbolV2::category_entry(*source_src_idx),
                            weight: LexicographicWeight::one(),
                            new_state: WpdsState::PrefixDispatch {
                                pos: _pos,
                                cur_bp: *outer_bp,
                            },
                        }
                    }
                    WpdsState::AmbiguityFanout { .. } => unreachable!(
                        "engine.step called with AmbiguityFanout — walker drives \
                         this state via step_fanout, not the engine. Reaching \
                         this arm signals a routing bug in WpdsWalker::run_to_*."
                    ),
                    WpdsState::OptionalGroup {
                        result_src_idx,
                        rule_idx,
                        group_idx,
                        sub_pos,
                        outer_bp,
                    } => {
                        // Opt-Group (2026-04-29): per-rule per-group dispatch.
                        // sub_pos=0 peeks the FIRST set and chooses
                        // take-or-skip; sub_pos>0 walks inner positions; the
                        // final sub_pos finalizes via OptGroupFinalize.
                        // For grammars without `#opt(...)`, the
                        // `optional_group_body` collapses to `WpdsStepAction::Idle`
                        // and the destructured fields are unused. Suppress the
                        // unused-variable warnings via explicit no-op binds —
                        // these compile to nothing in optimized builds.
                        let _ = (result_src_idx, rule_idx, group_idx, sub_pos, outer_bp);
                        #optional_group_body
                    }
                    WpdsState::Saturating { .. } => WpdsStepAction::Idle,
                    WpdsState::Accepted | WpdsState::Error { .. } => WpdsStepAction::Idle,
                }
            }

            fn action_for(
                &self,
                src_idx: u16,
                rule_idx: u16,
            ) -> Option<&mettail_prattail::wpds_runtime::ActionEntry> {
                #action_for_body
            }
        }
    }
}

/// Emit the InfixLoop dispatch expression — a `match state_cat_src_idx`
/// that calls the per-category `infix_bp_<cat>(text)` lookup helper. The
/// expression evaluates to `Option<(u8, u8, u16, u16)>` (l_bp, r_bp,
/// result_src, rule_idx) per the BP table emission.
fn emit_infix_loop_dispatch(categories: &[String]) -> TokenStream {
    let arms = categories.iter().enumerate().map(|(i, cat)| {
        let i_u16 = i as u16;
        let fn_ident = quote::format_ident!("infix_bp_{}", cat.to_lowercase());
        quote! { #i_u16 => #fn_ident(token_text), }
    });
    quote! {
        {
            match state_cat_src_idx {
                #(#arms)*
                _ => None,
            }
        }
    }
}

fn emit_postfix_dispatch(categories: &[String]) -> TokenStream {
    let arms = categories.iter().enumerate().map(|(i, cat)| {
        let i_u16 = i as u16;
        let fn_ident = quote::format_ident!("postfix_bp_{}", cat.to_lowercase());
        quote! { #i_u16 => #fn_ident(token_text), }
    });
    quote! {
        {
            match state_cat_src_idx {
                #(#arms)*
                _ => None,
            }
        }
    }
}

/// B7 Pattern 1: emit the per-category mixfix BP dispatch — `match
/// state_cat_src_idx` calling the per-category `mixfix_bp_<cat>(text)`
/// lookup. Evaluates to `Option<(u8, u16, u16)>` (left_bp, result_src,
/// rule_idx) for any mixfix trigger keyword whose left operand is in
/// the dispatched category.
fn emit_mixfix_dispatch(categories: &[String]) -> TokenStream {
    let arms = categories.iter().enumerate().map(|(i, cat)| {
        let i_u16 = i as u16;
        let fn_ident = quote::format_ident!("mixfix_bp_{}", cat.to_lowercase());
        quote! { #i_u16 => #fn_ident(token_text), }
    });
    quote! {
        {
            match state_cat_src_idx {
                #(#arms)*
                _ => None,
            }
        }
    }
}

