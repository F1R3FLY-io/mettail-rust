//! Emits the per-language `impl WpdsStepEngine` body.
//!
//! Phase A.1 deliverable: the infrastructure-complete skeleton — Ready →
//! PrefixDispatch transitions, all other states return Idle. Phase A.2–A.10
//! populate the per-rule dispatch arms that make the engine actually parse.

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
    let collection_close_lookup = super::collection::emit_collection_close_lookup(per_cat);
    let collection_element_src_lookup =
        super::collection::emit_collection_element_src_lookup(categories, per_cat);
    // Phase 5: binder rule prefix arms (recognize trigger literal of binder
    // rules) + BinderRule state body (multi-step state machine per rule).
    let binder_arms = super::binder::emit_binder_prefix_arms(language, categories, per_cat);
    let binder_rule_body = super::binder::emit_binder_rule_body(categories, per_cat);
    // Phase 5b: BinderListLoop body for multi-binder list (^[xs]).
    let binder_list_loop_body = super::binder::emit_binder_list_loop_body(per_cat);

    let action_for_body =
        semantic_actions::emit_action_for_body(language, categories, &per_cat_indexed);

    // Phase 3: InfixLoop dispatch arm. Per-category match on
    // `state_cat_src_idx` calling the emitted `infix_bp_<cat>` lookup
    // helpers.
    let infix_loop_dispatch = emit_infix_loop_dispatch(categories);
    let postfix_dispatch = emit_postfix_dispatch(categories);

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
                            // Phase 4: collection open-delim arms run first
                            // since `{` / `[` are unambiguous open markers.
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
                                _ => WpdsStepAction::Idle,
                            }
                        } else {
                            WpdsStepAction::Accept
                        }
                    }
                    WpdsState::InfixLoop { cur_bp } => {
                        // Phase 4/5: if frontier_top is a CollectionMarker or
                        // RuleAt (binder rule marker), skip infix dispatch and
                        // fall through to Unwinding. The separator/close delim
                        // (Phase 4) and binder action (Phase 5) are handled in
                        // CollectionLoop / Unwinding-RuleAt arms, not InfixLoop.
                        if let Some(node) = frontier_top {
                            match node.symbol.kind {
                                mettail_prattail::wpds_runtime::SymbolKind::CollectionMarker
                                | mettail_prattail::wpds_runtime::SymbolKind::RuleAt(_) => {
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
                    WpdsState::AmbiguityFanout { .. }
                    | WpdsState::Saturating { .. } => WpdsStepAction::Idle,
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

/// Legacy thin wrapper used by tests that predate Phase A.2. Still emits
/// the minimal skeleton but without access to the full LanguageDef.
pub(crate) fn emit_engine_impl(engine_ident: &Ident, primary_src_idx: u16) -> TokenStream {
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
                _tokens: &dyn mettail_prattail::wpds_runtime::WpdsTokenSource,
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
                    WpdsState::PrefixDispatch { .. } => {
                        // Phase A.2+ populates this arm with per-rule
                        // prefix dispatch. Phase A.1 accepts once a frame
                        // is established.
                        if frontier_top.is_some() {
                            WpdsStepAction::Accept
                        } else {
                            WpdsStepAction::Idle
                        }
                    }
                    WpdsState::Unwinding => {
                        // Phase A.2: pop `Return` frames, fire their actions,
                        // then pop the enclosing `CategoryEntry` and accept.
                        if let Some(node) = frontier_top {
                            match node.symbol.kind {
                                mettail_prattail::wpds_runtime::SymbolKind::Return => {
                                    WpdsStepAction::Pop {
                                        weight: LexicographicWeight::one(),
                                        new_state: WpdsState::Unwinding,
                                    }
                                }
                                mettail_prattail::wpds_runtime::SymbolKind::CategoryEntry => {
                                    WpdsStepAction::Pop {
                                        weight: LexicographicWeight::one(),
                                        new_state: WpdsState::Accepted,
                                    }
                                }
                                _ => WpdsStepAction::Idle,
                            }
                        } else {
                            WpdsStepAction::Accept
                        }
                    }
                    WpdsState::InfixLoop { .. }
                    | WpdsState::CollectionLoop { .. }
                    | WpdsState::AmbiguityFanout { .. }
                    | WpdsState::Saturating { .. } => WpdsStepAction::Idle,
                    WpdsState::Accepted | WpdsState::Error { .. } => WpdsStepAction::Idle,
                }
            }
        }
    }
}
