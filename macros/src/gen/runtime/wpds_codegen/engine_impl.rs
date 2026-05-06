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
    // Stage 3.27d (G-PREFIX-BP, 2026-04-30): build the unary-prefix BP map
    // once per language; consumed by ParamParse arms in BinderRule and
    // OptionalGroup state bodies. Empty map => non-unary-prefix rules use
    // `cur_bp: 0` per the legacy default.
    let prefix_bp_map = super::binder::build_prefix_bp_map(language, per_cat);
    let binder_rule_body =
        super::binder::emit_binder_rule_body(categories, per_cat, &prefix_bp_map);
    // Phase 5b: BinderListLoop body for multi-binder list (^[xs]).
    let binder_list_loop_body = super::binder::emit_binder_list_loop_body(per_cat);
    // Opt-Group (2026-04-29): per-rule per-group OptionalGroup state
    // dispatch — FIRST-set peek + inner-position walk + finalize.
    let optional_group_body =
        super::binder::emit_optional_group_body(categories, per_cat, &prefix_bp_map);
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
                        // Stage 3.16 / Hack #7 (Cluster 1, Mechanism γ,
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
                        // (wpds_walker.rs:2188) transfers the live builder's
                        // open collection_stack to the parent cursor on
                        // Lazy→Strict promotion, fixing the LIFO invariant
                        // for empty cross-cat collections (Hack #7's hot
                        // path). See `feedback_use_wpds_disambiguation_not_heuristics.md`.
                        if let Some(node) = frontier_top {
                            if node.symbol.kind
                                == mettail_prattail::wpds_runtime::SymbolKind::CollectionMarker
                            {
                                let result_src_idx = node.symbol.category_src_idx;
                                let rule_idx = node.symbol.rule_index_in_category;
                                let close_lookup: Option<&'static str> = #collection_close_lookup;
                                let token_text = tokens.peek_text(*pos).unwrap_or("");
                                let token_is_close = Some(token_text) == close_lookup;
                                let element_src_lookup: Option<u16> = {
                                    let result_src_idx = result_src_idx;
                                    let rule_idx = rule_idx;
                                    #collection_element_src_lookup
                                };
                                let needs_redirect = element_src_lookup
                                    .map(|esi| esi != result_src_idx)
                                    .unwrap_or(false);
                                if token_is_close || needs_redirect {
                                    let mut __branches: Vec<
                                        mettail_prattail::wpds_walker::ForkBranch<
                                            LexicographicWeight,
                                        >,
                                    > = Vec::with_capacity(2);
                                    if token_is_close {
                                        __branches.push(
                                            mettail_prattail::wpds_walker::ForkBranch {
                                                symbol: StackSymbolV2::category_entry(0),
                                                weight: LexicographicWeight::from_cost(
                                                    0.0, result_src_idx, rule_idx,
                                                ),
                                                new_state: WpdsState::Unwinding,
                                                action_kind:
                                                    mettail_prattail::wpds_walker::ForkActionKind::ConsumeAndPop,
                                            },
                                        );
                                    }
                                    if needs_redirect {
                                        let element_src_idx =
                                            element_src_lookup.unwrap();
                                        __branches.push(
                                            mettail_prattail::wpds_walker::ForkBranch {
                                                symbol: StackSymbolV2::category_entry(
                                                    element_src_idx,
                                                ),
                                                weight: LexicographicWeight::from_cost(
                                                    mettail_prattail::automata::lex_weight::EPSILON_OPT_SKIP,
                                                    result_src_idx, rule_idx,
                                                ),
                                                new_state: WpdsState::PrefixDispatch {
                                                    pos: *pos,
                                                    cur_bp: *cur_bp,
                                                },
                                                action_kind:
                                                    mettail_prattail::wpds_walker::ForkActionKind::Push,
                                            },
                                        );
                                    }
                                    return WpdsStepAction::Fork {
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
                                    //
                                    // Stage 3.16 / Hack #18 (Cluster 4, Mechanism γ,
                                    // 2026-05-06): Return symbols ALWAYS carry
                                    // `bp = Some(outer_bp)` per codegen invariant
                                    // (constructed via with_kind_return on a
                                    // RuleAt that itself had Some(*cur_bp) at the
                                    // ConsumeAndPush site). Use expect() to surface
                                    // any codegen-invariant violation instead of
                                    // silently substituting 0 — a `feedback_no_stubs_timebombs`
                                    // safeguard.
                                    let outer_bp = node.symbol.bp.expect(
                                        "Return symbol invariant: bp must be Some(outer_bp) \
                                         set at the originating ConsumeAndPush site"
                                    );
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
                                    // Stage 3.16 / Hack #18 (Cluster 4, Mechanism γ,
                                    // 2026-05-06): CollectionMarker symbols ALWAYS
                                    // carry `bp = Some(accumulator_id)` per the
                                    // codegen invariant in
                                    // StackSymbolV2::collection_marker. expect()
                                    // surfaces invariant violations instead of
                                    // silently substituting 0.
                                    let accumulator_id = node.symbol.bp.expect(
                                        "CollectionMarker invariant: bp must be \
                                         Some(accumulator_id) set at construction"
                                    );
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
                                    //
                                    // Stage 3.16 / Hack #18 (Cluster 4, Mechanism γ,
                                    // 2026-05-06): RuleAt's `bp: Option<u8>` is
                                    // genuinely Optional per
                                    // `StackSymbolV2::rule_at(.., bp: Option<u8>)`.
                                    // Some callers thread `Some(*outer_bp)` (when
                                    // a precedenced parent context exists);
                                    // others pass `None` (top-level RuleAt where
                                    // no outer_bp is tracked). The `unwrap_or(0)`
                                    // fallback is the legitimate Optional
                                    // handling — `0` is the canonical "top-level
                                    // cur_bp" sentinel used everywhere a Pratt
                                    // dispatch starts fresh. This is NOT a stub;
                                    // it's the documented Optional-default.
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
                                    //
                                    // Stage 3.16 / Hack #18 (Cluster 4, Mechanism γ,
                                    // 2026-05-06): GroupingMarker symbols ALWAYS
                                    // carry `bp = Some(outer_bp)` per the codegen
                                    // invariant in StackSymbolV2::grouping_marker.
                                    // expect() surfaces invariant violations.
                                    let outer_bp = node.symbol.bp.expect(
                                        "GroupingMarker invariant: bp must be \
                                         Some(outer_bp) — saved cur_bp at the open paren"
                                    );
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
                                    // Stage 3.16 / Hack #18 (Cluster 4, Mechanism γ,
                                    // 2026-05-06): MixfixMarker symbols ALWAYS
                                    // carry `bp = Some(operands_completed)` per
                                    // the codegen invariant in
                                    // StackSymbolV2::mixfix_marker. expect()
                                    // surfaces invariant violations.
                                    let completed_idx = node.symbol.bp.expect(
                                        "MixfixMarker invariant: bp must be \
                                         Some(operands_completed) set at construction"
                                    );
                                    // Stage 3.16 / Hack #19 (Cluster 4, Mechanism γ,
                                    // 2026-05-06): mixfix_parts_len returning None
                                    // means the (result_src_idx, rule_idx) pair
                                    // is missing from the codegen-time mixfix-parts
                                    // table — a hard codegen invariant violation,
                                    // not a parse-time choice. Surface as Error
                                    // with a precise message instead of silently
                                    // substituting 0 (which would skip the mixfix
                                    // dispatch entirely). Per
                                    // `feedback_no_stubs_timebombs.md`.
                                    let parts_len = match mixfix_parts_len(
                                        result_src_idx, rule_idx,
                                    ) {
                                        Some(n) => n,
                                        None => return WpdsStepAction::Error(format!(
                                            "mixfix_parts_len(result={}, rule={}) returned None — \
                                             codegen invariant violated: every MixfixMarker symbol \
                                             must have a mixfix-parts table entry",
                                            result_src_idx, rule_idx,
                                        )),
                                    };
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
                                    // Stage 3.16 / Hack #10 (Cluster 1,
                                    // Mechanism γ, 2026-05-05): two-branch
                                    // Fork over separator-match and
                                    // last-operand-elision (G2 future
                                    // grammar support). Lex-min picks:
                                    //   - separator-match (weight 0.0)
                                    //     when token == following.
                                    //   - last-operand-elision (weight
                                    //     SKIP_BIAS) Pop the marker and
                                    //     transition to InfixLoop. Fires
                                    //     for grammars permitting optional
                                    //     trailing separator (e.g.
                                    //     `if c then a [else b] end`).
                                    //
                                    // (None, _) case is a codegen invariant
                                    // violation — reachable only when the
                                    // codegen-time mixfix-parts table is
                                    // malformed; no Fork branch needed.
                                    match (following, tokens.peek_text(_pos)) {
                                        (Some(t), _) => {
                                            let _ = t;
                                            WpdsStepAction::Fork {
                                                branches: vec![
                                                    // BRANCH 1: separator-match.
                                                    mettail_prattail::wpds_walker::ForkBranch {
                                                        symbol: StackSymbolV2::category_entry(0),
                                                        weight: LexicographicWeight::from_cost(
                                                            0.0, result_src_idx, rule_idx,
                                                        ),
                                                        new_state: WpdsState::MixfixContinuation {
                                                            result_src_idx,
                                                            rule_idx,
                                                            completed_idx: completed_idx + 1,
                                                        },
                                                        action_kind:
                                                            mettail_prattail::wpds_walker::ForkActionKind::Consume,
                                                    },
                                                    // BRANCH 2: last-operand-elision (G2 support).
                                                    mettail_prattail::wpds_walker::ForkBranch {
                                                        symbol: StackSymbolV2::category_entry(0),
                                                        weight: LexicographicWeight::from_cost(
                                                            mettail_prattail::automata::lex_weight::EPSILON_OPT_SKIP,
                                                            result_src_idx, rule_idx,
                                                        ),
                                                        new_state: WpdsState::InfixLoop { cur_bp: 0 },
                                                        action_kind:
                                                            mettail_prattail::wpds_walker::ForkActionKind::Pop,
                                                    },
                                                ],
                                                consume_trigger: false,
                                            }
                                        }
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
                                    //
                                    // Stage 3.16 / Hack #18 (Cluster 4, Mechanism γ,
                                    // 2026-05-06): OptionalGroupAt symbols ALWAYS
                                    // carry `bp = Some(outer_bp)` per the codegen
                                    // invariant in
                                    // StackSymbolV2::optional_group_at.
                                    let result_src_idx = node.symbol.category_src_idx;
                                    let rule_idx = node.symbol.rule_index_in_category;
                                    let outer_bp = node.symbol.bp.expect(
                                        "OptionalGroupAt invariant: bp must be \
                                         Some(outer_bp) — preserved across the group \
                                         so on group exit BinderRule resumes at the \
                                         correct precedence"
                                    );
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
                                other => WpdsStepAction::Error(format!(
                                    "Unwinding: unrecognized symbol kind {:?} at pos {} \
                                     (expected CollectionMarker / RuleAt / GroupingMarker / \
                                     MixfixMarker / OptionalGroupAt) — codegen invariant violated",
                                    other, _pos,
                                )),
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
                        // Stage 3.18 / Hacks #17+#20 (Cluster 3, Mechanism γ,
                        // 2026-05-05): collect ALL tier candidates whose
                        // l_bp >= cur_bp, then emit a Fork over them with
                        // BP_TIER_INFIX < BP_TIER_POSTFIX < BP_TIER_MIXFIX
                        // bias offsets so lex-min picks the lower tier on
                        // weight ties. Source-order tiebreak via rule_idx
                        // within tier. Singleton fast-path emits
                        // ConsumeAndPush directly to preserve zero-overhead
                        // dispatch for the deterministic case (one tier
                        // matches at l_bp >= cur_bp).
                        let state_cat_src_idx: u16 = frontier_top
                            .map(|n| n.symbol.category_src_idx)
                            .unwrap_or(#primary_src_idx);
                        let token_text = tokens.peek_text(_pos).unwrap_or("");
                        let _ = token_text;

                        let mut __cands: Vec<
                            mettail_prattail::wpds_walker::ForkBranch<
                                LexicographicWeight,
                            >,
                        > = Vec::new();

                        // Infix tier (BP_TIER_INFIX = 0.00).
                        if let Some((l_bp, r_bp, result_src, rule_idx)) =
                            #infix_loop_dispatch
                        {
                            if l_bp >= *cur_bp {
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
                                __cands.push(
                                    mettail_prattail::wpds_walker::ForkBranch {
                                        symbol: StackSymbolV2::rule_at(
                                            result_src, rule_idx, 0, Some(*cur_bp),
                                        )
                                        .with_kind_return(),
                                        weight: LexicographicWeight::from_cost(
                                            mettail_prattail::automata::lex_weight::BP_TIER_INFIX,
                                            result_src, rule_idx,
                                        ),
                                        new_state,
                                        action_kind:
                                            mettail_prattail::wpds_walker::ForkActionKind::Push,
                                    },
                                );
                            }
                        }

                        // Postfix tier (BP_TIER_POSTFIX = 0.10).
                        if let Some((l_bp, result_src, rule_idx)) =
                            #postfix_dispatch
                        {
                            if l_bp >= *cur_bp {
                                __cands.push(
                                    mettail_prattail::wpds_walker::ForkBranch {
                                        symbol: StackSymbolV2::rule_at(
                                            result_src, rule_idx, 0, Some(*cur_bp),
                                        )
                                        .with_kind_return(),
                                        weight: LexicographicWeight::from_cost(
                                            mettail_prattail::automata::lex_weight::BP_TIER_POSTFIX,
                                            result_src, rule_idx,
                                        ),
                                        new_state: WpdsState::InfixLoop {
                                            cur_bp: *cur_bp,
                                        },
                                        action_kind:
                                            mettail_prattail::wpds_walker::ForkActionKind::Push,
                                    },
                                );
                            }
                        }

                        // Mixfix tier (BP_TIER_MIXFIX = 0.20).
                        if let Some((l_bp, result_src, rule_idx)) =
                            #mixfix_dispatch
                        {
                            if l_bp >= *cur_bp {
                                __cands.push(
                                    mettail_prattail::wpds_walker::ForkBranch {
                                        symbol: StackSymbolV2::mixfix_marker(
                                            result_src, rule_idx, 0,
                                        ),
                                        weight: LexicographicWeight::from_cost(
                                            mettail_prattail::automata::lex_weight::BP_TIER_MIXFIX,
                                            result_src, rule_idx,
                                        ),
                                        new_state: WpdsState::PrefixDispatch {
                                            pos: _pos + 1,
                                            cur_bp: 0,
                                        },
                                        action_kind:
                                            mettail_prattail::wpds_walker::ForkActionKind::Push,
                                    },
                                );
                            }
                        }

                        match __cands.len() {
                            0 => {
                                // No tier matched — fall through to Unwinding.
                                WpdsStepAction::Advance(WpdsState::Unwinding)
                            }
                            1 => {
                                // Singleton fast-path: only one tier matched,
                                // so emit ConsumeAndPush directly. Preserves
                                // zero-overhead dispatch for shipped grammars
                                // (typical case — only one operator at any
                                // given (token, l_bp >= cur_bp) pair).
                                let b = __cands.into_iter().next().unwrap();
                                WpdsStepAction::ConsumeAndPush {
                                    symbol: b.symbol,
                                    weight: b.weight,
                                    new_state: b.new_state,
                                    capture_token: false,
                                }
                            }
                            _ => {
                                // Multi-tier ambiguity (G5: e.g. infix and
                                // postfix sharing a token at the same
                                // l_bp >= cur_bp) — emit a Fork. Lex-min
                                // picks the lower BP tier on ties.
                                WpdsStepAction::Fork {
                                    branches: __cands,
                                    consume_trigger: true,
                                }
                            }
                        }
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

