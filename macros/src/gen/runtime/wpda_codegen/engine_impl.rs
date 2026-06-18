//! Emits the per-language `impl WpdaEngine` body.
//!
//! Covers all WpdaState dispatch: Ready → PrefixDispatch seed, prefix arms
//! per atomic/binder/cross-cat rule, InfixLoop with Pratt BP, CollectionLoop
//! for sep/close, BinderRule per-position dispatch, CrossCatDelegate for
//! cross-cat projections, Unwinding for Pop chains, terminal Accepted/Error.
//! AmbiguityFanout is owned by the walker; if routed to `engine.step`, the
//! generated engine reports a structured error rather than panicking.

use mettail_ast::grammar::GrammarRule;
use mettail_ast::language::LanguageDef;
use proc_macro2::{Ident, TokenStream};
use quote::quote;

use super::{prefix, semantic_actions};

/// Emit the `impl WpdaEngine<LexicographicWeight> for <engine_ident>`
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
    // Plan B (F5 close/sep filter, 2026-05-11): per-rule (close, sep)
    // lookup used by InfixLoop's CollectionMarker filter.
    let collection_close_sep_lookup =
        super::collection::emit_collection_close_sep_lookup(language, per_cat);
    // Phase 4 #5b (2026-05-12): per-(src, rule, slot_idx) lookup for
    // HashMap collection slots' key/value separator. Yields the body
    // of `kv_separator_for_collection` (returns `Option<&'static str>`).
    let kv_separator_for_collection_lookup =
        super::collection::emit_kv_separator_for_collection(language, per_cat);
    let collection_element_src_lookup =
        super::collection::emit_collection_element_src_lookup(language, categories, per_cat);
    // B9 / Class 2 (2026-05-08): per-rule lookup for Class-2 binder rules'
    // internal collection slots. Used by the walker's CollectionMarker-pop
    // arm to suppress the default FireAction.
    let is_binder_internal_collection_lookup =
        super::collection::emit_is_binder_internal_collection_lookup(per_cat);
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
    let binder_list_loop_body = super::binder::emit_binder_list_loop_body(categories, per_cat);
    // B8 / Path P1 (2026-05-08): per-rule predicate for routing
    // OptionalGroupAt symbols to BinderListLoop when the rule is Class 3.
    let is_binderlist_inner_lookup = super::binder::emit_binderlist_inner_lookup(per_cat);
    // B8 / Issue A' (2026-05-09): per-rule lookup for outer-slot
    // coordinates (marker_pos, next_pos, body_src_idx) used at
    // Unwinding-OptionalGroupAt routing for Class 3 rules.
    let binderlist_inner_metadata = super::binder::emit_binderlist_inner_metadata(per_cat);
    // B8 / Issue D (2026-05-09); Phase 4 #2 (2026-05-12): per-(src, rule,
    // slot_idx) predicate for Class 3 CollectionMarker pushes that should
    // also open a BinderScope. Per-slot variant is required for rules
    // with a Class-3 BinderListLoop AND a Class-2 SimpleCollection
    // sibling (e.g. PInputsTagged) — the per-rule predicate (pre-Phase-4-#2)
    // incorrectly opened a BinderScope for the Class-2 sibling too.
    let is_class3_collection_lookup = super::binder::emit_is_class3_collection_per_slot(per_cat);
    // B8 / Issue 2 (2026-05-10): per-(src, rule, sub_pos) lookup
    // distinguishing Class 3 inner-walk OptionalGroupAt from genuine
    // *opt(...) OptionalGroup. Replaces the prior alias to
    // emit_is_class3_collection (per-rule only) — alias was correct
    // for shipped grammars but incorrect for the supported feature
    // combination of Class 3 BinderListLoop + real *opt(...) in same
    // rule.
    let is_class3_inner_marker_lookup =
        super::binder::emit_is_class3_inner_marker_per_subpos(per_cat);
    // B8 / Issue C (2026-05-09): per-(rule, sub_pos) splice lookup
    // for Class 3 inner walk Name-parse return points.
    let binderlist_inner_post_splice_lookup =
        super::binder::emit_binderlist_inner_post_splice_lookup(per_cat);
    // Opt-Group (2026-04-29): per-rule per-group OptionalGroup state
    // dispatch — FIRST-set peek + inner-position walk + finalize.
    let optional_group_body = super::binder::emit_optional_group_body(categories, per_cat);
    // B7 Pattern 2: paren-grouping arms in PrefixDispatch — backend
    // emission of `(`-grouping for every parseable category, satisfying
    // the user mandate "no per-grammar order; backend change". Emitted
    // BEFORE generic prefix_arms so `(` matches grouping rather than
    // any rule that happens to start with `(`.
    // Stage 3.20 / Commit 4 part 2 (Plan agent Fix, 2026-05-06): replace
    // `emit_grouping_arms` with `emit_paren_dispatch_arms` that detects
    // `(`-trigger conflicts (e.g. Lambda's App rule shares `(` with the
    // B7 paren-grouping arm) and emits a Fork combining both
    // interpretations so lex-min disambiguates per
    // `feedback_use_wpds_disambiguation_not_heuristics.md`. For grammars
    // without a `(`-triggered binder rule (all shipped except Lambda),
    // the output is byte-identical to `emit_grouping_arms`.
    let grouping_arms = super::prefix::emit_paren_dispatch_arms(categories, language, per_cat);

    let action_for_body =
        semantic_actions::emit_action_for_body(language, categories, &per_cat_indexed);
    // Pass-2c token-soundness backstop (2026-05-30): per-rule in-span literal
    // count consumed by the realize-time soundness filter.
    let min_terminal_span_body =
        semantic_actions::emit_min_terminal_span_body(categories, &per_cat_indexed);
    // Sig-B Blocker-3 §2.3 (2026-06-01, pgmcp experiment #9): grammar
    // single-hop coercion table (`(from_cat, to_cat) -> &[(target_cat,
    // rule_idx)]`). Mirrors the live Pass-2a/Pass-2c synthesis rule set
    // EXACTLY; consumed by the span-anchored splice's §2.4a clause-4
    // (category compatibility) + §2.4c (interpose the coercion Symbol).
    let single_hop_coercion_body =
        semantic_actions::emit_single_hop_coercion_body(categories, &per_cat_indexed, language);
    // RC-B (2026-06-17): the trigger-bearing prefix-cast table (the complement
    // of single_hop_coercion), consumed by the pop-site prefix-cast wrap
    // reconciliation to fire e.g. `BoolToInt` over a chain-folded `Bool` body.
    let prefix_cast_into_body =
        semantic_actions::emit_prefix_cast_into_body(categories, &per_cat_indexed);
    // RC-B (2026-06-17): the leading keyword of each prefix-cast rule (the
    // SAME set), so the pop-site wrap synthesis can reject a candidate whose
    // keyword differs from the enclosing `kw "(" .. ")"` frame's (token-sound).
    let prefix_cast_keyword_body =
        semantic_actions::emit_prefix_cast_keyword_body(categories, &per_cat_indexed);
    let (structural_open_body, structural_close_body) =
        emit_structural_delimiter_predicates(language, per_cat);

    // Phase 3: InfixLoop dispatch arm. Per-category match on
    // `state_cat_src_idx` calling the emitted `infix_bp_<cat>` lookup
    // helpers.
    let infix_loop_dispatch = emit_infix_loop_dispatch(categories);
    let postfix_dispatch = emit_postfix_dispatch(categories);
    let mixfix_dispatch = emit_mixfix_dispatch(categories);
    // Phase F.13 chain_10000 Exp 6 Substage 6b (2026-05-26): per-category
    // iter-eligible dispatch consumed by the singleton InfixLoop fast
    // path and the `InfixChainIterative` arm. Routes iterative-eligible
    // operators through `IterativeChainAbsorb` (per-chain GSS push
    // elision) instead of per-iteration `ConsumeAndPush`.
    let iter_eligible_dispatch = emit_iter_eligible_dispatch(categories);
    // Plan A (paren+postfix redesign, 2026-05-11): per-category
    // recognize-token lookup for the Unwinding-CategoryEntry's
    // lookahead-conditional GroupingClosePreservingInner branch.
    let category_recognizes_token_dispatch = emit_category_recognizes_token_dispatch(categories);
    let category_recognizes_operator_body = emit_category_recognizes_operator_body(categories);
    // D8 fix (2026-05-13): per-language `type_name → cat_src_idx`
    // lookup body, consumed by the walker's
    // `GroupingClosePreservingInner` sentinel resolution.
    let cat_of_type_name_body = emit_cat_of_type_name(language, categories);
    // L-substrate Piece #6 (2026-05-13): lex-fork dispatch block,
    // emitted at the top of the WpdaState::PrefixDispatch arm.
    let lex_fork_dispatch = super::forks::emit_lex_fork_at_prefix_dispatch(primary_src_idx);
    let lex_fork_infix_dispatch = super::forks::emit_lex_fork_at_infix_loop(primary_src_idx);

    // M6c.2 (2026-05-14): per-grammar `lex_alt_rule_for` free fn.
    // Used by the lex-Fork emitter (M6c.3) to bind alts to atomic-
    // literal rules. Emitted as a sibling of the engine impl so the
    // codegen output uses a single match expression with all
    // (cat, kind) entries.
    let lex_alt_rule_for_fn =
        super::kind_dispatch::emit_lex_alt_rule_for_fn(language, per_cat, categories);

    quote! {
        #lex_alt_rule_for_fn

        #[allow(unused_variables, unused_braces)]
        impl mettail_prattail::wpda_walker::WpdaEngine<
            mettail_prattail::automata::lex_weight::LexicographicWeight,
        > for #engine_ident
        {
            fn step(
                &self,
                state: &mettail_prattail::wpda_runtime::WpdaState,
                _gss: &mettail_prattail::gss::WpdaGss<
                    mettail_prattail::automata::lex_weight::LexicographicWeight,
                >,
                frontier_top: Option<&mettail_prattail::gss::WpdaGssNode>,
                _pos: usize,
                tokens: &dyn mettail_prattail::wpda_runtime::WpdaTokenSource,
            ) -> mettail_prattail::wpda_walker::WpdaStepAction<
                mettail_prattail::automata::lex_weight::LexicographicWeight,
            > {
                use mettail_prattail::wpda_runtime::{
                    StackSymbolV2, WpdaState,
                };
                use mettail_prattail::wpda_walker::WpdaStepAction;
                use mettail_prattail::automata::lex_weight::LexicographicWeight;
                use mettail_prattail::automata::semiring::Semiring;
                // C11.5 (2026-05-16): unused DerivationWeight + DerivationSnapshot
                // imports deleted alongside the C10 W revert. The M11.4 weight
                // wrappers no longer carry a snapshot — `lex_w`/`lex_w_alt`/
                // `lex_one` directly construct LexicographicWeight values.
                use mettail_prattail::wpda_runtime::{lex_w, lex_w_alt, lex_one};
                // Phase 3.1.7 (C10, 2026-05-15): walker `W` is plain
                // `LexicographicWeight` — SPPF arena carries derivation
                // ambiguity; W carries only path-cost tiebreak.
                #[allow(non_camel_case_types)]
                type __DwW = LexicographicWeight;

                match state {
                    WpdaState::Ready { min_bp } => {
                        let primary = StackSymbolV2::category_entry(#primary_src_idx);
                        WpdaStepAction::Push {
                            symbol: primary,
                            weight: lex_w(0.0, #primary_src_idx, 0),
                            new_state: WpdaState::PrefixDispatch {
                                pos: 0,
                                cur_bp: *min_bp,
                            },
                        }
                    }
                    WpdaState::PrefixDispatch { pos, cur_bp } => {
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
                        #lex_fork_dispatch
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
                            if node.symbol.kind
                                == mettail_prattail::wpda_runtime::SymbolKind::CollectionMarker
                            {
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
                                let close_lookup: Option<&'static str> = #collection_close_lookup;
                                let token_text = tokens.peek_text(*pos).unwrap_or("");
                                // #307 ROOT-F G1 site-2 (2026-06-11): the
                                // empty-collection close detection is edge
                                // MEMBERSHIP (primary + alternatives), not
                                // primary-only text equality (the ROOT-A
                                // primary_equality_loses trap — live for
                                // multi-char closes like the Bag "}#").
                                let token_is_close = Some(token_text) == close_lookup
                                    || close_lookup.is_some_and(|cl| {
                                        tokens
                                            .peek_alternatives(*pos)
                                            .iter()
                                            .any(|a| a.text == cl)
                                    });
                                let element_src_lookup: Option<u16> = {
                                    let result_src_idx = result_src_idx;
                                    let rule_idx = rule_idx;
                                    let slot_idx = slot_idx;
                                    #collection_element_src_lookup
                                };
                                let redirect_src_idx =
                                    element_src_lookup.filter(|&esi| esi != result_src_idx);
                                if token_is_close || redirect_src_idx.is_some() {
                                    let mut __branches: Vec<
                                        mettail_prattail::wpda_walker::ForkBranch<
                                            __DwW,
                                        >,
                                    > = Vec::with_capacity(2);
                                    if token_is_close {
                                        // #307 ROOT-F G1 site-2: one
                                        // ConsumeAtAndPop per matched close
                                        // edge (deduped by target), never the
                                        // alt-0 ConsumeAndPop advance.
                                        let cl = close_lookup.unwrap_or("");
                                        let mut __targets: Vec<usize> =
                                            Vec::with_capacity(2);
                                        if token_text == cl {
                                            if let Some(np) = tokens.next_pos(*pos, 0) {
                                                __targets.push(np);
                                            }
                                        }
                                        for (__i, __alt) in
                                            tokens.peek_alternatives(*pos).iter().enumerate()
                                        {
                                            if __alt.text == cl {
                                                if let Some(np) =
                                                    tokens.next_pos(*pos, __i + 1)
                                                {
                                                    if !__targets.contains(&np) {
                                                        __targets.push(np);
                                                    }
                                                }
                                            }
                                        }
                                        for np in __targets {
                                            __branches.push(
                                                mettail_prattail::wpda_walker::ForkBranch {
                                                    symbol: StackSymbolV2::category_entry(0),
                                                    weight: lex_w(
                                                        0.0, result_src_idx, rule_idx,
                                                    ),
                                                    new_state: WpdaState::Unwinding,
                                                    action_kind:
                                                        mettail_prattail::wpda_walker::ForkActionKind::ConsumeAtAndPop {
                                                            next_pos: np,
                                                        },
                                                },
                                            );
                                        }
                                    }
                                    if let Some(element_src_idx) = redirect_src_idx {
                                        __branches.push(
                                            mettail_prattail::wpda_walker::ForkBranch {
                                                symbol: StackSymbolV2::category_entry(
                                                    element_src_idx,
                                                ),
                                                weight: lex_w(
                                                    mettail_prattail::automata::lex_weight::EPSILON_OPT_SKIP,
                                                    result_src_idx, rule_idx,
                                                ),
                                                new_state: WpdaState::PrefixDispatch {
                                                    pos: *pos,
                                                    cur_bp: *cur_bp,
                                                },
                                                action_kind:
                                                    mettail_prattail::wpda_walker::ForkActionKind::Push,
                                            },
                                        );
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
                            _ => {
                                // Stage 3.20 / L12 (Commit D, 2026-05-06):
                                // WPDS-edge recovery. The wrapper-level
                                // skip-to-sync loop in facade.rs is replaced
                                // by intrinsic Walker recovery emitted via
                                // recovery_dispatch::emit_recovery_fork. Up
                                // to K=8 lex-min-ranked branches
                                // (Skip/Delete/Insert/Substitute) replace
                                // the prior Idle that hung the parse on
                                // dead-end. Per `feedback_use_wpds_disambiguation_not_heuristics.md`.
                                //
                                // Bounded recovery (2026-05-06): the walker's
                                // apply_action_to_cursor::Fork detects this
                                // recovery Fork (via branches' BuilderDelta
                                // effect kind) and enforces three principled
                                // WPDS-correct bounds before allocating
                                // children:
                                //   1. cursor.recovery_depth < RecoveryConfig.max_recovery_depth
                                //   2. (pos, cat, cur_bp) ∉ cursor.visited_recovery
                                //   3. forward-progress filter: branches with
                                //      new_pos == base_pos AND no InsertToken
                                //      effect are dropped
                                // No EOF heuristic; recovery_dispatch's
                                // empty-token-ids path returns Error cleanly,
                                // and the depth/visited bounds catch any
                                // mid-stream loops.
                                match recovery_infra_for(state_cat_src_idx) {
                                    Some(infra) => {
                                        let active_recovery_config =
                                            mettail_prattail::recovery_cohort::with_active_recovery_config(
                                                |config| config.clone(),
                                            );
                                        let recovery_config = active_recovery_config
                                            .as_ref()
                                            .unwrap_or(&infra.config);
                                        // Phase F.13 Task #117 (2026-05-23):
                                        // try cohort-cached path first via
                                        // the walker's pinned TLS pointer.
                                        // Falls through to the uncached path
                                        // when the cache pointer is null
                                        // (engine.step called outside a
                                        // walker parse loop).
                                        let cached: Option<mettail_prattail::wpda_walker::WpdaStepAction<__DwW>> =
                                            mettail_prattail::recovery_cohort::with_active_cache_typed::<__DwW, _, _>(
                                                |cache| {
                                                    let view = mettail_prattail::recovery_dispatch::WalkerRuntimeView::new(
                                                        _gss,
                                                        frontier_top,
                                                        *pos,
                                                        state_cat_src_idx,
                                                        *cur_bp,
                                                    );
                                                    mettail_prattail::recovery_dispatch::emit_recovery_fork_cached_with_config::<__DwW>(
                                                        view,
                                                        tokens,
                                                        infra,
                                                        recovery_config,
                                                        cache,
                                                    )
                                                },
                                            );
                                        match cached {
                                            Some(action) => action,
                                            None => {
                                                let view = mettail_prattail::recovery_dispatch::WalkerRuntimeView::new(
                                                    _gss,
                                                    frontier_top,
                                                    *pos,
                                                    state_cat_src_idx,
                                                    *cur_bp,
                                                );
                                                mettail_prattail::recovery_dispatch::emit_recovery_fork_with_config::<__DwW>(
                                                    view,
                                                    tokens,
                                                    infra,
                                                    recovery_config,
                                                )
                                            }
                                        }
                                    }
                                    None => WpdaStepAction::Error(format!(
                                        "no recovery infra for category src_idx {} at pos {} — \
                                         codegen invariant violated (recovery_infra_for is exhaustive)",
                                        state_cat_src_idx, *pos,
                                    )),
                                }
                            }
                        }
                    }
                    WpdaState::Unwinding => {
                        if let Some(node) = frontier_top {
                            match node.symbol.kind {
                                mettail_prattail::wpda_runtime::SymbolKind::Return => {
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
                                         set at the originating ConsumeAndPush site"
                                    );
                                    WpdaStepAction::Pop {
                                        weight: lex_one(),
                                        new_state: WpdaState::InfixLoop { cur_bp: outer_bp },
                                    }
                                }
                                mettail_prattail::wpda_runtime::SymbolKind::CategoryEntry => {
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
                                        let next_tok = tokens.peek_text(_pos + 1).unwrap_or("");
                                        let inner_matches: bool = #category_recognizes_token_dispatch;
                                        if inner_matches {
                                            // D8 fix (2026-05-13): emit sentinel
                                            // `u16::MAX`. The walker resolves the
                                            // ACTUAL inner-expression RESULT cat
                                            // from cursor evidence.
                                            let _ = inner_cat;
                                            WpdaState::GroupingClosePreservingInner {
                                                inner_cat_src_idx: u16::MAX,
                                            }
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
                                    WpdaStepAction::Pop {
                                        weight: lex_one(),
                                        new_state,
                                    }
                                }
                                mettail_prattail::wpda_runtime::SymbolKind::CollectionMarker => {
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
                                    if self.is_class3_collection_per_slot(
                                        result_src_idx, rule_idx, slot_idx_for_class3,
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
                                         Some(slot_idx) set at construction"
                                    );
                                    // The CollectionLoop field remains for
                                    // compatibility with existing state
                                    // constructors; cursor-aware walker
                                    // paths treat it as non-authoritative.
                                    let accumulator_id = slot_idx;
                                    let element_src_lookup: Option<u16> = {
                                        let result_src_idx = result_src_idx;
                                        let rule_idx = rule_idx;
                                        let slot_idx = slot_idx;
                                        #collection_element_src_lookup
                                    };
                                    let element_src_idx = element_src_lookup.unwrap_or(result_src_idx);
                                    // str-cast collection-infix fix (2026-06-18):
                                    // recover the Pratt dispatch bp captured on the
                                    // CollectionMarker at open (coll_dispatch_bp =
                                    // Some(cur_bp) for Class-5 literals, Some(0) for
                                    // binder-internal collections). It feeds
                                    // CollectionLoop.outer_bp so the G1 close branch
                                    // resumes InfixLoop { cur_bp: outer_bp } — a
                                    // finalized collection joins the enclosing Pratt
                                    // loop exactly as an atomic primary does.
                                    // unwrap_or(0) degrades to the pre-fix behavior.
                                    let dispatch_bp = node.symbol.coll_dispatch_bp.unwrap_or(0);
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
                                }
                                mettail_prattail::wpda_runtime::SymbolKind::RuleAt(position) => {
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
                                }
                                mettail_prattail::wpda_runtime::SymbolKind::GroupingMarker => {
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
                                    // Stage 3.16 invariant (Cluster 4, Mechanism γ,
                                    // 2026-05-06): GroupingMarker symbols ALWAYS
                                    // carry `bp = Some(outer_bp)` per the codegen
                                    // invariant in StackSymbolV2::grouping_marker.
                                    // expect() surfaces invariant violations.
                                    let outer_bp = node.symbol.bp.expect(
                                        "GroupingMarker invariant: bp must be \
                                         Some(outer_bp) — saved cur_bp at the open paren"
                                    );
                                    match tokens.peek_text(_pos) {
                                        Some(")") => WpdaStepAction::ConsumeAndPop {
                                            weight: lex_one(),
                                            new_state: WpdaState::InfixLoop {
                                                cur_bp: outer_bp,
                                            },
                                        },
                                        other => WpdaStepAction::Error(format!(
                                            "expected `)` to close grouping at pos {}, found {:?}",
                                            _pos, other
                                        )),
                                    }
                                }
                                mettail_prattail::wpda_runtime::SymbolKind::MixfixMarker => {
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
                                         Some(operands_completed) set at construction"
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
                                    let parts_len = match mixfix_parts_len(
                                        result_src_idx, rule_idx,
                                    ) {
                                        Some(n) => n,
                                        None => return WpdaStepAction::Error(format!(
                                            "mixfix_parts_len(result={}, rule={}) returned None — \
                                             codegen invariant violated: every MixfixMarker symbol \
                                             must have a mixfix-parts table entry",
                                            result_src_idx, rule_idx,
                                        )),
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
                                    let _ = parts_len;  // suppress unused warning
                                    let _ = mixfix_part;  // path used in arm below
                                    return WpdaStepAction::Advance(
                                        WpdaState::MixfixLiteralRun {
                                            result_src_idx,
                                            rule_idx,
                                            completed_idx,
                                            kind: 0,
                                            sub_pos: 0,
                                        },
                                    );
                                }
                                mettail_prattail::wpda_runtime::SymbolKind::OptionalGroupAt(sub_pos) => {
                                    // Opt-Group: inner ParamParse / Literal /
                                    // BinderIdent / GuardSlot just returned to
                                    // the optional-group marker.
                                    //
                                    // B8 / Path P1 (2026-05-08): when the rule
                                    // is a Class 3 BinderListLoop (per the
                                    // is_binderlist_inner lookup), route to
                                    // BinderListLoop{sub_pos} instead of
                                    // OptionalGroup. The OptionalGroupAt symbol
                                    // is reused as a pluggable inner-walk
                                    // marker; the per-rule lookup disambiguates.
                                    let result_src_idx = node.symbol.category_src_idx;
                                    let rule_idx = node.symbol.rule_index_in_category;
                                    let outer_bp = node.symbol.bp.expect(
                                        "OptionalGroupAt invariant: bp must be \
                                         Some(outer_bp) — preserved across the group"
                                    );
                                    let is_binderlist_inner: bool = #is_binderlist_inner_lookup;
                                    if is_binderlist_inner {
                                        // B8 / Issue A' (2026-05-09): per-rule
                                        // metadata lookup recovers outer-slot
                                        // coordinates so sub_pos=N arms can
                                        // reference the BinderListLoop's
                                        // marker_pos correctly.
                                        let (marker_pos, next_pos, body_src_idx): (u8, u8, u16) =
                                            #binderlist_inner_metadata;
                                        let new_state = WpdaState::BinderListLoop {
                                            result_src_idx,
                                            rule_idx,
                                            body_src_idx,
                                            outer_bp,
                                            marker_pos,
                                            next_pos,
                                            sub_pos,
                                        };
                                        // B8 / Issue C (2026-05-09): when the
                                        // just-completed inner step was a
                                        // ParamParse{collection:Some}, splice
                                        // the parsed term into the Names
                                        // accumulator (id=0).
                                        let splice_id: Option<u8> =
                                            #binderlist_inner_post_splice_lookup;
                                        if let Some(id) = splice_id {
                                            return WpdaStepAction::AdvanceWithEffect {
                                                new_state,
                                                effect: mettail_prattail::wpda_walker::BuilderDelta::SpliceIntoCollection { id },
                                            };
                                        }
                                        return WpdaStepAction::Advance(new_state);
                                    }
                                    return WpdaStepAction::Advance(
                                        WpdaState::OptionalGroup {
                                            result_src_idx,
                                            rule_idx,
                                            group_idx: 0,
                                            sub_pos,
                                            outer_bp,
                                        },
                                    );
                                }
                                other => WpdaStepAction::Error(format!(
                                    "Unwinding: unrecognized symbol kind {:?} at pos {} \
                                     (expected CollectionMarker / RuleAt / GroupingMarker / \
                                     MixfixMarker / OptionalGroupAt) — codegen invariant violated",
                                    other, _pos,
                                )),
                            }
                        } else {
                            WpdaStepAction::Accept
                        }
                    }
                    WpdaState::InfixLoop { cur_bp } => {
                        // Phase 4/5/B7: if frontier_top is a marker symbol
                        // for a mid-rule context, skip infix dispatch and
                        // fall through to Unwinding. Each marker has its
                        // own Unwinding handler.
                        //
                        // F5 fix (2026-05-10): `CollectionMarker` REMOVED
                        // from this skip list. After a cross-cat sub-parse
                        // returns to a CollectionMarker top, the next
                        // tokens may be Pratt infix/postfix/mixfix operators
                        // extending the current element (e.g., `+ 2` after
                        // `1` inside `{1 + 2 + 3}`). The infix dispatch
                        // below uses state_cat_src_idx =
                        // CollectionMarker.category_src_idx = the
                        // collection's RESULT category (e.g., Proc for
                        // PPar) — exactly the category whose operators
                        // (Add, Mul, ==, etc.) should fire. If no operator
                        // matches, the standard 0-cands fallthrough below
                        // advances to Unwinding-CollectionMarker → routes
                        // to CollectionLoop for close/sep/bare dispatch —
                        // preserving the close-on-`}` and sep-on-`|`
                        // semantics. The marker-skip remains for RuleAt /
                        // MixfixMarker / OptionalGroupAt because those
                        // indicate mid-rule contexts where the next tokens
                        // are rule-internal literals.
                        //
                        // F1 follow-up Cluster B (2026-05-10): `MixfixMarker`
                        // REMOVED from this skip list. Mixfix inner operands
                        // must allow infix/postfix extension (e.g.,
                        // `1 ? 3! : 0` requires `!` to bind to `3` BEFORE
                        // the mixfix advances to consume `:`). The InfixLoop
                        // dispatch reads state_cat_src_idx from the marker
                        // (= result_src_idx of the mixfix rule, which is the
                        // operand's category for traditional mixfix shapes).
                        // If no candidate matches, cands is empty and we
                        // fall through to Unwinding-MixfixMarker, which
                        // routes to MixfixLiteralRun for the next
                        // separator/operand transition.
                        if let Some(node) = frontier_top {
                            match node.symbol.kind {
                                mettail_prattail::wpda_runtime::SymbolKind::RuleAt(_)
                                | mettail_prattail::wpda_runtime::SymbolKind::OptionalGroupAt(_) => {
                                    // Opt-Group: an OptionalGroupAt marker
                                    // indicates we're mid-group; defer to
                                    // Unwinding so the OptionalGroup state
                                    // resumes at the recorded sub_pos.
                                    return WpdaStepAction::Advance(WpdaState::Unwinding);
                                }
                                mettail_prattail::wpda_runtime::SymbolKind::CollectionMarker => {
                                    // Plan B (F5 close/sep filter, 2026-05-11):
                                    // when frontier_top is CollectionMarker, only
                                    // proceed with infix/postfix/mixfix dispatch
                                    // if the next token is actually an operator
                                    // candidate. If the next token is the
                                    // collection's close or separator, skip
                                    // infix dispatch immediately — falling
                                    // through to Unwinding-CollectionMarker
                                    // routes to CollectionLoop which handles
                                    // close/sep/bare correctly.
                                    //
                                    // Without this gating, the F5 fix's removal
                                    // of CollectionMarker from the skip list
                                    // causes Fork branches that diverge on
                                    // collection_stack depth, leading to
                                    // "builder result was empty" failures and
                                    // degenerate AST (e.g., `{1+2+3}` → ["3"]).
                                    let result_src_idx = node.symbol.category_src_idx;
                                    let rule_idx = node.symbol.rule_index_in_category;
                                    let slot_idx = node.symbol.bp.unwrap_or(0u8);
                                    let close_sep: Option<(&'static str, &'static str)> = {
                                        let result_src_idx = result_src_idx;
                                        let rule_idx = rule_idx;
                                        let slot_idx = slot_idx;
                                        #collection_close_sep_lookup
                                    };
                                    if let Some((close, sep)) = close_sep {
                                        // #307 ROOT-F G2 site-3 (2026-06-11):
                                        // close/sep DETECTION is edge
                                        // MEMBERSHIP over the complete
                                        // alternative set. The reroute stays
                                        // SINGLE (round-2 D-C: longest-match
                                        // lexing orders multi-char closes as
                                        // the primary, so a live close/sep on
                                        // a secondary alternative with a
                                        // live primary operand is
                                        // unrealizable in shipped grammars;
                                        // if a future grammar realizes it,
                                        // BOTH routes must be forked).
                                        let token_text = tokens.peek_text(_pos).unwrap_or("");
                                        let __hit = token_text == close
                                            || token_text == sep
                                            || tokens
                                                .peek_alternatives(_pos)
                                                .iter()
                                                .any(|a| a.text == close || a.text == sep);
                                        if __hit {
                                            return WpdaStepAction::Advance(WpdaState::Unwinding);
                                        }
                                    }
                                    // Otherwise fall through to infix dispatch
                                    // below — the F5 fix behavior for genuine
                                    // operator extension of the current element.
                                }
                                _ => {}
                            }
                        }
                        // Stage 3.18 / Fixes #17+#20 (Cluster 3, Mechanism γ,
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
                        #lex_fork_infix_dispatch
                        let token_text = tokens.peek_text(_pos).unwrap_or("");
                        let _ = token_text;

                        let mut __cands: Vec<
                            mettail_prattail::wpda_walker::ForkBranch<
                                __DwW,
                            >,
                        > = Vec::new();

                        // Infix tier (BP_TIER_INFIX = 0.00).
                        if let Some((l_bp, r_bp, result_src, rule_idx)) =
                            #infix_loop_dispatch
                        {
                            if l_bp >= *cur_bp {
                                let new_state =
                                    if result_src != state_cat_src_idx {
                                        // D-strings fix (2026-05-13): pass r_bp
                                        // as the sub-parse's `inner_cur_bp` so
                                        // the cross-cat operand sub-parse
                                        // enforces the outer Pratt precedence
                                        // (e.g. `Str < Str : Bool` at r_bp=7
                                        // prevents `==` at l_bp=2 from leaking
                                        // into the RHS sub-parse).
                                        WpdaState::CrossCatDelegate {
                                            source_src_idx: state_cat_src_idx,
                                            inner_cur_bp: r_bp,
                                        }
                                    } else {
                                        WpdaState::PrefixDispatch {
                                            pos: tokens.next_pos(_pos, 0).unwrap_or(_pos + 1),
                                            cur_bp: r_bp,
                                        }
                                    };
                                __cands.push(
                                    mettail_prattail::wpda_walker::ForkBranch {
                                        symbol: StackSymbolV2::rule_at(
                                            result_src, rule_idx, 0, Some(*cur_bp),
                                        )
                                        .with_kind_return(),
                                        weight: lex_w(
                                            mettail_prattail::automata::lex_weight::BP_TIER_INFIX,
                                            result_src, rule_idx,
                                        ),
                                        new_state,
                                        action_kind:
                                            mettail_prattail::wpda_walker::ForkActionKind::Push,
                                    },
                                );
                            }
                        }

                        // Postfix tier (BP_TIER_POSTFIX = 0.10).
                        // F1 fix (2026-05-10): new_state must be Unwinding, not InfixLoop.
                        // Postfix has no RHS to parse, so the Return symbol it pushes must
                        // be popped immediately to fire the action. Going to InfixLoop
                        // instead leaves the Return on the GSS while subsequent operator
                        // dispatches push more symbols on top — the action then fires in
                        // the wrong order (after the surrounding operator's action), with
                        // wrong types and wrong values on the builder stack. Unwinding
                        // pops the Return → fires the action → transitions to
                        // InfixLoop { cur_bp: outer_bp } via the standard Return-pop path
                        // at engine_impl.rs:357-360.
                        if let Some((l_bp, result_src, rule_idx)) =
                            #postfix_dispatch
                        {
                            if l_bp >= *cur_bp {
                                __cands.push(
                                    mettail_prattail::wpda_walker::ForkBranch {
                                        symbol: StackSymbolV2::rule_at(
                                            result_src, rule_idx, 0, Some(*cur_bp),
                                        )
                                        .with_kind_return(),
                                        weight: lex_w(
                                            mettail_prattail::automata::lex_weight::BP_TIER_POSTFIX,
                                            result_src, rule_idx,
                                        ),
                                        new_state: WpdaState::Unwinding,
                                        action_kind:
                                            mettail_prattail::wpda_walker::ForkActionKind::Push,
                                    },
                                );
                            }
                        }

                        // Mixfix tier (BP_TIER_MIXFIX = 0.20).
                        // #307 ROOT-A D1/D2 (2026-06-11; FV:
                        // MixfixLiteralAccounting.accounting_gap): the trigger
                        // previously dispatched the part-0 OPERAND directly
                        // (PrefixDispatch), skipping the part's PRECEDING
                        // literals (POutput's "(") — the part-0 accounting
                        // gap. It now enters the pre-operand literal run
                        // (kind=2), which consumes parts[0].preceding by
                        // membership-checked steps and then dispatches the
                        // operand. Empty preceding (Tern/PAmb) passes through
                        // with zero consumes (empty_pre_passthrough). The
                        // state is pos-less: every entry path (singleton
                        // ConsumeAndPush, engine Fork{consume_trigger:true},
                        // lex-fork next_pos child allocation) advances
                        // cursor.pos past the trigger BEFORE it activates.
                        if let Some((l_bp, result_src, rule_idx)) =
                            #mixfix_dispatch
                        {
                            if l_bp >= *cur_bp {
                                __cands.push(
                                    mettail_prattail::wpda_walker::ForkBranch {
                                        symbol: StackSymbolV2::mixfix_marker(
                                            result_src, rule_idx, 0,
                                        ),
                                        weight: lex_w(
                                            mettail_prattail::automata::lex_weight::BP_TIER_MIXFIX,
                                            result_src, rule_idx,
                                        ),
                                        new_state: WpdaState::MixfixLiteralRun {
                                            result_src_idx: result_src,
                                            rule_idx,
                                            completed_idx: 0,
                                            kind: 2,
                                            sub_pos: 0,
                                        },
                                        action_kind:
                                            mettail_prattail::wpda_walker::ForkActionKind::Push,
                                    },
                                );
                            }
                        }

                        // C1-M (WALK-S2, 2026-05-28): pre-fork MIXFIX ternary
                        // absorption trigger. Mixfix operators (`Tern`,
                        // `c "?" t ":" e`, right-recursive in the else slot)
                        // enter the mixfix tier above (pushing a MixfixMarker
                        // then a PrefixDispatch for the inner operand) and
                        // NEVER re-iterate to the InfixLoop singleton (mixfix
                        // associativity is hard-coded Left; plan D2/V5), so the
                        // singleton fast-path below cannot reach them.
                        // Intercept HERE — after `__cands` is built (which now
                        // holds the MixfixMarker candidate), before the
                        // singleton-vs-fork branch — for the LEADING mixfix-tier
                        // candidate: if it is the canonical iterative-eligible
                        // op for its trigger (`iter_eligible_<cat>` → Some) AND
                        // mixfix AND a forward peek confirms a deterministic
                        // >= 2-level ternary chain, emit `IterativeChainAbsorb`
                        // with `new_state = Unwinding` and SUPPRESS the fork
                        // (the MixfixMarker push is bypassed by the early
                        // `return`). The peek proves the region is a single
                        // ternary-shape run, so the normal mixfix descent would
                        // only re-walk the (about-to-be-absorbed) interior.
                        // `_pos` is ON the trigger (`?`); the head cond c0
                        // (parsed at `_pos - 1`) is on `cursor.sppf_stack_id`.
                        // On peek-failure this block is inert and control falls
                        // through to the unchanged `match __cands.len()` (other
                        // languages' mixfix ops won't have `Some(spec)` — the
                        // `right_recursive_tail` + exact-shape gate in
                        // `is_iterative_candidate` restricts eligibility to
                        // Tern-shaped ops — so they are bit-identical).
                        if let Some((_pmx_l_bp, _pmx_result_src, _pmx_rule_idx)) =
                            #mixfix_dispatch
                        {
                            if _pmx_l_bp >= *cur_bp {
                                let symbol_rs = _pmx_result_src;
                                let symbol_ri = _pmx_rule_idx;
                                let _pmx_spec: Option<mettail_prattail::binding_power::IterAbsorbSpec> =
                                    #iter_eligible_dispatch;
                                if let Some(spec) = _pmx_spec {
                                    if spec.is_mixfix
                                        && mettail_prattail::wpda_walker::peek_ternary_chain(
                                            tokens,
                                            _pos,
                                            spec.trigger,
                                            spec.sep,
                                            2,
                                        )
                                    {
                                        return WpdaStepAction::IterativeChainAbsorb {
                                            symbol: StackSymbolV2::rule_at(
                                                _pmx_result_src,
                                                _pmx_rule_idx,
                                                0,
                                                Some(*cur_bp),
                                            )
                                            .with_kind_return(),
                                            weight: lex_w(
                                                mettail_prattail::automata::lex_weight::BP_TIER_MIXFIX,
                                                _pmx_result_src,
                                                _pmx_rule_idx,
                                            ),
                                            new_state: WpdaState::Unwinding,
                                            spec,
                                        };
                                    }
                                }
                            }
                        }

                        // C1-R (WALK-S1, 2026-05-28): pre-fork right-assoc
                        // absorption trigger. Right-associative binary
                        // operators (`^`) recurse via the RHS sub-parse and
                        // NEVER re-iterate to the InfixLoop singleton (plan
                        // D2), so the left-assoc singleton fast-path below
                        // can't reach them. Intercept HERE — after `__cands`
                        // is built, before the singleton-vs-fork branch — for
                        // the LEADING infix-tier candidate: if it is the
                        // canonical iterative-eligible op for its terminal
                        // (`iter_eligible_<cat>` → Some) AND right-assoc AND a
                        // forward peek confirms a deterministic >= 5-atom
                        // (>= 4 remaining after the head) chain of that
                        // op-kind, emit `IterativeChainAbsorb` with
                        // `new_state = Unwinding` and SUPPRESS the fork. The
                        // peek proves the region is a single-op-kind run, so a
                        // fork at the chain head would only spawn cursors that
                        // either can't complete the chain or redundantly
                        // re-walk the (already-absorbed) interior. `_pos` is
                        // ON the operator; the head atom (parsed at `_pos - 1`)
                        // is on `cursor.sppf_stack_id`. On peek-failure this
                        // block is inert and control falls through to the
                        // unchanged `match __cands.len()` (non-chain /
                        // short-chain workloads bit-identical). LEFT-assoc
                        // (AddInt) is NOT routed here — it keeps the existing
                        // singleton path (minimal blast radius).
                        if let Some((_pf_l_bp, _pf_r_bp, _pf_result_src, _pf_rule_idx)) =
                            #infix_loop_dispatch
                        {
                            if _pf_l_bp >= *cur_bp {
                                let symbol_rs = _pf_result_src;
                                let symbol_ri = _pf_rule_idx;
                                let _pf_spec: Option<mettail_prattail::binding_power::IterAbsorbSpec> =
                                    #iter_eligible_dispatch;
                                if let Some(spec) = _pf_spec {
                                    // S1 scope: right-assoc binary only. (S2
                                    // adds `|| spec.is_mixfix` for ternary.)
                                    if spec.assoc_right
                                        && mettail_prattail::wpda_walker::peek_binary_chain(
                                            tokens, _pos, 5,
                                        )
                                    {
                                        return WpdaStepAction::IterativeChainAbsorb {
                                            symbol: StackSymbolV2::rule_at(
                                                _pf_result_src,
                                                _pf_rule_idx,
                                                0,
                                                Some(*cur_bp),
                                            )
                                            .with_kind_return(),
                                            weight: lex_w(
                                                mettail_prattail::automata::lex_weight::BP_TIER_INFIX,
                                                _pf_result_src,
                                                _pf_rule_idx,
                                            ),
                                            new_state: WpdaState::Unwinding,
                                            spec,
                                        };
                                    }
                                }
                            }
                        }

                        match __cands.len() {
                            0 => {
                                // No tier matched — fall through to Unwinding.
                                WpdaStepAction::Advance(WpdaState::Unwinding)
                            }
                            1 => {
                                // Singleton fast-path: only one tier matched,
                                // so emit ConsumeAndPush directly. Preserves
                                // zero-overhead dispatch for shipped grammars
                                // (typical case — only one operator at any
                                // given (token, l_bp >= cur_bp) pair).
                                //
                                // Phase F.13 chain_10000 Exp 6 Substage 6b
                                // (2026-05-26): if the singleton candidate
                                // refers to an iterative-eligible operator
                                // AND its (terminal, l_bp) is unique in the
                                // dispatched category (per Plan A invariant
                                // I1, codegen-checked in `iter_eligible_<cat>`),
                                // route through `IterativeChainAbsorb`
                                // instead so the per-chain Return RuleAt
                                // push is shared across all `+` iterations.
                                // First iteration pushes; subsequent
                                // iterations skip the push via the walker
                                // arm's chain-extension witness (Plan A
                                // invariant I2). RHS sub-parse is dispatched
                                // by the `InfixChainIterative` engine arm.
                                let b = __cands.into_iter().next().unwrap();
                                let symbol_rs = b.symbol.category_src_idx;
                                let symbol_ri = b.symbol.rule_index_in_category;
                                let iter_lookup: Option<mettail_prattail::binding_power::IterAbsorbSpec> = #iter_eligible_dispatch;
                                if let Some(spec) = iter_lookup {
                                    // C1: only LEFT-associative binary operators
                                    // absorb via this singleton fast-path (the
                                    // existing iterative chain path). Right-assoc
                                    // and mixfix operators recurse / enter the
                                    // mixfix tier and never re-iterate to a
                                    // singleton, so they are handled by the
                                    // pre-fork absorption trigger below; here
                                    // they fall through to ConsumeAndPush.
                                    if !spec.assoc_right && !spec.is_mixfix {
                                        return WpdaStepAction::IterativeChainAbsorb {
                                            symbol: b.symbol,
                                            weight: b.weight,
                                            new_state: WpdaState::InfixChainIterative {
                                                result_src_idx: symbol_rs,
                                                rule_idx: symbol_ri,
                                                outer_bp: *cur_bp,
                                                rhs_bp: spec.right_bp,
                                            },
                                            spec,
                                        };
                                    }
                                }
                                WpdaStepAction::ConsumeAndPush {
                                    symbol: b.symbol,
                                    weight: b.weight,
                                    new_state: b.new_state,
                                    // Phase F.8: infix-tier singleton
                                    // discards the operator token at the
                                    // SPPF layer (the operator's LHS/RHS
                                    // terms are already on the SPPF stack).
                                    trigger_mode: mettail_prattail::wpda_walker::TriggerMode::Discard,
                                }
                            }
                            _ => {
                                // Multi-tier ambiguity (G5: e.g. infix and
                                // postfix sharing a token at the same
                                // l_bp >= cur_bp) — emit a Fork. Lex-min
                                // picks the lower BP tier on ties.
                                WpdaStepAction::Fork {
                                    branches: __cands,
                                    consume_trigger: true,
                                }
                            }
                        }
                    }
                    WpdaState::InfixChainIterative {
                        result_src_idx: _result_src_idx,
                        rule_idx: _rule_idx,
                        outer_bp: _outer_bp,
                        rhs_bp,
                    } => {
                        // Phase F.13 chain_10000 Exp 6 Substage 6b
                        // (2026-05-26): dispatch the RHS sub-parse at
                        // `cur_bp: rhs_bp` per Plan A invariant I3.
                        //
                        // STRUCTURAL NOTE (Substage 6b implementation
                        // judgment): the user's plan suggested a
                        // chain-continuation probe here that peeks the
                        // NEXT token for another iterative-eligible
                        // operator. That probe would fire BEFORE the
                        // RHS is parsed (the next token after `+` is
                        // the RHS literal `2`, not another `+`), so
                        // the probe always yields zero candidates and
                        // the RHS would never be dispatched — the
                        // chain would terminate after the first
                        // iteration. The structurally-correct flow is:
                        //
                        //   1. InfixLoop singleton emits
                        //      `IterativeChainAbsorb` (this commit's
                        //      step 2 change).
                        //   2. Walker consumes `+`, pushes Return
                        //      RuleAt on first iteration (elides on
                        //      subsequent iterations per invariant I2),
                        //      sets state = `InfixChainIterative`.
                        //   3. THIS ARM dispatches RHS sub-parse via
                        //      `PrefixDispatch { cur_bp: rhs_bp }`.
                        //   4. RHS completes; Unwinding-Return pops
                        //      the Return symbol → InfixLoop {
                        //      cur_bp: outer_bp } via the standard
                        //      Return-pop path (engine_impl.rs:457-464).
                        //   5. InfixLoop re-enters; singleton
                        //      fast-path re-detects iterative-
                        //      eligible operator and emits
                        //      IterativeChainAbsorb — walker's chain-
                        //      extension elision (invariant I2)
                        //      avoids the second push.
                        //
                        // Per-chain GSS-push elision is the entire
                        // win: O(N) chain steps → O(1) Return frames.
                        // Action fires once on chain terminate via the
                        // standard Unwinding-Return → Pop path with
                        // all accumulated RHS SPPF nodes attached.
                        WpdaStepAction::Advance(WpdaState::PrefixDispatch {
                            pos: _pos,
                            cur_bp: *rhs_bp,
                        })
                    }
                    WpdaState::CollectionLoop {
                        result_src_idx,
                        rule_idx,
                        element_src_idx: _element_src_idx,
                        outer_bp: _outer_bp,
                        accumulator_id: _accumulator_id,
                        slot_idx,
                        kv_phase,
                    } => {
                        // Phase 4: dispatch on close / sep / element.
                        // Phase 4 #1.B (2026-05-11): slot_idx in scope
                        // for 3-tuple-keyed (close, sep) lookup in
                        // `emit_collection_loop_arm`.
                        // Phase 4 #5b (2026-05-12): kv_phase in scope
                        // for HashMap 3-phase dispatch.
                        #collection_loop_body
                    }
                    WpdaState::MixfixContinuation {
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
                        // L12 follow-up B6 (2026-05-07): widened tuple.
                        // mixfix_part returns
                        //   Option<(operand_src, preceding, following)>
                        // where preceding/following are &[&str].
                        // The MixfixContinuation path uses operand_src to
                        // route the sub-parse; preceding/following are
                        // consumed by Unwinding-MixfixMarker and
                        // MixfixLiteralRun (when needed).
                        match mixfix_part(*result_src_idx, *rule_idx, *completed_idx) {
                            Some((operand_src_idx, _preceding, _following)) => {
                                WpdaStepAction::ReplaceAndPush {
                                    replace_symbol: StackSymbolV2::mixfix_marker(
                                        *result_src_idx,
                                        *rule_idx,
                                        *completed_idx,
                                    ),
                                    push_symbol: StackSymbolV2::category_entry(
                                        operand_src_idx,
                                    ),
                                    weight: lex_one(),
                                    new_state: WpdaState::PrefixDispatch {
                                        pos: _pos,
                                        cur_bp: 0,
                                    },
                                }
                            }
                            None => WpdaStepAction::Error(format!(
                                "mixfix part {} not found for (result={}, rule={})",
                                completed_idx, result_src_idx, rule_idx
                            )),
                        }
                    }
                    WpdaState::MixfixLiteralRun {
                        result_src_idx,
                        rule_idx,
                        completed_idx,
                        kind,
                        sub_pos,
                    } => {
                        // L12 follow-up B6 step 3 (2026-05-07): walk
                        // postfix-mixfix per-part literal sequences.
                        // kind=0: consume following_terminals after the
                        //         just-completed operand `completed_idx`.
                        // kind=1: consume preceding_terminals before the
                        //         next operand `completed_idx + 1`.
                        let part = mixfix_part(
                            *result_src_idx, *rule_idx, *completed_idx,
                        );
                        let parts_len = match mixfix_parts_len(
                            *result_src_idx, *rule_idx,
                        ) {
                            Some(n) => n,
                            None => return WpdaStepAction::Error(format!(
                                "mixfix_parts_len(result={}, rule={}) returned None — \
                                 codegen invariant violated",
                                result_src_idx, rule_idx,
                            )),
                        };
                        // #307 ROOT-A D3 (2026-06-11; FV:
                        // MixfixLiteralAccounting.{checked_run_iff_spells,
                        // primary_equality_loses, unchecked_accepts_mismatch,
                        // checked_never_fabricates, fork_completeness}):
                        // membership-checked literal consume. A rule literal
                        // matches iff its TEXT equals some out-edge of the
                        // position (primary OR lattice alternative — single-
                        // token primary equality would lose multi-length
                        // lattice parses, e.g. the `-3` node). The consume
                        // advances along the MATCHED edge's target, carried
                        // explicitly (the generic advance is alt-0-hardwired).
                        // No match (incl. vacuously at edge-less EOF/orphan
                        // nodes — lattice peek SYNTHESIZES Some(Eof), never
                        // None) ⇒ pure Error before any mutation
                        // (advance-or-die). Multiple distinct targets (soft-
                        // fail orphan duplication only) ⇒ Fork, never
                        // pick-one. The PREVIOUS code consumed UNCHECKED
                        // (`_expected` unused) — stealing enclosing
                        // delimiters or fabricating positions: the ROOT-A
                        // defect (rhocalc `x!(0)` never parsed).
                        fn __mixfix_literal_targets(
                            tokens: &dyn mettail_prattail::wpda_runtime::WpdaTokenSource,
                            pos: usize,
                            expected: &str,
                        ) -> Vec<usize> {
                            let mut targets: Vec<usize> = Vec::with_capacity(2);
                            if tokens.peek_text(pos) == Some(expected) {
                                if let Some(np) = tokens.next_pos(pos, 0) {
                                    targets.push(np);
                                }
                            }
                            for (i, alt) in tokens.peek_alternatives(pos).iter().enumerate() {
                                if alt.text == expected {
                                    if let Some(np) = tokens.next_pos(pos, i + 1) {
                                        if !targets.contains(&np) {
                                            targets.push(np);
                                        }
                                    }
                                }
                            }
                            targets
                        }
                        macro_rules! __checked_literal_consume {
                            ($expected:expr, $next_state:expr) => {{
                                let __expected: &str = $expected;
                                let __next_state = $next_state;
                                let __targets =
                                    __mixfix_literal_targets(tokens, _pos, __expected);
                                match __targets.len() {
                                    0 => WpdaStepAction::Error(format!(
                                        "mixfix literal mismatch: expected {:?} at pos {} \
                                         (rule {}:{}) — no lattice edge matches",
                                        __expected, _pos, result_src_idx, rule_idx,
                                    )),
                                    1 => WpdaStepAction::ConsumeAtAndReplace {
                                        symbol: StackSymbolV2::mixfix_marker(
                                            *result_src_idx,
                                            *rule_idx,
                                            *completed_idx,
                                        ),
                                        weight: lex_one(),
                                        new_state: __next_state,
                                        next_pos: __targets[0],
                                    },
                                    _ => WpdaStepAction::Fork {
                                        branches: __targets
                                            .iter()
                                            .map(|np| {
                                                mettail_prattail::wpda_walker::ForkBranch {
                                                    symbol: StackSymbolV2::mixfix_marker(
                                                        *result_src_idx,
                                                        *rule_idx,
                                                        *completed_idx,
                                                    ),
                                                    weight: lex_one(),
                                                    new_state: __next_state.clone(),
                                                    action_kind:
                                                        mettail_prattail::wpda_walker::ForkActionKind::ConsumeAtAndReplace {
                                                            next_pos: *np,
                                                        },
                                                }
                                            })
                                            .collect(),
                                        consume_trigger: false,
                                    },
                                }
                            }};
                        }
                        match (*kind, part) {
                            // #307 ROOT-A D1: the NEW pre-operand literal run
                            // — consumes parts[completed_idx].PRECEDING before
                            // the operand dispatch; the marker stays at
                            // completed_idx (the bump is owed only after the
                            // operand completes). Empty preceding (Tern/PAmb)
                            // passes straight through to the operand
                            // (empty_pre_passthrough: zero blast radius).
                            (2, Some((operand_src_idx, preceding, _following))) => {
                                if (*sub_pos as usize) < preceding.len() {
                                    let expected = preceding[*sub_pos as usize];
                                    __checked_literal_consume!(
                                        expected,
                                        WpdaState::MixfixLiteralRun {
                                            result_src_idx: *result_src_idx,
                                            rule_idx: *rule_idx,
                                            completed_idx: *completed_idx,
                                            kind: 2,
                                            sub_pos: sub_pos + 1,
                                        }
                                    )
                                } else if operand_src_idx == *result_src_idx {
                                    // Part-0 operand under the marker — the
                                    // shipped convention, correct exactly when
                                    // the operand category equals the result
                                    // category (all shipped part-0 rules:
                                    // POutput q:Proc→Proc, PAmb, Tern); the
                                    // marker is the frontier top, so
                                    // PrefixDispatch derives the dispatch
                                    // category from it.
                                    WpdaStepAction::Advance(WpdaState::PrefixDispatch {
                                        pos: _pos,
                                        cur_bp: 0,
                                    })
                                } else {
                                    // Cross-category part-0 operand: explicit
                                    // CategoryEntry push (the kind=1 proven
                                    // pattern) — closes the latent
                                    // wrong-category hole; the marker is NOT
                                    // bumped (bp counts completed operands).
                                    WpdaStepAction::Push {
                                        symbol: StackSymbolV2::category_entry(
                                            operand_src_idx,
                                        ),
                                        weight: lex_one(),
                                        new_state: WpdaState::PrefixDispatch {
                                            pos: _pos,
                                            cur_bp: 0,
                                        },
                                    }
                                }
                            }
                            (0, Some((_, _preceding, following))) => {
                                if (*sub_pos as usize) < following.len() {
                                    // Consume following[sub_pos] — CHECKED.
                                    let expected = following[*sub_pos as usize];
                                    __checked_literal_consume!(
                                        expected,
                                        WpdaState::MixfixLiteralRun {
                                            result_src_idx: *result_src_idx,
                                            rule_idx: *rule_idx,
                                            completed_idx: *completed_idx,
                                            kind: 0,
                                            sub_pos: sub_pos + 1,
                                        }
                                    )
                                } else if *completed_idx + 1 == parts_len {
                                    // Last operand done; Pop the marker.
                                    WpdaStepAction::Pop {
                                        weight: lex_one(),
                                        new_state: WpdaState::InfixLoop { cur_bp: 0 },
                                    }
                                } else {
                                    // Transition to kind=1 to consume
                                    // preceding_terminals of the next operand.
                                    WpdaStepAction::Advance(
                                        WpdaState::MixfixLiteralRun {
                                            result_src_idx: *result_src_idx,
                                            rule_idx: *rule_idx,
                                            completed_idx: *completed_idx,
                                            kind: 1,
                                            sub_pos: 0,
                                        },
                                    )
                                }
                            }
                            (1, _) => {
                                let next_part = mixfix_part(
                                    *result_src_idx, *rule_idx, *completed_idx + 1,
                                );
                                match next_part {
                                    Some((operand_src_idx, preceding, _following)) => {
                                        if (*sub_pos as usize) < preceding.len() {
                                            // Consume preceding[sub_pos] — CHECKED (#307 D3).
                                            let expected = preceding[*sub_pos as usize];
                                            __checked_literal_consume!(
                                                expected,
                                                WpdaState::MixfixLiteralRun {
                                                    result_src_idx: *result_src_idx,
                                                    rule_idx: *rule_idx,
                                                    completed_idx: *completed_idx,
                                                    kind: 1,
                                                    sub_pos: sub_pos + 1,
                                                }
                                            )
                                        } else {
                                            // All literals consumed; push the next
                                            // operand's CategoryEntry.
                                            WpdaStepAction::ReplaceAndPush {
                                                replace_symbol: StackSymbolV2::mixfix_marker(
                                                    *result_src_idx,
                                                    *rule_idx,
                                                    *completed_idx + 1,
                                                ),
                                                push_symbol: StackSymbolV2::category_entry(
                                                    operand_src_idx,
                                                ),
                                                weight: lex_one(),
                                                new_state: WpdaState::PrefixDispatch {
                                                    pos: _pos,
                                                    cur_bp: 0,
                                                },
                                            }
                                        }
                                    }
                                    None => WpdaStepAction::Error(format!(
                                        "mixfix part {} not found for (result={}, rule={})",
                                        completed_idx + 1, result_src_idx, rule_idx,
                                    )),
                                }
                            }
                            _ => WpdaStepAction::Error(format!(
                                "MixfixLiteralRun: invalid kind={} or missing part \
                                 for (result={}, rule={}, completed_idx={})",
                                kind, result_src_idx, rule_idx, completed_idx,
                            )),
                        }
                    }
                    WpdaState::CollectionOpenParen {
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
                            Some("(") => WpdaStepAction::Consume {
                                weight: lex_one(),
                                new_state: WpdaState::PrefixDispatch {
                                    pos: tokens.next_pos(_pos, 0).unwrap_or(_pos + 1),
                                    cur_bp: 0,
                                },
                            },
                            other => WpdaStepAction::Error(format!(
                                "expected `(` after collection-open keyword at pos {}, found {:?}",
                                _pos, other
                            )),
                        }
                    }
                    WpdaState::BinderRule {
                        result_src_idx,
                        rule_idx,
                        body_src_idx: _body_src_idx,
                        outer_bp,
                    } => {
                        let _ = (result_src_idx, rule_idx, outer_bp);
                        // Phase 5: per-position dispatch for binder rules.
                        #binder_rule_body
                    }
                    WpdaState::BinderListLoop {
                        result_src_idx,
                        rule_idx,
                        body_src_idx,
                        outer_bp,
                        marker_pos,
                        next_pos,
                        sub_pos,
                    } => {
                        let _ = (
                            result_src_idx,
                            rule_idx,
                            body_src_idx,
                            outer_bp,
                            marker_pos,
                            next_pos,
                            sub_pos,
                        );
                        // Phase 5b: ^[xs] binder list loop.
                        // B8 (2026-05-08): sub_pos indexes per-iteration
                        // inner walk for Class 3 ZIP-MAP-SEP. PNew-style
                        // rules dispatch at sub_pos=0 only.
                        #binder_list_loop_body
                    }
                    WpdaState::CrossCatDelegate {
                        source_src_idx,
                        inner_cur_bp,
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
                        //
                        // D-strings fix (2026-05-13): use `*inner_cur_bp`
                        // (set by the emission site) as the sub-parse's
                        // cur_bp, NOT a hardcoded 0. For cross-cat infix
                        // RHS dispatch (`engine_impl.rs:920-925`), the
                        // emitter passes `r_bp` so the sub-parse rejects
                        // lower-precedence operators leaking in from the
                        // enclosing Pratt context. For PrefixDispatch
                        // CrossCatProjection/ImplicitCast/CrossCatPrefixUnary
                        // arms, the emitter passes 0 (fresh-operand
                        // semantics). The outer cur_bp is restored via the
                        // wrapping `Return(..., bp=Some(outer_cur_bp))`
                        // symbol when that Return is later popped, not via
                        // this state.
                        WpdaStepAction::Push {
                            symbol: StackSymbolV2::category_entry(*source_src_idx),
                            weight: lex_one(),
                            new_state: WpdaState::PrefixDispatch {
                                pos: _pos,
                                cur_bp: *inner_cur_bp,
                            },
                        }
                    }
                    WpdaState::AmbiguityFanout { .. } => WpdaStepAction::Error(
                        "engine.step called with AmbiguityFanout; walker should \
                         drive this state via step_fanout"
                            .to_string(),
                    ),
                    WpdaState::OptionalGroup {
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
                        // `optional_group_body` collapses to `WpdaStepAction::Idle`
                        // and the destructured fields are unused. Suppress the
                        // unused-variable warnings via explicit no-op binds —
                        // these compile to nothing in optimized builds.
                        let _ = (result_src_idx, rule_idx, group_idx, sub_pos, outer_bp);
                        #optional_group_body
                    }
                    WpdaState::GroupingClosePreservingInner { inner_cat_src_idx } => {
                        // Plan A (paren+postfix redesign, 2026-05-11):
                        // top is now the GroupingMarker (the inner CategoryEntry
                        // was just popped via the Unwinding-CategoryEntry
                        // lookahead-conditional branch). Demand `)`,
                        // ConsumeAndReplace the GroupingMarker on top with
                        // a CategoryEntry of the inner cat so subsequent
                        // InfixLoop dispatch uses the inner-cat tables.
                        //
                        // The GroupingMarker's `bp` field carries outer_bp
                        // (saved cur_bp at the open paren — established by
                        // the codegen invariant in StackSymbolV2::grouping_marker).
                        // Restore that BP for the post-`)` InfixLoop.
                        if let Some(node) = frontier_top {
                            if node.symbol.kind == mettail_prattail::wpda_runtime::SymbolKind::GroupingMarker {
                                let outer_bp = node.symbol.bp.expect(
                                    "GroupingMarker invariant: bp must be Some(outer_bp) — \
                                     saved cur_bp at the open paren"
                                );
                                return match tokens.peek_text(_pos) {
                                    Some(")") => WpdaStepAction::ConsumeAndReplace {
                                        symbol: StackSymbolV2::category_entry(*inner_cat_src_idx),
                                        weight: lex_one(),
                                        new_state: WpdaState::InfixLoop { cur_bp: outer_bp },
                                    },
                                    other => WpdaStepAction::Error(format!(
                                        "GroupingClosePreservingInner: expected `)` to close \
                                         grouping (preserving inner cat={}) at pos {}, found {:?}",
                                        inner_cat_src_idx, _pos, other,
                                    )),
                                };
                            }
                        }
                        WpdaStepAction::Error(format!(
                            "GroupingClosePreservingInner: expected GroupingMarker on top at \
                             pos {}, found {:?}",
                            _pos,
                            frontier_top.map(|n| n.symbol.kind),
                        ))
                    }
                    WpdaState::Saturating { .. } => WpdaStepAction::Idle,
                    WpdaState::Accepted | WpdaState::Error { .. } => WpdaStepAction::Idle,
                }
            }

            fn action_for(
                &self,
                src_idx: u16,
                rule_idx: u16,
            ) -> Option<&mettail_prattail::wpda_runtime::ActionEntry> {
                #action_for_body
            }

            // EP-P2 (Stage B): delegate the obligation-gate functions to the
            // generated module-level tables (beside WPDA_RULES).
            fn parikh_class_of(
                &self,
                kind: &mettail_prattail::automata::TokenKind,
            ) -> Option<u8> {
                Some(WPDA_PARIKH_CLASS_OF(kind))
            }

            fn parikh_must_mask(&self, cat: u16, rule: u16, pos: u8) -> u128 {
                WPDA_MUST_MASK(cat, rule, pos)
            }

            fn is_binder_internal_collection(
                &self,
                result_src_idx: u16,
                rule_idx: u16,
            ) -> bool {
                let _ = (result_src_idx, rule_idx);
                #is_binder_internal_collection_lookup
            }

            fn is_class3_collection_per_slot(
                &self,
                src_idx: u16,
                rule_idx: u16,
                slot_idx: u8,
            ) -> bool {
                let _ = (src_idx, rule_idx, slot_idx);
                #is_class3_collection_lookup
            }

            fn is_class3_inner_marker(
                &self,
                src_idx: u16,
                rule_idx: u16,
                sub_pos: u8,
            ) -> bool {
                let _ = (src_idx, rule_idx, sub_pos);
                // B8 / Issue 2 (2026-05-10): per-(src, rule, sub_pos)
                // lookup. Returns true ONLY when the OptionalGroupAt
                // belongs to a Class 3 inner walk (not a genuine
                // *opt(...) OptionalGroup).
                #is_class3_inner_marker_lookup
            }

            fn kv_separator_for_collection(
                &self,
                result_src_idx: u16,
                rule_idx: u16,
                slot_idx: u8,
            ) -> Option<&'static str> {
                // Phase 4 #5b (2026-05-12): per-(src, rule, slot_idx)
                // lookup. Returns `Some(":")` (or user-overridden
                // literal) for HashMap collection slots and `None`
                // for Vec/HashBag/HashSet slots or unknown tuples.
                // Consumed by the walker's `set_cursor_inner_state`
                // to patch `WpdaState::CollectionLoop.kv_phase` from
                // cursor.collection_stack[acc_id].len() parity.
                #kv_separator_for_collection_lookup
            }

            fn collection_element_src_idx(
                &self,
                result_src_idx: u16,
                rule_idx: u16,
                slot_idx: u8,
            ) -> Option<u16> {
                // #307 TR ghost (2026-06-17): the declared element-category
                // src_idx per (result_src_idx, rule_idx, slot_idx). Reuses the
                // same per-rule lookup the CollectionLoop/CollectionOpenParen
                // arms use for cross-cat element redirect, now exposed to the
                // collection-element splice gate so a pre-wrap raw cross-cat
                // element Symbol is refuted at the source.
                let _ = (result_src_idx, rule_idx, slot_idx);
                #collection_element_src_lookup
            }

            fn cat_of_type_name(&self, name: &str) -> Option<u16> {
                // D8 fix (2026-05-13): map a Rust
                // `std::any::type_name::<T>()` string to the category
                // `src_idx` for `T`. Used by the walker's
                // `GroupingClosePreservingInner` resolution. The
                // emitted body covers both the wrapped enum form
                // (e.g. `mettail_languages::calculator::Bool`) and
                // the native payload form (e.g. `i64`, `bool`,
                // `f64`, `String`) for `![native] as Cat` categories
                // so both `push_term::<Cat>` and
                // `push_term::<NativeTy>` resolve correctly.
                #cat_of_type_name_body
            }

            fn min_terminal_span(&self, src_idx: u16, rule_idx: u16) -> u32 {
                // Pass-2c token-soundness backstop (2026-05-30): per-rule
                // count of literal terminals matched STRICTLY WITHIN the
                // rule's result-Symbol span (literals after the first param).
                // The realize-time filter rejects any packing whose Symbol
                // span leaves less slack than this — dropping token-unsound
                // fabricated-cast derivations on evidence (yield != span).
                #min_terminal_span_body
            }

            fn single_hop_coercion(&self, from_cat: u16, to_cat: u16) -> &[(u16, u16)] {
                // Sig-B Blocker-3 §2.3 (2026-06-01): grammar single-hop
                // coercion table — the `(target_cat, rule_idx)` of every
                // Pass-2a transparent projection / Pass-2c trigger-bearing
                // cast that bridges `from_cat → to_cat`. Mirrors the live
                // synthesis rule set EXACTLY. Empty when no grammar coercion
                // exists. The span-anchored splice consumes this to (a)
                // accept a category-incompatible body whose category is
                // one-hop-reachable to the cast's arg cat (§2.4a clause-4) and
                // (b) interpose the named coercion Symbol before the cast
                // fires (§2.4c).
                #single_hop_coercion_body
            }

            fn prefix_cast_into(&self, from_cat: u16, to_cat: u16) -> Option<u16> {
                // RC-B (2026-06-17): trigger-bearing prefix cast table — the
                // local rule index in `to_cat` of the `kw "(" a ")"` cast
                // `from_cat -> to_cat` (e.g. `BoolToInt`). The COMPLEMENT of
                // `single_hop_coercion` (which lists only span-0 supertype
                // injections). `None` when no such bracketed cast exists. The
                // walker re-validates every hit against `action_for` +
                // `min_terminal_span`.
                #prefix_cast_into_body
            }

            fn prefix_cast_keyword(&self, to_cat: u16, rule_idx: u16) -> Option<&'static str> {
                // RC-B (2026-06-17): the leading keyword literal of the
                // trigger-bearing prefix-cast rule `(to_cat, rule_idx)` (e.g.
                // `"int"` for `BoolToInt`, `"|"` for `Len`). The wrap synthesis
                // rejects a candidate whose keyword differs from the enclosing
                // `kw "(" .. ")"` frame's keyword, so a length operator is never
                // synthesized under the cast frame's `int` keyword.
                #prefix_cast_keyword_body
            }

            fn category_recognizes_operator(&self, cat: u16, token_text: &str) -> bool {
                #category_recognizes_operator_body
            }

            fn is_structural_open_delimiter(
                &self,
                kind: &mettail_prattail::automata::TokenKind,
                text: Option<&str>,
            ) -> bool {
                #structural_open_body
            }

            fn is_structural_close_delimiter(
                &self,
                kind: &mettail_prattail::automata::TokenKind,
                text: Option<&str>,
            ) -> bool {
                #structural_close_body
            }
        }
    }
}

fn emit_structural_delimiter_predicate_body(delimiters: &[String]) -> TokenStream {
    let delimiter_lits: Vec<&str> = delimiters.iter().map(String::as_str).collect();
    quote! {
        match kind {
            mettail_prattail::automata::TokenKind::Fixed(__s) => {
                match __s.as_str() {
                    #( #delimiter_lits => return true, )*
                    _ => {},
                }
            },
            _ => {},
        }
        match text {
            #( Some(#delimiter_lits) => true, )*
            _ => false,
        }
    }
}

fn emit_structural_delimiter_predicates(
    language: &LanguageDef,
    per_cat: &[Vec<GrammarRule>],
) -> (TokenStream, TokenStream) {
    let (opens, closes) = super::collection::collect_structural_delimiters(language, per_cat);
    let open_delimiters: Vec<String> = opens.into_iter().collect();
    let close_delimiters: Vec<String> = closes.into_iter().collect();
    (
        emit_structural_delimiter_predicate_body(&open_delimiters),
        emit_structural_delimiter_predicate_body(&close_delimiters),
    )
}

/// D8 fix (2026-05-13): emit the body of
/// `WpdaEngine::cat_of_type_name(name: &str) -> Option<u16>`.
///
/// Maps Rust `type_name` strings to the category's `src_idx`. Two
/// forms emitted per category:
///   1. Wrapped enum:   `std::any::type_name::<Cat>()`  (e.g.,
///      `mettail_languages::calculator::Bool`).
///   2. Native payload: `std::any::type_name::<NativeTy>()` when
///      the category declares `![native_ty] as Cat`.
///
/// The walker's `GroupingClosePreservingInner` resolution reads
/// `cursor.builder.top_term_type_name()` (the type_name of the
/// last-pushed `ActionArg::Term`) and calls this method to derive
/// the RESULT category of the inner expression.
fn emit_cat_of_type_name(language: &LanguageDef, categories: &[String]) -> TokenStream {
    let mut arms: Vec<TokenStream> = Vec::with_capacity(categories.len() * 2);
    for (i, cat_name) in categories.iter().enumerate() {
        let i_u16 = i as u16;
        let cat_ident: Ident =
            syn::parse_str(cat_name).expect("category name is a valid Rust identifier");
        arms.push(quote! {
            if name == std::any::type_name::<#cat_ident>() {
                return Some(#i_u16);
            }
        });
        if let Some(lang_type) = language
            .types
            .iter()
            .find(|t| t.name.to_string() == *cat_name)
        {
            if let Some(native_ty) = &lang_type.native_type {
                arms.push(quote! {
                    if name == std::any::type_name::<#native_ty>() {
                        return Some(#i_u16);
                    }
                });
            }
        }
    }
    quote! {
        {
            #(#arms)*
            None
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

/// Phase F.13 chain_10000 Exp 6 Substage 6b (2026-05-26): per-category
/// iter-eligible dispatch. Emits a `match state_cat_src_idx` calling
/// the per-category `iter_eligible_<cat>(symbol_rs, symbol_ri)` lookup.
/// Evaluates to `Option<(u8, u8)>` (left_bp, right_bp). Reads two free
/// vars from the surrounding scope:
/// - `state_cat_src_idx: u16` — same as in the InfixLoop dispatch.
/// - `symbol_rs: u16`, `symbol_ri: u16` — the candidate operator's
///   (result_src_idx, rule_index_in_category).
fn emit_iter_eligible_dispatch(categories: &[String]) -> TokenStream {
    let arms = categories.iter().enumerate().map(|(i, cat)| {
        let i_u16 = i as u16;
        let fn_ident = quote::format_ident!("iter_eligible_{}", cat.to_lowercase());
        quote! { #i_u16 => #fn_ident(symbol_rs, symbol_ri), }
    });
    quote! {
        {
            match state_cat_src_idx {
                #(#arms)*
                _ => None::<mettail_prattail::binding_power::IterAbsorbSpec>,
            }
        }
    }
}

/// Plan A (paren+postfix redesign, 2026-05-11): emit a per-category lookup
/// that answers "does this category recognize this token as an operator
/// (infix/postfix/mixfix)?". Used by the `Unwinding-CategoryEntry` arm's
/// lookahead-conditional GroupingClosePreservingInner branch to decide
/// whether to preserve the inner-cat dispatch context across a closing `)`.
///
/// Evaluates to `bool`. Reads three free vars from the surrounding scope:
/// - `inner_cat: u16` — the category whose tables to check.
/// - `next_tok: &str` — the token to check (typically `peek_text(_pos+1)`).
fn emit_category_recognizes_token_dispatch(categories: &[String]) -> TokenStream {
    let arms = categories.iter().enumerate().map(|(i, cat)| {
        let i_u16 = i as u16;
        let infix_fn = quote::format_ident!("infix_bp_{}", cat.to_lowercase());
        let postfix_fn = quote::format_ident!("postfix_bp_{}", cat.to_lowercase());
        let mixfix_fn = quote::format_ident!("mixfix_bp_{}", cat.to_lowercase());
        quote! {
            #i_u16 => {
                #infix_fn(next_tok).is_some()
                    || #postfix_fn(next_tok).is_some()
                    || #mixfix_fn(next_tok).is_some()
            }
        }
    });
    quote! {
        {
            match inner_cat {
                #(#arms,)*
                _ => false,
            }
        }
    }
}

/// Body for `WpdaEngine::category_recognizes_operator(cat, token_text)`.
///
/// This is the same grammar table used by the generated Pratt dispatch, exposed
/// to the walker for transparent-source continuation. Keeping the query in the
/// generated engine avoids walker-side token special cases.
fn emit_category_recognizes_operator_body(categories: &[String]) -> TokenStream {
    let arms = categories.iter().enumerate().map(|(i, cat)| {
        let i_u16 = i as u16;
        let infix_fn = quote::format_ident!("infix_bp_{}", cat.to_lowercase());
        let postfix_fn = quote::format_ident!("postfix_bp_{}", cat.to_lowercase());
        let mixfix_fn = quote::format_ident!("mixfix_bp_{}", cat.to_lowercase());
        quote! {
            #i_u16 => {
                #infix_fn(token_text).is_some()
                    || #postfix_fn(token_text).is_some()
                    || #mixfix_fn(token_text).is_some()
            }
        }
    });
    quote! {
        match cat {
            #(#arms,)*
            _ => false,
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
