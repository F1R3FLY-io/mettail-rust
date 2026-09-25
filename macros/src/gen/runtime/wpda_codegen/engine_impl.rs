//! Emits the per-language `impl WpdaEngine` body.
//!
//! Covers all WpdaState dispatch: Ready → PrefixDispatch seed, prefix arms
//! per atomic/binder/cross-cat rule, InfixLoop with Pratt BP, CollectionLoop
//! for sep/close, BinderRule per-position dispatch, CrossCatDelegate for
//! cross-cat projections, Unwinding for Pop chains, terminal Accepted/Error.
//! AmbiguityFanout is owned by the walker; if routed to `engine.step`, the
//! generated engine reports a structured error rather than panicking.

use mettail_ast::grammar::GrammarRule;
use mettail_ast::language::{AttributeValue, LanguageDef};
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
    // Task #10 item 1: the fork-emission ordinal collector — filled by the
    // prefix/paren emitters below as they emit (never re-derived from the
    // grammar model); `mod.rs` turns it into the module-level
    // `WPDA_FORK_EMISSION_ORDINAL` table beside the Parikh tables, and the
    // trait override emitted here delegates to that fn.
    fork_rows: &mut super::fork_emission::ForkEmissionOrdinalModel,
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

    // S1-FACTORING F1 (2026-07-12, plan scratchpad/zz_probes/
    // s1_factoring_plan.md §D F1): the ONE-per-expansion spine emission
    // bundle. With `forks::S1_FACTORING == false` the emission-effective
    // partition has zero groups, every stream/map in the bundle is empty,
    // and every consumer threads below emit byte-identically to the pre-F1
    // output (the F0 receipt discipline). With the const `true`: prefix.rs
    // emits one spine trigger branch per eligible group, binder.rs's
    // BinderRule match gains the `(cat, SPINE_ID, node_pos)` arms,
    // kind_dispatch's lex-alt surface emits group entries (A3), the lex-fork
    // weight stamps route through `__s1_spine_weight_rule` (AV5), and the
    // engine tables gain the spine rows (H9 poison `action_for` union rows,
    // A7 leading-trigger conjunction, min-span min-over-members,
    // `trigger_spine_owner` + A-1 `spine_members` trait overrides).
    let s1_spine = super::factoring::build_spine_emission(language, categories, per_cat);
    let s1_empty_dispositions: std::collections::HashMap<u16, super::factoring::SpineDisposition> =
        std::collections::HashMap::new();
    // Task #10 item 1: the empty-map mirror for `group_members` (same
    // shape discipline as the dispositions above).
    let s1_empty_group_members: std::collections::HashMap<u16, Vec<u16>> =
        std::collections::HashMap::new();

    // Aggregate Phase A.2 prefix arms across all categories. Each arm
    // guards on `state_cat_src_idx` so the same token can produce
    // different AST depending on which category is being parsed.
    let mut prefix_category_dispatch_arms = TokenStream::new();
    let mut prefix_category_router_helpers = TokenStream::new();
    // Task #15 (frame-bound peel): collect each category's per-arm
    // `#[inline(never)]` PrefixDispatch helper methods alongside the arms; they
    // are emitted into the inherent `impl #engine_ident` block below.
    let mut all_prefix_helpers = TokenStream::new();
    for (i, rules) in per_cat_indexed.iter().enumerate() {
        let (arms, helpers) = prefix::emit_prefix_arms_for_category(
            language,
            i as u16,
            categories.get(i).map(String::as_str).unwrap_or(""),
            rules,
            s1_spine
                .dispositions
                .get(i)
                .unwrap_or(&s1_empty_dispositions),
            s1_spine
                .group_members
                .get(i)
                .unwrap_or(&s1_empty_group_members),
            fork_rows,
        );
        all_prefix_helpers.extend(helpers);

        // A category router is a grammar-table lookup layer in the generated
        // WPDA.  The transition bodies already live in bounded, non-inlined
        // leaf methods, so keep the complete token match in one router.  This
        // gives rustc/LLVM the whole discriminant/key decision at once and
        // avoids a rule-count-dependent chain of chunk calls on a miss while
        // preserving the former ordered, first-match transition semantics.
        let category_src_idx = i as u16;
        let category_router = quote::format_ident!("step_prefix_category_c{category_src_idx}");
        prefix_category_router_helpers.extend(quote! {
            #[inline(never)]
            fn #category_router(
                &self,
                pos: &usize,
                cur_bp: &u8,
                state_cat_src_idx: u16,
                tokens: &dyn mettail_prattail::wpda_runtime::WpdaTokenSource,
                frontier_top: Option<&mettail_prattail::gss::WpdaGssNode>,
                frame_ctx: mettail_prattail::wpda_runtime::FrameCtx,
            ) -> Option<
                mettail_prattail::wpda_walker::WpdaStepAction<
                    mettail_prattail::automata::lex_weight::LexicographicWeight,
                >,
            > {
                let _outer_bp = *cur_bp;
                let __action = match tokens.peek_kind(*pos) {
                    #( #arms )*
                    _ => return None,
                };
                Some(__action)
            }
        });
        prefix_category_dispatch_arms.extend(quote! {
            #category_src_idx => self.#category_router(
                pos,
                cur_bp,
                state_cat_src_idx,
                tokens,
                frontier_top,
                frame_ctx,
            ),
        });
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
    let collection_element_prefix_predicate =
        super::collection::emit_collection_element_prefix_predicate(language, categories);
    // Stage 2 consolidation (2026-06-27): the single per-(result_src_idx,
    // rule_idx, slot_idx) → CollectionSpec table. Supersedes the former
    // collection_close_lookup / collection_close_sep_lookup /
    // kv_separator_for_collection_lookup / collection_element_src_lookup (and
    // the inline 4-tuple the CollectionLoop arm built). Every consumer reads
    // the field it needs off the one CollectionSpec record via the engine's
    // `collection_spec(src, rule, slot)` method.
    let collection_spec_table =
        super::collection::emit_collection_spec_table(language, categories, per_cat);
    // B9 / Class 2 (2026-05-08): per-rule lookup for Class-2 binder rules'
    // internal collection slots. Used by the walker's CollectionMarker-pop
    // arm to suppress the default FireAction.
    let is_binder_internal_collection_lookup =
        super::collection::emit_is_binder_internal_collection_lookup(language, per_cat);
    // Trigger-ownership soundness (2026-07-02): per-rule predicate — does the
    // rule's surface pattern begin with a structural literal trigger? Gates the
    // `emit_fire_action` walk-back `pos_match` fallback so an operand-leading
    // rule cannot claim a foreign-owned leading TriggerTerminal at its
    // frame-start position (the `@Nil!!(…)`→`NVar("Nil")` phantom).
    let rule_has_leading_structural_trigger_lookup =
        super::collection::emit_rule_has_leading_structural_trigger_lookup(language, per_cat);
    // ROOT-P Stage 4 (2026-07-08): per-CATEGORY binder-scope classifier. Gates
    // the Stage-4 conditional edge-drop — TRUE (keep edge) for binder-scoped
    // categories, FALSE (droppable) for context-free-interchangeable ones.
    let category_is_binder_scoped_lookup =
        super::collection::emit_category_is_binder_scoped_lookup(language, categories, per_cat);
    // Phase 5: BinderRule state body (multi-step state machine per rule).
    // Literal-leading binder/prefix entry arms are emitted by
    // prefix::emit_prefix_arms_for_category so they share one ambiguity bucket
    // with atomics, cross-category LHS delegation, and transparent projection
    // alternatives that have the same first-token evidence.
    // Stage 3.27d (G-PREFIX-BP, 2026-04-30): build the unary-prefix BP map
    // once per language; consumed by ParamParse arms in BinderRule and
    // OptionalGroup state bodies. Empty map => non-unary-prefix rules use
    // `cur_bp: 0` per the legacy default.
    let prefix_bp_map = super::binder::build_prefix_bp_map(language, per_cat);
    // One deterministic table supplies every nested traversal marker and both
    // unwind decoders. Construct it before the emitters so all of them share
    // one classification and one marker-ID assignment.
    let traversal_markers = super::binder::build_traversal_marker_table(language, per_cat);
    // Task #15 (frame-bound peel): `emit_binder_rule_body` returns the inline
    // skeleton body PLUS the per-(cat,rule) `#[inline(never)]` helper methods
    // that get emitted into the sibling inherent `impl #engine_ident` block.
    let (binder_rule_body, binder_rule_helpers) = super::binder::emit_binder_rule_body(
        language,
        categories,
        per_cat,
        &prefix_bp_map,
        &traversal_markers,
        // S1-FACTORING F1: the `(cat, SPINE_ID, node_pos)` spine arms
        // (empty under the OFF const).
        &s1_spine.binder_arms,
    );
    // Phase 5b: BinderListLoop body for multi-binder list (^[xs]).
    let binder_list_loop_body = super::binder::emit_binder_list_loop_body(
        language,
        categories,
        per_cat,
        &traversal_markers,
    );
    // B8 / Issue D (2026-05-09); Phase 4 #2 (2026-05-12): per-(src, rule,
    // slot_idx) predicate for Class 3 CollectionMarker pushes that should
    // also open a BinderScope. Per-slot variant is required for rules
    // with a Class-3 BinderListLoop AND a Class-2 SimpleCollection
    // sibling (e.g. PInputsTagged) — the per-rule predicate (pre-Phase-4-#2)
    // incorrectly opened a BinderScope for the Class-2 sibling too.
    let is_class3_collection_lookup =
        super::binder::emit_is_class3_collection_per_slot(language, per_cat);
    // B8 / Issue C (2026-05-09): per-(rule, sub_pos) splice lookup
    // for Class 3 inner walk Name-parse return points.
    let binderlist_inner_post_splice_lookup =
        super::binder::emit_binderlist_inner_post_splice_lookup(language, per_cat);
    let optional_marker_metadata_lookup =
        super::binder::emit_optional_marker_metadata_lookup(&traversal_markers);
    let binder_marker_metadata_lookup =
        super::binder::emit_binder_marker_metadata_lookup(&traversal_markers);
    // Opt-Group (2026-04-29): per-rule per-group OptionalGroup state
    // dispatch — FIRST-set peek + inner-position walk + finalize.
    let optional_group_body =
        super::binder::emit_optional_group_body(language, categories, per_cat, &traversal_markers);
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
    let grouping_arms =
        super::prefix::emit_paren_dispatch_arms(categories, language, per_cat, fork_rows);

    let semantic_actions::PartitionedActionFor {
        helpers: action_for_helpers,
        body: action_for_body,
    } = semantic_actions::emit_partitioned_action_for(language, categories, &per_cat_indexed);
    let chain_atom_rules_for_token_body =
        super::kind_dispatch::emit_chain_atom_rules_for_token_body(language, per_cat);
    let chain_atom_producers_for_token_body =
        super::kind_dispatch::emit_chain_atom_producers_for_token_body(
            language, per_cat, categories,
        );
    // Pass-2c token-soundness backstop (2026-05-30): per-rule in-span literal
    // count consumed by the realize-time soundness filter.
    let min_terminal_span_body =
        semantic_actions::emit_min_terminal_span_body(categories, &per_cat_indexed);
    // ROOT-C structural token-soundness backstop (2026-07-08): per-rule
    // "leads with a literal" predicate consumed by the realize-time filter to
    // reject the demand-driver's fabricated leading-literal cast phantom (whose
    // `children[0]` is the operand `Symbol`, not the realized leading terminal).
    let rule_leads_with_literal_body =
        semantic_actions::emit_rule_leads_with_literal_body(&per_cat_indexed);
    // AT_QUOTED_BIND_GATE realize-backstop (option B, 2026-07-03): the two
    // grammar-derived engine helper methods are emitted ONLY when the codegen
    // realize kill-switch is on (in lock-step with the walker-side
    // `AT_QUOTED_BIND_REALIZE_GATE`). Baseline (off) ⇒ EMPTY ⇒ the trait
    // defaults (`false`) apply ⇒ generated engine impl byte-identical.
    let at_quoted_bind_realize_methods: proc_macro2::TokenStream =
        if super::forks::AT_QUOTED_BIND_REALIZE_GATE {
            let overgen_body =
                semantic_actions::emit_sigil_quoted_bind_overgen_rule_body(&per_cat_indexed);
            let atom_body = semantic_actions::emit_sigil_quoted_source_atom_rule_body(
                categories,
                &per_cat_indexed,
                language,
            );
            quote! {
                fn sigil_quoted_bind_overgen_rule(&self, src_idx: u16, rule_idx: u16) -> bool {
                    // AT_QUOTED_BIND_GATE realize-backstop drop-set (option B):
                    // generic whole-source bind rules subsumed by a sigil-quoted
                    // sibling. Grammar-derived (see
                    // emit_sigil_quoted_bind_overgen_rule_body).
                    #overgen_body
                }
                fn sigil_quoted_source_atom_rule(&self, src_idx: u16, rule_idx: u16) -> bool {
                    // AT_QUOTED_BIND_GATE realize-backstop sigil-atom set
                    // (option B): source-cat rules whose leading sigil also
                    // triggers a rule in another (result) category.
                    #atom_body
                }
            }
        } else {
            quote! {}
        };
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
    let trigger_unary_wrappers_into_body =
        semantic_actions::emit_trigger_unary_wrappers_into_body(categories, &per_cat_indexed);
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
    let category_accepts_operator_at_floor_body =
        emit_category_accepts_operator_at_floor_body(categories);
    // D8 fix (2026-05-13): per-language `type_name → cat_src_idx`
    // lookup body, consumed by the walker's
    // `GroupingClosePreservingInner` sentinel resolution.
    let cat_of_type_name_body = emit_cat_of_type_name(language, categories);
    // GEN-1 goal-gate (2026-06-28): the `cat_can_reach(from, goal)` body —
    // reflexive-transitive closure of the post-built cross-cat extension graph
    // (cross-cat infix/postfix/mixfix LHS edges ∪ transparent projections;
    // prefix edges EXCLUDED). Emitted into a sibling inherent impl so the
    // InfixLoop's goal filter can call `Self::cat_can_reach`.
    let cat_can_reach_body =
        super::kind_dispatch::emit_cat_can_reach(language, per_cat, categories);
    // L-substrate Piece #6 (2026-05-13): lex-fork dispatch block,
    // emitted at the top of the WpdaState::PrefixDispatch arm.
    // S1-FACTORING AV5: when factored groups exist, the PrefixOp lex-alt
    // weight stamps route through the `__s1_spine_weight_rule` free fn
    // (min-member identity for spine entries; the fn is emitted below).
    let contextual_keywords = match language.options.get("contextual_keywords") {
        Some(AttributeValue::StringList(values)) => values.as_slice(),
        _ => &[],
    };
    let lex_fork_dispatch = super::forks::emit_lex_fork_at_prefix_dispatch(
        primary_src_idx,
        contextual_keywords,
        s1_spine.any_groups(),
    );
    // S1-FACTORING F5-2 (plan f5_mixfix_cohorts_plan.md, A-M5): when THIS
    // language has factored mixfix cohorts, the InfixLoop lex-fork's
    // MixfixFirstTrigger sites route the scalar-cost trigger identity and the
    // `LexAltMixfixOp.rule_idx` action-kind field through
    // `__s1_spine_weight_rule` (min member for spine ids, identity
    // otherwise). Gated per language so every no-mixfix-group engine stays
    // byte-identical.
    let mixfix_any = !s1_spine.mixfix_groups.is_empty();
    let lex_fork_infix_dispatch =
        super::forks::emit_lex_fork_at_infix_loop(primary_src_idx, mixfix_any);

    // M6c.2 (2026-05-14): per-grammar `lex_alt_rule_for` free fn.
    // Used by the lex-Fork emitter (M6c.3) to bind alts to atomic-
    // literal rules. Emitted as a sibling of the engine impl so the
    // codegen output uses a single match expression with all
    // (cat, kind) entries.
    let lex_alt_rule_for_fn =
        super::kind_dispatch::emit_lex_alt_rule_for_fn(language, per_cat, categories, &s1_spine);

    // SPPF-realize observational-dedup (2026-06-28): the
    // `WpdaEngine::semantic_fingerprint` override. Probe the realized
    // `Arc<dyn Any>` against each declared category; on the (unique) match,
    // emit `category_discriminant ‖ term.semantic_hash(..)` through the
    // module-scope `__MettailWpdaSemanticKeyHasher` — the SAME byte key the
    // facade root-dedup consumes. The discriminant (category source index)
    // is constant within any single SPPF node's realization (one category
    // per node), so it never changes a dedup partition; it only prevents a
    // cross-category collision. A non-category term yields `None` (kept
    // distinct). This makes per-node dedup byte-for-byte equivalent to
    // root-only dedup (the output-identity theorem).
    let semantic_fingerprint_arms: Vec<TokenStream> = categories
        .iter()
        .enumerate()
        .map(|(i, cat_name)| {
            let cat_ident = quote::format_ident!("{}", cat_name);
            let cat_disc = i as u16;
            quote! {
                if let Some(__t) = (&**term).downcast_ref::<#cat_ident>() {
                    let mut __hasher = __MettailWpdaSemanticKeyHasher::default();
                    std::hash::Hasher::write_u16(&mut __hasher, #cat_disc);
                    __t.semantic_hash(&mut __hasher);
                    return Some(__hasher.into_key());
                }
            }
        })
        .collect();

    // Fixed-width accelerator over the exact same tagged stream. The walker
    // uses this only for bucket selection and always regenerates the complete
    // `semantic_fingerprint` bytes before folding a candidate, so digest
    // collisions cannot change the parse result.
    let semantic_fingerprint_digest_arms: Vec<TokenStream> = categories
        .iter()
        .enumerate()
        .map(|(i, cat_name)| {
            let cat_ident = quote::format_ident!("{}", cat_name);
            let cat_disc = i as u16;
            quote! {
                if let Some(__t) = (&**term).downcast_ref::<#cat_ident>() {
                    let mut __hasher =
                        mettail_prattail::wpda_walker::SemanticFingerprintHasher::default();
                    std::hash::Hasher::write_u16(&mut __hasher, #cat_disc);
                    __t.semantic_hash(&mut __hasher);
                    return Some(__hasher.into_fingerprint());
                }
            }
        })
        .collect();

    // Persistent exact key over the byte-identical category-tagged semantic
    // stream. The category method shares cached descendant keys; the prefix is
    // one local fragment, so neither step flattens a subtree.
    let semantic_content_key_arms: Vec<TokenStream> = categories
        .iter()
        .enumerate()
        .map(|(i, cat_name)| {
            let cat_ident = quote::format_ident!("{}", cat_name);
            let cat_disc = i as u16;
            quote! {
                if let Ok(__owner) = term.clone().downcast::<#cat_ident>() {
                    let __term_key = #cat_ident::semantic_content_key(__owner, cache)?;
                    let mut __builder =
                        mettail_runtime::exact_semantic_key::SemanticKeyBuilder::with_max_bytes(
                            cache.max_key_bytes(),
                        );
                    std::hash::Hasher::write_u16(&mut __builder, #cat_disc);
                    __builder.push_key(__term_key);
                    return Ok(Some(__builder.into_key()?));
                }
            }
        })
        .collect();

    // Positive structural equality is a sufficient certificate for exact
    // semantic-key equality. A negative typed comparison remains
    // inconclusive because two structurally different terms can be
    // observationally equal (for example through transparent constructors),
    // so the walker retains its complete exact-key fallback.
    let semantic_structural_equality_arms: Vec<TokenStream> = categories
        .iter()
        .map(|cat_name| {
            let cat_ident = quote::format_ident!("{}", cat_name);
            quote! {
                if let (Some(__left), Some(__right)) = (
                    (&**left).downcast_ref::<#cat_ident>(),
                    (&**right).downcast_ref::<#cat_ident>(),
                ) {
                    return if __left == __right {
                        mettail_prattail::wpda_walker::SemanticEqualityWitness::Equal
                    } else {
                        mettail_prattail::wpda_walker::SemanticEqualityWitness::Inconclusive
                    };
                }
            }
        })
        .collect();

    // S1-FACTORING F1: the spine-bundle streams interpolated below. ALL are
    // empty under `forks::S1_FACTORING == false` (byte-identical output).
    let s1_action_for_prelude = &s1_spine.action_for_prelude;
    let s1_leading_trigger_prelude = &s1_spine.leading_trigger_prelude;
    let s1_min_span_prelude = &s1_spine.min_span_prelude;
    let s1_trigger_spine_owner_fn = &s1_spine.trigger_spine_owner_fn;
    let s1_spine_members_fn = &s1_spine.spine_members_fn;
    let s1_spine_weight_rule_fn = &s1_spine.spine_weight_rule_fn;
    // ★ #141 G8 — the factoring model's ENCODING-LIMIT refusals. EMPTY for every
    // grammar whose spine factoring encodes, which is every shipped one, so the
    // generated module is byte-identical wherever there is nothing to refuse.
    // Non-empty, it is a run of `compile_error!` items that fails the build with
    // a message naming the category and the ceiling — the outcome the `assert!`s
    // it replaces could not deliver, because a proc-macro panic under this
    // workspace's cranelift dev backend prints nothing at all (#141 RED-0).
    let s1_refusals = &s1_spine.refusals;

    // ── S1-FACTORING F5-2: the InfixLoop mixfix loop-v2 + the spliced
    // MixfixLiteralRun spine prelude (plan f5_mixfix_cohorts_plan.md §2). ──
    //
    // The VERBATIM per-member fan loop, extracted so the no-groups emission
    // interpolates the byte-identical tokens at the original position and
    // the grouped emission reuses it as the loop-v2 `_` fallback arm (D-1:
    // partial floor windows / goal / method-name rejections reproduce
    // today's per-member behavior exactly).
    let mixfix_member_fan_loop = quote! {
        mettail_prattail::wpda_transitions::mixfix::member_fan(
            __mixfix_slice, cur_bp, __mixfix_fallback_full,
            &__goal_admits, &__method_name_admits, lex_w, &mut __cands,
        );
    };
    let s1_mixfix_fan_arms = &s1_spine.mixfix_fan_arms;
    let mixfix_fan_tokens = if mixfix_any {
        // Loop v2: ONE spine branch per fully-admitted cohort (the group
        // arms carry the D-1 guard — min_l_bp floor + the member-uniform
        // goal/method-name gates on the A-M4 MEMBER id); everything else
        // falls to the verbatim per-member loop.
        quote! {
            let mut __mixfix_spine_pushed = false;
            match (state_cat_src_idx, token_text) {
                #s1_mixfix_fan_arms
                _ => {
                    #mixfix_member_fan_loop
                }
            }
        }
    } else {
        mixfix_member_fan_loop.clone()
    };
    // The MixfixLiteralRun literal-step helpers, extracted so the ON
    // emission can HOIST them above the spine prelude (A-M3: macro_rules!
    // is post-definition-visible and duplicating the fn is E0428) while the
    // OFF emission interpolates the byte-identical tokens at the original
    // position. #307 ROOT-A D3 (2026-06-11; FV: MixfixLiteralAccounting.
    // {checked_run_iff_spells, primary_equality_loses,
    // unchecked_accepts_mismatch, checked_never_fabricates,
    // fork_completeness}): membership-checked literal consume — a rule
    // literal matches iff its TEXT equals some out-edge of the position
    // (primary OR lattice alternative); the consume advances along the
    // MATCHED edge's target; no match ⇒ pure Error; multiple distinct
    // targets ⇒ Fork, never pick-one.
    let mixfix_literal_helpers = quote! {
        fn __mixfix_literal_targets(
            tokens: &dyn mettail_prattail::wpda_runtime::WpdaTokenSource,
            pos: usize,
            expected: &str,
        ) -> Vec<usize> {
            mettail_prattail::wpda_transitions::mixfix::literal_targets(tokens, pos, expected)
        }
        /// ★ #131: satisfy a CAPTURE `MixfixPart` — consume exactly ONE token of
        /// the part's kind and fold its text as this rule's next action argument.
        ///
        /// `$capture_kind` is the kind NAME from `mixfix_part(..).3`;
        /// `$part_idx` is the index of the part being satisfied, which becomes the
        /// marker's new `completed_idx`. For a part-0 capture entered at `kind: 2`
        /// that equals the current `completed_idx` (a self-replace, the shipped
        /// no-op); for a later capture entered at `kind: 1` it is
        /// `completed_idx + 1`, which BUMPS the marker exactly as the operand
        /// hand-off does.
        ///
        /// # Why this is `GuardedConsumeTokenKindAndReplace` and not a new action
        ///
        /// That fork action already does precisely the three things a capture
        /// needs, and is already live (`l9modaltoy` emits it for its mid-rule
        /// `w@Word` capture):
        ///
        /// 1. it GATES on `capture_kind(kind_name)`, which maps the builtin
        ///    `"Ident"` to `TokenKind::Ident` — the kind the lexer actually emits —
        ///    rather than to `TokenKind::Custom("Ident")`, which nothing emits and
        ///    which left the gate permanently dead before `ac46362b`;
        /// 2. on a MISS it allocates no child at all, so a wrong token kills only
        ///    this reading and leaves sibling readings intact (fanout-survival);
        /// 3. on a HIT it interns the token as an SPPF terminal and FOLDS it into
        ///    the marker's frame, which is what makes it an action argument. A
        ///    literal consume (`ConsumeAtAndReplace`) deliberately folds nothing —
        ///    that is the difference between punctuation and data, and it is why a
        ///    capture cannot be expressed as a literal run.
        ///
        /// The folded terminal reaches the rule action as
        /// `ActionArg::Token { kind: Ident, .. }` (the intern records
        /// `pushed_via_push_ident = false`, and realization branches on THAT
        /// discriminator, not on the token kind). The mixfix action extractor in
        /// `semantic_actions.rs` reads it accordingly.
        macro_rules! __mixfix_capture_consume {
            ($capture_kind:expr, $part_idx:expr) => {{
                let __capture_kind: &str = $capture_kind;
                let __part_idx: u8 = $part_idx;
                mettail_prattail::wpda_transitions::mixfix::capture_consume(
                    result_src_idx, rule_idx, __mixfix_continuation_bp,
                    __capture_kind, __part_idx, || lex_one(),
                )
            }};
        }
        macro_rules! __checked_literal_consume {
            ($expected:expr, $next_state:expr) => {{
                let __expected: &str = $expected;
                let __next_state = $next_state;
                mettail_prattail::wpda_transitions::mixfix::checked_literal_consume(
                    tokens, _pos, result_src_idx, rule_idx, completed_idx,
                    __mixfix_continuation_bp, __expected, __next_state, || lex_one(),
                )
            }};
        }
    };
    let s1_mixfix_prelude_arms = &s1_spine.mixfix_prelude_arms;
    // A-M3 hoist: under the grouped emission the helpers move ABOVE the
    // spine prelude, which sits BEFORE the generic `mixfix_part`/
    // `mixfix_parts_len` reads (spine ids never reach them — every prelude
    // arm early-returns). No-groups emission: helpers stay at their
    // original site, prelude absent — byte-identical.
    let (mixfix_mlr_head_tokens, _mixfix_mlr_helpers_site_tokens) = if mixfix_any {
        (
            quote! {
                #mixfix_literal_helpers
                match (*result_src_idx, *rule_idx, *kind, *completed_idx, *sub_pos) {
                    #s1_mixfix_prelude_arms
                    _ => {},
                }
            },
            TokenStream::new(),
        )
    } else {
        (TokenStream::new(), mixfix_literal_helpers)
    };

    quote! {
        #lex_alt_rule_for_fn

        // S1-FACTORING AV5 (2026-07-12): `__s1_spine_weight_rule(cat, rule)`
        // — the lex-fork PrefixOp weight identity redirect (min member for
        // spine ids, identity otherwise). Emitted ONLY when factored groups
        // exist; the lex-fork emission references it only in that case.
        #s1_spine_weight_rule_fn

        #s1_refusals

        // Task #15 (frame-bound peel, 2026-07-14): module-level imports so the
        // peeled BinderRule/PrefixDispatch helper methods (in the inherent impl
        // below) resolve the same SHORT names the trait `step` uses via its
        // fn-local `use`s — the relocated arm bodies are byte-for-byte verbatim
        // and reference `WpdaStepAction`/`WpdaState`/`StackSymbolV2` and the
        // exact scalar-cost constructors unqualified. These land at the language module's top level
        // (where the engine impls sit, alongside `ast`/`language`/… includes).
        // The only sibling generated file with a column-0 `use` is `parser.rs`
        // (a `runtime_types::*` GLOB + an explicit `Cow`); an explicit `use`
        // never conflicts with a glob and none of these names is `Cow`, so no
        // E0252. `#[allow(unused_imports)]` because any one helper body needs
        // only a subset.
        #[allow(unused_imports)]
        use mettail_prattail::wpda_runtime::{
            StackSymbolV2, WpdaState, lex_w, lex_w_alt, lex_w_alt_with_len,
            lex_w_with_len, lex_one,
        };
        #[allow(unused_imports)]
        use mettail_prattail::wpda_walker::WpdaStepAction;
        #[allow(unused_imports)]
        use mettail_prattail::wpda_walker::WpdaEngine as _;
        #[allow(unused_imports)]
        use mettail_prattail::automata::lex_weight::LexicographicWeight;
        #[allow(unused_imports)]
        use mettail_prattail::automata::semiring::Semiring;

        // GEN-1 goal-gate (2026-06-28): sibling inherent impl carrying the
        // pure `cat_can_reach` predicate. Lives outside the `WpdaEngine` trait
        // impl (the trait fixes its method set) yet is reachable as
        // `Self::cat_can_reach` from the trait impl's `step` method because
        // `Self == #engine_ident` there and inherent associated fns resolve
        // through `Self::`. `from == goal` short-circuits reflexivity; the
        // emitted `matches!` enumerates only the non-reflexive RTC pairs.
        //
        // Task #15: ALSO the drop-in home for the peeled `binder_rule_c*_r*`
        // and `prefix_arm_c*_a*` `#[inline(never)]` helper methods, called via
        // `self.` from the trait `step`. `#[allow(unused_variables)]` covers
        // their over-provisioned params (frame_ctx / tokens / _pos / …);
        // `#[allow(unused_braces)]` the relocated `{ .. }` bodies.
        #[allow(dead_code, unused_variables, unused_braces)]
        impl #engine_ident {
            fn cat_can_reach(from: u16, goal: u16) -> bool {
                if from == goal {
                    return true;
                }
                #cat_can_reach_body
            }
            #collection_element_prefix_predicate
            // A lexical lattice fork is a transition submachine, not part of
            // PrefixDispatch's ordinary token router.  Keeping it in its own
            // non-inlined frame prevents the generated grammar's alternative
            // constructors from being reserved alongside every normal prefix
            // arm.  `None` is the exact former fall-through edge; `Some` is the
            // exact former early-return action.
            #[inline(never)]
            fn step_prefix_lex_fork(
                &self,
                pos: &usize,
                cur_bp: &u8,
                frontier_top: Option<&mettail_prattail::gss::WpdaGssNode>,
                tokens: &dyn mettail_prattail::wpda_runtime::WpdaTokenSource,
                frame_ctx: mettail_prattail::wpda_runtime::FrameCtx,
            ) -> Option<
                mettail_prattail::wpda_walker::WpdaStepAction<
                    mettail_prattail::automata::lex_weight::LexicographicWeight,
                >,
            > {
                #[allow(non_camel_case_types)]
                type __DwW =
                    mettail_prattail::automata::lex_weight::LexicographicWeight;
                #lex_fork_dispatch
                None
            }
            // Task #15: peeled BinderRule per-(cat,rule) dispatch helpers
            // (each an `#[inline(never)]` `match (cat,rule,position)` group).
            #binder_rule_helpers
            // Semantic action construction is likewise routed through one
            // non-inlined, category-sized helper. The rule arms themselves are
            // unchanged; this bounds rustc's native frame without adding a
            // runtime table or dynamic dispatch.
            #action_for_helpers
            // Task #15: peeled PrefixDispatch per-arm-body helpers.
            #all_prefix_helpers
            // Stack-bound token routers: category -> token decision ->
            // transition leaf. All calls are non-recursive; semantic branch
            // temporaries remain isolated in the leaf methods.
            #prefix_category_router_helpers
        }

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
                // Stage 4 (Lever-1 emit-both): innermost-collection structural
                // delimiters, computed by the walker. Consulted by the
                // InfixLoop/PrefixDispatch lex-fork to add a CollectionMarker
                // yield ALONGSIDE the operator branches on an ambiguous close.
                frame_ctx: mettail_prattail::wpda_runtime::FrameCtx,
            ) -> mettail_prattail::wpda_walker::WpdaStepAction<
                mettail_prattail::automata::lex_weight::LexicographicWeight,
            > {
                use mettail_prattail::wpda_runtime::{
                    StackSymbolV2, WpdaState,
                };
                use mettail_prattail::wpda_walker::WpdaStepAction;
                use mettail_prattail::automata::lex_weight::LexicographicWeight;
                use mettail_prattail::automata::semiring::Semiring;
                use mettail_prattail::wpda_runtime::{
                    lex_w, lex_w_alt, lex_w_alt_with_len, lex_w_with_len, lex_one,
                };
                #[allow(non_camel_case_types)]
                type __DwW = LexicographicWeight;

                // Stack-safety partition: generated grammars can have thousands
                // of transition arms. In an unoptimized build, keeping every
                // state body in this one function makes rustc reserve the sum of
                // their branch temporaries in a single native frame. The actual
                // pushdown store already lives in the walker/GSS; this transparent
                // wrapper gives each PDA control-state family a named, non-inlined
                // native frame without adding a runtime state or recursive call.
                struct __MettailWpdaStepFrame<'a>(&'a #engine_ident);
                impl std::ops::Deref for __MettailWpdaStepFrame<'_> {
                    type Target = #engine_ident;

                    #[inline(always)]
                    fn deref(&self) -> &Self::Target {
                        self.0
                    }
                }
                let __step_frame = __MettailWpdaStepFrame(self);

                match state {
                    WpdaState::Ready { min_bp } => {

                        mettail_prattail::wpda_transitions::control::ready(
                            #primary_src_idx, min_bp, lex_w,
                        )
                    }
                    WpdaState::PrefixDispatch { pos, cur_bp } => {
                        impl __MettailWpdaStepFrame<'_> {
                            #[inline(never)]
                            fn step_prefix_dispatch(
                                &self,
                                pos: &usize,
                                cur_bp: &u8,
                                _gss: &mettail_prattail::gss::WpdaGss<
                                    mettail_prattail::automata::lex_weight::LexicographicWeight,
                                >,
                                frontier_top: Option<&mettail_prattail::gss::WpdaGssNode>,
                                _pos: usize,
                                tokens: &dyn mettail_prattail::wpda_runtime::WpdaTokenSource,
                                frame_ctx: mettail_prattail::wpda_runtime::FrameCtx,
                            ) -> mettail_prattail::wpda_walker::WpdaStepAction<
                                mettail_prattail::automata::lex_weight::LexicographicWeight,
                            > {
                                mettail_prattail::wpda_transitions::prefix_dispatch::prefix_dispatch(
                                    #primary_src_idx, pos, cur_bp, frontier_top, tokens,
                                    || self.step_prefix_lex_fork(
                                        pos, cur_bp, frontier_top, tokens, frame_ctx,
                                    ),
                                    |result_src_idx, rule_idx, slot_idx| {
                                        self.collection_spec(result_src_idx, rule_idx, slot_idx)
                                    },
                                    |src_idx, kind| self.collection_element_can_start(src_idx, kind),
                                    lex_w,
                                    |state_cat_src_idx, _outer_bp, peek| {
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
                                            _ => {
                                                // Generic unified prefix arms.  They retain
                                                // their original source order, but are routed
                                                // through bounded per-category match chunks so
                                                // grammar growth cannot inflate this state's
                                                // native frame.
                                                if let Some(__action) = match state_cat_src_idx {
                                                    #prefix_category_dispatch_arms
                                                    _ => None,
                                                } {
                                                    return __action;
                                                }
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
                                                mettail_prattail::wpda_transitions::prefix_dispatch::recover(
                                                    _gss, frontier_top, pos, cur_bp, state_cat_src_idx,
                                                    tokens, recovery_infra_for,
                                                )
                                            }
                                        }
                                    },
                                )
                            }
                        }
                        __step_frame.step_prefix_dispatch(
                            pos,
                            cur_bp,
                            _gss,
                            frontier_top,
                            _pos,
                            tokens,
                            frame_ctx,
                        )
                    }
                    WpdaState::Unwinding => {
                        impl __MettailWpdaStepFrame<'_> {
                            #[inline(never)]
                            fn step_unwinding(
                                &self,
                                frontier_top: Option<&mettail_prattail::gss::WpdaGssNode>,
                                _pos: usize,
                                tokens: &dyn mettail_prattail::wpda_runtime::WpdaTokenSource,
                            ) -> mettail_prattail::wpda_walker::WpdaStepAction<
                                mettail_prattail::automata::lex_weight::LexicographicWeight,
                            > {
                                mettail_prattail::wpda_transitions::unwinding::unwinding_step(
                                    self.0, frontier_top, _pos, tokens, lex_one,
                                    |inner_cat, next_tok| #category_recognizes_token_dispatch,
                                    mixfix_parts_len, mixfix_part,
                                    |marker_id| #binder_marker_metadata_lookup,
                                    |result_src_idx, rule_idx, frame_idx, sub_pos| {
                                        #binderlist_inner_post_splice_lookup
                                    },
                                    |marker_id| #optional_marker_metadata_lookup,
                                )
                            }
                        }
                        __step_frame.step_unwinding(frontier_top, _pos, tokens)
                    }
                    WpdaState::InfixLoop { cur_bp } => {
                        impl __MettailWpdaStepFrame<'_> {
                            #[inline(never)]
                            fn step_infix_loop(
                                &self,
                                cur_bp: &u8,
                                _gss: &mettail_prattail::gss::WpdaGss<
                                    mettail_prattail::automata::lex_weight::LexicographicWeight,
                                >,
                                frontier_top: Option<&mettail_prattail::gss::WpdaGssNode>,
                                _pos: usize,
                                tokens: &dyn mettail_prattail::wpda_runtime::WpdaTokenSource,
                                frame_ctx: mettail_prattail::wpda_runtime::FrameCtx,
                            ) -> mettail_prattail::wpda_walker::WpdaStepAction<
                                mettail_prattail::automata::lex_weight::LexicographicWeight,
                            > {
                                mettail_prattail::wpda_transitions::infix::infix_loop::<_, #mixfix_any>(
                                    #primary_src_idx, cur_bp, frontier_top, _pos, tokens,
                                    |result_src_idx, rule_idx, slot_idx| {
                                        self.collection_spec(result_src_idx, rule_idx, slot_idx)
                                    },
                                    <#engine_ident>::cat_can_reach,
                                    |state_cat_src_idx| { #lex_fork_infix_dispatch },
                                    |state_cat_src_idx, token_text| { #infix_loop_dispatch },
                                    |state_cat_src_idx, token_text| { #postfix_dispatch },
                                    |state_cat_src_idx, token_text| { #mixfix_dispatch },
                                    mixfix_part, mixfix_nullary_literals,
                                    |state_cat_src_idx, symbol_rs, symbol_ri| {
                                        #iter_eligible_dispatch
                                    },
                                    lex_w,
                                    |state_cat_src_idx, token_text, __mixfix_slice,
                                     __mixfix_fallback_full, __goal_admits,
                                     __method_name_admits, mut __cands| {
                                        let __mixfix_spine_pushed = false;
                                        #mixfix_fan_tokens
                                        __mixfix_spine_pushed
                                    },
                                )
                            }
                        }
                        __step_frame.step_infix_loop(
                            cur_bp,
                            _gss,
                            frontier_top,
                            _pos,
                            tokens,
                            frame_ctx,
                        )
                    }
                    WpdaState::InfixChainIterative {
                        result_src_idx: _result_src_idx,
                        rule_idx: _rule_idx,
                        outer_bp: _outer_bp,
                        rhs_bp,
                    } => {

                        mettail_prattail::wpda_transitions::control::infix_chain_iterative(
                            rhs_bp, _pos,
                        )
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
                        impl __MettailWpdaStepFrame<'_> {
                            #[inline(never)]
                            fn step_collection_loop(
                                &self,
                                result_src_idx: &u16,
                                rule_idx: &u16,
                                _element_src_idx: &u16,
                                _outer_bp: &u8,
                                _accumulator_id: &u8,
                                slot_idx: &u8,
                                kv_phase: &u8,
                                frontier_top: Option<&mettail_prattail::gss::WpdaGssNode>,
                                _pos: usize,
                                tokens: &dyn mettail_prattail::wpda_runtime::WpdaTokenSource,
                                frame_ctx: mettail_prattail::wpda_runtime::FrameCtx,
                            ) -> mettail_prattail::wpda_walker::WpdaStepAction<
                                mettail_prattail::automata::lex_weight::LexicographicWeight,
                            > {
                        // Phase 4: dispatch on close / sep / element.
                        // Phase 4 #1.B (2026-05-11): slot_idx in scope
                        // for 3-tuple-keyed (close, sep) lookup in
                        // `emit_collection_loop_arm`.
                        // Phase 4 #5b (2026-05-12): kv_phase in scope
                        // for HashMap 3-phase dispatch.
                        #collection_loop_body
                            }
                        }
                        __step_frame.step_collection_loop(
                            result_src_idx,
                            rule_idx,
                            _element_src_idx,
                            _outer_bp,
                            _accumulator_id,
                            slot_idx,
                            kv_phase,
                            frontier_top,
                            _pos,
                            tokens,
                            frame_ctx,
                        )
                    }
                    WpdaState::MixfixContinuation {
                        result_src_idx,
                        rule_idx,
                        completed_idx,
                    } => {

                        mettail_prattail::wpda_transitions::mixfix::continuation(
                            result_src_idx, rule_idx, completed_idx, frontier_top, _pos, mixfix_part, lex_one,
                        )
                    }
                    WpdaState::MixfixLiteralRun {
                        result_src_idx,
                        rule_idx,
                        completed_idx,
                        kind,
                        sub_pos,
                    } => {
                        let __mixfix_continuation_bp = frontier_top
                            .filter(|node| {
                                node.symbol.kind
                                    == mettail_prattail::wpda_runtime::SymbolKind::MixfixMarker
                            })
                            .and_then(|node| node.symbol.continuation_bp)
                            .expect(
                                "MixfixLiteralRun invariant: frontier top must be a \
                                 MixfixMarker carrying its result continuation floor",
                            );
                        impl __MettailWpdaStepFrame<'_> {
                            #[inline(never)]
                            fn step_mixfix_literal_run(
                                &self,
                                result_src_idx: &u16,
                                rule_idx: &u16,
                                completed_idx: &u8,
                                kind: &u8,
                                sub_pos: &u8,
                                __mixfix_continuation_bp: u8,
                                _pos: usize,
                                tokens: &dyn mettail_prattail::wpda_runtime::WpdaTokenSource,
                            ) -> mettail_prattail::wpda_walker::WpdaStepAction<
                                mettail_prattail::automata::lex_weight::LexicographicWeight,
                            > {
                        // L12 follow-up B6 step 3 (2026-05-07): walk
                        // postfix-mixfix per-part literal sequences.
                        // kind=0: consume following_terminals after the
                        //         just-completed operand `completed_idx`.
                        // kind=1: consume preceding_terminals before the
                        //         next operand `completed_idx + 1`.
                        //
                        // S1-FACTORING F5-2: `#mixfix_mlr_head_tokens` is
                        // EMPTY for languages without factored mixfix
                        // cohorts; otherwise it is the A-M3-hoisted literal
                        // helpers followed by the spine prelude match —
                        // every prelude arm early-returns, so spine ids
                        // never reach the generic reads below.
                        #mixfix_mlr_head_tokens
                        mettail_prattail::wpda_transitions::mixfix::literal_run(
                            result_src_idx, rule_idx, completed_idx, kind, sub_pos,
                            __mixfix_continuation_bp, _pos, tokens, lex_one,
                            mixfix_part, mixfix_parts_len, mixfix_rep, mixfix_nullary_literals,
                        )
                            }
                        }
                        __step_frame.step_mixfix_literal_run(
                            result_src_idx,
                            rule_idx,
                            completed_idx,
                            kind,
                            sub_pos,
                            __mixfix_continuation_bp,
                            _pos,
                            tokens,
                        )
                    }
                    WpdaState::CollectionOpenParen {
                        result_src_idx,
                        rule_idx,
                        element_src_idx,
                        outer_bp,
                    } => {

                        mettail_prattail::wpda_transitions::control::collection_open_paren(
                            result_src_idx, rule_idx, element_src_idx, outer_bp, _pos, tokens, lex_one,
                        )
                    }
                    WpdaState::BinderRule {
                        result_src_idx,
                        rule_idx,
                        body_src_idx: _body_src_idx,
                        outer_bp,
                    } => {
                        impl __MettailWpdaStepFrame<'_> {
                            #[inline(never)]
                            fn step_binder_rule(
                                &self,
                                result_src_idx: &u16,
                                rule_idx: &u16,
                                _body_src_idx: &u16,
                                outer_bp: &u8,
                                frontier_top: Option<&mettail_prattail::gss::WpdaGssNode>,
                                _pos: usize,
                                tokens: &dyn mettail_prattail::wpda_runtime::WpdaTokenSource,
                                frame_ctx: mettail_prattail::wpda_runtime::FrameCtx,
                            ) -> mettail_prattail::wpda_walker::WpdaStepAction<
                                mettail_prattail::automata::lex_weight::LexicographicWeight,
                            > {
                        let _ = (result_src_idx, rule_idx, outer_bp);
                        // Phase 5: per-position dispatch for binder rules.
                        #binder_rule_body
                            }
                        }
                        __step_frame.step_binder_rule(
                            result_src_idx,
                            rule_idx,
                            _body_src_idx,
                            outer_bp,
                            frontier_top,
                            _pos,
                            tokens,
                            frame_ctx,
                        )
                    }
                    WpdaState::BinderListLoop {
                        result_src_idx,
                        rule_idx,
                        frame_idx,
                        outer_bp,
                        sub_pos,
                    } => {
                        impl __MettailWpdaStepFrame<'_> {
                            #[inline(never)]
                            fn step_binder_list_loop(
                                &self,
                                result_src_idx: &u16,
                                rule_idx: &u16,
                                frame_idx: &u32,
                                outer_bp: &u8,
                                sub_pos: &u32,
                                frontier_top: Option<&mettail_prattail::gss::WpdaGssNode>,
                                _pos: usize,
                                tokens: &dyn mettail_prattail::wpda_runtime::WpdaTokenSource,
                                frame_ctx: mettail_prattail::wpda_runtime::FrameCtx,
                            ) -> mettail_prattail::wpda_walker::WpdaStepAction<
                                mettail_prattail::automata::lex_weight::LexicographicWeight,
                            > {
                        let _ = (
                            result_src_idx,
                            rule_idx,
                            frame_idx,
                            outer_bp,
                            sub_pos,
                        );
                        // Phase 5b: ^[xs] binder list loop.
                        // B8 (2026-05-08): sub_pos indexes per-iteration
                        // inner walk for Class 3 ZIP-MAP-SEP. PNew-style
                        // rules dispatch at sub_pos=0 only.
                        #binder_list_loop_body
                            }
                        }
                        __step_frame.step_binder_list_loop(
                            result_src_idx,
                            rule_idx,
                            frame_idx,
                            outer_bp,
                            sub_pos,
                            frontier_top,
                            _pos,
                            tokens,
                            frame_ctx,
                        )
                    }
                    WpdaState::CrossCatDelegate {
                        source_src_idx,
                        inner_cur_bp,
                    } => {

                        mettail_prattail::wpda_transitions::control::cross_category_delegate(
                            source_src_idx, inner_cur_bp, _pos, lex_one,
                        )
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
                        impl __MettailWpdaStepFrame<'_> {
                            #[inline(never)]
                            fn step_optional_group(
                                &self,
                                result_src_idx: &u16,
                                rule_idx: &u16,
                                group_idx: &u32,
                                sub_pos: &u32,
                                outer_bp: &u8,
                                frontier_top: Option<&mettail_prattail::gss::WpdaGssNode>,
                                _pos: usize,
                                tokens: &dyn mettail_prattail::wpda_runtime::WpdaTokenSource,
                                frame_ctx: mettail_prattail::wpda_runtime::FrameCtx,
                            ) -> mettail_prattail::wpda_walker::WpdaStepAction<
                                mettail_prattail::automata::lex_weight::LexicographicWeight,
                            > {
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
                        }
                        __step_frame.step_optional_group(
                            result_src_idx,
                            rule_idx,
                            group_idx,
                            sub_pos,
                            outer_bp,
                            frontier_top,
                            _pos,
                            tokens,
                            frame_ctx,
                        )
                    }
                    WpdaState::GroupingClosePreservingInner { inner_cat_src_idx } => {

                        mettail_prattail::wpda_transitions::control::grouping_close(
                            inner_cat_src_idx, frontier_top, _pos, tokens, lex_one,
                        )
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
                // S1-FACTORING H9 prelude (empty under the OFF const): spine
                // rows with expected_input_cats = member union + POISON arity
                // (u8::MAX) — legitimate for the H1/A-1 evidence queries
                // (`binder_slot_accepts_body_category`, the ∃-member
                // acceptor), NEVER for firing (the walker consumption sites
                // debug-assert `!is_spine_rule_id`).
                #s1_action_for_prelude
                #action_for_body
            }

            // SPPF-realize observational-dedup (2026-06-28): per-node dedup key.
            // Consumed by the walker's (unconditional) realize dedup path; emitted
            // here so the hook compiles against the concrete category types.
            fn semantic_fingerprint(
                &self,
                term: &std::sync::Arc<dyn std::any::Any + Send + Sync>,
            ) -> Option<Vec<u8>> {
                #(#semantic_fingerprint_arms)*
                None
            }

            fn semantic_fingerprint_digest(
                &self,
                term: &std::sync::Arc<dyn std::any::Any + Send + Sync>,
            ) -> Option<mettail_prattail::wpda_walker::SemanticFingerprintDigest> {
                #(#semantic_fingerprint_digest_arms)*
                None
            }

            fn semantic_content_key(
                &self,
                term: &std::sync::Arc<dyn std::any::Any + Send + Sync>,
                cache: &mut mettail_runtime::exact_semantic_key::ContentKeyCache,
            ) -> Result<
                Option<mettail_runtime::exact_semantic_key::ContentKey>,
                mettail_runtime::exact_semantic_key::ContentKeyCacheError,
            > {
                #(#semantic_content_key_arms)*
                Ok(None)
            }

            fn semantic_structural_equality_witness(
                &self,
                left: &std::sync::Arc<dyn std::any::Any + Send + Sync>,
                right: &std::sync::Arc<dyn std::any::Any + Send + Sync>,
            ) -> mettail_prattail::wpda_walker::SemanticEqualityWitness {
                #(#semantic_structural_equality_arms)*
                mettail_prattail::wpda_walker::SemanticEqualityWitness::Inconclusive
            }

            fn chain_atom_rules_for_token(
                &self,
                cat_src_idx: u16,
                kind: &mettail_prattail::automata::TokenKind,
                text: Option<&str>,
            ) -> Vec<u16> {
                #chain_atom_rules_for_token_body
            }

            fn chain_atom_producers_for_token(
                &self,
                cat_src_idx: u16,
                kind: &mettail_prattail::automata::TokenKind,
                text: Option<&str>,
            ) -> Vec<mettail_prattail::wpda_walker::ChainAtomProducer> {
                #chain_atom_producers_for_token_body
            }

            fn prefix_token_has_non_atom_start(
                &self,
                cat_src_idx: u16,
                kind: &mettail_prattail::automata::TokenKind,
                text: Option<&str>,
            ) -> bool {
                let _ = text;
                mettail_prattail::wpda_transitions::control::prefix_token_has_non_atom_start(
                    cat_src_idx, kind, lex_alt_rules_for_prefix,
                    prefix_primary_has_non_atom_dispatch_rule,
                    prefix_crosscat_lhs_has_dispatch_rule,
                )
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

            // Task #10 item 1: the per-grammar K-C election tiebreak — the
            // ordinals are the emitters' STATIC DECLARATION POSITIONS,
            // recorded at codegen and emitted as the module-level table
            // beside the Parikh tables (see WPDA_FORK_EMISSION_ORDINAL's
            // generated doc for the per-site semantics).
            fn fork_emission_ordinal(&self, site_kind: u8, cat: u16, rule: u16) -> u16 {
                WPDA_FORK_EMISSION_ORDINAL(site_kind, cat, rule)
            }

            fn is_binder_internal_collection(
                &self,
                result_src_idx: u16,
                rule_idx: u16,
            ) -> bool {
                let _ = (result_src_idx, rule_idx);
                #is_binder_internal_collection_lookup
            }

            fn rule_has_leading_structural_trigger(
                &self,
                result_src_idx: u16,
                rule_idx: u16,
            ) -> bool {
                let _ = (result_src_idx, rule_idx);
                // S1-FACTORING A7 prelude (empty under the OFF const): spine
                // rows = the CONJUNCTION over group members (all-true under
                // F0 eligibility, asserted at codegen). Emitted regardless of
                // arm (consumer census: classic B2 shape mask,
                // sppf_shallow_ident_trigger_masked, the claim-gate pos_match
                // path, stats-only cgll_w_cond, the dormant step_canonical).
                #s1_leading_trigger_prelude
                #rule_has_leading_structural_trigger_lookup
            }

            fn category_is_binder_scoped(&self, src_idx: u16) -> bool {
                let _ = src_idx;
                #category_is_binder_scoped_lookup
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

            fn collection_spec(
                &self,
                result_src_idx: u16,
                rule_idx: u16,
                slot_idx: u8,
            ) -> Option<mettail_prattail::wpda_runtime::CollectionSpec> {
                // Stage 2 consolidation (2026-06-27): the single per-slot
                // CollectionSpec table. kv_separator_for_collection /
                // collection_element_src_idx and the InfixLoop / PrefixDispatch
                // / CollectionLoop close gates all project their field off this
                // one record.
                #collection_spec_table
            }

            fn kv_separator_for_collection(
                &self,
                result_src_idx: u16,
                rule_idx: u16,
                slot_idx: u8,
            ) -> Option<&'static str> {
                // Stage 2: projected off the consolidated CollectionSpec
                // (was the per-(src, rule, slot_idx) kv-separator lookup —
                // `Some(":")` for kv-maps, `None` otherwise).
                self.collection_spec(result_src_idx, rule_idx, slot_idx)
                    .and_then(|__s| __s.kv_sep)
            }

            fn collection_element_src_idx(
                &self,
                result_src_idx: u16,
                rule_idx: u16,
                slot_idx: u8,
            ) -> Option<u16> {
                // Stage 2: projected off the consolidated CollectionSpec
                // (was the per-(src, rule, slot_idx) element-src lookup; the
                // #307 TR ghost splice gate reads it here).
                self.collection_spec(result_src_idx, rule_idx, slot_idx)
                    .and_then(|__s| __s.element_src_idx)
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
                // S1-FACTORING prelude (empty under the OFF const): spine
                // rows = MIN over the group members' effective rows (omitted
                // when the min is 0 = the table default) — conservative for
                // any live-frame reader that sees an uncommitted SPINE_ID.
                #s1_min_span_prelude
                // Pass-2c token-soundness backstop (2026-05-30): per-rule
                // count of literal terminals matched STRICTLY WITHIN the
                // rule's result-Symbol span (literals after the first param).
                // The realize-time filter rejects any packing whose Symbol
                // span leaves less slack than this — dropping token-unsound
                // fabricated-cast derivations on evidence (yield != span).
                #min_terminal_span_body
            }

            fn rule_leads_with_literal(&self, src_idx: u16, rule_idx: u16) -> bool {
                // ROOT-C structural token-soundness backstop (2026-07-08):
                // `true` iff this rule's first syntax element is a literal. A
                // sound packing of a literal-led rule realizes that literal as a
                // terminal-kind first child; the realize filter rejects a
                // literal-led packing whose `children[0]` is a `Symbol` (the
                // fabricated grouping-close cast phantom). See
                // emit_rule_leads_with_literal_body.
                #rule_leads_with_literal_body
            }

            // AT_QUOTED_BIND_GATE realize-backstop (option B, 2026-07-03):
            // emitted ONLY when the codegen realize kill-switch is on;
            // byte-identical (nothing) at baseline.
            #at_quoted_bind_realize_methods

            // S1-FACTORING F1 (2026-07-12): grammar-derived spine-owner +
            // A-1 member tables, emitted ONLY when factored groups exist
            // (the `at_quoted_bind_realize_methods` conditional-override
            // convention — empty ⇒ the prattail trait defaults `None`/`&[]`
            // stand and the generated impl is byte-identical).
            //   - `trigger_spine_owner(cat, member) -> Some(SPINE_ID)`: the
            //     fire-time claim re-attribution (classic gate
            //     `owner_match || group_owner_match || pos_match`).
            //   - `spine_members(cat, SPINE_ID) -> &[members]`: the A-1
            //     ∃-member expansion at `action_accepts_single_body_category`
            //     (H9 poison-arity rows would otherwise default-refuse every
            //     mid-spine acceptance query and DROP readings).
            #s1_trigger_spine_owner_fn
            #s1_spine_members_fn

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

            fn single_hop_coercion_weight(
                &self,
                from_cat: u16,
                to_cat: u16,
                coercion_cat: u16,
                rule_idx: u16,
                span_len: u32,
            ) -> mettail_prattail::automata::lex_weight::LexicographicWeight {
                let _ = (from_cat, to_cat);
                if coercion_cat == to_cat {
                    mettail_prattail::wpda_runtime::lex_w(
                        mettail_prattail::automata::lex_weight::BP_TIER_CROSSCAT_PROJECTION
                            * f64::from(span_len.max(1)),
                        coercion_cat,
                        rule_idx,
                    )
                } else {
                    mettail_prattail::wpda_runtime::lex_one()
                }
            }

            fn single_hop_coercion_completion_weight(
                &self,
                from_cat: u16,
                to_cat: u16,
                coercion_cat: u16,
                rule_idx: u16,
                span_len: u32,
            ) -> mettail_prattail::automata::lex_weight::LexicographicWeight {
                let _ = (from_cat, to_cat);
                let extra_span = span_len.saturating_sub(1);
                if coercion_cat == to_cat && extra_span > 0 {
                    mettail_prattail::wpda_runtime::lex_w(
                        mettail_prattail::automata::lex_weight::BP_TIER_CROSSCAT_PROJECTION
                            * f64::from(extra_span),
                        coercion_cat,
                        rule_idx,
                    )
                } else {
                    mettail_prattail::wpda_runtime::lex_one()
                }
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

            fn trigger_unary_wrappers_into(&self, from_cat: u16, to_cat: u16) -> &'static [u16] {
                // RC-B (2026-06-19): all trigger-bearing unary wrappers for
                // `(from_cat, to_cat)`, including same-category wrappers.
                // Callers filter by keyword and action evidence so ambiguity
                // is preserved until the observed wrapper token rejects it.
                #trigger_unary_wrappers_into_body
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

            fn category_accepts_operator_at_floor(
                &self,
                cat: u16,
                token_text: &str,
                floor: u8,
            ) -> bool {
                #category_accepts_operator_at_floor_body
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
/// that calls the per-category `infix_bp_<cat>(text)` lookup helper. GEN-1 B-2
/// (Stage S0): evaluates to `&'static [(u8, u8, u16, u16)]` (l_bp, r_bp,
/// result_src, rule_idx) — a slice of every infix rule sharing the trigger,
/// capped to `GEN1_MAX_SLICE` at codegen (1 at S0 ⇒ at most the legacy
/// single-winner element). `_ => &[]` for unknown categories.
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
                _ => &[],
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
                mettail_prattail::wpda_transitions::control::operator_recognized(
                    || #infix_fn(next_tok), || #postfix_fn(next_tok), || #mixfix_fn(next_tok),
                )
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
                mettail_prattail::wpda_transitions::control::operator_recognized(
                    || #infix_fn(token_text), || #postfix_fn(token_text), || #mixfix_fn(token_text),
                )
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

/// Body for `WpdaEngine::category_accepts_operator_at_floor(cat, token_text, floor)`.
///
/// Binding-power values are category-local, so this query intentionally uses
/// only the queried category's own operator tables. It answers whether the
/// category recognizes `token_text` as an operator whose left binding power is
/// high enough for the active Pratt floor.
fn emit_category_accepts_operator_at_floor_body(categories: &[String]) -> TokenStream {
    let arms = categories.iter().enumerate().map(|(i, cat)| {
        let i_u16 = i as u16;
        let infix_fn = quote::format_ident!("infix_bp_{}", cat.to_lowercase());
        let postfix_fn = quote::format_ident!("postfix_bp_{}", cat.to_lowercase());
        let mixfix_fn = quote::format_ident!("mixfix_bp_{}", cat.to_lowercase());
        quote! {
            #i_u16 => {
                mettail_prattail::wpda_transitions::control::operator_at_floor(
                    floor, || #infix_fn(token_text), || #postfix_fn(token_text), || #mixfix_fn(token_text),
                )
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

/// GEN-1 B-2 (Stage S0): evaluates to `&'static [(u8, u16, u16)]`
/// (l_bp, result_src, rule_idx) — a slice of every postfix rule sharing the
/// trigger, capped to `GEN1_MAX_SLICE` at codegen. `_ => &[]` for unknown cats.
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
                _ => &[],
            }
        }
    }
}

/// B7 Pattern 1: emit the per-category mixfix BP dispatch — `match
/// state_cat_src_idx` calling the per-category `mixfix_bp_<cat>(text)`
/// lookup. GEN-1 B-2 (Stage S0): evaluates to `&'static [(u8, u16, u16)]`
/// (left_bp, result_src, rule_idx) — a slice of every mixfix trigger keyword
/// (sharing the trigger) whose left operand is in the dispatched category,
/// capped to `GEN1_MAX_SLICE` at codegen. `_ => &[]` for unknown categories.
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
                _ => &[],
            }
        }
    }
}
