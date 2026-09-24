//! Phase A.5: Collection rule classification + dispatch.
//!
//! Detects judgement-style rules that parse a collection literal, e.g.,
//! Rholang's `PPar . ps:HashBag(Proc) |- "{" ps.*sep("|") "}" : Proc;`
//!
//! The parsed shape:
//! - `term_context = [Simple { name: ps, ty: Collection { coll_type: HashBag, element: Proc } }]`
//! - `syntax_pattern = [Literal("{"), Op(Sep { collection: ps, separator: "|", ... }), Literal("}")]`
//!
//! Classification yields `CollectionShape { open_token, has_synth_paren,
//! close, separator, element_cat, coll_kind, label }`. Engine integration emits a
//! collection-loop state machine: open → element-loop → close →
//! arity-1 action that pushes the constructed collection.

use mettail_ast::grammar::{GrammarRule, PatternOp, SyntaxExpr, TermParam};
use mettail_ast::language::{CollectionDelimiters, LanguageDef};
use mettail_ast::types::{CollectionType, TypeExpr};
use proc_macro2::TokenStream;
use quote::quote;
#[cfg(test)]
use std::collections::BTreeMap;
use std::collections::BTreeSet;

use crate::gen::term_param_walk::{TermParamLeafKind, TermParamLeaves};
use crate::gen::type_expr_walk::TypeExprBaseIdents;

use super::binder::{classify_binder_in, BinderPosition, BinderShape};
use mettail_prattail::wpda_rule_analysis::collection::assembly::{
    self as collection_assembly, CollectionAssemblyContext,
};
#[cfg(test)]
use mettail_prattail::wpda_rule_analysis::collection::assembly::{
    binder_collection_infos, insert_collection_spec_arm, GeneratedCollectionSpec,
};

struct MacroCollectionAssemblyContext<'language> {
    language: &'language LanguageDef,
}

#[cfg(test)]
pub(crate) fn original_collection_descriptors_for_test(
    language: &LanguageDef,
    categories: &[String],
    per_cat: &[Vec<GrammarRule>],
) -> Vec<collection_assembly::GeneratedCollectionSpecArm> {
    collection_assembly::try_build_collection_specs(
        categories,
        per_cat,
        &mut MacroCollectionAssemblyContext { language },
    )
    .expect("captured static collection descriptors must be valid")
}

impl<'source> CollectionAssemblyContext<'source, GrammarRule>
    for MacroCollectionAssemblyContext<'_>
{
    type Error = std::convert::Infallible;
    type Label = &'source syn::Ident;

    fn try_infix(
        &mut self,
        rule: &'source GrammarRule,
    ) -> Result<Option<mettail_prattail::binding_power::InfixRuleInfo>, Self::Error> {
        Ok(super::infix::classify_rule_public(rule))
    }

    fn try_collection(
        &mut self,
        rule: &'source GrammarRule,
    ) -> Result<Option<CollectionShape>, Self::Error> {
        Ok(classify_collection(rule, self.language))
    }

    fn try_binder(
        &mut self,
        rule: &'source GrammarRule,
    ) -> Result<Option<BinderShape>, Self::Error> {
        Ok(classify_binder_in(rule, self.language))
    }

    fn try_label(&mut self, rule: &'source GrammarRule) -> Result<Self::Label, Self::Error> {
        Ok(&rule.label)
    }
}

/// Classification of a collection-literal rule.
pub type CollectionShape =
    mettail_prattail::wpda_rule_analysis::collection::CollectionShape<CollectionType>;

pub(crate) fn collect_structural_delimiters(
    language: &LanguageDef,
    per_cat: &[Vec<GrammarRule>],
) -> (BTreeSet<String>, BTreeSet<String>) {
    collection_assembly::try_collect_structural_delimiters(
        per_cat,
        &mut MacroCollectionAssemblyContext { language },
    )
    .expect("static collection delimiter observations are infallible")
}

fn has_binder_internal_collection_slot(positions: &[BinderPosition]) -> bool {
    let mut work: Vec<&BinderPosition> = positions.iter().rev().collect();
    while let Some(position) = work.pop() {
        match position {
            BinderPosition::ParamParse { collection: Some(_), .. }
            | BinderPosition::BinderListLoop { collection_param_cat: Some(_), .. } => return true,
            BinderPosition::OptionalGroup { positions: inner_positions, .. } => {
                work.extend(inner_positions.iter().rev());
            },
            _ => {},
        }
    }
    false
}

/// Stage 3 (2026-06-27): the SINGLE key/value-separator resolver for collection
/// slots. The three formerly-independent kv-sources now route through this one
/// function, so they provably read the SAME value for every `(src, rule, slot)`:
///
/// 1. inline binder-param slots — [`super::binder::classify_binder_in`] (the
///    `ms.*sep(",")` collection in a Class-2/3 binder rule),
/// 2. declared-category collection literals — [`classify_collection`]'s
///    `pair_separator`,
/// 3. the lexer terminal set — `find_collection_info` in
///    `crate::gen::syntax::parser::prattail_bridge`.
///
/// Resolution: **the container type decides whether a key/value separator exists
/// at all**; the declared delimiters only choose its spelling. A `HashMap`/
/// `PathMap` slot resolves to the declared `key_val_sep` when one is in scope and
/// to the `":"` default otherwise; a `Vec`/`HashBag`/`HashSet` slot is `None`
/// unconditionally, *including* when the enclosing category declares a
/// `key_val_sep`.
///
/// ★ ROOT 3 (2026-07-29, #151) — why the type gate is load-bearing. Until this
/// fix the resolver read `declared.key_val_sep` *before* looking at `coll_type`:
///
// ignore-justification: historical pre-fix expression intentionally names the surrounding generator's `declared` and `coll_type` bindings and enum variants; making it standalone would obscure the exact faulty branch order being documented.
/// ```ignore
/// declared.and_then(|d| d.key_val_sep.clone())
///     .or_else(|| match coll_type { HashMap | PathMap => Some(":"), _ => None })
/// ```
///
/// [`super::binder::classify_binder_in`] resolves `declared_delims` from the
/// rule's **own result category**, on the premise that a binder rule's category
/// is a host category like `Proc`/`Name` and therefore never a declared
/// collection. That premise is false: the auto-injected higher-order-literal
/// (`MVar`/`MApply*`) variants exist in *every* category, including rholang's
/// `Map` and `Pathmap`, which **are** declared collection categories carrying
/// `key_val_sep: Some(":")`. So `MApplyProc(Arc<Map>, Vec<Proc>)` — whose slot is
/// a `Vec`, not a map — inherited `":"` from its home category and was classified
/// `is_kv` by the walker (`prattail/src/wpda_walker.rs`, the `CollectionMarker`
/// close). MEASURED at HEAD `8c946bff`: 42 of rholang's generated collection
/// slots carried `kv_sep: Some(":")` where only **2** are genuine kv rules
/// (`MapLit`, `PathmapLit`); the other 40 were `Vec` slots wearing a map's
/// separator, hence graded by the kv arity gate (`items == 2·(seps+1)`) instead
/// of the sequence gate (`items == seps+1`) and skipped by the element-category
/// gate.
///
/// Byte-identity (existing corpus): the inline-binder and lexer sources that pass
/// `declared = None` are unaffected — they already reduced to
/// `type_default(coll_type)`. The declared-category source is unaffected for
/// genuine `Map`/`Pathmap` literal rules, whose `coll_type` is `HashMap`/
/// `PathMap` and whose declared `key_val_sep` is `Some(":")`. Only the
/// `Vec`-in-a-collection-category case moves, and it moves from a wrong answer to
/// the right one.
///
/// `PathMap` note: `PathMap` NEVER lexes as an inline collection type
/// (`ast/src/types.rs` accepts only `Vec | HashBag | HashSet | HashMap` inline,
/// and `binder.rs` rejects it at its `_ => return None` collection arm), so its
/// only live sources are the declared-category and lexer-terminal paths — both
/// handled uniformly here.
pub(crate) fn kv_sep_for(
    coll_type: &CollectionType,
    declared: Option<&CollectionDelimiters>,
) -> Option<String> {
    mettail_prattail::wpda_rule_analysis::collection::kv_sep_for(coll_type, || {
        declared.and_then(|d| d.key_val_sep.as_deref())
    })
}

/// Try to classify a `GrammarRule` as a collection-literal rule.
///
/// Accepts both 3- and 4-element syntax patterns:
/// - 3-element: `[Literal(open), Op(Sep), Literal(close)]` — explicit single-token
///   open delimiter (e.g., Rholang's `"{" ... "}"`).
/// - 4-element: `[Literal(open_kw), Literal("("), Op(Sep), Literal(close)]` — the
///   default form from `synthetic.rs` where `synthetic.rs` splits `"list("` into
///   `["list", "("]` so the lexer (which tokenizes whitespace between tokens)
///   sees them as two separate `Fixed` tokens. The engine consumes both before
///   pushing the marker via `WpdaState::CollectionOpenParen`.
///
/// `language` is consulted to look up the `pair_separator` for Map collections —
/// `LangType::collection_kind = Some(CollectionCategory::Map(d))` carries
/// `d.key_val_sep` (e.g., `":"`) which encodes the inter-pair separator.
pub(crate) fn classify_collection(
    rule: &GrammarRule,
    language: &LanguageDef,
) -> Option<CollectionShape> {
    use mettail_prattail::wpda_rule_analysis::collection_projection::try_project_collection_rule_in;

    // Keep every authored position. Unlike the infix projection, a Sep with
    // a source is unsupported here and must not become an accepted plain Sep.
    let view =
        try_project_collection_rule_in(&super::binder::MacroBinderSyntaxReader, rule, |_, _| {
            Ok::<_, std::convert::Infallible>(())
        })
        .expect("original AST collection observations are valid and admitted");
    mettail_prattail::wpda_rule_analysis::collection::classify_collection(&view, || {
        // Retain the original first-match result-category lookup, lazily after
        // successful structural classification, using the original Ident.
        language
            .types
            .iter()
            .find(|t| t.name == rule.category)
            .and_then(|t| t.collection_kind.as_ref())
            .and_then(|c| kv_sep_for(&c.coll_type(), Some(c.delimiters())))
    })
}

/// ROOT-A (2026-06-27): detect the cross-cat collection projections that COLLIDE
/// with a braced collection rule on its open token.
///
/// A collision exists when a rule in the SAME result category is classified by
/// [`prefix::classify_atomic`] as `CrossCatProjection { source }` where `source`
/// is a collection-kind category (`collection_kind.is_some()`) whose open
/// FIRST-token — trailing `(` trimmed exactly as `prefix.rs:594` does so the
/// token equals the lexer's first emitted `Fixed` token — equals this collection
/// rule's open token.
///
/// The defect this guards: at Rholang's `Proc` entry the open `{` is a single
/// (non-lex-ambiguous) token, so the lex-fork is SKIPPED and the braced `PPar`
/// arm commits a bare `ConsumeAndPush(collection_marker)` before the registered
/// `Map` projection alternative (`CastMap . m:Map |- m : Proc`, Map open `{`)
/// can be tried — so `{1:2}` is lost. Emitting the projection branch(es)
/// directly into the prefix arm keeps the Map reading reachable.
///
/// Returns `(source_src_idx, proj_rule_idx)` per colliding projection, where
/// `proj_rule_idx` is the projection rule's index within its category's
/// `per_cat` row (the runtime `rule_idx`). An empty result selects the
/// no-collision fast path (the byte-identical bare `ConsumeAndPush`).
///
/// Formally verified: `formal/rocq/.../CollectionPrefixDispatchFork.v` (no-loss,
/// no-spurious-accept, decisive mutual-exclusion, empty-collection tie-break to
/// the primary, fast-path identity, frontier-delta ≤ 1 — all zero-admission) and
/// `formal/tla/prattail_wpda` `CollectionFork` scenario.
fn collection_open_collision_projections(
    language: &LanguageDef,
    categories: &[String],
    rules_in_result_cat: &[GrammarRule],
    open_token: &str,
) -> Vec<(u16, u16)> {
    let mut out = Vec::new();
    for (rule_i, rule) in rules_in_result_cat.iter().enumerate() {
        let super::prefix::AtomicShape::CrossCatProjection { source_cat_name, .. } =
            super::prefix::classify_atomic(rule, language)
        else {
            continue;
        };
        let Some(lang_type) = language
            .types
            .iter()
            .find(|t| t.name.to_string() == source_cat_name)
        else {
            continue;
        };
        let Some(coll_kind) = lang_type.collection_kind.as_ref() else {
            continue;
        };
        // Stage 2 (2026-06-27): one delimiters() accessor in place of a
        // per-variant `match coll_kind { List(d) => &d.open, ... }`.
        let open = &coll_kind.delimiters().open;
        // Mirror prefix.rs:594 — trim a trailing `(` so the open FIRST token
        // matches the lexer's first emitted `Fixed` token (`list(` → `list`).
        if open.trim_end_matches('(') != open_token {
            continue;
        }
        let Some(source_src_idx) = categories.iter().position(|c| c == &source_cat_name) else {
            continue;
        };
        out.push((source_src_idx as u16, rule_i as u16));
    }
    out
}

/// Phase 4: emit prefix-dispatch arms that recognize the open delimiter
/// of each collection-shaped rule. On match, the arm pushes a
/// `CollectionMarker` symbol carrying `(result_src_idx, rule_idx,
/// slot_idx)`. The walker allocates a fresh runtime accumulator id when the
/// marker is pushed and carries that id through the CollectionId action
/// argument that the finalize action consumes.
///
/// After the open delim, the new_state is `PrefixDispatch{cur_bp:0}`. The
/// frontier_top is the marker, whose `category_src_idx == result_src_idx`.
/// For self-collections (Rholang PPar: HashBag(Proc) in Proc), this routes
/// the first-element parse to the right category. For cross-cat collections
/// (e.g. `Vec<Int>` in some `List` category), the open arm pushes an
/// additional CategoryEntry(element_src_idx) frame to redirect dispatch.
///
/// Arms guard on `state_cat_src_idx == result_src_idx` so the same open
/// delimiter routes to different collection rules per category.
pub(crate) fn emit_collection_prefix_arms(
    language: &mettail_ast::language::LanguageDef,
    categories: &[String],
    per_cat: &[Vec<GrammarRule>],
) -> TokenStream {
    let mut arms = Vec::new();
    for (cat_i, rules) in per_cat.iter().enumerate() {
        for (rule_i, rule) in rules.iter().enumerate() {
            let Some(shape) = classify_collection(rule, language) else {
                continue;
            };
            let result_src_idx = cat_i as u16;
            let rule_idx = rule_i as u16;
            // The lexer emits the open keyword as a single `Fixed` token
            // matching `shape.open_token` (e.g. `"list"` for the default
            // form, or `"{"` for explicit-delimited 3-element rules).
            // For 4-element forms (`has_synth_paren = true`), the next
            // token is `Fixed("(")` which the engine consumes via
            // `WpdaState::CollectionOpenParen` BEFORE entering the
            // first-element parse. For 3-element forms, the prefix arm
            // transitions directly to `PrefixDispatch`.
            let open_token = &shape.open_token;
            // Look up the element category's src_idx (for both self and
            // cross-cat). Required by CollectionOpenParen so the engine
            // arm knows whether to push CategoryEntry for cross-cat.
            let Some(element_src) = lookup_element_src_idx(&shape.element_cat, categories) else {
                continue;
            };
            let new_state = if shape.has_synth_paren {
                quote! {
                    WpdaState::CollectionOpenParen {
                        result_src_idx: #result_src_idx,
                        rule_idx: #rule_idx,
                        element_src_idx: #element_src,
                        outer_bp: *cur_bp,
                    }
                }
            } else {
                quote! {
                    WpdaState::PrefixDispatch {
                        pos: tokens.next_pos(*pos, 0).unwrap_or(*pos + 1),
                        cur_bp: 0,
                    }
                }
            };
            // ROOT-A (2026-06-27): does this open token collide with a cross-cat
            // collection projection sharing the open token? If so, FORK into the
            // PPar collection marker (the primary) + the Map projection(s); else
            // emit the byte-identical bare ConsumeAndPush (no-collision fast path).
            // FV: CollectionPrefixDispatchFork.v + TLA CollectionFork scenario.
            let collisions =
                collection_open_collision_projections(language, categories, rules, open_token);
            if collisions.is_empty() {
                // ── No-collision fast path: byte-identical bare ConsumeAndPush. ──
                arms.push(quote! {
                    Some(mettail_prattail::automata::TokenKind::Fixed(__open))
                        if __open == #open_token && state_cat_src_idx == #result_src_idx => {
                        return WpdaStepAction::ConsumeAndPush {
                            symbol: StackSymbolV2::collection_marker(
                                // str-cast collection-infix fix (2026-06-18): capture the
                                // enclosing Pratt dispatch bp (*cur_bp) on the marker so
                                // the collection close resumes InfixLoop at that precedence
                                // (a finalized collection joins the enclosing Pratt loop
                                // like an atomic primary). Covers both the synth-paren and
                                // direct-delimited open paths (shared ConsumeAndPush).
                                #result_src_idx, #rule_idx, 0, *cur_bp,
                            ),
                            weight: lex_w(0.0, #result_src_idx, #rule_idx),
                            new_state: #new_state,
                            // Phase F.8: collection open delimiter discards
                            // the trigger token.
                            trigger_mode: mettail_prattail::wpda_walker::TriggerMode::Discard,
                        };
                    }
                });
            } else {
                // ── Collision: fork into branch0 (PPar collection marker, the
                // PRIMARY infix tier weight 0.0) + branch1+ (one Map cross-cat
                // projection per colliding rule, BP_TIER_CROSSCAT_PROJECTION =
                // 0.025). The empty `{}` ties to the primary by the 0.0 < 0.025
                // weight ordering (empty_collection_tie_breaks_to_primary). Branch
                // shapes mirror forks.rs:272-292 (projection) + the singleton
                // projection arm prefix.rs:1480-1491, and the marker branch
                // mirrors the no-collision ConsumeAndPush above. ──
                let proj_branches: Vec<TokenStream> = collisions
                    .iter()
                    .map(|(source_src_idx, proj_rule)| {
                        let source_src_idx = *source_src_idx;
                        let proj_rule = *proj_rule;
                        quote! {
                            mettail_prattail::wpda_walker::ForkBranch {
                                symbol: StackSymbolV2::rule_at(
                                    #result_src_idx, #proj_rule, 0, Some(*cur_bp),
                                ).with_kind_return(),
                                weight: lex_w(
                                    mettail_prattail::automata::lex_weight::BP_TIER_CROSSCAT_PROJECTION,
                                    #result_src_idx,
                                    #proj_rule,
                                ),
                                new_state: WpdaState::CrossCatDelegate {
                                    source_src_idx: #source_src_idx,
                                    inner_cur_bp: *cur_bp,
                                },
                                // Unified Fix A (ROOT C): route the Map cross-cat
                                // projection through the SINGLETON uncached push so
                                // it reconciles in its OWN binder frame (not the
                                // cohort broadcast that drops it). FV:
                                // ForkSurvivorBinderPop.v.
                                action_kind:
                                    mettail_prattail::wpda_walker::ForkActionKind::PushProjectionInline,
                            }
                        }
                    })
                    .collect();
                arms.push(quote! {
                    Some(mettail_prattail::automata::TokenKind::Fixed(__open))
                        if __open == #open_token && state_cat_src_idx == #result_src_idx => {
                        return WpdaStepAction::Fork {
                            branches: vec![
                                // branch0 — the PPar collection marker (primary,
                                // weight BP_TIER_INFIX = 0.0). Discards the open
                                // trigger token, like the no-collision path.
                                mettail_prattail::wpda_walker::ForkBranch {
                                    symbol: StackSymbolV2::collection_marker(
                                        #result_src_idx, #rule_idx, 0, *cur_bp,
                                    ),
                                    weight: lex_w(0.0, #result_src_idx, #rule_idx),
                                    new_state: #new_state,
                                    action_kind:
                                        mettail_prattail::wpda_walker::ForkActionKind::ConsumeAndPush {
                                            trigger_mode:
                                                mettail_prattail::wpda_walker::TriggerMode::Discard,
                                        },
                                },
                                // branch1+ — the Map cross-cat projection(s).
                                #(#proj_branches),*
                            ],
                            // Each branch's action_kind encodes its own consume
                            // semantics (Discard for the marker, no-consume Push
                            // for the projection).
                            consume_trigger: false,
                        };
                    }
                });
            }
        }
    }
    quote! { #(#arms)* }
}

/// Phase 4: emit the body of `WpdaState::CollectionLoop`. Looks up the
/// close + separator for the marker's `(result_src_idx, rule_idx)`, then
/// dispatches: token == close → `ConsumeAndPop` (fires finalize); token
/// == sep → `Consume` → `PrefixDispatch{cur_bp:0}` to parse next element;
/// else → `Error`.
///
/// Phase 4 #5b (2026-05-12): for HashMap collection slots the dispatch is
/// 3-phased per `kv_phase`:
/// - `0`: outer dispatch — 3-branch Fork (close / inter-pair-sep
///   / first-key element). Vec/HashBag/HashSet always stay at `0`.
/// - `1`: single-arm Consume(`:`) → `kv_phase: 2`. Error if token != `:`.
/// - `2`: single-arm Push CategoryEntry(element_src) → PrefixDispatch.
///   The walker patches kv_phase back to 0 when the value returns via
///   Unwinding-CollectionMarker (parity-driven in `set_cursor_inner_state`).
pub(crate) fn emit_collection_loop_arm(
    language: &mettail_ast::language::LanguageDef,
    _categories: &[String],
    per_cat: &[Vec<GrammarRule>],
) -> TokenStream {
    // Stage 2 consolidation (2026-06-27): the per-slot (close, sep, kv_sep,
    // is_binder_internal) tuple this arm used to build inline now lives in the
    // single `collection_spec(src, rule, slot)` table
    // (emit_collection_spec_table). The arm reads the fields it needs off that
    // one `CollectionSpec` record.
    if !has_any_collection_slot(language, per_cat) {
        return quote! { WpdaStepAction::Idle };
    }
    quote! {
        mettail_prattail::wpda_transitions::collection_loop::collection_loop_step(
            self.0,
            result_src_idx,
            rule_idx,
            _element_src_idx,
            _outer_bp,
            _accumulator_id,
            slot_idx,
            kv_phase,
            _pos,
            tokens,
            lex_w,
            |src_idx, kind| self.collection_element_can_start(src_idx, kind),
        )
    }
}

/// Stage 2 consolidation (2026-06-27): emit the body of
/// `WpdaEngine::collection_spec` — the SINGLE per-(result_src_idx, rule_idx,
/// slot_idx) → `CollectionSpec` table. Supersedes the four former per-field
/// lookups (`emit_collection_close_lookup`, `emit_collection_close_sep_lookup`,
/// `emit_collection_element_src_lookup`, `emit_kv_separator_for_collection`)
/// and the inline `(close, sep, kv_sep, is_binder_internal)` tuple
/// `emit_collection_loop_arm` used to build. Every collection slot — a Class-5
/// literal rule (single slot at slot_idx=0) or a Class-2/3 binder-internal
/// slot (one arm per `binder_collection_infos` entry) — maps to ONE record.
///
/// BYTE-IDENTITY with the former tables, projected per consumer:
/// - `close` / `sep` are always present (the former close / (close, sep)
///   lookups, whose domain was every collection slot — exactly this domain).
/// - `kv_sep` is `Some(..)` iff the slot is a kv-map, else `None`, so
///   `collection_spec(..).and_then(|s| s.kv_sep)` reproduces the former
///   kv-separator table (domain: kv slots only).
/// - `element_src_idx` is `Some(..)` iff the element category resolves, else
///   `None`, so `.and_then(|s| s.element_src_idx)` reproduces the former
///   element-src table (domain: resolvable slots only).
/// - `close_resumes_via_unwinding` is the former loop-arm `is_binder_internal`
///   selector: `true` for binder-internal slots, `false` for Class-5.
/// - `open` / `has_synth_paren` carry the Class-5 open token; binder-internal
///   slots get `""` / `false` (no consumer reads them yet — open-side dispatch
///   stays in `emit_collection_prefix_arms`).
///
/// The iteration order (Class-5 first, else binder infos in order) matches the
/// former tables exactly, so the emitted arm order — hence duplicate-key
/// resolution — is preserved.
///
/// NOTE (R5): the 2-tuple `is_binder_internal_collection(src, rule)`
/// FireAction-suppression query (`emit_is_binder_internal_collection_lookup`)
/// stays a SEPARATE method — it is keyed without a slot and is not a per-slot
/// field of this record.
pub(crate) fn emit_collection_spec_table(
    language: &mettail_ast::language::LanguageDef,
    categories: &[String],
    per_cat: &[Vec<GrammarRule>],
) -> TokenStream {
    let arms = match collection_assembly::try_build_collection_specs(
        categories,
        per_cat,
        &mut MacroCollectionAssemblyContext { language },
    ) {
        Ok(arms) => arms,
        Err(error) => {
            let message = error.to_string();
            return quote! {{
                compile_error!(#message);
                let _ = (result_src_idx, rule_idx, slot_idx);
                None
            }};
        },
    };
    if arms.is_empty() {
        return quote! {
            {
                let _ = (result_src_idx, rule_idx, slot_idx);
                None
            }
        };
    }
    let rendered_arms: Vec<TokenStream> = arms
        .iter()
        .map(|arm| {
            let (result_src_idx, rule_idx, slot_idx) = arm.key;
            let spec = &arm.spec;
            let open = &spec.open;
            let has_synth_paren = spec.has_synth_paren;
            let close = &spec.close;
            let sep = &spec.sep;
            let min_elements = spec.min_elements;
            let kv_sep = match &spec.kv_sep {
                Some(value) => quote! { Some(#value) },
                None => quote! { None },
            };
            let kv_value_optional = spec.kv_value_optional;
            let element_src_idx = match spec.element_src_idx {
                Some(value) => quote! { Some(#value) },
                None => quote! { None },
            };
            let close_resumes_via_unwinding = spec.close_resumes_via_unwinding;
            quote! {
                (#result_src_idx, #rule_idx, #slot_idx) => Some(
                    mettail_prattail::wpda_runtime::CollectionSpec {
                        open: #open,
                        has_synth_paren: #has_synth_paren,
                        close: #close,
                        sep: #sep,
                        min_elements: #min_elements,
                        kv_sep: #kv_sep,
                        kv_value_optional: #kv_value_optional,
                        element_src_idx: #element_src_idx,
                        close_resumes_via_unwinding: #close_resumes_via_unwinding,
                    }
                ),
            }
        })
        .collect();
    quote! {
        match (result_src_idx, rule_idx, slot_idx) {
            #(#rendered_arms)*
            _ => None,
        }
    }
}

/// Stage 2 helper (2026-06-27): does this language declare ANY collection slot
/// (a Class-5 literal rule, or a binder rule with at least one internal
/// collection slot)? Used by `emit_collection_loop_arm` to preserve the former
/// `lookup_arms.is_empty()` short-circuit to `WpdaStepAction::Idle` for
/// languages with no collections.
fn has_any_collection_slot(
    language: &mettail_ast::language::LanguageDef,
    per_cat: &[Vec<GrammarRule>],
) -> bool {
    collection_assembly::try_has_any_collection_slot(
        per_cat,
        &mut MacroCollectionAssemblyContext { language },
    )
    .expect("static collection slot discovery requires representable coordinates")
}

fn lookup_element_src_idx(element_cat: &str, categories: &[String]) -> Option<u16> {
    collection_assembly::try_lookup_element_src_idx::<std::convert::Infallible>(
        element_cat,
        categories,
    )
    .expect("static collection element category requires a u16 coordinate")
}

/// GEN-1 B-3 (Stage S3): the `*sep` repetition `MixfixPart`s of a rule, as
/// `(part_idx, element_category, separator, close_terminals)` tuples.
///
/// Empty unless `rule` is a Param-prefixed infix/mixfix rule with a CLASSIFIED
/// repetition operand (e.g. POutput2Plus `n "!" "(" a "," bs.*sep(",") ")"`). This
/// REUSES the infix classifier (`super::infix::classify_rule_public`) so the
/// per-result-category B-3 stage gate (`gen1_rep_classify_enabled`) is the SINGLE
/// source of truth: a ForRow `&`-join rep rule classifies to `None` and therefore
/// yields no rep slots here (no `collection_spec` / `is_binder_internal_collection`
/// entry), keeping it byte-identical to baseline. Collection-literal rules
/// (`"{" ps.*sep("|") "}"`) and binder rules start with a literal / are handled by
/// their own classifiers, so they classify to non-mixfix or `None` here and never
/// collide with a rep slot's `(result_src, rule_idx, part_idx)` key.
fn mixfix_rep_slots(rule: &GrammarRule) -> Vec<(u8, String, String, Vec<String>, u8)> {
    collection_assembly::try_mixfix_rep_slots_with::<std::convert::Infallible>(|| {
        Ok(super::infix::classify_rule_public(rule))
    })
    .expect("static collection repetition requires a u8 part coordinate")
}

/// Emit the grammar-derived FIRST-set predicate used by collection entry and
/// no-separator continuation.  It reuses the same closure computation and
/// token patterns as ordinary prefix dispatch, so collection control flow
/// cannot drift from the element parser it is about to invoke.
pub(crate) fn emit_collection_element_prefix_predicate(
    language: &mettail_ast::language::LanguageDef,
    categories: &[String],
) -> TokenStream {
    let mut category_arms = Vec::new();
    for (category_src_idx, category) in categories.iter().enumerate() {
        let first_arms = super::prefix::first_set_of_category(category, language)
            .into_iter()
            .map(|first| {
                let pattern = first.pattern;
                match first.extra_guard {
                    Some(guard) => quote! { #pattern if #guard => true, },
                    None => quote! { #pattern => true, },
                }
            })
            .collect::<Vec<_>>();
        let category_src_idx = category_src_idx as u16;
        category_arms.push(quote! {
            #category_src_idx => match Some(kind) {
                #(#first_arms)*
                _ => false,
            },
        });
    }
    quote! {
        #[inline]
        fn collection_element_can_start(
            &self,
            category_src_idx: u16,
            kind: &mettail_prattail::automata::TokenKind,
        ) -> bool {
            match category_src_idx {
                #(#category_arms)*
                _ => false,
            }
        }
    }
}

/// Trigger-ownership soundness (2026-07-02): emit a per-rule lookup that
/// returns true when `(result_src_idx, rule_idx)` identifies a rule whose
/// surface syntax pattern BEGINS with a structural literal trigger (its first
/// `SyntaxExpr` is a `Literal`, e.g. `@ p` NQuoteShort, `int ( a )` casts, `-
/// a` Neg). Consumed by the walker's `emit_fire_action` walk-back drain to gate
/// the `pos_match` fallback that claims a leading `TriggerTerminal` at the
/// firing rule's frame-start position.
///
/// ROOT (trace-pinned, rholang `@Nil!!(x,y)` name/proc display roundtrip): a
/// lex-ambiguous keyword (`Nil` = `Fixed("Nil") | Ident`) at a send channel
/// admits a phantom reading where the `@` structural trigger (owner: the
/// `@`-prefix send rule, e.g. POutputQuoted) is claimed by an OPERAND-leading
/// rule (PPersistOutput2Plus `n "!!" "(" a "," bs ")"`, whose first element is
/// the Name operand `n`, NOT a trigger) via the pos-only fallback — because that
/// rule's frame happens to start at the `@` position (reached through the
/// `@`→Name cross-cat delegation). The resulting AST binds `Nil` as the name
/// variable `NVar("Nil")` and drops the `@`, displaying as bare `Nil!!(...)`
/// which the grammar REJECTS (`Nil` is the reserved null-process keyword). This
/// violates parser soundness: `parse(display(t))` must succeed for any `t` the
/// parser returns. The `pos_match` fallback was introduced only to repair an
/// AMBIGUOUSLY-OWNED-BUT-CORRECTLY-POSITIONED prefix trigger of a rule that
/// ACTUALLY HAS a leading trigger (the `@{map}` binder case); it must NOT fire
/// for an operand-leading rule that has no leading trigger of its own. Gating
/// `pos_match` on this predicate confines the fallback to genuine prefix rules,
/// eliminating the phantom while preserving the `@{map}` repair.
///
/// Grammar-derived (first `SyntaxExpr` is a `Literal`); no per-rule/per-language
/// hardcode. Default (empty) is `false` ⇒ the gate is conservative: pos_match is
/// disabled for every rule unless it demonstrably begins with a trigger.
pub(crate) fn emit_rule_has_leading_structural_trigger_lookup(
    _language: &LanguageDef,
    per_cat: &[Vec<GrammarRule>],
) -> TokenStream {
    let mut arms = Vec::new();
    for (cat_i, rules) in per_cat.iter().enumerate() {
        for (rule_i, rule) in rules.iter().enumerate() {
            let leads_with_literal = rule
                .syntax_pattern
                .as_ref()
                .map(|sp| matches!(sp.first(), Some(SyntaxExpr::Literal(_))))
                .unwrap_or(false);
            if leads_with_literal {
                let result_src_idx = cat_i as u16;
                let rule_idx = rule_i as u16;
                arms.push(quote! {
                    (#result_src_idx, #rule_idx) => true,
                });
            }
        }
    }
    if arms.is_empty() {
        return quote! { false };
    }
    quote! {
        match (result_src_idx, rule_idx) {
            #(#arms)*
            _ => false,
        }
    }
}

/// ROOT-P Stage 4 (2026-07-08): emit a per-CATEGORY lookup returning `true` when
/// `src_idx` names a category that is BINDER-SCOPED — a category whose parses
/// may sit under (or constitute) a NON-context-free binder scope, so the GLL
/// pop-routing edge pair (`incoming_edge`/`incoming_edge_stack`) MUST be kept in
/// the merge key. Dropping the edge for such a category could over-merge two
/// scope-distinct cursors, whose subsequent pop-fan would attach an operand to a
/// scope-continuation it was never paired with — a category-valid but SPURIOUS
/// reading (red-team #2, the `@a<-@b` / `for` / `PNew` danger zone). Everything
/// else is context-free-INTERCHANGEABLE (sends `POutput*`, `NQuote` `@(p)`,
/// arithmetic, collections): its return context does not change the reading, so
/// its edge is DROPPABLE — the ROOT-P Stage-4 delivery lever.
///
/// A category `C` is marked binder-scoped iff, over the grammar's abstraction
/// (`BinderShape`) metadata:
///   (a) `C` is the RESULT category of a rule that opens a binder scope (a
///       `TermParam::Abstraction`/`MultiAbstraction`, i.e. emits
///       `StartBinderScope` — e.g. rholang `PNew . ^[xs].p:[Name* -> Proc] :
///       Proc`);
///   (b) `C` is a binder-PATTERN category — the abstraction DOMAIN (bound
///       position), e.g. `Name` in `[Name* -> Proc]`;
///   (c) [conservative closure] `C` is reachable, in the category-reference
///       graph (rule `A` references cat `B` when `B` is a base category in one
///       of `A`'s param types), from the BODY (codomain) or PATTERN (domain)
///       slot of ANY scope-opener. Marks over-broadly on purpose: a false KEEP
///       costs only delivery, a false DROP costs SOUNDNESS, so unsure ⇒ `true`.
///
/// DELIBERATELY NOT `rule_has_leading_structural_trigger` (which keys on "first
/// `SyntaxExpr` is a `Literal`" — `true` for @-sends AND `NQuote` AND
/// `InputBindQuoted` alike; the wrong axis for edge-drop).
///
/// Category-level (keyed on `src_idx` only). Empty (no scope-openers anywhere —
/// e.g. the calculator) ⇒ `false` for every category (all CF-interchangeable).
/// The trait method's own DEFAULT is `true` (keep-edge = safe); this codegen
/// override supplies the grammar-derived per-category truth.
pub(crate) fn emit_category_is_binder_scoped_lookup(
    _language: &LanguageDef,
    categories: &[String],
    per_cat: &[Vec<GrammarRule>],
) -> TokenStream {
    // Every Base category name mentioned anywhere in a `TypeExpr` (peels Arrow
    // domain/codomain, MultiBinder, Collection element, Map key/value, Refined
    // base).
    fn collect_base_cats(ty: &TypeExpr, out: &mut Vec<String>) {
        out.extend(TypeExprBaseIdents::new(ty).map(ToString::to_string));
    }
    fn arrow_domain_cats(ty: &TypeExpr, out: &mut Vec<String>) {
        if let TypeExpr::Arrow { domain, .. } = ty {
            collect_base_cats(domain, out);
        }
    }
    fn arrow_codomain_cats(ty: &TypeExpr, out: &mut Vec<String>) {
        if let TypeExpr::Arrow { codomain, .. } = ty {
            collect_base_cats(codomain, out);
        }
    }
    // Referenced categories of a rule (category-reference graph out-edges).
    fn rule_ref_cats(params: &[TermParam], out: &mut Vec<String>) {
        for leaf in TermParamLeaves::new(params, false) {
            match leaf.kind {
                TermParamLeafKind::Simple { ty, .. } => collect_base_cats(ty, out),
                TermParamLeafKind::Abstraction { ty, .. }
                | TermParamLeafKind::MultiAbstraction { ty, .. } => collect_base_cats(ty, out),
                TermParamLeafKind::GuardBody { .. } => {},
            }
        }
    }
    // A rule opens a binder scope iff a param (recursively) is an abstraction.
    fn opens_scope(params: &[TermParam]) -> bool {
        TermParamLeaves::new(params, false).any(|leaf| match leaf.kind {
            TermParamLeafKind::Abstraction { .. } | TermParamLeafKind::MultiAbstraction { .. } => {
                true
            },
            TermParamLeafKind::Simple { .. } | TermParamLeafKind::GuardBody { .. } => false,
        })
    }
    // (domain, codomain) base cats of a rule's abstraction params.
    fn scope_slot_cats(params: &[TermParam], dom: &mut Vec<String>, cod: &mut Vec<String>) {
        for leaf in TermParamLeaves::new(params, false) {
            match leaf.kind {
                TermParamLeafKind::Abstraction { ty, .. }
                | TermParamLeafKind::MultiAbstraction { ty, .. } => {
                    arrow_domain_cats(ty, dom);
                    arrow_codomain_cats(ty, cod);
                },
                _ => {},
            }
        }
    }

    let mut ref_graph: std::collections::BTreeMap<String, BTreeSet<String>> =
        std::collections::BTreeMap::new();
    let mut marked: BTreeSet<String> = BTreeSet::new(); // (a)+(b) direct marks
    let mut seed: BTreeSet<String> = BTreeSet::new(); // (c) closure seeds (body+pattern slots)
    for rules in per_cat.iter() {
        for rule in rules.iter() {
            let Some(params) = rule.term_context.as_ref() else {
                continue;
            };
            let cat = rule.category.to_string();
            let mut refs = Vec::new();
            rule_ref_cats(params, &mut refs);
            let entry = ref_graph.entry(cat.clone()).or_default();
            for r in refs {
                entry.insert(r);
            }
            if opens_scope(params) {
                marked.insert(cat.clone()); // (a) result category
                let (mut dom, mut cod) = (Vec::new(), Vec::new());
                scope_slot_cats(params, &mut dom, &mut cod);
                for d in dom {
                    marked.insert(d.clone()); // (b) pattern category
                    seed.insert(d); // (c) seed: pattern slot
                }
                for c in cod {
                    seed.insert(c); // (c) seed: body slot
                }
            }
        }
    }
    // (c) closure: BFS from the body+pattern slot seeds over the ref graph.
    let mut queue: std::collections::VecDeque<String> = seed.iter().cloned().collect();
    let mut reached: BTreeSet<String> = seed;
    while let Some(cur) = queue.pop_front() {
        marked.insert(cur.clone());
        if let Some(neigh) = ref_graph.get(&cur) {
            for n in neigh {
                if reached.insert(n.clone()) {
                    queue.push_back(n.clone());
                }
            }
        }
    }
    // Map marked category NAMES → runtime `src_idx` via the categories slice
    // (per_cat + categories share the runtime `category_src_idx` ordering).
    let mut arms = Vec::new();
    for (idx, name) in categories.iter().enumerate() {
        if marked.contains(name) {
            let sidx = idx as u16;
            arms.push(quote! { #sidx => true, });
        }
    }
    if arms.is_empty() {
        return quote! { false };
    }
    quote! {
        match src_idx {
            #(#arms)*
            _ => false,
        }
    }
}

/// B9 / Class 2 (2026-05-08): emit a per-rule lookup that returns true
/// when `(result_src_idx, rule_idx)` identifies a Class-2 binder rule's
/// internal collection slot. Used by the walker's CollectionMarker-pop
/// arm to SUPPRESS the default FireAction (the binder rule's terminal
/// action will drain the CollectionId at its own RuleAt pop, not at
/// CollectionMarker pop).
///
/// For Class-5 collection-rule CollectionMarkers, returns false → the
/// walker fires the collection-finalize action as today.
pub(crate) fn emit_is_binder_internal_collection_lookup(
    language: &LanguageDef,
    per_cat: &[Vec<GrammarRule>],
) -> TokenStream {
    let mut arms = Vec::new();
    for (cat_i, rules) in per_cat.iter().enumerate() {
        for (rule_i, rule) in rules.iter().enumerate() {
            // GEN-1 B-3 (Stage S3): a mixfix rule with a `*sep` repetition slot is
            // treated EXACTLY like a Class-2 binder-internal collection — its
            // CollectionMarker pop SUPPRESSES the collection-finalize FireAction so
            // the CollectionId flows to the enclosing mixfix-rule action, which
            // drains it (`drain_collection`). Emit `true` once per such rule.
            if !mixfix_rep_slots(rule).is_empty() {
                let result_src_idx = cat_i as u16;
                let rule_idx = rule_i as u16;
                arms.push(quote! {
                    (#result_src_idx, #rule_idx) => true,
                });
                continue;
            }
            let Some(shape) = classify_binder_in(rule, language) else {
                continue;
            };
            // Phase 2 / Redesign C follow-up (2026-05-11): extend the
            // discriminator to ALSO recognize Class 3 binder-internal
            // collections (BinderListLoop with `collection_param_cat`
            // set). Same conceptual role as Class 2's ParamParse
            // collection slot — the binder rule's terminal action
            // drains the CollectionId at outer RuleAt pop, so the
            // CollectionMarker pop must NOT fire its own action.
            // Prior to this extension, Class 3 rules (rholang PInputs)
            // were missing from the suppression table, causing spurious
            // PInputs action fire when `apply_pop_body_to_cursor`
            // popped the Class 3 CollectionMarker.
            let has_collection_slot = has_binder_internal_collection_slot(&shape.positions);
            if !has_collection_slot {
                continue;
            }
            let result_src_idx = cat_i as u16;
            let rule_idx = rule_i as u16;
            arms.push(quote! {
                (#result_src_idx, #rule_idx) => true,
            });
        }
    }
    if arms.is_empty() {
        return quote! { false };
    }
    quote! {
        match (result_src_idx, rule_idx) {
            #(#arms)*
            _ => false,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    include!("../../../../tests/support/owned_collection_reuse.rs");
    use mettail_ast::grammar::{rule_fixture, GrammarRule};
    use mettail_ast::language::CollectionCategory;
    use mettail_ast::types::CollectionType;
    use proc_macro2::Span;
    use syn::Ident;

    // ── ROOT 3 (#151, 2026-07-29): the container type decides whether a kv
    // separator exists; the declared delimiters only choose its spelling. ──
    //
    // The defect these pin: `MApplyProc(Arc<Map>, Vec<Proc>)` is an
    // auto-injected higher-order-literal variant whose *home category* is
    // rholang's `Map` (a declared collection carrying `key_val_sep: Some(":")`)
    // but whose *slot* is a `Vec`. `binder::classify_binder_in` resolves
    // `declared_delims` from the home category, so this `Vec` slot used to
    // inherit `":"` and be classified `is_kv` by the walker — putting 40 of
    // rholang's 42 generated kv slots under the wrong arity gate. MEASURED at
    // HEAD `8c946bff`.

    /// Row G of the #151/#74 RED — the cheapest one in the set: a pure
    /// macro-crate unit test that needs no `languages` build.
    #[test]
    fn kv_sep_for_vec_in_a_map_category_is_none() {
        let map_delims = CollectionCategory::map_defaults();
        assert_eq!(
            map_delims.key_val_sep.as_deref(),
            Some(":"),
            "fixture precondition: a declared Map category carries `:`"
        );
        assert_eq!(
            kv_sep_for(&CollectionType::Vec, Some(&map_delims)),
            None,
            "a `Vec` slot has no key/value separator even when its enclosing \
             category declares one (ROOT 3: the auto-injected `MApply*` HOL \
             variants live in the `Map`/`Pathmap` categories but carry `Vec` \
             slots)"
        );
    }

    /// The same rule for the other two non-kv container types, so the fix is a
    /// class fix rather than a `Vec`-shaped instance fix.
    #[test]
    fn kv_sep_for_bag_and_set_in_a_map_category_are_none() {
        let map_delims = CollectionCategory::map_defaults();
        assert_eq!(kv_sep_for(&CollectionType::HashBag, Some(&map_delims)), None);
        assert_eq!(kv_sep_for(&CollectionType::HashSet, Some(&map_delims)), None);
    }

    /// The control that proves the fix is surgical: genuine kv containers keep
    /// resolving, declared spelling first, `":"` default second.
    #[test]
    fn kv_sep_for_genuine_kv_containers_is_unchanged() {
        let map_delims = CollectionCategory::map_defaults();
        assert_eq!(kv_sep_for(&CollectionType::HashMap, Some(&map_delims)).as_deref(), Some(":"),);
        assert_eq!(kv_sep_for(&CollectionType::PathMap, Some(&map_delims)).as_deref(), Some(":"),);
        // No declared delimiters in scope (the inline-binder and lexer-terminal
        // sources) ⇒ the per-type default.
        assert_eq!(kv_sep_for(&CollectionType::HashMap, None).as_deref(), Some(":"),);
        assert_eq!(kv_sep_for(&CollectionType::PathMap, None).as_deref(), Some(":"),);
        assert_eq!(kv_sep_for(&CollectionType::Vec, None), None);
        // A user-overridden spelling still wins for a genuine kv container.
        let custom = mettail_ast::language::CollectionDelimiters {
            open: "map(".to_string(),
            close: ")".to_string(),
            sep: ",".to_string(),
            key_val_sep: Some("=>".to_string()),
        };
        assert_eq!(kv_sep_for(&CollectionType::HashMap, Some(&custom)).as_deref(), Some("=>"),);
        assert_eq!(kv_sep_for(&CollectionType::Vec, Some(&custom)), None);
    }

    fn empty_lang() -> mettail_ast::language::LanguageDef {
        mettail_ast::language::LanguageDef {
            name: Ident::new("Test", Span::call_site()),
            options: Default::default(),
            extends_names: Vec::new(),
            include_names: Vec::new(),
            mixin_names: Vec::new(),
            types: Vec::new(),
            refinement_types: Vec::new(),
            token_defs: Vec::new(),
            mode_defs: Vec::new(),
            sync_constraints: Vec::new(),
            tree_invariants: Vec::new(),
            terms: Vec::new(),
            equations: Vec::new(),
            rewrites: Vec::new(),
            logic: None,
            guard_config: None,
        }
    }

    #[test]
    fn classifies_hashbag_collection_rule() {
        // Mirror of Rholang's:
        //   PPar . ps:HashBag(Proc) |- "{" ps.*sep("|") "}" : Proc;
        let rule = GrammarRule {
            term_context: Some(vec![TermParam::Simple {
                name: Ident::new("ps", Span::call_site()),
                ty: TypeExpr::Collection {
                    coll_type: CollectionType::HashBag,
                    element: Box::new(TypeExpr::Base(Ident::new("Proc", Span::call_site()))),
                },
            }]),
            syntax_pattern: Some(vec![
                SyntaxExpr::Literal("{".into()),
                SyntaxExpr::Op(PatternOp::Sep {
                    collection: Ident::new("ps", Span::call_site()),
                    separator: "|".into(),
                    source: None,
                }),
                SyntaxExpr::Literal("}".into()),
            ]),
            ..rule_fixture(
                Ident::new("PPar", Span::call_site()),
                Ident::new("Proc", Span::call_site()),
            )
        };
        let lang = empty_lang();
        let shape = classify_collection(&rule, &lang).expect("collection");
        assert_eq!(shape.open_token, "{");
        assert!(!shape.has_synth_paren);
        assert_eq!(shape.close, "}");
        assert_eq!(shape.separator, "|");
        assert_eq!(shape.pair_separator, None);
        assert_eq!(shape.element_cat, "Proc");
        assert_eq!(shape.label, "PPar");
        assert!(matches!(shape.coll_kind, CollectionType::HashBag));
    }

    #[test]
    fn classifies_4element_split_open_pattern() {
        // Mirror of synthetic.rs's default split form:
        //   ListLit . ps:Vec(Proc) |- "list" "(" ps.*sep(",") ")" : List;
        let rule = GrammarRule {
            term_context: Some(vec![TermParam::Simple {
                name: Ident::new("ps", Span::call_site()),
                ty: TypeExpr::Collection {
                    coll_type: CollectionType::Vec,
                    element: Box::new(TypeExpr::Base(Ident::new("Proc", Span::call_site()))),
                },
            }]),
            syntax_pattern: Some(vec![
                SyntaxExpr::Literal("list".into()),
                SyntaxExpr::Literal("(".into()),
                SyntaxExpr::Op(PatternOp::Sep {
                    collection: Ident::new("ps", Span::call_site()),
                    separator: ",".into(),
                    source: None,
                }),
                SyntaxExpr::Literal(")".into()),
            ]),
            ..rule_fixture(
                Ident::new("ListLit", Span::call_site()),
                Ident::new("List", Span::call_site()),
            )
        };
        let lang = empty_lang();
        let shape = classify_collection(&rule, &lang).expect("4-element collection");
        assert_eq!(shape.open_token, "list");
        assert!(shape.has_synth_paren);
        assert_eq!(shape.close, ")");
        assert_eq!(shape.separator, ",");
        assert_eq!(shape.pair_separator, None);
        assert_eq!(shape.element_cat, "Proc");
        assert_eq!(shape.label, "ListLit");
        assert!(matches!(shape.coll_kind, CollectionType::Vec));
    }

    fn collection_baseline_rule(kind: CollectionType, split: bool) -> GrammarRule {
        let ident = |name| Ident::new(name, Span::call_site());
        let mut syntax = vec![SyntaxExpr::Literal("open".into())];
        if split {
            syntax.push(SyntaxExpr::Literal("(".into()));
        }
        syntax.push(SyntaxExpr::Op(PatternOp::Sep {
            collection: ident("items"),
            separator: ";;".into(),
            source: None,
        }));
        syntax.push(SyntaxExpr::Literal("close".into()));
        GrammarRule {
            term_context: Some(vec![TermParam::Simple {
                name: ident("items"),
                ty: TypeExpr::Collection {
                    coll_type: kind,
                    element: Box::new(TypeExpr::Base(ident("Element"))),
                },
            }]),
            syntax_pattern: Some(syntax),
            ..rule_fixture(ident("Constructor"), ident("Home"))
        }
    }

    #[test]
    fn collection_baseline_all_kinds_preserve_complete_descriptor() {
        for kind in [
            CollectionType::Vec,
            CollectionType::HashBag,
            CollectionType::HashSet,
            CollectionType::HashMap,
            CollectionType::PathMap,
        ] {
            for split in [false, true] {
                let rule = collection_baseline_rule(kind.clone(), split);
                let shape = owned_collection_reuse::assert_parity(&rule, &empty_lang())
                    .expect("original shape");
                assert_eq!(shape.open_token, "open");
                assert_eq!(shape.has_synth_paren, split);
                assert_eq!(shape.close, "close");
                assert_eq!(shape.separator, ";;");
                assert_eq!(shape.pair_separator, None);
                assert_eq!(shape.element_cat, "Element");
                assert_eq!(shape.coll_kind, kind);
                assert_eq!(shape.label, "Constructor");
            }
        }
    }

    #[test]
    fn collection_baseline_rejects_inexact_context_and_syntax() {
        let original = collection_baseline_rule(CollectionType::Vec, false);
        let mut cases = Vec::new();
        for context in [
            None,
            Some(Vec::new()),
            Some(vec![TermParam::GuardBody {
                name: Ident::new("guard", Span::call_site()),
            }]),
            Some(vec![TermParam::Simple {
                name: Ident::new("items", Span::call_site()),
                ty: TypeExpr::Base(Ident::new("Element", Span::call_site())),
            }]),
        ] {
            let mut rule = original.clone();
            rule.term_context = context;
            cases.push(rule);
        }
        let mut two_params = original.clone();
        let context = two_params.term_context.as_mut().expect("fixture context");
        context.push(context[0].clone());
        cases.push(two_params);
        let mut nested = original.clone();
        if let TermParam::Simple {
            ty: TypeExpr::Collection { element, .. }, ..
        } = &mut nested.term_context.as_mut().expect("fixture context")[0]
        {
            *element = Box::new(TypeExpr::Collection {
                coll_type: CollectionType::Vec,
                element: Box::new(TypeExpr::Base(Ident::new("Element", Span::call_site()))),
            });
        } else {
            panic!("fixture has a simple collection parameter");
        }
        cases.push(nested);
        for syntax in [None, Some(Vec::new())] {
            let mut rule = original.clone();
            rule.syntax_pattern = syntax;
            cases.push(rule);
        }
        for slot in 0..3 {
            let mut rule = original.clone();
            rule.syntax_pattern.as_mut().expect("fixture syntax")[slot] =
                SyntaxExpr::Param(Ident::new("items", Span::call_site()));
            cases.push(rule);
        }
        let mut extra = original.clone();
        extra
            .syntax_pattern
            .as_mut()
            .expect("fixture syntax")
            .extend([SyntaxExpr::Literal("extra".into()), SyntaxExpr::Literal("extra".into())]);
        cases.push(extra);
        let mut wrong_split = collection_baseline_rule(CollectionType::Vec, true);
        wrong_split.syntax_pattern.as_mut().expect("fixture syntax")[1] =
            SyntaxExpr::Literal("[".into());
        cases.push(wrong_split);
        for (name, source) in [
            ("different", None),
            (
                "items",
                Some(Box::new(PatternOp::Zip {
                    left: Ident::new("items", Span::call_site()),
                    right: Ident::new("items", Span::call_site()),
                })),
            ),
        ] {
            let mut rule = original.clone();
            rule.syntax_pattern.as_mut().expect("fixture syntax")[1] =
                SyntaxExpr::Op(PatternOp::Sep {
                    collection: Ident::new(name, Span::call_site()),
                    separator: ";;".into(),
                    source,
                });
            cases.push(rule);
        }
        for (index, rule) in cases.iter().enumerate() {
            assert!(
                owned_collection_reuse::assert_parity(rule, &empty_lang()).is_none(),
                "case {index}"
            );
        }
    }

    #[test]
    fn collection_baseline_empty_literal_spellings_are_retained() {
        let mut rule = collection_baseline_rule(CollectionType::Vec, false);
        rule.syntax_pattern = Some(vec![
            SyntaxExpr::Literal(String::new()),
            SyntaxExpr::Op(PatternOp::Sep {
                collection: Ident::new("items", Span::call_site()),
                separator: String::new(),
                source: None,
            }),
            SyntaxExpr::Literal(String::new()),
        ]);
        let shape = owned_collection_reuse::assert_parity(&rule, &empty_lang())
            .expect("empty literals allowed");
        assert_eq!(
            (shape.open_token, shape.close, shape.separator),
            (String::new(), String::new(), String::new())
        );
    }

    #[test]
    fn collection_baseline_pair_separator_uses_first_declared_result_category() {
        let mut language = empty_lang();
        let declaration = |kind| mettail_ast::language::LangType {
            name: Ident::new("Home", Span::call_site()),
            role: Default::default(),
            native_type: None,
            collection_kind: kind,
        };
        let custom = CollectionDelimiters {
            open: "[".into(),
            close: "]".into(),
            sep: ",".into(),
            key_val_sep: Some("=>".into()),
        };
        let vector = collection_baseline_rule(CollectionType::Vec, false);
        let map = collection_baseline_rule(CollectionType::HashMap, false);
        assert_eq!(
            owned_collection_reuse::assert_parity(&map, &language)
                .expect("map shape")
                .pair_separator,
            None
        );
        for kind in [CollectionCategory::Map(custom.clone()), CollectionCategory::Pathmap(custom)] {
            language.types = vec![declaration(Some(kind))];
            assert_eq!(
                owned_collection_reuse::assert_parity(&vector, &language)
                    .expect("vector shape")
                    .pair_separator
                    .as_deref(),
                Some("=>")
            );
            // A first matching noncollection declaration blocks later duplicates.
            language.types.insert(0, declaration(None));
            assert_eq!(
                owned_collection_reuse::assert_parity(&map, &language)
                    .expect("map shape")
                    .pair_separator,
                None
            );
        }
        let mut defaults = CollectionCategory::map_defaults();
        defaults.key_val_sep = None;
        language.types = vec![declaration(Some(CollectionCategory::Map(defaults)))];
        assert_eq!(
            owned_collection_reuse::assert_parity(&map, &language)
                .expect("map shape")
                .pair_separator
                .as_deref(),
            Some(":")
        );
        language.types =
            vec![declaration(Some(CollectionCategory::List(CollectionCategory::map_defaults())))];
        assert_eq!(
            owned_collection_reuse::assert_parity(&map, &language)
                .expect("map shape")
                .pair_separator,
            None
        );
    }

    fn optional_inner_collection_rule() -> GrammarRule {
        GrammarRule {
            term_context: Some(vec![
                TermParam::Simple {
                    name: Ident::new("a", Span::call_site()),
                    ty: TypeExpr::Base(Ident::new("Proc", Span::call_site())),
                },
                TermParam::Optional {
                    params: vec![TermParam::Simple {
                        name: Ident::new("qs", Span::call_site()),
                        ty: TypeExpr::Collection {
                            coll_type: CollectionType::Vec,
                            element: Box::new(TypeExpr::Base(Ident::new(
                                "Proc",
                                Span::call_site(),
                            ))),
                        },
                    }],
                },
            ]),
            syntax_pattern: Some(vec![
                SyntaxExpr::Literal("choose".into()),
                SyntaxExpr::Param(Ident::new("a", Span::call_site())),
                SyntaxExpr::Op(PatternOp::Opt {
                    inner: vec![
                        SyntaxExpr::Literal("with".into()),
                        SyntaxExpr::Literal("(".into()),
                        SyntaxExpr::Op(PatternOp::Sep {
                            collection: Ident::new("qs", Span::call_site()),
                            separator: "|".into(),
                            source: None,
                        }),
                        SyntaxExpr::Literal(")".into()),
                    ],
                }),
            ]),
            ..rule_fixture(
                Ident::new("ChooseMaybe", Span::call_site()),
                Ident::new("Proc", Span::call_site()),
            )
        }
    }

    #[test]
    fn binder_collection_infos_recurse_into_optional_groups() {
        let rule = optional_inner_collection_rule();
        let shape = classify_binder_in(&rule, &empty_lang()).expect("optional binder shape");
        let infos = binder_collection_infos(&shape);
        assert_eq!(infos.len(), 1);
        assert_eq!(infos[0].slot_idx, 0);
        assert_eq!(infos[0].elem_cat, "Proc");
        assert_eq!(infos[0].separator, "|");
        assert_eq!(infos[0].close, ")");
        assert!(has_binder_internal_collection_slot(&shape.positions));
    }

    #[test]
    fn optional_inner_collection_codegen_tables_include_slot() {
        let lang = empty_lang();
        let categories = vec!["Proc".to_string()];
        let per_cat = vec![vec![optional_inner_collection_rule()]];

        // Stage 2 consolidation: the slot is now carried by the single
        // collection_spec table; the shared loop worker reads that same table.
        let spec = emit_collection_spec_table(&lang, &categories, &per_cat).to_string();
        assert!(
            spec.contains("0u16 , 0u16 , 0u8") || spec.contains("0u16, 0u16, 0u8"),
            "optional inner collection slot missing from collection_spec table: {spec}"
        );
        let loop_body = emit_collection_loop_arm(&lang, &categories, &per_cat).to_string();
        assert_eq!(
            loop_body,
            quote! {
                mettail_prattail::wpda_transitions::collection_loop::collection_loop_step(
                    self.0, result_src_idx, rule_idx, _element_src_idx, _outer_bp,
                    _accumulator_id, slot_idx, kv_phase, _pos, tokens, lex_w,
                    |src_idx, kind| self.collection_element_can_start(src_idx, kind),
                )
            }
            .to_string(),
            "collection loop must forward the original engine, state, token and FIRST observations"
        );
    }

    #[test]
    fn structural_delimiter_collector_includes_grouping_collections_and_binder_closes() {
        let collection_rule = GrammarRule {
            term_context: Some(vec![TermParam::Simple {
                name: Ident::new("ps", Span::call_site()),
                ty: TypeExpr::Collection {
                    coll_type: CollectionType::HashBag,
                    element: Box::new(TypeExpr::Base(Ident::new("Proc", Span::call_site()))),
                },
            }]),
            syntax_pattern: Some(vec![
                SyntaxExpr::Literal("{".into()),
                SyntaxExpr::Op(PatternOp::Sep {
                    collection: Ident::new("ps", Span::call_site()),
                    separator: "|".into(),
                    source: None,
                }),
                SyntaxExpr::Literal("}".into()),
            ]),
            ..rule_fixture(
                Ident::new("PPar", Span::call_site()),
                Ident::new("Proc", Span::call_site()),
            )
        };
        let lang = empty_lang();
        let per_cat = vec![vec![collection_rule, optional_inner_collection_rule()]];

        let (opens, closes) = collect_structural_delimiters(&lang, &per_cat);

        assert!(opens.contains("("), "backend grouping open must be structural");
        assert!(opens.contains("{"), "collection open delimiter must be structural");
        assert!(closes.contains(")"), "grouping/binder close delimiter must be structural");
        assert!(closes.contains("}"), "collection close delimiter must be structural");
        assert!(
            !opens.contains("choose"),
            "binder keywords are trigger terminals, not delimiters"
        );
    }

    // Rholang's `PPar . ps:HashBag(Proc) |- "{" ps.*sep("|") "}" : Proc;`.
    fn ppar_brace_rule() -> GrammarRule {
        GrammarRule {
            term_context: Some(vec![TermParam::Simple {
                name: Ident::new("ps", Span::call_site()),
                ty: TypeExpr::Collection {
                    coll_type: CollectionType::HashBag,
                    element: Box::new(TypeExpr::Base(Ident::new("Proc", Span::call_site()))),
                },
            }]),
            syntax_pattern: Some(vec![
                SyntaxExpr::Literal("{".into()),
                SyntaxExpr::Op(PatternOp::Sep {
                    collection: Ident::new("ps", Span::call_site()),
                    separator: "|".into(),
                    source: None,
                }),
                SyntaxExpr::Literal("}".into()),
            ]),
            ..rule_fixture(
                Ident::new("PPar", Span::call_site()),
                Ident::new("Proc", Span::call_site()),
            )
        }
    }

    // Rholang's `CastMap . m:Map |- m : Proc;` — a cross-cat projection from the
    // Map collection category into Proc (classify_atomic ⇒ CrossCatProjection).
    fn cast_map_projection_rule() -> GrammarRule {
        GrammarRule {
            term_context: Some(vec![TermParam::Simple {
                name: Ident::new("m", Span::call_site()),
                ty: TypeExpr::Base(Ident::new("Map", Span::call_site())),
            }]),
            syntax_pattern: Some(vec![SyntaxExpr::Param(Ident::new("m", Span::call_site()))]),
            ..rule_fixture(
                Ident::new("CastMap", Span::call_site()),
                Ident::new("Proc", Span::call_site()),
            )
        }
    }

    // ROOT-A (2026-06-27): the `{`-prefix dispatch fork. When the braced
    // collection rule's open token collides with a cross-cat projection into a
    // collection-kind source sharing that open token, the prefix arm forks
    // (PPar marker + Map projection); otherwise it stays the byte-identical bare
    // ConsumeAndPush. FV: CollectionPrefixDispatchFork.v + TLA CollectionFork.
    #[test]
    fn collection_open_collision_emits_fork_else_bare_consume_and_push() {
        let ppar = ppar_brace_rule();
        let cast_map = cast_map_projection_rule();
        let mut lang = empty_lang();
        lang.types.push(mettail_ast::language::LangType {
            name: Ident::new("Proc", Span::call_site()),
            role: Default::default(),
            native_type: None,
            collection_kind: None,
        });
        // Map's open delimiter is `{` — the shared open token that collides.
        lang.types.push(mettail_ast::language::LangType {
            name: Ident::new("Map", Span::call_site()),
            role: Default::default(),
            native_type: None,
            collection_kind: Some(CollectionCategory::Map(
                mettail_ast::language::CollectionDelimiters {
                    open: "{".to_string(),
                    close: "}".to_string(),
                    sep: ",".to_string(),
                    key_val_sep: Some(":".to_string()),
                },
            )),
        });
        let categories = vec!["Proc".to_string(), "Map".to_string()];

        // ── Collision: per_cat[Proc] = [PPar, CastMap] ⇒ Fork. ──
        let per_cat_collision = vec![vec![ppar.clone(), cast_map.clone()], Vec::new()];
        let collision =
            emit_collection_prefix_arms(&lang, &categories, &per_cat_collision).to_string();
        assert!(
            collision.contains("WpdaStepAction :: Fork"),
            "collision must emit a Fork: {collision}"
        );
        assert!(
            collision.contains("collection_marker"),
            "branch0 must push the PPar collection marker: {collision}"
        );
        assert!(
            collision.contains("ForkActionKind :: ConsumeAndPush"),
            "branch0 marker must be a ConsumeAndPush fork branch (Discard trigger): {collision}"
        );
        assert!(
            collision.contains("TriggerMode :: Discard"),
            "branch0 marker must discard the open trigger token: {collision}"
        );
        assert!(
            collision.contains("ForkActionKind :: PushProjectionInline"),
            "branch1 projection must be a PushProjectionInline fork branch \
             (unified Fix A: singleton uncached push, not the cohort path): {collision}"
        );
        assert!(
            collision.contains("CrossCatDelegate"),
            "branch1 must delegate to the Map source via CrossCatDelegate: {collision}"
        );
        assert!(
            collision.contains("BP_TIER_CROSSCAT_PROJECTION"),
            "branch1 must carry the cross-cat-projection weight tier: {collision}"
        );
        // CastMap is rule index 1 within per_cat[Proc]; Map is category index 1.
        assert!(
            collision.contains("source_src_idx : 1u16"),
            "projection must delegate to source Map (src_idx 1): {collision}"
        );
        assert!(
            collision.contains("consume_trigger : false"),
            "the Fork must not pre-consume the trigger: {collision}"
        );

        // ── No collision: per_cat[Proc] = [PPar] only ⇒ bare ConsumeAndPush. ──
        let per_cat_fast = vec![vec![ppar.clone()], Vec::new()];
        let fast = emit_collection_prefix_arms(&lang, &categories, &per_cat_fast).to_string();
        assert!(
            fast.contains("WpdaStepAction :: ConsumeAndPush"),
            "no-collision fast path must be a bare ConsumeAndPush: {fast}"
        );
        assert!(
            !fast.contains("Fork"),
            "no-collision fast path must NOT Fork (byte-identical to pre-ROOT-A): {fast}"
        );
    }

    fn generated_spec(close: &str) -> GeneratedCollectionSpec {
        GeneratedCollectionSpec {
            open: String::new(),
            has_synth_paren: false,
            close: close.to_string(),
            sep: ",".to_string(),
            min_elements: 0,
            kv_sep: None,
            kv_value_optional: false,
            element_src_idx: Some(3),
            close_resumes_via_unwinding: true,
        }
    }

    #[test]
    fn collection_spec_table_coalesces_identical_duplicate_keys() {
        let mut arms = Vec::new();
        let mut indices = BTreeMap::new();
        let key = (2, 7, 1);
        insert_collection_spec_arm(
            &mut arms,
            &mut indices,
            key,
            generated_spec(")"),
            "first".to_string(),
        )
        .expect("first insertion is fresh");
        insert_collection_spec_arm(
            &mut arms,
            &mut indices,
            key,
            generated_spec(")"),
            "duplicate".to_string(),
        )
        .expect("an identical duplicate is idempotent");

        assert_eq!(arms.len(), 1, "one key emits exactly one Rust match arm");
        assert_eq!(indices.get(&key), Some(&0));
    }

    #[test]
    fn collection_spec_table_rejects_conflicting_duplicate_keys() {
        let mut arms = Vec::new();
        let mut indices = BTreeMap::new();
        let key = (2, 7, 1);
        insert_collection_spec_arm(
            &mut arms,
            &mut indices,
            key,
            generated_spec(")"),
            "first origin".to_string(),
        )
        .expect("first insertion is fresh");
        let error = insert_collection_spec_arm(
            &mut arms,
            &mut indices,
            key,
            generated_spec("}"),
            "second origin".to_string(),
        )
        .expect_err("the same key cannot select a different parser specification");

        assert!(error.contains("(2, 7, 1)"));
        assert!(error.contains("first origin"));
        assert!(error.contains("second origin"));
        assert_eq!(arms.len(), 1, "a conflict never mutates the admitted table");
    }
}
