//! Phase A.5: Collection rule classification + dispatch.
//!
//! Detects judgement-style rules that parse a collection literal, e.g.,
//! RhoCalc's `PPar . ps:HashBag(Proc) |- "{" ps.*sep("|") "}" : Proc;`
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
use std::collections::BTreeSet;

use super::binder::{classify_binder_in, BinderPosition, BinderShape, CollectionSepInfo};

/// Classification of a collection-literal rule.
#[derive(Debug, Clone)]
pub struct CollectionShape {
    /// First-token slice of the open delimiter — what the lexer emits as a
    /// single `Fixed` token. When `has_synth_paren` is true, the full logical
    /// open delimiter is this token followed by a separate `"("` token.
    pub open_token: String,
    /// True when the synthetic-rule emitter (`synthetic.rs`) split a default
    /// open delimiter like `"list("` into the 4-element pattern
    /// `[Literal("list"), Literal("("), Op(Sep), Literal(close)]`. The
    /// engine consumes two tokens in sequence (open keyword, then `(`) before
    /// pushing the CollectionMarker.
    pub has_synth_paren: bool,
    /// Close delimiter.
    pub close: String,
    /// Separator between elements (e.g., `"|"` for HashBag, `","` for Map between pairs).
    pub separator: String,
    /// Pair separator for Map (`":"` between key and value). `None` for List/Bag/Set.
    pub pair_separator: Option<String>,
    /// Category name of each element (e.g., `"Proc"`).
    pub element_cat: String,
    /// Container kind (Vec, HashBag, HashSet, HashMap).
    pub coll_kind: CollectionType,
    /// Constructor label (e.g., `"PPar"`).
    pub label: String,
}

fn collect_binder_collection_infos<'a>(
    positions: &'a [BinderPosition],
    out: &mut Vec<&'a CollectionSepInfo>,
) {
    for position in positions {
        match position {
            BinderPosition::ParamParse { collection: Some(info), .. } => out.push(info),
            BinderPosition::OptionalGroup { positions: inner, .. } => {
                collect_binder_collection_infos(inner, out);
            },
            _ => {},
        }
    }
}

fn binder_collection_infos(shape: &BinderShape) -> Vec<&CollectionSepInfo> {
    let mut infos = Vec::new();
    collect_binder_collection_infos(&shape.positions, &mut infos);
    infos
}

fn collect_binder_close_delimiters(positions: &[BinderPosition], closes: &mut BTreeSet<String>) {
    for position in positions {
        match position {
            BinderPosition::BinderListLoop { close, inner_positions, .. } => {
                if !close.is_empty() {
                    closes.insert(close.clone());
                }
                collect_binder_close_delimiters(inner_positions, closes);
            },
            BinderPosition::ParamParse { collection: Some(info), .. } => {
                if !info.close.is_empty() {
                    closes.insert(info.close.clone());
                }
            },
            BinderPosition::OptionalGroup { positions: inner, .. } => {
                collect_binder_close_delimiters(inner, closes);
            },
            _ => {},
        }
    }
}

pub(crate) fn collect_structural_delimiters(
    language: &LanguageDef,
    per_cat: &[Vec<GrammarRule>],
) -> (BTreeSet<String>, BTreeSet<String>) {
    let mut opens = BTreeSet::new();
    let mut closes = BTreeSet::new();

    // Grouping is emitted by the backend for every parseable category.
    opens.insert("(".to_string());
    closes.insert(")".to_string());

    for rules in per_cat {
        for rule in rules {
            if let Some(shape) = classify_collection(rule, language) {
                opens.insert(shape.open_token);
                if shape.has_synth_paren {
                    opens.insert("(".to_string());
                }
                closes.insert(shape.close);
                continue;
            }
            if let Some(shape) = classify_binder_in(rule, language) {
                collect_binder_close_delimiters(&shape.positions, &mut closes);
            }
        }
    }

    (opens, closes)
}

fn has_binder_internal_collection_slot(positions: &[BinderPosition]) -> bool {
    positions.iter().any(|position| match position {
        BinderPosition::ParamParse { collection: Some(_), .. } => true,
        BinderPosition::BinderListLoop { collection_param_cat: Some(_), .. } => true,
        BinderPosition::OptionalGroup { positions: inner, .. } => {
            has_binder_internal_collection_slot(inner)
        },
        _ => false,
    })
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
/// Resolution: an explicitly **declared** `key_val_sep` (from a
/// [`CollectionDelimiters`] on an `as Map`/`as Pathmap` category) wins; otherwise
/// the per-type default applies — `":"` for the kv-bearing container types
/// (`HashMap`, `PathMap`), `None` for the sequence/set types (`Vec`, `HashBag`,
/// `HashSet`).
///
/// Byte-identity (existing corpus): the inline-binder and lexer sources have no
/// declared delimiters in scope and pass `declared = None`, reducing to
/// `type_default(coll_type)` — exactly the former
/// `match coll_kind { HashMap | PathMap => Some(":"), _ => None }` hardcode. The
/// declared-category source always carries `Some(d)` whose `key_val_sep` is
/// `Some(":")` for the shipped `Map`/`Pathmap` categories, so the declared value
/// wins and equals the former `d.key_val_sep.clone()`.
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
    declared
        .and_then(|d| d.key_val_sep.clone())
        .or_else(|| match coll_type {
            CollectionType::HashMap | CollectionType::PathMap => Some(":".to_string()),
            _ => None,
        })
}

/// Try to classify a `GrammarRule` as a collection-literal rule.
///
/// Accepts both 3- and 4-element syntax patterns:
/// - 3-element: `[Literal(open), Op(Sep), Literal(close)]` — explicit single-token
///   open delimiter (e.g., RhoCalc's `"{" ... "}"`).
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
    let tc = rule.term_context.as_ref()?;
    let sp = rule.syntax_pattern.as_ref()?;
    // Expect exactly 1 Simple param of Collection type.
    if tc.len() != 1 {
        return None;
    }
    let (param_name, coll_type, element_ident) = match &tc[0] {
        TermParam::Simple {
            name,
            ty: TypeExpr::Collection { coll_type, element },
        } => match element.as_ref() {
            TypeExpr::Base(elem) => (name, coll_type.clone(), elem.to_string()),
            _ => return None,
        },
        _ => return None,
    };
    // Accept 3-element [Literal, Op(Sep), Literal] or 4-element
    // [Literal, Literal("("), Op(Sep), Literal] form.
    let (open_token, has_synth_paren, sep_idx, close_idx) = match sp.len() {
        3 => {
            let open_kw = match &sp[0] {
                SyntaxExpr::Literal(s) => s.clone(),
                _ => return None,
            };
            (open_kw, false, 1usize, 2usize)
        },
        4 => {
            let open_kw = match &sp[0] {
                SyntaxExpr::Literal(s) => s.clone(),
                _ => return None,
            };
            // Second element must be the literal `(` synthesized by synthetic.rs
            // (which splits default open delimiters of the form `kw(`).
            match &sp[1] {
                SyntaxExpr::Literal(s) if s == "(" => {},
                _ => return None,
            }
            (open_kw, true, 2usize, 3usize)
        },
        _ => return None,
    };
    let close = match &sp[close_idx] {
        SyntaxExpr::Literal(s) => s.clone(),
        _ => return None,
    };
    let separator = match &sp[sep_idx] {
        SyntaxExpr::Op(PatternOp::Sep { collection, separator, source: None })
            if collection == param_name =>
        {
            separator.clone()
        },
        _ => return None,
    };
    // Look up the pair_separator from the LangType's collection_kind for Maps.
    // For List/Bag/Set this is None; for Map it's the user's `key_val_sep`
    // (default `":"` per `language.rs::map_defaults`).
    //
    // Stage 3 (2026-06-27): routed through the single `kv_sep_for` resolver
    // (`coll_type` from the declared category, `declared = Some(d)`) — byte-
    // identical to the former per-variant `match`: Map/Pathmap carry a declared
    // `key_val_sep` (so the declared value wins) while List/Bag/Set carry
    // `key_val_sep = None` AND a non-kv `coll_type` (so type_default is also
    // `None`).
    let pair_separator = language
        .types
        .iter()
        .find(|t| t.name == rule.category)
        .and_then(|t| t.collection_kind.as_ref())
        .and_then(|c| kv_sep_for(&c.coll_type(), Some(c.delimiters())));
    Some(CollectionShape {
        open_token,
        has_synth_paren,
        close,
        separator,
        pair_separator,
        element_cat: element_ident,
        coll_kind: coll_type,
        label: rule.label.to_string(),
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
/// The defect this guards: at RhoCalc's `Proc` entry the open `{` is a single
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
/// For self-collections (RhoCalc PPar: HashBag(Proc) in Proc), this routes
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
                            weight: lex_w(
                                0.0, #result_src_idx, #rule_idx,
                            ),
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
                                    #result_src_idx, #proj_rule,
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
                                    weight: lex_w(
                                        0.0, #result_src_idx, #rule_idx,
                                    ),
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
        {
            // Stage 2: the single per-slot CollectionSpec (was the inline
            // (close, sep, kv_sep, is_binder_internal) lookup match).
            let lookup = self.collection_spec(*result_src_idx, *rule_idx, *slot_idx);
            let token_text = tokens.peek_text(_pos).unwrap_or("");
            match lookup {
                Some(__spec) => {
                    // Project the fields the kv_phase dispatch below reads.
                    // `is_binder_internal` is the former loop-arm selector
                    // (`close_resumes_via_unwinding`).
                    let close = __spec.close;
                    let sep = __spec.sep;
                    let kv_sep = __spec.kv_sep;
                    // Pathmap optional-value (2026-06-27): `true` ⇒ a bare path
                    // `{| k |}` (no `: v`) is finalized as `k → k` rather than
                    // erroring on the missing `kv_sep` (read in the kv_phase==1
                    // arm). `false` for HashMap and every non-kv container.
                    let kv_value_optional = __spec.kv_value_optional;
                    let is_binder_internal = __spec.close_resumes_via_unwinding;
                    // Phase 4 #5b (2026-05-12): three-phase dispatch
                    // keyed on kv_phase. For Vec/HashBag/HashSet
                    // (kv_sep == None), only phase 0 ever runs (the
                    // walker's parity-driven patch keeps kv_phase=0).
                    let _ = (close, sep, kv_sep);
                    let element_src_idx = *_element_src_idx;
                    match *kv_phase {
                        0u8 => {
                            // #307 ROOT-F G1-G4 (2026-06-11; FV:
                            // CollectionForkEvidence.v, 13 thms zero-admission;
                            // design red-team CONVERGED round 2): the
                            // post-element fork emits ONLY evidence-licensed
                            // branches. The Stage-3.16 unconditional three-way
                            // fork over-generated: BRANCH-1 consumed ANY token
                            // as a pseudo-close ({0|1} finalized {0} after
                            // eating `|` — pseudo_close_overgenerates) and
                            // BRANCH-3 split elements separator-free
                            // ({c d} parsed; {c!(p)} shredded into c, p —
                            // bare_element_overgenerates). The realize layer
                            // cannot refute the junk (min_terminal_span = 0
                            // for collections + zero-width symbol span), so
                            // the fix is at GENERATION: gated_run_iff_loop_lang
                            // proves the gated machine accepts EXACTLY the
                            // collection continuation language (no-loss).
                            //
                            // G1 close: membership over the COMPLETE out-edge
                            //   set (peek_text primary + peek_alternatives,
                            //   deduped — the ROOT-A __mixfix_literal_targets
                            //   discipline); one branch per matching edge,
                            //   each a ConsumeAtAndPop carrying the MATCHED
                            //   edge's target (R2-1: the post-close position
                            //   feeds the splice/re-host reads inside
                            //   apply_pop_body_to_cursor; alt-0 advance is the
                            //   alt0_close_lands_on_wrong_target defect).
                            // G2 sep: the consume branch is emitted iff a sep
                            //   edge is PRESENT (membership detection). The
                            //   consume itself resolves the PRIMARY edge
                            //   (R2-2 constraint: safe while detection stays a
                            //   presence test and shipped seps are primary-
                            //   resolved — longest-match orders multi-char
                            //   delimiters first; if sep detection ever forks
                            //   per matched edge, the consume needs next_pos
                            //   carriage like G1).
                            // G3 bare-element: licensed ONLY for separator-free
                            //   (whitespace-joined) collection grammars —
                            //   sep.is_empty() is a per-slot compile-time
                            //   constant from the lookup (the ENTRY separator;
                            //   Map kv_sep never governs this fork).
                            // G4 advance-or-recover: zero licensed normal
                            //   branches means the collection continuation
                            //   cannot consume the live token. For explicit
                            //   close-delimited slots, synthesize a bounded
                            //   recovery close insertion and pop the marker
                            //   through the same finalize path as a real
                            //   close. Empty-close grammars still error:
                            //   there is no concrete token to insert.
                            let mut __branches: Vec<
                                mettail_prattail::wpda_walker::ForkBranch<_>,
                            > = Vec::with_capacity(3);
                            // G1: close branches by edge membership.
                            if token_text == close {
                                if let Some(np) = tokens.next_pos(_pos, 0) {
                                    __branches.push(
                                        mettail_prattail::wpda_walker::ForkBranch {
                                            symbol: StackSymbolV2::category_entry(0),
                                            weight: lex_w(
                                                0.0, *result_src_idx, *rule_idx,
                                            ),
                                            // str-cast collection-infix fix (2026-06-18):
                                            // resume the enclosing Pratt InfixLoop at the
                                            // dispatch bp (CollectionLoop.outer_bp, carried
                                            // from the marker's coll_dispatch_bp) so a
                                            // finalized collection can attach a following
                                            // infix operator with l_bp > outer_bp — exactly
                                            // mirroring the atomic Return-pop path. When no
                                            // higher-bp operator follows (close/sep/lower-bp
                                            // op next), InfixLoop falls through to Unwinding
                                            // (engine_impl CollectionMarker reroute) — no-loss.
                                            // Binder-internal collections (is_binder_internal)
                                            // are NOT Pratt primaries: they resume the binder
                                            // rule continuation via Unwinding (their pre-fix
                                            // behavior), so a following token is never wrongly
                                            // consumed as an infix on the collection.
                                            new_state: if is_binder_internal {
                                                WpdaState::Unwinding
                                            } else {
                                                WpdaState::InfixLoop { cur_bp: *_outer_bp }
                                            },
                                            action_kind:
                                                mettail_prattail::wpda_walker::ForkActionKind::ConsumeAtAndPop {
                                                    next_pos: np,
                                                },
                                        },
                                    );
                                }
                            }
                            for (__i, __alt) in
                                tokens.peek_alternatives(_pos).iter().enumerate()
                            {
                                if __alt.text == close {
                                    if let Some(np) = tokens.next_pos(_pos, __i + 1) {
                                        let __dup = __branches.iter().any(|b| {
                                            matches!(
                                                b.action_kind,
                                                mettail_prattail::wpda_walker::ForkActionKind::ConsumeAtAndPop {
                                                    next_pos,
                                                } if next_pos == np
                                            )
                                        });
                                        if !__dup {
                                            __branches.push(
                                                mettail_prattail::wpda_walker::ForkBranch {
                                                    symbol: StackSymbolV2::category_entry(0),
                                                    weight: lex_w(
                                                        0.0, *result_src_idx, *rule_idx,
                                                    ),
                                                    // str-cast collection-infix fix
                                                    // (2026-06-18): same as the primary close
                                                    // branch — resume InfixLoop at the dispatch
                                                    // bp; no-loss fall-through to Unwinding.
                                                    // Binder-internal collections stay Unwinding.
                                                    new_state: if is_binder_internal {
                                                        WpdaState::Unwinding
                                                    } else {
                                                        WpdaState::InfixLoop { cur_bp: *_outer_bp }
                                                    },
                                                    action_kind:
                                                        mettail_prattail::wpda_walker::ForkActionKind::ConsumeAtAndPop {
                                                            next_pos: np,
                                                        },
                                                },
                                            );
                                        }
                                    }
                                }
                            }
                            // G2: sep branch, presence-gated.
                            let __sep_present = !sep.is_empty()
                                && (token_text == sep
                                    || tokens
                                        .peek_alternatives(_pos)
                                        .iter()
                                        .any(|a| a.text == sep));
                            if __sep_present {
                                __branches.push(
                                    mettail_prattail::wpda_walker::ForkBranch {
                                        symbol: StackSymbolV2::category_entry(0),
                                        weight: lex_w(
                                            0.0, *result_src_idx, *rule_idx,
                                        ),
                                        new_state: WpdaState::PrefixDispatch {
                                            pos: tokens.next_pos(_pos, 0).unwrap_or(_pos + 1),
                                            cur_bp: 0,
                                        },
                                        // #307 ROOT-F coverage backstop: the
                                        // dedicated separator-consume kind
                                        // increments the child's per-slot sep
                                        // count (the fire-time accounting
                                        // witness).
                                        action_kind:
                                            mettail_prattail::wpda_walker::ForkActionKind::ConsumeCollectionSep,
                                    },
                                );
                            }
                            // G3: bare-element, separator-free grammars only.
                            if sep.is_empty() {
                                __branches.push(
                                    mettail_prattail::wpda_walker::ForkBranch {
                                        // GEN-1 goal-gate G2 (2026-06-28): strict
                                        // GOAL = the element's category so a
                                        // cross-cat element cannot over-extend
                                        // past its category into a cross-cat-out
                                        // operator that cannot reach the goal.
                                        symbol: StackSymbolV2::category_entry_goal(
                                            element_src_idx,
                                        ),
                                        weight: lex_w(
                                            mettail_prattail::automata::lex_weight::EPSILON_OPT_SKIP,
                                            *result_src_idx, *rule_idx,
                                        ),
                                        new_state: WpdaState::PrefixDispatch {
                                            pos: _pos,
                                            cur_bp: 0,
                                        },
                                        action_kind:
                                            mettail_prattail::wpda_walker::ForkActionKind::Push,
                                    },
                                );
                            }
                            // G4: advance-or-recover.
                            if __branches.is_empty() {
                                if close.is_empty() {
                                    // F2 (§4.5 no-close repetition, 2026-06-28):
                                    // a `*sep` rep with an EMPTY close (e.g.
                                    // ForRowNoWhere `b "&" bs.*sep("&")`) has no
                                    // explicit terminator literal. A token that is
                                    // neither the separator (G2 would have fired)
                                    // nor a close (none exists) TERMINATES the rep:
                                    // finalize the accumulated Vec by popping the
                                    // CollectionMarker WITHOUT consuming the token
                                    // (it belongs to the enclosing context — the
                                    // for-`)`, a `where`/`;`, or the body `{`).
                                    // `WpdaStepAction::Pop` fires the marker's
                                    // finalize via `apply_pop_body_to_cursor`
                                    // (keyed on the popped CollectionMarker symbol)
                                    // exactly like the G1 explicit-close
                                    // `ConsumeAtAndPop`, minus the consume; the
                                    // popped-into parent mixfix marker resumes its
                                    // post-rep handling → FireAction. The rule's
                                    // own slice fork (GEN1_MAX_SLICE uncapped) keeps
                                    // a `where`-closed sibling (e.g. ForRowWhere)
                                    // alive in parallel; lex-min selects the
                                    // no-recovery finalize for the no-`where` input.
                                    // count ≥ min holds by construction: the rep
                                    // entry's PrefixDispatch parses ≥ 1 element
                                    // before this loop runs and MixfixRep.min = 0.
                                    WpdaStepAction::Pop {
                                        weight: lex_w(0.0, *result_src_idx, *rule_idx),
                                        new_state: if is_binder_internal {
                                            WpdaState::Unwinding
                                        } else {
                                            WpdaState::InfixLoop { cur_bp: *_outer_bp }
                                        },
                                    }
                                } else {
                                    WpdaStepAction::Fork {
                                        branches: vec![
                                            mettail_prattail::wpda_walker::ForkBranch {
                                                symbol: StackSymbolV2::category_entry(0),
                                                weight: lex_w(
                                                    mettail_prattail::recovery::costs::INSERT.value(),
                                                    *result_src_idx,
                                                    *rule_idx,
                                                ),
                                                new_state: if is_binder_internal {
                                                    WpdaState::Unwinding
                                                } else {
                                                    WpdaState::InfixLoop { cur_bp: *_outer_bp }
                                                },
                                                action_kind:
                                                    mettail_prattail::wpda_walker::ForkActionKind::PopWithEffect {
                                                        effect:
                                                            mettail_prattail::wpda_walker::BuilderDelta::InsertToken {
                                                                pos: _pos,
                                                                kind: mettail_prattail::automata::TokenKind::Fixed(close.to_string()),
                                                                text: close.to_string(),
                                                            },
                                                    },
                                            },
                                        ],
                                        consume_trigger: false,
                                    }
                                }
                            } else {
                                WpdaStepAction::Fork {
                                    branches: __branches,
                                    // Each branch's action_kind encodes its own
                                    // consume semantics (or no-consume for Push).
                                    consume_trigger: false,
                                }
                            }
                        }
                        1u8 => {
                            // Phase 4 #5b (2026-05-12): just parsed a key.
                            // Consume the key/value separator `:` (or
                            // user-overridden equivalent). On mismatch,
                            // error — the cursor's collection_stack parity
                            // is odd, so we MUST consume `:` to proceed.
                            //
                            // Pathmap optional-value (2026-06-27): for a
                            // value-optional kv-collection (Pathmap), a key
                            // followed DIRECTLY by the close or an entry
                            // separator (not the `kv_sep`) is a bare path
                            // `{| k |}` ≡ `{| k : k |}`. Duplicate the key as
                            // its own value (DuplicateLastCollectionElement)
                            // and re-dispatch as kv_phase=0 WITHOUT consuming:
                            // the arena is now even so the walker's parity
                            // patch lands kv_phase=0, and the phase-0 dispatch
                            // resolves the close (finalize) or separator (next
                            // key) exactly as a value-ful entry would. HashMap
                            // (kv_value_optional=false) keeps the strict
                            // error — its values are mandatory.
                            match kv_sep {
                                Some(expected_kv_sep) => {
                                    // Membership-detect the close / entry
                                    // separator across the COMPLETE lattice
                                    // edge set (primary peek + alternatives),
                                    // mirroring the phase-0 G1 close discipline
                                    // — the Pathmap close `|}` is lattice-
                                    // ambiguous with the `|` operator.
                                    let __bare_path = kv_value_optional
                                        && token_text != expected_kv_sep
                                        && (token_text == close
                                            || token_text == sep
                                            || tokens
                                                .peek_alternatives(_pos)
                                                .iter()
                                                .any(|a| a.text == close || a.text == sep));
                                    if token_text == expected_kv_sep {
                                        WpdaStepAction::Consume {
                                            weight: lex_w(
                                                0.0, *result_src_idx, *rule_idx,
                                            ),
                                            // Transition to kv_phase=2 to
                                            // Push the value's CategoryEntry
                                            // on the next step. We use
                                            // explicit `2u8` here (not 0):
                                            // the walker's parity-patch
                                            // only overrides kv_phase==0,
                                            // so this `2` survives.
                                            new_state: WpdaState::CollectionLoop {
                                                result_src_idx: *result_src_idx,
                                                rule_idx: *rule_idx,
                                                element_src_idx: *_element_src_idx,
                                                outer_bp: *_outer_bp,
                                                accumulator_id: *_accumulator_id,
                                                slot_idx: *slot_idx,
                                                kv_phase: 2u8,
                                            },
                                        }
                                    } else if __bare_path {
                                        // Bare path: duplicate the just-parsed
                                        // key as its value (keeps the arena
                                        // even-length), then re-enter the loop
                                        // at kv_phase=0 with the SAME position
                                        // (non-consuming) so phase-0 handles the
                                        // close / separator uniformly.
                                        WpdaStepAction::AdvanceWithEffect {
                                            effect:
                                                mettail_prattail::wpda_walker::BuilderDelta::DuplicateLastCollectionElement {
                                                    id: *slot_idx,
                                                },
                                            new_state: WpdaState::CollectionLoop {
                                                result_src_idx: *result_src_idx,
                                                rule_idx: *rule_idx,
                                                element_src_idx: *_element_src_idx,
                                                outer_bp: *_outer_bp,
                                                accumulator_id: *_accumulator_id,
                                                slot_idx: *slot_idx,
                                                kv_phase: 0u8,
                                            },
                                        }
                                    } else {
                                        WpdaStepAction::Error(format!(
                                            "expected key/value separator `{}` after \
                                             HashMap key at pos {}, found {:?}",
                                            expected_kv_sep, _pos, token_text,
                                        ))
                                    }
                                }
                                None => {
                                    // Defensive: kv_phase=1 reached but
                                    // slot has no kv_sep — invariant
                                    // violation (parity-patch should not
                                    // have set kv_phase=1 for non-HashMap).
                                    WpdaStepAction::Error(format!(
                                        "kv_phase=1 reached at (src={}, rule={}, slot={}) \
                                         but slot has no key/value separator — invariant \
                                         violation",
                                        *result_src_idx, *rule_idx, *slot_idx,
                                    ))
                                }
                            }
                        }
                        2u8 => {
                            // Phase 4 #5b (2026-05-12): just consumed `:`.
                            // Push CategoryEntry(element_src) onto GSS
                            // and dispatch value parse via PrefixDispatch.
                            // When the value returns, splice happens in
                            // apply_pop_body_to_cursor; the next state
                            // (CollectionLoop with engine-emitted kv_phase=0)
                            // gets parity-patched to phase 0 since the
                            // slot's len is now even.
                            WpdaStepAction::Push {
                                // GEN-1 goal-gate G2 (2026-06-28): strict GOAL =
                                // the kv-collection value element's category.
                                symbol: StackSymbolV2::category_entry_goal(element_src_idx),
                                weight: lex_w(
                                    0.0, *result_src_idx, *rule_idx,
                                ),
                                new_state: WpdaState::PrefixDispatch {
                                    pos: _pos,
                                    cur_bp: 0,
                                },
                            }
                        }
                        other => WpdaStepAction::Error(format!(
                            "invalid kv_phase {} at (src={}, rule={}, slot={})",
                            other, *result_src_idx, *rule_idx, *slot_idx,
                        )),
                    }
                }
                None => WpdaStepAction::Idle,
            }
        }
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
    let mut arms = Vec::new();
    for (cat_i, rules) in per_cat.iter().enumerate() {
        for (rule_i, rule) in rules.iter().enumerate() {
            let result_src_idx = cat_i as u16;
            let rule_idx = rule_i as u16;
            // GEN-1 B-3 (Stage S3): mixfix `*sep` repetition slots. Each maps to a
            // per-slot CollectionSpec keyed (result_src, rule_idx, part_idx) that
            // the CollectionLoop reads. `close_resumes_via_unwinding: true` (like a
            // Class-2 binder-internal slot) so the close pops via Unwinding back to
            // the enclosing mixfix marker — the FireAction-suppression then leaves
            // the CollectionId in the marker's args for the rule action to drain.
            // The close is the SINGLE terminator literal following the `*sep` (")",
            // "<-", "<="); open-ended reps (empty close — ForRow only, gated out)
            // would carry "". Disjoint from collection-literal / binder keys.
            for (slot_idx, elem_cat, sep, close) in mixfix_rep_slots(rule) {
                let close_str = close.first().cloned().unwrap_or_default();
                let element_src_expr = match lookup_element_src_idx(&elem_cat, categories) {
                    Some(i) => quote! { Some(#i) },
                    None => quote! { None },
                };
                arms.push(quote! {
                    (#result_src_idx, #rule_idx, #slot_idx) => Some(
                        mettail_prattail::wpda_runtime::CollectionSpec {
                            open: "",
                            has_synth_paren: false,
                            close: #close_str,
                            sep: #sep,
                            kv_sep: None,
                            kv_value_optional: false,
                            element_src_idx: #element_src_expr,
                            close_resumes_via_unwinding: true,
                        }
                    ),
                });
            }
            let Some(shape) = classify_collection(rule, language) else {
                // Class-2/3 binder-internal collection slots: one arm per slot
                // keyed on the 3-tuple (src, rule, slot_idx). The close resumes
                // via Unwinding (close_resumes_via_unwinding = true).
                if let Some(bshape) = classify_binder_in(rule, language) {
                    for info in binder_collection_infos(&bshape) {
                        let close = &info.close;
                        let sep = &info.separator;
                        let slot_idx = info.slot_idx;
                        let kv_sep_expr = match &info.key_val_separator {
                            Some(k) => quote! { Some(#k) },
                            None => quote! { None },
                        };
                        let element_src_expr =
                            match lookup_element_src_idx(&info.elem_cat, categories) {
                                Some(i) => quote! { Some(#i) },
                                None => quote! { None },
                            };
                        arms.push(quote! {
                            (#result_src_idx, #rule_idx, #slot_idx) => Some(
                                mettail_prattail::wpda_runtime::CollectionSpec {
                                    open: "",
                                    has_synth_paren: false,
                                    close: #close,
                                    sep: #sep,
                                    kv_sep: #kv_sep_expr,
                                    // Binder-internal collection slots are never
                                    // PathMap (`ast/src/types.rs` admits only
                                    // Vec/HashBag/HashSet/HashMap inline, and
                                    // `binder.rs` rejects PathMap), so the value
                                    // is never optional here.
                                    kv_value_optional: false,
                                    element_src_idx: #element_src_expr,
                                    close_resumes_via_unwinding: true,
                                }
                            ),
                        });
                    }
                }
                continue;
            };
            // Class-5 collection literal rule: single slot at slot_idx=0. The
            // close resumes the enclosing InfixLoop
            // (close_resumes_via_unwinding = false).
            let open = &shape.open_token;
            let has_synth_paren = shape.has_synth_paren;
            let close = &shape.close;
            let sep = &shape.separator;
            let kv_sep_expr = match &shape.pair_separator {
                Some(k) => quote! { Some(#k) },
                None => quote! { None },
            };
            let element_src_expr = match lookup_element_src_idx(&shape.element_cat, categories) {
                Some(i) => quote! { Some(#i) },
                None => quote! { None },
            };
            // Pathmap optional-value (2026-06-27): a Pathmap set-form literal
            // `{| k |}` ≡ `{| k : k |}` (value = key). ONLY PathMap admits an
            // optional per-entry value; HashMap values stay mandatory. Scoped
            // to the declared collection type, NOT a blanket kv change.
            let kv_value_optional = matches!(shape.coll_kind, CollectionType::PathMap);
            arms.push(quote! {
                (#result_src_idx, #rule_idx, 0u8) => Some(
                    mettail_prattail::wpda_runtime::CollectionSpec {
                        open: #open,
                        has_synth_paren: #has_synth_paren,
                        close: #close,
                        sep: #sep,
                        kv_sep: #kv_sep_expr,
                        kv_value_optional: #kv_value_optional,
                        element_src_idx: #element_src_expr,
                        close_resumes_via_unwinding: false,
                    }
                ),
            });
        }
    }
    if arms.is_empty() {
        return quote! {
            {
                let _ = (result_src_idx, rule_idx, slot_idx);
                None
            }
        };
    }
    quote! {
        match (result_src_idx, rule_idx, slot_idx) {
            #(#arms)*
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
    for rules in per_cat {
        for rule in rules {
            if classify_collection(rule, language).is_some() {
                return true;
            }
            if let Some(shape) = classify_binder_in(rule, language) {
                if !binder_collection_infos(&shape).is_empty() {
                    return true;
                }
            }
            // GEN-1 B-3 (Stage S3): a mixfix `*sep` repetition slot also drives the
            // CollectionLoop, so a language with ONLY rep slots (no literals /
            // binder collections) still needs the loop arm emitted.
            if !mixfix_rep_slots(rule).is_empty() {
                return true;
            }
        }
    }
    false
}

fn lookup_element_src_idx(element_cat: &str, categories: &[String]) -> Option<u16> {
    categories
        .iter()
        .position(|c| c == element_cat)
        .map(|i| i as u16)
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
fn mixfix_rep_slots(rule: &GrammarRule) -> Vec<(u8, String, String, Vec<String>)> {
    let Some(info) = super::infix::classify_rule_public(rule) else {
        return Vec::new();
    };
    info.mixfix_parts
        .iter()
        .enumerate()
        .filter_map(|(i, part)| {
            part.repetition.as_ref().map(|rep| {
                (
                    i as u8,
                    part.operand_category.clone(),
                    rep.separator.clone(),
                    rep.close.clone(),
                )
            })
        })
        .collect()
}

/// Trigger-ownership soundness (2026-07-02): emit a per-rule lookup that
/// returns true when `(result_src_idx, rule_idx)` identifies a rule whose
/// surface syntax pattern BEGINS with a structural literal trigger (its first
/// `SyntaxExpr` is a `Literal`, e.g. `@ p` NQuoteShort, `int ( a )` casts, `-
/// a` Neg). Consumed by the walker's `emit_fire_action` walk-back drain to gate
/// the `pos_match` fallback that claims a leading `TriggerTerminal` at the
/// firing rule's frame-start position.
///
/// ROOT (trace-pinned, rhocalc `@Nil!!(x,y)` name/proc display roundtrip): a
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
            // Prior to this extension, Class 3 rules (rhocalc PInputs)
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
    use mettail_ast::grammar::GrammarRule;
    use mettail_ast::language::CollectionCategory;
    use mettail_ast::types::CollectionType;
    use proc_macro2::Span;
    use syn::Ident;

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
        // Mirror of RhoCalc's:
        //   PPar . ps:HashBag(Proc) |- "{" ps.*sep("|") "}" : Proc;
        let rule = GrammarRule {
            label: Ident::new("PPar", Span::call_site()),
            category: Ident::new("Proc", Span::call_site()),
            items: Vec::new(),
            bindings: Vec::new(),
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
            rust_code: None,
            eval_mode: None,
            is_right_assoc: false,
            prefix_bp: None,
            tier_directive: None,
            is_auto_injected: false,
            doc_comment: None,
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
            label: Ident::new("ListLit", Span::call_site()),
            category: Ident::new("List", Span::call_site()),
            items: Vec::new(),
            bindings: Vec::new(),
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
            rust_code: None,
            eval_mode: None,
            is_right_assoc: false,
            prefix_bp: None,
            tier_directive: None,
            is_auto_injected: false,
            doc_comment: None,
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

    fn optional_inner_collection_rule() -> GrammarRule {
        GrammarRule {
            label: Ident::new("ChooseMaybe", Span::call_site()),
            category: Ident::new("Proc", Span::call_site()),
            items: Vec::new(),
            bindings: Vec::new(),
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
            rust_code: None,
            eval_mode: None,
            is_right_assoc: false,
            prefix_bp: None,
            tier_directive: None,
            is_auto_injected: false,
            doc_comment: None,
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
        // collection_spec table; the loop arm reads it via `collection_spec`.
        let spec = emit_collection_spec_table(&lang, &categories, &per_cat).to_string();
        assert!(
            spec.contains("0u16 , 0u16 , 0u8") || spec.contains("0u16, 0u16, 0u8"),
            "optional inner collection slot missing from collection_spec table: {spec}"
        );
        let loop_body = emit_collection_loop_arm(&lang, &categories, &per_cat).to_string();
        assert!(
            loop_body.contains("collection_spec"),
            "collection loop arm must read the consolidated collection_spec: {loop_body}"
        );
    }

    #[test]
    fn structural_delimiter_collector_includes_grouping_collections_and_binder_closes() {
        let collection_rule = GrammarRule {
            label: Ident::new("PPar", Span::call_site()),
            category: Ident::new("Proc", Span::call_site()),
            items: Vec::new(),
            bindings: Vec::new(),
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
            rust_code: None,
            eval_mode: None,
            is_right_assoc: false,
            prefix_bp: None,
            tier_directive: None,
            is_auto_injected: false,
            doc_comment: None,
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

    // RhoCalc's `PPar . ps:HashBag(Proc) |- "{" ps.*sep("|") "}" : Proc;`.
    fn ppar_brace_rule() -> GrammarRule {
        GrammarRule {
            label: Ident::new("PPar", Span::call_site()),
            category: Ident::new("Proc", Span::call_site()),
            items: Vec::new(),
            bindings: Vec::new(),
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
            rust_code: None,
            eval_mode: None,
            is_right_assoc: false,
            prefix_bp: None,
            tier_directive: None,
            is_auto_injected: false,
            doc_comment: None,
        }
    }

    // RhoCalc's `CastMap . m:Map |- m : Proc;` — a cross-cat projection from the
    // Map collection category into Proc (classify_atomic ⇒ CrossCatProjection).
    fn cast_map_projection_rule() -> GrammarRule {
        GrammarRule {
            label: Ident::new("CastMap", Span::call_site()),
            category: Ident::new("Proc", Span::call_site()),
            items: Vec::new(),
            bindings: Vec::new(),
            term_context: Some(vec![TermParam::Simple {
                name: Ident::new("m", Span::call_site()),
                ty: TypeExpr::Base(Ident::new("Map", Span::call_site())),
            }]),
            syntax_pattern: Some(vec![SyntaxExpr::Param(Ident::new("m", Span::call_site()))]),
            rust_code: None,
            eval_mode: None,
            is_right_assoc: false,
            prefix_bp: None,
            tier_directive: None,
            is_auto_injected: false,
            doc_comment: None,
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
            native_type: None,
            collection_kind: None,
        });
        // Map's open delimiter is `{` — the shared open token that collides.
        lang.types.push(mettail_ast::language::LangType {
            name: Ident::new("Map", Span::call_site()),
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
}
