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
use mettail_ast::language::{CollectionCategory, LanguageDef};
use mettail_ast::types::{CollectionType, TypeExpr};
use proc_macro2::TokenStream;
use quote::quote;
use std::collections::BTreeSet;

use super::binder::{classify_binder, BinderPosition, BinderShape, CollectionSepInfo};

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
            if let Some(shape) = classify_binder(rule) {
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
    let pair_separator = language
        .types
        .iter()
        .find(|t| t.name == rule.category)
        .and_then(|t| t.collection_kind.as_ref())
        .and_then(|c| match c {
            CollectionCategory::Map(d) => d.key_val_sep.clone(),
            _ => None,
        });
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

/// Phase 4: emit prefix-dispatch arms that recognize the open delimiter
/// of each collection-shaped rule. On match, the arm pushes a
/// `CollectionMarker` symbol carrying `(result_src_idx, rule_idx,
/// accumulator_id)`. The walker overrides the symbol's `bp` field with
/// a freshly-allocated accumulator id from `SemanticBuilder::start_collection`,
/// and pushes an `ActionArg::CollectionId` arg that the finalize action
/// will consume.
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
            arms.push(quote! {
                Some(mettail_prattail::automata::TokenKind::Fixed(__open))
                    if __open == #open_token && state_cat_src_idx == #result_src_idx => {
                    return WpdaStepAction::ConsumeAndPush {
                        symbol: StackSymbolV2::collection_marker(
                            #result_src_idx, #rule_idx, 0,
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
    // Per-rule lookup arms: (result_src_idx, rule_idx, slot_idx) →
    // (close, sep, kv_sep). Phase 4 #1.B (2026-05-11): 3-tuple keying
    // so multi-slot rules can disambiguate sibling slots within the
    // same rule. Phase 4 #5b (2026-05-12): widened the value tuple
    // to also carry the optional kv_sep (`":"` for HashMap, None
    // otherwise) so the kv_phase dispatch can match on it directly.
    let mut lookup_arms = Vec::new();
    for (cat_i, rules) in per_cat.iter().enumerate() {
        for (rule_i, rule) in rules.iter().enumerate() {
            let Some(shape) = classify_collection(rule, language) else {
                // B9 / Class 2 (2026-05-08): iterate ALL Class-2 binder
                // rule SimpleCollection slots; emit per-slot arm.
                if let Some(shape) = classify_binder(rule) {
                    for info in binder_collection_infos(&shape) {
                        let result_src_idx = cat_i as u16;
                        let rule_idx = rule_i as u16;
                        let close = &info.close;
                        let sep = &info.separator;
                        let slot_idx = info.slot_idx;
                        let kv_sep_expr = match &info.key_val_separator {
                            Some(k) => quote! { Some(#k) },
                            None => quote! { None },
                        };
                        lookup_arms.push(quote! {
                            (#result_src_idx, #rule_idx, #slot_idx) => Some((#close, #sep, #kv_sep_expr)),
                        });
                    }
                }
                continue;
            };
            // Class-5 collection rules: single slot at slot_idx=0.
            let result_src_idx = cat_i as u16;
            let rule_idx = rule_i as u16;
            let close = &shape.close;
            let sep = &shape.separator;
            // Phase 4 #5b (2026-05-12): Class-5 collection rules expose
            // their pair_separator (populated from
            // `LangType.collection_kind = Some(Map(...))`). For
            // List/Bag/Set this is None.
            let kv_sep_expr = match &shape.pair_separator {
                Some(k) => quote! { Some(#k) },
                None => quote! { None },
            };
            lookup_arms.push(quote! {
                (#result_src_idx, #rule_idx, 0u8) => Some((#close, #sep, #kv_sep_expr)),
            });
        }
    }
    if lookup_arms.is_empty() {
        return quote! { WpdaStepAction::Idle };
    }
    quote! {
        {
            // Lookup (close, sep, kv_sep) for this marker's rule + slot.
            let lookup: Option<(&'static str, &'static str, Option<&'static str>)> = match (*result_src_idx, *rule_idx, *slot_idx) {
                #(#lookup_arms)*
                _ => None,
            };
            let token_text = tokens.peek_text(_pos).unwrap_or("");
            match lookup {
                Some((close, sep, kv_sep)) => {
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
                            // G4 advance-or-die: zero licensed branches ⇒
                            //   WpdaStepAction::Error (no_branch_no_word +
                            //   advance_or_die_emits_error: an empty Fork
                            //   would silently delete the cursor).
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
                                            new_state: WpdaState::Unwinding,
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
                                                    new_state: WpdaState::Unwinding,
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
                                        symbol: StackSymbolV2::category_entry(
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
                            // G4: advance-or-die.
                            if __branches.is_empty() {
                                WpdaStepAction::Error(format!(
                                    "collection continuation mismatch at pos {}:                                      expected close {:?} or separator {:?}                                      (rule {}:{}) — no lattice edge matches",
                                    _pos, close, sep, result_src_idx, rule_idx,
                                ))
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
                            match kv_sep {
                                Some(expected_kv_sep) => {
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
                                symbol: StackSymbolV2::category_entry(element_src_idx),
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

/// Phase 4: emit a per-language lookup that maps `(result_src_idx, rule_idx)`
/// of a `CollectionMarker` symbol to its `element_src_idx`. Used by the
/// `WpdaState::Unwinding` arm when transitioning from CollectionMarker top
/// to `WpdaState::CollectionLoop`.
pub(crate) fn emit_collection_element_src_lookup(
    language: &mettail_ast::language::LanguageDef,
    categories: &[String],
    per_cat: &[Vec<GrammarRule>],
) -> TokenStream {
    let mut arms = Vec::new();
    for (cat_i, rules) in per_cat.iter().enumerate() {
        for (rule_i, rule) in rules.iter().enumerate() {
            let Some(shape) = classify_collection(rule, language) else {
                // Phase 4 #1.B (2026-05-11): iterate ALL collection
                // slots; emit one arm per slot keyed on 3-tuple
                // (src, rule, slot_idx). The element_src may differ
                // between sibling slots (e.g., one slot of Vec(Proc)
                // and another of Vec(Name)).
                if let Some(shape) = classify_binder(rule) {
                    for info in binder_collection_infos(&shape) {
                        if let Some(element_src_idx) =
                            lookup_element_src_idx(&info.elem_cat, categories)
                        {
                            let result_src_idx = cat_i as u16;
                            let rule_idx = rule_i as u16;
                            let slot_idx = info.slot_idx;
                            arms.push(quote! {
                                (#result_src_idx, #rule_idx, #slot_idx) => Some(#element_src_idx),
                            });
                        }
                    }
                }
                continue;
            };
            let Some(element_src_idx) = lookup_element_src_idx(&shape.element_cat, categories)
            else {
                continue;
            };
            let result_src_idx = cat_i as u16;
            let rule_idx = rule_i as u16;
            arms.push(quote! {
                (#result_src_idx, #rule_idx, 0u8) => Some(#element_src_idx),
            });
        }
    }
    if arms.is_empty() {
        return quote! { None::<u16> };
    }
    quote! {
        match (result_src_idx, rule_idx, slot_idx) {
            #(#arms)*
            _ => None,
        }
    }
}

/// Phase 4: emit a per-language lookup that maps `(result_src_idx, rule_idx)`
/// to the close-delimiter literal. Used by `WpdaState::PrefixDispatch`'s
/// empty-collection bootstrap: when frontier_top is a `CollectionMarker`
/// and the next token equals the close delim, the empty-collection path
/// fires `ConsumeAndPop` instead of falling through to element dispatch.
pub(crate) fn emit_collection_close_lookup(
    language: &mettail_ast::language::LanguageDef,
    per_cat: &[Vec<GrammarRule>],
) -> TokenStream {
    let mut arms = Vec::new();
    for (cat_i, rules) in per_cat.iter().enumerate() {
        for (rule_i, rule) in rules.iter().enumerate() {
            let Some(shape) = classify_collection(rule, language) else {
                // B9 / Class 2 (2026-05-08): also register Class-2 binder
                // rules' collection slot close delim. Used by the empty-
                // collection bootstrap path in PrefixDispatch.
                //
                // Phase 4 #1.B (2026-05-11): iterate ALL collection slots
                // (not just `find`) and emit one arm per slot keyed on
                // 3-tuple `(src, rule, slot_idx)`. The walker passes
                // `slot_idx` from `node.symbol.bp` at lookup time. In
                // the supported subset (no outer collection nesting),
                // accumulator_id == slot_idx, so the codegen-stamped
                // value matches the walker's post-overwrite `bp`.
                if let Some(shape) = classify_binder(rule) {
                    for info in binder_collection_infos(&shape) {
                        let result_src_idx = cat_i as u16;
                        let rule_idx = rule_i as u16;
                        let close = &info.close;
                        let slot_idx = info.slot_idx;
                        arms.push(quote! {
                            (#result_src_idx, #rule_idx, #slot_idx) => Some(#close),
                        });
                    }
                }
                continue;
            };
            // Class-5 collection rules have a single slot at slot_idx=0.
            let result_src_idx = cat_i as u16;
            let rule_idx = rule_i as u16;
            let close = &shape.close;
            arms.push(quote! {
                (#result_src_idx, #rule_idx, 0u8) => Some(#close),
            });
        }
    }
    if arms.is_empty() {
        return quote! { None::<&'static str> };
    }
    quote! {
        match (result_src_idx, rule_idx, slot_idx) {
            #(#arms)*
            _ => None,
        }
    }
}

/// Plan B (F5 close/sep filter, 2026-05-11): per-language lookup that maps
/// `(result_src_idx, rule_idx)` of a CollectionMarker to BOTH the close
/// delimiter and the separator. Used by `WpdaState::InfixLoop` (in
/// `engine_impl.rs`) to skip infix dispatch when frontier_top is
/// CollectionMarker AND the next token is the collection's close or
/// separator — avoiding spurious Fork branches that diverge on
/// collection_stack depth.
///
/// Evaluates to `Option<(&'static str, &'static str)>` — `(close, sep)`.
pub(crate) fn emit_collection_close_sep_lookup(
    language: &mettail_ast::language::LanguageDef,
    per_cat: &[Vec<GrammarRule>],
) -> TokenStream {
    let mut arms = Vec::new();
    for (cat_i, rules) in per_cat.iter().enumerate() {
        for (rule_i, rule) in rules.iter().enumerate() {
            let Some(shape) = classify_collection(rule, language) else {
                // Phase 4 #1.B (2026-05-11): iterate ALL collection
                // slots; emit one arm per slot keyed on 3-tuple
                // (src, rule, slot_idx). Mirrors
                // emit_collection_close_lookup's slot extension.
                if let Some(shape) = classify_binder(rule) {
                    for info in binder_collection_infos(&shape) {
                        let result_src_idx = cat_i as u16;
                        let rule_idx = rule_i as u16;
                        let close = &info.close;
                        let sep = &info.separator;
                        let slot_idx = info.slot_idx;
                        arms.push(quote! {
                            (#result_src_idx, #rule_idx, #slot_idx) => Some((#close, #sep)),
                        });
                    }
                }
                continue;
            };
            let result_src_idx = cat_i as u16;
            let rule_idx = rule_i as u16;
            let close = &shape.close;
            let sep = &shape.separator;
            arms.push(quote! {
                (#result_src_idx, #rule_idx, 0u8) => Some((#close, #sep)),
            });
        }
    }
    if arms.is_empty() {
        return quote! { None::<(&'static str, &'static str)> };
    }
    quote! {
        match (result_src_idx, rule_idx, slot_idx) {
            #(#arms)*
            _ => None,
        }
    }
}

fn lookup_element_src_idx(element_cat: &str, categories: &[String]) -> Option<u16> {
    categories
        .iter()
        .position(|c| c == element_cat)
        .map(|i| i as u16)
}

/// Phase 4 #5b (2026-05-12): emit the body of
/// `WpdaEngine::kv_separator_for_collection`. Returns the per-
/// (result_src_idx, rule_idx, slot_idx) lookup that yields
/// `Some(":")` (or user-overridden literal) for HashMap collection
/// slots and `None` for Vec/HashBag/HashSet slots or unknown tuples.
///
/// Used by the walker's `set_cursor_inner_state` to detect HashMap
/// slots and patch `WpdaState::CollectionLoop.kv_phase` based on
/// `cursor.collection_stack[acc_id].len()` parity.
pub(crate) fn emit_kv_separator_for_collection(
    language: &mettail_ast::language::LanguageDef,
    per_cat: &[Vec<GrammarRule>],
) -> TokenStream {
    let mut arms = Vec::new();
    for (cat_i, rules) in per_cat.iter().enumerate() {
        for (rule_i, rule) in rules.iter().enumerate() {
            let Some(shape) = classify_collection(rule, language) else {
                // Class-2 binder rule SimpleCollection slots: emit one
                // arm per slot keyed on (src, rule, slot_idx) when the
                // slot's coll_kind is HashMap. The arm yields the
                // hardcoded `":"` separator (per binder.rs::605-625's
                // Phase 4 #5 pilot wiring).
                if let Some(shape) = classify_binder(rule) {
                    for info in binder_collection_infos(&shape) {
                        if let Some(kv) = &info.key_val_separator {
                            let result_src_idx = cat_i as u16;
                            let rule_idx = rule_i as u16;
                            let slot_idx = info.slot_idx;
                            arms.push(quote! {
                                (#result_src_idx, #rule_idx, #slot_idx) => Some(#kv),
                            });
                        }
                    }
                }
                continue;
            };
            // Class-5 collection rules: single slot at slot_idx=0. Emit
            // an arm iff this rule is a Map (has pair_separator).
            if let Some(kv) = &shape.pair_separator {
                let result_src_idx = cat_i as u16;
                let rule_idx = rule_i as u16;
                arms.push(quote! {
                    (#result_src_idx, #rule_idx, 0u8) => Some(#kv),
                });
            }
        }
    }
    if arms.is_empty() {
        return quote! { None::<&'static str> };
    }
    quote! {
        match (result_src_idx, rule_idx, slot_idx) {
            #(#arms)*
            _ => None,
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
    per_cat: &[Vec<GrammarRule>],
) -> TokenStream {
    let mut arms = Vec::new();
    for (cat_i, rules) in per_cat.iter().enumerate() {
        for (rule_i, rule) in rules.iter().enumerate() {
            let Some(shape) = classify_binder(rule) else {
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
        let shape = classify_binder(&rule).expect("optional binder shape");
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

        let close = emit_collection_close_lookup(&lang, &per_cat).to_string();
        let close_sep = emit_collection_close_sep_lookup(&lang, &per_cat).to_string();
        let element = emit_collection_element_src_lookup(&lang, &categories, &per_cat).to_string();
        let loop_body = emit_collection_loop_arm(&lang, &categories, &per_cat).to_string();

        for emitted in [close, close_sep, element, loop_body] {
            assert!(
                emitted.contains("0u16 , 0u16 , 0u8") || emitted.contains("0u16, 0u16, 0u8"),
                "optional inner collection slot missing from emitted lookup: {emitted}"
            );
        }
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
}
