//! Phase A.5: Collection rule classification + dispatch.
//!
//! Detects judgement-style rules that parse a collection literal, e.g.,
//! RhoCalc's `PPar . ps:HashBag(Proc) |- "{" ps.*sep("|") "}" : Proc;`
//!
//! The parsed shape:
//! - `term_context = [Simple { name: ps, ty: Collection { coll_type: HashBag, element: Proc } }]`
//! - `syntax_pattern = [Literal("{"), Op(Sep { collection: ps, separator: "|", ... }), Literal("}")]`
//!
//! Classification yields `CollectionShape { open, close, separator,
//! element_cat, coll_kind, label }`. Engine integration emits a
//! collection-loop state machine: open → element-loop → close →
//! arity-1 action that pushes the constructed collection.

use mettail_ast::grammar::{GrammarRule, PatternOp, SyntaxExpr, TermParam};
use mettail_ast::language::{CollectionCategory, LanguageDef};
use mettail_ast::types::{CollectionType, TypeExpr};
use proc_macro2::TokenStream;
use quote::quote;

use super::binder::{classify_binder, BinderPosition};

/// Classification of a collection-literal rule.
#[derive(Debug, Clone)]
pub struct CollectionShape {
    /// Open delimiter as a single string (e.g., `"{"` for HashBag, `"list("` for default Vec).
    /// When `has_synth_paren` is true, this is the concatenation of `open_token + "("`.
    pub open: String,
    /// First-token slice of the open delimiter — what the lexer emits as a
    /// single `Fixed` token. Equal to `open` when `has_synth_paren` is false;
    /// when true, equal to `open_token == open.trim_end_matches('(')`.
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
    /// Result category (where the collection lives, e.g., `"Proc"`).
    pub result_cat: String,
    /// Constructor label (e.g., `"PPar"`).
    pub label: String,
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
///   pushing the marker via `WpdsState::CollectionOpenParen`.
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
        }
        4 => {
            let open_kw = match &sp[0] {
                SyntaxExpr::Literal(s) => s.clone(),
                _ => return None,
            };
            // Second element must be the literal `(` synthesized by synthetic.rs
            // (which splits default open delimiters of the form `kw(`).
            match &sp[1] {
                SyntaxExpr::Literal(s) if s == "(" => {}
                _ => return None,
            }
            (open_kw, true, 2usize, 3usize)
        }
        _ => return None,
    };
    let close = match &sp[close_idx] {
        SyntaxExpr::Literal(s) => s.clone(),
        _ => return None,
    };
    let separator = match &sp[sep_idx] {
        SyntaxExpr::Op(PatternOp::Sep {
            collection,
            separator,
            source: None,
        }) if collection == param_name => separator.clone(),
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
    let open = if has_synth_paren {
        format!("{}(", open_token)
    } else {
        open_token.clone()
    };
    Some(CollectionShape {
        open,
        open_token,
        has_synth_paren,
        close,
        separator,
        pair_separator,
        element_cat: element_ident,
        coll_kind: coll_type,
        result_cat: rule.category.to_string(),
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
            // `WpdsState::CollectionOpenParen` BEFORE entering the
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
                    WpdsState::CollectionOpenParen {
                        result_src_idx: #result_src_idx,
                        rule_idx: #rule_idx,
                        element_src_idx: #element_src,
                        outer_bp: *cur_bp,
                    }
                }
            } else {
                quote! {
                    WpdsState::PrefixDispatch {
                        pos: *pos + 1,
                        cur_bp: 0,
                    }
                }
            };
            arms.push(quote! {
                Some(mettail_prattail::automata::TokenKind::Fixed(__open))
                    if __open == #open_token && state_cat_src_idx == #result_src_idx => {
                    return WpdsStepAction::ConsumeAndPush {
                        symbol: StackSymbolV2::collection_marker(
                            #result_src_idx, #rule_idx, 0,
                        ),
                        weight: LexicographicWeight::from_cost(
                            0.0, #result_src_idx, #rule_idx,
                        ),
                        new_state: #new_state,
                        capture_token: false,
                    };
                }
            });
        }
    }
    quote! { #(#arms)* }
}

/// Phase 4: emit the body of `WpdsState::CollectionLoop`. Looks up the
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
                    for position in shape.positions.iter() {
                        if let BinderPosition::ParamParse {
                            collection: Some(info),
                            ..
                        } = position {
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
        return quote! { WpdsStepAction::Idle };
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
                            // Stage 3.16 / Hack #11 (Cluster 1, Mechanism γ,
                            // 2026-05-05): three-branch Fork over close / sep /
                            // bare-element. Lex-min over the three branches'
                            // weights picks the surviving cursor:
                            //   - close branch: from_cost(0.0, ...) — wins when
                            //     token_text == close.
                            //   - sep branch: from_cost(0.0, ...) — wins when
                            //     token_text == sep (different token from close
                            //     ⇒ mutually exclusive; on G1-style ambiguous
                            //     close==sep, source-order picks close first).
                            //   - bare-element branch: from_cost(SKIP_BIAS, ...)
                            //     — wins when token_text matches neither close
                            //     nor sep (G3 future-grammar support: `[a b c]`
                            //     whitespace-separated lists). Penalized so close
                            //     and sep branches win when their tokens match.
                            //
                            // Branches whose runtime guard fails downstream (e.g.
                            // close branch when token_text != close means the
                            // following Unwinding step will diverge from a clean
                            // close-context) drop via cursor_resolution_check at
                            // commit_winner time.
                            WpdsStepAction::Fork {
                                branches: vec![
                                    // BRANCH 1: close — ConsumeAndPop into Unwinding.
                                    mettail_prattail::wpds_walker::ForkBranch {
                                        symbol: StackSymbolV2::category_entry(0),
                                        weight: LexicographicWeight::from_cost(
                                            0.0, *result_src_idx, *rule_idx,
                                        ),
                                        new_state: WpdsState::Unwinding,
                                        action_kind:
                                            mettail_prattail::wpds_walker::ForkActionKind::ConsumeAndPop,
                                    },
                                    // BRANCH 2: sep — Consume token, return to
                                    // PrefixDispatch for next element.
                                    mettail_prattail::wpds_walker::ForkBranch {
                                        symbol: StackSymbolV2::category_entry(0),
                                        weight: LexicographicWeight::from_cost(
                                            0.0, *result_src_idx, *rule_idx,
                                        ),
                                        new_state: WpdsState::PrefixDispatch {
                                            pos: _pos + 1,
                                            cur_bp: 0,
                                        },
                                        action_kind:
                                            mettail_prattail::wpds_walker::ForkActionKind::Consume,
                                    },
                                    // BRANCH 3: bare-element (G3 support) —
                                    // Push CategoryEntry(element_src) onto GSS,
                                    // dispatch element parse without consuming
                                    // a separator first.
                                    mettail_prattail::wpds_walker::ForkBranch {
                                        symbol: StackSymbolV2::category_entry(
                                            element_src_idx,
                                        ),
                                        weight: LexicographicWeight::from_cost(
                                            mettail_prattail::automata::lex_weight::EPSILON_OPT_SKIP,
                                            *result_src_idx, *rule_idx,
                                        ),
                                        new_state: WpdsState::PrefixDispatch {
                                            pos: _pos,
                                            cur_bp: 0,
                                        },
                                        action_kind:
                                            mettail_prattail::wpds_walker::ForkActionKind::Push,
                                    },
                                ],
                                // Each branch's action_kind encodes its own
                                // consume semantics (or no-consume for Push).
                                consume_trigger: false,
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
                                        WpdsStepAction::Consume {
                                            weight: LexicographicWeight::from_cost(
                                                0.0, *result_src_idx, *rule_idx,
                                            ),
                                            // Transition to kv_phase=2 to
                                            // Push the value's CategoryEntry
                                            // on the next step. We use
                                            // explicit `2u8` here (not 0):
                                            // the walker's parity-patch
                                            // only overrides kv_phase==0,
                                            // so this `2` survives.
                                            new_state: WpdsState::CollectionLoop {
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
                                        WpdsStepAction::Error(format!(
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
                                    WpdsStepAction::Error(format!(
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
                            WpdsStepAction::Push {
                                symbol: StackSymbolV2::category_entry(element_src_idx),
                                weight: LexicographicWeight::from_cost(
                                    0.0, *result_src_idx, *rule_idx,
                                ),
                                new_state: WpdsState::PrefixDispatch {
                                    pos: _pos,
                                    cur_bp: 0,
                                },
                            }
                        }
                        other => WpdsStepAction::Error(format!(
                            "invalid kv_phase {} at (src={}, rule={}, slot={})",
                            other, *result_src_idx, *rule_idx, *slot_idx,
                        )),
                    }
                }
                None => WpdsStepAction::Idle,
            }
        }
    }
}

/// Phase 4: emit a per-language lookup that maps `(result_src_idx, rule_idx)`
/// of a `CollectionMarker` symbol to its `element_src_idx`. Used by the
/// `WpdsState::Unwinding` arm when transitioning from CollectionMarker top
/// to `WpdsState::CollectionLoop`.
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
                    for position in shape.positions.iter() {
                        if let BinderPosition::ParamParse {
                            collection: Some(info),
                            ..
                        } = position {
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
/// to the close-delimiter literal. Used by `WpdsState::PrefixDispatch`'s
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
                    for position in shape.positions.iter() {
                        if let BinderPosition::ParamParse {
                            collection: Some(info),
                            ..
                        } = position {
                            let result_src_idx = cat_i as u16;
                            let rule_idx = rule_i as u16;
                            let close = &info.close;
                            let slot_idx = info.slot_idx;
                            arms.push(quote! {
                                (#result_src_idx, #rule_idx, #slot_idx) => Some(#close),
                            });
                        }
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
/// delimiter and the separator. Used by `WpdsState::InfixLoop` (in
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
                    for position in shape.positions.iter() {
                        if let BinderPosition::ParamParse {
                            collection: Some(info),
                            ..
                        } = position {
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
/// `WpdsStepEngine::kv_separator_for_collection`. Returns the per-
/// (result_src_idx, rule_idx, slot_idx) lookup that yields
/// `Some(":")` (or user-overridden literal) for HashMap collection
/// slots and `None` for Vec/HashBag/HashSet slots or unknown tuples.
///
/// Used by the walker's `set_cursor_inner_state` to detect HashMap
/// slots and patch `WpdsState::CollectionLoop.kv_phase` based on
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
                    for position in shape.positions.iter() {
                        if let BinderPosition::ParamParse {
                            collection: Some(info),
                            ..
                        } = position {
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
            let has_collection_slot = shape.positions.iter().any(|p| {
                matches!(
                    p,
                    BinderPosition::ParamParse {
                        collection: Some(_),
                        ..
                    }
                    | BinderPosition::BinderListLoop {
                        collection_param_cat: Some(_),
                        ..
                    }
                )
            });
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
        assert_eq!(shape.open, "{");
        assert_eq!(shape.open_token, "{");
        assert!(!shape.has_synth_paren);
        assert_eq!(shape.close, "}");
        assert_eq!(shape.separator, "|");
        assert_eq!(shape.pair_separator, None);
        assert_eq!(shape.element_cat, "Proc");
        assert_eq!(shape.label, "PPar");
        assert_eq!(shape.result_cat, "Proc");
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
        assert_eq!(shape.open, "list(");
        assert_eq!(shape.open_token, "list");
        assert!(shape.has_synth_paren);
        assert_eq!(shape.close, ")");
        assert_eq!(shape.separator, ",");
        assert_eq!(shape.pair_separator, None);
        assert_eq!(shape.element_cat, "Proc");
        assert_eq!(shape.label, "ListLit");
        assert!(matches!(shape.coll_kind, CollectionType::Vec));
    }
}
