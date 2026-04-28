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
pub(crate) fn emit_collection_loop_arm(
    language: &mettail_ast::language::LanguageDef,
    _categories: &[String],
    per_cat: &[Vec<GrammarRule>],
) -> TokenStream {
    // Per-rule lookup arms: (result_src_idx, rule_idx) → (close, sep).
    let mut lookup_arms = Vec::new();
    for (cat_i, rules) in per_cat.iter().enumerate() {
        for (rule_i, rule) in rules.iter().enumerate() {
            let Some(shape) = classify_collection(rule, language) else {
                continue;
            };
            let result_src_idx = cat_i as u16;
            let rule_idx = rule_i as u16;
            let close = &shape.close;
            let sep = &shape.separator;
            lookup_arms.push(quote! {
                (#result_src_idx, #rule_idx) => Some((#close, #sep)),
            });
        }
    }
    if lookup_arms.is_empty() {
        return quote! { WpdsStepAction::Idle };
    }
    quote! {
        {
            // Lookup (close, sep) for this marker's rule.
            let lookup: Option<(&'static str, &'static str)> = match (*result_src_idx, *rule_idx) {
                #(#lookup_arms)*
                _ => None,
            };
            let token_text = tokens.peek_text(_pos).unwrap_or("");
            match lookup {
                Some((close, sep)) if token_text == close => {
                    let _ = sep;
                    WpdsStepAction::ConsumeAndPop {
                        weight: LexicographicWeight::from_cost(
                            0.0, *result_src_idx, *rule_idx,
                        ),
                        new_state: WpdsState::Unwinding,
                    }
                }
                Some((_close, sep)) if token_text == sep => {
                    WpdsStepAction::Consume {
                        weight: LexicographicWeight::one(),
                        new_state: WpdsState::PrefixDispatch {
                            pos: _pos + 1,
                            cur_bp: 0,
                        },
                    }
                }
                Some((close, sep)) => {
                    WpdsStepAction::Error(format!(
                        "expected '{}' or '{}', got '{}'",
                        close, sep, token_text,
                    ))
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
                continue;
            };
            let Some(element_src_idx) = lookup_element_src_idx(&shape.element_cat, categories)
            else {
                continue;
            };
            let result_src_idx = cat_i as u16;
            let rule_idx = rule_i as u16;
            arms.push(quote! {
                (#result_src_idx, #rule_idx) => Some(#element_src_idx),
            });
        }
    }
    if arms.is_empty() {
        return quote! { None::<u16> };
    }
    quote! {
        match (result_src_idx, rule_idx) {
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
                continue;
            };
            let result_src_idx = cat_i as u16;
            let rule_idx = rule_i as u16;
            let close = &shape.close;
            arms.push(quote! {
                (#result_src_idx, #rule_idx) => Some(#close),
            });
        }
    }
    if arms.is_empty() {
        return quote! { None::<&'static str> };
    }
    quote! {
        match (result_src_idx, rule_idx) {
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
