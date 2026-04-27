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
use mettail_ast::types::{CollectionType, TypeExpr};
use proc_macro2::TokenStream;
use quote::quote;

/// Classification of a collection-literal rule.
#[derive(Debug, Clone)]
pub struct CollectionShape {
    /// Open delimiter (e.g., `"{"` for HashBag, `"["` for Vec).
    pub open: String,
    /// Close delimiter.
    pub close: String,
    /// Separator between elements (e.g., `"|"` for HashBag).
    pub separator: String,
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
pub(crate) fn classify_collection(rule: &GrammarRule) -> Option<CollectionShape> {
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
    // Expect syntax_pattern = [Literal(open), Op(Sep), Literal(close)].
    if sp.len() != 3 {
        return None;
    }
    let open = match &sp[0] {
        SyntaxExpr::Literal(s) => s.clone(),
        _ => return None,
    };
    let close = match &sp[2] {
        SyntaxExpr::Literal(s) => s.clone(),
        _ => return None,
    };
    let separator = match &sp[1] {
        SyntaxExpr::Op(PatternOp::Sep {
            collection,
            separator,
            source: None,
        }) if collection == param_name => separator.clone(),
        _ => return None,
    };
    Some(CollectionShape {
        open,
        close,
        separator,
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
            let Some(shape) = classify_collection(rule) else {
                continue;
            };
            let result_src_idx = cat_i as u16;
            let rule_idx = rule_i as u16;
            let open = &shape.open;
            // Look up the element category's src_idx for the cross-cat case.
            let element_src_idx = lookup_element_src_idx(&shape.element_cat, categories);
            // Self-collection (element_cat == result_cat) — frontier_top.cat_src_idx
            // already routes correctly. No CategoryEntry push needed.
            if element_src_idx == Some(result_src_idx) {
                arms.push(quote! {
                    Some(mettail_prattail::automata::TokenKind::Fixed(__open))
                        if __open == #open && state_cat_src_idx == #result_src_idx => {
                        return WpdsStepAction::ConsumeAndPush {
                            symbol: StackSymbolV2::collection_marker(
                                #result_src_idx, #rule_idx, 0,
                            ),
                            weight: LexicographicWeight::from_cost(
                                0.0, #result_src_idx, #rule_idx,
                            ),
                            new_state: WpdsState::PrefixDispatch {
                                pos: *pos + 1,
                                cur_bp: 0,
                            },
                            capture_token: false,
                        };
                    }
                });
            } else if let Some(element_src) = element_src_idx {
                // Cross-cat collection: push CategoryEntry(element_src_idx)
                // on top of the marker so PrefixDispatch routes to element cat.
                arms.push(quote! {
                    Some(mettail_prattail::automata::TokenKind::Fixed(__open))
                        if __open == #open && state_cat_src_idx == #result_src_idx => {
                        // Push the marker first via ConsumeAndPush. Walker
                        // auto-allocates accumulator_id. Then the next step
                        // (in PrefixDispatch with marker on top) will detect
                        // a cross-cat shape via lookup and Push CategoryEntry.
                        return WpdsStepAction::ConsumeAndPush {
                            symbol: StackSymbolV2::collection_marker(
                                #result_src_idx, #rule_idx, 0,
                            ),
                            weight: LexicographicWeight::from_cost(
                                0.0, #result_src_idx, #rule_idx,
                            ),
                            new_state: WpdsState::PrefixDispatch {
                                pos: *pos + 1,
                                cur_bp: 0,
                            },
                            capture_token: false,
                        };
                    }
                });
                let _ = element_src;
            }
        }
    }
    let _ = language;
    quote! { #(#arms)* }
}

/// Phase 4: emit the body of `WpdsState::CollectionLoop`. Looks up the
/// close + separator for the marker's `(result_src_idx, rule_idx)`, then
/// dispatches: token == close → `ConsumeAndPop` (fires finalize); token
/// == sep → `Consume` → `PrefixDispatch{cur_bp:0}` to parse next element;
/// else → `Error`.
pub(crate) fn emit_collection_loop_arm(
    _language: &mettail_ast::language::LanguageDef,
    _categories: &[String],
    per_cat: &[Vec<GrammarRule>],
) -> TokenStream {
    // Per-rule lookup arms: (result_src_idx, rule_idx) → (close, sep).
    let mut lookup_arms = Vec::new();
    for (cat_i, rules) in per_cat.iter().enumerate() {
        for (rule_i, rule) in rules.iter().enumerate() {
            let Some(shape) = classify_collection(rule) else {
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
    categories: &[String],
    per_cat: &[Vec<GrammarRule>],
) -> TokenStream {
    let mut arms = Vec::new();
    for (cat_i, rules) in per_cat.iter().enumerate() {
        for (rule_i, rule) in rules.iter().enumerate() {
            let Some(shape) = classify_collection(rule) else {
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
pub(crate) fn emit_collection_close_lookup(per_cat: &[Vec<GrammarRule>]) -> TokenStream {
    let mut arms = Vec::new();
    for (cat_i, rules) in per_cat.iter().enumerate() {
        for (rule_i, rule) in rules.iter().enumerate() {
            let Some(shape) = classify_collection(rule) else {
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
        let shape = classify_collection(&rule).expect("collection");
        assert_eq!(shape.open, "{");
        assert_eq!(shape.close, "}");
        assert_eq!(shape.separator, "|");
        assert_eq!(shape.element_cat, "Proc");
        assert_eq!(shape.label, "PPar");
        assert_eq!(shape.result_cat, "Proc");
        assert!(matches!(shape.coll_kind, CollectionType::HashBag));
    }
}
