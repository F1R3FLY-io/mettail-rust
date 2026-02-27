//! Bridge between MeTTaIL's `LanguageDef` AST and PraTTaIL's `LanguageSpec`.
//!
//! Converts the rich `LanguageDef` type (with both old BNFC-style and new
//! judgement-style syntax) into the simplified `LanguageSpec` that PraTTaIL
//! uses for parser generation.
//!
//! This bridge performs **structural mapping only** — converting `GrammarRule`
//! syntax items to `SyntaxItemSpec`. All semantic classification (is_infix,
//! is_postfix, is_cast, etc.) is performed by PraTTaIL's `classify` module
//! via `LanguageSpec::new()`.

use crate::ast::{
    grammar::{GrammarItem, GrammarRule, PatternOp, SyntaxExpr, TermParam},
    language::{AttributeValue, CollectionCategory, LanguageDef},
    types::{CollectionType, TypeExpr},
};
use crate::gen::native::native_type_to_string;
use mettail_prattail::{
    binding_power::Associativity, recursive::CollectionKind, BeamWidthConfig, CategorySpec,
    DispatchStrategy, LanguageSpec, RuleSpecInput, SyntaxItemSpec,
};

/// Convert a `LanguageDef` to a PraTTaIL `LanguageSpec`.
///
/// Performs structural mapping of syntax items, then delegates all
/// flag classification to `LanguageSpec::new()`.
pub fn language_def_to_spec(language: &LanguageDef) -> LanguageSpec {
    // has_var: true for scalar types (IVar, FVar, ...) and for List/Bag (LVar, BVar) so that
    // length(x), at(x, 0), concat(x, y), etc. accept identifier expressions.
    let categories: Vec<CategorySpec> = language
        .types
        .iter()
        .enumerate()
        .map(|(idx, t)| CategorySpec {
            name: t.name.to_string(),
            native_type: t.native_type.as_ref().map(native_type_to_string),
            is_primary: idx == 0,
            has_var: true,
        })
        .collect();

    let cat_names: Vec<String> = categories.iter().map(|c| c.name.clone()).collect();

    let mut inputs: Vec<RuleSpecInput> = language
        .terms
        .iter()
        .map(|rule| convert_rule(rule, &cat_names))
        .collect();

    // Add synthetic variable rules for categories with has_var (no collection_kind) so that
    // identifiers parse as variables and infix expressions like "a + b" work.
    // Use the same label convention as AST (generate_var_label: first letter + "Var", e.g. IVar, PVar).
    for lang_type in &language.types {
        if lang_type.collection_kind.is_none() {
            let category = lang_type.name.to_string();
            let label = crate::gen::generate_var_label(&lang_type.name).to_string();
            inputs.push(RuleSpecInput {
                label,
                category: category.clone(),
                syntax: vec![SyntaxItemSpec::IdentCapture {
                    param_name: "v".to_string(),
                }],
                associativity: mettail_prattail::binding_power::Associativity::Left,
                prefix_precedence: None,
                has_rust_code: false,
                rust_code: None,
                eval_mode: None,
            });
        }
    }

    // Add synthetic variable rules for List/Bag so that identifiers (e.g. x in at(x, 0))
    // parse as list/bag variables when the name is bound in the environment.
    for lang_type in &language.types {
        if lang_type.collection_kind.is_some() {
            let category = lang_type.name.to_string();
            let label = crate::gen::generate_var_label(&lang_type.name).to_string();
            inputs.push(RuleSpecInput {
                label,
                category: category.clone(),
                syntax: vec![SyntaxItemSpec::IdentCapture {
                    param_name: "v".to_string(),
                }],
                associativity: mettail_prattail::binding_power::Associativity::Left,
                prefix_precedence: None,
                has_rust_code: false,
                rust_code: None,
                eval_mode: None,
            });
        }
    }

    // Add synthetic literal rules for List/Bag categories (parameterised by delimiters)
    let elem_cat = language
        .types
        .iter()
        .find(|t| t.name.to_string() == "Proc")
        .map(|t| t.name.to_string())
        .or_else(|| language.types.first().map(|t| t.name.to_string()));
    if let Some(ref elem_cat) = elem_cat {
        for lang_type in &language.types {
            if let Some(ref coll) = lang_type.collection_kind {
                let (label, open, close, sep, kind) = match coll {
                    CollectionCategory::List(d) => (
                        "ListLit".to_string(),
                        d.open.clone(),
                        d.close.clone(),
                        d.sep.clone(),
                        CollectionKind::Vec,
                    ),
                    CollectionCategory::Bag(d) => (
                        "BagLit".to_string(),
                        d.open.clone(),
                        d.close.clone(),
                        d.sep.clone(),
                        CollectionKind::HashBag,
                    ),
                };
                let category = lang_type.name.to_string();
                inputs.push(RuleSpecInput {
                    label: label.clone(),
                    category: category.clone(),
                    syntax: vec![
                        SyntaxItemSpec::Terminal(open),
                        SyntaxItemSpec::Collection {
                            param_name: "elems".to_string(),
                            element_category: elem_cat.clone(),
                            separator: sep,
                            kind,
                        },
                        SyntaxItemSpec::Terminal(close),
                    ],
                    associativity: mettail_prattail::binding_power::Associativity::Left,
                    prefix_precedence: None,
                    has_rust_code: false,
                    rust_code: None,
                    eval_mode: None,
                });
            }
        }
    }

    // Extract beam_width from options (defaults to Disabled if not specified)
    let beam_width = match language.options.get("beam_width") {
        Some(AttributeValue::Float(f)) => BeamWidthConfig::Explicit(*f),
        Some(AttributeValue::Keyword(kw)) => match kw.as_str() {
            "none" | "disabled" => BeamWidthConfig::Disabled,
            "auto" => BeamWidthConfig::Auto,
            _ => unreachable!("beam_width keyword validated at parse time"),
        },
        None => BeamWidthConfig::Disabled,
        _ => unreachable!("beam_width type validated at parse time"),
    };

    let log_semiring_model_path =
        language
            .options
            .get("log_semiring_model_path")
            .map(|v| match v {
                AttributeValue::Str(s) => s.clone(),
                _ => unreachable!("log_semiring_model_path type validated at parse time"),
            });

    let dispatch_strategy = match language.options.get("dispatch") {
        Some(AttributeValue::Keyword(kw)) => match kw.as_str() {
            "static" => DispatchStrategy::Static,
            "weighted" => DispatchStrategy::Weighted,
            "auto" => DispatchStrategy::Auto,
            _ => unreachable!("dispatch keyword validated at parse time"),
        },
        None => DispatchStrategy::Static,
        _ => unreachable!("dispatch type validated at parse time"),
    };

    LanguageSpec::with_options(
        language.name.to_string(),
        categories,
        inputs,
        beam_width,
        log_semiring_model_path,
        dispatch_strategy,
    )
}

/// Convert a single grammar rule to a PraTTaIL `RuleSpecInput`.
///
/// Only performs structural mapping — no flag classification.
fn convert_rule(rule: &GrammarRule, cat_names: &[String]) -> RuleSpecInput {
    // Convert syntax items
    let syntax = if let Some(ref pattern) = rule.syntax_pattern {
        convert_syntax_pattern(pattern, rule.term_context.as_deref().unwrap_or(&[]), cat_names)
    } else {
        convert_grammar_items(&rule.items, cat_names)
    };

    RuleSpecInput {
        label: rule.label.to_string(),
        category: rule.category.to_string(),
        syntax,
        associativity: if rule.is_right_assoc {
            Associativity::Right
        } else {
            Associativity::Left
        },
        prefix_precedence: rule.prefix_bp,
        has_rust_code: rule.rust_code.is_some(),
        rust_code: rule.rust_code.as_ref().map(|rc| {
            let expr = &rc.code;
            quote::quote! { #expr }
        }),
        eval_mode: rule.eval_mode.as_ref().map(|e| format!("{:?}", e)),
    }
}

/// Convert new-style syntax pattern to SyntaxItemSpec list.
fn convert_syntax_pattern(
    pattern: &[SyntaxExpr],
    context: &[TermParam],
    cat_names: &[String],
) -> Vec<SyntaxItemSpec> {
    let mut items = Vec::new();

    for expr in pattern {
        match expr {
            SyntaxExpr::Literal(text) => {
                items.push(SyntaxItemSpec::Terminal(text.clone()));
            },
            SyntaxExpr::Param(name) => {
                let name_str = name.to_string();
                // Look up the parameter type from context
                if let Some(param) = context.iter().find(|p| match p {
                    TermParam::Simple { name: n, .. } => n.to_string() == name_str,
                    TermParam::Abstraction { binder, body, .. } => {
                        binder.to_string() == name_str || body.to_string() == name_str
                    },
                    TermParam::MultiAbstraction { binder, body, .. } => {
                        binder.to_string() == name_str || body.to_string() == name_str
                    },
                }) {
                    match param {
                        TermParam::Simple { ty, .. } => {
                            let base_cat = extract_base_category(ty);
                            if cat_names.contains(&base_cat) {
                                items.push(SyntaxItemSpec::NonTerminal {
                                    category: base_cat,
                                    param_name: name_str,
                                });
                            } else {
                                items.push(SyntaxItemSpec::IdentCapture { param_name: name_str });
                            }
                        },
                        TermParam::Abstraction { binder, body: _, ty, .. } => {
                            if binder.to_string() == name_str {
                                items.push(SyntaxItemSpec::Binder {
                                    param_name: name_str,
                                    category: extract_binder_category(ty),
                                    is_multi: false,
                                });
                            } else {
                                let base_cat = extract_base_category(ty);
                                items.push(SyntaxItemSpec::NonTerminal {
                                    category: base_cat,
                                    param_name: name_str,
                                });
                            }
                        },
                        TermParam::MultiAbstraction { binder, body: _, ty, .. } => {
                            if binder.to_string() == name_str {
                                items.push(SyntaxItemSpec::Binder {
                                    param_name: name_str,
                                    category: extract_binder_category(ty),
                                    is_multi: true,
                                });
                            } else {
                                let base_cat = extract_base_category(ty);
                                items.push(SyntaxItemSpec::NonTerminal {
                                    category: base_cat,
                                    param_name: name_str,
                                });
                            }
                        },
                    }
                } else {
                    // Unknown parameter — treat as ident capture
                    items.push(SyntaxItemSpec::IdentCapture { param_name: name_str });
                }
            },
            SyntaxExpr::Op(op) => {
                // Pattern operations are handled as collections or special items
                convert_pattern_op(op, context, cat_names, &mut items);
            },
        }
    }

    items
}

/// Classify a parameter name from the term context into the correct SyntaxItemSpec.
///
/// Checks whether the parameter is a binder, a nonterminal, or an ident capture
/// based on its definition in the term context.
fn classify_param_from_context(
    name_str: &str,
    context: &[TermParam],
    cat_names: &[String],
) -> SyntaxItemSpec {
    if let Some(param) = context.iter().find(|p| match p {
        TermParam::Simple { name, .. } => name.to_string() == name_str,
        TermParam::Abstraction { binder, body, .. } => {
            binder.to_string() == name_str || body.to_string() == name_str
        },
        TermParam::MultiAbstraction { binder, body, .. } => {
            binder.to_string() == name_str || body.to_string() == name_str
        },
    }) {
        match param {
            TermParam::Abstraction { binder, ty, .. } if binder.to_string() == name_str => {
                SyntaxItemSpec::Binder {
                    param_name: name_str.to_string(),
                    category: extract_binder_category(ty),
                    is_multi: false,
                }
            },
            TermParam::MultiAbstraction { binder, ty, .. } if binder.to_string() == name_str => {
                SyntaxItemSpec::Binder {
                    param_name: name_str.to_string(),
                    category: extract_binder_category(ty),
                    is_multi: true,
                }
            },
            TermParam::Simple { ty, .. } => {
                let base_cat = extract_base_category(ty);
                if cat_names.contains(&base_cat) {
                    SyntaxItemSpec::NonTerminal {
                        category: base_cat,
                        param_name: name_str.to_string(),
                    }
                } else {
                    SyntaxItemSpec::IdentCapture { param_name: name_str.to_string() }
                }
            },
            // body of an abstraction — treat as nonterminal
            TermParam::Abstraction { ty, .. } | TermParam::MultiAbstraction { ty, .. } => {
                let base_cat = extract_base_category(ty);
                SyntaxItemSpec::NonTerminal {
                    category: base_cat,
                    param_name: name_str.to_string(),
                }
            },
        }
    } else {
        SyntaxItemSpec::IdentCapture { param_name: name_str.to_string() }
    }
}

/// Convert a pattern operation to syntax items.
fn convert_pattern_op(
    op: &PatternOp,
    context: &[TermParam],
    cat_names: &[String],
    items: &mut Vec<SyntaxItemSpec>,
) {
    match op {
        PatternOp::Sep { collection, separator, source } => {
            if let Some(source_op) = source {
                // Chained pattern: e.g., *zip(ns,xs).*map(|n,x| n "?" x).*sep(",")
                convert_chained_sep(source_op, separator, context, cat_names, items);
            } else {
                let coll_name = collection.to_string();

                // Check if this is a multi-binder collection (e.g., xs.*sep(",")
                // where xs comes from ^[xs].p:[Name* -> Proc])
                let is_multi_binder = context.iter().any(|p| {
                    matches!(p, TermParam::MultiAbstraction { binder, .. }
                        if binder.to_string() == coll_name)
                });

                if is_multi_binder {
                    items.push(SyntaxItemSpec::BinderCollection {
                        param_name: coll_name,
                        separator: separator.clone(),
                    });
                } else {
                    let (elem_cat, kind) = find_collection_info(&coll_name, context);
                    items.push(SyntaxItemSpec::Collection {
                        param_name: coll_name,
                        element_category: elem_cat,
                        separator: separator.clone(),
                        kind,
                    });
                }
            }
        },
        PatternOp::Zip { left, right } => {
            // Zip is usually followed by Map and Sep — handle at the Map level.
            // Classify each parameter correctly (binder vs nonterminal vs ident).
            items.push(classify_param_from_context(&left.to_string(), context, cat_names));
            items.push(classify_param_from_context(&right.to_string(), context, cat_names));
        },
        PatternOp::Map { source: _, params: _, body } => {
            // Map transforms — convert the body items.
            // Parameters inside the map body are local closure params (e.g., |n,x|)
            // and reference the same types as the original term context params.
            for expr in body {
                match expr {
                    SyntaxExpr::Literal(text) => {
                        items.push(SyntaxItemSpec::Terminal(text.clone()));
                    },
                    SyntaxExpr::Param(name) => {
                        // Map closure params reference original context params.
                        // Classify them correctly.
                        items.push(classify_param_from_context(
                            &name.to_string(),
                            context,
                            cat_names,
                        ));
                    },
                    SyntaxExpr::Op(inner_op) => {
                        convert_pattern_op(inner_op, context, cat_names, items);
                    },
                }
            }
        },
        PatternOp::Opt { inner } => {
            // Optional groups: collect inner items and wrap in SyntaxItemSpec::Optional
            let mut opt_items = Vec::new();
            for expr in inner {
                match expr {
                    SyntaxExpr::Literal(text) => {
                        opt_items.push(SyntaxItemSpec::Terminal(text.clone()));
                    },
                    SyntaxExpr::Param(name) => {
                        let item =
                            classify_param_from_context(&name.to_string(), context, cat_names);
                        opt_items.push(item);
                    },
                    SyntaxExpr::Op(inner_op) => {
                        convert_pattern_op(inner_op, context, cat_names, &mut opt_items);
                    },
                }
            }
            items.push(SyntaxItemSpec::Optional { inner: opt_items });
        },
        PatternOp::Var(name) => {
            items.push(SyntaxItemSpec::IdentCapture { param_name: name.to_string() });
        },
    }
}

/// Convert a chained Sep(Map(Zip(...))) pattern into a ZipMapSep syntax item.
///
/// This handles patterns like `*zip(ns,xs).*map(|n,x| n "?" x).*sep(",")`,
/// converting them into a single `ZipMapSep` item that the RD generator
/// can handle as a separated list of structured patterns.
fn convert_chained_sep(
    source_op: &PatternOp,
    separator: &str,
    context: &[TermParam],
    cat_names: &[String],
    items: &mut Vec<SyntaxItemSpec>,
) {
    match source_op {
        PatternOp::Map { source, params, body } => {
            match source.as_ref() {
                PatternOp::Zip { left, right } => {
                    let left_name = left.to_string();
                    let right_name = right.to_string();

                    // Determine categories for left and right from the term context
                    let left_cat = find_param_category(&left_name, context);
                    let right_cat = find_param_category(&right_name, context);

                    // Build a mapping from closure params to zip params
                    // e.g., |n,x| means n→ns (left), x→xs (right)
                    let mut param_mapping: std::collections::HashMap<String, String> =
                        std::collections::HashMap::new();
                    if !params.is_empty() {
                        param_mapping.insert(params[0].to_string(), left_name.clone());
                    }
                    if params.len() >= 2 {
                        param_mapping.insert(params[1].to_string(), right_name.clone());
                    }

                    // Convert body items, resolving closure params to their original context
                    let body_items: Vec<SyntaxItemSpec> = body
                        .iter()
                        .map(|expr| match expr {
                            SyntaxExpr::Literal(text) => SyntaxItemSpec::Terminal(text.clone()),
                            SyntaxExpr::Param(name) => {
                                let name_str = name.to_string();
                                // Check if this is a closure param and map it back
                                if let Some(original) = param_mapping.get(&name_str) {
                                    classify_param_from_context(original, context, cat_names)
                                } else {
                                    classify_param_from_context(&name_str, context, cat_names)
                                }
                            },
                            SyntaxExpr::Op(_) => {
                                // Nested ops in map body — fallback to ident capture
                                SyntaxItemSpec::IdentCapture {
                                    param_name: "__nested_op__".to_string(),
                                }
                            },
                        })
                        .collect();

                    items.push(SyntaxItemSpec::ZipMapSep {
                        left_name,
                        right_name,
                        left_category: left_cat,
                        right_category: right_cat,
                        body_items,
                        separator: separator.to_string(),
                    });
                },
                _ => {
                    // Unsupported map source — fall back to simple collection
                    items.push(SyntaxItemSpec::Collection {
                        param_name: "__chain__".to_string(),
                        element_category: "Unknown".to_string(),
                        separator: separator.to_string(),
                        kind: CollectionKind::Vec,
                    });
                },
            }
        },
        _ => {
            // Unsupported sep source — fall back to simple collection
            items.push(SyntaxItemSpec::Collection {
                param_name: "__chain__".to_string(),
                element_category: "Unknown".to_string(),
                separator: separator.to_string(),
                kind: CollectionKind::Vec,
            });
        },
    }
}

/// Find the category of a parameter from the term context.
fn find_param_category(name: &str, context: &[TermParam]) -> String {
    for param in context {
        match param {
            TermParam::Simple { name: n, ty, .. } if n.to_string() == name => {
                return extract_base_category(ty);
            },
            TermParam::Abstraction { binder, ty, .. } if binder.to_string() == name => {
                return extract_binder_category(ty);
            },
            TermParam::Abstraction { body, ty, .. } if body.to_string() == name => {
                return extract_base_category(ty);
            },
            TermParam::MultiAbstraction { binder, ty, .. } if binder.to_string() == name => {
                return extract_binder_category(ty);
            },
            TermParam::MultiAbstraction { body, ty, .. } if body.to_string() == name => {
                return extract_base_category(ty);
            },
            _ => {},
        }
    }
    "Unknown".to_string()
}

/// Convert old-style grammar items to SyntaxItemSpec list.
fn convert_grammar_items(
    grammar_items: &[GrammarItem],
    cat_names: &[String],
) -> Vec<SyntaxItemSpec> {
    let mut items = Vec::new();

    for gi in grammar_items {
        match gi {
            GrammarItem::Terminal(text) => {
                items.push(SyntaxItemSpec::Terminal(text.clone()));
            },
            GrammarItem::NonTerminal(nt) => {
                let nt_str = nt.to_string();
                if nt_str == "Var" || nt_str == "Ident" {
                    items.push(SyntaxItemSpec::IdentCapture { param_name: nt_str.to_lowercase() });
                } else if cat_names.contains(&nt_str) {
                    items.push(SyntaxItemSpec::NonTerminal {
                        category: nt_str.clone(),
                        param_name: nt_str.to_lowercase(),
                    });
                } else {
                    items.push(SyntaxItemSpec::IdentCapture { param_name: nt_str.to_lowercase() });
                }
            },
            GrammarItem::Binder { category } => {
                items.push(SyntaxItemSpec::Binder {
                    param_name: format!("binder_{}", category.to_string().to_lowercase()),
                    category: category.to_string(),
                    is_multi: false,
                });
            },
            GrammarItem::Collection {
                coll_type,
                element_type,
                separator,
                delimiters,
            } => {
                let kind = match coll_type {
                    CollectionType::HashBag => CollectionKind::HashBag,
                    CollectionType::HashSet => CollectionKind::HashSet,
                    CollectionType::Vec => CollectionKind::Vec,
                };
                // Add open delimiter if present
                if let Some((ref open, _)) = delimiters {
                    items.push(SyntaxItemSpec::Terminal(open.clone()));
                }
                items.push(SyntaxItemSpec::Collection {
                    param_name: element_type.to_string().to_lowercase(),
                    element_category: element_type.to_string(),
                    separator: separator.clone(),
                    kind,
                });
                // Add close delimiter if present
                if let Some((_, ref close)) = delimiters {
                    items.push(SyntaxItemSpec::Terminal(close.clone()));
                }
            },
        }
    }

    items
}

/// Extract the base category name from a TypeExpr.
/// For Arrow types, follows the codomain (appropriate for body variables).
fn extract_base_category(ty: &TypeExpr) -> String {
    match ty {
        TypeExpr::Base(ident) => ident.to_string(),
        TypeExpr::Collection { element, .. } => extract_base_category(element),
        TypeExpr::Arrow { codomain, .. } => extract_base_category(codomain),
        TypeExpr::MultiBinder(inner) => extract_base_category(inner),
    }
}

/// Extract the binder's category from an abstraction type.
/// For Arrow types `[A -> B]` or `[A* -> B]`, returns the domain category `A`.
fn extract_binder_category(ty: &TypeExpr) -> String {
    match ty {
        TypeExpr::Arrow { domain, .. } => extract_base_category(domain),
        _ => extract_base_category(ty),
    }
}

/// Find collection info (element category and kind) from term context.
fn find_collection_info(name: &str, context: &[TermParam]) -> (String, CollectionKind) {
    for param in context {
        if let TermParam::Simple { name: n, ty, .. } = param {
            if n.to_string() == name {
                if let TypeExpr::Collection { coll_type, element, .. } = ty {
                    let elem_cat = extract_base_category(element);
                    let kind = match coll_type {
                        CollectionType::HashBag => CollectionKind::HashBag,
                        CollectionType::HashSet => CollectionKind::HashSet,
                        CollectionType::Vec => CollectionKind::Vec,
                    };
                    return (elem_cat, kind);
                }
            }
        }
    }

    // Fallback: unknown element type
    ("Unknown".to_string(), CollectionKind::Vec)
}

/// Generate the PraTTaIL parser for a language definition.
///
/// This is the main entry point for PraTTaIL parser generation.
/// Returns a TokenStream containing the complete parser code.
pub fn generate_prattail_parser(language: &LanguageDef) -> proc_macro2::TokenStream {
    let spec = language_def_to_spec(language);
    mettail_prattail::generate_parser(&spec)
}
