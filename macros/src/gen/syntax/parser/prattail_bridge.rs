//! Bridge between MeTTaIL's `LanguageDef` AST and PraTTaIL's `LanguageSpec`.
//!
//! Converts the rich `LanguageDef` type (with both old BNFC-style and new
//! judgement-style syntax) into the simplified `LanguageSpec` that PraTTaIL
//! uses for parser generation.

use crate::ast::{
    grammar::{GrammarItem, GrammarRule, PatternOp, SyntaxExpr, TermParam},
    language::LanguageDef,
    types::{CollectionType, TypeExpr},
};
use crate::gen::native::native_type_to_string;
use crate::gen::{is_literal_rule, is_var_rule};
use mettail_prattail::{
    binding_power::Associativity,
    recursive::CollectionKind,
    CategorySpec, LanguageSpec, RuleSpec, SyntaxItemSpec,
};

/// Convert a `LanguageDef` to a PraTTaIL `LanguageSpec`.
pub fn language_def_to_spec(language: &LanguageDef) -> LanguageSpec {
    let categories: Vec<CategorySpec> = language
        .types
        .iter()
        .enumerate()
        .map(|(idx, t)| CategorySpec {
            name: t.name.to_string(),
            native_type: t.native_type.as_ref().map(native_type_to_string),
            is_primary: idx == 0,
        })
        .collect();

    let cat_names: Vec<String> = categories.iter().map(|c| c.name.clone()).collect();

    let rules: Vec<RuleSpec> = language
        .terms
        .iter()
        .map(|rule| convert_rule(rule, &cat_names, language))
        .collect();

    LanguageSpec {
        name: language.name.to_string(),
        types: categories,
        rules,
    }
}

/// Convert a single grammar rule to a PraTTaIL `RuleSpec`.
fn convert_rule(
    rule: &GrammarRule,
    cat_names: &[String],
    _language: &LanguageDef,
) -> RuleSpec {
    let category = rule.category.to_string();
    let label = rule.label.to_string();

    // Determine if this is a postfix rule: exactly [Param(same_category), Terminal]
    let is_postfix = is_postfix_rule_check(rule);

    // Determine if this is an infix rule (postfix also participates in the Pratt led loop)
    let is_infix = is_infix_rule_check(rule) || is_postfix;

    // Determine if this is a cross-category rule
    let (is_cross_category, cross_source) = check_cross_category(rule, cat_names);

    // Determine if this is a cast rule (single non-terminal from different category)
    let (is_cast, cast_source) = check_cast_rule(rule, cat_names);

    // Convert syntax items
    let syntax = if let Some(ref pattern) = rule.syntax_pattern {
        convert_syntax_pattern(pattern, rule.term_context.as_deref().unwrap_or(&[]), cat_names)
    } else {
        convert_grammar_items(&rule.items, cat_names)
    };

    // Determine collection properties
    let (is_collection, collection_type, separator) = check_collection(rule);

    // Check for binders (multi-binder takes precedence over single binder)
    let has_multi_binder = rule
        .term_context
        .as_ref()
        .is_some_and(|ctx| {
            ctx.iter()
                .any(|p| matches!(p, TermParam::MultiAbstraction { .. }))
        });

    let has_binder = !has_multi_binder
        && (rule.bindings.len() == 1
            || rule
                .term_context
                .as_ref()
                .is_some_and(|ctx| {
                    ctx.iter()
                        .any(|p| matches!(p, TermParam::Abstraction { .. }))
                }));

    // Detect unary prefix: exactly [Terminal, Param(same_category)]
    let is_unary_prefix = if let Some(ref sp) = rule.syntax_pattern {
        if sp.len() == 2 {
            if let (SyntaxExpr::Literal(_), SyntaxExpr::Param(p)) = (&sp[0], &sp[1]) {
                let cat_str = rule.category.to_string();
                if let Some(ref tc) = rule.term_context {
                    tc.iter().any(|tp| {
                        if let TermParam::Simple { name, ty } = tp {
                            name.to_string() == p.to_string()
                                && matches!(ty, TypeExpr::Base(t) if t.to_string() == cat_str)
                        } else {
                            false
                        }
                    })
                } else {
                    false
                }
            } else {
                false
            }
        } else {
            false
        }
    } else {
        false
    };

    RuleSpec {
        label,
        category,
        syntax,
        is_infix,
        associativity: if rule.is_right_assoc {
            Associativity::Right
        } else {
            Associativity::Left
        },
        is_var: is_var_rule(rule),
        is_literal: is_literal_rule(rule),
        has_binder,
        has_multi_binder,
        is_collection,
        collection_type,
        separator,
        is_cross_category,
        cross_source_category: cross_source,
        is_cast,
        cast_source_category: cast_source,
        is_unary_prefix,
        prefix_precedence: rule.prefix_bp,
        is_postfix,
        has_rust_code: rule.rust_code.is_some(),
        rust_code: rule.rust_code.as_ref().map(|rc| {
            let expr = &rc.code;
            quote::quote! { #expr }
        }),
        eval_mode: rule.eval_mode.as_ref().map(|e| format!("{:?}", e)),
    }
}

/// Check if a rule is an infix operator.
///
/// Handles both old BNFC-style and new judgement-style syntax.
fn is_infix_rule_check(rule: &GrammarRule) -> bool {
    // New syntax: check syntax_pattern.
    // A rule is infix (or mixfix) if the first item is a Param of the same
    // category. Standard infix: [Param, Literal, Param] (len=3).
    // Mixfix: [Param, Literal, Param, Literal, Param, ...] (len=5+).
    if let (Some(tc), Some(sp)) = (&rule.term_context, &rule.syntax_pattern) {
        if sp.len() >= 3 {
            // First item must be a Param of the same category
            if let SyntaxExpr::Param(first_param) = &sp[0] {
                let cat_str = rule.category.to_string();
                let param_ty = |name: &syn::Ident| -> Option<String> {
                    tc.iter().find_map(|p| {
                        if let TermParam::Simple { name: n, ty } = p {
                            if n.to_string() == name.to_string() {
                                if let TypeExpr::Base(t) = ty {
                                    return Some(t.to_string());
                                }
                            }
                        }
                        None
                    })
                };

                if let Some(first_ty) = param_ty(first_param) {
                    if first_ty == cat_str {
                        // Second item must be a Terminal (the operator/trigger)
                        if matches!(&sp[1], SyntaxExpr::Literal(_)) {
                            return true;
                        }
                    }
                }
            }
        }
        return false;
    }

    // Old syntax: check items
    if rule.items.len() < 3 {
        return false;
    }
    let first_match = matches!(&rule.items[0],
        GrammarItem::NonTerminal(nt) if nt == &rule.category);
    let last_match = matches!(rule.items.last(),
        Some(GrammarItem::NonTerminal(nt)) if nt == &rule.category);
    let has_terminal = rule.items[1..rule.items.len() - 1]
        .iter()
        .any(|item| matches!(item, GrammarItem::Terminal(_)));

    first_match && last_match && has_terminal
}

/// Check if a rule is a postfix operator.
///
/// A postfix rule has syntax pattern [Param(same_category), Terminal],
/// the mirror of a unary prefix [Terminal, Param(same_category)].
/// Examples: `a "!"`, `a "?"`, `a "++"`.
fn is_postfix_rule_check(rule: &GrammarRule) -> bool {
    // New syntax: check syntax_pattern [Param, Literal]
    if let (Some(tc), Some(sp)) = (&rule.term_context, &rule.syntax_pattern) {
        if sp.len() == 2 {
            if let (SyntaxExpr::Param(p), SyntaxExpr::Literal(_)) = (&sp[0], &sp[1]) {
                let cat_str = rule.category.to_string();
                return tc.iter().any(|tp| {
                    if let TermParam::Simple { name, ty } = tp {
                        name.to_string() == p.to_string()
                            && matches!(ty, TypeExpr::Base(t) if t.to_string() == cat_str)
                    } else {
                        false
                    }
                });
            }
        }
        return false;
    }

    // Old syntax: [NonTerminal(Cat), Terminal]
    if rule.items.len() == 2 {
        let first_match = matches!(&rule.items[0],
            GrammarItem::NonTerminal(nt) if nt == &rule.category);
        let second_terminal = matches!(&rule.items[1], GrammarItem::Terminal(_));
        return first_match && second_terminal;
    }

    false
}

/// Check if a rule is a cross-category rule (e.g., Int == Int → Bool).
fn check_cross_category(
    rule: &GrammarRule,
    cat_names: &[String],
) -> (bool, Option<String>) {
    if let Some(ref tc) = rule.term_context {
        if let Some(ref sp) = rule.syntax_pattern {
            if sp.len() == 3 {
                if let (SyntaxExpr::Param(l), SyntaxExpr::Literal(_), SyntaxExpr::Param(r)) =
                    (&sp[0], &sp[1], &sp[2])
                {
                    let cat_str = rule.category.to_string();
                    let param_ty = |name: &syn::Ident| -> Option<String> {
                        tc.iter().find_map(|p| {
                            if let TermParam::Simple { name: n, ty } = p {
                                if n.to_string() == name.to_string() {
                                    if let TypeExpr::Base(t) = ty {
                                        return Some(t.to_string());
                                    }
                                }
                            }
                            None
                        })
                    };

                    if let (Some(lt), Some(rt)) = (param_ty(l), param_ty(r)) {
                        // Cross-category if both operands are the same type but different from result
                        if lt == rt && lt != cat_str && cat_names.contains(&lt) {
                            return (true, Some(lt));
                        }
                    }
                }
            }
        }
    }

    (false, None)
}

/// Check if a rule is a cast rule (single non-terminal from different category).
fn check_cast_rule(
    rule: &GrammarRule,
    cat_names: &[String],
) -> (bool, Option<String>) {
    let cat_str = rule.category.to_string();

    // New syntax: a cast rule must have exactly one parameter of a different
    // category, and the syntax pattern must be just that parameter (no
    // terminals).  Rules like `Len . s:Str |- "|" s "|" : Int` have
    // terminals in the syntax pattern and are NOT simple casts.
    if let Some(ref tc) = rule.term_context {
        if tc.len() == 1 {
            if let TermParam::Simple { ty: TypeExpr::Base(t), .. } = &tc[0] {
                let type_name = t.to_string();
                if type_name != cat_str && cat_names.contains(&type_name) {
                    // Verify the syntax pattern is just a single Param (no terminals)
                    if let Some(ref sp) = rule.syntax_pattern {
                        if sp.len() == 1 && matches!(&sp[0], SyntaxExpr::Param(_)) {
                            return (true, Some(type_name));
                        }
                    }
                    // Syntax has terminals or is missing → not a simple cast
                    return (false, None);
                }
            }
        }
    }

    // Old syntax: single non-terminal from different category
    if rule.items.len() == 1 {
        if let GrammarItem::NonTerminal(nt) = &rule.items[0] {
            let nt_str = nt.to_string();
            if nt_str != cat_str
                && nt_str != "Var"
                && cat_names.contains(&nt_str)
                && !is_var_rule(rule)
            {
                return (true, Some(nt_str));
            }
        }
    }

    (false, None)
}

/// Check if a rule is a collection rule.
fn check_collection(
    rule: &GrammarRule,
) -> (bool, Option<CollectionKind>, Option<String>) {
    // Check old-style items for Collection items
    for item in &rule.items {
        if let GrammarItem::Collection {
            coll_type,
            separator,
            ..
        } = item
        {
            let kind = match coll_type {
                CollectionType::HashBag => CollectionKind::HashBag,
                CollectionType::HashSet => CollectionKind::HashSet,
                CollectionType::Vec => CollectionKind::Vec,
            };
            return (true, Some(kind), Some(separator.clone()));
        }
    }

    // Check new-style term_context for collection types
    if let Some(ref tc) = rule.term_context {
        for param in tc {
            if let TermParam::Simple { ty: TypeExpr::Collection { coll_type, .. }, .. } = param {
                let kind = match coll_type {
                    CollectionType::HashBag => CollectionKind::HashBag,
                    CollectionType::HashSet => CollectionKind::HashSet,
                    CollectionType::Vec => CollectionKind::Vec,
                };
                // Try to find separator from syntax pattern
                let sep = find_separator_in_pattern(rule);
                return (true, Some(kind), sep);
            }
        }
    }

    (false, None, None)
}

/// Find the separator in a syntax pattern's #sep operation.
fn find_separator_in_pattern(rule: &GrammarRule) -> Option<String> {
    if let Some(ref sp) = rule.syntax_pattern {
        for expr in sp {
            if let SyntaxExpr::Op(PatternOp::Sep { separator, .. }) = expr {
                return Some(separator.clone());
            }
        }
    }
    None
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
            }
            SyntaxExpr::Param(name) => {
                let name_str = name.to_string();
                // Look up the parameter type from context
                if let Some(param) = context.iter().find(|p| match p {
                    TermParam::Simple { name: n, .. } => n.to_string() == name_str,
                    TermParam::Abstraction { binder, body, .. } => {
                        binder.to_string() == name_str || body.to_string() == name_str
                    }
                    TermParam::MultiAbstraction { binder, body, .. } => {
                        binder.to_string() == name_str || body.to_string() == name_str
                    }
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
                                items.push(SyntaxItemSpec::IdentCapture {
                                    param_name: name_str,
                                });
                            }
                        }
                        TermParam::Abstraction { binder, body: _, ty, .. } => {
                            if binder.to_string() == name_str {
                                items.push(SyntaxItemSpec::Binder {
                                    param_name: name_str,
                                    category: extract_base_category(ty),
                                });
                            } else {
                                let base_cat = extract_base_category(ty);
                                items.push(SyntaxItemSpec::NonTerminal {
                                    category: base_cat,
                                    param_name: name_str,
                                });
                            }
                        }
                        TermParam::MultiAbstraction { binder, body: _, ty, .. } => {
                            if binder.to_string() == name_str {
                                items.push(SyntaxItemSpec::Binder {
                                    param_name: name_str,
                                    category: extract_base_category(ty),
                                });
                            } else {
                                let base_cat = extract_base_category(ty);
                                items.push(SyntaxItemSpec::NonTerminal {
                                    category: base_cat,
                                    param_name: name_str,
                                });
                            }
                        }
                    }
                } else {
                    // Unknown parameter — treat as ident capture
                    items.push(SyntaxItemSpec::IdentCapture {
                        param_name: name_str,
                    });
                }
            }
            SyntaxExpr::Op(op) => {
                // Pattern operations are handled as collections or special items
                convert_pattern_op(op, context, cat_names, &mut items);
            }
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
        }
        TermParam::MultiAbstraction { binder, body, .. } => {
            binder.to_string() == name_str || body.to_string() == name_str
        }
    }) {
        match param {
            TermParam::Abstraction { binder, ty, .. } if binder.to_string() == name_str => {
                SyntaxItemSpec::Binder {
                    param_name: name_str.to_string(),
                    category: extract_base_category(ty),
                }
            }
            TermParam::MultiAbstraction { binder, ty, .. } if binder.to_string() == name_str => {
                SyntaxItemSpec::Binder {
                    param_name: name_str.to_string(),
                    category: extract_base_category(ty),
                }
            }
            TermParam::Simple { ty, .. } => {
                let base_cat = extract_base_category(ty);
                if cat_names.contains(&base_cat) {
                    SyntaxItemSpec::NonTerminal {
                        category: base_cat,
                        param_name: name_str.to_string(),
                    }
                } else {
                    SyntaxItemSpec::IdentCapture {
                        param_name: name_str.to_string(),
                    }
                }
            }
            // body of an abstraction — treat as nonterminal
            TermParam::Abstraction { ty, .. } | TermParam::MultiAbstraction { ty, .. } => {
                let base_cat = extract_base_category(ty);
                SyntaxItemSpec::NonTerminal {
                    category: base_cat,
                    param_name: name_str.to_string(),
                }
            }
        }
    } else {
        SyntaxItemSpec::IdentCapture {
            param_name: name_str.to_string(),
        }
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
        PatternOp::Sep {
            collection,
            separator,
            source,
        } => {
            if let Some(source_op) = source {
                // Chained pattern: e.g., *zip(ns,xs).*map(|n,x| n "?" x).*sep(",")
                convert_chained_sep(source_op, separator, context, cat_names, items);
            } else {
                // Simple collection sep: e.g., ps.*sep("|")
                let coll_name = collection.to_string();
                let (elem_cat, kind) = find_collection_info(&coll_name, context);

                items.push(SyntaxItemSpec::Collection {
                    param_name: coll_name,
                    element_category: elem_cat,
                    separator: separator.clone(),
                    kind,
                });
            }
        }
        PatternOp::Zip { left, right } => {
            // Zip is usually followed by Map and Sep — handle at the Map level.
            // Classify each parameter correctly (binder vs nonterminal vs ident).
            items.push(classify_param_from_context(&left.to_string(), context, cat_names));
            items.push(classify_param_from_context(&right.to_string(), context, cat_names));
        }
        PatternOp::Map { source: _, params: _, body } => {
            // Map transforms — convert the body items.
            // Parameters inside the map body are local closure params (e.g., |n,x|)
            // and reference the same types as the original term context params.
            for expr in body {
                match expr {
                    SyntaxExpr::Literal(text) => {
                        items.push(SyntaxItemSpec::Terminal(text.clone()));
                    }
                    SyntaxExpr::Param(name) => {
                        // Map closure params reference original context params.
                        // Classify them correctly.
                        items.push(classify_param_from_context(
                            &name.to_string(),
                            context,
                            cat_names,
                        ));
                    }
                    SyntaxExpr::Op(inner_op) => {
                        convert_pattern_op(inner_op, context, cat_names, items);
                    }
                }
            }
        }
        PatternOp::Opt { inner } => {
            // Optional groups: collect inner items and wrap in SyntaxItemSpec::Optional
            let mut opt_items = Vec::new();
            for expr in inner {
                match expr {
                    SyntaxExpr::Literal(text) => {
                        opt_items.push(SyntaxItemSpec::Terminal(text.clone()));
                    }
                    SyntaxExpr::Param(name) => {
                        let item = classify_param_from_context(
                            &name.to_string(), context, cat_names,
                        );
                        opt_items.push(item);
                    }
                    SyntaxExpr::Op(inner_op) => {
                        convert_pattern_op(inner_op, context, cat_names, &mut opt_items);
                    }
                }
            }
            items.push(SyntaxItemSpec::Optional { inner: opt_items });
        }
        PatternOp::Var(name) => {
            items.push(SyntaxItemSpec::IdentCapture {
                param_name: name.to_string(),
            });
        }
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
                            }
                            SyntaxExpr::Op(_) => {
                                // Nested ops in map body — fallback to ident capture
                                SyntaxItemSpec::IdentCapture {
                                    param_name: "__nested_op__".to_string(),
                                }
                            }
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
                }
                _ => {
                    // Unsupported map source — fall back to simple collection
                    items.push(SyntaxItemSpec::Collection {
                        param_name: "__chain__".to_string(),
                        element_category: "Unknown".to_string(),
                        separator: separator.to_string(),
                        kind: CollectionKind::Vec,
                    });
                }
            }
        }
        _ => {
            // Unsupported sep source — fall back to simple collection
            items.push(SyntaxItemSpec::Collection {
                param_name: "__chain__".to_string(),
                element_category: "Unknown".to_string(),
                separator: separator.to_string(),
                kind: CollectionKind::Vec,
            });
        }
    }
}

/// Find the category of a parameter from the term context.
fn find_param_category(name: &str, context: &[TermParam]) -> String {
    for param in context {
        match param {
            TermParam::Simple { name: n, ty, .. } if n.to_string() == name => {
                return extract_base_category(ty);
            }
            TermParam::Abstraction { binder, ty, .. } if binder.to_string() == name => {
                return extract_base_category(ty);
            }
            TermParam::Abstraction { body, ty, .. } if body.to_string() == name => {
                return extract_base_category(ty);
            }
            TermParam::MultiAbstraction { binder, ty, .. } if binder.to_string() == name => {
                return extract_base_category(ty);
            }
            TermParam::MultiAbstraction { body, ty, .. } if body.to_string() == name => {
                return extract_base_category(ty);
            }
            _ => {}
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
            }
            GrammarItem::NonTerminal(nt) => {
                let nt_str = nt.to_string();
                if nt_str == "Var" || nt_str == "Ident" {
                    items.push(SyntaxItemSpec::IdentCapture {
                        param_name: nt_str.to_lowercase(),
                    });
                } else if cat_names.contains(&nt_str) {
                    items.push(SyntaxItemSpec::NonTerminal {
                        category: nt_str.clone(),
                        param_name: nt_str.to_lowercase(),
                    });
                } else {
                    items.push(SyntaxItemSpec::IdentCapture {
                        param_name: nt_str.to_lowercase(),
                    });
                }
            }
            GrammarItem::Binder { category } => {
                items.push(SyntaxItemSpec::Binder {
                    param_name: format!("binder_{}", category.to_string().to_lowercase()),
                    category: category.to_string(),
                });
            }
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
            }
        }
    }

    items
}

/// Extract the base category name from a TypeExpr.
fn extract_base_category(ty: &TypeExpr) -> String {
    match ty {
        TypeExpr::Base(ident) => ident.to_string(),
        TypeExpr::Collection { element, .. } => extract_base_category(element),
        TypeExpr::Arrow { codomain, .. } => extract_base_category(codomain),
        TypeExpr::MultiBinder(inner) => extract_base_category(inner),
    }
}

/// Find collection info (element category and kind) from term context.
fn find_collection_info(name: &str, context: &[TermParam]) -> (String, CollectionKind) {
    for param in context {
        if let TermParam::Simple {
            name: n, ty, ..
        } = param
        {
            if n.to_string() == name {
                if let TypeExpr::Collection {
                    coll_type, element, ..
                } = ty
                {
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
