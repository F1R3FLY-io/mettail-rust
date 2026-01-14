#![allow(clippy::cmp_owned)]

use crate::ast::{Expr, GrammarItem, GrammarRule, RewriteRule, TheoryDef};
use std::collections::{HashMap, HashSet};
use syn::Ident;

/// Information about a collection congruence rule
#[allow(dead_code)]
#[derive(Debug, Clone)]
pub struct CollectionCongruenceInfo {
    pub constructor: Ident,      // PPar
    pub parent_category: Ident,  // Proc
    pub element_category: Ident, // Proc (for PPar)
    pub source_var: Ident,       // S in "if S => T"
    pub target_var: Ident,       // T in "if S => T"
    pub rest_var: Option<Ident>, // rest in "{S, ...rest}"
}

/// Information about a regular (non-collection) congruence rule
#[allow(dead_code)]
#[derive(Debug, Clone)]
pub struct RegularCongruencePattern {
    pub constructor: Ident,       // PNew
    pub category: Ident,          // Proc
    pub rewrite_field_idx: usize, // Which field rewrites (the one matching source_var)
    pub is_binding: bool,         // Whether this is a binding constructor
    pub source_var: Ident,        // S in "if S => T"
    pub target_var: Ident,        // T in "if S => T"
}

/// Information about an element pattern extracted from a base rewrite
#[derive(Debug, Clone)]
pub struct ElementPatternInfo {
    pub constructor: Ident, // PInput, POutput, PDrop, PAmb
    pub category: Ident,    // Proc
    pub captures: Vec<CaptureInfo>,
    pub is_nested: bool,         // True if pattern has nested structure
    pub expr: Option<Expr>,      // The full element expression for nested pattern matching
    pub rest_var: Option<Ident>, // Rest variable from the collection pattern
}

/// Information about a captured variable
#[derive(Debug, Clone)]
pub struct CaptureInfo {
    pub var_name: String,
    pub category: Ident,
    pub field_idx: usize,
    pub is_binder: bool,
}

/// Parse a congruence rule LHS to extract constructor, field index, and variable bindings
/// Returns (constructor, rewrite_field_idx, all_bindings)
///
/// For collection congruences, returns a sentinel field_idx of 0.
/// For regular congruences, returns the actual field index where source_var appears.
pub fn parse_congruence_lhs(
    expr: &Expr,
    source_var: &Ident,
    _theory: &TheoryDef,
) -> Option<(Ident, usize, Vec<Ident>)> {
    match expr {
        Expr::Apply { constructor, args } => {
            // Check if any arg is a CollectionPattern
            for arg in args.iter() {
                if let Expr::CollectionPattern { elements, .. } = arg {
                    // Collection pattern case
                    // Check if source_var appears in the elements
                    for elem in elements {
                        if let Expr::Var(v) = elem {
                            if v == source_var {
                                // Found it! This is a collection congruence
                                // Return constructor and a sentinel field_idx
                                // We'll use field_idx = 0 to indicate "collection field"
                                return Some((constructor.clone(), 0, vec![source_var.clone()]));
                            }
                        }
                    }
                }
            }

            // Regular (non-collection) case
            let mut bindings = Vec::new();
            let mut field_idx = None;

            for (i, arg) in args.iter().enumerate() {
                match arg {
                    Expr::Var(var) => {
                        if var == source_var {
                            field_idx = Some(i);
                        }
                        bindings.push(var.clone());
                    },
                    Expr::CollectionPattern { .. } => {
                        // Skip collection patterns in regular case
                        continue;
                    },
                    _ => return None, // Nested constructors not supported in congruence LHS
                }
            }

            Some((constructor.clone(), field_idx?, bindings))
        },
        _ => None,
    }
}

/// Check if a rewrite LHS involves a category
/// This includes:
/// - Root constructor of that category: (PDrop ...)
/// - Collection containing that category: (PPar {(PInput ...), ...})
fn rule_involves_category(expr: &Expr, category: &Ident, theory: &TheoryDef) -> bool {
    // Check root category
    if let Some(root_cat) = extract_category(expr, theory) {
        if root_cat == *category {
            return true;
        }
    }

    // Check collection element categories
    if let Expr::Apply { constructor, args } = expr {
        for arg in args {
            if let Expr::CollectionPattern { .. } = arg {
                // Get collection element type from grammar rule
                if let Some(rule) = theory.terms.iter().find(|r| r.label == *constructor) {
                    for item in &rule.items {
                        if let GrammarItem::Collection { element_type, .. } = item {
                            if element_type == category {
                                return true;
                            }
                        }
                    }
                }
            }
        }
    }

    false
}

/// Find all base rewrites that involve a category
/// This includes:
/// - Root constructor of that category: (PDrop ...)
/// - Collection containing that category: (PPar {(PInput ...), ...})
pub fn find_base_rewrites_for_category<'a>(
    category: &Ident,
    theory: &'a TheoryDef,
) -> Vec<&'a RewriteRule> {
    theory
        .rewrites
        .iter()
        .filter(|rule| {
            // Base rewrites only (no premise)
            rule.premise.is_none() &&
            // Rule involves the target category (either as root or in collection)
            rule_involves_category(&rule.left, category, theory)
        })
        .collect()
}

/// Extract element patterns from a base rewrite LHS
/// For `(PDrop (NQuote P)) => P`: returns [(PDrop, ...)]
/// For `(PPar {(PInput ...), (POutput ...)}) => ...`: returns [(PInput, ...), (POutput, ...)]
pub fn extract_element_patterns_from_base_rewrite(
    lhs: &Expr,
    cong_info: &CollectionCongruenceInfo,
    theory: &TheoryDef,
) -> Vec<ElementPatternInfo> {
    let mut patterns = Vec::new();

    // Only extract patterns from collection LHS that match the congruence's collection constructor
    // Case 1: Direct constructor patterns (e.g., (PDrop ...) for PDrop base rewrite)
    // Case 2: Collection with element patterns (e.g., (PPar {(PInput ...), (POutput ...)})

    if let Expr::Apply { constructor, args } = lhs {
        if *constructor == cong_info.constructor {
            // This is the collection constructor we're interested in
            // Extract element patterns from inside the collection
            for arg in args {
                if let Expr::CollectionPattern { elements, rest, .. } = arg {
                    // Extract each element pattern
                    for elem in elements {
                        if let Some(mut pattern_info) = analyze_constructor_pattern(elem, theory) {
                            // Store the element expression for nested pattern matching
                            if pattern_info.is_nested {
                                pattern_info.expr = Some(elem.clone());
                            }
                            // Store the rest variable from this collection pattern
                            pattern_info.rest_var = rest.clone();
                            patterns.push(pattern_info);
                        }
                    }
                }
            }
        } else {
            // This is a direct pattern (not a collection)
            // Check if it's of the element category
            if let Some(root_cat) = extract_category(lhs, theory) {
                if root_cat == cong_info.element_category {
                    // This is a direct pattern - the congruence should lift it into collections
                    // Extract captures from the pattern for the congruence clause
                    let var_categories = extract_variable_categories(lhs, theory);
                    let captures: Vec<CaptureInfo> = var_categories
                        .iter()
                        .map(|(var_name, cat)| {
                            CaptureInfo {
                                var_name: var_name.clone(),
                                category: cat.clone(),
                                field_idx: 0,     // Not used for nested patterns
                                is_binder: false, // Simplified for now
                            }
                        })
                        .collect();

                    patterns.push(ElementPatternInfo {
                        constructor: constructor.clone(),
                        category: cong_info.element_category.clone(),
                        captures,
                        is_nested: true, // Direct patterns use full pattern matching
                        expr: Some(lhs.clone()), // Store full LHS for pattern matching
                        rest_var: None,  // Direct patterns don't have rest (they're the whole term)
                    });
                }
            }
        }
    }

    patterns
}

/// Analyze a constructor pattern to extract captures
fn analyze_constructor_pattern(expr: &Expr, theory: &TheoryDef) -> Option<ElementPatternInfo> {
    if let Expr::Apply { constructor, args } = expr {
        let grammar_rule = theory.terms.iter().find(|r| r.label == *constructor)?;

        let category = grammar_rule.category.clone();

        // Pattern is nested if it has nested Apply nodes in args (not just Vars)
        let is_nested = args.iter().any(|arg| matches!(arg, Expr::Apply { .. }));

        // For nested patterns, we'll use full pattern matching via generate_ascent_pattern
        // Don't extract captures here - they'll be extracted during projection generation
        let captures = if is_nested {
            Vec::new() // Will be populated during projection generation
        } else {
            // For flat patterns, extract captures normally
            extract_captures(args, grammar_rule, theory)
        };

        return Some(ElementPatternInfo {
            constructor: constructor.clone(),
            category,
            captures,
            is_nested,
            expr: None,     // Will be set by caller if needed
            rest_var: None, // Will be set by caller based on parent collection pattern
        });
    }
    None
}

/// Extract captures from constructor arguments
fn extract_captures(
    args: &[Expr],
    grammar_rule: &GrammarRule,
    _theory: &TheoryDef,
) -> Vec<CaptureInfo> {
    let mut captures = Vec::new();

    // Get non-terminal positions in grammar
    let non_term_positions: Vec<(usize, &GrammarItem)> = grammar_rule
        .items
        .iter()
        .enumerate()
        .filter(|(_, item)| {
            matches!(
                item,
                GrammarItem::NonTerminal(_)
                    | GrammarItem::Binder { .. }
                    | GrammarItem::Collection { .. }
            )
        })
        .collect();

    // Build a map of which indices are bound together
    // For bindings like (binder_idx, [body_idx]), both should map to the same field
    let mut bound_indices: std::collections::HashMap<usize, usize> =
        std::collections::HashMap::new();
    for (binder_idx, body_indices) in &grammar_rule.bindings {
        for body_idx in body_indices {
            bound_indices.insert(*body_idx, *binder_idx);
        }
    }

    // Map grammar indices to field indices, accounting for bindings
    let mut field_idx = 0;
    let mut grammar_to_field = vec![0; grammar_rule.items.len()];
    let mut processed_as_binding = std::collections::HashSet::new();

    for (idx, item) in grammar_rule.items.iter().enumerate() {
        if matches!(
            item,
            GrammarItem::NonTerminal(_)
                | GrammarItem::Binder { .. }
                | GrammarItem::Collection { .. }
        ) {
            // Check if this index is a body that's bound to a binder
            if let Some(&binder_idx) = bound_indices.get(&idx) {
                // This is a body bound to a binder - use the binder's field index
                if let Some(&binder_field) = grammar_to_field.get(binder_idx) {
                    grammar_to_field[idx] = binder_field;
                }
                processed_as_binding.insert(idx);
                continue;
            }

            // Check if this is a binder
            let is_binder = grammar_rule.bindings.iter().any(|(b_idx, _)| *b_idx == idx);
            if is_binder {
                // This is a binder - assign it a field and mark that its bodies will share this field
                grammar_to_field[idx] = field_idx;
                field_idx += 1;
                processed_as_binding.insert(idx);
                continue;
            }

            // Regular non-terminal
            grammar_to_field[idx] = field_idx;
            field_idx += 1;
        }
    }

    // Process each argument
    for (arg_idx, arg) in args.iter().enumerate() {
        if arg_idx >= non_term_positions.len() {
            continue;
        }

        let (grammar_idx, grammar_item) = non_term_positions[arg_idx];
        let field_idx = grammar_to_field[grammar_idx];

        let category = match grammar_item {
            GrammarItem::NonTerminal(cat) => cat.clone(),
            GrammarItem::Binder { category: cat } => cat.clone(),
            GrammarItem::Collection { element_type, .. } => element_type.clone(),
            _ => continue,
        };

        let is_binder = grammar_rule
            .bindings
            .iter()
            .any(|(binder_idx, _)| *binder_idx == grammar_idx);

        // Extract all variables from this argument (handles nested patterns)
        extract_vars_from_expr(arg, &category, field_idx, is_binder, &mut captures);
    }

    captures
}

/// Helper: Extract variables from an expression recursively
fn extract_vars_from_expr(
    expr: &Expr,
    category: &Ident,
    field_idx: usize,
    is_binder: bool,
    captures: &mut Vec<CaptureInfo>,
) {
    match expr {
        Expr::Var(var_name) => {
            captures.push(CaptureInfo {
                var_name: var_name.to_string(),
                category: category.clone(),
                field_idx,
                is_binder,
            });
        },
        Expr::Apply { args, .. } => {
            // Recursively extract from nested constructors
            for arg in args {
                extract_vars_from_expr(arg, category, field_idx, is_binder, captures);
            }
        },
        Expr::CollectionPattern { elements, .. } => {
            // Extract from collection elements
            for elem in elements {
                extract_vars_from_expr(elem, category, field_idx, is_binder, captures);
            }
        },
        Expr::Subst { term, replacement, .. } => {
            extract_vars_from_expr(term, category, field_idx, is_binder, captures);
            extract_vars_from_expr(replacement, category, field_idx, is_binder, captures);
        },
        // Lambda expressions - extract from body
        Expr::Lambda { body, .. } | Expr::MultiLambda { body, .. } => {
            extract_vars_from_expr(body, category, field_idx, is_binder, captures);
        },
    }
}

/// Extract all variables and their categories from an expression
pub fn extract_variable_categories(expr: &Expr, theory: &TheoryDef) -> HashMap<String, Ident> {
    let mut categories = HashMap::new();
    extract_variable_categories_recursive(expr, theory, &mut categories);
    categories
}

/// Recursively extract variable categories from an expression
fn extract_variable_categories_recursive(
    expr: &Expr,
    theory: &TheoryDef,
    categories: &mut HashMap<String, Ident>,
) {
    match expr {
        Expr::Var(_var_name) => {
            // We don't know the category from just the variable, need context
            // This will be filled in from the grammar context
        },
        Expr::Apply { constructor, args } => {
            // Look up the constructor in the grammar to find field categories
            if let Some(grammar_rule) = theory.terms.iter().find(|r| r.label == *constructor) {
                let mut non_term_idx = 0;
                for (item_idx, item) in grammar_rule.items.iter().enumerate() {
                    match item {
                        GrammarItem::NonTerminal(cat) => {
                            if non_term_idx < args.len() {
                                if let Expr::Var(var_name) = &args[non_term_idx] {
                                    categories.insert(var_name.to_string(), cat.clone());
                                } else {
                                    // Recurse into nested expressions
                                    extract_variable_categories_recursive(
                                        &args[non_term_idx],
                                        theory,
                                        categories,
                                    );
                                }
                            }
                            non_term_idx += 1;
                        },
                        GrammarItem::Binder { category } => {
                            if non_term_idx < args.len() {
                                if let Expr::Var(var_name) = &args[non_term_idx] {
                                    categories.insert(var_name.to_string(), category.clone());
                                }
                            }
                            non_term_idx += 1;

                            // The body is the next non-terminal (handled in bindings)
                            if let Some(&body_idx) = grammar_rule
                                .bindings
                                .iter()
                                .find(|(binder_idx, _)| *binder_idx == item_idx)
                                .and_then(|(_, bodies)| bodies.first())
                            {
                                if let Some(GrammarItem::NonTerminal(body_cat)) =
                                    grammar_rule.items.get(body_idx)
                                {
                                    if non_term_idx < args.len() {
                                        if let Expr::Var(var_name) = &args[non_term_idx] {
                                            categories
                                                .insert(var_name.to_string(), body_cat.clone());
                                        } else {
                                            extract_variable_categories_recursive(
                                                &args[non_term_idx],
                                                theory,
                                                categories,
                                            );
                                        }
                                    }
                                    non_term_idx += 1;
                                }
                            }
                        },
                        GrammarItem::Collection { element_type, .. } => {
                            if non_term_idx < args.len() {
                                if let Expr::CollectionPattern { elements, .. } =
                                    &args[non_term_idx]
                                {
                                    for elem in elements {
                                        // Bare variables in collections should have the element type
                                        if let Expr::Var(var_name) = elem {
                                            categories
                                                .insert(var_name.to_string(), element_type.clone());
                                        } else {
                                            extract_variable_categories_recursive(
                                                elem, theory, categories,
                                            );
                                        }
                                    }
                                }
                            }
                            non_term_idx += 1;
                        },
                        _ => {},
                    }
                }
            }
        },
        Expr::Subst { term, .. } => {
            extract_variable_categories_recursive(term, theory, categories);
        },
        Expr::CollectionPattern { elements, .. } => {
            for elem in elements {
                extract_variable_categories_recursive(elem, theory, categories);
            }
        },
        // Lambda expressions - extract from body
        Expr::Lambda { body, .. } | Expr::MultiLambda { body, .. } => {
            extract_variable_categories_recursive(body, theory, categories);
        },
    }
}

/// Check if a rewrite rule is a collection congruence
pub fn is_collection_congruence(rule: &RewriteRule, _theory: &TheoryDef) -> bool {
    // Check if LHS contains CollectionPattern
    contains_collection_pattern(&rule.left)
}

/// Check if an expression contains a collection pattern
pub fn contains_collection_pattern(expr: &Expr) -> bool {
    match expr {
        Expr::CollectionPattern { .. } => true,
        Expr::Apply { args, .. } => args.iter().any(contains_collection_pattern),
        Expr::Subst { term, replacement, .. } => {
            contains_collection_pattern(term) || contains_collection_pattern(replacement)
        },
        Expr::Var(_) => false,
        // Lambdas - check body
        Expr::Lambda { body, .. } | Expr::MultiLambda { body, .. } => {
            contains_collection_pattern(body)
        },
    }
}

/// Extract the category of an expression
pub fn extract_category(expr: &Expr, theory: &TheoryDef) -> Option<Ident> {
    match expr {
        Expr::Apply { constructor, .. } => {
            // Look up this constructor in the theory to find its category
            for rule in &theory.terms {
                if rule.label == *constructor {
                    return Some(rule.category.clone());
                }
            }
            None
        },
        Expr::Var(_) => None,
        Expr::Subst { term, .. } => extract_category(term, theory),
        Expr::CollectionPattern { constructor, .. } => {
            // If constructor is specified, look it up
            if let Some(cons) = constructor {
                for rule in &theory.terms {
                    if rule.label == *cons {
                        return Some(rule.category.clone());
                    }
                }
            }
            None
        },
        // Lambda body determines category
        Expr::Lambda { body, .. } | Expr::MultiLambda { body, .. } => {
            extract_category(body, theory)
        },
    }
}

/// Extract collection congruence information from a congruence rule
/// Returns Some if this is a collection congruence (has CollectionPattern in LHS)
pub fn extract_collection_congruence_info(
    lhs: &Expr,
    source_var: &Ident,
    target_var: &Ident,
    theory: &TheoryDef,
) -> Option<CollectionCongruenceInfo> {
    // Parse: (Constructor {source_var, ...rest})
    if let Expr::Apply { constructor, args } = lhs {
        for arg in args {
            if let Expr::CollectionPattern { elements, rest, .. } = arg {
                // Check if elements contains just source_var
                if elements.len() == 1 {
                    if let Expr::Var(v) = &elements[0] {
                        if v == source_var {
                            // Found it! Get category info
                            let parent_category = theory
                                .terms
                                .iter()
                                .find(|r| r.label == *constructor)
                                .map(|r| r.category.clone())?;

                            // Get element category from the collection field
                            let element_category =
                                get_constructor_collection_element_type(constructor, theory)?;

                            return Some(CollectionCongruenceInfo {
                                constructor: constructor.clone(),
                                parent_category,
                                element_category,
                                source_var: source_var.clone(),
                                target_var: target_var.clone(),
                                rest_var: rest.as_ref().cloned(),
                            });
                        }
                    }
                }
            }
        }
    }
    None
}

/// Find all collection congruence element categories
/// Returns the set of categories that are subjects of collection congruences
pub fn find_collection_congruence_element_categories(theory: &TheoryDef) -> HashSet<Ident> {
    let mut categories = HashSet::new();

    for rule in &theory.rewrites {
        if let Some((source_var, target_var)) = &rule.premise {
            if let Some(info) =
                extract_collection_congruence_info(&rule.left, source_var, target_var, theory)
            {
                categories.insert(info.element_category);
            }
        }
    }

    categories
}

/// Helper: Get element type from a collection constructor
pub fn get_constructor_collection_element_type(
    constructor: &Ident,
    theory: &TheoryDef,
) -> Option<Ident> {
    let grammar_rule = theory.terms.iter().find(|r| r.label == *constructor)?;

    for item in &grammar_rule.items {
        if let GrammarItem::Collection { element_type, .. } = item {
            return Some(element_type.clone());
        }
    }

    None
}
