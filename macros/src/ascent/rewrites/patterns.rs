#![allow(
    clippy::cmp_owned,
    clippy::too_many_arguments,
    clippy::needless_borrow,
    clippy::for_kv_map,
    clippy::let_and_return,
    clippy::unused_enumerate_index,
    clippy::expect_fun_call,
    clippy::collapsible_match,
    clippy::unwrap_or_default,
    clippy::unnecessary_filter_map
)]

use crate::ascent::congruence;
use crate::ast::{Expr, TheoryDef};
use crate::utils::has_native_type;
use proc_macro2::TokenStream;
use quote::quote;
use std::collections::HashMap;
use syn::Ident;

/// Generate Ascent pattern matching clauses for LHS
/// Handles nested patterns and tracks bindings for equational checks
/// `expected_category` is the category this expression should have based on its context
/// Made public for use in congruence projection generation
pub fn generate_ascent_pattern(
    expr: &Expr,
    term_name: &Ident,
    expected_category: &Ident,
    theory: &TheoryDef,
    bindings: &mut HashMap<String, TokenStream>,
    variable_categories: &mut HashMap<String, Ident>,
    clauses: &mut Vec<TokenStream>,
    duplicate_vars: &std::collections::HashSet<String>,
    equational_checks: &mut Vec<TokenStream>,
) {
    match expr {
        Expr::Var(var) => {
            let var_name = var.to_string();

            // Check if this is actually a nullary constructor (like PZero)
            // Nullary constructors have no semantic fields (NonTerminal, Binder, Collection)
            // They may have Terminal items for syntax (like "0")
            let is_nullary_constructor = theory.terms.iter().any(|rule| {
                use crate::ast::GrammarItem;
                let matches_name = rule.label.to_string() == var_name;
                let matches_category = rule.category == *expected_category;
                let has_no_semantic_fields = rule
                    .items
                    .iter()
                    .all(|item| matches!(item, GrammarItem::Terminal(_)));
                matches_name && matches_category && has_no_semantic_fields
            });

            if is_nullary_constructor {
                // Match the constructor exactly
                let constructor_ident = var;
                clauses.push(quote! {
                    if let #expected_category::#constructor_ident = #term_name
                });
            } else {
                // It's a pattern variable
                let binding = quote! { #term_name.clone() };

                // Check if this is a duplicate variable
                if duplicate_vars.contains(&var_name) {
                    // Check if we've seen this variable before
                    if let Some(first_binding) = bindings.get(&var_name) {
                        // Duplicate occurrence - use the stored category
                        let category = variable_categories
                            .get(&var_name)
                            .expect(&format!("Variable {} should have been tracked", var_name));
                        let eq_rel =
                            quote::format_ident!("eq_{}", category.to_string().to_lowercase());

                        equational_checks.push(quote! {
                            #eq_rel(#first_binding, #binding)
                        });
                    } else {
                        // First occurrence of duplicate variable - bind it and track its category
                        bindings.insert(var_name.clone(), binding);
                        variable_categories.insert(var_name, expected_category.clone());
                    }
                } else {
                    // Single occurrence - bind and track category (needed for env_actions)
                    bindings.insert(var_name.clone(), binding);
                    variable_categories.insert(var_name, expected_category.clone());
                }
            }
        },

        Expr::Apply { constructor, args } => {
            let category = congruence::extract_category(expr, theory).unwrap();

            // Find the grammar rule for this constructor
            let grammar_rule = theory
                .terms
                .iter()
                .find(|r| r.label == *constructor && r.category == category)
                .unwrap_or_else(|| {
                    panic!(
                        "Constructor {} (category: {}) not found in theory. Available: {:?}",
                        constructor,
                        category,
                        theory
                            .terms
                            .iter()
                            .map(|r| (&r.label, &r.category))
                            .collect::<Vec<_>>()
                    )
                });

            // Check if this is a binder constructor
            if !grammar_rule.bindings.is_empty() {
                generate_ascent_binder_pattern(
                    &category,
                    constructor,
                    args,
                    term_name,
                    theory,
                    grammar_rule,
                    bindings,
                    variable_categories,
                    clauses,
                    duplicate_vars,
                    equational_checks,
                );
            } else {
                generate_ascent_regular_pattern(
                    &category,
                    constructor,
                    args,
                    term_name,
                    theory,
                    grammar_rule,
                    bindings,
                    variable_categories,
                    clauses,
                    duplicate_vars,
                    equational_checks,
                );
            }
        },

        Expr::Subst { .. } => {
            panic!("Substitution should not appear in LHS of rewrite rule")
        },

        Expr::CollectionPattern { constructor, elements, rest } => {
            // Collection patterns in LHS need special handling
            generate_ascent_collection_pattern(
                constructor,
                elements,
                rest,
                term_name,
                expected_category,
                theory,
                bindings,
                variable_categories,
                clauses,
                duplicate_vars,
                equational_checks,
            );
        },

        Expr::Lambda { .. } | Expr::MultiLambda { .. } => {
            // TODO: Lambdas CAN appear in LHS patterns, e.g. `in(n, ^x.p)` matches
            // an input constructor with a bound variable. Implement pattern matching
            // for lambda binders when rewrite support is added.
            panic!("Lambda pattern matching in LHS not yet implemented")
        },
    }
}

/// Generate Ascent pattern matching for collection patterns with rest variables
/// Handles patterns like `{P, Q, ...rest}` by:
/// 1. Matching the constructor that contains a collection
/// 2. Checking minimum size
/// 3. Extracting specific elements
/// 4. Binding the rest to remaining elements
#[allow(clippy::too_many_arguments)]
fn generate_ascent_collection_pattern(
    constructor: &Option<Ident>,
    elements: &[Expr],
    rest: &Option<Ident>,
    term_name: &Ident,
    expected_category: &Ident,
    theory: &TheoryDef,
    bindings: &mut HashMap<String, TokenStream>,
    variable_categories: &mut HashMap<String, Ident>,
    clauses: &mut Vec<TokenStream>,
    duplicate_vars: &std::collections::HashSet<String>,
    equational_checks: &mut Vec<TokenStream>,
) {
    // Find the constructor that contains a collection field
    let constructor_ident = if let Some(cons) = constructor {
        cons.clone()
    } else {
        // No explicit constructor - need to infer from context
        // For now, require explicit constructor
        panic!("Collection patterns must specify explicit constructor (e.g., PPar {{P, ...rest}})");
    };

    // Find the grammar rule
    let grammar_rule = theory
        .terms
        .iter()
        .find(|r| r.label == constructor_ident && r.category == *expected_category)
        .unwrap_or_else(|| {
            panic!(
                "Constructor {} (category: {}) not found in theory",
                constructor_ident, expected_category
            )
        });

    // Find the collection field in this constructor
    let collection_info = grammar_rule
        .items
        .iter()
        .enumerate()
        .find_map(|(idx, item)| {
            if let crate::ast::GrammarItem::Collection { element_type, .. } = item {
                Some((idx, element_type.clone()))
            } else {
                None
            }
        })
        .unwrap_or_else(|| {
            panic!("Constructor {} does not have a collection field", constructor_ident)
        });

    let (_field_idx, element_category) = collection_info;

    // Generate pattern match for the constructor
    // For now, assume the collection is the only field (like PPar(HashBag<Proc>))
    let bag_var = quote::format_ident!("{}_bag", term_name);

    clauses.push(quote! {
        if let #expected_category::#constructor_ident(#bag_var) = #term_name
    });

    // Generate loop-based matching for each element (order-independent!)
    let mut elem_vars = Vec::new();

    for (elem_idx, elem_pattern) in elements.iter().enumerate() {
        let elem_var = quote::format_ident!("{}_elem_{}", term_name, elem_idx);
        let count_var = quote::format_ident!("_count_{}_{}", term_name, elem_idx);
        elem_vars.push(elem_var.clone());

        // Generate: for (elem_var, _count_NAME_N) in bag_field.iter()
        clauses.push(quote! {
            for (#elem_var, #count_var) in #bag_var.iter()
        });

        // Add distinctness checks (ensure we don't match the same element twice)
        for prev_elem_var in &elem_vars[..elem_idx] {
            clauses.push(quote! {
                if &#elem_var != &#prev_elem_var
            });
        }

        // Recursively generate pattern for this element
        // This handles Var, Apply, and any nested structures
        generate_ascent_pattern(
            elem_pattern,
            &elem_var,
            &element_category,
            theory,
            bindings,
            variable_categories,
            clauses,
            duplicate_vars,
            equational_checks,
        );
    }

    // Bind rest variable if present
    if let Some(rest_var) = rest {
        let rest_var_name = rest_var.to_string();
        let rest_ident = quote::format_ident!("{}_rest", term_name);

        if !elem_vars.is_empty() {
            // Build rest by removing matched elements
            clauses.push(quote! {
                let #rest_ident = {
                    let mut bag = #bag_var.clone();
                    #(bag.remove(&#elem_vars);)*
                    bag
                }
            });
        } else {
            // No specific elements - rest is the whole bag
            clauses.push(quote! {
                let #rest_ident = #bag_var.clone()
            });
        }

        // Bind the rest variable
        // Rest has type HashBag<ElementCategory>, not ElementCategory
        // Use .clone() since HashBag doesn't implement Copy and may be used multiple times
        bindings.insert(rest_var_name, quote! { #rest_ident.clone() });
        // Don't add to variable_categories since it's a different type (collection vs element)
    }
}

/// Generate pattern for binder constructor in Ascent
fn generate_ascent_binder_pattern(
    category: &Ident,
    constructor: &Ident,
    args: &[Expr],
    term_name: &Ident,
    theory: &TheoryDef,
    grammar_rule: &crate::ast::GrammarRule,
    bindings: &mut HashMap<String, TokenStream>,
    variable_categories: &mut HashMap<String, Ident>,
    clauses: &mut Vec<TokenStream>,
    duplicate_vars: &std::collections::HashSet<String>,
    equational_checks: &mut Vec<TokenStream>,
) {
    // Count all AST fields
    // Note: A binder + its body count as ONE field (the Scope)
    let (_binder_idx, body_indices) = &grammar_rule.bindings[0];
    let body_idx = body_indices[0];

    let mut field_count = 0;
    for (idx, item) in grammar_rule.items.iter().enumerate() {
        match item {
            crate::ast::GrammarItem::NonTerminal(_) => {
                // Regular non-terminal counts as a field, unless it's the body (which is part of the Scope)
                if idx != body_idx {
                    field_count += 1;
                }
            },
            crate::ast::GrammarItem::Collection { .. } => {
                // Collection counts as a field
                field_count += 1;
            },
            crate::ast::GrammarItem::Binder { .. } => {
                // Binder + body together form one Scope field
                field_count += 1;
            },
            crate::ast::GrammarItem::Terminal(_) => {},
        }
    }

    // Generate field names for ALL fields using term_name as prefix for uniqueness
    let term_name_str = term_name.to_string();
    let field_names: Vec<Ident> = (0..field_count)
        .map(|i| quote::format_ident!("{}_f{}", term_name_str, i as u32))
        .collect();

    // Generate pattern: if let Category::Constructor(field_0, field_1, ...) = term_name
    clauses.push(quote! {
        if let #category::#constructor(#(#field_names),*) = #term_name
    });

    // Find which field is the scope (combining binder and body)
    let (binder_idx, body_indices) = &grammar_rule.bindings[0];
    let body_idx = body_indices[0];

    // Map grammar indices to field/arg indices
    // AST fields: non-terminals (except body which is part of Scope) + binder (as Scope)
    let mut grammar_idx_to_field: Vec<Option<usize>> = vec![None; grammar_rule.items.len()];
    let mut field_idx = 0;
    for (grammar_idx, item) in grammar_rule.items.iter().enumerate() {
        match item {
            crate::ast::GrammarItem::NonTerminal(_) => {
                if grammar_idx != body_idx {
                    // Regular non-terminal gets its own field
                    grammar_idx_to_field[grammar_idx] = Some(field_idx);
                    field_idx += 1;
                }
                // Body doesn't get a separate field - it's part of the Scope
            },
            crate::ast::GrammarItem::Collection { .. } => {
                // Collection gets its own field
                grammar_idx_to_field[grammar_idx] = Some(field_idx);
                field_idx += 1;
            },
            crate::ast::GrammarItem::Binder { .. } => {
                // Binder itself points to the Scope field
                grammar_idx_to_field[grammar_idx] = Some(field_idx);
                // Body also points to the same Scope field
                grammar_idx_to_field[body_idx] = Some(field_idx);
                field_idx += 1;
            },
            crate::ast::GrammarItem::Terminal(_) => {},
        }
    }

    // Map grammar indices to arg indices
    // Args in rewrite rule correspond to non-terminals AND binders (but binder appears twice: once for name, once for body)
    let mut grammar_idx_to_arg: Vec<Option<usize>> = vec![None; grammar_rule.items.len()];
    let mut arg_idx = 0;
    for (grammar_idx, item) in grammar_rule.items.iter().enumerate() {
        match item {
            crate::ast::GrammarItem::NonTerminal(_) => {
                if arg_idx < args.len() {
                    grammar_idx_to_arg[grammar_idx] = Some(arg_idx);
                    arg_idx += 1;
                }
            },
            crate::ast::GrammarItem::Collection { .. } => {
                // Collection gets an arg slot
                if arg_idx < args.len() {
                    grammar_idx_to_arg[grammar_idx] = Some(arg_idx);
                    arg_idx += 1;
                }
            },
            crate::ast::GrammarItem::Binder { .. } => {
                // Binder gets TWO arg slots: one for the binder name, one for the body
                // The binder name comes first
                if arg_idx < args.len() {
                    grammar_idx_to_arg[grammar_idx] = Some(arg_idx);
                    arg_idx += 1;
                }
                // Body comes next - map it too
                if body_idx < grammar_rule.items.len() && arg_idx < args.len() {
                    grammar_idx_to_arg[body_idx] = Some(arg_idx);
                    arg_idx += 1;
                }
            },
            crate::ast::GrammarItem::Terminal(_) => {},
        }
    }

    let scope_field_idx =
        grammar_idx_to_field[*binder_idx].expect("Binder should have field index");
    let scope_field = &field_names[scope_field_idx];

    // Access scope without unbinding to preserve variable IDs
    // This is critical for equations where we need structural equality
    let binder_var = quote::format_ident!("binder_{}", bindings.len());
    let body_var = quote::format_ident!("body_{}", bindings.len());

    clauses.push(quote! {
        let #binder_var = #scope_field.inner().unsafe_pattern.clone()
    });
    clauses.push(quote! {
        let #body_var = #scope_field.inner().unsafe_body.as_ref().clone()
    });

    // Bind the binder variable name if present in args
    if let Some(binder_arg_idx) = grammar_idx_to_arg[*binder_idx] {
        if binder_arg_idx < args.len() {
            if let Expr::Var(binder_name_var) = &args[binder_arg_idx] {
                let binder_name = binder_name_var.to_string();
                bindings.insert(binder_name, quote! { #binder_var });
            }
        }
    }

    // Process all arguments
    for (arg_idx, arg) in args.iter().enumerate() {
        // Check if this arg is the binder variable (skip it, already bound above)
        if grammar_idx_to_arg[*binder_idx] == Some(arg_idx) {
            continue;
        }

        // Check if this arg is the body
        if grammar_idx_to_arg[body_idx] == Some(arg_idx) {
            // This is the body - get its category from the grammar
            let body_category = match &grammar_rule.items[body_idx] {
                crate::ast::GrammarItem::NonTerminal(cat) => cat.clone(),
                _ => panic!("Body should be NonTerminal"),
            };

            // Body is already the inner value (not Box) due to unsafe_body access
            // So we can use it directly
            generate_ascent_pattern(
                arg,
                &body_var,
                &body_category,
                theory,
                bindings,
                variable_categories,
                clauses,
                duplicate_vars,
                equational_checks,
            );
        } else {
            // Regular field - find which field it corresponds to
            // Find the grammar index for this arg
            if let Some((grammar_idx, item)) = grammar_rule
                .items
                .iter()
                .enumerate()
                .find(|(gi, _)| grammar_idx_to_arg[*gi] == Some(arg_idx))
            {
                if let crate::ast::GrammarItem::NonTerminal(field_category) = item {
                    if let Some(field_idx) = grammar_idx_to_field[grammar_idx] {
                        let field_name = &field_names[field_idx];
                        let inner_var = quote::format_ident!("{}_val", field_name);
                        clauses.push(quote! {
                            let #inner_var = #field_name.as_ref()
                        });

                        generate_ascent_pattern(
                            arg,
                            &inner_var,
                            field_category,
                            theory,
                            bindings,
                            variable_categories,
                            clauses,
                            duplicate_vars,
                            equational_checks,
                        );
                    }
                }
            }
        }
    }

    // Store binder binding (for legacy compatibility)
    bindings.insert(format!("binder_{}", binder_idx), quote! { #binder_var });
}

/// Generate pattern for regular constructor in Ascent
fn generate_ascent_regular_pattern(
    category: &Ident,
    constructor: &Ident,
    args: &[Expr],
    term_name: &Ident,
    theory: &TheoryDef,
    grammar_rule: &crate::ast::GrammarRule,
    bindings: &mut HashMap<String, TokenStream>,
    variable_categories: &mut HashMap<String, Ident>,
    clauses: &mut Vec<TokenStream>,
    duplicate_vars: &std::collections::HashSet<String>,
    equational_checks: &mut Vec<TokenStream>,
) {
    // Count ALL fields (NonTerminal AND Collection)
    let field_count = grammar_rule
        .items
        .iter()
        .filter(|item| {
            matches!(
                item,
                crate::ast::GrammarItem::NonTerminal(_)
                    | crate::ast::GrammarItem::Collection { .. }
            )
        })
        .count();

    // Generate field names using term_name as prefix for uniqueness
    let term_name_str = term_name.to_string();
    let field_names: Vec<Ident> = (0..field_count)
        .map(|i| quote::format_ident!("{}_f{}", term_name_str, i))
        .collect();

    // Generate pattern: if let Category::Constructor(field_0, field_1, ...) = term_name
    clauses.push(quote! {
        if let #category::#constructor(#(#field_names),*) = #term_name
    });

    // Process each argument
    for (i, arg) in args.iter().enumerate() {
        if i >= field_names.len() {
            break;
        }

        // Get the category/type from the grammar for this field
        let (field_info, is_collection) = grammar_rule
            .items
            .iter()
            .filter(|item| {
                matches!(
                    item,
                    crate::ast::GrammarItem::NonTerminal(_)
                        | crate::ast::GrammarItem::Collection { .. }
                )
            })
            .nth(i)
            .map(|item| match item {
                crate::ast::GrammarItem::NonTerminal(cat) => (cat.clone(), false),
                crate::ast::GrammarItem::Collection { element_type, .. } => {
                    (element_type.clone(), true)
                },
                _ => unreachable!(),
            })
            .unwrap_or_else(|| panic!("Field {} not found in grammar rule", i));

        let field_category = field_info;
        let field_name = &field_names[i];

        match arg {
            Expr::CollectionPattern { elements, rest, .. } if is_collection => {
                // This argument is a collection pattern matching a collection field
                // The field_name already points to the HashBag from the constructor match
                // Generate loop-based matching for order independence!

                let mut elem_vars = Vec::new();

                // Generate loop-based matching for each element
                for (elem_idx, elem_pattern) in elements.iter().enumerate() {
                    let elem_var = quote::format_ident!("{}_elem_{}", field_name, elem_idx);
                    let count_var = quote::format_ident!("_count_{}_{}", field_name, elem_idx);
                    elem_vars.push(elem_var.clone());

                    // Generate: for (elem_var, _count_FIELD_N) in field.iter()
                    clauses.push(quote! {
                        for (#elem_var, #count_var) in #field_name.iter()
                    });

                    // Add distinctness checks (ensure we don't match the same element twice)
                    for prev_elem_var in &elem_vars[..elem_idx] {
                        clauses.push(quote! {
                            if &#elem_var != &#prev_elem_var
                        });
                    }

                    // Recursively generate pattern for this element
                    // This handles Var, Apply, and any nested structures
                    generate_ascent_pattern(
                        elem_pattern,
                        &elem_var,
                        &field_category,
                        theory,
                        bindings,
                        variable_categories,
                        clauses,
                        duplicate_vars,
                        equational_checks,
                    );
                }

                // Bind rest variable if present
                if let Some(rest_var) = rest {
                    let rest_var_name = rest_var.to_string();
                    let rest_ident = quote::format_ident!("{}_rest", field_name);

                    if !elem_vars.is_empty() {
                        // Build rest by removing matched elements
                        clauses.push(quote! {
                            let #rest_ident = {
                                let mut bag = #field_name.clone();
                                #(bag.remove(&#elem_vars);)*
                                bag
                            }
                        });
                    } else {
                        clauses.push(quote! {
                            let #rest_ident = #field_name.clone()
                        });
                    }

                    bindings.insert(rest_var_name, quote! { #rest_ident.clone() });
                }
            },
            Expr::Var(_) => {
                // Check if field is Var type (stored as OrdVar, not Box<OrdVar>)
                let is_var_field = field_category.to_string() == "Var";

                if is_var_field {
                    // Var fields are stored directly as OrdVar, no dereferencing needed
                    generate_ascent_pattern(
                        arg,
                        field_name,
                        &field_category,
                        theory,
                        bindings,
                        variable_categories,
                        clauses,
                        duplicate_vars,
                        equational_checks,
                    );
                } else {
                    // Check if field has native type (like i32)
                    // Integer is a special keyword for native integer types
                    let is_native_type = field_category.to_string() == "Integer"
                        || has_native_type(&field_category, theory).is_some();

                    if is_native_type {
                        // For native types, bind directly without as_ref()
                        // Store binding for the variable (extract name from Var expression)
                        if let Expr::Var(var_name) = arg {
                            bindings.insert(var_name.to_string(), quote! { #field_name.clone() });
                        }
                    } else {
                        // Regular field - need to dereference the Box
                        let inner_var = quote::format_ident!("{}_val", field_name);
                        clauses.push(quote! {
                            let #inner_var = #field_name.as_ref()
                        });

                        generate_ascent_pattern(
                            arg,
                            &inner_var,
                            &field_category,
                            theory,
                            bindings,
                            variable_categories,
                            clauses,
                            duplicate_vars,
                            equational_checks,
                        );
                    }
                }
            },
            Expr::Apply { .. } => {
                // Check if field is Var type (stored as OrdVar, not Box<OrdVar>)
                let is_var_field = field_category.to_string() == "Var";

                if is_var_field {
                    // Var fields are stored directly as OrdVar
                    generate_ascent_pattern(
                        arg,
                        field_name,
                        &field_category,
                        theory,
                        bindings,
                        variable_categories,
                        clauses,
                        duplicate_vars,
                        equational_checks,
                    );
                } else {
                    // Nested constructor - create inner term and recurse
                    let inner_var = quote::format_ident!("{}_inner", field_name);
                    clauses.push(quote! {
                        let #inner_var = #field_name.as_ref()
                    });

                    generate_ascent_pattern(
                        arg,
                        &inner_var,
                        &field_category,
                        theory,
                        bindings,
                        variable_categories,
                        clauses,
                        duplicate_vars,
                        equational_checks,
                    );
                }
            },
            Expr::Subst { .. } => {
                panic!("Substitution in LHS");
            },
            Expr::CollectionPattern { .. } => {
                panic!("Collection pattern in LHS - not yet implemented");
            },
            Expr::Lambda { .. } | Expr::MultiLambda { .. } => {
                panic!("Lambda expressions should not appear in LHS of rewrite rules");
            },
        }
    }
}
