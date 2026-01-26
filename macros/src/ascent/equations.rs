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
use crate::ascent::rewrites;
use crate::ast::{Equation, Expr, TheoryDef};
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use std::collections::{HashMap, HashSet};
use syn::Ident;

/// Main entry point: Generate all equation rules
pub fn generate_equation_rules(theory: &TheoryDef) -> TokenStream {
    let mut rules = Vec::new();

    // Add reflexivity for eq relations
    // This is needed for rewrites that check eq_cat(x, y) where x == y syntactically
    // The eqrel data structure requires explicit seeding even for reflexivity
    for export in &theory.exports {
        let cat = &export.name;
        let cat_lower = format_ident!("{}", cat.to_string().to_lowercase());
        let eq_rel = format_ident!("eq_{}", cat.to_string().to_lowercase());

        rules.push(quote! {
            #eq_rel(t.clone(), t.clone()) <-- #cat_lower(t);
        });
    }

    // Add congruence rules for all constructors
    // If arg1 == arg2, then Constructor(arg1) == Constructor(arg2)
    let congruence_rules = generate_congruence_rules(theory);
    rules.extend(congruence_rules);

    // Generate clauses for each equation declaration
    // These add the BASE equalities specified by the theory
    for equation in theory.equations.iter() {
        if let Some(rule) = generate_equation_clause(equation, theory) {
            rules.push(rule);
        } else {
            eprintln!("  ❌ Failed to generate (returned None)");
        }
    }

    quote! {
        #(#rules)*
    }
}

/// Generate congruence rules for equality
/// For each constructor, generate: if args are equal, then constructed terms are equal
fn generate_congruence_rules(theory: &TheoryDef) -> Vec<TokenStream> {
    let mut rules = Vec::new();

    for grammar_rule in &theory.terms {
        let category = &grammar_rule.category;
        let eq_rel = format_ident!("eq_{}", category.to_string().to_lowercase());
        let _cat_lower = format_ident!("{}", category.to_string().to_lowercase());

        // Check if this constructor has binders
        let has_binders = !grammar_rule.bindings.is_empty();

        if has_binders {
            // Skip binders for now - congruence for binders is more complex
            // (requires alpha-equivalence reasoning)
            continue;
        }

        // Check if this constructor has collections - skip if so
        let has_collections = grammar_rule
            .items
            .iter()
            .any(|item| matches!(item, crate::ast::GrammarItem::Collection { .. }));

        if has_collections {
            // Skip collections - they have built-in equality
            // (HashBag/HashSet equality is order-independent)
            continue;
        }

        // Build parameter map for HOL syntax
        let param_map: std::collections::HashMap<String, syn::Ident> = grammar_rule
            .parameters
            .iter()
            .map(|p| (p.name.to_string(), p.param_type.clone()))
            .collect();

        // Collect non-terminal arguments and their categories
        let mut args = Vec::new();
        let mut arg_categories = Vec::new();

        for item in &grammar_rule.items {
            if let crate::ast::GrammarItem::NonTerminal(cat) = item {
                // HOL syntax: resolve parameter names to their types
                let resolved_cat = param_map
                    .get(&cat.to_string())
                    .cloned()
                    .unwrap_or_else(|| cat.clone());
                args.push(resolved_cat);
                arg_categories.push(cat);
            }
        }

        if args.is_empty() {
            // No arguments - nullary constructor, no congruence needed
            continue;
        }

        // Skip constructors with Var or Integer arguments - they are built-in types, not user-defined categories
        if args.iter().any(|cat| {
            let cat_str = cat.to_string();
            cat_str == "Var" || cat_str == "Integer"
        }) {
            continue;
        }

        // Generate variable names for LHS and RHS
        let lhs_vars: Vec<Ident> = (0..args.len()).map(|i| format_ident!("x{}", i)).collect();
        let rhs_vars: Vec<Ident> = (0..args.len()).map(|i| format_ident!("y{}", i)).collect();

        // Generate category bindings and equality checks for each argument
        // For each arg: cat(x), cat(y), eq_cat(x, y)
        // Note: First occurrences bind the variables (no .clone()), subsequent uses need .clone()
        let mut body_clauses = Vec::new();

        for (cat, (lhs, rhs)) in args.iter().zip(lhs_vars.iter().zip(rhs_vars.iter())) {
            let cat_rel = format_ident!("{}", cat.to_string().to_lowercase());
            let eq_arg_rel = format_ident!("eq_{}", cat.to_string().to_lowercase());

            // Bind the variables (no .clone())
            //////////////////// trying without! //////////////////
            body_clauses.push(quote! { #cat_rel(#lhs) });
            body_clauses.push(quote! { #cat_rel(#rhs) });
            // Use the bound variables (.clone() needed here)
            body_clauses.push(quote! { #eq_arg_rel(#lhs.clone(), #rhs.clone()) });
        }

        // Generate LHS and RHS constructor applications for the head
        let lhs_boxed: Vec<TokenStream> = lhs_vars
            .iter()
            .map(|v| quote! { Box::new(#v.clone()) })
            .collect();
        let rhs_boxed: Vec<TokenStream> = rhs_vars
            .iter()
            .map(|v| quote! { Box::new(#v.clone()) })
            .collect();

        let label = grammar_rule.label.clone();
        // Generate the congruence rule
        // eq_cat(Constructor(x0, x1, ...), Constructor(y0, y1, ...)) <--
        //   cat0(x0), cat0(y0), eq_cat0(x0, y0),
        //   cat1(x1), cat1(y1), eq_cat1(x1, y1), ...
        rules.push(quote! {
            #eq_rel(
                #category::#label(#(#lhs_boxed),*),
                #category::#label(#(#rhs_boxed),*)
            ) <-- #(#body_clauses),*;
        });
    }

    rules
}

/// Adapter function: Use rewrite rule pattern matching for equations
/// Converts between equation-style bindings and rewrite-style bindings
/// This allows equations to leverage the full power of rewrite pattern matching
fn generate_equation_pattern_via_rewrite_logic(
    expr: &Expr,
    term_name: &str,
    bindings: &mut HashMap<String, Ident>,
    theory: &TheoryDef,
) -> Option<Vec<TokenStream>> {
    // Setup for rewrite pattern matching
    let mut rewrite_bindings: HashMap<String, TokenStream> = HashMap::new();
    let mut variable_categories: HashMap<String, Ident> = HashMap::new();
    let mut clauses: Vec<TokenStream> = Vec::new();
    let duplicate_vars: HashSet<String> = HashSet::new(); // No duplicates in single-occurrence equations
    let mut equational_checks: Vec<TokenStream> = Vec::new();

    // Call rewrite pattern logic
    let term_ident = format_ident!("{}", term_name);
    let expected_category = congruence::extract_category(expr, theory)?;

    rewrites::generate_ascent_pattern(
        expr,
        &term_ident,
        &expected_category,
        theory,
        &mut rewrite_bindings,
        &mut variable_categories,
        &mut clauses,
        &duplicate_vars,
        &mut equational_checks,
    );

    // Convert bindings to equation format
    // Rewrite bindings are TokenStream like `term.clone()` or `(*field).clone()`
    // For equations, we need explicit `let var = ...` bindings after pattern matching
    // so the RHS can reference simple variable names
    let mut explicit_bindings = Vec::new();

    for (var_name, binding_expr) in &rewrite_bindings {
        // Skip internal binder variable names (binder_0, binder_1, etc.)
        // These are implementation details, not user-facing variables
        if var_name.starts_with("binder_") {
            continue;
        }

        let var_snake = to_snake_case(var_name);
        let var_ident = format_ident!("{}", var_snake);

        // Check if this is a binder variable binding (e.g., x -> binder_1)
        // Binder bindings are just identifiers, not expressions with .clone()
        let binding_str = binding_expr.to_string();
        let is_binder_binding = binding_str.starts_with("binder_")
            && !binding_str.contains('.')
            && !binding_str.contains('(')
            && binding_str.trim() == binding_str; // No whitespace, just the identifier

        if is_binder_binding {
            // For binder variables like `x -> binder_1`, we DO need the explicit binding
            // `let x = binder_1.clone()` so the user variable name is available
            // We need to clone because Binder doesn't implement Copy
            let binder_ident_str = binding_str.trim();
            let binder_ident = format_ident!("{}", binder_ident_str);
            explicit_bindings.push(quote! {
                let #var_ident = #binder_ident.clone()
            });
        } else {
            // Regular variable binding with .clone()
            explicit_bindings.push(quote! {
                let #var_ident = #binding_expr
            });
        }
        bindings.insert(var_name.clone(), var_ident);
    }

    // Also add variables from variable_categories
    for (var_name, _category) in &variable_categories {
        if !bindings.contains_key(var_name) {
            let var_snake = to_snake_case(var_name);
            let var_ident = format_ident!("{}", var_snake);
            bindings.insert(var_name.clone(), var_ident);
        }
    }

    // Combine pattern matching clauses with explicit bindings
    let mut all_clauses = clauses;
    all_clauses.extend(explicit_bindings);

    Some(all_clauses)
}

/// Check if an identifier is a constructor in the theory
fn is_constructor(ident: &Ident, theory: &TheoryDef) -> bool {
    theory.terms.iter().any(|rule| rule.label == *ident)
}

/// Generate RHS for equations where variables are already bound as T (not &Box<T>)
/// This is simpler than generate_equation_rhs which assumes Apply pattern matching
/// Generate RHS for equations using Ident-based bindings (from pattern matching)
/// This is simpler than rewrite RHS generation because variables are bound as Ident, not &Box<T>
fn generate_equation_rhs_from_idents(
    expr: &Expr,
    bindings: &HashMap<String, Ident>,
    theory: &TheoryDef,
) -> TokenStream {
    match expr {
        Expr::Var(var) => {
            // Check if this is a constructor or a variable
            if is_constructor(var, theory) {
                // It's a nullary constructor
                let constructor_category = theory
                    .terms
                    .iter()
                    .find(|r| r.label == *var)
                    .map(|r| &r.category)
                    .expect("Constructor not found in theory");
                quote! { #constructor_category::#var }
            } else {
                // It's a variable - already bound as plain T
                let var_name = var.to_string();
                if let Some(var_ident) = bindings.get(&var_name) {
                    quote! { #var_ident.clone() }
                } else {
                    panic!("Variable {} not found in bindings", var_name);
                }
            }
        },
        Expr::Apply { constructor, args } => {
            let grammar_rule = theory
                .terms
                .iter()
                .find(|r| r.label == *constructor)
                .expect("Constructor not found in theory");
            let category = &grammar_rule.category;

            // Special case: Apply(Constructor, [CollectionPattern{constructor: None}])
            // This means the collection should have the Apply's constructor
            if args.len() == 1 {
                if let Expr::CollectionPattern { constructor: None, elements, rest } = &args[0] {
                    // Treat as CollectionPattern{constructor: Some(constructor)}
                    let normalized = Expr::CollectionPattern {
                        constructor: Some(constructor.clone()),
                        elements: elements.clone(),
                        rest: rest.clone(),
                    };
                    return generate_equation_rhs_from_idents(&normalized, bindings, theory);
                }
            }

            // Check if this constructor has binders
            if !grammar_rule.bindings.is_empty() {
                // This is a binding constructor like PNew
                // Args should be: [binder_var, body_expr]
                // We need to construct a Scope
                if args.len() >= 2 {
                    let binder_expr = generate_equation_rhs_from_idents(&args[0], bindings, theory);
                    let body_expr = generate_equation_rhs_from_idents(&args[1], bindings, theory);

                    return quote! {
                        #category::#constructor(mettail_runtime::Scope::from_parts_unsafe(#binder_expr, Box::new(#body_expr)))
                    };
                } else {
                    panic!("Binding constructor {} requires at least 2 arguments", constructor);
                }
            }

            let arg_tokens: Vec<_> = args
                .iter()
                .map(|arg| {
                    let inner = generate_equation_rhs_from_idents(arg, bindings, theory);
                    quote! { Box::new(#inner) }
                })
                .collect();

            quote! {
                #category::#constructor(#(#arg_tokens),*)
            }
        },
        Expr::CollectionPattern { constructor, elements, rest } => {
            // Reconstruct collection
            let elem_inserts: Vec<_> = elements
                .iter()
                .map(|elem| {
                    let elem_expr = generate_equation_rhs_from_idents(elem, bindings, theory);
                    quote! {
                        bag.insert(#elem_expr);
                    }
                })
                .collect();

            if let Some(cons) = constructor {
                let category = theory
                    .terms
                    .iter()
                    .find(|r| r.label == *cons)
                    .map(|r| &r.category)
                    .expect("Constructor category not found");

                // Check if there's a rest variable to merge in
                let rest_merge = if let Some(rest_var) = rest {
                    let rest_var_str = rest_var.to_string();
                    if let Some(rest_ident) = bindings.get(&rest_var_str) {
                        Some(quote! {
                            for (elem, count) in #rest_ident.iter() {
                                for _ in 0..count {
                                    bag.insert(elem.clone());
                                }
                            }
                        })
                    } else {
                        panic!("Rest variable {} not found in bindings", rest_var_str);
                    }
                } else {
                    None
                };

                quote! {
                    #category::#cons({
                        let mut bag = mettail_runtime::HashBag::new();
                        #(#elem_inserts)*
                        #rest_merge
                        bag
                    })
                }
            } else {
                panic!(
                    "Collection pattern without constructor in RHS: Elements={:?}",
                    elements
                        .iter()
                        .map(|e| format!("{:?}", e))
                        .collect::<Vec<_>>()
                );
            }
        },
        Expr::Subst { .. } => {
            panic!("Substitution expressions are not supported in equation RHS");
        },
    }
}

/// Generate a single equation clause
/// Example: (PPar P Q) == (PPar Q P) generates:
/// eq_proc(p0, p1) <-- proc(p0), if let Proc::PPar(p, q) = p0, let p1 = Proc::PPar(q.clone(), p.clone());
fn generate_equation_clause(equation: &Equation, theory: &TheoryDef) -> Option<TokenStream> {
    // NORMALIZE: If LHS is Apply(Constructor, [CollectionPattern{constructor: None}]),
    // transform to CollectionPattern{constructor: Some(Constructor)}
    let normalized_left = normalize_collection_apply(&equation.left);

    // Determine the category from the LHS
    let category = congruence::extract_category(&normalized_left, theory)?;
    let cat_lower = format_ident!("{}", category.to_string().to_lowercase());
    let eq_rel = format_ident!("eq_{}", category.to_string().to_lowercase());

    // Generate pattern matching for LHS using rewrite rule logic!
    let mut bindings: HashMap<String, Ident> = HashMap::new();
    let lhs_clauses =
        generate_equation_pattern_via_rewrite_logic(&normalized_left, "p0", &mut bindings, theory)?;

    // Generate RHS construction
    // Variables from our explicit bindings are already T, not &Box<T>
    // So we use a simpler RHS generator
    let rhs_construction = generate_equation_rhs_from_idents(&equation.right, &bindings, theory);

    // Generate freshness checks if any
    let freshness_checks = generate_equation_freshness(&equation.conditions, &bindings);

    // Only call normalize() if the category has collection constructors
    let rhs_with_normalize = if category_has_collections(&category, theory) {
        quote! { (#rhs_construction).normalize() }
    } else {
        rhs_construction
    };

    Some(quote! {
        #eq_rel(p0, p1) <--
            #cat_lower(p0),
            #(#lhs_clauses,)*
            #(#freshness_checks,)*
            let p1 = #rhs_with_normalize;
    })
}

/// Normalize Apply(Constructor, [CollectionPattern]) to CollectionPattern{constructor}
/// This handles cases like (PPar {P}) where the collection is wrapped in Apply
fn normalize_collection_apply(expr: &Expr) -> Expr {
    match expr {
        Expr::Apply { constructor, args } if args.len() == 1 => {
            // Check if the single argument is a CollectionPattern with no constructor
            if let Expr::CollectionPattern { constructor: None, elements, rest } = &args[0] {
                // Transform to CollectionPattern with the Apply's constructor
                return Expr::CollectionPattern {
                    constructor: Some(constructor.clone()),
                    elements: elements.clone(),
                    rest: rest.clone(),
                };
            }
            // Not a collection, return as-is
            expr.clone()
        },
        _ => expr.clone(),
    }
}

/// Generate pattern matching code for equation LHS
/// Convert a variable name to snake_case for use in generated code
/// Examples: P -> p, Chan -> chan, MyVar -> my_var
fn to_snake_case(name: &str) -> String {
    if name.is_empty() {
        return name.to_string();
    }

    // If it's a single character, just lowercase it
    if name.len() == 1 {
        return name.to_lowercase();
    }

    // If it's already all lowercase, return as-is
    if name.chars().all(|c| !c.is_uppercase()) {
        return name.to_string();
    }

    // Convert CamelCase or UPPERCASE to snake_case
    let mut result = String::new();
    let mut prev_was_uppercase = false;

    for (i, ch) in name.chars().enumerate() {
        if ch.is_uppercase() {
            // Add underscore before uppercase if not at start and prev was lowercase
            if i > 0 && !prev_was_uppercase {
                result.push('_');
            }
            result.push(ch.to_lowercase().next().unwrap());
            prev_was_uppercase = true;
        } else {
            result.push(ch);
            prev_was_uppercase = false;
        }
    }

    result
}

/// Generate RHS construction code for collection pattern equations
/// Collection variables are bound as T (cloned from iterator), not &Box<T>
#[allow(dead_code)]
fn generate_collection_equation_rhs(
    expr: &Expr,
    bindings: &HashMap<String, Ident>,
    theory: &TheoryDef,
) -> TokenStream {
    match expr {
        Expr::Var(var) => {
            // Check if this is a constructor or a variable
            if is_constructor(var, theory) {
                // It's a nullary constructor
                let constructor_category = theory
                    .terms
                    .iter()
                    .find(|r| r.label == *var)
                    .map(|r| &r.category)
                    .expect("Constructor not found in theory");
                quote! { #constructor_category::#var }
            } else {
                // It's a variable - just clone it (it's already a T value)
                let var_name = var.to_string();
                if let Some(var_ident) = bindings.get(&var_name) {
                    quote! { #var_ident.clone() }
                } else {
                    // Unbound variable
                    quote! { #var }
                }
            }
        },
        _ => {
            // For other expressions, use the regular generator
            // (shouldn't happen for simple collection equations like (PPar {P}) == P)
            generate_equation_rhs(expr, bindings, theory, false)
        },
    }
}

/// Generate RHS construction code
/// `in_constructor` flag indicates if we're inside a constructor argument (affects Box wrapping)
#[allow(dead_code)]
fn generate_equation_rhs(
    expr: &Expr,
    bindings: &HashMap<String, Ident>,
    theory: &TheoryDef,
    in_constructor: bool,
) -> TokenStream {
    match expr {
        Expr::Var(var) => {
            // Check if this is a constructor or a variable
            if is_constructor(var, theory) {
                // It's a nullary constructor - generate the constructor
                let constructor_category = theory
                    .terms
                    .iter()
                    .find(|r| r.label == *var)
                    .map(|r| &r.category)
                    .expect("Constructor not found in theory");

                if in_constructor {
                    quote! { Box::new(#constructor_category::#var) }
                } else {
                    quote! { #constructor_category::#var }
                }
            } else {
                // It's a variable
                let var_name = var.to_string();
                if let Some(var_ident) = bindings.get(&var_name) {
                    // Variables are bound as &Box<T> from Apply pattern matching
                    if in_constructor {
                        // Inside constructor: just clone (keeps it as Box<T>)
                        quote! { #var_ident.clone() }
                    } else {
                        // Top-level: need to dereference to get the inner value
                        // Use .as_ref().clone() to go from &Box<T> to T
                        quote! { #var_ident.as_ref().clone() }
                    }
                } else {
                    // Unbound variable - shouldn't happen
                    quote! { #var }
                }
            }
        },
        Expr::Apply { constructor, args } => {
            let category =
                congruence::extract_category(expr, theory).unwrap_or_else(|| constructor.clone());
            let arg_constructions: Vec<TokenStream> = args
                .iter()
                .map(|arg| {
                    let inner = generate_equation_rhs(arg, bindings, theory, true);
                    // The recursive call with in_constructor=true handles Box wrapping
                    inner
                })
                .collect();

            if in_constructor {
                // We're being called as an argument to another constructor
                // We need to wrap ourselves in Box::new
                quote! {
                    Box::new(#category::#constructor(#(#arg_constructions),*))
                }
            } else {
                // Top-level constructor - no wrapping needed
                quote! {
                    #category::#constructor(#(#arg_constructions),*)
                }
            }
        },
        Expr::Subst { term, var, replacement } => {
            let term_code = generate_equation_rhs(term, bindings, theory, in_constructor);
            let var_name = var.to_string();
            let replacement_code =
                generate_equation_rhs(replacement, bindings, theory, in_constructor);

            quote! {
                mettail_runtime::substitute(
                    &#term_code,
                    &mettail_runtime::Var::new(#var_name.to_string()),
                    &#replacement_code
                )
            }
        },
        Expr::CollectionPattern { elements, rest, .. } => {
            // Build a collection in RHS
            let elem_constructions: Vec<TokenStream> = elements
                .iter()
                .map(|e| generate_equation_rhs(e, bindings, theory, false))
                .collect();

            let coll_type = quote! { mettail_runtime::HashBag };

            if let Some(rest_var) = rest {
                // Merge rest with new elements
                if let Some(rest_binding) = bindings.get(&rest_var.to_string()) {
                    quote! {
                        {
                            let mut bag = (#rest_binding).clone();
                            #(bag.insert(#elem_constructions);)*
                            bag
                        }
                    }
                } else {
                    // Rest variable not bound - shouldn't happen
                    quote! {
                        {
                            let mut bag = #coll_type::new();
                            #(bag.insert(#elem_constructions);)*
                            bag
                        }
                    }
                }
            } else {
                // Just build from elements
                if in_constructor {
                    quote! {
                        Box::new({
                            let mut bag = #coll_type::new();
                            #(bag.insert(#elem_constructions);)*
                            bag
                        })
                    }
                } else {
                    quote! {
                        {
                            let mut bag = #coll_type::new();
                            #(bag.insert(#elem_constructions);)*
                            bag
                        }
                    }
                }
            }
        },
    }
}

/// Generate freshness checks for equation
fn generate_equation_freshness(
    conditions: &[crate::ast::FreshnessCondition],
    bindings: &HashMap<String, Ident>,
) -> Vec<TokenStream> {
    let mut checks = Vec::new();

    for condition in conditions {
        let var_name = condition.var.to_string();
        let term_name = match &condition.term {
            crate::ast::FreshnessTarget::Var(id) => id.to_string(),
            crate::ast::FreshnessTarget::CollectionRest(id) => id.to_string(),
        };

        // Find the bound identifiers for both the binder variable and the term
        let var_ident = bindings
            .get(&var_name)
            .unwrap_or_else(|| panic!("Freshness variable '{}' not found in bindings", var_name));
        let term_ident = bindings
            .get(&term_name)
            .unwrap_or_else(|| panic!("Freshness term '{}' not found in bindings", term_name));

        // Generate: if is_fresh(var, term)
        // The is_fresh function checks if the binder is not free in the term
        checks.push(quote! {
            if is_fresh(&#var_ident, &#term_ident)
        });
    }

    checks
}

/// Check if a category has any collection constructors
fn category_has_collections(category: &Ident, theory: &TheoryDef) -> bool {
    use crate::ast::GrammarItem;

    theory.terms.iter().any(|rule| {
        rule.category == *category
            && rule
                .items
                .iter()
                .any(|item| matches!(item, GrammarItem::Collection { .. }))
    })
}

/// Check if a constructor is nullary (has no non-terminal arguments)
#[allow(dead_code)]
fn is_nullary_constructor(ident: &Ident, theory: &TheoryDef) -> bool {
    theory
        .terms
        .iter()
        .find(|rule| rule.label == *ident)
        .map(|rule| {
            rule.items
                .iter()
                .all(|item| matches!(item, crate::ast::GrammarItem::Terminal(_)))
        })
        .unwrap_or(false)
}
