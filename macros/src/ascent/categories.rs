#![allow(clippy::cmp_owned)]

//! Category exploration and deconstruction rules
//!
//! Generates Ascent rules for:
//! - Category exploration (following rewrite edges)
//! - Term deconstruction (extracting subterms)
//! - Collection projections (extracting elements from collections)
//! - Congruence rules for equality

use crate::ast::{GrammarRule, TheoryDef};
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use syn::Ident;

/// Generate category exploration rules
pub fn generate_category_rules(theory: &TheoryDef) -> TokenStream {
    let mut rules = Vec::new();

    for export in &theory.exports {
        let cat = &export.name;
        let cat_lower = format_ident!("{}", cat.to_string().to_lowercase());
        let rw_rel = format_ident!("rw_{}", cat.to_string().to_lowercase());

        // Expand via rewrites ONLY (not via equality)
        // This prevents exponential term explosion from eq + exploration feedback loop
        rules.push(quote! {
            #cat_lower(c1) <-- #cat_lower(c0), #rw_rel(c0, c1);
        });

        // Generate deconstruction rules for this category
        let deconstruct_rules = generate_deconstruction_rules(cat, theory);
        rules.extend(deconstruct_rules);

        // Generate collection projection population rules for this category
        let projection_rules = generate_collection_projection_population(cat, theory);
        rules.extend(projection_rules);

        // Generate projection seeding rules for this category
        // This adds collection elements to their category relations
        let seeding_rules = generate_projection_seeding_rules(cat, theory);
        rules.extend(seeding_rules);
    }

    quote! {
        #(#rules)*
    }
}

/// Generate deconstruction rules for a category
fn generate_deconstruction_rules(category: &Ident, theory: &TheoryDef) -> Vec<TokenStream> {
    use crate::codegen::has_assign_rule;

    let mut rules = Vec::new();

    // Find all constructors for this category
    let constructors: Vec<&GrammarRule> = theory
        .terms
        .iter()
        .filter(|r| r.category == *category)
        .collect();

    for constructor in constructors {
        if let Some(rule) = generate_deconstruction_for_constructor(category, constructor, theory) {
            rules.push(rule);
        }
    }

    // Generate deconstruction rule for auto-generated Assign constructor
    // Assign has form: Assign(OrdVar, Box<Category>)
    // We need to extract the RHS (Box<Category>) and add it to the category relation
    // Generate for all exported categories that don't have explicit Assign rules
    let has_assign = has_assign_rule(category, theory);
    let is_exported = theory.exports.iter().any(|e| e.name == *category);

    if !has_assign && is_exported {
        let cat_lower = format_ident!("{}", category.to_string().to_lowercase());
        // Extract RHS from Assign and add it to category relation
        rules.push(quote! {
            #cat_lower(rhs.as_ref().clone()) <--
                #cat_lower(t),
                if let #category::Assign(_, rhs) = t;
        });
    }

    rules
}

/// Generate deconstruction rule for a single constructor
fn generate_deconstruction_for_constructor(
    category: &Ident,
    constructor: &GrammarRule,
    _theory: &TheoryDef,
) -> Option<TokenStream> {
    let _cat_lower = format_ident!("{}", category.to_string().to_lowercase());
    let _label = &constructor.label;

    // Check if this constructor has collection fields
    let has_collections = constructor
        .items
        .iter()
        .any(|item| matches!(item, crate::ast::GrammarItem::Collection { .. }));

    if has_collections {
        // Generate deconstruction for collection fields
        return generate_collection_deconstruction(category, constructor);
    }

    // Build parameter map for HOL syntax
    let param_map: std::collections::HashMap<String, Ident> = constructor
        .parameters
        .iter()
        .map(|p| (p.name.to_string(), p.param_type.clone()))
        .collect();

    // Count non-terminal fields (resolving parameter names for HOL syntax)
    let non_terminals: Vec<_> = constructor
        .items
        .iter()
        .enumerate()
        .filter_map(|(i, item)| {
            if let crate::ast::GrammarItem::NonTerminal(ident) = item {
                // HOL syntax: resolve parameter names to their types
                let resolved_ident = param_map
                    .get(&ident.to_string())
                    .cloned()
                    .unwrap_or_else(|| ident.clone());
                Some((i, resolved_ident))
            } else {
                None
            }
        })
        .collect();

    if non_terminals.is_empty() {
        // No fields to deconstruct (e.g., PZero)
        return None;
    }

    // Check if this is a binding constructor
    if !constructor.bindings.is_empty() {
        // Binding constructor - need to unbind
        generate_binding_deconstruction(category, constructor)
    } else {
        // Regular constructor
        generate_regular_deconstruction(category, constructor, &non_terminals)
    }
}

/// Generate deconstruction for constructors with collection fields
///
/// PERFORMANCE NOTE: This eagerly extracts ALL elements from collections as separate facts,
/// which causes exponential fact explosion (O(N*M) where N=terms, M=bag size).
///
/// This is DISABLED because:
/// 1. Collection congruence works via projection relations, not deconstruction
/// 2. Base rewrites are seeded directly from projection relations (see generate_category_rules)
/// 3. Eager deconstruction creates 100s-1000s of redundant facts
/// 4. Results in 50x+ slowdown on moderately complex terms
///
/// Instead: Elements are accessed on-demand via `ppar_contains` projection relation.
fn generate_collection_deconstruction(
    _category: &Ident,
    _constructor: &GrammarRule,
) -> Option<TokenStream> {
    // DISABLED: Use projection relations instead
    None
}

/// Generate collection projection population rules
/// For each constructor with a collection field, generate rules that populate
/// the corresponding "contains" relation.
///
/// Example: For PPar(HashBag<Proc>), generates:
/// ```text
/// ppar_contains(parent.clone(), elem.clone()) <--
///     proc(parent),
///     if let Proc::PPar(ref bag_field) = parent,
///     for (elem, _count) in bag_field.iter();
/// ```
///
/// This creates a database of all collection-element relationships that can be
/// efficiently queried and joined by Ascent.
fn generate_collection_projection_population(
    category: &Ident,
    theory: &TheoryDef,
) -> Vec<TokenStream> {
    let mut rules = Vec::new();

    // Find all constructors for this category
    let constructors: Vec<&GrammarRule> = theory
        .terms
        .iter()
        .filter(|r| r.category == *category)
        .collect();

    for constructor in constructors {
        // Check if this constructor has a collection field
        for item in &constructor.items {
            if let crate::ast::GrammarItem::Collection { element_type, .. } = item {
                // Found a collection field - generate projection rule
                let parent_cat = &constructor.category;
                let parent_cat_lower = format_ident!("{}", parent_cat.to_string().to_lowercase());
                let constructor_label = &constructor.label;
                let _elem_cat = element_type;

                // Generate relation name: <constructor_lowercase>_contains
                let rel_name =
                    format_ident!("{}_contains", constructor_label.to_string().to_lowercase());

                rules.push(quote! {
                    #rel_name(parent.clone(), elem.clone()) <--
                        #parent_cat_lower(parent),
                        if let #parent_cat::#constructor_label(ref bag_field) = parent,
                        for (elem, _count) in bag_field.iter();
                });

                // Only handle one collection per constructor for now
                break;
            }
        }
    }

    rules
}

/// Generate rules to seed category relations from projection relations
/// This allows base rewrites to match on collection elements without eager deconstruction.
///
/// Example: For PPar(HashBag<Proc>) with projection relation ppar_contains(Proc, Proc),
/// generates:
/// ```text
/// proc(elem) <-- ppar_contains(_parent, elem);
/// ```
///
/// This is much more efficient than eager deconstruction because:
/// 1. Elements are only added to proc when they're actually in a ppar_contains fact
/// 2. No redundant facts for elements that appear in multiple collections
/// 3. Lazy evaluation: only computes what's needed
fn generate_projection_seeding_rules(category: &Ident, theory: &TheoryDef) -> Vec<TokenStream> {
    let mut rules = Vec::new();
    let _cat_lower = format_ident!("{}", category.to_string().to_lowercase());

    // Find all constructors for this category that have collections
    let constructors: Vec<&GrammarRule> = theory
        .terms
        .iter()
        .filter(|r| r.category == *category)
        .collect();

    for constructor in constructors {
        // Check if this constructor has a collection field
        for item in &constructor.items {
            if let crate::ast::GrammarItem::Collection { element_type, .. } = item {
                // Found a collection field
                let elem_cat = element_type;
                let elem_cat_lower = format_ident!("{}", elem_cat.to_string().to_lowercase());
                let constructor_label = &constructor.label;

                // Generate relation name: <constructor_lowercase>_contains
                let rel_name =
                    format_ident!("{}_contains", constructor_label.to_string().to_lowercase());

                // Generate seeding rule: elem_cat(elem) <-- contains_rel(_parent, elem);
                rules.push(quote! {
                    #elem_cat_lower(elem) <-- #rel_name(_parent, elem);
                });

                // Only handle one collection per constructor
                break;
            }
        }
    }

    rules
}

/// Generate deconstruction for regular (non-binding) constructor
fn generate_regular_deconstruction(
    category: &Ident,
    constructor: &GrammarRule,
    non_terminals: &[(usize, Ident)],
) -> Option<TokenStream> {
    let cat_lower = format_ident!("{}", category.to_string().to_lowercase());
    let label = &constructor.label;

    // Build parameter map for HOL syntax
    let param_map: std::collections::HashMap<String, Ident> = constructor
        .parameters
        .iter()
        .map(|p| (p.name.to_string(), p.param_type.clone()))
        .collect();

    // Generate field names
    let field_names: Vec<_> = (0..non_terminals.len())
        .map(|i| format_ident!("field_{}", i))
        .collect();

    // Generate subterm facts for each non-terminal field
    // Skip 'Var' and 'Integer' fields as they are built-in types, not exported categories
    let subterm_facts: Vec<TokenStream> = non_terminals
        .iter()
        .zip(&field_names)
        .filter_map(|((_, field_type), field_name)| {
            let field_type_str = field_type.to_string();
            // HOL syntax: resolve parameter names to their types
            let resolved_type = param_map
                .get(&field_type_str)
                .cloned()
                .unwrap_or_else(|| field_type.clone());
            let resolved_type_str = resolved_type.to_string();
            
            // Skip Var and Integer - they are special built-in types, not categories
            if resolved_type_str == "Var" || resolved_type_str == "Integer" {
                return None;
            }
            let field_type_lower = format_ident!("{}", resolved_type_str.to_lowercase());
            // In Ascent pattern matching, fields are &Box<T>
            // Clone the Box to get Box<T>, then use as_ref() to get &T, then clone to get T
            Some(quote! {
                #field_type_lower(#field_name.as_ref().clone())
            })
        })
        .collect();

    // If all fields are Var, skip this constructor entirely
    if subterm_facts.is_empty() {
        return None;
    }

    Some(quote! {
        #(#subterm_facts),* <--
            #cat_lower(t),
            if let #category::#label(#(#field_names),*) = t;
    })
}

/// Generate deconstruction for binding constructor
fn generate_binding_deconstruction(
    category: &Ident,
    constructor: &GrammarRule,
) -> Option<TokenStream> {
    let cat_lower = format_ident!("{}", category.to_string().to_lowercase());
    let label = &constructor.label;

    // For now, handle single binder binding in single body
    let (_binder_idx, body_indices) = &constructor.bindings[0];
    let body_idx = body_indices[0];

    // Get the body category
    let body_cat = match &constructor.items[body_idx] {
        crate::ast::GrammarItem::NonTerminal(cat) => cat,
        _ => return None,
    };
    let body_cat_lower = format_ident!("{}", body_cat.to_string().to_lowercase());

    // Count fields (for pattern matching)
    let field_count = constructor
        .items
        .iter()
        .filter(|item| matches!(item, crate::ast::GrammarItem::NonTerminal(_)))
        .count();

    if field_count == 1 {
        // Only the scope field (body)
        // IMPORTANT: Access unsafe_body field directly to avoid fresh IDs from unbind()
        // The inner moniker Scope has public unsafe_body and unsafe_pattern fields
        // We access via .inner() to get the moniker Scope, then access the field directly
        Some(quote! {
            #body_cat_lower(body_value) <--
                #cat_lower(t),
                if let #category::#label(scope) = t,
                let body_value = scope.inner().unsafe_body.as_ref().clone();
        })
    } else {
        // Has other fields besides the scope
        // Generate field names and collect their categories
        let mut field_names = Vec::new();
        let mut field_cats = Vec::new();
        let mut ast_field_idx = 0usize;

        for (_i, item) in constructor.items.iter().enumerate() {
            if _i == *_binder_idx {
                continue; // Skip binder
            } else if _i == body_idx {
                field_names.push(format_ident!("scope_field"));
            } else if let crate::ast::GrammarItem::NonTerminal(cat) = item {
                let field_name = format!("field_{}", ast_field_idx);
                field_names.push(format_ident!("{}", field_name));
                field_cats.push((ast_field_idx, cat.clone()));
                ast_field_idx += 1;
            }
        }

        // Generate category facts for all non-body fields, then the body
        // Maintain grammar order: non-body fields first, then body
        let mut subterm_facts = Vec::new();
        for (idx, cat) in &field_cats {
            let cat_lower = format_ident!("{}", cat.to_string().to_lowercase());
            let field_name = format_ident!("field_{}", idx);
            subterm_facts.push(quote! { #cat_lower(#field_name.as_ref().clone()) });
        }

        // NOTE: We do NOT add the binder to its category relation here.
        // The binder is a Binder<String> which is not convertible to the category type.
        // Binders only exist inside Scope and are not standalone category values.

        // The body from unsafe_body is T (not Box<T>), so we just clone it directly
        subterm_facts.push(quote! { #body_cat_lower(body.clone()) });

        // IMPORTANT: Access unsafe_body directly instead of unbind() to avoid fresh IDs
        Some(quote! {
            #(#subterm_facts),* <--
                #cat_lower(t),
                if let #category::#label(#(#field_names),*) = t,
                let body = (* scope_field.inner().unsafe_body).clone();
        })
    }
}
