#![allow(clippy::cmp_owned)]

//! Category exploration and deconstruction rules
//!
//! Generates Ascent rules for:
//! - Category exploration (following rewrite edges)
//! - Term deconstruction (extracting subterms)
//! - Collection projections (extracting elements from collections)
//! - Congruence rules for equality

use crate::ast::{grammar::{GrammarRule, GrammarItem}, theory::TheoryDef};
use crate::ast::grammar::TermParam;
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
        
        // Generate rewrite congruence rules for auto-generated Apply/Lam variants
        let congruence_rules = generate_auto_variant_congruence(cat, theory);
        rules.extend(congruence_rules);
    }

    quote! {
        #(#rules)*
    }
}

/// Generate deconstruction rules for a category
fn generate_deconstruction_rules(category: &Ident, theory: &TheoryDef) -> Vec<TokenStream> {
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
    
    // Generate deconstruction rules for auto-generated variants (Apply, Lam, etc.)
    let auto_deconstruct = generate_auto_variant_deconstruction(category, theory);
    rules.extend(auto_deconstruct);

    rules
}

/// Generate deconstruction rules for auto-generated variants (Apply, Lam, MApply, MLam)
fn generate_auto_variant_deconstruction(category: &Ident, theory: &TheoryDef) -> Vec<TokenStream> {
    let mut rules = Vec::new();
    let cat_lower = format_ident!("{}", category.to_string().to_lowercase());
    
    // Get all non-native categories for domain types
    let domain_cats: Vec<_> = theory.exports.iter()
        .filter(|e| e.native_type.is_none())
        .map(|e| &e.name)
        .collect();
    
    for domain in &domain_cats {
        let domain_lower = format_ident!("{}", domain.to_string().to_lowercase());
        
        // ApplyX(lam, arg) - extract both lam (same category) and arg (domain category)
        let apply_variant = format_ident!("Apply{}", domain);
        rules.push(quote! {
            #cat_lower(lam.as_ref().clone()),
            #domain_lower(arg.as_ref().clone()) <--
                #cat_lower(t),
                if let #category::#apply_variant(lam, arg) = t;
        });
        
        // MApplyX(lam, args) - extract lam and all args
        let mapply_variant = format_ident!("MApply{}", domain);
        rules.push(quote! {
            #cat_lower(lam.as_ref().clone()) <--
                #cat_lower(t),
                if let #category::#mapply_variant(lam, _) = t;
        });
        rules.push(quote! {
            #domain_lower(arg.clone()) <--
                #cat_lower(t),
                if let #category::#mapply_variant(_, args) = t,
                for arg in args.iter();
        });
        
        // LamX(scope) - extract body from scope
        let lam_variant = format_ident!("Lam{}", domain);
        rules.push(quote! {
            #cat_lower((* scope.inner().unsafe_body).clone()) <--
                #cat_lower(t),
                if let #category::#lam_variant(scope) = t;
        });
        
        // MLamX(scope) - extract body from scope
        let mlam_variant = format_ident!("MLam{}", domain);
        rules.push(quote! {
            #cat_lower((* scope.inner().unsafe_body).clone()) <--
                #cat_lower(t),
                if let #category::#mlam_variant(scope) = t;
        });
    }
    
    rules
}

/// Generate rewrite congruence rules for auto-generated Apply variants
/// 
/// These rules propagate rewrites through applications:
/// - If lam rewrites in ApplyX(lam, arg), the whole ApplyX rewrites
/// - If arg rewrites in ApplyX(lam, arg), the whole ApplyX rewrites
/// 
/// Note: We do NOT propagate rewrites through lambda bodies (LamX, MLamX)
/// because lambdas are suspended computations - their bodies shouldn't
/// reduce until they are applied.
fn generate_auto_variant_congruence(category: &Ident, theory: &TheoryDef) -> Vec<TokenStream> {
    let mut rules = Vec::new();
    let cat_lower = format_ident!("{}", category.to_string().to_lowercase());
    let rw_cat = format_ident!("rw_{}", category.to_string().to_lowercase());
    
    // Get all non-native categories for domain types
    let domain_cats: Vec<_> = theory.exports.iter()
        .filter(|e| e.native_type.is_none())
        .map(|e| &e.name)
        .collect();
    
    for domain in &domain_cats {
        let rw_domain = format_ident!("rw_{}", domain.to_string().to_lowercase());
        
        // ApplyX(lam, arg) - congruence for lam rewriting
        let apply_variant = format_ident!("Apply{}", domain);
        rules.push(quote! {
            #rw_cat(
                #category::#apply_variant(lam.clone(), arg.clone()),
                #category::#apply_variant(Box::new(lam_new.clone()), arg.clone())
            ) <--
                #cat_lower(t),
                if let #category::#apply_variant(ref lam, ref arg) = t,
                #rw_cat(lam.as_ref().clone(), lam_new);
        });
        
        // ApplyX(lam, arg) - congruence for arg rewriting
        rules.push(quote! {
            #rw_cat(
                #category::#apply_variant(lam.clone(), arg.clone()),
                #category::#apply_variant(lam.clone(), Box::new(arg_new.clone()))
            ) <--
                #cat_lower(t),
                if let #category::#apply_variant(ref lam, ref arg) = t,
                #rw_domain(arg.as_ref().clone(), arg_new);
        });
        
        // MApplyX(lam, args) - congruence for lam rewriting
        let mapply_variant = format_ident!("MApply{}", domain);
        rules.push(quote! {
            #rw_cat(
                #category::#mapply_variant(lam.clone(), args.clone()),
                #category::#mapply_variant(Box::new(lam_new.clone()), args.clone())
            ) <--
                #cat_lower(t),
                if let #category::#mapply_variant(ref lam, ref args) = t,
                #rw_cat(lam.as_ref().clone(), lam_new);
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
        .any(|item| matches!(item, GrammarItem::Collection { .. }));

    if has_collections {
        // Generate deconstruction for collection fields
        return generate_collection_deconstruction(category, constructor);
    }

    // Count non-terminal fields
    let non_terminals: Vec<_> = constructor
        .items
        .iter()
        .enumerate()
        .filter_map(|(i, item)| {
            if let GrammarItem::NonTerminal(ident) = item {
                Some((i, ident))
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
        // Skip multi-binder constructors (they have term_context with MultiAbstraction)
        let is_multi_binder = constructor.term_context.as_ref().map_or(false, |ctx| {
            ctx.iter().any(|p| matches!(p, TermParam::MultiAbstraction { .. }))
        });
        if is_multi_binder {
            continue;
        }
        
        // Check if this constructor has a collection field
        for item in &constructor.items {
            if let GrammarItem::Collection { element_type, .. } = item {
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
        // Skip multi-binder constructors
        let is_multi_binder = constructor.term_context.as_ref().map_or(false, |ctx| {
            ctx.iter().any(|p| matches!(p, TermParam::MultiAbstraction { .. }))
        });
        if is_multi_binder {
            continue;
        }
        
        // Check if this constructor has a collection field
        for item in &constructor.items {
            if let GrammarItem::Collection { element_type, .. } = item {
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
    non_terminals: &[(usize, &Ident)],
) -> Option<TokenStream> {
    let cat_lower = format_ident!("{}", category.to_string().to_lowercase());
    let label = &constructor.label;

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
            // Skip Var and Integer - they are special built-in types, not categories
            if field_type_str == "Var" || field_type_str == "Integer" {
                return None;
            }
            let field_type_lower = format_ident!("{}", field_type_str.to_lowercase());
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
        GrammarItem::NonTerminal(cat) => cat,
        _ => return None,
    };
    let body_cat_lower = format_ident!("{}", body_cat.to_string().to_lowercase());

    // Count fields (for pattern matching)
    let field_count = constructor
        .items
        .iter()
        .filter(|item| matches!(item, GrammarItem::NonTerminal(_)))
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
            } else if let GrammarItem::NonTerminal(cat) = item {
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
