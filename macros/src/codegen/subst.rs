//! Substitution generation for MeTTaIL terms
//!
//! Generates capture-avoiding substitution methods using moniker's BoundTerm trait.
//! For each exported category, we generate a `substitute` method that performs
//! capture-avoiding substitution of variables.

#![allow(clippy::cmp_owned)]

use crate::ast::{grammar::{GrammarItem, GrammarRule, TermParam}, types::{TypeExpr, CollectionType}, theory::{TheoryDef, Export}};
use crate::codegen::{generate_var_label, generate_literal_label, is_var_rule, is_integer_rule};
use crate::utils::has_native_type;
use proc_macro2::TokenStream;
use quote::quote;
use syn::Ident;

pub fn generate_substitution(theory: &TheoryDef) -> TokenStream {
    // Find all categories that appear anywhere in the theory
    // This ensures every exported category gets substitute_X methods for all other categories
    let all_subst_cats = find_all_substitutable_categories(&theory.terms);

    let impls: Vec<TokenStream> = theory
        .exports
        .iter()
        .map(|export| {
            let category = &export.name;

            // Find all rules for this category
            let rules: Vec<&GrammarRule> = theory
                .terms
                .iter()
                .filter(|r| r.category == *category)
                .collect();

            generate_category_substitution(category, &rules, &all_subst_cats, theory)
        })
        .collect();

    quote! {
        #(#impls)*
    }
}

/// Find all categories that appear anywhere in the theory
/// This ensures we generate substitute_X methods for all possible cross-category substitutions
fn find_all_substitutable_categories(rules: &[GrammarRule]) -> std::collections::HashSet<String> {
    let mut cats = std::collections::HashSet::new();

    for rule in rules {
        // Add binder categories
        if !rule.bindings.is_empty() {
            let (binder_idx, _) = &rule.bindings[0];
            if let GrammarItem::Binder { category } = &rule.items[*binder_idx] {
                cats.insert(category.to_string());
            }
        }

        // Add all non-terminal categories (except Var) and collection element types
        for item in &rule.items {
            match item {
                GrammarItem::NonTerminal(cat) => {
                    let cat_str = cat.to_string();
                    if cat_str != "Var" {
                        cats.insert(cat_str);
                    }
                },
                GrammarItem::Collection { element_type, .. } => {
                    cats.insert(element_type.to_string());
                },
                _ => {},
            }
        }

        // Also add the rule's own category to ensure we have all categories
        cats.insert(rule.category.to_string());
    }

    cats
}

fn generate_category_substitution(
    category: &Ident,
    rules: &[&GrammarRule],
    subst_cats: &std::collections::HashSet<String>,
    theory: &TheoryDef,
) -> TokenStream {
    let category_str = category.to_string();

    // For native types, skip substitution generation (native values don't need substitution)
    if has_native_type(category, theory).is_some() {
        return quote! {
            impl #category {
                // Native types don't support substitution - they're values, not variables
            }
        };
    }

    // Generate the main substitute method (same-category)
    let main_method = generate_substitute_method(category, rules, category, theory);

    // Generate cross-category substitute methods for OTHER categories
    let cross_methods: Vec<TokenStream> = subst_cats
        .iter()
        .filter(|cat| **cat != category_str)
        .map(|cat_str| {
            let cat = syn::Ident::new(cat_str, proc_macro2::Span::call_site());
            generate_cross_category_substitute_method(category, rules, &cat)
        })
        .collect();

    let self_method = generate_self_substitute_method(category);
    
    // Generate multi_substitute method for simultaneous same-category substitution
    let multi_method = generate_multi_substitute_method(category, rules);
    
    // Generate cross-category multi_substitute methods
    let cross_multi_methods: Vec<TokenStream> = subst_cats
        .iter()
        .filter(|cat| **cat != category_str)
        .map(|cat_str| {
            let cat = syn::Ident::new(cat_str, proc_macro2::Span::call_site());
            generate_cross_category_multi_substitute_method(category, rules, &cat)
        })
        .collect();

    quote! {
        impl #category {
            #main_method
            #self_method
            #(#cross_methods)*
            #multi_method
            #(#cross_multi_methods)*
        }
    }
}

fn generate_substitute_method(
    category: &Ident,
    rules: &[&GrammarRule],
    _replacement_cat: &Ident,
    theory: &TheoryDef,
) -> TokenStream {
    let mut match_arms: Vec<TokenStream> = rules
        .iter()
        .map(|rule| generate_substitution_arm(category, rule, category))
        .collect();

    // Check if Var variant was auto-generated
    // Skip for native types - they don't have Var variants and don't need substitution
    let has_var_rule = rules.iter().any(|rule| is_var_constructor(rule));
    if !has_var_rule {
        // Only generate auto-var substitution if category doesn't have native type
        // (We already skip substitution entirely for native types in generate_category_substitution,
        // but this is a safety check)
        let var_arm = generate_auto_var_substitution_arm(category, category);
        match_arms.push(var_arm);
    }

    // Check if NumLit variant was auto-generated (for native types)
    let has_integer_rule = rules.iter().any(|rule| is_integer_rule(rule));
    if let Some(native_type) = has_native_type(category, theory) {
        if !has_integer_rule {
            let literal_arm = generate_auto_literal_substitution_arm(category, &native_type);
            match_arms.push(literal_arm);
        }
    }

    quote! {
        pub fn substitute(
            &self,
            var: &mettail_runtime::FreeVar<String>,
            replacement: &Self
        ) -> Self {
            match self {
                #(#match_arms),*
            }
        }
    }
}

/// Generate a cross-category substitute method
fn generate_cross_category_substitute_method(
    category: &Ident,
    rules: &[&GrammarRule],
    binder_cat: &Ident,
) -> TokenStream {
    let method_name = quote::format_ident!("substitute_{}", binder_cat.to_string().to_lowercase());

    let mut match_arms: Vec<TokenStream> = rules
        .iter()
        .map(|rule| generate_substitution_arm(category, rule, binder_cat))
        .collect();

    // Check if Var variant was auto-generated
    let has_var_rule = rules.iter().any(|rule| is_var_constructor(rule));
    if !has_var_rule {
        let var_arm = generate_auto_var_substitution_arm(category, binder_cat);
        match_arms.push(var_arm);
    }

    quote! {
        /// Substitute `replacement` (of type #binder_cat) for free occurrences of `var` in this term
        ///
        /// This is used for cross-category substitution where a binder binds variables
        /// of a different category than the term itself.
        pub fn #method_name(
            &self,
            var: &mettail_runtime::FreeVar<String>,
            replacement: &#binder_cat
        ) -> Self {
            match self {
                #(#match_arms),*
            }
        }
    }
}

/// Generate a self-referential substitute method (substitute_X where X is the category itself)
/// This is just an alias for the main substitute method, needed for uniform cross-category recursion
fn generate_self_substitute_method(category: &Ident) -> TokenStream {
    let method_name = quote::format_ident!("substitute_{}", category.to_string().to_lowercase());
    let multi_method_name = quote::format_ident!("multi_substitute_{}", category.to_string().to_lowercase());

    quote! {
        /// Alias for substitute(), provided for uniform cross-category substitution
        pub fn #method_name(
            &self,
            var: &mettail_runtime::FreeVar<String>,
            replacement: &Self
        ) -> Self {
            self.substitute(var, replacement)
        }
        
        /// Alias for multi_substitute(), provided for uniform cross-category substitution
        pub fn #multi_method_name(
            &self,
            vars: &[&mettail_runtime::FreeVar<String>],
            replacements: &[Self]
        ) -> Self {
            self.multi_substitute(vars, replacements)
        }
    }
}

/// Generate multi_substitute method for simultaneous substitution of multiple variables
///
/// This is the foundation for multi-channel communication rules where we need
/// to substitute multiple variables at once (capture-avoiding for the whole set).
///
/// # Example
/// ```ignore
/// // Given: for(x0<-n0, x1<-n1){p} | n0!(q0) | n1!(q1)
/// // Result: p[NQuote(q0)/x0, NQuote(q1)/x1]
/// body.multi_substitute(&[&x0_var, &x1_var], &[q0_name, q1_name])
/// ```
fn generate_multi_substitute_method(
    category: &Ident,
    rules: &[&GrammarRule],
) -> TokenStream {
    let match_arms: Vec<TokenStream> = rules
        .iter()
        .map(|rule| generate_multi_substitution_arm(category, rule))
        .collect();
    
    // Add auto-generated Var handling if needed
    let has_var_rule = rules.iter().any(|rule| is_var_constructor(rule));
    
    // Generate the correct Var constructor name for this category
    // Convention: first letter + "Var" (e.g., PVar for Proc, NVar for Name)
    let cat_str = category.to_string();
    let var_label = quote::format_ident!("{}Var", cat_str.chars().next().unwrap());
    
    // Add var_arm to match_arms if needed
    let mut all_arms = match_arms;
    if !has_var_rule {
        // Generate the correct Var arms
        all_arms.push(quote! {
            #category::#var_label(mettail_runtime::OrdVar(mettail_runtime::Var::Free(v))) => {
                // Check if this var matches any in the substitution list
                for (i, var) in vars.iter().enumerate() {
                    if v == *var {
                        return replacements[i].clone();
                    }
                }
                self.clone()
            }
        });
        all_arms.push(quote! {
            #category::#var_label(_) => self.clone()
        });
    }
    
    quote! {
        /// Simultaneous substitution of multiple variables
        ///
        /// Replaces vars[i] with replacements[i] for all i, simultaneously.
        /// This is capture-avoiding for the entire set of substitutions.
        ///
        /// # Panics
        /// Panics if vars.len() != replacements.len()
        pub fn multi_substitute(
            &self,
            vars: &[&mettail_runtime::FreeVar<String>],
            replacements: &[Self],
        ) -> Self {
            assert_eq!(vars.len(), replacements.len(), 
                "multi_substitute: vars and replacements must have same length");
            
            if vars.is_empty() {
                return self.clone();
            }
            
            match self {
                #(#all_arms),*
            }
        }
    }
}

/// Generate cross-category multi_substitute method
/// For Proc.multi_substitute_name, substitutes Name replacements for Name variables
fn generate_cross_category_multi_substitute_method(
    category: &Ident,
    rules: &[&GrammarRule],
    replacement_cat: &Ident,
) -> TokenStream {
    let method_name = quote::format_ident!("multi_substitute_{}", replacement_cat.to_string().to_lowercase());
    
    let mut all_arms: Vec<TokenStream> = rules
        .iter()
        .map(|rule| generate_cross_multi_substitution_arm(category, rule, replacement_cat))
        .collect();
    
    // Add auto-generated Var handling if needed  
    let has_var_rule = rules.iter().any(|rule| is_var_constructor(rule));
    let category_str = category.to_string();
    let replacement_str = replacement_cat.to_string();
    
    // Generate the correct Var constructor name
    let var_label = quote::format_ident!("{}Var", category_str.chars().next().unwrap());
    
    if !has_var_rule {
        if category_str == replacement_str {
            // Same category - Var can match and substitute
            all_arms.push(quote! {
                #category::#var_label(mettail_runtime::OrdVar(mettail_runtime::Var::Free(v))) => {
                    for (i, var) in vars.iter().enumerate() {
                        if v == *var {
                            return replacements[i].clone();
                        }
                    }
                    self.clone()
                }
            });
        }
        // Always add a fallback arm for the Var case (just clone)
        all_arms.push(quote! {
            #category::#var_label(_) => self.clone()
        });
    }
    
    quote! {
        /// Cross-category simultaneous substitution
        ///
        /// Replaces vars[i] with replacements[i] for all i, simultaneously.
        /// Used when binder category differs from term category.
        pub fn #method_name(
            &self,
            vars: &[&mettail_runtime::FreeVar<String>],
            replacements: &[#replacement_cat],
        ) -> Self {
            assert_eq!(vars.len(), replacements.len(), 
                "multi_substitute: vars and replacements must have same length");
            
            if vars.is_empty() {
                return self.clone();
            }
            
            match self {
                #(#all_arms),*
            }
        }
    }
}

/// Generate cross-category multi-substitution arm for a constructor
fn generate_cross_multi_substitution_arm(
    category: &Ident,
    rule: &GrammarRule,
    replacement_cat: &Ident,
) -> TokenStream {
    let label = &rule.label;
    let method_name = quote::format_ident!("multi_substitute_{}", replacement_cat.to_string().to_lowercase());
    let category_str = category.to_string();
    let replacement_cat_str = replacement_cat.to_string();
    
    // Check if this is a multi-binder constructor
    let is_multi_binder = rule.term_context.as_ref().map_or(false, |ctx| {
        ctx.iter().any(|p| matches!(p, TermParam::MultiAbstraction { .. }))
    });
    
    if is_multi_binder {
        // Multi-binder: filter out shadowed vars and recurse
        // Find binder category and collection element category
        let (binder_cat, collection_elem_cat) = rule.term_context.as_ref()
            .map(|ctx| {
                let mut binder_cat = None;
                let mut coll_elem = None;
                for p in ctx {
                    match p {
                        TermParam::MultiAbstraction { ty, .. } => {
                            if let TypeExpr::Arrow { domain, .. } = ty {
                                if let TypeExpr::MultiBinder(elem_type) = domain.as_ref() {
                                    if let TypeExpr::Base(cat) = elem_type.as_ref() {
                                        binder_cat = Some(cat.to_string());
                                    }
                                }
                            }
                        }
                        TermParam::Simple { ty, .. } => {
                            if let TypeExpr::Collection { element, .. } = ty {
                                if let TypeExpr::Base(elem) = element.as_ref() {
                                    coll_elem = Some(elem.to_string());
                                }
                            }
                        }
                        _ => {}
                    }
                }
                (binder_cat, coll_elem)
            })
            .unwrap_or((None, None));
        
        // Determine method for collection elements:
        // If element type matches replacement type, use same-category multi_substitute
        // Otherwise use cross-category multi_substitute_X
        let coll_method = if let Some(elem_cat) = &collection_elem_cat {
            if *elem_cat == replacement_cat_str {
                // Same as replacement - use same-category method
                quote! { multi_substitute }
            } else {
                // Different - use cross-category method
                quote! { #method_name }
            }
        } else {
            quote! { #method_name }
        };
        
        let should_filter = binder_cat.as_ref().map_or(false, |b| *b == replacement_cat_str);
        
        if should_filter {
            return quote! {
                #category::#label(field_0, scope) => {
                    let binders = &scope.inner().unsafe_pattern;
                    let body = &scope.inner().unsafe_body;
                    
                    let (filtered_vars, filtered_repls): (Vec<_>, Vec<_>) = vars.iter()
                        .zip(replacements.iter())
                        .filter(|(v, _)| !binders.iter().any(|b| &b.0 == **v))
                        .map(|(v, r)| (*v, r.clone()))
                        .unzip();
                    
                    let subst_field_0: Vec<_> = field_0.iter()
                        .map(|elem| elem.#coll_method(vars, replacements))
                        .collect();
                    
                    if filtered_vars.is_empty() {
                        #category::#label(subst_field_0, scope.clone())
                    } else {
                        let filtered_var_refs: Vec<&mettail_runtime::FreeVar<String>> = filtered_vars.iter().map(|v| *v).collect();
                        let subst_body = (**body).#method_name(&filtered_var_refs[..], &filtered_repls);
                        let new_scope = mettail_runtime::Scope::new(
                            binders.clone(),
                            Box::new(subst_body),
                        );
                        #category::#label(subst_field_0, new_scope)
                    }
                }
            };
        } else {
            // Different category binder - no shadowing
            return quote! {
                #category::#label(field_0, scope) => {
                    let binders = &scope.inner().unsafe_pattern;
                    let body = &scope.inner().unsafe_body;
                    
                    let subst_field_0: Vec<_> = field_0.iter()
                        .map(|elem| elem.#coll_method(vars, replacements))
                        .collect();
                    let subst_body = (**body).#method_name(vars, replacements);
                    let new_scope = mettail_runtime::Scope::new(
                        binders.clone(),
                        Box::new(subst_body),
                    );
                    #category::#label(subst_field_0, new_scope)
                }
            };
        }
    }
    
    // Check if this is a single-binder constructor (either new or old style)
    let has_binder = !rule.bindings.is_empty() || rule.term_context.as_ref().map_or(false, |ctx| {
        ctx.iter().any(|p| matches!(p, TermParam::Abstraction { .. }))
    });
    
    if has_binder {
        // Get binder category
        let binder_cat = rule.term_context.as_ref()
            .and_then(|ctx| {
                ctx.iter().find_map(|p| {
                    if let TermParam::Abstraction { ty, .. } = p {
                        if let TypeExpr::Arrow { domain, .. } = ty {
                            if let TypeExpr::Base(cat) = domain.as_ref() {
                                return Some(cat.to_string());
                            }
                        }
                    }
                    None
                })
            })
            .or_else(|| {
                rule.bindings.first()
                    .and_then(|(binder_idx, _)| {
                        if let GrammarItem::Binder { category } = &rule.items[*binder_idx] {
                            Some(category.to_string())
                        } else {
                            None
                        }
                    })
            });
        
        // Count fields before the scope
        let binder_idx = rule.bindings.first().map(|(idx, _)| *idx).unwrap_or(0);
        let pre_scope_fields: Vec<_> = rule.items.iter().take(binder_idx)
            .filter(|item| matches!(item, GrammarItem::NonTerminal(_) | GrammarItem::Collection { .. }))
            .collect();
        
        let has_pre_scope_fields = !pre_scope_fields.is_empty();
        let should_filter = binder_cat.as_ref().map_or(false, |b| *b == replacement_cat_str);
        
        if has_pre_scope_fields {
            let field_names: Vec<_> = (0..pre_scope_fields.len())
                .map(|i| quote::format_ident!("field_{}", i))
                .collect();
            
            if should_filter {
                return quote! {
                    #category::#label(#(#field_names,)* scope) => {
                        let binder = &scope.inner().unsafe_pattern;
                        let body = &scope.inner().unsafe_body;
                        
                        let (filtered_vars, filtered_repls): (Vec<_>, Vec<_>) = vars.iter()
                            .zip(replacements.iter())
                            .filter(|(v, _)| binder.0 != ***v)
                            .map(|(v, r)| (*v, r.clone()))
                            .unzip();
                        
                        if filtered_vars.is_empty() {
                            self.clone()
                        } else {
                            let subst_body = (**body).#method_name(&filtered_vars[..], &filtered_repls);
                            let new_scope = mettail_runtime::Scope::new(
                                binder.clone(),
                                Box::new(subst_body),
                            );
                            #category::#label(#(#field_names.clone(),)* new_scope)
                        }
                    }
                };
            } else {
                // Different category binder - no shadowing
                return quote! {
                    #category::#label(#(#field_names,)* scope) => {
                        let binder = &scope.inner().unsafe_pattern;
                        let body = &scope.inner().unsafe_body;
                        let subst_body = (**body).#method_name(vars, replacements);
                        let new_scope = mettail_runtime::Scope::new(
                            binder.clone(),
                            Box::new(subst_body),
                        );
                        #category::#label(#(#field_names.clone(),)* new_scope)
                    }
                };
            }
        } else {
            // No pre-scope fields (just scope)
            if should_filter {
                return quote! {
                    #category::#label(scope) => {
                        let binder = &scope.inner().unsafe_pattern;
                        let body = &scope.inner().unsafe_body;
                        
                        let (filtered_vars, filtered_repls): (Vec<_>, Vec<_>) = vars.iter()
                            .zip(replacements.iter())
                            .filter(|(v, _)| binder.0 != ***v)
                            .map(|(v, r)| (*v, r.clone()))
                            .unzip();
                        
                        if filtered_vars.is_empty() {
                            self.clone()
                        } else {
                            let subst_body = (**body).#method_name(&filtered_vars[..], &filtered_repls);
                            let new_scope = mettail_runtime::Scope::new(
                                binder.clone(),
                                Box::new(subst_body),
                            );
                            #category::#label(new_scope)
                        }
                    }
                };
            } else {
                return quote! {
                    #category::#label(scope) => {
                        let binder = &scope.inner().unsafe_pattern;
                        let body = &scope.inner().unsafe_body;
                        let subst_body = (**body).#method_name(vars, replacements);
                        let new_scope = mettail_runtime::Scope::new(
                            binder.clone(),
                            Box::new(subst_body),
                        );
                        #category::#label(new_scope)
                    }
                };
            }
        }
    }
    
    // Check for collection fields
    let has_collection = rule.items.iter().any(|item| {
        matches!(item, GrammarItem::Collection { .. })
    });
    
    if has_collection {
        return quote! {
            #category::#label(bag) => {
                let mut new_bag = mettail_runtime::HashBag::new();
                for (elem, count) in bag.iter() {
                    let subst_elem = elem.#method_name(vars, replacements);
                    for _ in 0..count {
                        new_bag.insert(subst_elem.clone());
                    }
                }
                #category::#label(new_bag)
            }
        };
    }
    
    // Regular constructor - recursively substitute in all fields
    let non_terminals: Vec<_> = rule.items.iter().enumerate()
        .filter_map(|(i, item)| match item {
            GrammarItem::NonTerminal(nt) => Some((i, nt.clone())),
            _ => None,
        })
        .collect();
    
    if non_terminals.is_empty() {
        return quote! {
            #category::#label => self.clone()
        };
    }
    
    let field_names: Vec<_> = non_terminals.iter()
        .map(|(i, _)| quote::format_ident!("field_{}", i))
        .collect();
    
    let field_substs: Vec<TokenStream> = non_terminals.iter()
        .zip(field_names.iter())
        .map(|((_, nt), field_name)| {
            let nt_str = nt.to_string();
            if nt_str == "Var" {
                quote! { #field_name.clone() }
            } else {
                quote! { Box::new((**#field_name).#method_name(vars, replacements)) }
            }
        })
        .collect();
    
    quote! {
        #category::#label(#(#field_names),*) => {
            #category::#label(#(#field_substs),*)
        }
    }
}

/// Generate a multi-substitution match arm for a single constructor
fn generate_multi_substitution_arm(
    category: &Ident,
    rule: &GrammarRule,
) -> TokenStream {
    let label = &rule.label;
    
    // Check if this is a multi-binder constructor
    let is_multi_binder = rule.term_context.as_ref().map_or(false, |ctx| {
        ctx.iter().any(|p| matches!(p, TermParam::MultiAbstraction { .. }))
    });
    
    if is_multi_binder {
        return generate_multi_binder_multi_subst_arm(category, rule);
    }
    
    // Check if this is a single-binder constructor  
    if !rule.bindings.is_empty() {
        return generate_binder_multi_subst_arm(category, rule);
    }
    
    // Check for collection fields
    let has_collection = rule.items.iter().any(|item| {
        matches!(item, GrammarItem::Collection { .. })
    });
    
    if has_collection {
        return generate_collection_multi_subst_arm(category, rule);
    }
    
    // Regular constructor - recursively substitute in all fields
    generate_regular_multi_subst_arm(category, rule)
}

/// Generate multi-subst arm for regular (non-binding) constructor
fn generate_regular_multi_subst_arm(
    category: &Ident,
    rule: &GrammarRule,
) -> TokenStream {
    let label = &rule.label;
    let category_str = category.to_string();
    
    let non_terminals: Vec<_> = rule.items.iter().enumerate()
        .filter_map(|(i, item)| match item {
            GrammarItem::NonTerminal(nt) => Some((i, nt.clone())),
            _ => None,
        })
        .collect();
    
    if non_terminals.is_empty() {
        // Nullary constructor
        return quote! {
            #category::#label => self.clone()
        };
    }
    
    let field_names: Vec<_> = non_terminals.iter()
        .map(|(i, _)| quote::format_ident!("field_{}", i))
        .collect();
    
    let field_substs: Vec<TokenStream> = non_terminals.iter()
        .zip(field_names.iter())
        .map(|((_, nt), field_name)| {
            let nt_str = nt.to_string();
            if nt_str == "Var" {
                quote! { #field_name.clone() }
            } else if nt_str == category_str {
                // Same category - use multi_substitute
                quote! { Box::new((**#field_name).multi_substitute(vars, replacements)) }
            } else {
                // Different category - use multi_substitute_<category>
                let method = quote::format_ident!("multi_substitute_{}", category_str.to_lowercase());
                quote! { Box::new((**#field_name).#method(vars, replacements)) }
            }
        })
        .collect();
    
    quote! {
        #category::#label(#(#field_names),*) => {
            #category::#label(#(#field_substs),*)
        }
    }
}

/// Generate multi-subst arm for constructor with single binder
fn generate_binder_multi_subst_arm(
    category: &Ident,
    rule: &GrammarRule,
) -> TokenStream {
    let label = &rule.label;
    
    // For same-category substitution (Proc::multi_substitute(&[Proc])):
    // - We substitute Proc values for variables in Proc terms
    // - When we encounter a binder of a DIFFERENT category (e.g., Name binder in PInput),
    //   we DON'T filter by that binder since it's a different namespace
    // - We always call multi_substitute (same category) on the body
    //
    // The key insight: same-category substitution only substitutes for variables 
    // of the SAME category. A Name binder doesn't shadow Proc variables.
    
    // Count non-terminal fields before the scope (binder fields)
    let binder_idx = rule.bindings.first().map(|(idx, _)| *idx).unwrap_or(0);
    let pre_scope_fields: Vec<_> = rule.items.iter().take(binder_idx)
        .filter(|item| matches!(item, GrammarItem::NonTerminal(_) | GrammarItem::Collection { .. }))
        .collect();
    
    let has_pre_scope_fields = !pre_scope_fields.is_empty();
    
    // Find the binder category to check if we need to filter
    let binder_cat = rule.term_context.as_ref()
        .and_then(|ctx| {
            ctx.iter().find_map(|p| {
                if let TermParam::Abstraction { ty, .. } = p {
                    if let TypeExpr::Arrow { domain, .. } = ty {
                        if let TypeExpr::Base(cat) = domain.as_ref() {
                            return Some(cat.clone());
                        }
                    }
                }
                None
            })
        })
        .or_else(|| {
            rule.bindings.first()
                .and_then(|(binder_idx, _)| {
                    if let GrammarItem::Binder { category } = &rule.items[*binder_idx] {
                        Some(category.clone())
                    } else {
                        None
                    }
                })
        });
    
    // For same-category substitution:
    // - If binder is same category, we need to check for shadowing
    // - If binder is different category, we DON'T filter (different namespace)
    let category_str = category.to_string();
    let same_category_binder = binder_cat.as_ref()
        .map_or(true, |b| b.to_string() == category_str);
    
    if has_pre_scope_fields {
        // Constructor has fields before the scope (e.g., PInput(name, scope))
        let field_names: Vec<_> = (0..pre_scope_fields.len())
            .map(|i| quote::format_ident!("field_{}", i))
            .collect();
        
        if same_category_binder {
            // Same category binder - need to check for shadowing
            quote! {
                #category::#label(#(#field_names,)* scope) => {
                    let binder = &scope.inner().unsafe_pattern;
                    let body = &scope.inner().unsafe_body;
                    
                    // Filter out any vars that are shadowed by this binder
                    let (filtered_vars, filtered_repls): (Vec<_>, Vec<_>) = vars.iter()
                        .zip(replacements.iter())
                        .filter(|(v, _)| binder.0 != ***v)
                        .map(|(v, r)| (*v, r.clone()))
                        .unzip();
                    
                    if filtered_vars.is_empty() {
                        self.clone()
                    } else {
                        let subst_body = (**body).multi_substitute(&filtered_vars[..], &filtered_repls);
                        let new_scope = mettail_runtime::Scope::new(
                            binder.clone(),
                            Box::new(subst_body),
                        );
                        #category::#label(#(#field_names.clone(),)* new_scope)
                    }
                }
            }
        } else {
            // Different category binder - no shadowing possible, just recurse
            quote! {
                #category::#label(#(#field_names,)* scope) => {
                    let binder = &scope.inner().unsafe_pattern;
                    let body = &scope.inner().unsafe_body;
                    let subst_body = (**body).multi_substitute(vars, replacements);
                    let new_scope = mettail_runtime::Scope::new(
                        binder.clone(),
                        Box::new(subst_body),
                    );
                    #category::#label(#(#field_names.clone(),)* new_scope)
                }
            }
        }
    } else {
        // Constructor is just a scope (e.g., PNew(scope))
        if same_category_binder {
            quote! {
                #category::#label(scope) => {
                    let binder = &scope.inner().unsafe_pattern;
                    let body = &scope.inner().unsafe_body;
                    
                    let (filtered_vars, filtered_repls): (Vec<_>, Vec<_>) = vars.iter()
                        .zip(replacements.iter())
                        .filter(|(v, _)| binder.0 != ***v)
                        .map(|(v, r)| (*v, r.clone()))
                        .unzip();
                    
                    if filtered_vars.is_empty() {
                        self.clone()
                    } else {
                        let subst_body = (**body).multi_substitute(&filtered_vars[..], &filtered_repls);
                        let new_scope = mettail_runtime::Scope::new(
                            binder.clone(),
                            Box::new(subst_body),
                        );
                        #category::#label(new_scope)
                    }
                }
            }
        } else {
            quote! {
                #category::#label(scope) => {
                    let binder = &scope.inner().unsafe_pattern;
                    let body = &scope.inner().unsafe_body;
                    let subst_body = (**body).multi_substitute(vars, replacements);
                    let new_scope = mettail_runtime::Scope::new(
                        binder.clone(),
                        Box::new(subst_body),
                    );
                    #category::#label(new_scope)
                }
            }
        }
    }
}

/// Generate multi-subst arm for constructor with multi-binder (Vec<Binder>)
fn generate_multi_binder_multi_subst_arm(
    category: &Ident,
    rule: &GrammarRule,
) -> TokenStream {
    let label = &rule.label;
    let category_str = category.to_string();
    
    // Find the binder category and collection element type from term_context
    let (binder_cat, collection_elem_cat) = rule.term_context.as_ref()
        .map(|ctx| {
            let mut binder_cat = None;
            let mut coll_elem = None;
            for p in ctx {
                match p {
                    TermParam::MultiAbstraction { ty, .. } => {
                        if let TypeExpr::Arrow { domain, .. } = ty {
                            if let TypeExpr::MultiBinder(elem_type) = domain.as_ref() {
                                if let TypeExpr::Base(cat) = elem_type.as_ref() {
                                    binder_cat = Some(cat.clone());
                                }
                            }
                        }
                    }
                    TermParam::Simple { ty, .. } => {
                        if let TypeExpr::Collection { element, .. } = ty {
                            if let TypeExpr::Base(elem) = element.as_ref() {
                                coll_elem = Some(elem.clone());
                            }
                        }
                    }
                    _ => {}
                }
            }
            (binder_cat, coll_elem)
        })
        .unwrap_or((None, None));
    
    // Determine the method to call on the body
    // For same-category multi_substitute: if binder is Name, body contains Proc vars being substituted
    // The body is of type Proc, so we call Proc::multi_substitute
    let body_method = quote! { multi_substitute };
    
    // Determine the method to call on collection elements
    // If collection elements are Name and we're in Proc::multi_substitute, 
    // we need Name::multi_substitute_proc to propagate substitution into NQuote
    let collection_method = if let Some(elem_cat) = &collection_elem_cat {
        let elem_str = elem_cat.to_string();
        if elem_str == category_str {
            quote! { multi_substitute }
        } else {
            let method = quote::format_ident!("multi_substitute_{}", category_str.to_lowercase());
            quote! { #method }
        }
    } else {
        quote! { multi_substitute }
    };
    
    // Check if binder category matches this category (affects shadowing)
    let binder_cat_str = binder_cat.as_ref().map(|c| c.to_string());
    let should_filter = binder_cat_str.as_ref().map_or(false, |b| *b == category_str);
    
    if should_filter {
        // Binder is same category - need to filter out shadowed vars
        quote! {
            #category::#label(field_0, scope) => {
                let binders = &scope.inner().unsafe_pattern;
                let body = &scope.inner().unsafe_body;
                
                // Filter out any vars that are shadowed by any binder
                let (filtered_vars, filtered_repls): (Vec<_>, Vec<_>) = vars.iter()
                    .zip(replacements.iter())
                    .filter(|(v, _)| !binders.iter().any(|b| &b.0 == **v))
                    .map(|(v, r)| (*v, r.clone()))
                    .unzip();
                
                // Also substitute in the collection field
                let subst_field_0: Vec<_> = field_0.iter()
                    .map(|elem| elem.#collection_method(vars, replacements))
                    .collect();
                
                if filtered_vars.is_empty() {
                    // All vars are shadowed in body
                    #category::#label(subst_field_0, scope.clone())
                } else {
                    let filtered_var_refs: Vec<&mettail_runtime::FreeVar<String>> = filtered_vars.iter().map(|v| *v).collect();
                    let subst_body = (**body).#body_method(&filtered_var_refs[..], &filtered_repls);
                    let new_scope = mettail_runtime::Scope::new(
                        binders.clone(),
                        Box::new(subst_body),
                    );
                    #category::#label(subst_field_0, new_scope)
                }
            }
        }
    } else {
        // Binder is different category - no shadowing, just substitute in body and collection
        quote! {
            #category::#label(field_0, scope) => {
                let binders = &scope.inner().unsafe_pattern;
                let body = &scope.inner().unsafe_body;
                
                let subst_field_0: Vec<_> = field_0.iter()
                    .map(|elem| elem.#collection_method(vars, replacements))
                    .collect();
                let subst_body = (**body).#body_method(vars, replacements);
                let new_scope = mettail_runtime::Scope::new(
                    binders.clone(),
                    Box::new(subst_body),
                );
                #category::#label(subst_field_0, new_scope)
            }
        }
    }
}

/// Generate multi-subst arm for collection constructor
fn generate_collection_multi_subst_arm(
    category: &Ident,
    rule: &GrammarRule,
) -> TokenStream {
    let label = &rule.label;
    
    // Collection: substitute in each element
    quote! {
        #category::#label(bag) => {
            let mut new_bag = mettail_runtime::HashBag::new();
            for (elem, count) in bag.iter() {
                let subst_elem = elem.multi_substitute(vars, replacements);
                for _ in 0..count {
                    new_bag.insert(subst_elem.clone());
                }
            }
            #category::#label(new_bag)
        }
    }
}

/// Generate a substitution match arm for a single constructor
fn generate_substitution_arm(
    category: &Ident,
    rule: &GrammarRule,
    replacement_cat: &Ident,
) -> TokenStream {
    let label = &rule.label;

    // Check if this is a variable constructor
    if is_var_constructor(rule) {
        // Variable constructors only substitute if replacement category matches
        if category == replacement_cat {
            // Special case: EVar(v) - check if v matches the variable to substitute
            return quote! {
                #category::#label(mettail_runtime::OrdVar(mettail_runtime::Var::Free(v))) if v == var => {
                    // This free variable matches - replace it
                    replacement.clone()
                }
                #category::#label(_) => {
                    // Different variable or bound variable - keep as is
                    self.clone()
                }
            };
        } else {
            // Different category - can't substitute
            return quote! {
                #category::#label(_) => self.clone()
            };
        }
    }

    // Check if this has bindings (uses Scope)
    if !rule.bindings.is_empty() {
        // Check if this is a multi-binder rule (uses term_context with MultiAbstraction)
        let is_multi_binder = rule.term_context.as_ref().map_or(false, |ctx| {
            ctx.iter().any(|p| matches!(p, TermParam::MultiAbstraction { .. }))
        });
        
        if is_multi_binder {
            // Multi-binder substitution needs special handling
            return generate_multi_binder_substitution_arm(category, rule, replacement_cat);
        }
        
        return generate_scope_substitution_arm(category, rule, replacement_cat);
    }

    // Regular constructor - substitute in all subterms
    generate_regular_substitution_arm(category, rule, replacement_cat)
}

/// Check if a rule is a variable constructor (Var category)
fn is_var_constructor(rule: &GrammarRule) -> bool {
    rule.items.len() == 1
        && matches!(&rule.items[0], GrammarItem::NonTerminal(ident) if ident.to_string() == "Var")
}

/// Generate substitution match arm for an auto-generated Var variant
fn generate_auto_var_substitution_arm(category: &Ident, replacement_cat: &Ident) -> TokenStream {
    // Generate Var label: first letter + "Var"
    let var_label = generate_var_label(category);

    let category_str = category.to_string();
    let replacement_cat_str = replacement_cat.to_string();

    if category_str == replacement_cat_str {
        // Same category - can substitute
        quote! {
            #category::#var_label(mettail_runtime::OrdVar(mettail_runtime::Var::Free(v))) if v == var => {
                // This free variable matches - replace it
                replacement.clone()
            }
            #category::#var_label(_) => {
                // Different variable or bound variable - keep as is
                self.clone()
            }
        }
    } else {
        // Different category - can't substitute
        quote! {
            #category::#var_label(_) => self.clone()
        }
    }
}

/// Generate substitution match arm for an auto-generated literal variant (NumLit, etc.)
/// Literals don't contain variables, so substitution just returns self.
fn generate_auto_literal_substitution_arm(category: &Ident, native_type: &syn::Type) -> TokenStream {
    let literal_label = generate_literal_label(native_type);

    quote! {
        #category::#literal_label(_) => self.clone()
    }
}

/// Generate substitution for a constructor with Scope (binder)
fn generate_scope_substitution_arm(
    category: &Ident,
    rule: &GrammarRule,
    replacement_cat: &Ident,
) -> TokenStream {
    let label = &rule.label;

    let (binder_idx, body_indices) = &rule.bindings[0];
    let body_idx = body_indices[0];

    // Get the binder category to determine substitution type
    let binder_cat = match &rule.items[*binder_idx] {
        GrammarItem::Binder { category } => category,
        _ => panic!("Binding index doesn't point to a Binder"),
    };

    let body_cat = match &rule.items[body_idx] {
        GrammarItem::NonTerminal(cat) => cat,
        _ => panic!("Body index doesn't point to a NonTerminal"),
    };

    // Generate pattern bindings for all fields (in grammar order)
    // Track which position is the scope
    let mut field_bindings = Vec::new();
    let mut scope_field_idx = None;

    for (i, item) in rule.items.iter().enumerate() {
        if i == *binder_idx {
            // Skip binder - it's part of the Scope
            continue;
        }

        match item {
            GrammarItem::NonTerminal(_) | GrammarItem::Binder { .. } => {
                let field_name = if i == body_idx {
                    scope_field_idx = Some(field_bindings.len());
                    quote::format_ident!("scope")
                } else {
                    quote::format_ident!("field_{}", field_bindings.len())
                };
                field_bindings.push(field_name);
            },
            GrammarItem::Collection { .. } => {
                // Collection gets a field binding
                let field_name = quote::format_ident!("field_{}", field_bindings.len());
                field_bindings.push(field_name);
            },
            GrammarItem::Terminal(_) => {},
        }
    }

    let scope_idx = scope_field_idx.expect("Should have found scope field");

    // Check if we need to recurse into the body
    // We only recurse if the replacement category matches the binder category
    let binder_cat_str = binder_cat.to_string();
    let replacement_cat_str = replacement_cat.to_string();

    if binder_cat_str == replacement_cat_str {
        // The replacement type matches what this Scope binds
        // So we need to check for shadowing and potentially substitute in the body

        // Determine the method name to call on the body
        let body_cat_str = body_cat.to_string();
        let subst_method = if body_cat_str == replacement_cat_str {
            // Same category - use plain substitute
            quote! { substitute }
        } else {
            // Cross-category - use substitute_X
            let method_name =
                quote::format_ident!("substitute_{}", replacement_cat_str.to_lowercase());
            quote! { #method_name }
        };

        // Generate field reconstruction - substitute in scope, clone others
        let field_reconstructions: Vec<TokenStream> = field_bindings.iter().enumerate().map(|(i, field_name)| {
            if i == scope_idx {
                quote! { new_scope.clone() }
            } else {
                // For non-scope fields, we should also substitute!
                // Find the corresponding field in rule.items (skipping binder)
                let field_item = rule.items.iter()
                    .enumerate()
                    .filter(|(idx, item)| {
                        *idx != *binder_idx &&
                        (matches!(item, GrammarItem::NonTerminal(_)) || matches!(item, GrammarItem::Collection { .. }))
                    })
                    .nth(i)
                    .map(|(_, item)| item);

                match field_item {
                    Some(GrammarItem::NonTerminal(field_cat)) => {
                        let field_cat_str = field_cat.to_string();
                        let subst_method = if field_cat_str == replacement_cat_str {
                            quote! { substitute }
                        } else {
                            let method_name = quote::format_ident!("substitute_{}", replacement_cat_str.to_lowercase());
                            quote! { #method_name }
                        };
                        quote! { Box::new((**#field_name).#subst_method(var, replacement)) }
                    }
                    Some(GrammarItem::Collection { element_type, coll_type, .. }) => {
                        let elem_cat_str = element_type.to_string();
                        let subst_method = if elem_cat_str == replacement_cat_str {
                            quote! { substitute }
                        } else {
                            let method_name = quote::format_ident!("substitute_{}", replacement_cat_str.to_lowercase());
                            quote! { #method_name }
                        };

                        // Map over collection elements
                        match coll_type {
                            CollectionType::HashBag => {
                                // Use flatten helper to automatically flatten nested collections
                                let helper_name = quote::format_ident!("insert_into_{}", rule.label.to_string().to_lowercase());
                                quote! {
                                    {
                                        let mut bag = mettail_runtime::HashBag::new();
                                        for (elem, count) in #field_name.iter() {
                                            let subst_elem = elem.#subst_method(var, replacement);
                                            for _ in 0..count {
                                                // Use flatten helper: auto-flattens if subst_elem is nested collection
                                                #category::#helper_name(&mut bag, subst_elem.clone());
                                            }
                                        }
                                        bag
                                    }
                                }
                            }
                            CollectionType::HashSet => {
                                quote! {
                                    #field_name.iter().map(|elem| {
                                        elem.#subst_method(var, replacement)
                                    }).collect()
                                }
                            }
                            CollectionType::Vec => {
                                quote! {
                                    #field_name.iter().map(|elem| {
                                        elem.#subst_method(var, replacement)
                                    }).collect()
                                }
                            }
                        }
                    }
                    _ => {
                        // Shouldn't happen, but clone as fallback
                        quote! { #field_name.clone() }
                    }
                }
            }
        }).collect();

        quote! {
            #category::#label(#(#field_bindings),*) => {
                // Use unsafe_pattern and unsafe_body to avoid generating fresh IDs for comparison
                let binder = &scope.inner().unsafe_pattern;
                let body = &scope.inner().unsafe_body;

                // Check if the binder shadows our variable
                if binder.0 == *var {
                    // The scope binds the same variable we're substituting
                    // So the variable is not free in the body - no substitution needed
                    self.clone()
                } else {
                    // The scope doesn't shadow our variable - substitute in the body
                    let subst_body = (**body).#subst_method(var, replacement);
                    // Use Scope::new to properly handle variable binding (capture-avoiding)
                    let new_scope = mettail_runtime::Scope::new(binder.clone(), Box::new(subst_body));

                    // Reconstruct with updated scope and cloned other fields
                    #category::#label(#(#field_reconstructions),*)
                }
            }
        }
    } else {
        // The replacement type doesn't match what this Scope binds
        // So variables in the body won't be affected - just clone
        quote! {
            #category::#label(#(#field_bindings),*) => {
                // Cross-category mismatch: this Scope binds #binder_cat, but we're substituting #replacement_cat
                // Variables of type #binder_cat in the body won't match our substitution
                self.clone()
            }
        }
    }
}

/// Generate substitution for a constructor with multi-binder Scope (Vec<Binder>)
fn generate_multi_binder_substitution_arm(
    category: &Ident,
    rule: &GrammarRule,
    replacement_cat: &Ident,
) -> TokenStream {
    let label = &rule.label;
    
    // For multi-binder, we need to check if ANY of the binders shadows the variable
    // Pattern: PInputs(field_0, scope) 
    // Check: binders.iter().any(|b| b.0 == *var)
    
    let category_str = category.to_string();
    let replacement_cat_str = replacement_cat.to_string();
    
    // Get info about the collection and body types from term_context
    let term_context = rule.term_context.as_ref().expect("Multi-binder should have term_context");
    
    let mut collection_subst = quote! { field_0.clone() };
    let mut body_subst_method = quote! { substitute };
    
    // Find the collection and body types
    for param in term_context {
        match param {
            TermParam::Simple { ty, .. } => {
                if let TypeExpr::Collection { element, .. } = ty {
                    if let TypeExpr::Base(elem_type) = element.as_ref() {
                        let elem_type_str = elem_type.to_string();
                        let subst_method = if elem_type_str == replacement_cat_str {
                            quote! { substitute }
                        } else {
                            let method_name = quote::format_ident!("substitute_{}", replacement_cat_str.to_lowercase());
                            quote! { #method_name }
                        };
                        collection_subst = quote! {
                            field_0.iter().map(|elem| elem.#subst_method(var, replacement)).collect()
                        };
                    }
                }
            }
            TermParam::MultiAbstraction { ty, .. } => {
                if let TypeExpr::Arrow { codomain, .. } = ty {
                    if let TypeExpr::Base(body_type) = codomain.as_ref() {
                        let body_type_str = body_type.to_string();
                        body_subst_method = if body_type_str == replacement_cat_str {
                            quote! { substitute }
                        } else {
                            let method_name = quote::format_ident!("substitute_{}", replacement_cat_str.to_lowercase());
                            quote! { #method_name }
                        };
                    }
                }
            }
            _ => {}
        }
    }
    
    if category_str == replacement_cat_str {
        // Same category - need to check for shadowing
        quote! {
            #category::#label(field_0, scope) => {
                // Multi-binder: check if ANY binder shadows the variable
                let binders = &scope.inner().unsafe_pattern;
                let body = &scope.inner().unsafe_body;
                
                // Check if var is shadowed by any binder
                if binders.iter().any(|b| b.0 == *var) {
                    // Variable is shadowed - no substitution needed
                    self.clone()
                } else {
                    // Not shadowed - substitute in body and collection
                    let subst_body = (**body).#body_subst_method(var, replacement);
                    let new_scope = mettail_runtime::Scope::new(
                        binders.clone(),
                        Box::new(subst_body),
                    );
                    #category::#label(#collection_subst, new_scope)
                }
            }
        }
    } else {
        // Different category - just clone
        quote! {
            #category::#label(field_0, scope) => self.clone()
        }
    }
}

/// Generate substitution for a regular constructor (no bindings)
fn generate_regular_substitution_arm(
    category: &Ident,
    rule: &GrammarRule,
    replacement_cat: &Ident,
) -> TokenStream {
    let label = &rule.label;

    // Check if this constructor has a Var field
    let has_var_field = rule
        .items
        .iter()
        .any(|item| matches!(item, GrammarItem::NonTerminal(ident) if ident.to_string() == "Var"));

    // For constructors with Var fields, we need special handling
    if has_var_field {
        // NVar case - substitute directly at the Var level
        let category_str = category.to_string();
        let replacement_cat_str = replacement_cat.to_string();

        if category_str == replacement_cat_str {
            // Same category - use moniker's built-in substitution
            return quote! {
                #category::#label(var_field) => {
                    use mettail_runtime::Var;
                    match var_field {
                        Var::Bound(b) => #category::#label(Var::Bound(b.clone())),
                        Var::Free(ref fv) => {
                            if fv == var {
                                replacement.clone()
                            } else {
                                self.clone()
                            }
                        }
                    }
                }
            };
        } else {
            // Cross-category - no substitution possible in Var
            return quote! {
                #category::#label(_) => self.clone()
            };
        }
    }

    // Count total fields (non-terminals excluding Var, and collections)
    #[derive(Clone)]
    enum FieldInfo {
        NonTerminal(Ident),
        Collection {
            element_type: Ident,
            coll_type: CollectionType,
        },
    }

    let total_fields: Vec<FieldInfo> = rule
        .items
        .iter()
        .filter_map(|item| match item {
            GrammarItem::NonTerminal(ident) if ident.to_string() != "Var" => {
                Some(FieldInfo::NonTerminal(ident.clone()))
            },
            GrammarItem::Collection { element_type, coll_type, .. } => {
                Some(FieldInfo::Collection {
                    element_type: element_type.clone(),
                    coll_type: coll_type.clone(),
                })
            },
            _ => None,
        })
        .collect();

    if total_fields.is_empty() {
        // Unit constructor - no fields at all
        return quote! {
            #category::#label => self.clone()
        };
    }

    // Generate pattern bindings for all fields
    let field_bindings: Vec<TokenStream> = (0..total_fields.len())
        .map(|i| {
            let field = quote::format_ident!("field_{}", i);
            quote! { #field }
        })
        .collect();

    let replacement_cat_str = replacement_cat.to_string();

    // Generate substitution calls - recurse into ALL category fields
    let field_substitutions: Vec<TokenStream> = (0..total_fields.len())
        .map(|i| {
            let field = quote::format_ident!("field_{}", i);

            match &total_fields[i] {
                FieldInfo::NonTerminal(field_cat) => {
                    let field_cat_str = field_cat.to_string();

                    // Determine which method to call on this field
                    let subst_method = if field_cat_str == replacement_cat_str {
                        quote! { substitute }
                    } else {
                        let method_name = quote::format_ident!(
                            "substitute_{}",
                            replacement_cat_str.to_lowercase()
                        );
                        quote! { #method_name }
                    };

                    quote! {
                        Box::new((**#field).#subst_method(var, replacement))
                    }
                },
                FieldInfo::Collection { element_type, coll_type } => {
                    let elem_cat_str = element_type.to_string();

                    // Determine which method to call on collection elements
                    let subst_method = if elem_cat_str == replacement_cat_str {
                        quote! { substitute }
                    } else {
                        let method_name = quote::format_ident!(
                            "substitute_{}",
                            replacement_cat_str.to_lowercase()
                        );
                        quote! { #method_name }
                    };

                    // Map over collection, substituting in each element
                    match coll_type {
                        CollectionType::HashBag => {
                            // Use flatten helper to automatically flatten nested collections
                            let helper_name = quote::format_ident!(
                                "insert_into_{}",
                                label.to_string().to_lowercase()
                            );
                            quote! {
                                {
                                    let mut bag = mettail_runtime::HashBag::new();
                                    for (elem, count) in #field.iter() {
                                        let subst_elem = elem.#subst_method(var, replacement);
                                        for _ in 0..count {
                                            // Use flatten helper: auto-flattens if subst_elem is nested collection
                                            #category::#helper_name(&mut bag, subst_elem.clone());
                                        }
                                    }
                                    bag
                                }
                            }
                        },
                        CollectionType::HashSet => {
                            quote! {
                                #field.iter().map(|elem| {
                                    elem.#subst_method(var, replacement)
                                }).collect()
                            }
                        },
                        CollectionType::Vec => {
                            quote! {
                                #field.iter().map(|elem| {
                                    elem.#subst_method(var, replacement)
                                }).collect()
                            }
                        },
                    }
                },
            }
        })
        .collect();

    // Generate the match arm
    if total_fields.len() == 1 {
        // Single field (possibly boxed)
        quote! {
            #category::#label(#(#field_bindings),*) => {
                #category::#label(#(#field_substitutions),*)
            }
        }
    } else {
        // Multiple fields
        quote! {
            #category::#label(#(#field_bindings),*) => {
                #category::#label(#(#field_substitutions),*)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use syn::parse_quote;

    #[test]
    fn test_generate_simple_substitution() {
        let theory = TheoryDef {
            name: parse_quote!(Test),
            params: vec![],
            exports: vec![Export {
                name: parse_quote!(Elem),
                native_type: None,
            }],
            terms: vec![
                GrammarRule {
                    label: parse_quote!(Zero),
                    category: parse_quote!(Elem),
                    items: vec![GrammarItem::Terminal("0".to_string())],
                    bindings: vec![],
                    term_context: None,
                    syntax_pattern: None,
                },
                GrammarRule {
                    label: parse_quote!(Var),
                    category: parse_quote!(Elem),
                    items: vec![GrammarItem::NonTerminal(parse_quote!(Var))],
                    bindings: vec![],
                    term_context: None,
                    syntax_pattern: None,
                },
            ],
            equations: vec![],
            rewrites: vec![],
            semantics: vec![],
        };

        let output = generate_substitution(&theory);
        let output_str = output.to_string();

        println!("Generated substitution:\n{}", output_str);

        // Check that it generates substitute method
        assert!(output_str.contains("substitute"));
        assert!(output_str.contains("replacement"));
    }
}
