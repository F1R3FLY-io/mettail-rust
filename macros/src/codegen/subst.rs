//! Substitution generation for MeTTaIL terms
//!
//! Generates capture-avoiding substitution methods using moniker's BoundTerm trait.
//! For each exported category, we generate a `substitute` method that performs
//! capture-avoiding substitution of variables.

#![allow(clippy::cmp_owned)]

use crate::ast::{GrammarItem, GrammarRule, TheoryDef};
use crate::codegen::generate_var_label;
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
    let main_method = generate_substitute_method(category, rules, category);

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

    quote! {
        impl #category {
            #main_method
            #self_method
            #(#cross_methods)*
        }
    }
}

fn generate_substitute_method(
    category: &Ident,
    rules: &[&GrammarRule],
    _replacement_cat: &Ident,
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

    quote! {
        /// Alias for substitute(), provided for uniform cross-category substitution
        pub fn #method_name(
            &self,
            var: &mettail_runtime::FreeVar<String>,
            replacement: &Self
        ) -> Self {
            self.substitute(var, replacement)
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
                            crate::ast::CollectionType::HashBag => {
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
                            crate::ast::CollectionType::HashSet => {
                                quote! {
                                    #field_name.iter().map(|elem| {
                                        elem.#subst_method(var, replacement)
                                    }).collect()
                                }
                            }
                            crate::ast::CollectionType::Vec => {
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
            coll_type: crate::ast::CollectionType,
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
                        crate::ast::CollectionType::HashBag => {
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
                        crate::ast::CollectionType::HashSet => {
                            quote! {
                                #field.iter().map(|elem| {
                                    elem.#subst_method(var, replacement)
                                }).collect()
                            }
                        },
                        crate::ast::CollectionType::Vec => {
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
    use crate::ast::*;
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
