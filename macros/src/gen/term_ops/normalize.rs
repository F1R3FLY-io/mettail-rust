#![allow(clippy::cmp_owned, clippy::single_match)]

use crate::ast::language::LanguageDef;
use crate::ast::grammar::{GrammarItem, GrammarRule, TermParam};
use proc_macro2::TokenStream;
use quote::quote;
use std::collections::HashMap;

/// For each constructor with a collection field, generates a helper function that automatically flattens nested collections of the same type.
pub fn generate_flatten_helpers(language: &LanguageDef) -> TokenStream {
    use quote::format_ident;

    // Group rules by category
    let mut helpers_by_cat: HashMap<String, Vec<TokenStream>> = HashMap::new();

    for rule in &language.terms {
        // Skip rules that use new term_context with multi-binders
        // These have structured fields, not just a collection
        if let Some(ref ctx) = rule.term_context {
            let has_multi_binder = ctx.iter().any(|p| matches!(p, TermParam::MultiAbstraction { .. }));
            if has_multi_binder {
                continue;
            }
        }
        
        // Check if this rule has a collection field (old style)
        let has_collection = rule
            .items
            .iter()
            .any(|item| matches!(item, GrammarItem::Collection { .. }));

        if !has_collection {
            continue;
        }

        let category = &rule.category;
        let label = &rule.label;
        let helper_name = format_ident!("insert_into_{}", label.to_string().to_lowercase());

        let helper = quote! {
            /// Auto-flattening insert for #label
            ///
            /// If elem is itself a #label, recursively merges its contents instead of nesting.
            /// This ensures that collection constructors are always flat, never nested.
            pub fn #helper_name(
                bag: &mut mettail_runtime::HashBag<#category>,
                elem: #category
            ) {
                match elem {
                    #category::#label(inner) => {
                        // Flatten: recursively merge inner bag contents
                        for (e, count) in inner.iter() {
                            for _ in 0..count {
                                // Recursive call handles multi-level nesting
                                Self::#helper_name(bag, e.clone());
                            }
                        }
                    }
                    _ => {
                        // Normal insert - not a nested collection
                        bag.insert(elem);
                    }
                }
            }
        };

        helpers_by_cat
            .entry(category.to_string())
            .or_default()
            .push(helper);
    }

    // Generate impl blocks for each category
    let impls: Vec<TokenStream> = language
        .types
        .iter()
        .filter_map(|lang_type| {
            let cat_name = &lang_type.name;
            let helpers = helpers_by_cat.get(&cat_name.to_string())?;

            if helpers.is_empty() {
                return None;
            }

            Some(quote! {
                impl #cat_name {
                    #(#helpers)*
                }
            })
        })
        .collect();

    quote! {
        #(#impls)*
    }
}

/// Generate normalize functions that recursively flatten nested collections
pub fn generate_normalize_functions(language: &LanguageDef) -> TokenStream {
    use quote::format_ident;

    let mut impls = Vec::new();

    for lang_type in &language.types {
        let category = &lang_type.name;

        // Find all rules for this category
        let rules_for_category: Vec<_> = language
            .terms
            .iter()
            .filter(|rule| rule.category == *category)
            .collect();

        // Find collection constructors
        let has_collections = rules_for_category.iter().any(|rule| {
            rule.items
                .iter()
                .any(|item| matches!(item, GrammarItem::Collection { .. }))
        });

        // If no collections, generate a simple normalize that just clones
        if !has_collections {
            let impl_block = quote! {
                impl #category {
                    /// Normalize (no-op for categories without collections)
                    pub fn normalize(&self) -> Self {
                        self.clone()
                    }
                }
            };
            impls.push(impl_block);
            continue;
        }

        // Generate match arms for each constructor
        let match_arms: Vec<TokenStream> = rules_for_category
            .iter()
            .filter_map(|rule| {
                let label = &rule.label;

                // Check if this rule uses term_context with multi-binder
                let has_multi_binder = rule.term_context.as_ref().map_or(false, |ctx| {
                    ctx.iter().any(|p| matches!(p, TermParam::MultiAbstraction { .. }))
                });

                // Check if this is a simple collection constructor (no multi-binder)
                let is_collection = !has_multi_binder && rule
                    .items
                    .iter()
                    .any(|item| matches!(item, GrammarItem::Collection { .. }));

                if is_collection {
                    // For collection constructors, rebuild using the flattening helper
                    let helper_name =
                        format_ident!("insert_into_{}", label.to_string().to_lowercase());

                    Some(quote! {
                        #category::#label(bag) => {
                            // Rebuild the bag using the flattening insert helper
                            let mut new_bag = mettail_runtime::HashBag::new();
                            for (elem, count) in bag.iter() {
                                for _ in 0..count {
                                    // Recursively normalize the element before inserting
                                    let normalized_elem = elem.normalize();
                                    Self::#helper_name(&mut new_bag, normalized_elem);
                                }
                            }
                            #category::#label(new_bag)
                        }
                    })
                } else if has_multi_binder {
                    // Multi-binder constructor: just clone (no collection flattening)
                    Some(quote! {
                        #category::#label(field_0, scope) => self.clone()
                    })
                } else if rule.bindings.is_empty() {
                    // For non-collection, non-binder constructors
                    // Get fields (excluding Terminals)
                    let fields: Vec<_> = rule
                        .items
                        .iter()
                        .filter(|item| {
                            matches!(
                                item,
                                GrammarItem::NonTerminal(_) | GrammarItem::Collection { .. }
                            )
                        })
                        .collect();

                    if fields.is_empty() {
                        // Nullary - no changes needed
                        Some(quote! {
                            #category::#label => self.clone()
                        })
                    } else if fields.len() == 1 {
                        // Single field constructor
                        match fields[0] {
                            GrammarItem::NonTerminal(field_cat) if field_cat == category => {
                                // Recursive case - normalize the field
                                Some(quote! {
                                    #category::#label(f0) => {
                                        #category::#label(Box::new(f0.as_ref().normalize()))
                                    }
                                })
                            },
                            GrammarItem::NonTerminal(field_cat)
                                if field_cat.to_string() == "Var" =>
                            {
                                // Var field - just clone (no Box)
                                Some(quote! {
                                    #category::#label(v) => {
                                        #category::#label(v.clone())
                                    }
                                })
                            },
                            _ => {
                                // Different category or unsupported - just clone
                                Some(quote! {
                                    #category::#label(f0) => {
                                        #category::#label(f0.clone())
                                    }
                                })
                            },
                        }
                    } else {
                        // Multiple fields - skip for now (too complex)
                        None
                    }
                } else {
                    // Binder constructor
                    // Count total AST fields (non-terminal, non-binder)
                    let (_binder_idx, body_indices) = &rule.bindings[0];
                    let body_idx = body_indices[0];

                    let mut field_names = Vec::new();
                    let mut scope_field_idx = None;
                    for (i, item) in rule.items.iter().enumerate() {
                        if i == *_binder_idx {
                            continue; // Skip binder
                        }
                        match item {
                            GrammarItem::NonTerminal(_) => {
                                if i == body_idx {
                                    scope_field_idx = Some(field_names.len());
                                    field_names.push(format_ident!("scope"));
                                } else {
                                    field_names.push(format_ident!("f{}", field_names.len()));
                                }
                            },
                            _ => {},
                        }
                    }

                    let scope_idx = scope_field_idx.expect("Should have scope");

                    // Generate field reconstruction
                    let reconstructed_fields: Vec<_> = field_names
                        .iter()
                        .enumerate()
                        .map(|(i, name)| {
                            if i == scope_idx {
                                quote! {
                                    mettail_runtime::Scope::from_parts_unsafe(
                                        #name.inner().unsafe_pattern.clone(),
                                        Box::new(#name.inner().unsafe_body.as_ref().normalize())
                                    )
                                }
                            } else {
                                quote! { #name.clone() }
                            }
                        })
                        .collect();

                    Some(quote! {
                        #category::#label(#(#field_names),*) => {
                            #category::#label(#(#reconstructed_fields),*)
                        }
                    })
                }
            })
            .collect();

        // Add a fallback for any unhandled patterns
        let fallback = quote! {
            _ => self.clone()
        };

        let impl_block = quote! {
            impl #category {
                /// Recursively normalize this term by flattening any nested collections.
                ///
                /// For example, `PPar({PPar({a, b}), c})` becomes `PPar({a, b, c})`.
                /// This ensures that collection constructors are always in canonical flat form.
                pub fn normalize(&self) -> Self {
                    match self {
                        #(#match_arms,)*
                        #fallback
                    }
                }
            }
        };

        impls.push(impl_block);
    }

    quote! {
        #(#impls)*
    }
}
