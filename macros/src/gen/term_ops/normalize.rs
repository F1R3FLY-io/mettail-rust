#![allow(clippy::cmp_owned, clippy::single_match)]

use crate::ast::grammar::{GrammarItem, TermParam};
use crate::ast::language::LanguageDef;
use crate::gen::{generate_literal_label, generate_var_label, is_integer_rule, is_var_rule};
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
            let has_multi_binder = ctx
                .iter()
                .any(|p| matches!(p, TermParam::MultiAbstraction { .. }));
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
/// and perform immediate beta-reduction.
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

        // Native types: generate simple recursive normalize (no beta-reduction, no collections)
        if let Some(ref native_type) = lang_type.native_type {
            let has_integer_rule = rules_for_category.iter().any(|r| is_integer_rule(r));
            let has_var_rule = rules_for_category.iter().any(|r| is_var_rule(r));
            let mut match_arms: Vec<TokenStream> = rules_for_category
                .iter()
                .filter_map(|rule| {
                    if is_var_rule(rule) || is_integer_rule(rule) {
                        return None;
                    }
                    let label = &rule.label;
                    let fields: Vec<_> = rule
                        .items
                        .iter()
                        .filter(|item| matches!(item, GrammarItem::NonTerminal(_)))
                        .collect();
                    if fields.is_empty() {
                        return Some(quote! { #category::#label => self.clone() });
                    }
                    let field_names: Vec<_> =
                        (0..fields.len()).map(|i| format_ident!("f{}", i)).collect();
                    let field_patterns: Vec<_> =
                        field_names.iter().map(|n| quote! { ref #n }).collect();
                    let normalized_fields: Vec<_> = fields
                        .iter()
                        .zip(field_names.iter())
                        .map(|(item, name)| {
                            if let GrammarItem::NonTerminal(field_cat) = item {
                                if field_cat == category {
                                    quote! { Box::new(#name.as_ref().normalize()) }
                                } else {
                                    quote! { #name.clone() }
                                }
                            } else {
                                quote! { #name.clone() }
                            }
                        })
                        .collect();
                    Some(quote! {
                        #category::#label(#(#field_patterns),*) => {
                            #category::#label(#(#normalized_fields),*)
                        }
                    })
                })
                .collect();
            if !has_integer_rule {
                let literal_label = generate_literal_label(native_type);
                match_arms.push(quote! {
                    #category::#literal_label(_) => self.clone()
                });
            }
            if !has_var_rule {
                let var_label = generate_var_label(category);
                match_arms.push(quote! {
                    #category::#var_label(_) => self.clone()
                });
            }
            let impl_block = quote! {
                impl #category {
                    /// Recursively normalize subterms (no beta-reduction for native-type categories)
                    pub fn normalize(&self) -> Self {
                        match self {
                            #(#match_arms),*,
                            _ => self.clone()
                        }
                    }
                }
            };
            impls.push(impl_block);
            continue;
        }

        // Find collection constructors
        let has_collections = rules_for_category.iter().any(|rule| {
            rule.items
                .iter()
                .any(|item| matches!(item, GrammarItem::Collection { .. }))
        });

        // Generate beta-reduction arms for Apply/Lam variants
        let beta_reduction_arms = generate_beta_reduction_arms(category, language);

        // If no collections and no beta-reduction, generate a simple normalize
        if !has_collections && beta_reduction_arms.is_empty() {
            let impl_block = quote! {
                impl #category {
                    /// Normalize (no-op for categories without collections or beta-redexes)
                    pub fn normalize(&self) -> Self {
                        self.clone()
                    }
                }
            };
            impls.push(impl_block);
            continue;
        }

        // Generate match arms for each constructor
        #[allow(clippy::unnecessary_filter_map)]
        let match_arms: Vec<TokenStream> = rules_for_category
            .iter()
            .filter_map(|rule| {
                let label = &rule.label;

                // Check if this rule uses term_context with multi-binder
                let has_multi_binder = rule.term_context.as_ref().is_some_and(|ctx| {
                    ctx.iter()
                        .any(|p| matches!(p, TermParam::MultiAbstraction { .. }))
                });

                // Check if this is a simple collection constructor (no multi-binder)
                let is_collection = !has_multi_binder
                    && rule
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
                    // Multi-binder constructor: normalize the scope body
                    Some(quote! {
                        #category::#label(field_0, scope) => {
                            #category::#label(
                                field_0.clone(),
                                mettail_runtime::Scope::from_parts_unsafe(
                                    scope.inner().unsafe_pattern.clone(),
                                    Box::new(scope.inner().unsafe_body.as_ref().normalize())
                                )
                            )
                        }
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
                        // Multiple fields - generate normalization for each
                        let field_names: Vec<_> =
                            (0..fields.len()).map(|i| format_ident!("f{}", i)).collect();

                        let normalized_fields: Vec<_> = fields
                            .iter()
                            .enumerate()
                            .map(|(i, field)| {
                                let field_name = &field_names[i];
                                match field {
                                    GrammarItem::NonTerminal(field_cat) => {
                                        // Check if field is same category or another normalizable type
                                        let field_cat_str = field_cat.to_string();
                                        if field_cat == category {
                                            // Same category - normalize recursively (boxed)
                                            quote! { Box::new(#field_name.as_ref().normalize()) }
                                        } else if field_cat_str == "Var" {
                                            // Var field - not boxed, just clone
                                            quote! { #field_name.clone() }
                                        } else if language.types.iter().any(|t| {
                                            t.name == *field_cat && t.native_type.is_none()
                                        }) {
                                            // Another non-native category - normalize it (boxed)
                                            quote! { Box::new(#field_name.as_ref().normalize()) }
                                        } else {
                                            // Native type or unknown - just clone (boxed)
                                            quote! { #field_name.clone() }
                                        }
                                    },
                                    GrammarItem::Collection { .. } => {
                                        // Collection field - just clone for now
                                        // (collection flattening is handled separately)
                                        quote! { #field_name.clone() }
                                    },
                                    _ => quote! { #field_name.clone() },
                                }
                            })
                            .collect();

                        Some(quote! {
                            #category::#label(#(#field_names),*) => {
                                #category::#label(#(#normalized_fields),*)
                            }
                        })
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
                /// Recursively normalize this term by:
                /// 1. Flattening nested collections (e.g., `PPar({PPar({a, b}), c})` becomes `PPar({a, b, c})`)
                /// 2. Performing immediate beta-reduction (e.g., `Apply(Lam(^x.body), arg)` becomes `body[arg/x]`)
                ///
                /// This ensures terms are always in canonical form with beta-redexes reduced.
                pub fn normalize(&self) -> Self {
                    match self {
                        #(#beta_reduction_arms,)*
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

/// Generate match arms for beta-reduction of Apply/Lam variants
fn generate_beta_reduction_arms(category: &syn::Ident, language: &LanguageDef) -> Vec<TokenStream> {
    use quote::format_ident;

    let mut arms = Vec::new();

    // For each domain type, generate beta-reduction arms
    for domain_lang_type in &language.types {
        // Skip native types
        if domain_lang_type.native_type.is_some() {
            continue;
        }

        let domain = &domain_lang_type.name;
        let domain_lower = domain.to_string().to_lowercase();

        // Variant names
        let apply_variant = format_ident!("Apply{}", domain);
        let lam_variant = format_ident!("Lam{}", domain);
        let mapply_variant = format_ident!("MApply{}", domain);
        let mlam_variant = format_ident!("MLam{}", domain);

        // Substitution method names
        let subst_method = format_ident!("substitute_{}", domain_lower);
        let multi_subst_method = format_ident!("multi_substitute_{}", domain_lower);

        // Single-argument beta reduction:
        // ApplyDomain(LamDomain(scope), arg) => body[binder := arg].normalize()
        arms.push(quote! {
            #category::#apply_variant(lam_box, arg_box) => {
                // First normalize the function position
                let lam_normalized = lam_box.as_ref().normalize();
                match &lam_normalized {
                    #category::#lam_variant(scope) => {
                        // Beta-reduce: unbind and substitute
                        let (binder, body) = scope.clone().unbind();
                        // Normalize the argument before substitution, then normalize the result
                        let arg_normalized = arg_box.as_ref().normalize();
                        (*body).#subst_method(&binder.0, &arg_normalized).normalize()
                    }
                    _ => {
                        // Not a beta-redex after normalization: return normalized subterms
                        #category::#apply_variant(
                            Box::new(lam_normalized),
                            Box::new(arg_box.as_ref().normalize())
                        )
                    }
                }
            }
        });

        // Multi-argument beta reduction:
        // MApplyDomain(MLamDomain(scope), args) => body[binders := args].normalize()
        arms.push(quote! {
            #category::#mapply_variant(lam_box, args) => {
                // First normalize the function position
                let lam_normalized = lam_box.as_ref().normalize();
                match &lam_normalized {
                    #category::#mlam_variant(scope) => {
                        // Beta-reduce: unbind and substitute all binders
                        let (binders, body) = scope.clone().unbind();
                        let vars: Vec<_> = binders.iter().map(|b| &b.0).collect();
                        // Normalize arguments before substitution
                        let args_normalized: Vec<_> = args.iter()
                            .map(|a| a.normalize())
                            .collect();
                        (*body).#multi_subst_method(&vars, &args_normalized).normalize()
                    }
                    _ => {
                        // Not a beta-redex after normalization: return normalized subterms
                        #category::#mapply_variant(
                            Box::new(lam_normalized),
                            args.iter().map(|a| a.normalize()).collect()
                        )
                    }
                }
            }
        });
    }

    arms
}
