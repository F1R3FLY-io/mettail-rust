#![allow(clippy::cmp_owned, clippy::single_match)]

use super::{display, env, generate_var_label, is_integer_rule, is_var_rule, subst, termgen};
use crate::ast::{theory::{TheoryDef, Export, SemanticOperation, BuiltinOp, Condition, EnvAction, RewriteRule}, grammar::{GrammarItem, GrammarRule, TermParam}, types::{TypeExpr, CollectionType}, term::Term};
use proc_macro2::TokenStream;
use quote::quote;
use std::collections::HashMap;

pub fn generate_ast(theory: &TheoryDef) -> TokenStream {
    let ast_enums = generate_ast_enums(theory);
    let flatten_helpers = generate_flatten_helpers(theory);
    let normalize_impl = generate_normalize_functions(theory);
    let subst_impl = subst::generate_substitution(theory);
    let env_types = env::generate_environments(theory);
    let env_subst_impl = subst::generate_env_substitution(theory);
    let display_impl = display::generate_display(theory);
    let generation_impl = termgen::generate_term_generation(theory);
    let random_gen_impl = termgen::generate_random_generation(theory);
    let eval_impl = generate_eval_method(theory);
    let rewrite_impl = generate_rewrite_application(theory);
    let var_inference_impl = generate_var_category_inference(theory);

    // Generate LALRPOP module reference
    let theory_name = &theory.name;
    let theory_name_lower = theory_name.to_string().to_lowercase();
    let theory_mod = syn::Ident::new(&theory_name_lower, proc_macro2::Span::call_site());

    quote! {
        use lalrpop_util::lalrpop_mod;

        #ast_enums

        #flatten_helpers

        #normalize_impl

        #subst_impl

        #env_types

        #env_subst_impl

        #display_impl

        #generation_impl

        #random_gen_impl

        #eval_impl

        #rewrite_impl

        #var_inference_impl

        #[cfg(not(test))]
        #[allow(unused_imports)]
        lalrpop_util::lalrpop_mod!(pub #theory_mod);

        #[cfg(test)]
        #[allow(unused_imports)]
        lalrpop_util::lalrpop_mod!(#theory_mod);
    }
}

/// Generate just the AST enums (without parser)
fn generate_ast_enums(theory: &TheoryDef) -> TokenStream {
    // Group rules by category
    let mut rules_by_cat: HashMap<String, Vec<&GrammarRule>> = HashMap::new();

    for rule in &theory.terms {
        let cat_name = rule.category.to_string();
        rules_by_cat.entry(cat_name).or_default().push(rule);
    }

    // Generate enum for each exported category
    let enums: Vec<TokenStream> = theory.exports.iter().map(|export| {
        let cat_name = &export.name;

        let rules = rules_by_cat
            .get(&cat_name.to_string())
            .map(|v| v.as_slice())
            .unwrap_or(&[]);

        let has_integer_rule = rules.iter().any(|rule| is_integer_rule(rule));
        let has_var_rule = rules.iter().any(|rule| is_var_rule(rule));

        let mut variants: Vec<TokenStream> = rules.iter().map(|rule| {
            generate_variant(rule, theory)
        }).collect();

        // Auto-generate NumLit variant for native types without explicit Integer rule
        if let Some(native_type) = &export.native_type {
            if !has_integer_rule {
                let literal_label = super::generate_literal_label(native_type);
                let native_type_cloned = native_type.clone();
                variants.push(quote! {
                    #literal_label(#native_type_cloned)
                });
            }
        }

        // Auto-generate Var variant if no explicit Var rule exists
        if !has_var_rule {
            let var_label = generate_var_label(cat_name);
            variants.push(quote! {
                #var_label(mettail_runtime::OrdVar)
            });
        }

        // Auto-generate lambda variants for every domain category
        // This creates Lam{Domain} and MLam{Domain} for each domain type
        for domain_export in &theory.exports {
            // Skip native types (e.g., Int) - can't use as lambda binder
            if domain_export.native_type.is_some() {
                continue;
            }
            
            let domain_name = &domain_export.name;
            
            // Single-binder lambda: Lam{Domain}
            let lam_variant = syn::Ident::new(
                &format!("Lam{}", domain_name),
                proc_macro2::Span::call_site()
            );
            variants.push(quote! {
                #lam_variant(mettail_runtime::Scope<mettail_runtime::Binder<String>, Box<#cat_name>>)
            });
            
            // Multi-binder lambda: MLam{Domain}
            let mlam_variant = syn::Ident::new(
                &format!("MLam{}", domain_name),
                proc_macro2::Span::call_site()
            );
            variants.push(quote! {
                #mlam_variant(mettail_runtime::Scope<Vec<mettail_runtime::Binder<String>>, Box<#cat_name>>)
            });
            
            // Application variant: Apply{Domain}
            // Represents unevaluated application of a lambda to an argument
            let apply_variant = syn::Ident::new(
                &format!("Apply{}", domain_name),
                proc_macro2::Span::call_site()
            );
            variants.push(quote! {
                #apply_variant(Box<#cat_name>, Box<#domain_name>)
            });
            
            // Multi-application variant: MApply{Domain}
            let mapply_variant = syn::Ident::new(
                &format!("MApply{}", domain_name),
                proc_macro2::Span::call_site()
            );
            variants.push(quote! {
                #mapply_variant(Box<#cat_name>, Vec<#domain_name>)
            });
        }

        quote! {
            #[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, mettail_runtime::BoundTerm)]
            pub enum #cat_name {
                #(#variants),*
            }
        }
    }).collect();

    quote! {
        #(#enums)*
    }
}

fn generate_variant(rule: &GrammarRule, theory: &TheoryDef) -> TokenStream {
    let label = &rule.label;

    // Check if this rule uses new syntax (term_context)
    if let Some(ref term_context) = rule.term_context {
        return generate_variant_from_term_context(label, term_context);
    }

    // Check if this rule has bindings (old syntax)
    if !rule.bindings.is_empty() {
        // This constructor has binders - generate Scope type
        return generate_binder_variant(rule);
    }

    // Count non-terminal and collection items (these become fields)
    #[derive(Clone)]
    enum FieldType {
        NonTerminal(syn::Ident),
        Collection {
            coll_type: CollectionType,
            element_type: syn::Ident,
        },
    }

    let fields: Vec<FieldType> = rule
        .items
        .iter()
        .filter_map(|item| match item {
            GrammarItem::NonTerminal(ident) => Some(FieldType::NonTerminal(ident.clone())),
            GrammarItem::Collection { coll_type, element_type, .. } => {
                Some(FieldType::Collection {
                    coll_type: coll_type.clone(),
                    element_type: element_type.clone(),
                })
            },
            GrammarItem::Binder { .. } => None, // Handled above
            _ => None,
        })
        .collect();

    if fields.is_empty() {
        // Unit variant
        quote! { #label }
    } else if fields.len() == 1 {
        #[allow(clippy::cmp_owned)]
        match &fields[0] {
            FieldType::NonTerminal(ident) if ident.to_string() == "Integer" => {
                // Special case: Integer field - use the category's native type
                let category = &rule.category;

                // Integer requires native type (should be validated earlier)
                if let Some(native_type) = theory
                    .exports
                    .iter()
                    .find(|e| e.name == *category)
                    .and_then(|e| e.native_type.as_ref())
                {
                    let native_type_cloned = native_type.clone();
                    quote! { #label(#native_type_cloned) }
                } else {
                    // Fallback to i32 if native type not found
                    quote! { #label(i32) }
                }
            },
            FieldType::NonTerminal(ident) if ident.to_string() == "Var" => {
                // Special case: Var field - always use OrdVar
                quote! { #label(mettail_runtime::OrdVar) }
            },
            FieldType::NonTerminal(ident) => {
                // Single non-terminal field
                quote! { #label(Box<#ident>) }
            },
            FieldType::Collection { coll_type, element_type } => {
                // Single collection field
                let coll_type_ident = match coll_type {
                    CollectionType::HashBag => quote! { mettail_runtime::HashBag },
                    CollectionType::HashSet => quote! { std::collections::HashSet },
                    CollectionType::Vec => quote! { Vec },
                };
                quote! { #label(#coll_type_ident<#element_type>) }
            },
        }
    } else {
        // Multiple fields - tuple variant
        let field_types: Vec<TokenStream> = fields
            .iter()
            .map(|f| match f {
                FieldType::NonTerminal(ident) if ident.to_string() == "Var" => {
                    quote! { mettail_runtime::OrdVar }
                },
                FieldType::NonTerminal(ident) => {
                    quote! { Box<#ident> }
                },
                FieldType::Collection { coll_type, element_type } => {
                    let coll_type_ident = match coll_type {
                        CollectionType::HashBag => quote! { mettail_runtime::HashBag },
                        CollectionType::HashSet => quote! { std::collections::HashSet },
                        CollectionType::Vec => quote! { Vec },
                    };
                    quote! { #coll_type_ident<#element_type> }
                },
            })
            .collect();

        quote! { #label(#(#field_types),*) }
    }
}

/// Generate variant from new term_context syntax
fn generate_variant_from_term_context(label: &syn::Ident, term_context: &[TermParam]) -> TokenStream {
    let mut fields: Vec<TokenStream> = Vec::new();
    
    for param in term_context {
        match param {
            TermParam::Simple { ty, .. } => {
                // Simple parameter: generate appropriate field type
                let field_type = type_expr_to_field_type(ty);
                fields.push(field_type);
            }
            TermParam::Abstraction { ty, .. } => {
                // Single abstraction: ^x.p:[A -> B]
                // Generates: Scope<Binder<String>, Box<B>>
                if let TypeExpr::Arrow { codomain, .. } = ty {
                    let body_type = type_expr_to_rust_type(codomain);
                    fields.push(quote! {
                        mettail_runtime::Scope<mettail_runtime::Binder<String>, Box<#body_type>>
                    });
                }
            }
            TermParam::MultiAbstraction { ty, .. } => {
                // Multi-abstraction: ^[xs].p:[Name* -> B]
                // Generates: Scope<Vec<Binder<String>>, Box<B>>
                if let TypeExpr::Arrow { codomain, .. } = ty {
                    let body_type = type_expr_to_rust_type(codomain);
                    fields.push(quote! {
                        mettail_runtime::Scope<Vec<mettail_runtime::Binder<String>>, Box<#body_type>>
                    });
                }
            }
        }
    }
    
    if fields.is_empty() {
        // Unit variant
        quote! { #label }
    } else if fields.len() == 1 {
        let field = &fields[0];
        quote! { #label(#field) }
    } else {
        quote! { #label(#(#fields),*) }
    }
}

/// Convert TypeExpr to a Rust field type (for enum variant fields)
fn type_expr_to_field_type(ty: &TypeExpr) -> TokenStream {
    match ty {
        TypeExpr::Base(ident) => {
            let name = ident.to_string();
            if name == "Var" {
                quote! { mettail_runtime::OrdVar }
            } else if name == "Integer" {
                quote! { i64 }
            } else {
                quote! { Box<#ident> }
            }
        }
        TypeExpr::Collection { coll_type, element } => {
            let elem_type = type_expr_to_rust_type(element);
            match coll_type {
                CollectionType::HashBag => quote! { mettail_runtime::HashBag<#elem_type> },
                CollectionType::HashSet => quote! { std::collections::HashSet<#elem_type> },
                CollectionType::Vec => quote! { Vec<#elem_type> },
            }
        }
        TypeExpr::Arrow { .. } => {
            // Arrow types in simple params shouldn't happen, but handle gracefully
            quote! { Box<dyn std::any::Any> }
        }
        TypeExpr::MultiBinder(inner) => {
            // MultiBinder in simple context: Vec<T>
            let inner_type = type_expr_to_rust_type(inner);
            quote! { Vec<#inner_type> }
        }
    }
}

/// Convert TypeExpr to a Rust type (for use inside Box<>, etc.)
fn type_expr_to_rust_type(ty: &TypeExpr) -> TokenStream {
    match ty {
        TypeExpr::Base(ident) => {
            quote! { #ident }
        }
        TypeExpr::Collection { coll_type, element } => {
            let elem_type = type_expr_to_rust_type(element);
            match coll_type {
                CollectionType::HashBag => quote! { mettail_runtime::HashBag<#elem_type> },
                CollectionType::HashSet => quote! { std::collections::HashSet<#elem_type> },
                CollectionType::Vec => quote! { Vec<#elem_type> },
            }
        }
        TypeExpr::Arrow { domain, codomain } => {
            let dom = type_expr_to_rust_type(domain);
            let cod = type_expr_to_rust_type(codomain);
            quote! { (#dom -> #cod) }
        }
        TypeExpr::MultiBinder(inner) => {
            let inner_type = type_expr_to_rust_type(inner);
            quote! { Vec<#inner_type> }
        }
    }
}

fn generate_binder_variant(rule: &GrammarRule) -> TokenStream {
    let label = &rule.label;

    // For now, support single binder binding in single body
    // Future: support multiple binders and bodies
    let (binder_idx, body_indices) = &rule.bindings[0];
    let body_idx = body_indices[0];

    // Get the binder and body categories
    let _binder_cat = match &rule.items[*binder_idx] {
        GrammarItem::Binder { category } => category,
        _ => panic!("Binding index doesn't point to a Binder"),
    };

    let body_cat = match &rule.items[body_idx] {
        GrammarItem::NonTerminal(cat) => cat,
        _ => panic!("Body index doesn't point to a NonTerminal"),
    };

    let mut fields = Vec::new();

    for (i, item) in rule.items.iter().enumerate() {
        if i == *binder_idx {
            // Skip the binder - it's part of the Scope
            continue;
        }

        if i == body_idx {
            // This is the body - generate Scope
            fields.push(quote! {
                mettail_runtime::Scope<mettail_runtime::Binder<String>, Box<#body_cat>>
            });
        } else {
            // Regular field (comes before or after, but not binder or body)
            match item {
                GrammarItem::NonTerminal(cat) => {
                    if cat.to_string() == "Var" {
                        fields.push(quote! { mettail_runtime::Var<String> });
                    } else {
                        fields.push(quote! { Box<#cat> });
                    }
                },
                GrammarItem::Collection { coll_type, element_type, .. } => {
                    // Collection becomes a field with the appropriate collection type
                    let coll_type_ident = match coll_type {
                        CollectionType::HashBag => quote! { mettail_runtime::HashBag },
                        CollectionType::HashSet => quote! { std::collections::HashSet },
                        CollectionType::Vec => quote! { Vec },
                    };
                    fields.push(quote! { #coll_type_ident<#element_type> });
                },
                GrammarItem::Binder { .. } => {
                    // Should have been skipped above
                    panic!("Unexpected binder at position {}", i);
                },
                GrammarItem::Terminal(_) => {
                    // Terminals don't become fields
                },
            }
        }
    }

    // Generate the variant
    quote! {
        #label(#(#fields),*)
    }
}

/// For each constructor with a collection field, generates a helper function that automatically flattens nested collections of the same type.
fn generate_flatten_helpers(theory: &TheoryDef) -> TokenStream {
    use quote::format_ident;

    // Group rules by category
    let mut helpers_by_cat: HashMap<String, Vec<TokenStream>> = HashMap::new();

    for rule in &theory.terms {
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
    let impls: Vec<TokenStream> = theory
        .exports
        .iter()
        .filter_map(|export| {
            let cat_name = &export.name;
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
fn generate_normalize_functions(theory: &TheoryDef) -> TokenStream {
    use quote::format_ident;

    let mut impls = Vec::new();

    for export in &theory.exports {
        let category = &export.name;

        // Find all rules for this category
        let rules_for_category: Vec<_> = theory
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

        // Only generate normalize if this category has collections
        if !has_collections {
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

/// Generate eval() method for native types
fn generate_eval_method(theory: &TheoryDef) -> TokenStream {
    let mut impls = Vec::new();

    for export in &theory.exports {
        let category = &export.name;

        // Only generate for native types
        let native_type = match export.native_type.as_ref() {
            Some(ty) => ty,
            None => continue,
        };

        // Find all rules for this category
        let rules: Vec<&GrammarRule> = theory
            .terms
            .iter()
            .filter(|r| r.category == *category)
            .collect();

        if rules.is_empty() {
            continue;
        }

        // Build map of constructor -> semantic operation
        let mut semantics_map: HashMap<String, BuiltinOp> = HashMap::new();
        for semantic_rule in &theory.semantics {
            // Find the rule for this constructor
            if let Some(rule) = rules.iter().find(|r| r.label == semantic_rule.constructor) {
                if rule.category == *category {
                    let SemanticOperation::Builtin(op) = &semantic_rule.operation;
                    semantics_map.insert(semantic_rule.constructor.to_string(), *op);
                }
            }
        }

        // Generate match arms
        let mut match_arms = Vec::new();
        
        // Check for existing rules
        let has_integer_rule = rules.iter().any(|rule| is_integer_rule(rule));
        
        // Add arm for auto-generated NumLit if no explicit Integer rule
        if !has_integer_rule {
            let literal_label = super::generate_literal_label(native_type);
            match_arms.push(quote! {
                #category::#literal_label(n) => *n,
            });
        }
        
        // Add arm for auto-generated Var variant if no explicit Var rule
        let var_label = super::generate_var_label(category);
        let panic_msg = format!(
            "Cannot evaluate {} - variables must be substituted via rewrites first",
            var_label
        );
        match_arms.push(quote! {
            #category::#var_label(_) => loop { panic!(#panic_msg) },
        });

        for rule in &rules {
            let label = &rule.label;
            let label_str = label.to_string();

            // Check if this is an Integer rule (literal with native type)
            if is_integer_rule(rule) {
                match_arms.push(quote! {
                    #category::#label(n) => *n,
                });
            }
            // Check if this has semantics (operator)
            else if let Some(op) = semantics_map.get(&label_str) {
                // Count non-terminal arguments (excluding terminals)
                let arg_count = rule
                    .items
                    .iter()
                    .filter(|item| matches!(item, GrammarItem::NonTerminal(_)))
                    .count();

                if arg_count == 2 {
                    // Binary operator
                    let op_token = match op {
                        BuiltinOp::Add => quote! { + },
                        BuiltinOp::Sub => quote! { - },
                        BuiltinOp::Mul => quote! { * },
                        BuiltinOp::Div => quote! { / },
                        BuiltinOp::Rem => quote! { % },
                        BuiltinOp::BitAnd => quote! { & },
                        BuiltinOp::BitOr => quote! { | },
                        BuiltinOp::BitXor => quote! { ^ },
                        BuiltinOp::Shl => quote! { << },
                        BuiltinOp::Shr => quote! { >> },
                    };

                    match_arms.push(quote! {
                        #category::#label(a, b) => a.as_ref().eval() #op_token b.as_ref().eval(),
                    });
                } else {
                    // Unary or other arity - skip for now
                    continue;
                }
            }
            // Handle rules with recursive self-reference and Var (like Assign . Int ::= Var "=" Int)
            // These evaluate to the value of the recursive argument
            else {
                // Find non-terminals in the rule
                let non_terminals: Vec<_> = rule
                    .items
                    .iter()
                    .filter_map(|item| match item {
                        GrammarItem::NonTerminal(nt) => Some(nt.to_string()),
                        _ => None,
                    })
                    .collect();

                // Check if this has Var and a recursive reference
                let has_var = non_terminals.iter().any(|nt| nt == "Var");
                let has_recursive = non_terminals.iter().any(|nt| *nt == category.to_string());

                if has_var && has_recursive {
                    // This is like Assign - evaluate the recursive part
                    // The constructor has (OrdVar, Box<T>) where T is the recursive part
                    // Need to dereference the Box to call eval()
                    match_arms.push(quote! {
                        #category::#label(_, expr) => expr.as_ref().eval(),
                    });
                }
                // Other constructors without semantics - skip
            }
        }

        if !match_arms.is_empty() {
            let impl_block = quote! {
                impl #category {
                    /// Evaluate the expression to its native type value.
                    /// Variables must be substituted via rewrites before evaluation.
                    pub fn eval(&self) -> #native_type {
                        match self {
                            #(#match_arms)*
                            _ => panic!("Cannot evaluate expression - contains unevaluated terms. Apply rewrites first."),
                        }
                    }
                }
            };
            impls.push(impl_block);
        }
    }

    quote! {
        #(#impls)*
    }
}

/// Generate apply_rewrites_with_facts() method for categories with rewrites
fn generate_rewrite_application(theory: &TheoryDef) -> TokenStream {
    let mut impls = Vec::new();

    // Only generate if there are rewrite rules
    if theory.rewrites.is_empty() {
        return quote! {};
    }

    // Find categories that have rewrite rules
    let mut categories_with_rewrites = std::collections::HashSet::new();
    for rewrite in &theory.rewrites {
        // Extract category from LHS pattern
        if let Some(constructor) = rewrite.left.constructor_name() {
            // Find the rule for this constructor to get its category
            if let Some(rule) = theory.terms.iter().find(|r| &r.label == constructor) {
                categories_with_rewrites.insert(rule.category.to_string());
            }
        }
    }

    // Generate for each exported category that has rewrites
    for export in &theory.exports {
        let category = &export.name;
        let cat_str = category.to_string();

        if !categories_with_rewrites.contains(&cat_str) {
            continue;
        }

        // Check if there are EnvQuery conditions to determine fact type
        let has_env_query = theory.rewrites.iter().any(|rw| {
            rw.conditions
                .iter()
                .any(|c| matches!(c, Condition::EnvQuery { .. }))
        });

        if has_env_query {
            // Find all rules for this category to generate match arms
            let category_str = category.to_string();
            let category_rules: Vec<&GrammarRule> = theory
                .terms
                .iter()
                .filter(|r| r.category.to_string() == category_str)
                .collect();

            // Find VarRef rule and Integer rule for the rewrite
            // Look for any Var rule (not just "VarRef" - could be any name)
            let var_ref_rule = category_rules.iter().find(|r| is_var_rule(r));
            // Integer rule is the one that uses Integer keyword (for native type literals)
            let integer_rule = category_rules.iter().find(|r| is_integer_rule(r));

            // Use auto-generated labels if no explicit rules
            let integer_label: Option<syn::Ident> = integer_rule
                .map(|r| r.label.clone())
                .or_else(|| export.native_type.as_ref().map(super::generate_literal_label));
            let var_label: Option<syn::Ident> = var_ref_rule
                .map(|r| r.label.clone())
                .or_else(|| Some(super::generate_var_label(category)));

            // Generate match arms for all constructors
            let mut match_arms: Vec<TokenStream> = Vec::new();
            let category_str = category.to_string();
            
            // Add match arm for auto-generated Var variant if no explicit rule
            if var_ref_rule.is_none() {
                if let (Some(var_lbl), Some(int_lbl)) = (&var_label, &integer_label) {
                    match_arms.push(quote! {
                        #category::#var_lbl(ord_var) => {
                            let var_name: &str = match ord_var {
                                mettail_runtime::OrdVar(mettail_runtime::Var::Free(ref fv)) => {
                                    fv.pretty_name.as_deref()
                                        .ok_or_else(|| "Variable has no name".to_string())?
                                }
                                _ => return Err("Cannot substitute bound variable".to_string()),
                            };
                            let val = env.get(var_name)
                                .ok_or_else(|| format!("undefined variable: {}", var_name))?;
                            Ok(#category::#int_lbl(*val))
                        }
                    });
                }
            }
            
            // Add match arm for auto-generated NumLit variant if no explicit rule
            if integer_rule.is_none() {
                if let Some(int_lbl) = &integer_label {
                    match_arms.push(quote! {
                        #category::#int_lbl(n) => Ok(#category::#int_lbl(*n))
                    });
                }
            }

            for rule in &category_rules {
                let label = &rule.label;
                let label_str = label.to_string();

                // Check if this is VarRef - apply rewrite (explicit rule only, auto-generated handled above)
                let is_var_ref = var_ref_rule
                    .map(|vr| vr.label.to_string() == label_str)
                    .unwrap_or(false);

                if is_var_ref {
                    if let Some(ref int_lbl) = integer_label {
                        match_arms.push(quote! {
                            #category::#label(ord_var) => {
                                let var_name: &str = match ord_var {
                                    mettail_runtime::OrdVar(mettail_runtime::Var::Free(ref fv)) => {
                                        fv.pretty_name.as_deref()
                                            .ok_or_else(|| "Variable has no name".to_string())?
                                    }
                                    _ => return Err("Cannot substitute bound variable".to_string()),
                                };
                                let val = env.get(var_name)
                                    .ok_or_else(|| format!("undefined variable: {}", var_name))?;
                                Ok(#category::#int_lbl(*val))
                            }
                        });
                        continue;
                    }
                }

                // Check if this is an Integer rule - pass through (explicit rule only, auto-generated handled above)
                let is_integer = integer_rule
                    .map(|ir| ir.label.to_string() == label_str)
                    .unwrap_or(false);

                if is_integer {
                    match_arms.push(quote! {
                        #category::#label(n) => Ok(#category::#label(*n))
                    });
                    continue;
                }

                // For other constructors (Add, Sub, etc.), collect fields
                let all_fields: Vec<syn::Ident> = rule
                    .items
                    .iter()
                    .filter_map(|item| match item {
                        GrammarItem::NonTerminal(cat) => Some(cat.clone()),
                        GrammarItem::Collection { element_type, .. } => Some(element_type.clone()),
                        _ => None,
                    })
                    .collect();

                let field_count = all_fields.len();

                if field_count == 0 {
                    // Nullary constructor
                    match_arms.push(quote! {
                        #category::#label => Ok(#category::#label)
                    });
                } else {
                    // Constructor with fields - generate recursive match arm
                    let field_names: Vec<syn::Ident> = (0..field_count)
                        .map(|i| {
                            syn::Ident::new(&format!("f{}", i), proc_macro2::Span::call_site())
                        })
                        .collect();

                    // Generate reconstruction expressions for each field
                    let reconstructed: Vec<TokenStream> = all_fields.iter()
                        .enumerate()
                        .map(|(idx, field_cat)| {
                            let field_name = &field_names[idx];
                            let field_cat_str = field_cat.to_string();

                            if field_cat_str == category_str && field_cat_str != "Var" {
                                // Same category - recurse
                                quote! { Box::new(Self::substitute_vars_recursive(#field_name.as_ref(), env)?) }
                            } else {
                                // Different category or Var - just clone
                                quote! { #field_name.clone() }
                            }
                        })
                        .collect();

                    match_arms.push(quote! {
                        #category::#label(#(#field_names),*) => {
                            Ok(#category::#label(#(#reconstructed),*))
                        }
                    });
                }
            }

            // Ensure we have at least some match arms (should always have VarRef and NumLit at minimum)
            if match_arms.is_empty() {
                return quote! {
                    compile_error!("No match arms generated for category with env_var rewrites");
                };
            }

            // Generate function that accepts env_var facts: (String, i32)
            let impl_block = quote! {
                impl #category {
                    /// Apply rewrites using environment facts.
                    /// Returns the normal form (most reduced term) after applying all rewrites.
                    ///
                    /// Implements the rewrite rule: if env_var(x, v) then (VarRef x) => (NumLit v)
                    pub fn apply_rewrites_with_facts<I>(&self, facts: I) -> Result<#category, String>
                    where
                        I: IntoIterator<Item = (String, i32)>,
                    {
                        // Convert facts to HashMap for efficient lookup
                        use std::collections::HashMap;
                        let env: HashMap<String, i32> = facts.into_iter().collect();

                        // Apply rewrites recursively
                        Self::substitute_vars_recursive(self, &env)
                    }

                    /// Recursively substitute variables using environment facts
                    /// Implements the rewrite rule: if env_var(x, v) then (VarRef x) => (NumLit v)
                    fn substitute_vars_recursive(term: &#category, env: &HashMap<String, i32>) -> Result<#category, String> {
                        match term {
                            #(#match_arms),*
                        }
                    }
                }
            };
            impls.push(impl_block);
        }
    }

    quote! {
        #(#impls)*
    }
}

/// Extract the category from a rewrite rule (from LHS)
/// Internal helper function for environment generation
fn extract_category_from_rewrite_internal(
    rewrite: &RewriteRule,
    theory: &TheoryDef,
) -> Option<proc_macro2::Ident> {
    // Try to extract category from LHS pattern
    if let Some(constructor) = rewrite.left.constructor_name() {
            // Find the rule with this constructor
            theory
                .terms
                .iter()
            .find(|r| &r.label == constructor)
                .map(|rule| rule.category.clone())
    } else {
        None
    }
}

/// Generate variable category inference methods for lambda type checking
/// 
/// For each category, generates a method that finds what category a variable
/// is used as within that term. Used by the parser to select the correct
/// Lam{Domain} variant based on how the binder is used in the body.
fn generate_var_category_inference(theory: &TheoryDef) -> TokenStream {
    // Get non-native categories
    let categories: Vec<_> = theory.exports.iter()
        .filter(|e| e.native_type.is_none())
        .collect();
    
    if categories.is_empty() {
        return quote! {};
    }
    
    // Generate an enum for the possible categories
    let cat_variants: Vec<TokenStream> = categories.iter()
        .map(|e| {
            let name = &e.name;
            quote! { #name }
        })
        .collect();
    
    let cat_names: Vec<_> = categories.iter().map(|e| &e.name).collect();
    
    // Generate the inference method for each category
    let impls: Vec<TokenStream> = categories.iter().map(|export| {
        let cat_name = &export.name;
        
        // Get rules for this category
        let rules: Vec<_> = theory.terms.iter()
            .filter(|r| r.category == *cat_name)
            .collect();
        
        // Generate match arms for each constructor
        let mut match_arms: Vec<TokenStream> = rules.iter().filter_map(|rule| {
            generate_var_inference_arm(rule, &cat_names, theory)
        }).collect();
        
        // Add arm for Var variant - if variable name matches, return this category
        let var_label = generate_var_label(cat_name);
        let cat_name_str = cat_name.to_string();
        match_arms.push(quote! {
            #cat_name::#var_label(mettail_runtime::OrdVar(mettail_runtime::Var::Free(ref fv))) => {
                if fv.pretty_name.as_deref() == Some(var_name) {
                    return Some(VarCategory::#cat_name);
                }
                None
            }
        });
        
        // Add wildcard arm for other variants (lambdas, etc.)
        match_arms.push(quote! {
            _ => None
        });
        
        quote! {
            impl #cat_name {
                /// Find what category a variable is used as in this term
                pub fn infer_var_category(&self, var_name: &str) -> Option<VarCategory> {
                    match self {
                        #(#match_arms),*
                    }
                }
            }
        }
    }).collect();
    
    quote! {
        /// Enum representing possible variable categories for type inference
        #[derive(Debug, Clone, Copy, PartialEq, Eq)]
        pub enum VarCategory {
            #(#cat_variants),*
        }
        
        #(#impls)*
    }
}

/// Field kind for inference generation
#[derive(Clone)]
enum InferFieldKind {
    Simple,          // Regular field
    HashBag,         // HashBag collection (iter returns (&T, usize))
    Vec,             // Vec collection (iter returns &T)
    Binder,          // Scope with single binder
    MultiBinder,     // Scope with multiple binders
}

/// Generate a match arm for variable inference in a constructor
fn generate_var_inference_arm(
    rule: &GrammarRule,
    all_cats: &[&syn::Ident],
    _theory: &TheoryDef,
) -> Option<TokenStream> {
    let category = &rule.category;
    let label = &rule.label;
    
    // Skip Var rules (handled separately)
    if is_var_rule(rule) {
        return None;
    }
    
    // Get field info from term_context or bindings
    let fields: Vec<(syn::Ident, syn::Ident, InferFieldKind)> = if let Some(ctx) = &rule.term_context {
        ctx.iter().enumerate().filter_map(|(i, param)| {
            let field_name = syn::Ident::new(&format!("f{}", i), proc_macro2::Span::call_site());
            match param {
                TermParam::Simple { ty, .. } => {
                    let field_cat = extract_base_cat(ty);
                    if all_cats.iter().any(|c| c.to_string() == field_cat.to_string()) {
                        let kind = match ty {
                            TypeExpr::Collection { coll_type: CollectionType::HashBag, .. } => InferFieldKind::HashBag,
                            TypeExpr::Collection { coll_type: CollectionType::Vec, .. } => InferFieldKind::Vec,
                            TypeExpr::Collection { coll_type: CollectionType::HashSet, .. } => InferFieldKind::Vec, // HashSet iter is like Vec
                            _ => InferFieldKind::Simple,
                        };
                        Some((field_name, field_cat, kind))
                    } else {
                        None
                    }
                }
                TermParam::Abstraction { ty, .. } => {
                    // For binders, we need to check the body inside the scope
                    let body_cat = extract_base_cat(ty);
                    if all_cats.iter().any(|c| c.to_string() == body_cat.to_string()) {
                        Some((field_name, body_cat, InferFieldKind::Binder))
                    } else {
                        None
                    }
                }
                TermParam::MultiAbstraction { ty, .. } => {
                    let body_cat = extract_base_cat(ty);
                    if all_cats.iter().any(|c| c.to_string() == body_cat.to_string()) {
                        Some((field_name, body_cat, InferFieldKind::MultiBinder))
                    } else {
                        None
                    }
                }
            }
        }).collect()
    } else {
        // Old syntax - use items
        rule.items.iter().enumerate().filter_map(|(i, item)| {
            let field_name = syn::Ident::new(&format!("f{}", i), proc_macro2::Span::call_site());
            match item {
                GrammarItem::NonTerminal(nt) => {
                    if all_cats.iter().any(|c| c.to_string() == nt.to_string()) {
                        Some((field_name, nt.clone(), InferFieldKind::Simple))
                    } else {
                        None
                    }
                }
                GrammarItem::Collection { element_type, coll_type, .. } => {
                    if all_cats.iter().any(|c| c.to_string() == element_type.to_string()) {
                        let kind = match coll_type {
                            CollectionType::HashBag => InferFieldKind::HashBag,
                            CollectionType::Vec => InferFieldKind::Vec,
                            CollectionType::HashSet => InferFieldKind::Vec,
                        };
                        Some((field_name, element_type.clone(), kind))
                    } else {
                        None
                    }
                }
                GrammarItem::Binder { category, .. } => {
                    if all_cats.iter().any(|c| c.to_string() == category.to_string()) {
                        Some((field_name, category.clone(), InferFieldKind::Binder))
                    } else {
                        None
                    }
                }
                _ => None,
            }
        }).collect()
    };
    
    if fields.is_empty() {
        // No recursive fields - check if this is a unit variant
        let has_any_fields = if let Some(ctx) = &rule.term_context {
            !ctx.is_empty()
        } else {
            !rule.items.iter().all(|i| matches!(i, GrammarItem::Terminal(_)))
        };
        
        return Some(if has_any_fields {
            quote! { #category::#label(..) => None }
        } else {
            quote! { #category::#label => None }
        });
    }
    
    // Generate pattern and recursive calls
    let field_patterns: Vec<TokenStream> = fields.iter().map(|(name, _, _)| {
        quote! { ref #name }
    }).collect();
    
    let recursive_calls: Vec<TokenStream> = fields.iter().map(|(name, _field_cat, kind)| {
        match kind {
            InferFieldKind::HashBag => {
                // HashBag.iter() returns (&T, usize), need to extract element
                quote! {
                    for (item, _count) in #name.iter() {
                        if let Some(cat) = item.infer_var_category(var_name) {
                            return Some(cat);
                        }
                    }
                }
            }
            InferFieldKind::Vec => {
                // Vec.iter() returns &T
                quote! {
                    for item in #name.iter() {
                        if let Some(cat) = item.infer_var_category(var_name) {
                            return Some(cat);
                        }
                    }
                }
            }
            InferFieldKind::Binder => {
                // Scope - access the body via unsafe_body()
                quote! {
                    if let Some(cat) = #name.unsafe_body().infer_var_category(var_name) {
                        return Some(cat);
                    }
                }
            }
            InferFieldKind::MultiBinder => {
                // Same as Binder
                quote! {
                    if let Some(cat) = #name.unsafe_body().infer_var_category(var_name) {
                        return Some(cat);
                    }
                }
            }
            InferFieldKind::Simple => {
                quote! {
                    if let Some(cat) = #name.infer_var_category(var_name) {
                        return Some(cat);
                    }
                }
            }
        }
    }).collect();
    
    Some(quote! {
        #category::#label(#(#field_patterns),*) => {
            #(#recursive_calls)*
            None
        }
    })
}

/// Extract the base category from a type expression
fn extract_base_cat(ty: &TypeExpr) -> syn::Ident {
    match ty {
        TypeExpr::Base(ident) => ident.clone(),
        TypeExpr::Collection { element, .. } => extract_base_cat(element),
        TypeExpr::Arrow { codomain, .. } => extract_base_cat(codomain),
        TypeExpr::MultiBinder(inner) => extract_base_cat(inner),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use syn::parse_quote;

    #[test]
    fn test_generate_simple_enum() {
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
                    label: parse_quote!(Plus),
                    category: parse_quote!(Elem),
                    items: vec![
                        GrammarItem::NonTerminal(parse_quote!(Elem)),
                        GrammarItem::Terminal("+".to_string()),
                        GrammarItem::NonTerminal(parse_quote!(Elem)),
                    ],
                    bindings: vec![],
                    term_context: None,
                    syntax_pattern: None,
                },
            ],
            equations: vec![],
            rewrites: vec![],
            semantics: vec![],
        };

        let output = generate_ast(&theory);

        // Check that it generates valid Rust code
        println!("Generated: {}", output);
        assert!(output.to_string().contains("enum Elem"));
        assert!(output.to_string().contains("Zero"));
        assert!(output.to_string().contains("Plus"));
    }

    #[test]
    fn test_generate_multiple_categories() {
        let theory = TheoryDef {
            name: parse_quote!(Test),
            params: vec![],
            exports: vec![
                Export {
                    name: parse_quote!(Proc),
                    native_type: None,
                },
                Export {
                    name: parse_quote!(Name),
                    native_type: None,
                },
            ],
            terms: vec![
                GrammarRule {
                    label: parse_quote!(PZero),
                    category: parse_quote!(Proc),
                    items: vec![GrammarItem::Terminal("0".to_string())],
                    bindings: vec![],
                    term_context: None,
                    syntax_pattern: None,
                },
                GrammarRule {
                    label: parse_quote!(NQuote),
                    category: parse_quote!(Name),
                    items: vec![
                        GrammarItem::Terminal("@".to_string()),
                        GrammarItem::NonTerminal(parse_quote!(Proc)),
                    ],
                    bindings: vec![],
                    term_context: None,
                    syntax_pattern: None,
                },
            ],
            equations: vec![],
            rewrites: vec![],
            semantics: vec![],
        };

        let output = generate_ast(&theory);

        println!("Generated: {}", output);
        assert!(output.to_string().contains("enum Proc"));
        assert!(output.to_string().contains("enum Name"));
    }

    #[test]
    fn test_automatic_var_generation() {
        // Tests theory without Var rules - they should be automatically generated
        let theory = TheoryDef {
            name: parse_quote!(Test),
            params: vec![],
            exports: vec![
                Export {
                    name: parse_quote!(Proc),
                    native_type: None,
                },
                Export {
                    name: parse_quote!(Name),
                    native_type: None,
                },
                Export {
                    name: parse_quote!(Term),
                    native_type: None,
                },
            ],
            terms: vec![
                GrammarRule {
                    label: parse_quote!(PZero),
                    category: parse_quote!(Proc),
                    items: vec![GrammarItem::Terminal("0".to_string())],
                    bindings: vec![],
                    term_context: None,
                    syntax_pattern: None,
                },
                GrammarRule {
                    label: parse_quote!(NQuote),
                    category: parse_quote!(Name),
                    items: vec![
                        GrammarItem::Terminal("@".to_string()),
                        GrammarItem::NonTerminal(parse_quote!(Proc)),
                    ],
                    bindings: vec![],
                    term_context: None,
                    syntax_pattern: None,
                },
                // No Var rules explicitly defined
            ],
            equations: vec![],
            rewrites: vec![],
            semantics: vec![],
        };

        let output = generate_ast(&theory);
        let output_str = output.to_string();

        println!("Generated AST:\n{}", output_str);

        // Checks that Var variants are automatically generated for each exported category
        // Looks for the enum definitions and verify they contain Var variants
        // Proc -> PVar
        let proc_enum_start = output_str.find("pub enum Proc").unwrap_or(0);
        let proc_enum_end = output_str[proc_enum_start..]
            .find("impl")
            .unwrap_or(output_str.len() - proc_enum_start);
        let proc_enum_section = &output_str[proc_enum_start..proc_enum_start + proc_enum_end];
        assert!(
            proc_enum_section.contains("PVar") && proc_enum_section.contains("OrdVar"),
            "Expected PVar variant for Proc category in enum definition"
        );

        // Name -> NVar
        let name_enum_start = output_str.find("pub enum Name").unwrap_or(0);
        let name_enum_end = output_str[name_enum_start..]
            .find("impl")
            .unwrap_or(output_str.len() - name_enum_start);
        let name_enum_section = &output_str[name_enum_start..name_enum_start + name_enum_end];
        assert!(
            name_enum_section.contains("NVar") && name_enum_section.contains("OrdVar"),
            "Expected NVar variant for Name category in enum definition"
        );

        // Term -> TVar
        let term_enum_start = output_str.find("pub enum Term").unwrap_or(0);
        let term_enum_end = output_str[term_enum_start..]
            .find("impl")
            .unwrap_or(output_str.len() - term_enum_start);
        let term_enum_section = &output_str[term_enum_start..term_enum_start + term_enum_end];
        assert!(
            term_enum_section.contains("TVar") && term_enum_section.contains("OrdVar"),
            "Expected TVar variant for Term category in enum definition"
        );

        // Verify the enum structure exists
        assert!(output_str.contains("enum Proc"));
        assert!(output_str.contains("enum Name"));
        assert!(output_str.contains("enum Term"));
    }

    #[test]
    fn test_automatic_var_generation_with_existing_var() {
        // Tests that if a Var rule already exists, we don't generate a duplicate
        let theory = TheoryDef {
            name: parse_quote!(Test),
            params: vec![],
            exports: vec![Export {
                name: parse_quote!(Proc),
                native_type: None,
            }],
            terms: vec![
                GrammarRule {
                    label: parse_quote!(PZero),
                    category: parse_quote!(Proc),
                    items: vec![GrammarItem::Terminal("0".to_string())],
                    bindings: vec![],
                    term_context: None,
                    syntax_pattern: None,
                },
                GrammarRule {
                    label: parse_quote!(PVar),
                    category: parse_quote!(Proc),
                    items: vec![GrammarItem::NonTerminal(parse_quote!(Var))],
                    bindings: vec![],
                    term_context: None,
                    syntax_pattern: None,
                },
                // Var rule explicitly defined
            ],
            equations: vec![],
            rewrites: vec![],
            semantics: vec![],
        };

        let output = generate_ast(&theory);
        let output_str = output.to_string();

        println!("Generated AST:\n{}", output_str);

        // Should have exactly one PVar variant in the enum definition (the explicitly defined one)
        // Finds the enum definition section
        let proc_enum_start = output_str.find("pub enum Proc").unwrap_or(0);
        let proc_enum_end = output_str[proc_enum_start..]
            .find("impl")
            .unwrap_or(output_str.len() - proc_enum_start);
        let proc_enum_section = &output_str[proc_enum_start..proc_enum_start + proc_enum_end];

        // Counts PVar in the enum definition only
        let pvar_in_enum = proc_enum_section.matches("PVar").count();
        assert_eq!(
            pvar_in_enum, 1,
            "Expected exactly one PVar variant in enum definition, found {}",
            pvar_in_enum
        );
        assert!(
            proc_enum_section.contains("PVar") && proc_enum_section.contains("OrdVar"),
            "Expected PVar variant in enum definition"
        );
    }
}
