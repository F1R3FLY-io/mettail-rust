use crate::ascent::congruence;
use crate::ast::{Expr, TheoryDef};
use crate::utils::{has_native_type, native_type_to_string};
use proc_macro2::TokenStream;
use quote::quote;
use std::collections::HashMap;

/// Generate RHS construction for Ascent clause
pub fn generate_ascent_rhs(
    expr: &Expr,
    bindings: &HashMap<String, TokenStream>,
    theory: &TheoryDef,
) -> TokenStream {
    match expr {
        Expr::CollectionPattern { .. } => {
            // If we reach here, it's a bare collection pattern (not inside Apply)
            // Fall back to no-flatten version
            generate_ascent_collection_rhs(expr, bindings, theory, None)
        },
        _ => generate_rhs_construction(expr, bindings, theory),
    }
}

/// Generate RHS for collection patterns, optionally using flatten helper
///
/// If `constructor_context` is Some((category, label)), uses the flatten helper.
/// Otherwise, uses plain `bag.insert`.
fn generate_ascent_collection_rhs(
    expr: &Expr,
    bindings: &HashMap<String, TokenStream>,
    theory: &TheoryDef,
    constructor_context: Option<(syn::Ident, syn::Ident)>,
) -> TokenStream {
    if let Expr::CollectionPattern { constructor: _, elements, rest } = expr {
        let elem_constructions: Vec<TokenStream> = elements
            .iter()
            .map(|e| generate_rhs_construction(e, bindings, theory))
            .collect();

        let coll_type = quote! { mettail_runtime::HashBag };

        if let Some((category, label)) = constructor_context {
            // Use flatten helper
            let helper_name =
                quote::format_ident!("insert_into_{}", label.to_string().to_lowercase());

            if let Some(rest_var) = rest {
                // Merge rest with new elements using flatten helper
                let rest_var_name = rest_var.to_string();
                let rest_binding = bindings.get(&rest_var_name).unwrap_or_else(|| {
                    panic!(
                        "Rest variable '{}' not bound. Available bindings: {:?}",
                        rest_var_name,
                        bindings.keys().collect::<Vec<_>>()
                    )
                });

                quote! {
                    {
                        let mut bag = (#rest_binding).clone();
                        #(#category::#helper_name(&mut bag, #elem_constructions);)*
                        bag
                    }
                }
            } else {
                // Build from elements using flatten helper
                quote! {
                    {
                        let mut bag = #coll_type::new();
                        #(#category::#helper_name(&mut bag, #elem_constructions);)*
                        bag
                    }
                }
            }
        } else {
            // No constructor context - use plain insert (shouldn't flatten)
            if let Some(rest_var) = rest {
                let rest_var_name = rest_var.to_string();
                let rest_binding = bindings.get(&rest_var_name).unwrap_or_else(|| {
                    panic!(
                        "Rest variable '{}' not bound. Available bindings: {:?}",
                        rest_var_name,
                        bindings.keys().collect::<Vec<_>>()
                    )
                });

                quote! {
                    {
                        let mut bag = (#rest_binding).clone();
                        #(bag.insert(#elem_constructions);)*
                        bag
                    }
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
    } else {
        panic!("generate_ascent_collection_rhs called on non-CollectionPattern");
    }
}

/// Generate RHS construction recursively
///
/// Handles Variables, Apply, Subst, and nested CollectionPatterns.
/// Made public for use in congruence generation.
pub fn generate_rhs_construction(
    expr: &Expr,
    bindings: &HashMap<String, TokenStream>,
    theory: &TheoryDef,
) -> TokenStream {
    match expr {
        Expr::Var(var) => {
            let var_name = var.to_string();
            if let Some(binding) = bindings.get(&var_name) {
                // The binding already includes .clone() if needed
                // If it's a Box type, we need to get the contents
                // For now, just use the binding as-is - the binding should already produce the right type
                quote! { #binding }
            } else {
                // Unbound variable - check if it's a constructor
                if let Some(rule) = theory.terms.iter().find(|r| r.label == *var) {
                    // It's a nullary constructor - qualify it
                    let category = &rule.category;
                    quote! { #category::#var }
                } else {
                    // Unknown identifier - this shouldn't happen
                    panic!("Unbound variable '{}' in RHS", var_name);
                }
            }
        },

        Expr::Apply { constructor, args } => {
            let category = congruence::extract_category(expr, theory).unwrap();

            // Check if this category has a native type - if so, we might need special handling
            let native_type_opt = has_native_type(&category, theory);

            // Check if this constructor has collection fields
            let grammar_rule = theory
                .terms
                .iter()
                .find(|r| r.label == *constructor && r.category == category);

            // Check if this is a NumLit constructor for a native type
            // If so, and if args are variables, we might need to evaluate them
            let is_native_literal =
                native_type_opt.is_some() && *constructor == "NumLit" && args.len() == 1;

            let rhs_args: Vec<TokenStream> = args
                .iter()
                .enumerate()
                .map(|(i, arg)| {
                    // Check if this argument position corresponds to a Collection field
                    let is_collection_field = grammar_rule
                        .and_then(|rule| {
                            rule.items
                                .iter()
                                .filter(|item| {
                                    matches!(
                                        item,
                                        crate::ast::GrammarItem::NonTerminal(_)
                                            | crate::ast::GrammarItem::Collection { .. }
                                    )
                                })
                                .nth(i)
                        })
                        .map(|item| matches!(item, crate::ast::GrammarItem::Collection { .. }))
                        .unwrap_or(false);

                    // For collection fields, pass the constructor label so flatten helper can be used
                    let inner =
                        if is_collection_field && matches!(arg, Expr::CollectionPattern { .. }) {
                            generate_ascent_collection_rhs(
                                arg,
                                bindings,
                                theory,
                                Some((category.clone(), constructor.clone())),
                            )
                        } else {
                            generate_ascent_rhs(arg, bindings, theory)
                        };

                    // Special handling for native type NumLit: if arg is a variable bound to a native value,
                    // use it directly (it's already the native type from env_var relation)
                    // Note: For EnvQuery bindings, the value is already the native type (i32), not an Int enum
                    // We need to mark this so we don't wrap it in Box::new
                    let is_native_value_binding = is_native_literal
                        && i == 0
                        && matches!(arg, Expr::Var(_))
                        && bindings.contains_key(&{
                            if let Expr::Var(var) = arg {
                                var.to_string()
                            } else {
                                String::new()
                            }
                        });

                    // Check if this argument position corresponds to a Var field
                    // Var fields are stored as OrdVar, not Box<OrdVar>, so don't wrap
                    let is_var_field = grammar_rule
                        .and_then(|rule| {
                            rule.items
                                .iter()
                                .filter(|item| {
                                    matches!(item, crate::ast::GrammarItem::NonTerminal(_))
                                })
                                .nth(i)
                        })
                        .and_then(|item| {
                            if let crate::ast::GrammarItem::NonTerminal(cat) = item {
                                Some(*cat == "Var")
                            } else {
                                None
                            }
                        })
                        .unwrap_or(false);

                    // Don't wrap collection fields, native value bindings, or Var fields in Box::new
                    if is_collection_field || is_native_value_binding || is_var_field {
                        inner
                    } else {
                        quote! { Box::new(#inner) }
                    }
                })
                .collect();

            // If this is NumLit for native type and we have a single native value, construct directly
            if is_native_literal && rhs_args.len() == 1 {
                if let Some(native_type) = native_type_opt {
                    let type_str = native_type_to_string(native_type);
                    if type_str == "i32" || type_str == "i64" {
                        // For integer types, NumLit takes the native value directly
                        let native_val = &rhs_args[0];
                        return quote! {
                            #category::NumLit(#native_val)
                        };
                    }
                }
            }

            quote! {
                #category::#constructor(#(#rhs_args),*)
            }
        },

        Expr::Subst { term, var, replacement } => {
            let term_rhs = generate_ascent_rhs(term, bindings, theory);
            let var_name = var.to_string();
            let var_binding = bindings.get(&var_name).unwrap_or_else(|| {
                panic!(
                    "Substitution variable '{}' not bound. Available bindings: {:?}",
                    var_name,
                    bindings.keys().collect::<Vec<_>>()
                )
            });
            let replacement_rhs = generate_ascent_rhs(replacement, bindings, theory);

            // Determine the category of the replacement to call the right substitute method
            let replacement_category = congruence::extract_category(replacement, theory)
                .unwrap()
                .to_string()
                .to_lowercase();
            let subst_method = quote::format_ident!("substitute_{}", replacement_category);

            quote! {
                (#term_rhs).#subst_method(&#var_binding.0, &#replacement_rhs)
            }
        },

        Expr::CollectionPattern { .. } => {
            // This should have been handled at the top level by generate_ascent_rhs
            panic!("CollectionPattern should be handled by generate_ascent_rhs/generate_ascent_collection_rhs");
        },

        Expr::Lambda { .. } | Expr::MultiLambda { .. } => {
            panic!("Lambda expressions in RHS not yet supported - use definitions block");
        },
    }
}
