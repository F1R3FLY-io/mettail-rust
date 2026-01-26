#![allow(clippy::cmp_owned, clippy::single_match)]

use super::{
    display, generate_literal_label, generate_var_label, has_assign_rule, is_integer_rule,
    is_var_rule, subst, termgen,
};
use crate::ast::{BuiltinOp, GrammarItem, GrammarRule, TheoryDef};
use crate::utils::has_native_type;
use proc_macro2::TokenStream;
use quote::quote;
use std::collections::HashMap;

pub fn generate_ast(theory: &TheoryDef) -> TokenStream {
    let ast_enums = generate_ast_enums(theory);
    let flatten_helpers = generate_flatten_helpers(theory);
    let normalize_impl = generate_normalize_functions(theory);
    let subst_impl = subst::generate_substitution(theory);
    let display_impl = display::generate_display(theory);
    let generation_impl = termgen::generate_term_generation(theory);
    let random_gen_impl = termgen::generate_random_generation(theory);
    let eval_impl = generate_eval_method(theory);
    let rewrite_impl = generate_rewrite_application(theory);
    let env_impl = generate_env_infrastructure(theory);

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

        #display_impl

        #generation_impl

        #random_gen_impl

        #eval_impl

        #rewrite_impl

        #env_impl

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

        // Check if there's already a Var rule
        let has_var_rule = rules.iter().any(|rule| is_var_rule(rule));
        // Check if there's already an Integer/literal rule
        let has_integer_rule = rules.iter().any(|rule| is_integer_rule(rule));

        let mut variants: Vec<TokenStream> = rules.iter().map(|rule| {
            generate_variant(rule, theory)
        }).collect();

        // Auto-generate literal variant for native types (if not explicitly declared)
        if let Some(native_type) = has_native_type(cat_name, theory) {
            if !has_integer_rule {
                let literal_label = generate_literal_label(native_type);
                let native_type_cloned = native_type.clone();

                variants.push(quote! {
                    #literal_label(#native_type_cloned)
                });
            }
        }

        // Auto-generate Var variant for ALL categories (native and non-native)
        if !has_var_rule {
            let var_label = generate_var_label(cat_name);

            variants.push(quote! {
                #var_label(mettail_runtime::OrdVar)
            });
        }

        // Automatically add Assign variant if it doesn't already exist
        let has_assign = has_assign_rule(cat_name, theory);
        if !has_assign {
            variants.push(quote! {
                Assign(mettail_runtime::OrdVar, Box<#cat_name>)
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

    // Check if this rule has bindings
    if !rule.bindings.is_empty() {
        // This constructor has binders - generate Scope type
        return generate_binder_variant(rule);
    }

    // Count non-terminal and collection items (these become fields)
    #[derive(Clone)]
    enum FieldType {
        NonTerminal(syn::Ident),
        Collection {
            coll_type: crate::ast::CollectionType,
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
                    crate::ast::CollectionType::HashBag => quote! { mettail_runtime::HashBag },
                    crate::ast::CollectionType::HashSet => quote! { std::collections::HashSet },
                    crate::ast::CollectionType::Vec => quote! { Vec },
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
                        crate::ast::CollectionType::HashBag => quote! { mettail_runtime::HashBag },
                        crate::ast::CollectionType::HashSet => quote! { std::collections::HashSet },
                        crate::ast::CollectionType::Vec => quote! { Vec },
                    };
                    quote! { #coll_type_ident<#element_type> }
                },
            })
            .collect();

        quote! { #label(#(#field_types),*) }
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
                        crate::ast::CollectionType::HashBag => quote! { mettail_runtime::HashBag },
                        crate::ast::CollectionType::HashSet => quote! { std::collections::HashSet },
                        crate::ast::CollectionType::Vec => quote! { Vec },
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
        // Check if this rule has a collection field
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

                // Check if this is a collection constructor
                let is_collection = rule
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
                    let crate::ast::SemanticOperation::Builtin(op) = &semantic_rule.operation;
                    semantics_map.insert(semantic_rule.constructor.to_string(), *op);
                }
            }
        }

        // Generate match arms
        let mut match_arms = Vec::new();

        // Check if there's an auto-generated literal (for native types without explicit Integer rule)
        let has_integer_rule = rules.iter().any(|rule| is_integer_rule(rule));
        if let Some(native_type) = has_native_type(category, theory) {
            if !has_integer_rule {
                let literal_label = generate_literal_label(native_type);
                match_arms.push(quote! {
                    #category::#literal_label(n) => *n,
                });
            }
        }

        for rule in &rules {
            let label = &rule.label;
            let label_str = label.to_string();

            // Check if this is an Integer rule (literal with native type)
            if is_integer_rule(rule) {
                match_arms.push(quote! {
                    #category::#label(n) => *n,
                });
            }
            // Check if this is a Var rule (auto-generated or explicit)
            else if is_var_rule(rule) {
                // Use loop { panic!() } idiom for proper `!` type handling in quote!
                let panic_msg = format!(
                    "Cannot evaluate {} - variables must be substituted via rewrites first",
                    label
                );
                match_arms.push(quote! {
                    #category::#label(_) => loop { panic!(#panic_msg) },
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
        // Extract category from LHS expression
        if let crate::ast::Expr::Apply { constructor, .. } = &rewrite.left {
            // Find the rule for this constructor to get its category
            if let Some(rule) = theory.terms.iter().find(|r| r.label == *constructor) {
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
                .any(|c| matches!(c, crate::ast::Condition::EnvQuery { .. }))
        });

        if has_env_query {
            // Find all rules for this category to generate match arms
            let category_str = category.to_string();
            let category_rules: Vec<&GrammarRule> = theory
                .terms
                .iter()
                .filter(|r| r.category.to_string() == category_str)
                .collect();

            // Find Var rule and Integer/literal rule for the rewrite
            // Look for any Var rule (auto-generated or explicit)
            let var_ref_rule = category_rules.iter().find(|r| is_var_rule(r));
            // Integer rule is the one that uses Integer keyword (for native type literals)
            // Or use auto-generated literal label if no explicit rule
            let integer_rule = category_rules.iter().find(|r| is_integer_rule(r));
            let integer_label = integer_rule
                .map(|rule| rule.label.clone())
                .or_else(|| has_native_type(category, theory).map(generate_literal_label));

            // Generate match arms for all constructors
            let mut match_arms: Vec<TokenStream> = Vec::new();
            let category_str = category.to_string();

            for rule in &category_rules {
                let label = &rule.label;
                let label_str = label.to_string();

                // Check if this is a Var rule - apply rewrite
                let is_var_ref = var_ref_rule
                    .map(|vr| vr.label.to_string() == label_str)
                    .unwrap_or(false);

                if is_var_ref {
                    if let Some(ref int_label) = integer_label {
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
                                Ok(#category::#int_label(*val))
                            }
                        });
                        continue;
                    }
                }

                // Check if this is an Integer rule - pass through (has native type value)
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

            // Ensure we have at least some match arms (should always have Var and NumLit at minimum)
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
                    /// Implements the rewrite rule: if env_var(x, v) then (Var x) => (NumLit v)
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
                    /// Implements the rewrite rule: if env_var(x, v) then (Var x) => (NumLit v)
                    fn substitute_vars_recursive(term: &#category, env: &std::collections::HashMap<String, i32>) -> Result<#category, String> {
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

/// Generate environment infrastructure for all theories
///
/// This generates environment structs for ALL exported categories (automatically):
/// - Environment struct (e.g., CalculatorIntEnv, RhoCalcProcEnv)
/// - Environment methods (new, set, get, clear)
/// - env_to_facts helper function
///
/// This enables automatic assignment and variable retrieval for every category.
fn generate_env_infrastructure(theory: &TheoryDef) -> TokenStream {
    use quote::format_ident;

    // Generate environment infrastructure for each exported category
    // Simply use the category name directly - no need to worry about native vs custom types
    let mut env_structs = Vec::new();

    for export in &theory.exports {
        let category = &export.name;
        let theory_name = &theory.name;
        // Generate environment struct name: TheoryNameCategoryEnv
        // e.g., CalculatorIntEnv, RhoCalcProcEnv
        let env_name = format_ident!("{}{}Env", theory_name, category);

        // Use category name directly - works for both native and custom types
        // For native types like Int = ![i32], Rust will use the type alias correctly
        // For custom types like Proc, it uses the enum type
        let value_type = category.clone();

        env_structs.push(quote! {
            /// Environment for storing variable bindings
            #[derive(Debug, Clone)]
            pub struct #env_name {
                vars: std::collections::HashMap<String, #value_type>,
            }

            impl #env_name {
                /// Create a new empty environment
                pub fn new() -> Self {
                    #env_name {
                        vars: std::collections::HashMap::new(),
                    }
                }

                /// Store a variable binding
                pub fn set(&mut self, name: String, value: #value_type) {
                    self.vars.insert(name, value);
                }

                /// Look up a variable value
                pub fn get(&self, name: &str) -> Option<#value_type> {
                    self.vars.get(name).cloned()
                }

                /// Clear all bindings
                pub fn clear(&mut self) {
                    self.vars.clear();
                }

                /// Convert environment to Ascent input facts
                /// Returns a vector of (variable_name, value) tuples
                pub fn env_to_facts(&self) -> Vec<(String, #value_type)> {
                    self.vars.iter().map(|(name, val)| (name.clone(), val.clone())).collect()
                }
            }

            impl Default for #env_name {
                fn default() -> Self {
                    Self::new()
                }
            }
        });
    }

    // Generate parse_and_eval_with_env function for native type categories
    let mut parse_eval_fns = Vec::new();
    for export in &theory.exports {
        if let Some(native_type) = &export.native_type {
            let category = &export.name;
            let theory_name = &theory.name;
            let env_name = format_ident!("{}{}Env", theory_name, category);
            let cat_str = category.to_string().to_lowercase();
            let theory_name_lower = theory_name.to_string().to_lowercase();
            let parser_module = format_ident!("{}", theory_name_lower);
            let parser_name = format_ident!("{}Parser", category);
            let source_name = format_ident!("{}_source", theory_name_lower);
            let env_rel_name = format_ident!("env_var_{}", cat_str);
            let rw_rel_name = format_ident!("rw_{}", cat_str);
            let cat_rel_name = format_ident!("{}", cat_str);

            // Find the Integer/NumLit rule to extract native values
            let integer_rule = theory
                .terms
                .iter()
                .find(|r| r.category == *category && is_integer_rule(r));

            // Store the literal label - either from explicit rule or auto-generated
            let num_lit_label = if let Some(rule) = integer_rule {
                // Explicit integer rule found - use its label
                rule.label.clone()
            } else {
                // No explicit integer rule - use auto-generated literal label
                generate_literal_label(native_type)
            };

            // Find Var rule to generate has_var_ref helper
            let var_rule = theory
                .terms
                .iter()
                .find(|r| r.category == *category && is_var_rule(r));

            // Store the var label - either from explicit rule or auto-generated
            let var_label = if let Some(rule) = var_rule {
                rule.label.clone()
            } else {
                // Use auto-generated label
                generate_var_label(category)
            };

            // Generate function name for has_var_ref helper
            let has_var_ref_fn = format_ident!("has_var_ref_{}", cat_str);

            // Generate match arms for has_var_ref recursively checking all constructors
            let mut has_var_ref_match_arms = Vec::new();
            has_var_ref_match_arms.push(quote! {
                #category::#var_label(_) => true,
            });
            has_var_ref_match_arms.push(quote! {
                #category::#num_lit_label(_) => false,
            });

            // Get all constructors for this category
            let rules: Vec<&GrammarRule> = theory
                .terms
                .iter()
                .filter(|r| r.category == *category)
                .collect();

            // Generate recursive checks for all other constructors
            for rule in &rules {
                let label = &rule.label;
                // Skip Var and NumLit rules - already handled
                if is_var_rule(rule) || is_integer_rule(rule) {
                    continue;
                }

                // Check if this is Assign (explicit or auto-generated)
                if label.to_string() == "Assign" {
                    has_var_ref_match_arms.push(quote! {
                        #category::Assign(_, rhs) => #has_var_ref_fn(rhs.as_ref()),
                    });
                    continue;
                }

                // Count recursive fields (fields of same category)
                let recursive_fields: Vec<_> = rule
                    .items
                    .iter()
                    .filter_map(|item| {
                        match item {
                            GrammarItem::NonTerminal(nt) if nt == category => {
                                Some(false) // Box<Category>
                            },
                            GrammarItem::Collection { element_type, .. }
                                if element_type == category =>
                            {
                                Some(true) // Collection<Category>
                            },
                            _ => None,
                        }
                    })
                    .collect();

                if recursive_fields.is_empty() {
                    // No recursive fields - can't have Var
                    has_var_ref_match_arms.push(quote! {
                        #category::#label(..) => false,
                    });
                } else if recursive_fields.len() == 1 {
                    // Single recursive field
                    if recursive_fields[0] {
                        // Collection field
                        has_var_ref_match_arms.push(quote! {
                            #category::#label(bag) => {
                                for (elem, _count) in bag.iter() {
                                    if #has_var_ref_fn(elem) {
                                        return true;
                                    }
                                }
                                false
                            }
                        });
                    } else {
                        // Single Box<Category> field
                        has_var_ref_match_arms.push(quote! {
                            #category::#label(field) => #has_var_ref_fn(field.as_ref()),
                        });
                    }
                } else if recursive_fields.len() == 2 {
                    // Binary operator (e.g., Add, Sub) - check both fields
                    has_var_ref_match_arms.push(quote! {
                        #category::#label(left, right) => {
                            #has_var_ref_fn(left.as_ref()) || #has_var_ref_fn(right.as_ref())
                        }
                    });
                } else {
                    // More than 2 fields - use conservative approach
                    has_var_ref_match_arms.push(quote! {
                        #category::#label(..) => false,
                    });
                }
            }

            parse_eval_fns.push(quote! {
                /// Parse and evaluate a statement (assignment or expression) with environment.
                /// Returns the computed native type value.
                pub fn parse_and_eval_with_env(
                    input: &str,
                    env: &mut #env_name,
                ) -> Result<#native_type, String> {
                    use ascent::*;

                    mettail_runtime::clear_var_cache();

                    let trimmed = input.trim();

                    // Parse the input (handles both assignments and expressions)
                    let parser = #parser_module::#parser_name::new();
                    let term = parser
                        .parse(trimmed)
                        .map_err(|e| format!("parse error: {:?}", e))?;

                    // Get environment facts - convert enum to native type for Ascent
                    let env_facts: Vec<(String, #native_type)> = env
                        .env_to_facts()
                        .into_iter()
                        .map(|(name, val)| {
                            // Extract native value from enum (NumLit variant)
                            match val {
                                #category::#num_lit_label(v) => Ok((name, v)),
                                _ => Err("Environment value must be a #num_lit_label".to_string()),
                            }
                        })
                        .collect::<Result<Vec<_>, String>>()?;

                    // Run Ascent to rewrite to normal form
                    let prog = ascent_run! {
                        include_source!(#source_name);

                        #cat_rel_name(term.clone());

                        // Seed environment facts (use category-specific relation name)
                        #env_rel_name(n.clone(), v) <-- for (n, v) in env_facts.clone();
                    };

                    // Find normal form (term with no outgoing rewrites)
                    let rewrites: Vec<(#category, #category)> = prog
                        .#rw_rel_name
                        .iter()
                        .map(|(from, to)| (from.clone(), to.clone()))
                        .collect();

                    let mut current = term;
                    loop {
                        // Find rewrite from current term
                        if let Some((_, next)) = rewrites.iter().find(|(from, _)| from == &current) {
                            current = next.clone();
                        } else {
                            // No more rewrites - this is the normal form
                            break;
                        }
                    }

                    // Handle assignments: extract value and update environment
                    if let #category::Assign(var, rhs) = &current {
                        // The RHS might still need rewriting (congruence rules may not fully rewrite nested expressions)
                        // So we recursively rewrite the RHS to its normal form
                        let mut rhs_current = rhs.as_ref().clone();
                        loop {
                            // Find rewrite from current RHS term
                            if let Some((_, next)) = rewrites.iter().find(|(from, _)| from == &rhs_current) {
                                rhs_current = next.clone();
                            } else {
                                // No more rewrites - this is the normal form
                                break;
                            }
                        }

                        // Extract value from fully rewritten RHS (should be a #num_lit_label)
                        let val = match &rhs_current {
                            #category::#num_lit_label(v) => *v,
                            _ => {
                                // Check for undefined variables first by looking for #var_label
                                if #has_var_ref_fn(&rhs_current) {
                                    return Err("undefined variable in expression".to_string());
                                }
                                // Try to evaluate
                                rhs_current.eval()
                            }
                        };

                        // Update environment if we have a variable name
                        if let Some(var_name) = match var {
                            mettail_runtime::OrdVar(mettail_runtime::Var::Free(ref fv)) => {
                                fv.pretty_name.clone()
                            }
                            _ => None,
                        } {
                            env.set(var_name, #category::#num_lit_label(val));
                        }

                        Ok(val)
                    } else {
                        // Not an assignment - extract value from normal form
                        match &current {
                            #category::#num_lit_label(v) => Ok(*v),
                            _ => {
                                // Check for undefined variables
                                if #has_var_ref_fn(&current) {
                                    return Err("undefined variable in expression".to_string());
                                }
                                // Try to evaluate
                                Ok(current.eval())
                            }
                        }
                    }
                }
            });

            // Generate public has_var_ref helper function separately
            parse_eval_fns.push(quote! {
                /// Helper function to check if a term contains a #var_label (undefined variable)
                pub fn #has_var_ref_fn(term: &#category) -> bool {
                    match term {
                        #(#has_var_ref_match_arms)*
                        _ => false,
                    }
                }
            });
        }
    }

    quote! {
        #(#env_structs)*

        #(#parse_eval_fns)*
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::*;
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
                    parameters: Vec::new(),
                    return_type: None,
                    rust_code: None,
                    eval_mode: None,
                    label: parse_quote!(Zero),
                    category: parse_quote!(Elem),
                    items: vec![GrammarItem::Terminal("0".to_string())],
                    bindings: vec![],
                },
                GrammarRule {
                    parameters: Vec::new(),
                    return_type: None,
                    rust_code: None,
                    eval_mode: None,
                    label: parse_quote!(Plus),
                    category: parse_quote!(Elem),
                    items: vec![
                        GrammarItem::NonTerminal(parse_quote!(Elem)),
                        GrammarItem::Terminal("+".to_string()),
                        GrammarItem::NonTerminal(parse_quote!(Elem)),
                    ],
                    bindings: vec![],
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
                    parameters: Vec::new(),
                    return_type: None,
                    rust_code: None,
                    eval_mode: None,
                    label: parse_quote!(PZero),
                    category: parse_quote!(Proc),
                    items: vec![GrammarItem::Terminal("0".to_string())],
                    bindings: vec![],
                },
                GrammarRule {
                    parameters: Vec::new(),
                    return_type: None,
                    rust_code: None,
                    eval_mode: None,
                    label: parse_quote!(NQuote),
                    category: parse_quote!(Name),
                    items: vec![
                        GrammarItem::Terminal("@".to_string()),
                        GrammarItem::NonTerminal(parse_quote!(Proc)),
                    ],
                    bindings: vec![],
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
                    parameters: Vec::new(),
                    return_type: None,
                    rust_code: None,
                    eval_mode: None,
                    label: parse_quote!(PZero),
                    category: parse_quote!(Proc),
                    items: vec![GrammarItem::Terminal("0".to_string())],
                    bindings: vec![],
                },
                GrammarRule {
                    parameters: Vec::new(),
                    return_type: None,
                    rust_code: None,
                    eval_mode: None,
                    label: parse_quote!(NQuote),
                    category: parse_quote!(Name),
                    items: vec![
                        GrammarItem::Terminal("@".to_string()),
                        GrammarItem::NonTerminal(parse_quote!(Proc)),
                    ],
                    bindings: vec![],
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
                    parameters: Vec::new(),
                    return_type: None,
                    rust_code: None,
                    eval_mode: None,
                    label: parse_quote!(PZero),
                    category: parse_quote!(Proc),
                    items: vec![GrammarItem::Terminal("0".to_string())],
                    bindings: vec![],
                },
                GrammarRule {
                    parameters: Vec::new(),
                    return_type: None,
                    rust_code: None,
                    eval_mode: None,
                    label: parse_quote!(PVar),
                    category: parse_quote!(Proc),
                    items: vec![GrammarItem::NonTerminal(parse_quote!(Var))],
                    bindings: vec![],
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
