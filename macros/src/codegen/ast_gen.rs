#![allow(clippy::cmp_owned, clippy::single_match)]

use super::{display, generate_var_label, is_integer_rule, is_var_rule, subst, termgen};
use crate::ast::{BuiltinOp, GrammarItem, GrammarRule, TheoryDef};
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

        let mut variants: Vec<TokenStream> = rules.iter().map(|rule| {
            generate_variant(rule, theory)
        }).collect();

        // For native types, we don't add a Var variant (native types don't use variables)
        // Instead, we'll handle native literals in the parser
        if !has_var_rule {
            // Only add Var variant if this is NOT a native type
            if export.native_type.is_none() {
                let var_label = generate_var_label(cat_name);

                variants.push(quote! {
                    #var_label(mettail_runtime::OrdVar)
                });
            }
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

        for rule in &rules {
            let label = &rule.label;
            let label_str = label.to_string();

            // Check if this is an Integer rule (literal with native type)
            if is_integer_rule(rule) {
                match_arms.push(quote! {
                    #category::#label(n) => *n,
                });
            }
            // Check if this is a Var rule (VarRef, etc.)
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

            // Find VarRef rule and Integer rule for the rewrite
            // Look for any Var rule (not just "VarRef" - could be any name)
            let var_ref_rule = category_rules.iter().find(|r| is_var_rule(r));
            // Integer rule is the one that uses Integer keyword (for native type literals)
            let integer_rule = category_rules.iter().find(|r| is_integer_rule(r));

            let integer_label = integer_rule.map(|r| &r.label);

            // Generate match arms for all constructors
            let mut match_arms: Vec<TokenStream> = Vec::new();
            let category_str = category.to_string();

            for rule in &category_rules {
                let label = &rule.label;
                let label_str = label.to_string();

                // Check if this is VarRef - apply rewrite
                let is_var_ref = var_ref_rule
                    .map(|vr| vr.label.to_string() == label_str)
                    .unwrap_or(false);

                if is_var_ref {
                    if let Some(int_label) = integer_label {
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

/// Generate environment infrastructure for theories with env_var conditions
///
/// This generates:
/// - Environment struct (e.g., CalculatorEnv)
/// - Environment methods (new, set, get, clear)
/// - env_to_facts helper function
/// - rewrite_to_normal_form helper function
fn generate_env_infrastructure(theory: &TheoryDef) -> TokenStream {
    use crate::ast::Condition;
    use quote::format_ident;
    use std::collections::HashSet;

    // Check if any rewrite uses env_var conditions OR env_actions
    let mut env_info = Vec::new();
    let mut seen_relations = HashSet::new();
    let mut has_env_actions = false;

    for rewrite in &theory.rewrites {
        // Check for env_actions (fact creation)
        if !rewrite.env_actions.is_empty() {
            has_env_actions = true;
        }

        for condition in &rewrite.conditions {
            if let Condition::EnvQuery { relation, args } = condition {
                if args.len() >= 2 {
                    let rel_name = relation.to_string();

                    // Avoid duplicates
                    if seen_relations.contains(&rel_name) {
                        continue;
                    }
                    seen_relations.insert(rel_name.clone());

                    // Extract category and native type from the rewrite
                    let category = extract_category_from_rewrite_internal(rewrite, theory);
                    if let Some(category) = category {
                        if let Some(export) = theory.exports.iter().find(|e| e.name == category) {
                            if let Some(native_type) = &export.native_type {
                                env_info.push((
                                    category.clone(),
                                    native_type.clone(),
                                    relation.clone(),
                                ));
                            }
                        }
                    }
                }
            }
        }
    }

    // Also check env_actions for relations
    if has_env_actions {
        for rewrite in &theory.rewrites {
            for action in &rewrite.env_actions {
                let crate::ast::EnvAction::CreateFact { relation, .. } = action;
                let rel_name = relation.to_string();
                if !seen_relations.contains(&rel_name) {
                    seen_relations.insert(rel_name.clone());
                    // Extract category and native type from the rewrite
                    let category = extract_category_from_rewrite_internal(rewrite, theory);
                    if let Some(category) = category {
                        if let Some(export) = theory.exports.iter().find(|e| e.name == category) {
                            if let Some(native_type) = &export.native_type {
                                env_info.push((
                                    category.clone(),
                                    native_type.clone(),
                                    relation.clone(),
                                ));
                            }
                        }
                    }
                }
            }
        }
    }

    if env_info.is_empty() {
        return quote! {};
    }

    // Generate environment infrastructure for each (category, native_type, relation) tuple
    // Currently we only support one env relation per theory, but the structure allows extension
    let mut env_structs = Vec::new();

    for (category, native_type, relation) in &env_info {
        let theory_name = &theory.name;
        let env_name = format_ident!("{}Env", theory_name);
        let theory_name_lower = theory_name.to_string().to_lowercase();
        let source_name = format_ident!("{}_source", theory_name_lower);
        let cat_lower = category.to_string().to_lowercase();
        let rw_rel = format_ident!("rw_{}", cat_lower);
        let cat_rel = format_ident!("{}", cat_lower);
        let category_clone = category.clone();
        let native_type_clone = native_type.clone();
        let relation_clone = relation.clone();

        env_structs.push(quote! {
            use std::collections::HashMap;

            /// Environment for storing variable bindings
            #[derive(Debug, Clone)]
            pub struct #env_name {
                vars: HashMap<String, #native_type_clone>,
            }

            impl #env_name {
                /// Create a new empty environment
                pub fn new() -> Self {
                    #env_name {
                        vars: HashMap::new(),
                    }
                }

                /// Store a variable binding
                pub fn set(&mut self, name: String, value: #native_type_clone) {
                    self.vars.insert(name, value);
                }

                /// Look up a variable value
                pub fn get(&self, name: &str) -> Option<#native_type_clone> {
                    self.vars.get(name).copied()
                }

                /// Clear all bindings
                pub fn clear(&mut self) {
                    self.vars.clear();
                }
            }

            impl Default for #env_name {
                fn default() -> Self {
                    Self::new()
                }
            }

            /// Convert environment to Ascent input facts
            /// Returns a vector of (variable_name, value) tuples for the #relation_clone relation
            pub fn env_to_facts(env: &#env_name) -> Vec<(String, #native_type_clone)> {
                env.vars.iter().map(|(name, val)| (name.clone(), *val)).collect()
            }

            /// Use Ascent to rewrite a term to normal form with environment
            pub fn rewrite_to_normal_form(term: #category_clone, env: &#env_name) -> Result<#category_clone, String> {
                use ascent::*;

                let env_facts = env_to_facts(env);

                // Run Ascent - seed #relation facts using a rule that iterates over the collection
                let prog = ascent_run! {
                    include_source!(#source_name);

                    #cat_rel(term.clone());

                    // Seed environment facts from the vector
                    #relation_clone(n.clone(), v) <-- for (n, v) in env_facts.clone();
                };

                // Find normal form (term with no outgoing rewrites)
                let rewrites: Vec<(#category_clone, #category_clone)> = prog.#rw_rel
                    .iter()
                    .map(|(from, to)| (from.clone(), to.clone()))
                    .collect();

                // Start from initial term and follow rewrite chain to normal form
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

                Ok(current)
            }
        });
    }

    // Generate parse_and_eval_with_env function
    // This function handles parsing, rewriting, and value extraction automatically
    let mut parse_eval_functions = Vec::new();
    for (category, native_type, _relation) in &env_info {
        let theory_name = &theory.name;
        let theory_name_lower = theory_name.to_string().to_lowercase();
        let parser_mod = format_ident!("{}", theory_name_lower);
        let cat_parser = format_ident!("{}Parser", category);
        let env_name = format_ident!("{}Env", theory_name);

        // Find assignment-like constructors (Var + recursive category)
        let assignment_constructors: Vec<_> = theory
            .terms
            .iter()
            .filter(|rule| {
                rule.category == *category
                    && rule.items.iter().any(|item| {
                        if let GrammarItem::NonTerminal(nt) = item {
                            nt.to_string() == "Var"
                        } else {
                            false
                        }
                    })
                    && rule.items.iter().any(|item| {
                        if let GrammarItem::NonTerminal(nt) = item {
                            nt == category
                        } else {
                            false
                        }
                    })
            })
            .map(|rule| &rule.label)
            .collect();

        // Helper function for checking undefined variables
        // We need to generate match arms for all constructors that might contain VarRef
        let mut check_var_ref_arms = Vec::new();

        // Add specific cases for common constructors
        for rule in theory.terms.iter().filter(|r| r.category == *category) {
            let label = &rule.label;
            let has_var_field = rule.items.iter().any(|item| {
                if let GrammarItem::NonTerminal(nt) = item {
                    nt.to_string() == "Var"
                } else {
                    false
                }
            });

            let recursive_fields: Vec<_> = rule
                .items
                .iter()
                .enumerate()
                .filter_map(|(i, item)| {
                    if let GrammarItem::NonTerminal(nt) = item {
                        if nt == category {
                            Some(i)
                        } else {
                            None
                        }
                    } else {
                        None
                    }
                })
                .collect();

            if has_var_field && recursive_fields.len() == 1 {
                // Assign-like: (Var, Box<Category>) - only check the recursive field
                check_var_ref_arms.push(quote! {
                    #category::#label(_, f1) => check_var_ref(f1),
                });
            } else if recursive_fields.len() == 2 {
                // Binary operators like Add, Sub: (Box<Category>, Box<Category>)
                check_var_ref_arms.push(quote! {
                    #category::#label(f0, f1) => check_var_ref(f0) || check_var_ref(f1),
                });
            } else if recursive_fields.len() == 1 {
                // Single recursive field
                check_var_ref_arms.push(quote! {
                    #category::#label(f0) => check_var_ref(f0),
                });
            } else {
                // No recursive fields or unit constructor
                check_var_ref_arms.push(quote! {
                    #category::#label(..) => false,
                });
            }
        }

        let check_var_ref_fn = quote! {
            fn check_var_ref(term: &#category) -> bool {
                match term {
                    #category::VarRef(_) => true,
                    #category::NumLit(_) => false,
                    #(#check_var_ref_arms)*
                    _ => false,
                }
            }
        };

        // Generate value extraction logic
        // Build match arms for assignment constructors
        let mut assign_match_arms = Vec::new();
        for assign_label in &assignment_constructors {
            assign_match_arms.push(quote! {
                #category::#assign_label(var, rhs) => {
                    // Extract variable name from OrdVar
                    let var_name = match var {
                        mettail_runtime::OrdVar(mettail_runtime::Var::Free(ref fv)) => {
                            fv.pretty_name.clone()
                        },
                        _ => None,
                    };

                    // Check if RHS is a NumLit (after rewriting)
                    let val = match rhs.as_ref() {
                        #category::NumLit(v) => *v,
                        _ => {
                            // RHS still has variables or isn't fully evaluated
                            // Check for undefined variables
                            if check_var_ref(rhs) {
                                return Err("undefined variable in expression".to_string());
                            }
                            // Try to evaluate the RHS
                            rhs.eval()
                        }
                    };

                    // Update environment if we have a variable name
                    if let Some(name) = var_name {
                        env.set(name, val);
                    }

                    val
                }
            });
        }

        parse_eval_functions.push(quote! {
            /// Parse and evaluate a statement (assignment or expression) with environment.
            /// Returns the computed value.
            /// This function is automatically generated for theories with declarative fact creation.
            pub fn parse_and_eval_with_env(
                input: &str,
                env: &mut #env_name,
            ) -> Result<#native_type, String> {
                #check_var_ref_fn

                mettail_runtime::clear_var_cache();

                let trimmed = input.trim();

                // Parse the input (handles both assignments and expressions)
                let parser = #parser_mod::#cat_parser::new();
                let term = parser
                    .parse(trimmed)
                    .map_err(|e| format!("parse error: {:?}", e))?;

                // Use Ascent to rewrite to normal form (generated function)
                // This will create env_var facts via rewrite rules with env_actions
                let normal_form = rewrite_to_normal_form(term, env)?;

                // Extract value from the normal form
                let val = match &normal_form {
                    #(#assign_match_arms,)*
                    #category::NumLit(v) => *v,
                    _ => {
                        // Fallback: try to evaluate the whole term
                        // Check for undefined variables first
                        if check_var_ref(&normal_form) {
                            return Err("undefined variable in expression".to_string());
                        }
                        normal_form.eval()
                    }
                };

                Ok(val)
            }
        });
    }

    quote! {
        #(#env_structs)*
        #(#parse_eval_functions)*
    }
}

/// Extract the category from a rewrite rule (from LHS)
/// Internal helper function for environment generation
fn extract_category_from_rewrite_internal(
    rewrite: &crate::ast::RewriteRule,
    theory: &TheoryDef,
) -> Option<proc_macro2::Ident> {
    use crate::ast::Expr;

    // Try to extract category from LHS pattern
    match &rewrite.left {
        Expr::Apply { constructor, .. } => {
            // Find the rule with this constructor
            theory
                .terms
                .iter()
                .find(|r| r.label == *constructor)
                .map(|rule| rule.category.clone())
        },
        Expr::Var(_) => None,
        Expr::Subst { .. } => None,
        Expr::CollectionPattern { .. } => None,
        // Lambdas are meta-level constructs, not patterns in rewrites
        Expr::Lambda { .. } | Expr::MultiLambda { .. } => None,
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
