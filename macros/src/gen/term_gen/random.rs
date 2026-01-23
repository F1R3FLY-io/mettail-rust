#![allow(
    clippy::cmp_owned,
    clippy::too_many_arguments,
    clippy::needless_borrow,
    clippy::for_kv_map,
    clippy::let_and_return,
    clippy::unused_enumerate_index,
    clippy::expect_fun_call,
    clippy::collapsible_match,
    clippy::unwrap_or_default,
    clippy::unnecessary_filter_map
)]

use crate::ast::{language::LanguageDef, grammar::{GrammarItem, GrammarRule, TermParam}};
use crate::gen::term_gen::is_lang_type;
use proc_macro2::TokenStream;
use quote::quote;
use syn::Ident;

/// Generate random term generation code for all exported categories
pub fn generate_random_generation(language: &LanguageDef) -> TokenStream {
    let category_impls: Vec<TokenStream> = language
        .types
        .iter()
        .map(|lang_type| generate_random_for_category(&lang_type.name, language))
        .collect();

    quote! {
        #(#category_impls)*
    }
}

/// Generate random generation methods for a specific category
fn generate_random_for_category(cat_name: &Ident, language: &LanguageDef) -> TokenStream {
    let rules: Vec<&GrammarRule> = language
        .terms
        .iter()
        .filter(|r| r.category == *cat_name)
        .collect();

    let depth_0_impl = generate_random_depth_0(cat_name, &rules, language);
    let depth_d_impl = generate_random_depth_d(cat_name, &rules, language);

    quote! {
        impl #cat_name {
            /// Generate a random term at exactly the given depth
            ///
            /// # Arguments
            /// * `vars` - Pool of variable names for free variables
            /// * `depth` - Target depth (operator nesting level)
            /// * `max_collection_width` - Maximum number of elements in any collection
            ///
            /// # Example
            /// ```ignore
            /// let term = Proc::generate_random_at_depth(&["a".into(), "b".into()], 25, 3);
            /// ```
            pub fn generate_random_at_depth(vars: &[String], depth: usize, max_collection_width: usize) -> Self {
                use rand::Rng;
                let mut rng = rand::thread_rng();
                Self::generate_random_at_depth_internal(vars, depth, max_collection_width, &mut rng, 0)
            }

            /// Generate a random term at exactly the given depth with a seed
            ///
            /// This is deterministic - same seed produces same term.
            ///
            /// # Arguments
            /// * `vars` - Pool of variable names for free variables
            /// * `depth` - Target depth (operator nesting level)
            /// * `max_collection_width` - Maximum number of elements in any collection
            /// * `seed` - Random seed for reproducibility
            pub fn generate_random_at_depth_with_seed(
                vars: &[String],
                depth: usize,
                max_collection_width: usize,
                seed: u64
            ) -> Self {
                use rand::{SeedableRng, Rng};
                let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
                Self::generate_random_at_depth_internal(vars, depth, max_collection_width, &mut rng, 0)
            }

            fn generate_random_at_depth_internal<R: rand::Rng>(
                vars: &[String],
                depth: usize,
                max_collection_width: usize,
                rng: &mut R,
                binding_depth: usize,
            ) -> Self {
                if depth == 0 {
                    #depth_0_impl
                } else {
                    #depth_d_impl
                }
            }
        }
    }
}

/// Generate random depth 0 case (nullary constructors and variables)
fn generate_random_depth_0(
    cat_name: &Ident,
    rules: &[&GrammarRule],
    _language: &LanguageDef,
) -> TokenStream {
    let mut cases = Vec::new();

    for rule in rules {
        let label = &rule.label;

        // Skip collection constructors
        let has_collections = rule
            .items
            .iter()
            .any(|item| matches!(item, GrammarItem::Collection { .. }));

        if has_collections {
            continue;
        }

        // Skip binder constructors at depth 0
        // Binders should only be generated at depth > 0 with correct binding_depth
        if !rule.bindings.is_empty() {
            continue;
        }

        let non_terminals: Vec<_> = rule
            .items
            .iter()
            .filter(|item| matches!(item, GrammarItem::NonTerminal(_) | GrammarItem::Binder { .. }))
            .collect();

        if non_terminals.is_empty() {
            // Nullary constructor
            cases.push(quote! { #cat_name::#label });
        } else if non_terminals.len() == 1 {
            // Check if it's a Var or Integer constructor
            if let GrammarItem::NonTerminal(nt) = non_terminals[0] {
                let nt_str = nt.to_string();
                if nt_str == "Var" {
                    // VarRef or other Var rules - generate variables
                    cases.push(quote! {
                        if !vars.is_empty() {
                            let idx = rng.gen_range(0..vars.len());
                            #cat_name::#label(
                                mettail_runtime::OrdVar(
                                    mettail_runtime::Var::Free(
                                        mettail_runtime::get_or_create_var(&vars[idx])
                                    )
                                )
                            )
                        } else {
                            #cat_name::#label(
                                mettail_runtime::OrdVar(
                                    mettail_runtime::Var::Free(
                                        mettail_runtime::get_or_create_var("_")
                                    )
                                )
                            )
                        }
                    });
                } else if nt_str == "Integer" {
                    // Integer literals - generate random native values
                    cases.push(quote! {
                        let val = rng.gen_range(-100i32..100i32);
                        #cat_name::#label(val)
                    });
                }
            }
        }
    }

    if cases.is_empty() {
        // No depth 0 constructors - should not happen, but handle gracefully
        quote! {
            panic!("No depth 0 constructors for {}", stringify!(#cat_name))
        }
    } else if cases.len() == 1 {
        // Only one case, return directly
        let case = &cases[0];
        quote! { #case }
    } else {
        // Multiple cases - generate match arms
        let match_arms: Vec<TokenStream> = cases
            .iter()
            .enumerate()
            .map(|(i, case)| {
                quote! {
                    #i => { #case }
                }
            })
            .collect();

        let num_cases = cases.len();

        quote! {
            {
                let choice = rng.gen_range(0..#num_cases);
                match choice {
                    #(#match_arms,)*
                    _ => unreachable!()
                }
            }
        }
    }
}

/// Generate random depth d case (recursive constructors)
fn generate_random_depth_d(
    cat_name: &Ident,
    rules: &[&GrammarRule],
    language: &LanguageDef,
) -> TokenStream {
    let mut constructor_cases = Vec::new();

    for rule in rules {
        // Check if this is a multi-binder rule (skip random generation for now)
        let is_multi_binder = rule.term_context.as_ref().map_or(false, |ctx| {
            ctx.iter().any(|p| matches!(p, TermParam::MultiAbstraction { .. }))
        });
        
        if is_multi_binder {
            // TODO: Implement proper random generation for multi-binder constructors
            continue;
        }
        
        // Check if this has collections
        let has_collections = rule
            .items
            .iter()
            .any(|item| matches!(item, GrammarItem::Collection { .. }));

        if has_collections {
            // Handle collection constructors
            constructor_cases.push(generate_random_collection_constructor(cat_name, rule, language));
            continue;
        }

        let non_terminals: Vec<_> = rule
            .items
            .iter()
            .filter_map(|item| match item {
                GrammarItem::NonTerminal(nt) => Some(nt.clone()),
                GrammarItem::Binder { category } => Some(category.clone()),
                _ => None,
            })
            .collect();

        // Skip depth 0 constructors
        if non_terminals.is_empty() {
            continue;
        }

        // Skip Var and Integer constructors at depth > 0 (they're depth 0 only)
        if non_terminals.len() == 1 {
            let nt_str = non_terminals[0].to_string();
            if nt_str == "Var" || nt_str == "Integer" {
                continue;
            }
        }

        // Generate case for this constructor
        if rule.bindings.is_empty() {
            constructor_cases.push(generate_random_simple_constructor(cat_name, rule, language));
        } else {
            constructor_cases.push(generate_random_binder_constructor(cat_name, rule, language));
        }
    }

    if constructor_cases.is_empty() {
        // No recursive constructors - just return depth 0
        let depth_0 = generate_random_depth_0(cat_name, rules, language);
        quote! { #depth_0 }
    } else {
        // Generate match arms instead of closures to avoid borrowing issues
        let match_arms: Vec<TokenStream> = constructor_cases
            .iter()
            .enumerate()
            .map(|(i, case)| {
                quote! {
                    #i => { #case }
                }
            })
            .collect();

        let num_cases = constructor_cases.len();

        quote! {
            {
                let choice = rng.gen_range(0..#num_cases);
                match choice {
                    #(#match_arms,)*
                    _ => unreachable!()
                }
            }
        }
    }
}

/// Generate random simple constructor (no binders)
fn generate_random_simple_constructor(
    cat_name: &Ident,
    rule: &GrammarRule,
    language: &LanguageDef,
) -> TokenStream {
    let label = &rule.label;

    let arg_cats: Vec<Ident> = rule
        .items
        .iter()
        .filter_map(|item| match item {
            GrammarItem::NonTerminal(nt) => Some(nt.clone()),
            _ => None,
        })
        .collect();

    match arg_cats.len() {
        1 => generate_random_unary(cat_name, label, &arg_cats[0], language),
        2 => generate_random_binary(cat_name, label, &arg_cats[0], &arg_cats[1], language),
        _ => generate_random_nary(cat_name, label, &arg_cats, language),
    }
}

fn generate_random_unary(
    cat_name: &Ident,
    label: &Ident,
    arg_cat: &Ident,
    language: &LanguageDef,
) -> TokenStream {
    if !is_lang_type(arg_cat, language) {
        return quote! {};
    }

    quote! {
        let arg = #arg_cat::generate_random_at_depth_internal(vars, depth - 1, max_collection_width, rng, binding_depth);
        #cat_name::#label(Box::new(arg))
    }
}

fn generate_random_binary(
    cat_name: &Ident,
    label: &Ident,
    arg1_cat: &Ident,
    arg2_cat: &Ident,
    language: &LanguageDef,
) -> TokenStream {
    let arg1_str = arg1_cat.to_string();
    let arg2_str = arg2_cat.to_string();

    // Handle Var specially - it's a built-in type, generate directly as OrdVar
    let is_arg1_var = arg1_str == "Var";
    let is_arg2_var = arg2_str == "Var";

    // If both args are non-exported and not Var, skip this constructor
    if !is_arg1_var && !is_lang_type(arg1_cat, language) {
        return quote! {};
    }
    if !is_arg2_var && !is_lang_type(arg2_cat, language) {
        return quote! {};
    }

    if is_arg1_var {
        // First arg is Var, second is recursive
        quote! {
            let arg1 = if !vars.is_empty() {
                let idx = rng.gen_range(0..vars.len());
                mettail_runtime::OrdVar(
                    mettail_runtime::Var::Free(
                        mettail_runtime::get_or_create_var(&vars[idx])
                    )
                )
            } else {
                mettail_runtime::OrdVar(
                    mettail_runtime::Var::Free(
                        mettail_runtime::get_or_create_var("_")
                    )
                )
            };
            // Var is depth 0, so second arg can be depth - 1
            let arg2 = Box::new(#arg2_cat::generate_random_at_depth_internal(vars, depth - 1, max_collection_width, rng, binding_depth));
            #cat_name::#label(arg1, arg2)
        }
    } else if is_arg2_var {
        // Second arg is Var, first is recursive
        quote! {
            let arg1 = Box::new(#arg1_cat::generate_random_at_depth_internal(vars, depth - 1, max_collection_width, rng, binding_depth));
            let arg2 = if !vars.is_empty() {
                let idx = rng.gen_range(0..vars.len());
                mettail_runtime::OrdVar(
                    mettail_runtime::Var::Free(
                        mettail_runtime::get_or_create_var(&vars[idx])
                    )
                )
            } else {
                mettail_runtime::OrdVar(
                    mettail_runtime::Var::Free(
                        mettail_runtime::get_or_create_var("_")
                    )
                )
            };
            #cat_name::#label(arg1, arg2)
        }
    } else {
        // Both are recursive categories
        quote! {
            let d1 = rng.gen_range(0..depth);
            let d2 = if d1 == depth - 1 {
                rng.gen_range(0..depth)
            } else {
                depth - 1
            };

            let arg1 = #arg1_cat::generate_random_at_depth_internal(vars, d1, max_collection_width, rng, binding_depth);
            let arg2 = #arg2_cat::generate_random_at_depth_internal(vars, d2, max_collection_width, rng, binding_depth);
            #cat_name::#label(Box::new(arg1), Box::new(arg2))
        }
    }
}

fn generate_random_nary(
    cat_name: &Ident,
    label: &Ident,
    arg_cats: &[Ident],
    language: &LanguageDef,
) -> TokenStream {
    // Simplified: all args at depth - 1
    let arg_generations: Vec<TokenStream> = arg_cats.iter().map(|cat| {
        if !is_lang_type(cat, language) {
            return quote! { panic!("Non-exported category") };
        }
        quote! {
            Box::new(#cat::generate_random_at_depth_internal(vars, depth - 1, max_collection_width, rng, binding_depth))
        }
    }).collect();

    quote! {
        #cat_name::#label(#(#arg_generations),*)
    }
}

/// Generate random binder constructor
fn generate_random_binder_constructor(
    cat_name: &Ident,
    rule: &GrammarRule,
    language: &LanguageDef,
) -> TokenStream {
    let label = &rule.label;

    let (binder_idx, body_indices) = &rule.bindings[0];
    let body_idx = body_indices[0];

    // Find body category
    let body_cat = match &rule.items[body_idx] {
        GrammarItem::NonTerminal(cat) => cat,
        _ => panic!("Body should be NonTerminal"),
    };

    // Find non-body, non-binder arguments
    let other_args: Vec<(usize, Ident)> = rule
        .items
        .iter()
        .enumerate()
        .filter_map(|(i, item)| {
            if i == *binder_idx || i == body_idx {
                None
            } else {
                match item {
                    GrammarItem::NonTerminal(cat) => Some((i, cat.clone())),
                    _ => None,
                }
            }
        })
        .collect();

    if other_args.is_empty() {
        // Simple binder: just body
        generate_random_simple_binder(cat_name, label, body_cat, language)
    } else if other_args.len() == 1 {
        // One non-body arg (e.g., PInput channel x. body)
        generate_random_binder_with_one_arg(cat_name, label, &other_args[0].1, body_cat, language)
    } else {
        // Multiple args - simplified
        generate_random_binder_with_multiple_args(cat_name, label, &other_args, body_cat, language)
    }
}

fn generate_random_simple_binder(
    cat_name: &Ident,
    label: &Ident,
    body_cat: &Ident,
    language: &LanguageDef,
) -> TokenStream {
    if !is_lang_type(body_cat, language) {
        return quote! {};
    }

    quote! {
        let binder_name = format!("x{}", binding_depth);
        let mut extended_vars = vars.to_vec();
        extended_vars.push(binder_name.clone());

        let body = #body_cat::generate_random_at_depth_internal(
            &extended_vars,
            depth - 1,
            max_collection_width,
            rng,
            binding_depth + 1
        );

        let binder_var = mettail_runtime::get_or_create_var(&binder_name);
        let binder = mettail_runtime::Binder(binder_var);
        let scope = mettail_runtime::Scope::new(binder, Box::new(body));

        #cat_name::#label(scope)
    }
}

fn generate_random_binder_with_one_arg(
    cat_name: &Ident,
    label: &Ident,
    arg_cat: &Ident,
    body_cat: &Ident,
    language: &LanguageDef,
) -> TokenStream {
    if !is_lang_type(arg_cat, language) || !is_lang_type(body_cat, language) {
        return quote! {};
    }

    quote! {
        let d1 = rng.gen_range(0..depth);
        let d2 = if d1 == depth - 1 {
            rng.gen_range(0..depth)
        } else {
            depth - 1
        };

        let arg1 = #arg_cat::generate_random_at_depth_internal(vars, d1, max_collection_width, rng, binding_depth);

        let binder_name = format!("x{}", binding_depth);
        let mut extended_vars = vars.to_vec();
        extended_vars.push(binder_name.clone());
        let body = #body_cat::generate_random_at_depth_internal(
            &extended_vars,
            d2,
            max_collection_width,
            rng,
            binding_depth + 1
        );

        let binder_var = mettail_runtime::get_or_create_var(&binder_name);
        let binder = mettail_runtime::Binder(binder_var);
        let scope = mettail_runtime::Scope::new(binder, Box::new(body));

        #cat_name::#label(Box::new(arg1), scope)
    }
}

fn generate_random_binder_with_multiple_args(
    cat_name: &Ident,
    label: &Ident,
    other_args: &[(usize, Ident)],
    body_cat: &Ident,
    language: &LanguageDef,
) -> TokenStream {
    if !is_lang_type(body_cat, language) {
        return quote! {};
    }

    let arg_generations: Vec<TokenStream> = other_args.iter().map(|(_, cat)| {
        if !is_lang_type(cat, language) {
            return quote! { panic!("Non-exported category") };
        }
        quote! {
            Box::new(#cat::generate_random_at_depth_internal(vars, depth - 1, max_collection_width, rng, binding_depth))
        }
    }).collect();

    quote! {
        let binder_name = format!("x{}", binding_depth);
        let mut extended_vars = vars.to_vec();
        extended_vars.push(binder_name.clone());
        let body = #body_cat::generate_random_at_depth_internal(
            &extended_vars,
            depth - 1,
            max_collection_width,
            rng,
            binding_depth + 1
        );

        let binder_var = mettail_runtime::get_or_create_var(&binder_name);
        let binder = mettail_runtime::Binder(binder_var);
        let scope = mettail_runtime::Scope::new(binder, Box::new(body));

        #cat_name::#label(#(#arg_generations,)* scope)
    }
}

/// Generate random collection constructor
fn generate_random_collection_constructor(
    cat_name: &Ident,
    rule: &GrammarRule,
    language: &LanguageDef,
) -> TokenStream {
    let label = &rule.label;

    // Find the collection field
    let element_cat = rule
        .items
        .iter()
        .find_map(|item| match item {
            GrammarItem::Collection { element_type, .. } => Some(element_type.clone()),
            _ => None,
        })
        .expect("Collection constructor must have a collection field");

    if !is_lang_type(&element_cat, language) {
        return quote! { panic!("Non-type collection element category") };
    }

    quote! {
        {
            // Choose a random collection size (0 to max_collection_width)
            let size = rng.gen_range(0..=max_collection_width);
            let mut bag = mettail_runtime::HashBag::new();

            for _ in 0..size {
                // Generate element at random depth < current depth
                let elem_depth = if depth > 0 { rng.gen_range(0..depth) } else { 0 };
                let elem = #element_cat::generate_random_at_depth_internal(
                    vars,
                    elem_depth,
                    max_collection_width,
                    rng,
                    binding_depth
                );
                bag.insert(elem);
            }

            #cat_name::#label(bag)
        }
    }
}