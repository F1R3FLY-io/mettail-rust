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

use crate::ast::{
    grammar::{GrammarItem, GrammarRule},
    language::{CollectionCategory, LanguageDef},
};
use crate::gen::term_gen::is_lang_type;
use proc_macro2::TokenStream;
use quote::quote;
use syn::Ident;

/// Generate term generation code for all exported categories
pub fn generate_term_generation(language: &LanguageDef) -> TokenStream {
    let context_struct = generate_context_struct(language);
    let context_impl = generate_context_impl(language);
    let public_apis = generate_public_apis(language);

    quote! {
        #context_struct
        #context_impl
        #public_apis
    }
}

/// Generate the GenerationContext struct that holds memoization tables
fn generate_context_struct(language: &LanguageDef) -> TokenStream {
    let category_fields: Vec<TokenStream> = language
        .types
        .iter()
        .map(|lang_type| {
            let cat_name = &lang_type.name;
            let field_name = category_to_field_name(cat_name);

            quote! {
                #field_name: std::collections::HashMap<usize, Vec<#cat_name>>
            }
        })
        .collect();

    quote! {
        struct GenerationContext {
            vars: Vec<String>,
            initial_var_count: usize,  // Track how many vars were in initial pool
            max_depth: usize,
            max_collection_width: usize,
            #(#category_fields),*
        }
    }
}

/// Generate impl GenerationContext with generation methods
fn generate_context_impl(language: &LanguageDef) -> TokenStream {
    let new_fields: Vec<TokenStream> = language
        .types
        .iter()
        .map(|lang_type| {
            let field_name = category_to_field_name(&lang_type.name);
            quote! {
                #field_name: std::collections::HashMap::new()
            }
        })
        .collect();

    let generation_calls: Vec<TokenStream> = language
        .types
        .iter()
        .map(|lang_type| {
            let method_name = category_to_generate_method(&lang_type.name);
            quote! {
                self.#method_name(depth);
            }
        })
        .collect();

    let category_methods: Vec<TokenStream> = language
        .types
        .iter()
        .map(|lang_type| generate_category_generation_method(lang_type.name.clone(), language))
        .collect();

    quote! {
        impl GenerationContext {
            fn new(vars: Vec<String>, max_depth: usize, max_collection_width: usize) -> Self {
                let initial_var_count = vars.len();
                Self {
                    vars,
                    initial_var_count,
                    max_depth,
                    max_collection_width,
                    #(#new_fields),*
                }
            }

            fn new_with_extended_vars(
                vars: Vec<String>,
                initial_var_count: usize,
                max_depth: usize,
                max_collection_width: usize
            ) -> Self {
                Self {
                    vars,
                    initial_var_count,
                    max_depth,
                    max_collection_width,
                    #(#new_fields),*
                }
            }

            fn generate_all(mut self) -> Self {
                for depth in 0..=self.max_depth {
                    #(#generation_calls)*
                }
                self
            }

            #(#category_methods)*
        }
    }
}

/// Generate generation method for a specific category
fn generate_category_generation_method(cat_name: Ident, language: &LanguageDef) -> TokenStream {
    let method_name = category_to_generate_method(&cat_name);
    let field_name = category_to_field_name(&cat_name);

    // Get all rules for this category
    let rules: Vec<&GrammarRule> = language
        .terms
        .iter()
        .filter(|r| r.category == cat_name)
        .collect();

    let depth_0_cases = generate_depth_0_cases(&cat_name, &rules, language);
    let depth_d_cases = generate_depth_d_cases(&cat_name, &rules, language);

    quote! {
        fn #method_name(&mut self, depth: usize) {
            let mut terms: Vec<#cat_name> = Vec::new();

            if depth == 0 {
                #depth_0_cases
            } else {
                #depth_d_cases
            }

            // Deduplicate
            terms.sort();
            terms.dedup();

            self.#field_name.insert(depth, terms);
        }
    }
}

/// Generate depth 0 cases (nullary constructors and variables)
fn generate_depth_0_cases(
    cat_name: &Ident,
    rules: &[&GrammarRule],
    language: &LanguageDef,
) -> TokenStream {
    let mut cases = Vec::new();

    for rule in rules {
        let label = &rule.label;

        // Check if this is a nullary constructor
        let non_terminals: Vec<_> = rule
            .items
            .iter()
            .filter(|item| {
                matches!(
                    item,
                    GrammarItem::NonTerminal(_)
                        | GrammarItem::Binder { .. }
                        | GrammarItem::Collection { .. }
                )
            })
            .collect();

        if non_terminals.is_empty() {
            // Nullary constructor
            cases.push(quote! {
                terms.push(#cat_name::#label);
            });
        } else if non_terminals.len() == 1 {
            // Check if it's a Var constructor
            if let GrammarItem::NonTerminal(nt) = non_terminals[0] {
                if nt.to_string() == "Var" {
                    // Check if this is NumLit with a native type
                    let label_str = label.to_string();
                    let is_numlit = label_str == "NumLit";
                    let has_native = language
                        .types
                        .iter()
                        .any(|t| t.name == *cat_name && t.native_type.is_some());

                    if has_native && is_numlit {
                        // For NumLit with native types, generate native values
                        // For i32/i64, generate some sample integers
                        cases.push(quote! {
                            // Generate some sample native values
                            for val in [0i32, 1i32, 2i32, 42i32] {
                                terms.push(#cat_name::#label(val));
                            }
                        });
                    } else {
                        // VarRef or other Var rules - generate from var pool
                        cases.push(quote! {
                            for var_name in &self.vars {
                                terms.push(#cat_name::#label(
                                    mettail_runtime::OrdVar(
                                        mettail_runtime::Var::Free(
                                            mettail_runtime::get_or_create_var(var_name)
                                        )
                                    )
                                ));
                            }
                        });
                    }
                }
            }
            // Skip Collection constructors - they can't be exhaustively generated
        }
    }

    quote! {
        #(#cases)*
    }
}

/// Generate depth d cases (recursive constructors)
fn generate_depth_d_cases(
    cat_name: &Ident,
    rules: &[&GrammarRule],
    language: &LanguageDef,
) -> TokenStream {
    let mut cases = Vec::new();

    for rule in rules {
        // Check if this rule has collections
        let has_collection = rule
            .items
            .iter()
            .any(|item| matches!(item, GrammarItem::Collection { .. }));

        if has_collection {
            // Handle collection constructors
            cases.push(generate_collection_constructor_case(cat_name, rule, language));
            continue;
        }

        // Skip nullary and var constructors (handled at depth 0)
        let non_terminals: Vec<_> = rule
            .items
            .iter()
            .filter_map(|item| match item {
                GrammarItem::NonTerminal(nt) => Some(nt.clone()),
                GrammarItem::Binder { category } => Some(category.clone()),
                _ => None,
            })
            .collect();

        if non_terminals.is_empty() {
            continue; // Nullary
        }

        if non_terminals.len() == 1 && non_terminals[0].to_string() == "Var" {
            continue; // Var constructor
        }

        // Generate recursive case
        if rule.bindings.is_empty() {
            // Simple constructor without binders
            cases.push(generate_simple_constructor_case(cat_name, rule, language));
        } else {
            // Constructor with binders
            cases.push(generate_binder_constructor_case(cat_name, rule, language));
        }
    }

    quote! {
        #(#cases)*
    }
}

/// Generate case for simple constructor (no binders)
fn generate_simple_constructor_case(
    cat_name: &Ident,
    rule: &GrammarRule,
    language: &LanguageDef,
) -> TokenStream {
    let label = &rule.label;

    // Get argument categories
    let arg_cats: Vec<Ident> = rule
        .items
        .iter()
        .filter_map(|item| match item {
            GrammarItem::NonTerminal(nt) => Some(nt.clone()),
            _ => None,
        })
        .collect();

    if arg_cats.is_empty() {
        return quote! {};
    }

    // Generate depth loops based on arity
    match arg_cats.len() {
        1 => generate_unary_case(cat_name, label, &arg_cats[0], language),
        2 => generate_binary_case(cat_name, label, &arg_cats[0], &arg_cats[1], language),
        _ => generate_nary_case(cat_name, label, &arg_cats, language),
    }
}

/// Generate unary constructor case
fn generate_unary_case(
    cat_name: &Ident,
    label: &Ident,
    arg_cat: &Ident,
    language: &LanguageDef,
) -> TokenStream {
    let field_name = category_to_field_name(arg_cat);
    let is_var = arg_cat.to_string() == "Var";

    if is_lang_type(arg_cat, language) {
        let constructor = if is_var {
            quote! {
                #cat_name::#label(arg1.clone())
            }
        } else {
            quote! {
                #cat_name::#label(Box::new(arg1.clone()))
            }
        };

        quote! {
            for d1 in 0..depth {
                if let Some(args1) = self.#field_name.get(&d1) {
                    for arg1 in args1 {
                        terms.push(#constructor);
                    }
                }
            }
        }
    } else {
        quote! {}
    }
}

/// Generate binary constructor case
fn generate_binary_case(
    cat_name: &Ident,
    label: &Ident,
    arg1_cat: &Ident,
    arg2_cat: &Ident,
    language: &LanguageDef,
) -> TokenStream {
    let field1 = category_to_field_name(arg1_cat);
    let field2 = category_to_field_name(arg2_cat);

    if !is_lang_type(arg1_cat, language) || !is_lang_type(arg2_cat, language) {
        return quote! {};
    }

    quote! {
        for d1 in 0..depth {
            for d2 in 0..depth {
                if d1.max(d2) + 1 == depth {
                    if let Some(args1) = self.#field1.get(&d1) {
                        if let Some(args2) = self.#field2.get(&d2) {
                            for arg1 in args1 {
                                for arg2 in args2 {
                                    terms.push(#cat_name::#label(
                                        Box::new(arg1.clone()),
                                        Box::new(arg2.clone())
                                    ));
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}

/// Generate n-ary constructor case (n > 2)
fn generate_nary_case(
    cat_name: &Ident,
    label: &Ident,
    arg_cats: &[Ident],
    language: &LanguageDef,
) -> TokenStream {
    let n = arg_cats.len();

    // Bail if any arg is not a language type
    for cat in arg_cats {
        if !is_lang_type(cat, language) {
            return quote! {};
        }
    }

    // Build constructor arguments
    let constructor_args: Vec<TokenStream> = (0..n)
        .map(|i| {
            let argi = syn::Ident::new(&format!("arg{}", i), proc_macro2::Span::call_site());
            quote! { Box::new(#argi.clone()) }
        })
        .collect();

    // Build nested code from inside out: innermost is the push
    let mut inner = quote! {
        terms.push(#cat_name::#label(#(#constructor_args),*));
    };

    // Wrap with for loops (innermost arg last, building outward)
    for i in (0..n).rev() {
        let args_i = syn::Ident::new(&format!("args{}", i), proc_macro2::Span::call_site());
        let arg_i = syn::Ident::new(&format!("arg{}", i), proc_macro2::Span::call_site());
        inner = quote! {
            for #arg_i in #args_i {
                #inner
            }
        };
    }

    // Wrap with if-let guards (innermost arg last, building outward)
    for i in (0..n).rev() {
        let field = category_to_field_name(&arg_cats[i]);
        let args_i = syn::Ident::new(&format!("args{}", i), proc_macro2::Span::call_site());
        inner = quote! {
            if let Some(#args_i) = self.#field.get(&d) {
                #inner
            }
        };
    }

    // Simplified: all args at depth-1
    quote! {
        if depth > 0 {
            let d = depth - 1;
            #inner
        }
    }
}

/// Generate case for constructor with binders
fn generate_binder_constructor_case(
    cat_name: &Ident,
    rule: &GrammarRule,
    language: &LanguageDef,
) -> TokenStream {
    let label = &rule.label;

    // For binder constructors, we need to:
    // 1. Get non-binder, non-body arguments
    // 2. Generate the body at various depths
    // 3. Create a Scope with a fixed binder name "x"

    let (binder_idx, body_indices) = &rule.bindings[0];
    let body_idx = body_indices[0];

    // Collect all argument categories (excluding binder)
    let mut arg_positions: Vec<(usize, Ident)> = Vec::new();
    for (i, item) in rule.items.iter().enumerate() {
        if i == *binder_idx {
            continue; // Skip binder
        }

        match item {
            GrammarItem::NonTerminal(cat) => {
                arg_positions.push((i, cat.clone()));
            },
            GrammarItem::Collection { .. } => {
                // Collections will be handled in Phase 5
                // For now, skip term generation for collection constructors
            },
            GrammarItem::Binder { .. } => {}, // Skip
            GrammarItem::Terminal(_) => {},   // Skip
        }
    }

    // Find the body category
    let body_cat = match &rule.items[body_idx] {
        GrammarItem::NonTerminal(cat) => cat,
        _ => panic!("Body should be a NonTerminal"),
    };

    // Find non-body arguments
    let other_args: Vec<(usize, Ident)> = arg_positions
        .iter()
        .filter(|(i, _)| *i != body_idx)
        .cloned()
        .collect();

    if other_args.is_empty() {
        // Simple case: only body (e.g., Lambda x. body)
        generate_simple_binder_case(cat_name, label, body_cat, language)
    } else if other_args.len() == 1 {
        // One non-body arg (e.g., PInput channel x. body)
        generate_binder_with_one_arg(cat_name, label, &other_args[0].1, body_cat, language)
    } else {
        // Multiple non-body args - use simplified approach
        generate_binder_with_multiple_args(cat_name, label, &other_args, body_cat, language)
    }
}

fn generate_simple_binder_case(
    cat_name: &Ident,
    label: &Ident,
    body_cat: &Ident,
    language: &LanguageDef,
) -> TokenStream {
    if !is_lang_type(body_cat, language) {
        return quote! {};
    }

    let body_field = category_to_field_name(body_cat);

    quote! {
        // Generate bodies WITH unique binder variables
        // Count how many vars are binder vars (vars beyond the initial pool)
        let current_binding_depth = self.vars.len() - self.initial_var_count;
        let binder_name = format!("x{}", current_binding_depth);
        let mut extended_vars = self.vars.clone();
        extended_vars.push(binder_name.clone());

        // Create temporary context for generating bodies that can use the binder
        let mut temp_ctx = GenerationContext::new_with_extended_vars(
            extended_vars,
            self.initial_var_count,
            depth - 1,
            self.max_collection_width
        );
        temp_ctx = temp_ctx.generate_all();

        // Get all bodies from temp context (up to depth-1)
        let mut bodies_with_binder = Vec::new();
        for d in 0..depth {
            if let Some(ts) = temp_ctx.#body_field.get(&d) {
                bodies_with_binder.extend(ts.clone());
            }
        }

        // Create scopes with bodies that may reference the binder
        for body in bodies_with_binder {
            let binder_var = mettail_runtime::get_or_create_var(&binder_name);
            let binder = mettail_runtime::Binder(binder_var);
            // Scope::new will automatically close free occurrences of binder_var in body
            let scope = mettail_runtime::Scope::new(binder, Box::new(body));
            terms.push(#cat_name::#label(scope));
        }
    }
}

fn generate_binder_with_one_arg(
    cat_name: &Ident,
    label: &Ident,
    arg_cat: &Ident,
    body_cat: &Ident,
    language: &LanguageDef,
) -> TokenStream {
    if !is_lang_type(arg_cat, language) || !is_lang_type(body_cat, language) {
        return quote! {};
    }

    let arg_field = category_to_field_name(arg_cat);
    let body_field = category_to_field_name(body_cat);

    quote! {
        // Generate bodies WITH unique binder variable
        let current_binding_depth = self.vars.len() - self.initial_var_count;
        let binder_name = format!("x{}", current_binding_depth);
        let mut extended_vars = self.vars.clone();
        extended_vars.push(binder_name.clone());

        let mut temp_ctx = GenerationContext::new_with_extended_vars(
            extended_vars,
            self.initial_var_count,
            depth - 1,
            self.max_collection_width
        );
        temp_ctx = temp_ctx.generate_all();

        // Collect all bodies from temp context
        let mut bodies_with_binder = Vec::new();
        for d in 0..depth {
            if let Some(terms) = temp_ctx.#body_field.get(&d) {
                bodies_with_binder.extend(terms.clone());
            }
        }

        // Generate with all depth combinations
        for d1 in 0..depth {
            if let Some(args1) = self.#arg_field.get(&d1) {
                for arg1 in args1 {
                    for body in &bodies_with_binder {
                        let binder_var = mettail_runtime::get_or_create_var(&binder_name);
                        let binder = mettail_runtime::Binder(binder_var);
                        // Scope::new will close free binder_var in body to bound variable
                        let scope = mettail_runtime::Scope::new(binder, Box::new(body.clone()));

                        // Check depth constraint
                        // This is approximate since we don't track individual body depths
                        terms.push(#cat_name::#label(
                            Box::new(arg1.clone()),
                            scope
                        ));
                    }
                }
            }
        }
    }
}

fn generate_binder_with_multiple_args(
    cat_name: &Ident,
    label: &Ident,
    other_args: &[(usize, Ident)],
    body_cat: &Ident,
    language: &LanguageDef,
) -> TokenStream {
    // Simplified: use depth-1 for all args
    if !is_lang_type(body_cat, language) {
        return quote! {};
    }

    // Bail if any arg is not a language type
    for (_, cat) in other_args {
        if !is_lang_type(cat, language) {
            return quote! {};
        }
    }

    let body_field = category_to_field_name(body_cat);
    let n = other_args.len();

    // Build constructor arguments
    let constructor_args: Vec<TokenStream> = (0..n)
        .map(|i| {
            let arg_i = syn::Ident::new(&format!("arg{}", i), proc_macro2::Span::call_site());
            quote! { Box::new(#arg_i.clone()) }
        })
        .collect();

    // Build nested code from inside out: innermost is the body loop + push
    let mut inner = quote! {
        for body in &bodies_with_binder {
            let binder_var = mettail_runtime::get_or_create_var(&binder_name);
            let binder = mettail_runtime::Binder(binder_var);
            let scope = mettail_runtime::Scope::new(binder, Box::new(body.clone()));
            terms.push(#cat_name::#label(
                #(#constructor_args,)*
                scope
            ));
        }
    };

    // Wrap with for loops (innermost arg last, building outward)
    for i in (0..n).rev() {
        let args_i = syn::Ident::new(&format!("args{}", i), proc_macro2::Span::call_site());
        let arg_i = syn::Ident::new(&format!("arg{}", i), proc_macro2::Span::call_site());
        inner = quote! {
            for #arg_i in #args_i {
                #inner
            }
        };
    }

    // Wrap with if-let guards (innermost arg last, building outward)
    for i in (0..n).rev() {
        let field = category_to_field_name(&other_args[i].1);
        let args_i = syn::Ident::new(&format!("args{}", i), proc_macro2::Span::call_site());
        inner = quote! {
            if let Some(#args_i) = self.#field.get(&d) {
                #inner
            }
        };
    }

    quote! {
        if depth > 0 {
            let d = depth - 1;

            // Generate bodies WITH unique binder variable
            let current_binding_depth = self.vars.len() - self.initial_var_count;
            let binder_name = format!("x{}", current_binding_depth);
            let mut extended_vars = self.vars.clone();
            extended_vars.push(binder_name.clone());

            let mut temp_ctx = GenerationContext::new_with_extended_vars(
                extended_vars,
                self.initial_var_count,
                d,
                self.max_collection_width
            );
            temp_ctx = temp_ctx.generate_all();

            let mut bodies_with_binder = Vec::new();
            for depth_i in 0..=d {
                if let Some(terms) = temp_ctx.#body_field.get(&depth_i) {
                    bodies_with_binder.extend(terms.clone());
                }
            }

            #inner
        }
    }
}

/// Generate case for constructor with collections
/// Example: PPar(HashBag<Proc>) generates bags of various sizes
fn generate_collection_constructor_case(
    cat_name: &Ident,
    rule: &GrammarRule,
    language: &LanguageDef,
) -> TokenStream {
    let label = &rule.label;

    // Find the collection field
    let (collection_idx, element_cat) = rule
        .items
        .iter()
        .enumerate()
        .find_map(|(i, item)| match item {
            GrammarItem::Collection { element_type, .. } => Some((i, element_type.clone())),
            _ => None,
        })
        .expect("Collection constructor must have a collection field");

    // Check if there are other (non-collection) fields
    let other_fields: Vec<(usize, Ident)> = rule
        .items
        .iter()
        .enumerate()
        .filter_map(|(i, item)| {
            if i == collection_idx {
                return None;
            }
            match item {
                GrammarItem::NonTerminal(cat) => Some((i, cat.clone())),
                _ => None,
            }
        })
        .collect();

    if other_fields.is_empty() {
        // Pure collection constructor (e.g., PPar(HashBag<Proc>))
        generate_pure_collection_case(cat_name, label, &element_cat, language)
    } else {
        // Mixed constructor (e.g., PAmb(Name, Proc) where Proc is a collection)
        // For now, skip these as they're more complex
        quote! {}
    }
}

/// Generate a pure collection constructor (only one field, which is a collection)
fn generate_pure_collection_case(
    cat_name: &Ident,
    label: &Ident,
    element_cat: &Ident,
    language: &LanguageDef,
) -> TokenStream {
    if !is_lang_type(element_cat, language) {
        return quote! {};
    }

    let field_name = category_to_field_name(element_cat);
    let is_list = language
        .get_type(cat_name)
        .and_then(|t| t.collection_kind.as_ref())
        .map(|ck| matches!(ck, CollectionCategory::List(_)))
        .unwrap_or(false);
    let is_bag = language
        .get_type(cat_name)
        .and_then(|t| t.collection_kind.as_ref())
        .map(|ck| matches!(ck, CollectionCategory::Bag(_)))
        .unwrap_or(false);

    if is_list {
        quote! {
            for size in 0..=self.max_collection_width {
                if size == 0 {
                    terms.push(#cat_name::#label(Vec::new()));
                } else if size == 1 {
                    for d in 0..depth {
                        if let Some(elems) = self.#field_name.get(&d) {
                            for elem in elems {
                                let mut vec = Vec::new();
                                vec.push(elem.clone());
                                terms.push(#cat_name::#label(vec));
                            }
                        }
                    }
                } else if size == 2 {
                    for d1 in 0..depth {
                        for d2 in 0..depth {
                            if let Some(elems1) = self.#field_name.get(&d1) {
                                if let Some(elems2) = self.#field_name.get(&d2) {
                                    for elem1 in elems1 {
                                        for elem2 in elems2 {
                                            let mut vec = Vec::new();
                                            vec.push(elem1.clone());
                                            vec.push(elem2.clone());
                                            terms.push(#cat_name::#label(vec));
                                        }
                                    }
                                }
                            }
                        }
                    }
                } else if size == 3 {
                    for d1 in 0..depth {
                        for d2 in 0..depth {
                            for d3 in 0..depth {
                                if let Some(elems1) = self.#field_name.get(&d1) {
                                    if let Some(elems2) = self.#field_name.get(&d2) {
                                        if let Some(elems3) = self.#field_name.get(&d3) {
                                            for elem1 in elems1 {
                                                for elem2 in elems2 {
                                                    for elem3 in elems3 {
                                                        let mut vec = Vec::new();
                                                        vec.push(elem1.clone());
                                                        vec.push(elem2.clone());
                                                        vec.push(elem3.clone());
                                                        terms.push(#cat_name::#label(vec));
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    } else if is_bag {
        quote! {
            for size in 0..=self.max_collection_width {
                if size == 0 {
                    terms.push(#cat_name::#label(mettail_runtime::HashBag::new()));
                } else if size == 1 {
                    for d in 0..depth {
                        if let Some(elems) = self.#field_name.get(&d) {
                            for elem in elems {
                                let mut bag = mettail_runtime::HashBag::new();
                                bag.insert(elem.clone());
                                terms.push(#cat_name::#label(bag));
                            }
                        }
                    }
                } else if size == 2 {
                    for d1 in 0..depth {
                        for d2 in 0..depth {
                            if let Some(elems1) = self.#field_name.get(&d1) {
                                if let Some(elems2) = self.#field_name.get(&d2) {
                                    for elem1 in elems1 {
                                        for elem2 in elems2 {
                                            let mut bag = mettail_runtime::HashBag::new();
                                            bag.insert(elem1.clone());
                                            bag.insert(elem2.clone());
                                            terms.push(#cat_name::#label(bag));
                                        }
                                    }
                                }
                            }
                        }
                    }
                } else if size == 3 {
                    for d1 in 0..depth {
                        for d2 in 0..depth {
                            for d3 in 0..depth {
                                if let Some(elems1) = self.#field_name.get(&d1) {
                                    if let Some(elems2) = self.#field_name.get(&d2) {
                                        if let Some(elems3) = self.#field_name.get(&d3) {
                                            for elem1 in elems1 {
                                                for elem2 in elems2 {
                                                    for elem3 in elems3 {
                                                        let mut bag = mettail_runtime::HashBag::new();
                                                        bag.insert(elem1.clone());
                                                        bag.insert(elem2.clone());
                                                        bag.insert(elem3.clone());
                                                        terms.push(#cat_name::#label(bag));
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    } else {
        quote! {
            for size in 0..=self.max_collection_width {
                if size == 0 {
                    let bag = mettail_runtime::HashBag::new();
                    terms.push(#cat_name::#label(bag));
                } else if size == 1 {
                    for d in 0..depth {
                        if let Some(elems) = self.#field_name.get(&d) {
                            for elem in elems {
                                let mut bag = mettail_runtime::HashBag::new();
                                bag.insert(elem.clone());
                                terms.push(#cat_name::#label(bag));
                            }
                        }
                    }
                } else if size == 2 {
                    for d1 in 0..depth {
                        for d2 in 0..depth {
                            if let Some(elems1) = self.#field_name.get(&d1) {
                                if let Some(elems2) = self.#field_name.get(&d2) {
                                    for elem1 in elems1 {
                                        for elem2 in elems2 {
                                            let mut bag = mettail_runtime::HashBag::new();
                                            bag.insert(elem1.clone());
                                            bag.insert(elem2.clone());
                                            terms.push(#cat_name::#label(bag));
                                        }
                                    }
                                }
                            }
                        }
                    }
                } else if size == 3 {
                    for d1 in 0..depth {
                        for d2 in 0..depth {
                            for d3 in 0..depth {
                                if let Some(elems1) = self.#field_name.get(&d1) {
                                    if let Some(elems2) = self.#field_name.get(&d2) {
                                        if let Some(elems3) = self.#field_name.get(&d3) {
                                            for elem1 in elems1 {
                                                for elem2 in elems2 {
                                                    for elem3 in elems3 {
                                                        let mut bag = mettail_runtime::HashBag::new();
                                                        bag.insert(elem1.clone());
                                                        bag.insert(elem2.clone());
                                                        bag.insert(elem3.clone());
                                                        terms.push(#cat_name::#label(bag));
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}

/// Generate public API methods for each category
fn generate_public_apis(language: &LanguageDef) -> TokenStream {
    let impls: Vec<TokenStream> = language.types.iter().map(|lang_type| {
        let cat_name = &lang_type.name;
        let field_name = category_to_field_name(cat_name);

        quote! {
            impl #cat_name {
                /// Generate all terms up to max_depth
                ///
                /// # Arguments
                /// * `vars` - Pool of variable names for free variables
                /// * `max_depth` - Maximum operator nesting level
                /// * `max_collection_width` - Maximum number of elements in any collection
                ///
                /// # Returns
                /// Sorted, deduplicated vector of terms
                ///
                /// # Warning
                /// Number of terms grows exponentially with depth and collection width!
                /// Recommend max_depth <= 3 and max_collection_width <= 2 for exhaustive generation.
                pub fn generate_terms(vars: &[String], max_depth: usize, max_collection_width: usize) -> Vec<#cat_name> {
                    let ctx = GenerationContext::new(vars.to_vec(), max_depth, max_collection_width);
                    let ctx = ctx.generate_all();

                    let mut all_terms = Vec::new();
                    for depth in 0..=max_depth {
                        if let Some(terms) = ctx.#field_name.get(&depth) {
                            all_terms.extend(terms.clone());
                        }
                    }

                    all_terms.sort();
                    all_terms.dedup();
                    all_terms
                }
            }
        }
    }).collect();

    quote! {
        #(#impls)*
    }
}

/// Helper: convert category name to field name (e.g., Proc -> proc_by_depth)
fn category_to_field_name(cat: &Ident) -> Ident {
    let name = format!("{}_by_depth", cat.to_string().to_lowercase());
    syn::Ident::new(&name, proc_macro2::Span::call_site())
}

/// Helper: convert category name to generation method name (e.g., Proc -> generate_proc)
fn category_to_generate_method(cat: &Ident) -> Ident {
    let name = format!("generate_{}", cat.to_string().to_lowercase());
    syn::Ident::new(&name, proc_macro2::Span::call_site())
}
