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

use mettail_ast::{
    grammar::{GrammarItem, GrammarRule, NonTerminalKind, TermParam},
    language::LanguageDef,
};
use crate::gen::native::NativeType;
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
    language: &LanguageDef,
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
            .filter(|item| matches!(item, GrammarItem::NonTerminal { .. } | GrammarItem::Binder { .. }))
            .collect();

        if non_terminals.is_empty() {
            // Nullary constructor
            cases.push(quote! { #cat_name::#label });
        } else if non_terminals.len() == 1 {
            // Check if it's a Var or literal constructor (Integer, Boolean, StringLiteral, FloatLiteral)
            if let GrammarItem::NonTerminal { ident: nt, kind } = non_terminals[0] {
                if *kind == NonTerminalKind::Var {
                    // VarRef or other Var rules — generate variables
                    // using a spec-derived ident name (replaces
                    // hard-coded "_" fallback). When `vars` is non-
                    // empty we use one from the binder context;
                    // otherwise we use `spec_admitted_var_name(language)`
                    // which derives from the language's effective
                    // Ident pattern.
                    let fallback_name = crate::gen::spec_admitted_var_name(language);
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
                                        mettail_runtime::get_or_create_var(#fallback_name)
                                    )
                                )
                            )
                        }
                    });
                } else if kind.is_literal() {
                    // Literal rules — generate native values whose RANGE
                    // is projected onto the spec's effective lexer
                    // pattern. Reads `effective_pattern_for(language,
                    // "Integer"|"Float"|"StringLit")` and consults
                    // `classify_token` to decide whether the pattern
                    // admits negatives. Replaces hard-coded
                    // `-100..100` / `0..20` ranges with spec-derived
                    // bounds.
                    use crate::gen::test_gen::automaton_walk::classify::{
                        classify_token, effective_pattern_for, language_equivalent, CanonicalKind,
                    };
                    let literal_case = match kind {
                        NonTerminalKind::Integer => {
                            let pattern = effective_pattern_for(language, "Integer");
                            let signed = matches!(classify_token(&pattern), CanonicalKind::SignedInt)
                                || (matches!(classify_token(&pattern), CanonicalKind::Unclassified)
                                    && language_equivalent(&pattern, "-?[0-9]+"));
                            if signed {
                                quote! {
                                    let val = rng.gen_range(-100i32..100i32);
                                    #cat_name::#label(val)
                                }
                            } else {
                                quote! {
                                    let val = rng.gen_range(0i32..100i32);
                                    #cat_name::#label(val)
                                }
                            }
                        },
                        NonTerminalKind::Boolean => quote! {
                            let val: bool = rng.gen();
                            #cat_name::#label(val)
                        },
                        NonTerminalKind::FloatLiteral => {
                            let is_f32 = language
                                .types
                                .iter()
                                .find(|t| t.name == *cat_name)
                                .and_then(|t| t.native_type.as_ref())
                                .map(|n| NativeType::from_syn_type(n).is_float() && NativeType::from_syn_type(n) == NativeType::Float32)
                                .unwrap_or(false);
                            let pattern = effective_pattern_for(language, "Float");
                            let signed = matches!(classify_token(&pattern), CanonicalKind::SignedFloat)
                                || (matches!(classify_token(&pattern), CanonicalKind::Unclassified)
                                    && language_equivalent(
                                        &pattern,
                                        r"-?[0-9]+\.[0-9]+([eE][+-]?[0-9]+)?",
                                    ));
                            let (wrapper_ty, val_ty) = if is_f32 {
                                if signed {
                                    (quote! { mettail_runtime::CanonicalFloat32 },
                                     quote! { rng.gen_range(-100.0f32..100.0f32) })
                                } else {
                                    (quote! { mettail_runtime::CanonicalFloat32 },
                                     quote! { rng.gen_range(0.0f32..100.0f32) })
                                }
                            } else if signed {
                                (quote! { mettail_runtime::CanonicalFloat64 },
                                 quote! { rng.gen_range(-100.0f64..100.0f64) })
                            } else {
                                (quote! { mettail_runtime::CanonicalFloat64 },
                                 quote! { rng.gen_range(0.0f64..100.0f64) })
                            };
                            quote! {
                                let val = #val_ty;
                                #cat_name::#label(#wrapper_ty::from(val))
                            }
                        },
                        NonTerminalKind::StringLiteral => {
                            // The default StringLit pattern admits any
                            // sequence of non-quote/non-backslash bytes
                            // (or escape sequences). For sampling we
                            // emit a small lowercase-ASCII string —
                            // valid under the default pattern. If the
                            // spec overrides StringLit to a more
                            // restrictive pattern the parser will
                            // surface a roundtrip failure loudly per
                            // the user directive.
                            let _ = effective_pattern_for(language, "StringLit");
                            quote! {
                                let len = rng.gen_range(0..20usize);
                                let val = (0..len).map(|_| {
                                    let idx = rng.gen_range(0..26u8);
                                    (b'a' + idx) as char
                                }).collect::<String>();
                                #cat_name::#label(val)
                            }
                        },
                        _ => continue,
                    };
                    cases.push(literal_case);
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
        let is_multi_binder = rule.term_context.as_ref().is_some_and(|ctx| {
            ctx.iter()
                .any(|p| matches!(p, TermParam::MultiAbstraction { .. }))
        });

        if is_multi_binder {
            // Handle multi-binder constructors (e.g., ^[x,y].body).
            // Skip if rule also has collections — that combination requires
            // Collection+MultiBinder codegen (not yet implemented).
            let has_collections = rule
                .items
                .iter()
                .any(|item| matches!(item, GrammarItem::Collection { .. }));
            if !rule.bindings.is_empty() && !has_collections {
                constructor_cases.push(
                    generate_random_multi_binder_constructor(cat_name, rule, language),
                );
            }
            continue;
        }

        // Check if this has collections
        let has_collections = rule
            .items
            .iter()
            .any(|item| matches!(item, GrammarItem::Collection { .. }));

        // B9 / Class 2 (2026-05-08): skip the collection-constructor random
        // generator for multi-Param rules whose collection slot is part of
        // a binder-rule body. The collection-constructor codegen assumes a
        // single-arg HashBag-typed tuple variant (Class-5 collection-literal
        // pattern); both assumptions break for Class-2 binder rules. Future
        // work: add a Class-2 random-term generator that fills both the
        // tag param(s) and the collection.
        let is_class2_binder = rule.term_context.as_ref().is_some_and(|ctx| {
            let simple_count = ctx
                .iter()
                .filter(|p| matches!(p, TermParam::Simple { .. }))
                .count();
            simple_count > 1
        });

        if has_collections && !is_class2_binder {
            // Handle collection constructors
            constructor_cases
                .push(generate_random_collection_constructor(cat_name, rule, language));
            continue;
        }
        if has_collections && is_class2_binder {
            // Class-2 binder rule with collection slot: skip random gen.
            continue;
        }

        let non_terminals: Vec<_> = rule
            .items
            .iter()
            .filter_map(|item| match item {
                GrammarItem::NonTerminal { ident: nt, .. } => Some(nt.clone()),
                GrammarItem::Binder { category } => Some(category.clone()),
                _ => None,
            })
            .collect();

        // Skip depth 0 constructors
        if non_terminals.is_empty() {
            continue;
        }

        // Skip Var and literal constructors at depth > 0 (they're depth 0 only)
        if non_terminals.len() == 1 {
            if let Some(kind) = rule.items.iter().find_map(|item| {
                if let GrammarItem::NonTerminal { kind, .. } = item {
                    Some(*kind)
                } else {
                    None
                }
            }) {
                if kind.is_builtin() {
                    continue;
                }
            }
        }

        // Phase 3A (predicated types): random term generation for
        // guarded constructors requires random predicate generation,
        // which is out of scope for the current term_gen pipeline.
        // Constructors with `?guard:Guard` slots are skipped from
        // random generation; tests that need to construct guarded
        // terms should build them by hand. The same skip is applied
        // in `exhaustive.rs:478-491` and `logic/helpers.rs`.
        let has_guard_slot = rule
            .term_context
            .as_ref()
            .map(|ctx| ctx.iter().any(|p| matches!(p, TermParam::GuardBody { .. })))
            .unwrap_or(false);
        if has_guard_slot {
            continue;
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

/// Generate random simple constructor (no binders).
///
/// Opt-Group: when the rule's term_context contains `TermParam::Optional`,
/// the corresponding variant fields are `Option<Box<T>>`. Random generation
/// always emits `None` for those positions (Some-generation is a future
/// enhancement; defaulting to None is a defensible no-coverage-loss choice
/// since shipped random testers don't exercise optional groups).
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
            GrammarItem::NonTerminal { ident: nt, .. } => Some(nt.clone()),
            _ => None,
        })
        .collect();

    // Compute the OPTIONAL-suffix count: how many of the trailing arg
    // positions are Option<Box<T>> per Opt-Group flattening. The
    // `convert_term_context_to_items` helper appends Optional inner items
    // AT THEIR DECLARATION POSITION; for the IfElse pilot, Optional sits
    // at the end of the term_context so all optional positions are at
    // the suffix. Multi-Optional or non-trailing Optional grammars are
    // not currently emitted by random.rs (which is a heuristic-driven
    // generator, not a fuzzer-strict one) — defer until a shipped grammar
    // exercises that shape.
    let optional_count: usize = rule
        .term_context
        .as_ref()
        .map(|ctx| {
            fn count(p: &mettail_ast::grammar::TermParam) -> usize {
                use mettail_ast::grammar::TermParam;
                match p {
                    TermParam::Optional { params: inner } => inner
                        .iter()
                        .map(count_one)
                        .sum(),
                    _ => 0,
                }
            }
            fn count_one(p: &mettail_ast::grammar::TermParam) -> usize {
                use mettail_ast::grammar::TermParam;
                match p {
                    TermParam::Simple { .. } | TermParam::GuardBody { .. } => 1,
                    TermParam::Abstraction { .. } | TermParam::MultiAbstraction { .. } => 1,
                    TermParam::Optional { params: inner } => {
                        inner.iter().map(count_one).sum()
                    }
                }
            }
            ctx.iter().map(count).sum()
        })
        .unwrap_or(0);

    let positional_count = arg_cats.len().saturating_sub(optional_count);
    let positional_cats: Vec<Ident> = arg_cats.iter().take(positional_count).cloned().collect();

    let core: TokenStream = match positional_cats.len() {
        0 => quote! { #cat_name::#label() },
        1 => generate_random_unary(cat_name, label, &positional_cats[0], language),
        2 => generate_random_binary(cat_name, label, &positional_cats[0], &positional_cats[1], language),
        _ => generate_random_nary(cat_name, label, &positional_cats, language),
    };

    if optional_count == 0 {
        core
    } else {
        // Re-emit the variant call appending `None` for each Optional position.
        let none_args: Vec<TokenStream> = (0..optional_count).map(|_| quote! { None }).collect();
        // The `core` token stream ends with `Cat::Label(args)`. Inject `None`
        // before the closing paren by re-constructing:
        let positional_args: Vec<TokenStream> = positional_cats
            .iter()
            .enumerate()
            .map(|(_, cat)| {
                if !is_lang_type(cat, language) {
                    quote! { panic!("Non-exported category") }
                } else {
                    quote! {
                        Box::new(#cat::generate_random_at_depth_internal(
                            vars, depth - 1, max_collection_width, rng, binding_depth,
                        ))
                    }
                }
            })
            .collect();
        let _ = core;
        quote! {
            #cat_name::#label(
                #(#positional_args,)*
                #(#none_args),*
            )
        }
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
    // Handle Var specially - it's a built-in type, generate directly as OrdVar
    let is_arg1_var = NonTerminalKind::classify(&arg1_cat.to_string()) == NonTerminalKind::Var;
    let is_arg2_var = NonTerminalKind::classify(&arg2_cat.to_string()) == NonTerminalKind::Var;

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
        GrammarItem::NonTerminal { ident: cat, .. } => cat,
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
                    GrammarItem::NonTerminal { ident: cat, .. } => Some((i, cat.clone())),
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

/// Generate random multi-binder constructor (e.g., ^[x,y].body)
///
/// Generates 1-3 random binder names, creates `Vec<Binder>`, and wraps with
/// `Scope::new(binders, Box::new(body))`.
fn generate_random_multi_binder_constructor(
    cat_name: &Ident,
    rule: &GrammarRule,
    language: &LanguageDef,
) -> TokenStream {
    let label = &rule.label;

    let (binder_idx, body_indices) = &rule.bindings[0];
    let body_idx = body_indices[0];

    // Find body category
    let body_cat = match &rule.items[body_idx] {
        GrammarItem::NonTerminal { ident: cat, .. } => cat,
        _ => panic!("Body should be NonTerminal"),
    };

    if !is_lang_type(body_cat, language) {
        return quote! {};
    }

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
                    GrammarItem::NonTerminal { ident: cat, .. } => Some((i, cat.clone())),
                    _ => None,
                }
            }
        })
        .collect();

    // Generate multi-binder scope construction
    // Binder name prefix derived from the spec's effective Ident
    // pattern (defaults to "a" for the standard Ident pattern).
    let var_prefix = crate::gen::spec_admitted_var_name(language);
    let scope_construction = quote! {
        // Generate 1-3 binder names
        let num_binders = rng.gen_range(1usize..=3);
        let mut binder_names = Vec::with_capacity(num_binders);
        let mut extended_vars = vars.to_vec();
        for j in 0..num_binders {
            let binder_name = format!("{}{}_{}", #var_prefix, binding_depth, j);
            extended_vars.push(binder_name.clone());
            binder_names.push(binder_name);
        }

        let body = #body_cat::generate_random_at_depth_internal(
            &extended_vars,
            depth - 1,
            max_collection_width,
            rng,
            binding_depth + num_binders,
        );

        let binders: Vec<mettail_runtime::Binder<String>> = binder_names
            .into_iter()
            .map(|s| mettail_runtime::Binder(mettail_runtime::get_or_create_var(&s)))
            .collect();
        let scope = mettail_runtime::Scope::new(binders, Box::new(body));
    };

    if other_args.is_empty() {
        // Simple multi-binder: just body
        quote! {
            #scope_construction
            #cat_name::#label(scope)
        }
    } else if other_args.len() == 1 {
        let arg_cat = &other_args[0].1;
        if !is_lang_type(arg_cat, language) {
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
            #scope_construction
            #cat_name::#label(Box::new(arg1), scope)
        }
    } else {
        // Multiple args: simplified
        let arg_generations: Vec<TokenStream> = other_args.iter().map(|(_, cat)| {
            if !is_lang_type(cat, language) {
                return quote! { panic!("Non-exported category") };
            }
            quote! {
                Box::new(#cat::generate_random_at_depth_internal(vars, depth - 1, max_collection_width, rng, binding_depth))
            }
        }).collect();

        quote! {
            #scope_construction
            #cat_name::#label(#(#arg_generations,)* scope)
        }
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

    let var_prefix = crate::gen::spec_admitted_var_name(language);
    quote! {
        let binder_name = format!("{}{}", #var_prefix, binding_depth);
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
    let var_prefix = crate::gen::spec_admitted_var_name(language);

    quote! {
        let d1 = rng.gen_range(0..depth);
        let d2 = if d1 == depth - 1 {
            rng.gen_range(0..depth)
        } else {
            depth - 1
        };

        let arg1 = #arg_cat::generate_random_at_depth_internal(vars, d1, max_collection_width, rng, binding_depth);

        let binder_name = format!("{}{}", #var_prefix, binding_depth);
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

    let var_prefix = crate::gen::spec_admitted_var_name(language);
    quote! {
        let binder_name = format!("{}{}", #var_prefix, binding_depth);
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
    use mettail_ast::language::CollectionCategory;

    let label = &rule.label;

    // Find the collection field and its type
    let (element_cat, _coll_type) = rule
        .items
        .iter()
        .find_map(|item| match item {
            GrammarItem::Collection { element_type, coll_type, .. } => {
                Some((element_type.clone(), coll_type.clone()))
            },
            _ => None,
        })
        .expect("Collection constructor must have a collection field");

    if !is_lang_type(&element_cat, language) {
        return quote! { panic!("Non-type collection element category") };
    }

    let is_list = language
        .get_type(cat_name)
        .and_then(|t| t.collection_kind.as_ref())
        .map(|ck| matches!(ck, CollectionCategory::List(_)))
        .unwrap_or(false);
    let is_map = language
        .get_type(cat_name)
        .and_then(|t| t.collection_kind.as_ref())
        .map(|ck| matches!(ck, CollectionCategory::Map(_)))
        .unwrap_or(false);

    if is_list {
        quote! {
            {
                let size = rng.gen_range(0..=max_collection_width);
                let mut vec = Vec::new();
                for _ in 0..size {
                    let elem_depth = if depth > 0 { rng.gen_range(0..depth) } else { 0 };
                    let elem = #element_cat::generate_random_at_depth_internal(
                        vars,
                        elem_depth,
                        max_collection_width,
                        rng,
                        binding_depth
                    );
                    vec.push(elem);
                }
                #cat_name::#label(vec)
            }
        }
    } else if is_map {
        quote! {
            {
                let size = rng.gen_range(0..=max_collection_width);
                let mut m = mettail_runtime::HashMapLit::new();
                for _ in 0..size {
                    let dk = if depth > 0 { rng.gen_range(0..depth) } else { 0 };
                    let dv = if depth > 0 { rng.gen_range(0..depth) } else { 0 };
                    let k = #element_cat::generate_random_at_depth_internal(
                        vars,
                        dk,
                        max_collection_width,
                        rng,
                        binding_depth
                    );
                    let v = #element_cat::generate_random_at_depth_internal(
                        vars,
                        dv,
                        max_collection_width,
                        rng,
                        binding_depth
                    );
                    m.insert(k, v);
                }
                #cat_name::#label(m)
            }
        }
    } else {
        // List and Bag both use the same bag-shaped generation when not is_list
        quote! {
            {
                let size = rng.gen_range(0..=max_collection_width);
                let mut bag = mettail_runtime::HashBag::new();
                for _ in 0..size {
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
}
