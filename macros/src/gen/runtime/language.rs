//! Language struct and Term wrapper generation
//!
//! This module generates:
//! - `{Name}Term` wrapper implementing `mettail_runtime::Term`
//! - `{Name}Language` struct implementing `mettail_runtime::Language`

use crate::ast::grammar::GrammarItem;
use crate::ast::language::LanguageDef;
use crate::gen::{generate_literal_label, generate_var_label};
use proc_macro2::Span;
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use syn::{Ident, LitStr};

/// Generate the complete language implementation
pub fn generate_language_impl(language: &LanguageDef) -> TokenStream {
    let name = &language.name;
    let name_str = name.to_string();
    let name_lower = name_str.to_lowercase();

    // Get the primary type (first type in the language)
    let primary_type = language
        .types
        .first()
        .map(|t| &t.name)
        .expect("Language must have at least one type");

    let (term_wrapper, language_struct, language_trait_impl) = if language.types.len() > 1 {
        (
            generate_term_wrapper_multi(name, language),
            generate_language_struct_multi(name, &name_str, &name_lower, language),
            generate_language_trait_impl_multi(name, &name_str, &name_lower, language),
        )
    } else {
        (
            generate_term_wrapper(name, primary_type),
            generate_language_struct(name, primary_type, &name_str, &name_lower, language),
            generate_language_trait_impl(name, primary_type, &name_str, &name_lower, language),
        )
    };

    quote! {
        #term_wrapper
        #language_struct
        #language_trait_impl
    }
}

/// Generate the Term wrapper struct
fn generate_term_wrapper(name: &syn::Ident, primary_type: &syn::Ident) -> TokenStream {
    let term_name = format_ident!("{}Term", name);

    quote! {
        /// Wrapper for the primary type that implements `mettail_runtime::Term`
        #[derive(Clone)]
        pub struct #term_name(pub #primary_type);

        impl mettail_runtime::Term for #term_name {
            fn clone_box(&self) -> Box<dyn mettail_runtime::Term> {
                Box::new(self.clone())
            }

            fn term_id(&self) -> u64 {
                use std::collections::hash_map::DefaultHasher;
                use std::hash::{Hash, Hasher};
                let mut hasher = DefaultHasher::new();
                self.0.hash(&mut hasher);
                hasher.finish()
            }

            fn term_eq(&self, other: &dyn mettail_runtime::Term) -> bool {
                if let Some(other_term) = other.as_any().downcast_ref::<#term_name>() {
                    self.0 == other_term.0
                } else {
                    false
                }
            }

            fn as_any(&self) -> &dyn std::any::Any {
                self
            }
        }

        impl std::fmt::Display for #term_name {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, "{}", self.0)
            }
        }

        impl std::fmt::Debug for #term_name {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, "{:?}", self.0)
            }
        }
    }
}

/// Generate the Term wrapper with an enum when the language has multiple types
/// (any combination of built-in or user-defined types, e.g. Int/Bool/Str or Proc/Name).
fn generate_term_wrapper_multi(name: &syn::Ident, language: &LanguageDef) -> TokenStream {
    let term_name = format_ident!("{}Term", name);
    let inner_enum_name = format_ident!("{}TermInner", name);

    let enum_variants: Vec<TokenStream> = language
        .types
        .iter()
        .map(|t| {
            let cat = &t.name;
            quote! { #cat(#cat) }
        })
        .collect();

    let display_arms: Vec<TokenStream> = language
        .types
        .iter()
        .map(|t| {
            let cat = &t.name;
            quote! { #inner_enum_name::#cat(v) => write!(f, "{}", v) }
        })
        .collect();
    let debug_arms: Vec<TokenStream> = language
        .types
        .iter()
        .map(|t| {
            let cat = &t.name;
            quote! { #inner_enum_name::#cat(v) => write!(f, "{:?}", v) }
        })
        .collect();

    let env_name = format_ident!("{}Env", name);
    let substitute_arms: Vec<TokenStream> = language
        .types
        .iter()
        .map(|t| {
            let cat = &t.name;
            let variant = format_ident!("{}", cat);
            quote! { #inner_enum_name::#variant(t) => #inner_enum_name::#variant(t.substitute_env(env)) }
        })
        .collect();

    // Cross-category variable resolution: if after substitution we still have a variable,
    // look it up in other categories (e.g. "x" parsed as Int but bound as Bool -> use Bool value).
    let var_label_per_cat: Vec<(Ident, Ident)> = language
        .types
        .iter()
        .map(|t| (t.name.clone(), generate_var_label(&t.name)))
        .collect();
    let cross_resolve_arms: Vec<TokenStream> = var_label_per_cat
        .iter()
        .map(|(cat, var_label)| {
            let other_lookups: Vec<TokenStream> = language
                .types
                .iter()
                .filter(|t| t.name != *cat)
                .map(|t| {
                    let variant = format_ident!("{}", t.name);
                    let field = format_ident!("{}", t.name.to_string().to_lowercase());
                    quote! {
                        if let Some(val) = env.#field.get(&name) {
                            return #inner_enum_name::#variant(val.clone());
                        }
                    }
                })
                .collect();
            quote! {
                #inner_enum_name::#cat(#cat::#var_label(v)) => {
                    let name = match &v.0 {
                        mettail_runtime::Var::Free(fv) => fv.pretty_name.as_ref().map(|s| s.to_string()),
                        mettail_runtime::Var::Bound(bv) => bv.pretty_name.as_ref().map(|s| s.to_string()),
                    };
                    if let Some(name) = name {
                        #(#other_lookups)*
                    }
                }
            }
        })
        .collect();

    quote! {
        /// Inner term enum for multi-category languages (one variant per type in the language).
        #[derive(Clone, PartialEq, Eq, Hash)]
        pub enum #inner_enum_name {
            #(#enum_variants),*
        }

        impl #inner_enum_name {
            /// Substitute environment bindings into the term.
            /// Variables are resolved by name; if a variable is bound in another category
            /// (e.g. "x" parsed as Int but x = true in env), the bound value is used.
            pub fn substitute_env(&self, env: &#env_name) -> Self {
                let substituted = match self {
                    #(#substitute_arms),*
                };
                // Cross-category: if still a variable, try resolving from other categories
                match &substituted {
                    #(#cross_resolve_arms)*
                    _ => {}
                }
                substituted
            }


        }

        impl std::fmt::Display for #inner_enum_name {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                match self {
                    #(#display_arms),*
                }
            }
        }

        impl std::fmt::Debug for #inner_enum_name {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                match self {
                    #(#debug_arms),*
                }
            }
        }

        /// Wrapper for the term that implements `mettail_runtime::Term`
        #[derive(Clone)]
        pub struct #term_name(pub #inner_enum_name);

        impl mettail_runtime::Term for #term_name {
            fn clone_box(&self) -> Box<dyn mettail_runtime::Term> {
                Box::new(self.clone())
            }

            fn term_id(&self) -> u64 {
                use std::collections::hash_map::DefaultHasher;
                use std::hash::{Hash, Hasher};
                let mut hasher = DefaultHasher::new();
                self.0.hash(&mut hasher);
                hasher.finish()
            }

            fn term_eq(&self, other: &dyn mettail_runtime::Term) -> bool {
                if let Some(other_term) = other.as_any().downcast_ref::<#term_name>() {
                    self.0 == other_term.0
                } else {
                    false
                }
            }

            fn as_any(&self) -> &dyn std::any::Any {
                self
            }
        }

        impl std::fmt::Display for #term_name {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, "{}", self.0)
            }
        }

        impl std::fmt::Debug for #term_name {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, "{:?}", self.0)
            }
        }
    }
}

/// Generate the Language struct with helper methods
fn generate_language_struct(
    name: &syn::Ident,
    primary_type: &syn::Ident,
    _name_str: &str,
    name_lower: &str,
    language: &LanguageDef,
) -> TokenStream {
    let language_name = format_ident!("{}Language", name);
    let term_name = format_ident!("{}Term", name);
    let _metadata_name = format_ident!("{}Metadata", name);
    let env_name = format_ident!("{}Env", name);
    let parser_name = format_ident!("{}Parser", primary_type);
    let parser_mod = format_ident!("{}", name_lower);
    let ascent_source = format_ident!("{}_source", name_lower);

    // Primary type relation names (lowercase)
    let primary_lower = primary_type.to_string().to_lowercase();
    let primary_relation = format_ident!("{}", primary_lower);
    let rw_relation = format_ident!("rw_{}", primary_lower);
    let _primary_type_str = primary_type.to_string();

    // Generate type inference helper
    let type_inference_impl = generate_type_inference_helpers(primary_type, language);

    // Generate variable collection implementation
    let var_collection_impl = generate_var_collection_impl(primary_type, language);

    // Generate custom relation extraction code
    let custom_relation_extraction = generate_custom_relation_extraction(language);

    quote! {
        /// Language implementation struct
        ///
        /// Auto-generated by the `language!` macro. Implements `mettail_runtime::Language`.
        pub struct #language_name;

        impl #language_name {
            /// Parse a term from a string (clears var cache for fresh evaluation)
            pub fn parse(input: &str) -> Result<#term_name, std::string::String> {
                mettail_runtime::clear_var_cache();
                Self::parse_preserving_vars(input)
            }

            /// Parse a term without clearing var cache (for environment sharing)
            pub fn parse_preserving_vars(input: &str) -> Result<#term_name, std::string::String> {
                let parser = #parser_mod::#parser_name::new();
                parser
                    .parse(input)
                    .map(#term_name)
                    .map_err(|e| format!("Parse error: {:?}", e))
            }

            /// Run Ascent on a typed term (seeds with term as-is so step-by-step rewrites are visible)
            pub fn run_ascent_typed(term: &#term_name) -> mettail_runtime::AscentResults {
                use ascent::*;

                let initial = term.0.clone();

                let prog = ascent_run! {
                    include_source!(#ascent_source);
                    #primary_relation(initial.clone());
                    step_term(initial.clone());
                };

                // Extract results
                let all_terms: Vec<#primary_type> = prog.#primary_relation
                    .iter()
                    .map(|(p,)| p.clone())
                    .collect();

                let rewrites: Vec<(#primary_type, #primary_type)> = prog
                    .#rw_relation
                    .iter()
                    .map(|(from, to)| (from.clone(), to.clone()))
                    .collect();

                // Build term info
                let mut term_infos = Vec::new();
                for t in &all_terms {
                    let term_id = {
                        use std::collections::hash_map::DefaultHasher;
                        use std::hash::{Hash, Hasher};
                        let mut hasher = DefaultHasher::new();
                        t.hash(&mut hasher);
                        hasher.finish()
                    };
                    let has_rewrites = rewrites.iter().any(|(from, _)| from == t);
                    term_infos.push(mettail_runtime::TermInfo {
                        term_id,
                        display: format!("{}", t),
                        is_normal_form: !has_rewrites,
                    });
                }

                // Build rewrite list
                let rewrite_list: Vec<mettail_runtime::Rewrite> = rewrites
                    .iter()
                    .map(|(from, to)| {
                        use std::collections::hash_map::DefaultHasher;
                        use std::hash::{Hash, Hasher};
                        let mut h1 = DefaultHasher::new();
                        let mut h2 = DefaultHasher::new();
                        from.hash(&mut h1);
                        to.hash(&mut h2);
                        mettail_runtime::Rewrite {
                            from_id: h1.finish(),
                            to_id: h2.finish(),
                            rule_name: Some("rewrite".to_string()),
                        }
                    })
                    .collect();

                // Extract custom relations
                let mut custom_relations = std::collections::HashMap::new();
                #custom_relation_extraction

                mettail_runtime::AscentResults {
                    all_terms: term_infos,
                    rewrites: rewrite_list,
                    equivalences: Vec::new(),
                    custom_relations,
                }
            }

            /// Create a new empty environment
            pub fn create_env() -> #env_name {
                #env_name::new()
            }

            // === Type Inference Helpers ===

            /// Convert InferredType to TermType
            fn inferred_to_term_type(t: &InferredType) -> mettail_runtime::TermType {
                match t {
                    InferredType::Base(cat) => mettail_runtime::TermType::Base(format!("{:?}", cat)),
                    InferredType::Arrow(d, c) => mettail_runtime::TermType::Arrow(
                        Box::new(Self::inferred_to_term_type(d)),
                        Box::new(Self::inferred_to_term_type(c)),
                    ),
                    InferredType::MultiArrow(d, c) => mettail_runtime::TermType::MultiArrow(
                        Box::new(Self::inferred_to_term_type(d)),
                        Box::new(Self::inferred_to_term_type(c)),
                    ),
                }
            }

            /// Infer the type of a term (typed version)
            pub fn infer_term_type_typed(term: &#primary_type) -> mettail_runtime::TermType {
                #type_inference_impl
            }

            /// Infer the type of a variable in a term (typed version)
            /// This finds both free and bound variables.
            pub fn infer_var_type_typed(term: &#primary_type, var_name: &str) -> Option<mettail_runtime::TermType> {
                // First try the direct method for free variables
                if let Some(t) = term.infer_var_type(var_name) {
                    return Some(Self::inferred_to_term_type(&t));
                }
                // If not found, search through all variables including bound ones
                Self::infer_var_types_typed(term)
                    .into_iter()
                    .find(|v| v.name == var_name)
                    .map(|v| v.ty)
            }

            /// Get all variable types in a term (typed version)
            /// This includes both bound variables (from lambdas) and free variables.
            pub fn infer_var_types_typed(term: &#primary_type) -> Vec<mettail_runtime::VarTypeInfo> {
                let mut result = Vec::new();
                let mut seen = std::collections::HashSet::new();
                Self::collect_all_vars_with_types(term, term, &mut result, &mut seen);
                result
            }

            /// Collect all variables (bound and free) with their types
            /// `root_term` is the original term for context, `term` is current position
            fn collect_all_vars_with_types(
                root_term: &#primary_type,
                term: &#primary_type,
                result: &mut Vec<mettail_runtime::VarTypeInfo>,
                seen: &mut std::collections::HashSet<std::string::String>,
            ) {
                Self::collect_all_vars_impl(root_term, term, result, seen);
            }
        }

        // Variable collection implementation with proper term traversal
        #[allow(unused_variables, unreachable_patterns)]
        impl #language_name {
            fn collect_all_vars_impl(
                root_term: &#primary_type,
                term: &#primary_type,
                result: &mut Vec<mettail_runtime::VarTypeInfo>,
                seen: &mut std::collections::HashSet<std::string::String>,
            ) {
                match term {
                    #var_collection_impl
                }
            }
        }
    }
}

/// Generate the collect_all_vars_impl method with proper traversal
fn generate_var_collection_impl(primary_type: &Ident, language: &LanguageDef) -> TokenStream {
    let categories: Vec<_> = language.types.iter().map(|t| &t.name).collect();

    // Generate lambda handling arms
    let mut lambda_arms: Vec<TokenStream> = Vec::new();

    for domain in &categories {
        let domain_lit = LitStr::new(&domain.to_string(), domain.span());
        let lam_variant = format_ident!("Lam{}", domain);
        let mlam_variant = format_ident!("MLam{}", domain);

        // LamX variant - extract binder and recurse into body
        lambda_arms.push(quote! {
            #primary_type::#lam_variant(scope) => {
                // Use unbind to get the binder with proper type
                let (binder, body) = scope.clone().unbind();
                if let Some(name) = &binder.0.pretty_name {
                    if !seen.contains(name) {
                        seen.insert(name.clone());
                        // Infer the binder's type from how it's used in the body
                        let var_type = body.infer_var_type(name)
                            .map(|t| Self::inferred_to_term_type(&t))
                            .unwrap_or_else(|| mettail_runtime::TermType::Base(#domain_lit.to_string()));
                        result.push(mettail_runtime::VarTypeInfo {
                            name: name.clone(),
                            ty: var_type,
                        });
                    }
                }
                // Recurse into body (body is Box<T>, so deref it)
                Self::collect_all_vars_impl(root_term, body.as_ref(), result, seen);
            }
        });

        // MLamX variant - extract all binders and recurse into body
        lambda_arms.push(quote! {
            #primary_type::#mlam_variant(scope) => {
                // Use unbind to get binders and body with proper types
                let (binders, body) = scope.clone().unbind();
                for binder in &binders {
                    if let Some(name) = &binder.0.pretty_name {
                        if !seen.contains(name) {
                            seen.insert(name.clone());
                            // Infer the binder's type from how it's used in the body
                            let var_type = body.infer_var_type(name)
                                .map(|t| Self::inferred_to_term_type(&t))
                                .unwrap_or_else(|| mettail_runtime::TermType::Base(#domain_lit.to_string()));
                            result.push(mettail_runtime::VarTypeInfo {
                                name: name.clone(),
                                ty: var_type,
                            });
                        }
                    }
                }
                // Recurse into body (body is Box<T>, so deref it)
                Self::collect_all_vars_impl(root_term, body.as_ref(), result, seen);
            }
        });

        // ApplyX variant - only recurse into lam (which has type Proc)
        // The arg has the domain type, not the primary type
        let apply_variant = format_ident!("Apply{}", domain);
        lambda_arms.push(quote! {
            #primary_type::#apply_variant(lam, _arg) => {
                Self::collect_all_vars_impl(root_term, lam.as_ref(), result, seen);
                // Note: _arg is of type #domain, not #primary_type, so we can't recurse on it here
            }
        });

        // MApplyX variant - only recurse into lam
        let mapply_variant = format_ident!("MApply{}", domain);
        lambda_arms.push(quote! {
            #primary_type::#mapply_variant(lam, _args) => {
                Self::collect_all_vars_impl(root_term, lam.as_ref(), result, seen);
                // Note: _args contains #domain values, not #primary_type, so we can't recurse on them here
            }
        });
    }

    // Generate arms for constructor variants from grammar
    let mut constructor_arms: Vec<TokenStream> = Vec::new();

    for rule in &language.terms {
        if rule.category != *primary_type {
            continue;
        }

        let label = &rule.label;

        // Skip if handled above (lambdas, applies)
        let label_str = label.to_string();
        if label_str.starts_with("Lam")
            || label_str.starts_with("MLam")
            || label_str.starts_with("Apply")
            || label_str.starts_with("MApply")
            || label_str.ends_with("Var")
        {
            continue;
        }

        // Use term_context if available for accurate field count
        // Each TermParam becomes one field (abstractions become Scope fields)
        let field_count = if let Some(ctx) = &rule.term_context {
            ctx.len()
        } else {
            // Old syntax - count non-terminals but combine binder+body pairs
            let mut count = 0;
            let mut skip_next = false;
            for item in &rule.items {
                if skip_next {
                    skip_next = false;
                    continue;
                }
                match item {
                    GrammarItem::NonTerminal(_) | GrammarItem::Collection { .. } => count += 1,
                    GrammarItem::Binder { .. } => {
                        // Binder + next NonTerminal = one Scope field
                        count += 1;
                        skip_next = true;
                    },
                    GrammarItem::Terminal(_) => {},
                }
            }
            count
        };

        if field_count == 0 {
            // Unit variant
            constructor_arms.push(quote! {
                #primary_type::#label => {}
            });
        } else {
            // Generate field patterns and recursion
            let field_names: Vec<_> = (0..field_count).map(|i| format_ident!("f{}", i)).collect();

            let field_patterns: Vec<TokenStream> =
                field_names.iter().map(|n| quote! { ref #n }).collect();

            // Generate recursion for each field based on type from term_context
            let mut recurse_calls: Vec<TokenStream> = Vec::new();

            if let Some(ctx) = &rule.term_context {
                for (i, param) in ctx.iter().enumerate() {
                    let field_name = &field_names[i];
                    use crate::ast::grammar::TermParam;
                    use crate::ast::types::TypeExpr;

                    match param {
                        TermParam::Simple { ty, .. } => {
                            // Check if type is primary type or contains it
                            match ty {
                                TypeExpr::Base(ident)
                                    if ident.to_string() == primary_type.to_string() =>
                                {
                                    recurse_calls.push(quote! {
                                        Self::collect_all_vars_impl(root_term, #field_name.as_ref(), result, seen);
                                    });
                                },
                                TypeExpr::Collection { element, .. } => {
                                    if let TypeExpr::Base(ident) = element.as_ref() {
                                        if ident.to_string() == primary_type.to_string() {
                                            recurse_calls.push(quote! {
                                                for (elem, _) in #field_name.iter() {
                                                    Self::collect_all_vars_impl(root_term, elem, result, seen);
                                                }
                                            });
                                        }
                                    }
                                },
                                _ => {},
                            }
                        },
                        TermParam::Abstraction { ty, .. } => {
                            // Scope field with single binder - recurse into body
                            if let TypeExpr::Arrow { codomain, .. } = ty {
                                if let TypeExpr::Base(ident) = codomain.as_ref() {
                                    if ident.to_string() == primary_type.to_string() {
                                        // Also extract binder info from scope
                                        let domain_str = if let TypeExpr::Arrow { domain, .. } = ty
                                        {
                                            if let TypeExpr::Base(d) = domain.as_ref() {
                                                d.to_string()
                                            } else {
                                                "Name".to_string()
                                            }
                                        } else {
                                            "Name".to_string()
                                        };
                                        let domain_lit =
                                            LitStr::new(&domain_str, Span::call_site());

                                        recurse_calls.push(quote! {
                                            // Extract binder from scope using unbind
                                            let (binder, body) = #field_name.clone().unbind();
                                            if let Some(name) = &binder.0.pretty_name {
                                                if !seen.contains(name) {
                                                    seen.insert(name.clone());
                                                    let var_type = body.infer_var_type(name)
                                                        .map(|t| Self::inferred_to_term_type(&t))
                                                        .unwrap_or_else(|| mettail_runtime::TermType::Base(#domain_lit.to_string()));
                                                    result.push(mettail_runtime::VarTypeInfo {
                                                        name: name.clone(),
                                                        ty: var_type,
                                                    });
                                                }
                                            }
                                            Self::collect_all_vars_impl(root_term, body.as_ref(), result, seen);
                                        });
                                    }
                                }
                            }
                        },
                        TermParam::MultiAbstraction { ty, .. } => {
                            // Scope field with multi-binder - recurse into body
                            if let TypeExpr::Arrow { codomain, .. } = ty {
                                if let TypeExpr::Base(ident) = codomain.as_ref() {
                                    if ident.to_string() == primary_type.to_string() {
                                        let domain_str = if let TypeExpr::Arrow { domain, .. } = ty
                                        {
                                            if let TypeExpr::MultiBinder(inner) = domain.as_ref() {
                                                if let TypeExpr::Base(d) = inner.as_ref() {
                                                    d.to_string()
                                                } else {
                                                    "Name".to_string()
                                                }
                                            } else {
                                                "Name".to_string()
                                            }
                                        } else {
                                            "Name".to_string()
                                        };
                                        let domain_lit =
                                            LitStr::new(&domain_str, Span::call_site());

                                        recurse_calls.push(quote! {
                                            // Extract binders from multi-scope using unbind
                                            let (binders, body) = #field_name.clone().unbind();
                                            for binder in &binders {
                                                if let Some(name) = &binder.0.pretty_name {
                                                    if !seen.contains(name) {
                                                        seen.insert(name.clone());
                                                        let var_type = body.infer_var_type(name)
                                                            .map(|t| Self::inferred_to_term_type(&t))
                                                            .unwrap_or_else(|| mettail_runtime::TermType::Base(#domain_lit.to_string()));
                                                        result.push(mettail_runtime::VarTypeInfo {
                                                            name: name.clone(),
                                                            ty: var_type,
                                                        });
                                                    }
                                                }
                                            }
                                            Self::collect_all_vars_impl(root_term, body.as_ref(), result, seen);
                                        });
                                    }
                                }
                            }
                        },
                    }
                }
            } else {
                // Old-style syntax - iterate through items directly
                // For old syntax, fields are paired: Binder + NonTerminal = one Scope field
                let mut field_idx = 0;
                let mut item_idx = 0;
                while item_idx < rule.items.len() {
                    let item = &rule.items[item_idx];
                    match item {
                        GrammarItem::NonTerminal(nt) => {
                            let field_name = &field_names[field_idx];
                            let nt_str = nt.to_string();
                            // Only recurse if it's the primary type
                            if nt_str == primary_type.to_string() {
                                recurse_calls.push(quote! {
                                    Self::collect_all_vars_impl(root_term, #field_name.as_ref(), result, seen);
                                });
                            }
                            field_idx += 1;
                            item_idx += 1;
                        },
                        GrammarItem::Collection { element_type, .. } => {
                            let field_name = &field_names[field_idx];
                            let elem_str = element_type.to_string();
                            if elem_str == primary_type.to_string() {
                                recurse_calls.push(quote! {
                                    for (elem, _) in #field_name.iter() {
                                        Self::collect_all_vars_impl(root_term, elem, result, seen);
                                    }
                                });
                            }
                            field_idx += 1;
                            item_idx += 1;
                        },
                        GrammarItem::Binder { category } => {
                            // Binder + next NonTerminal = one Scope field
                            let field_name = &field_names[field_idx];
                            let domain_lit = LitStr::new(&category.to_string(), category.span());

                            // Skip to the body item
                            item_idx += 1;
                            if item_idx < rule.items.len() {
                                if let GrammarItem::NonTerminal(body_type) = &rule.items[item_idx] {
                                    let body_str = body_type.to_string();
                                    if body_str == primary_type.to_string() {
                                        recurse_calls.push(quote! {
                                            // Extract binder from scope using unbind
                                            let (binder, body) = #field_name.clone().unbind();
                                            if let Some(name) = &binder.0.pretty_name {
                                                if !seen.contains(name) {
                                                    seen.insert(name.clone());
                                                    let var_type = body.infer_var_type(name)
                                                        .map(|t| Self::inferred_to_term_type(&t))
                                                        .unwrap_or_else(|| mettail_runtime::TermType::Base(#domain_lit.to_string()));
                                                    result.push(mettail_runtime::VarTypeInfo {
                                                        name: name.clone(),
                                                        ty: var_type,
                                                    });
                                                }
                                            }
                                            Self::collect_all_vars_impl(root_term, body.as_ref(), result, seen);
                                        });
                                    }
                                }
                            }
                            field_idx += 1;
                            item_idx += 1;
                        },
                        GrammarItem::Terminal(_) => {
                            item_idx += 1;
                        },
                    }
                }
            }

            if recurse_calls.is_empty() {
                constructor_arms.push(quote! {
                    #primary_type::#label(#(#field_patterns),*) => {}
                });
            } else {
                constructor_arms.push(quote! {
                    #primary_type::#label(#(#field_patterns),*) => {
                        #(#recurse_calls)*
                    }
                });
            }
        }
    }

    // Variable handling for free variables (e.g., PVar for Proc, NVar for Name, TVar for Term)
    let var_label = generate_var_label(primary_type);
    let primary_type_lit = LitStr::new(&primary_type.to_string(), primary_type.span());

    quote! {
        #primary_type::#var_label(mettail_runtime::OrdVar(mettail_runtime::Var::Free(fv))) => {
            if let Some(name) = &fv.pretty_name {
                if !seen.contains(name) {
                    seen.insert(name.clone());
                    // Try to infer type from usage in root term
                    let var_type = root_term.infer_var_type(name)
                        .map(|t| Self::inferred_to_term_type(&t))
                        .unwrap_or_else(|| mettail_runtime::TermType::Base(#primary_type_lit.to_string()));
                    result.push(mettail_runtime::VarTypeInfo {
                        name: name.clone(),
                        ty: var_type,
                    });
                }
            }
        }
        #primary_type::#var_label(_) => {}
        #(#lambda_arms)*
        #(#constructor_arms)*
        _ => {}
    }
}

/// Generate the Language struct when the language has multiple types (multi-category parse and run).
fn generate_language_struct_multi(
    name: &syn::Ident,
    _name_str: &str,
    name_lower: &str,
    language: &LanguageDef,
) -> TokenStream {
    let language_name = format_ident!("{}Language", name);
    let term_name = format_ident!("{}Term", name);
    let inner_enum_name = format_ident!("{}TermInner", name);
    let env_name = format_ident!("{}Env", name);
    let parser_mod = format_ident!("{}", name_lower);
    let ascent_source = format_ident!("{}_source", name_lower);

    let custom_relation_extraction = generate_custom_relation_extraction(language);

    // Parse: try category parsers in order. First success wins.
    // When both Int and Float exist, try Float before Int so that "1.0" is parsed as Float
    // (Int parser would see FloatLiteral and fail with UnrecognizedToken).
    let has_int = language.types.iter().any(|t| t.name.to_string() == "Int");
    let has_float = language.types.iter().any(|t| t.name.to_string() == "Float");
    let parse_order: Vec<syn::Ident> = if has_int && has_float {
        let mut order = Vec::new();
        order.push(
            language
                .types
                .iter()
                .find(|t| t.name.to_string() == "Float")
                .unwrap()
                .name
                .clone(),
        );
        order.push(
            language
                .types
                .iter()
                .find(|t| t.name.to_string() == "Int")
                .unwrap()
                .name
                .clone(),
        );
        for t in &language.types {
            let s = t.name.to_string();
            if s != "Int" && s != "Float" {
                order.push(t.name.clone());
            }
        }
        order
    } else {
        language.types.iter().map(|t| t.name.clone()).collect()
    };
    let parse_tries: Vec<TokenStream> = parse_order
        .iter()
        .map(|cat| {
            let parser_name = format_ident!("{}Parser", cat);
            let variant = format_ident!("{}", cat);
            quote! {
                match #parser_mod::#parser_name::new().parse(input) {
                    Ok(t) => return Ok(#term_name(#inner_enum_name::#variant(t))),
                    Err(e) => if first_err.is_none() { first_err = Some(format!("{:?}", e)); },
                }
            }
        })
        .collect();

    let primary_type_for_step = language.types.first().map(|t| &t.name);
    // run_ascent_typed: match on variant, seed the right relation, run, collect from that relation.
    // Term IDs must match the wrapper's term_id() which hashes the inner enum (e.g. CalculatorTermInner::Str(t)),
    // so we hash the enum variant wrapping each term for TermInfo and Rewrite.
    let run_arms: Vec<TokenStream> = language
        .types
        .iter()
        .map(|t| {
            let cat = &t.name;
            let cat_lower = format_ident!("{}", cat.to_string().to_lowercase());
            let rw_rel = format_ident!("rw_{}", cat.to_string().to_lowercase());
            let variant = format_ident!("{}", cat);
            let seed_step_term = primary_type_for_step.map(|pt| {
                if pt == cat {
                    quote! { step_term(initial.clone()); }
                } else {
                    quote! {}
                }
            }).unwrap_or_default();
            quote! {
                #inner_enum_name::#variant(inner) => {
                    use ascent::*;
                    let initial = inner.clone();
                    let prog = ascent_run! {
                        include_source!(#ascent_source);
                        #cat_lower(initial.clone());
                        #seed_step_term
                    };
                    let all_terms: Vec<#cat> = prog.#cat_lower.iter().map(|(p,)| p.clone()).collect();
                    let rewrites: Vec<(#cat, #cat)> = prog.#rw_rel.iter().map(|(from, to)| (from.clone(), to.clone())).collect();
                    let term_infos: Vec<mettail_runtime::TermInfo> = all_terms.iter().map(|t| {
                        let wrapped = #inner_enum_name::#variant(t.clone());
                        let term_id = { use std::collections::hash_map::DefaultHasher; use std::hash::{Hash, Hasher}; let mut hasher = DefaultHasher::new(); wrapped.hash(&mut hasher); hasher.finish() };
                        let has_rewrites = rewrites.iter().any(|(from, _)| from == t);
                        mettail_runtime::TermInfo { term_id, display: format!("{}", t), is_normal_form: !has_rewrites }
                    }).collect();
                    let rewrite_list: Vec<mettail_runtime::Rewrite> = rewrites.iter().map(|(from, to)| {
                        use std::collections::hash_map::DefaultHasher; use std::hash::{Hash, Hasher};
                        let w_from = #inner_enum_name::#variant(from.clone());
                        let w_to = #inner_enum_name::#variant(to.clone());
                        let mut h1 = DefaultHasher::new(); let mut h2 = DefaultHasher::new();
                        w_from.hash(&mut h1); w_to.hash(&mut h2);
                        mettail_runtime::Rewrite { from_id: h1.finish(), to_id: h2.finish(), rule_name: Some("rewrite".to_string()) }
                    }).collect();
                    let mut custom_relations = std::collections::HashMap::new();
                    #custom_relation_extraction
                    mettail_runtime::AscentResults { all_terms: term_infos, rewrites: rewrite_list, equivalences: Vec::new(), custom_relations }
                }
            }
        })
        .collect();

    quote! {
        /// Language implementation struct (multi-category: one parser/relation per type).
        pub struct #language_name;

        impl #language_name {
            /// Parse a term from a string (clears var cache). Tries each category parser in order.
            pub fn parse(input: &str) -> Result<#term_name, std::string::String> {
                mettail_runtime::clear_var_cache();
                Self::parse_preserving_vars(input)
            }

            /// Parse without clearing var cache. Tries each category parser in order.
            /// Reports the first parser's error when all fail (so the message is from the most general parser, e.g. Proc).
            pub fn parse_preserving_vars(input: &str) -> Result<#term_name, std::string::String> {
                let mut first_err = None;
                #(#parse_tries)*
                Err(first_err.unwrap_or_else(|| "Parse error".to_string()))
            }

            /// Run Ascent on a typed term (seeds the relation for the term's category).
            pub fn run_ascent_typed(term: &#term_name) -> mettail_runtime::AscentResults {
                match &term.0 {
                    #(#run_arms),*
                }
            }

            /// Create a new empty environment
            pub fn create_env() -> #env_name {
                #env_name::new()
            }
        }
    }
}

/// Generate the Language trait implementation
fn generate_language_trait_impl(
    name: &syn::Ident,
    primary_type: &syn::Ident,
    name_str: &str,
    _name_lower: &str,
    language: &LanguageDef,
) -> TokenStream {
    let language_name = format_ident!("{}Language", name);
    let term_name = format_ident!("{}Term", name);
    let metadata_name = format_ident!("{}Metadata", name);
    let env_name = format_ident!("{}Env", name);

    // Use a string literal for fn name() to avoid moving String (quote! #name_str can expand to a move)
    let name_lit = LitStr::new(name_str, name.span());

    // All categories for environment field access (include native so e.g. Calculator can list/remove Int bindings)
    let categories: Vec<_> = language.types.iter().map(|t| &t.name).collect();

    // Generate field name for primary type (lowercase)
    let primary_field = format_ident!("{}", primary_type.to_string().to_lowercase());

    // Generate remove_from_env checks for all type fields
    let remove_checks: Vec<TokenStream> = categories
        .iter()
        .map(|cat| {
            let field = format_ident!("{}", cat.to_string().to_lowercase());
            quote! { typed_env.#field.remove(name).is_some() }
        })
        .collect();

    // Generate list_env iterations for all type fields
    let list_iterations: Vec<TokenStream> = categories
        .iter()
        .map(|cat| {
            let field = format_ident!("{}", cat.to_string().to_lowercase());
            quote! {
                for (name, val) in typed_env.#field.iter() {
                    let comment = typed_env.comments.get(name).cloned();
                    result.push((name.clone(), format!("{}", val), comment));
                }
            }
        })
        .collect();

    // try_direct_eval: only for single-type languages whose primary type has native_type
    let primary_lang_type = language.types.first().expect("at least one type");
    let try_direct_eval_method: TokenStream = if let Some(native_ty) =
        &primary_lang_type.native_type
    {
        let literal_label = generate_literal_label(native_ty);
        quote! {
            fn try_direct_eval(&self, term: &dyn mettail_runtime::Term) -> Option<Box<dyn mettail_runtime::Term>> {
                let typed_term = term.as_any().downcast_ref::<#term_name>()?;
                let v = typed_term.0.try_eval()?;
                Some(Box::new(#term_name(#primary_type::#literal_label(v))))
            }
        }
    } else {
        quote! {}
    };

    quote! {
        impl mettail_runtime::Language for #language_name {
            fn name(&self) -> &'static str {
                #name_lit
            }

            fn metadata(&self) -> &'static dyn mettail_runtime::LanguageMetadata {
                &#metadata_name
            }

            fn parse_term(&self, input: &str) -> Result<Box<dyn mettail_runtime::Term>, std::string::String> {
                #language_name::parse(input)
                    .map(|t| Box::new(t) as Box<dyn mettail_runtime::Term>)
            }

            fn parse_term_for_env(&self, input: &str) -> Result<Box<dyn mettail_runtime::Term>, std::string::String> {
                #language_name::parse_preserving_vars(input)
                    .map(|t| Box::new(t) as Box<dyn mettail_runtime::Term>)
            }

            fn run_ascent(&self, term: &dyn mettail_runtime::Term) -> Result<mettail_runtime::AscentResults, std::string::String> {
                let typed_term = term
                    .as_any()
                    .downcast_ref::<#term_name>()
                    .ok_or_else(|| format!("Expected {}", stringify!(#term_name)))?;
                Ok(#language_name::run_ascent_typed(typed_term))
            }

            #try_direct_eval_method

            fn create_env(&self) -> Box<dyn std::any::Any + Send + Sync> {
                Box::new(#language_name::create_env())
            }

            fn add_to_env(&self, env: &mut dyn std::any::Any, name: &str, term: &dyn mettail_runtime::Term) -> Result<(), std::string::String> {
                let typed_env = env
                    .downcast_mut::<#env_name>()
                    .ok_or_else(|| "Invalid environment type".to_string())?;

                let typed_term = term
                    .as_any()
                    .downcast_ref::<#term_name>()
                    .ok_or_else(|| format!("Expected {}", stringify!(#term_name)))?;

                // Add to primary type environment
                typed_env.#primary_field.set(name.to_string(), typed_term.0.clone());
                Ok(())
            }

            fn remove_from_env(&self, env: &mut dyn std::any::Any, name: &str) -> Result<bool, std::string::String> {
                let typed_env = env
                    .downcast_mut::<#env_name>()
                    .ok_or_else(|| "Invalid environment type".to_string())?;

                // Try to remove from all type environments
                let removed = #(#remove_checks)||*;
                Ok(removed)
            }

            fn clear_env(&self, env: &mut dyn std::any::Any) {
                if let Some(typed_env) = env.downcast_mut::<#env_name>() {
                    typed_env.clear();
                }
            }

            fn substitute_env(&self, term: &dyn mettail_runtime::Term, env: &dyn std::any::Any) -> Result<Box<dyn mettail_runtime::Term>, std::string::String> {
                let typed_env = env
                    .downcast_ref::<#env_name>()
                    .ok_or_else(|| "Invalid environment type".to_string())?;

                let typed_term = term
                    .as_any()
                    .downcast_ref::<#term_name>()
                    .ok_or_else(|| format!("Expected {}", stringify!(#term_name)))?;

                let substituted = typed_term.0.substitute_env(typed_env);
                Ok(Box::new(#term_name(substituted)))
            }

            fn substitute_env_preserve_structure(&self, term: &dyn mettail_runtime::Term, env: &dyn std::any::Any) -> Result<Box<dyn mettail_runtime::Term>, std::string::String> {
                let typed_env = env
                    .downcast_ref::<#env_name>()
                    .ok_or_else(|| "Invalid environment type".to_string())?;
                let typed_term = term
                    .as_any()
                    .downcast_ref::<#term_name>()
                    .ok_or_else(|| format!("Expected {}", stringify!(#term_name)))?;
                let substituted = typed_term.0.substitute_env(typed_env);
                Ok(Box::new(#term_name(substituted)))
            }

            fn list_env(&self, env: &dyn std::any::Any) -> Vec<(std::string::String, std::string::String, Option<std::string::String>)> {
                let typed_env = match env.downcast_ref::<#env_name>() {
                    Some(e) => e,
                    None => return Vec::new(),
                };

                let mut result = Vec::new();
                // Iterate in insertion order (IndexMap preserves order)
                #(#list_iterations)*
                result
            }

            fn set_env_comment(&self, env: &mut dyn std::any::Any, name: &str, comment: std::string::String) -> Result<(), std::string::String> {
                let typed_env = env
                    .downcast_mut::<#env_name>()
                    .ok_or_else(|| "Invalid environment type".to_string())?;
                typed_env.set_comment(name, comment);
                Ok(())
            }

            fn is_env_empty(&self, env: &dyn std::any::Any) -> bool {
                env.downcast_ref::<#env_name>()
                    .map(|e| e.is_empty())
                    .unwrap_or(true)
            }

            // === Type Inference Methods ===

            fn infer_term_type(&self, term: &dyn mettail_runtime::Term) -> mettail_runtime::TermType {
                let typed_term = match term.as_any().downcast_ref::<#term_name>() {
                    Some(t) => t,
                    None => return mettail_runtime::TermType::Unknown,
                };
                #language_name::infer_term_type_typed(&typed_term.0)
            }

            fn infer_var_types(&self, term: &dyn mettail_runtime::Term) -> Vec<mettail_runtime::VarTypeInfo> {
                let typed_term = match term.as_any().downcast_ref::<#term_name>() {
                    Some(t) => t,
                    None => return Vec::new(),
                };
                #language_name::infer_var_types_typed(&typed_term.0)
            }

            fn infer_var_type(&self, term: &dyn mettail_runtime::Term, var_name: &str) -> Option<mettail_runtime::TermType> {
                let typed_term = match term.as_any().downcast_ref::<#term_name>() {
                    Some(t) => t,
                    None => return None,
                };
                #language_name::infer_var_type_typed(&typed_term.0, var_name)
            }
        }
    }
}

/// Generate the Language trait implementation when the language has multiple types (enum term).
fn generate_language_trait_impl_multi(
    name: &syn::Ident,
    name_str: &str,
    _name_lower: &str,
    language: &LanguageDef,
) -> TokenStream {
    let language_name = format_ident!("{}Language", name);
    let term_name = format_ident!("{}Term", name);
    let inner_enum_name = format_ident!("{}TermInner", name);
    let metadata_name = format_ident!("{}Metadata", name);
    let env_name = format_ident!("{}Env", name);
    let name_lit = LitStr::new(name_str, name.span());

    let categories: Vec<_> = language.types.iter().map(|t| &t.name).collect();
    let remove_checks: Vec<TokenStream> = categories
        .iter()
        .map(|cat| {
            let field = format_ident!("{}", cat.to_string().to_lowercase());
            quote! { typed_env.#field.remove(name).is_some() }
        })
        .collect();
    let list_iterations: Vec<TokenStream> = categories
        .iter()
        .map(|cat| {
            let field = format_ident!("{}", cat.to_string().to_lowercase());
            quote! {
                for (name, val) in typed_env.#field.iter() {
                    let comment = typed_env.comments.get(name).cloned();
                    result.push((name.clone(), format!("{}", val), comment));
                }
            }
        })
        .collect();

    // Before adding: remove name from all category envs so reassigning replaces (e.g. x = 1 then x = true)
    let remove_before_add: Vec<TokenStream> = categories
        .iter()
        .map(|cat| {
            let field = format_ident!("{}", cat.to_string().to_lowercase());
            quote! { typed_env.#field.remove(name); }
        })
        .collect();

    // add_to_env: match on term.0 and set the right env field
    let add_to_env_arms: Vec<TokenStream> = language
        .types
        .iter()
        .map(|t| {
            let cat = &t.name;
            let field = format_ident!("{}", cat.to_string().to_lowercase());
            let variant = format_ident!("{}", cat);
            quote! { #inner_enum_name::#variant(t) => typed_env.#field.set(name.to_string(), t.clone()) }
        })
        .collect();

    // infer_term_type: match and return Base(category name)
    let infer_term_type_arms: Vec<TokenStream> = language
        .types
        .iter()
        .map(|t| {
            let cat = &t.name;
            let cat_str = cat.to_string();
            let variant = format_ident!("{}", cat);
            let lit = LitStr::new(&cat_str, cat.span());
            quote! { #inner_enum_name::#variant(_) => mettail_runtime::TermType::Base(#lit.to_string()) }
        })
        .collect();

    // try_direct_eval for multi-type: only when at least one type has native_type
    let try_direct_eval_arms: Vec<TokenStream> = language
        .types
        .iter()
        .filter_map(|t| {
            let native_ty = t.native_type.as_ref()?;
            let cat = &t.name;
            let variant = format_ident!("{}", cat);
            let literal_label = generate_literal_label(native_ty);
            Some(quote! {
                #inner_enum_name::#variant(inner) => inner.try_eval().map(|v| #term_name(#inner_enum_name::#variant(#cat::#literal_label(v))))
            })
        })
        .collect();
    let try_direct_eval_method: TokenStream = if try_direct_eval_arms.is_empty() {
        quote! {}
    } else {
        quote! {
            fn try_direct_eval(&self, term: &dyn mettail_runtime::Term) -> Option<Box<dyn mettail_runtime::Term>> {
                let typed_term = term.as_any().downcast_ref::<#term_name>()?;
                let result = match &typed_term.0 {
                    #(#try_direct_eval_arms),*,
                    _ => None,
                }?;
                Some(Box::new(result))
            }
        }
    };

    quote! {
        impl mettail_runtime::Language for #language_name {
            fn name(&self) -> &'static str {
                #name_lit
            }

            fn metadata(&self) -> &'static dyn mettail_runtime::LanguageMetadata {
                &#metadata_name
            }

            fn parse_term(&self, input: &str) -> Result<Box<dyn mettail_runtime::Term>, std::string::String> {
                #language_name::parse(input)
                    .map(|t| Box::new(t) as Box<dyn mettail_runtime::Term>)
            }

            fn parse_term_for_env(&self, input: &str) -> Result<Box<dyn mettail_runtime::Term>, std::string::String> {
                #language_name::parse_preserving_vars(input)
                    .map(|t| Box::new(t) as Box<dyn mettail_runtime::Term>)
            }

            fn run_ascent(&self, term: &dyn mettail_runtime::Term) -> Result<mettail_runtime::AscentResults, std::string::String> {
                let typed_term = term
                    .as_any()
                    .downcast_ref::<#term_name>()
                    .ok_or_else(|| format!("Expected {}", stringify!(#term_name)))?;
                Ok(#language_name::run_ascent_typed(typed_term))
            }

            #try_direct_eval_method

            fn create_env(&self) -> Box<dyn std::any::Any + Send + Sync> {
                Box::new(#language_name::create_env())
            }

            fn add_to_env(&self, env: &mut dyn std::any::Any, name: &str, term: &dyn mettail_runtime::Term) -> Result<(), std::string::String> {
                let typed_env = env
                    .downcast_mut::<#env_name>()
                    .ok_or_else(|| "Invalid environment type".to_string())?;
                let typed_term = term
                    .as_any()
                    .downcast_ref::<#term_name>()
                    .ok_or_else(|| format!("Expected {}", stringify!(#term_name)))?;
                // Remove name from all categories first so reassigning replaces the binding
                #(#remove_before_add)*
                match &typed_term.0 {
                    #(#add_to_env_arms),*
                }
                Ok(())
            }

            fn remove_from_env(&self, env: &mut dyn std::any::Any, name: &str) -> Result<bool, std::string::String> {
                let typed_env = env
                    .downcast_mut::<#env_name>()
                    .ok_or_else(|| "Invalid environment type".to_string())?;
                let removed = #(#remove_checks)||*;
                Ok(removed)
            }

            fn clear_env(&self, env: &mut dyn std::any::Any) {
                if let Some(typed_env) = env.downcast_mut::<#env_name>() {
                    typed_env.clear();
                }
            }

            fn substitute_env(&self, term: &dyn mettail_runtime::Term, env: &dyn std::any::Any) -> Result<Box<dyn mettail_runtime::Term>, std::string::String> {
                let typed_env = env
                    .downcast_ref::<#env_name>()
                    .ok_or_else(|| "Invalid environment type".to_string())?;
                let typed_term = term
                    .as_any()
                    .downcast_ref::<#term_name>()
                    .ok_or_else(|| format!("Expected {}", stringify!(#term_name)))?;
                let substituted = typed_term.0.substitute_env(typed_env);
                Ok(Box::new(#term_name(substituted)))
            }

            fn substitute_env_preserve_structure(&self, term: &dyn mettail_runtime::Term, env: &dyn std::any::Any) -> Result<Box<dyn mettail_runtime::Term>, std::string::String> {
                let typed_env = env
                    .downcast_ref::<#env_name>()
                    .ok_or_else(|| "Invalid environment type".to_string())?;
                let typed_term = term
                    .as_any()
                    .downcast_ref::<#term_name>()
                    .ok_or_else(|| format!("Expected {}", stringify!(#term_name)))?;
                let substituted = typed_term.0.substitute_env(typed_env);
                Ok(Box::new(#term_name(substituted)))
            }

            fn list_env(&self, env: &dyn std::any::Any) -> Vec<(std::string::String, std::string::String, Option<std::string::String>)> {
                let typed_env = match env.downcast_ref::<#env_name>() {
                    Some(e) => e,
                    None => return Vec::new(),
                };
                let mut result = Vec::new();
                #(#list_iterations)*
                result
            }

            fn set_env_comment(&self, env: &mut dyn std::any::Any, name: &str, comment: std::string::String) -> Result<(), std::string::String> {
                let typed_env = env
                    .downcast_mut::<#env_name>()
                    .ok_or_else(|| "Invalid environment type".to_string())?;
                typed_env.set_comment(name, comment);
                Ok(())
            }

            fn is_env_empty(&self, env: &dyn std::any::Any) -> bool {
                env.downcast_ref::<#env_name>()
                    .map(|e| e.is_empty())
                    .unwrap_or(true)
            }

            fn infer_term_type(&self, term: &dyn mettail_runtime::Term) -> mettail_runtime::TermType {
                let typed_term = match term.as_any().downcast_ref::<#term_name>() {
                    Some(t) => t,
                    None => return mettail_runtime::TermType::Unknown,
                };
                match &typed_term.0 {
                    #(#infer_term_type_arms),*
                }
            }

            fn infer_var_types(&self, _term: &dyn mettail_runtime::Term) -> Vec<mettail_runtime::VarTypeInfo> {
                Vec::new()
            }

            fn infer_var_type(&self, _term: &dyn mettail_runtime::Term, _var_name: &str) -> Option<mettail_runtime::TermType> {
                None
            }
        }
    }
}

/// Generate the type inference helper for the primary type
///
/// This handles detecting lambda variants and building the full function type.
/// The domain type is inferred from how the binder is USED in the body,
/// not just from the lambda variant.
fn generate_type_inference_helpers(primary_type: &Ident, language: &LanguageDef) -> TokenStream {
    let primary_type_lit = LitStr::new(&primary_type.to_string(), primary_type.span());

    // Get all categories for lambda variant detection (including native, e.g. Int/Bool/Str)
    let categories: Vec<_> = language.types.iter().map(|t| &t.name).collect();

    // Generate match arms for lambda variants
    let mut lambda_arms: Vec<TokenStream> = Vec::new();

    for domain in &categories {
        let domain_lit = LitStr::new(&domain.to_string(), domain.span());
        let lam_variant = format_ident!("Lam{}", domain);
        let mlam_variant = format_ident!("MLam{}", domain);

        // Single lambda: Lam{Domain}(scope) -> [inferred_domain -> body_type]
        // We infer the domain type from how the binder is USED in the body
        lambda_arms.push(quote! {
            #primary_type::#lam_variant(scope) => {
                // Use unbind to get binder and body with proper types
                let (binder, body) = scope.clone().unbind();
                let body_type = Self::infer_term_type_typed(&body);

                // Get the binder name to infer its type from usage
                let binder_name = binder.0.pretty_name.as_ref();

                // Infer the binder's type from how it's used in the body
                let domain_type = if let Some(name) = binder_name {
                    // Use infer_var_type to get the actual type from usage
                    body.infer_var_type(name)
                        .map(|t| Self::inferred_to_term_type(&t))
                        .unwrap_or_else(|| mettail_runtime::TermType::Base(#domain_lit.to_string()))
                } else {
                    // Fallback to the variant's domain type
                    mettail_runtime::TermType::Base(#domain_lit.to_string())
                };

                mettail_runtime::TermType::Arrow(
                    Box::new(domain_type),
                    Box::new(body_type),
                )
            }
        });

        // Multi lambda: MLam{Domain}(scope) -> [Domain* -> body_type]
        lambda_arms.push(quote! {
            #primary_type::#mlam_variant(scope) => {
                let (_binders, body) = scope.clone().unbind();
                let body_type = Self::infer_term_type_typed(&body);
                mettail_runtime::TermType::MultiArrow(
                    Box::new(mettail_runtime::TermType::Base(#domain_lit.to_string())),
                    Box::new(body_type),
                )
            }
        });
    }

    quote! {
        match term {
            #(#lambda_arms)*
            // Non-lambda terms have the primary type as their type
            _ => mettail_runtime::TermType::Base(#primary_type_lit.to_string()),
        }
    }
}

/// Generate code to extract custom relations from the Ascent program
///
/// For each relation declared in the logic block, generates code like:
/// ```ignore
/// custom_relations.insert("path".to_string(), mettail_runtime::RelationData {
///     param_types: vec!["Proc".to_string(), "Proc".to_string()],
///     tuples: prog.path.iter().map(|(a, b)| vec![format!("{}", a), format!("{}", b)]).collect(),
/// });
/// ```
fn generate_custom_relation_extraction(language: &LanguageDef) -> TokenStream {
    let relations = match &language.logic {
        Some(logic_block) => &logic_block.relations,
        None => return quote! {},
    };

    if relations.is_empty() {
        return quote! {};
    }

    let mut extractions = Vec::new();

    for rel in relations {
        let rel_name = &rel.name;
        let rel_name_str = rel_name.to_string();
        let param_type_strs: Vec<String> = rel.param_types.iter().map(|t| t.to_string()).collect();

        // Generate tuple element names based on arity
        let arity = rel.param_types.len();
        let tuple_vars: Vec<syn::Ident> = (0..arity).map(|i| format_ident!("e{}", i)).collect();

        // Generate format expressions for each element
        let format_exprs: Vec<TokenStream> = tuple_vars
            .iter()
            .map(|v| quote! { format!("{}", #v) })
            .collect();

        // For arity 1, use (e0,) so Rust treats it as a tuple pattern; (e0) would bind the whole &(Proc,).
        let tuple_pattern: TokenStream = if arity == 1 {
            quote! { (#(#tuple_vars),*,) }
        } else {
            quote! { (#(#tuple_vars),*) }
        };

        extractions.push(quote! {
            custom_relations.insert(
                #rel_name_str.to_string(),
                mettail_runtime::RelationData {
                    param_types: vec![#(#param_type_strs.to_string()),*],
                    tuples: prog.#rel_name
                        .iter()
                        .map(|#tuple_pattern| vec![#(#format_exprs),*])
                        .collect(),
                }
            );
        });
    }

    quote! {
        #(#extractions)*
    }
}
