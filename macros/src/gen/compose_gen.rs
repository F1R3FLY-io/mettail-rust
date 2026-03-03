//! Code generation for `compose_languages!`.
//!
//! Given a `ComposeDef`, this module emits:
//!
//! 1. **`{Name}TermInner`** enum -- one variant per sub-language.
//! 2. **`{Name}Term`** wrapper struct implementing `mettail_runtime::Term`.
//! 3. Downcast accessors: `as_{sub}() -> Option<&{Sub}Term>`.
//! 4. **`{Name}Env`** struct with per-sub-language envs.
//! 5. **`{Name}Metadata`** composed metadata aggregating sub-language metadata.
//! 6. **`{Name}Language`** struct implementing `mettail_runtime::Language`.
//!
//! No parser or Ascent program is generated -- every method delegates to the
//! appropriate sub-language.

use crate::ast::compose::ComposeDef;
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use syn::LitStr;

/// Main entry point: generate all composed-language code from a `ComposeDef`.
pub fn generate_composed_language(def: &ComposeDef) -> TokenStream {
    let term_inner = generate_term_inner(def);
    let term_wrapper = generate_term_wrapper(def);
    let env_struct = generate_env_struct(def);
    let metadata = generate_metadata(def);
    let language_struct = generate_language_struct(def);
    let language_trait_impl = generate_language_trait_impl(def);

    quote! {
        #term_inner
        #term_wrapper
        #env_struct
        #metadata
        #language_struct
        #language_trait_impl
    }
}

// =============================================================================
// TermInner enum
// =============================================================================

fn generate_term_inner(def: &ComposeDef) -> TokenStream {
    let inner_name = format_ident!("{}TermInner", def.name);

    let variants: Vec<TokenStream> = def
        .languages
        .iter()
        .map(|lang| {
            let variant = &lang.variant_name;
            let path = &lang.module_path;
            let term_ty = format_ident!("{}Term", variant);
            quote! { #variant(#path::#term_ty) }
        })
        .collect();

    let display_arms: Vec<TokenStream> = def
        .languages
        .iter()
        .map(|lang| {
            let variant = &lang.variant_name;
            quote! { #inner_name::#variant(inner) => write!(f, "{}", inner) }
        })
        .collect();

    let debug_arms: Vec<TokenStream> = def
        .languages
        .iter()
        .map(|lang| {
            let variant = &lang.variant_name;
            quote! { #inner_name::#variant(inner) => write!(f, "{:?}", inner) }
        })
        .collect();

    let eq_arms: Vec<TokenStream> = def
        .languages
        .iter()
        .map(|lang| {
            let variant = &lang.variant_name;
            quote! {
                (#inner_name::#variant(a), #inner_name::#variant(b)) => {
                    mettail_runtime::Term::term_eq(a as &dyn mettail_runtime::Term, b as &dyn mettail_runtime::Term)
                }
            }
        })
        .collect();

    let hash_arms: Vec<TokenStream> = def
        .languages
        .iter()
        .map(|lang| {
            let variant = &lang.variant_name;
            let disc: u8 = def
                .languages
                .iter()
                .position(|l| l.variant_name == lang.variant_name)
                .expect("variant must exist") as u8;
            quote! {
                #inner_name::#variant(inner) => {
                    state.write_u8(#disc);
                    let id = mettail_runtime::Term::term_id(inner as &dyn mettail_runtime::Term);
                    state.write_u64(id);
                }
            }
        })
        .collect();

    quote! {
        /// Inner term enum for composed language -- one variant per sub-language.
        #[derive(Clone)]
        pub enum #inner_name {
            #(#variants),*
        }

        impl std::fmt::Display for #inner_name {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                match self {
                    #(#display_arms),*
                }
            }
        }

        impl std::fmt::Debug for #inner_name {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                match self {
                    #(#debug_arms),*
                }
            }
        }

        impl PartialEq for #inner_name {
            fn eq(&self, other: &Self) -> bool {
                match (self, other) {
                    #(#eq_arms),*,
                    _ => false,
                }
            }
        }

        impl Eq for #inner_name {}

        impl std::hash::Hash for #inner_name {
            fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
                use std::hash::Hasher;
                match self {
                    #(#hash_arms),*
                }
            }
        }
    }
}

// =============================================================================
// Term wrapper
// =============================================================================

fn generate_term_wrapper(def: &ComposeDef) -> TokenStream {
    let term_name = format_ident!("{}Term", def.name);
    let inner_name = format_ident!("{}TermInner", def.name);

    // Downcast accessor methods: as_calculator(), as_rho_calc(), etc.
    let accessors: Vec<TokenStream> = def
        .languages
        .iter()
        .map(|lang| {
            let variant = &lang.variant_name;
            let path = &lang.module_path;
            let sub_term = format_ident!("{}Term", variant);
            let fn_name = format_ident!(
                "as_{}",
                to_snake_case(&variant.to_string())
            );
            quote! {
                /// Downcast to the sub-language term, if this term belongs to that language.
                pub fn #fn_name(&self) -> Option<&#path::#sub_term> {
                    match &self.0 {
                        #inner_name::#variant(inner) => Some(inner),
                        _ => None,
                    }
                }
            }
        })
        .collect();

    quote! {
        /// Wrapper struct implementing `mettail_runtime::Term` for the composed language.
        #[derive(Clone)]
        pub struct #term_name(pub #inner_name);

        impl #term_name {
            #(#accessors)*
        }

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

// =============================================================================
// Env struct
// =============================================================================

fn generate_env_struct(def: &ComposeDef) -> TokenStream {
    let env_name = format_ident!("{}Env", def.name);

    let fields: Vec<TokenStream> = def
        .languages
        .iter()
        .map(|lang| {
            let field = format_ident!("{}", to_snake_case(&lang.variant_name.to_string()));
            quote! {
                pub #field: Box<dyn std::any::Any + Send + Sync>
            }
        })
        .collect();

    let field_inits: Vec<TokenStream> = def
        .languages
        .iter()
        .map(|lang| {
            let field = format_ident!("{}", to_snake_case(&lang.variant_name.to_string()));
            let path = &lang.module_path;
            let lang_struct = format_ident!("{}Language", lang.variant_name);
            quote! {
                #field: <#path::#lang_struct as mettail_runtime::Language>::create_env(&#path::#lang_struct)
            }
        })
        .collect();

    let clear_stmts: Vec<TokenStream> = def
        .languages
        .iter()
        .map(|lang| {
            let field = format_ident!("{}", to_snake_case(&lang.variant_name.to_string()));
            let path = &lang.module_path;
            let lang_struct = format_ident!("{}Language", lang.variant_name);
            quote! {
                <#path::#lang_struct as mettail_runtime::Language>::clear_env(&#path::#lang_struct, self.#field.as_mut());
            }
        })
        .collect();

    let is_empty_checks: Vec<TokenStream> = def
        .languages
        .iter()
        .map(|lang| {
            let field = format_ident!("{}", to_snake_case(&lang.variant_name.to_string()));
            let path = &lang.module_path;
            let lang_struct = format_ident!("{}Language", lang.variant_name);
            quote! {
                <#path::#lang_struct as mettail_runtime::Language>::is_env_empty(&#path::#lang_struct, self.#field.as_ref())
            }
        })
        .collect();

    quote! {
        /// Combined environment holding per-sub-language environments.
        pub struct #env_name {
            #(#fields),*
        }

        impl #env_name {
            /// Create a new combined environment with fresh sub-environments.
            pub fn new() -> Self {
                Self {
                    #(#field_inits),*
                }
            }

            /// Clear all sub-environments.
            pub fn clear(&mut self) {
                #(#clear_stmts)*
            }

            /// Check if all sub-environments are empty.
            pub fn is_empty(&self) -> bool {
                #(#is_empty_checks)&&*
            }
        }

        impl Default for #env_name {
            fn default() -> Self {
                Self::new()
            }
        }
    }
}

// =============================================================================
// Metadata
// =============================================================================

fn generate_metadata(def: &ComposeDef) -> TokenStream {
    let metadata_name = format_ident!("{}Metadata", def.name);
    let name_str = def.name.to_string();
    let name_lit = LitStr::new(&name_str, def.name.span());

    // Collect static metadata from each sub-language at init time via lazy_static / OnceLock.
    // Since LanguageMetadata methods return &'static slices, we aggregate them into
    // owned Vecs and leak them to obtain 'static references. This happens exactly once.
    let type_chains: Vec<TokenStream> = def
        .languages
        .iter()
        .map(|lang| {
            let path = &lang.module_path;
            let meta_name = format_ident!("{}Metadata", lang.variant_name);
            quote! {
                all_types.extend_from_slice(
                    mettail_runtime::LanguageMetadata::types(&#path::#meta_name)
                );
            }
        })
        .collect();

    let term_chains: Vec<TokenStream> = def
        .languages
        .iter()
        .map(|lang| {
            let path = &lang.module_path;
            let meta_name = format_ident!("{}Metadata", lang.variant_name);
            quote! {
                all_terms.extend_from_slice(
                    mettail_runtime::LanguageMetadata::terms(&#path::#meta_name)
                );
            }
        })
        .collect();

    let eq_chains: Vec<TokenStream> = def
        .languages
        .iter()
        .map(|lang| {
            let path = &lang.module_path;
            let meta_name = format_ident!("{}Metadata", lang.variant_name);
            quote! {
                all_eqs.extend_from_slice(
                    mettail_runtime::LanguageMetadata::equations(&#path::#meta_name)
                );
            }
        })
        .collect();

    let rw_chains: Vec<TokenStream> = def
        .languages
        .iter()
        .map(|lang| {
            let path = &lang.module_path;
            let meta_name = format_ident!("{}Metadata", lang.variant_name);
            quote! {
                all_rws.extend_from_slice(
                    mettail_runtime::LanguageMetadata::rewrites(&#path::#meta_name)
                );
            }
        })
        .collect();

    let rel_chains: Vec<TokenStream> = def
        .languages
        .iter()
        .map(|lang| {
            let path = &lang.module_path;
            let meta_name = format_ident!("{}Metadata", lang.variant_name);
            quote! {
                all_rels.extend_from_slice(
                    mettail_runtime::LanguageMetadata::logic_relations(&#path::#meta_name)
                );
            }
        })
        .collect();

    let rule_chains: Vec<TokenStream> = def
        .languages
        .iter()
        .map(|lang| {
            let path = &lang.module_path;
            let meta_name = format_ident!("{}Metadata", lang.variant_name);
            quote! {
                all_rules.extend_from_slice(
                    mettail_runtime::LanguageMetadata::logic_rules(&#path::#meta_name)
                );
            }
        })
        .collect();

    quote! {
        /// Aggregated metadata for the composed language.
        ///
        /// Lazily collects metadata from all sub-languages into leaked `&'static` slices
        /// on first access.
        pub struct #metadata_name;

        impl #metadata_name {
            fn aggregated() -> &'static AggregatedMetadata {
                use std::sync::OnceLock;
                static INSTANCE: OnceLock<AggregatedMetadata> = OnceLock::new();
                INSTANCE.get_or_init(|| {
                    let mut all_types = Vec::new();
                    #(#type_chains)*

                    let mut all_terms = Vec::new();
                    #(#term_chains)*

                    let mut all_eqs = Vec::new();
                    #(#eq_chains)*

                    let mut all_rws = Vec::new();
                    #(#rw_chains)*

                    let mut all_rels = Vec::new();
                    #(#rel_chains)*

                    let mut all_rules = Vec::new();
                    #(#rule_chains)*

                    AggregatedMetadata {
                        types: all_types.leak(),
                        terms: all_terms.leak(),
                        equations: all_eqs.leak(),
                        rewrites: all_rws.leak(),
                        logic_relations: all_rels.leak(),
                        logic_rules: all_rules.leak(),
                    }
                })
            }
        }

        struct AggregatedMetadata {
            types: &'static [mettail_runtime::TypeDef],
            terms: &'static [mettail_runtime::TermDef],
            equations: &'static [mettail_runtime::EquationDef],
            rewrites: &'static [mettail_runtime::RewriteDef],
            logic_relations: &'static [mettail_runtime::LogicRelationDef],
            logic_rules: &'static [mettail_runtime::LogicRuleDef],
        }

        // SAFETY: All inner slices are 'static and the sub-metadata types are Send+Sync.
        unsafe impl Send for AggregatedMetadata {}
        unsafe impl Sync for AggregatedMetadata {}

        impl mettail_runtime::LanguageMetadata for #metadata_name {
            fn name(&self) -> &'static str { #name_lit }

            fn types(&self) -> &'static [mettail_runtime::TypeDef] {
                Self::aggregated().types
            }

            fn terms(&self) -> &'static [mettail_runtime::TermDef] {
                Self::aggregated().terms
            }

            fn equations(&self) -> &'static [mettail_runtime::EquationDef] {
                Self::aggregated().equations
            }

            fn rewrites(&self) -> &'static [mettail_runtime::RewriteDef] {
                Self::aggregated().rewrites
            }

            fn logic_relations(&self) -> &'static [mettail_runtime::LogicRelationDef] {
                Self::aggregated().logic_relations
            }

            fn logic_rules(&self) -> &'static [mettail_runtime::LogicRuleDef] {
                Self::aggregated().logic_rules
            }
        }
    }
}

// =============================================================================
// Language struct
// =============================================================================

fn generate_language_struct(def: &ComposeDef) -> TokenStream {
    let lang_name = format_ident!("{}Language", def.name);

    quote! {
        /// Composed language struct implementing `mettail_runtime::Language`.
        ///
        /// All methods delegate to the constituent sub-languages. Parsing tries each
        /// sub-language in declaration order and returns the first success.
        pub struct #lang_name;
    }
}

// =============================================================================
// Language trait impl
// =============================================================================

fn generate_language_trait_impl(def: &ComposeDef) -> TokenStream {
    let lang_name = format_ident!("{}Language", def.name);
    let term_name = format_ident!("{}Term", def.name);
    let inner_name = format_ident!("{}TermInner", def.name);
    let env_name = format_ident!("{}Env", def.name);
    let metadata_name = format_ident!("{}Metadata", def.name);
    let name_str = def.name.to_string();
    let name_lit = LitStr::new(&name_str, def.name.span());

    // ── parse_term: try each sub-language in order ──
    let parse_attempts: Vec<TokenStream> = def
        .languages
        .iter()
        .map(|lang| {
            let variant = &lang.variant_name;
            let path = &lang.module_path;
            let sub_lang = format_ident!("{}Language", variant);
            let sub_term = format_ident!("{}Term", variant);
            quote! {
                match <#path::#sub_lang as mettail_runtime::Language>::parse_term(&#path::#sub_lang, input) {
                    Ok(boxed_term) => {
                        let sub_term = boxed_term
                            .as_any()
                            .downcast_ref::<#path::#sub_term>()
                            .expect("sub-language returned unexpected Term type")
                            .clone();
                        return Ok(Box::new(#term_name(#inner_name::#variant(sub_term)))
                            as Box<dyn mettail_runtime::Term>);
                    }
                    Err(e) => errors.push(e),
                }
            }
        })
        .collect();

    // ── parse_term_for_env: same but with parse_term_for_env ──
    let parse_for_env_attempts: Vec<TokenStream> = def
        .languages
        .iter()
        .map(|lang| {
            let variant = &lang.variant_name;
            let path = &lang.module_path;
            let sub_lang = format_ident!("{}Language", variant);
            let sub_term = format_ident!("{}Term", variant);
            quote! {
                match <#path::#sub_lang as mettail_runtime::Language>::parse_term_for_env(&#path::#sub_lang, input) {
                    Ok(boxed_term) => {
                        let sub_term = boxed_term
                            .as_any()
                            .downcast_ref::<#path::#sub_term>()
                            .expect("sub-language returned unexpected Term type")
                            .clone();
                        return Ok(Box::new(#term_name(#inner_name::#variant(sub_term)))
                            as Box<dyn mettail_runtime::Term>);
                    }
                    Err(e) => errors.push(e),
                }
            }
        })
        .collect();

    // ── run_ascent: match on variant, delegate ──
    let ascent_arms: Vec<TokenStream> = def
        .languages
        .iter()
        .map(|lang| {
            let variant = &lang.variant_name;
            let path = &lang.module_path;
            let sub_lang = format_ident!("{}Language", variant);
            quote! {
                #inner_name::#variant(inner) => {
                    <#path::#sub_lang as mettail_runtime::Language>::run_ascent(
                        &#path::#sub_lang,
                        inner as &dyn mettail_runtime::Term,
                    )
                }
            }
        })
        .collect();

    // ── try_direct_eval: match on variant, delegate ──
    let eval_arms: Vec<TokenStream> = def
        .languages
        .iter()
        .map(|lang| {
            let variant = &lang.variant_name;
            let path = &lang.module_path;
            let sub_lang = format_ident!("{}Language", variant);
            let sub_term = format_ident!("{}Term", variant);
            quote! {
                #inner_name::#variant(inner) => {
                    let result = <#path::#sub_lang as mettail_runtime::Language>::try_direct_eval(
                        &#path::#sub_lang,
                        inner as &dyn mettail_runtime::Term,
                    )?;
                    let sub = result
                        .as_any()
                        .downcast_ref::<#path::#sub_term>()
                        .expect("sub-language returned unexpected Term type")
                        .clone();
                    Some(Box::new(#term_name(#inner_name::#variant(sub)))
                        as Box<dyn mettail_runtime::Term>)
                }
            }
        })
        .collect();

    // ── normalize_term: match on variant, delegate ──
    let normalize_arms: Vec<TokenStream> = def
        .languages
        .iter()
        .map(|lang| {
            let variant = &lang.variant_name;
            let path = &lang.module_path;
            let sub_lang = format_ident!("{}Language", variant);
            let sub_term = format_ident!("{}Term", variant);
            quote! {
                #inner_name::#variant(inner) => {
                    let result = <#path::#sub_lang as mettail_runtime::Language>::normalize_term(
                        &#path::#sub_lang,
                        inner as &dyn mettail_runtime::Term,
                    );
                    let sub = result
                        .as_any()
                        .downcast_ref::<#path::#sub_term>()
                        .expect("sub-language returned unexpected Term type")
                        .clone();
                    Box::new(#term_name(#inner_name::#variant(sub)))
                }
            }
        })
        .collect();

    // ── add_to_env: match on variant, delegate to correct sub-env ──
    let add_env_arms: Vec<TokenStream> = def
        .languages
        .iter()
        .map(|lang| {
            let variant = &lang.variant_name;
            let path = &lang.module_path;
            let sub_lang = format_ident!("{}Language", variant);
            let field = format_ident!("{}", to_snake_case(&variant.to_string()));
            quote! {
                #inner_name::#variant(inner) => {
                    <#path::#sub_lang as mettail_runtime::Language>::add_to_env(
                        &#path::#sub_lang,
                        typed_env.#field.as_mut(),
                        name,
                        inner as &dyn mettail_runtime::Term,
                    )
                }
            }
        })
        .collect();

    // ── remove_from_env: try each sub-env ──
    let remove_stmts: Vec<TokenStream> = def
        .languages
        .iter()
        .map(|lang| {
            let variant = &lang.variant_name;
            let path = &lang.module_path;
            let sub_lang = format_ident!("{}Language", variant);
            let field = format_ident!("{}", to_snake_case(&variant.to_string()));
            quote! {
                match <#path::#sub_lang as mettail_runtime::Language>::remove_from_env(
                    &#path::#sub_lang,
                    typed_env.#field.as_mut(),
                    name,
                ) {
                    Ok(true) => removed = true,
                    _ => {}
                }
            }
        })
        .collect();

    // ── clear_env: clear all sub-envs ──
    let clear_stmts: Vec<TokenStream> = def
        .languages
        .iter()
        .map(|lang| {
            let variant = &lang.variant_name;
            let path = &lang.module_path;
            let sub_lang = format_ident!("{}Language", variant);
            let field = format_ident!("{}", to_snake_case(&variant.to_string()));
            quote! {
                <#path::#sub_lang as mettail_runtime::Language>::clear_env(
                    &#path::#sub_lang,
                    typed_env.#field.as_mut(),
                );
            }
        })
        .collect();

    // ── substitute_env: match on variant, delegate ──
    let subst_arms: Vec<TokenStream> = def
        .languages
        .iter()
        .map(|lang| {
            let variant = &lang.variant_name;
            let path = &lang.module_path;
            let sub_lang = format_ident!("{}Language", variant);
            let sub_term = format_ident!("{}Term", variant);
            let field = format_ident!("{}", to_snake_case(&variant.to_string()));
            quote! {
                #inner_name::#variant(inner) => {
                    let result = <#path::#sub_lang as mettail_runtime::Language>::substitute_env(
                        &#path::#sub_lang,
                        inner as &dyn mettail_runtime::Term,
                        typed_env.#field.as_ref(),
                    )?;
                    let sub = result
                        .as_any()
                        .downcast_ref::<#path::#sub_term>()
                        .expect("sub-language returned unexpected Term type")
                        .clone();
                    Ok(Box::new(#term_name(#inner_name::#variant(sub)))
                        as Box<dyn mettail_runtime::Term>)
                }
            }
        })
        .collect();

    // ── substitute_env_preserve_structure: match on variant, delegate ──
    let subst_preserve_arms: Vec<TokenStream> = def
        .languages
        .iter()
        .map(|lang| {
            let variant = &lang.variant_name;
            let path = &lang.module_path;
            let sub_lang = format_ident!("{}Language", variant);
            let sub_term = format_ident!("{}Term", variant);
            let field = format_ident!("{}", to_snake_case(&variant.to_string()));
            quote! {
                #inner_name::#variant(inner) => {
                    let result = <#path::#sub_lang as mettail_runtime::Language>::substitute_env_preserve_structure(
                        &#path::#sub_lang,
                        inner as &dyn mettail_runtime::Term,
                        typed_env.#field.as_ref(),
                    )?;
                    let sub = result
                        .as_any()
                        .downcast_ref::<#path::#sub_term>()
                        .expect("sub-language returned unexpected Term type")
                        .clone();
                    Ok(Box::new(#term_name(#inner_name::#variant(sub)))
                        as Box<dyn mettail_runtime::Term>)
                }
            }
        })
        .collect();

    // ── list_env: aggregate from all sub-envs ──
    let list_stmts: Vec<TokenStream> = def
        .languages
        .iter()
        .map(|lang| {
            let variant = &lang.variant_name;
            let path = &lang.module_path;
            let sub_lang = format_ident!("{}Language", variant);
            let field = format_ident!("{}", to_snake_case(&variant.to_string()));
            quote! {
                result.extend(
                    <#path::#sub_lang as mettail_runtime::Language>::list_env(
                        &#path::#sub_lang,
                        typed_env.#field.as_ref(),
                    )
                );
            }
        })
        .collect();

    // ── set_env_comment: try each sub-env until one succeeds ──
    let comment_stmts: Vec<TokenStream> = def
        .languages
        .iter()
        .map(|lang| {
            let variant = &lang.variant_name;
            let path = &lang.module_path;
            let sub_lang = format_ident!("{}Language", variant);
            let field = format_ident!("{}", to_snake_case(&variant.to_string()));
            quote! {
                if <#path::#sub_lang as mettail_runtime::Language>::set_env_comment(
                    &#path::#sub_lang,
                    typed_env.#field.as_mut(),
                    name,
                    comment.clone(),
                ).is_ok() {
                    return Ok(());
                }
            }
        })
        .collect();

    // ── is_env_empty: all must be empty ──
    let empty_checks: Vec<TokenStream> = def
        .languages
        .iter()
        .map(|lang| {
            let variant = &lang.variant_name;
            let path = &lang.module_path;
            let sub_lang = format_ident!("{}Language", variant);
            let field = format_ident!("{}", to_snake_case(&variant.to_string()));
            quote! {
                <#path::#sub_lang as mettail_runtime::Language>::is_env_empty(
                    &#path::#sub_lang,
                    typed_env.#field.as_ref(),
                )
            }
        })
        .collect();

    // ── infer_term_type: match on variant, delegate ──
    let infer_type_arms: Vec<TokenStream> = def
        .languages
        .iter()
        .map(|lang| {
            let variant = &lang.variant_name;
            let path = &lang.module_path;
            let sub_lang = format_ident!("{}Language", variant);
            quote! {
                #inner_name::#variant(inner) => {
                    <#path::#sub_lang as mettail_runtime::Language>::infer_term_type(
                        &#path::#sub_lang,
                        inner as &dyn mettail_runtime::Term,
                    )
                }
            }
        })
        .collect();

    // ── infer_var_types: match on variant, delegate ──
    let infer_var_types_arms: Vec<TokenStream> = def
        .languages
        .iter()
        .map(|lang| {
            let variant = &lang.variant_name;
            let path = &lang.module_path;
            let sub_lang = format_ident!("{}Language", variant);
            quote! {
                #inner_name::#variant(inner) => {
                    <#path::#sub_lang as mettail_runtime::Language>::infer_var_types(
                        &#path::#sub_lang,
                        inner as &dyn mettail_runtime::Term,
                    )
                }
            }
        })
        .collect();

    // ── infer_var_type: match on variant, delegate ──
    let infer_var_type_arms: Vec<TokenStream> = def
        .languages
        .iter()
        .map(|lang| {
            let variant = &lang.variant_name;
            let path = &lang.module_path;
            let sub_lang = format_ident!("{}Language", variant);
            quote! {
                #inner_name::#variant(inner) => {
                    <#path::#sub_lang as mettail_runtime::Language>::infer_var_type(
                        &#path::#sub_lang,
                        inner as &dyn mettail_runtime::Term,
                        var_name,
                    )
                }
            }
        })
        .collect();

    quote! {
        impl mettail_runtime::Language for #lang_name {
            fn name(&self) -> &'static str {
                #name_lit
            }

            fn metadata(&self) -> &'static dyn mettail_runtime::LanguageMetadata {
                &#metadata_name
            }

            fn parse_term(&self, input: &str) -> Result<Box<dyn mettail_runtime::Term>, std::string::String> {
                let mut errors = Vec::new();
                #(#parse_attempts)*
                // All sub-languages failed: aggregate error messages
                Err(format!(
                    "No sub-language could parse the input. Errors:\n{}",
                    errors.iter()
                        .enumerate()
                        .map(|(i, e)| format!("  [{}] {}", i + 1, e))
                        .collect::<Vec<_>>()
                        .join("\n")
                ))
            }

            fn parse_term_for_env(&self, input: &str) -> Result<Box<dyn mettail_runtime::Term>, std::string::String> {
                let mut errors = Vec::new();
                #(#parse_for_env_attempts)*
                Err(format!(
                    "No sub-language could parse the input. Errors:\n{}",
                    errors.iter()
                        .enumerate()
                        .map(|(i, e)| format!("  [{}] {}", i + 1, e))
                        .collect::<Vec<_>>()
                        .join("\n")
                ))
            }

            fn run_ascent(&self, term: &dyn mettail_runtime::Term) -> Result<mettail_runtime::AscentResults, std::string::String> {
                let typed_term = term
                    .as_any()
                    .downcast_ref::<#term_name>()
                    .ok_or_else(|| format!("Expected {}", stringify!(#term_name)))?;
                match &typed_term.0 {
                    #(#ascent_arms),*
                }
            }

            fn try_direct_eval(&self, term: &dyn mettail_runtime::Term) -> Option<Box<dyn mettail_runtime::Term>> {
                let typed_term = term.as_any().downcast_ref::<#term_name>()?;
                match &typed_term.0 {
                    #(#eval_arms),*
                }
            }

            fn normalize_term(&self, term: &dyn mettail_runtime::Term) -> Box<dyn mettail_runtime::Term> {
                if let Some(typed_term) = term.as_any().downcast_ref::<#term_name>() {
                    match &typed_term.0 {
                        #(#normalize_arms),*
                    }
                } else {
                    term.clone_box()
                }
            }

            fn format_term(&self, term: &dyn mettail_runtime::Term) -> std::string::String {
                format!("{}", term)
            }

            fn create_env(&self) -> Box<dyn std::any::Any + Send + Sync> {
                Box::new(#env_name::new())
            }

            fn add_to_env(&self, env: &mut dyn std::any::Any, name: &str, term: &dyn mettail_runtime::Term) -> Result<(), std::string::String> {
                let typed_env = env
                    .downcast_mut::<#env_name>()
                    .ok_or_else(|| "Invalid environment type".to_string())?;
                let typed_term = term
                    .as_any()
                    .downcast_ref::<#term_name>()
                    .ok_or_else(|| format!("Expected {}", stringify!(#term_name)))?;
                match &typed_term.0 {
                    #(#add_env_arms),*
                }
            }

            fn remove_from_env(&self, env: &mut dyn std::any::Any, name: &str) -> Result<bool, std::string::String> {
                let typed_env = env
                    .downcast_mut::<#env_name>()
                    .ok_or_else(|| "Invalid environment type".to_string())?;
                let mut removed = false;
                #(#remove_stmts)*
                Ok(removed)
            }

            fn clear_env(&self, env: &mut dyn std::any::Any) {
                if let Some(typed_env) = env.downcast_mut::<#env_name>() {
                    #(#clear_stmts)*
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
                match &typed_term.0 {
                    #(#subst_arms),*
                }
            }

            fn substitute_env_preserve_structure(&self, term: &dyn mettail_runtime::Term, env: &dyn std::any::Any) -> Result<Box<dyn mettail_runtime::Term>, std::string::String> {
                let typed_env = env
                    .downcast_ref::<#env_name>()
                    .ok_or_else(|| "Invalid environment type".to_string())?;
                let typed_term = term
                    .as_any()
                    .downcast_ref::<#term_name>()
                    .ok_or_else(|| format!("Expected {}", stringify!(#term_name)))?;
                match &typed_term.0 {
                    #(#subst_preserve_arms),*
                }
            }

            fn list_env(&self, env: &dyn std::any::Any) -> Vec<(std::string::String, std::string::String, Option<std::string::String>)> {
                let typed_env = match env.downcast_ref::<#env_name>() {
                    Some(e) => e,
                    None => return Vec::new(),
                };
                let mut result = Vec::new();
                #(#list_stmts)*
                result
            }

            fn set_env_comment(&self, env: &mut dyn std::any::Any, name: &str, comment: std::string::String) -> Result<(), std::string::String> {
                let typed_env = env
                    .downcast_mut::<#env_name>()
                    .ok_or_else(|| "Invalid environment type".to_string())?;
                #(#comment_stmts)*
                Err(format!("Binding '{}' not found in any sub-language environment", name))
            }

            fn is_env_empty(&self, env: &dyn std::any::Any) -> bool {
                match env.downcast_ref::<#env_name>() {
                    Some(typed_env) => #(#empty_checks)&&*,
                    None => true,
                }
            }

            fn infer_term_type(&self, term: &dyn mettail_runtime::Term) -> mettail_runtime::TermType {
                let typed_term = match term.as_any().downcast_ref::<#term_name>() {
                    Some(t) => t,
                    None => return mettail_runtime::TermType::Unknown,
                };
                match &typed_term.0 {
                    #(#infer_type_arms),*
                }
            }

            fn infer_var_types(&self, term: &dyn mettail_runtime::Term) -> Vec<mettail_runtime::VarTypeInfo> {
                let typed_term = match term.as_any().downcast_ref::<#term_name>() {
                    Some(t) => t,
                    None => return Vec::new(),
                };
                match &typed_term.0 {
                    #(#infer_var_types_arms),*
                }
            }

            fn infer_var_type(&self, term: &dyn mettail_runtime::Term, var_name: &str) -> Option<mettail_runtime::TermType> {
                let typed_term = term.as_any().downcast_ref::<#term_name>()?;
                match &typed_term.0 {
                    #(#infer_var_type_arms),*
                }
            }
        }
    }
}

// =============================================================================
// Helpers
// =============================================================================

/// Convert a PascalCase identifier to snake_case.
///
/// Examples:
/// - `Calculator` -> `calculator`
/// - `RhoCalc` -> `rho_calc`
/// - `MyLanguage` -> `my_language`
fn to_snake_case(s: &str) -> String {
    let mut result = String::with_capacity(s.len() + 4);
    for (i, ch) in s.chars().enumerate() {
        if ch.is_uppercase() {
            if i > 0 {
                result.push('_');
            }
            result.push(ch.to_lowercase().next().expect("char must have lowercase"));
        } else {
            result.push(ch);
        }
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_to_snake_case() {
        assert_eq!(to_snake_case("Calculator"), "calculator");
        assert_eq!(to_snake_case("RhoCalc"), "rho_calc");
        assert_eq!(to_snake_case("MyLanguage"), "my_language");
        assert_eq!(to_snake_case("A"), "a");
        assert_eq!(to_snake_case("ABC"), "a_b_c");
    }
}
