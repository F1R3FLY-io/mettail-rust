//! Substitution generation for MeTTaIL terms
//!
//! Generates capture-avoiding substitution methods for each exported category.
//!
//! ## Generated Methods
//!
//! For each category `Cat` with types `{Cat, Other, ...}`:
//! - `substitute(var, replacement) -> Self` - single variable substitution
//! - `subst(vars, repls) -> Self` - multi-variable simultaneous substitution
//! - `subst_other(vars, repls) -> Self` - cross-category substitution
//!
//! ## Design
//!
//! Substitution is generated based on the AST structure (variants), not grammar rules.
//! Each variant type has a uniform substitution pattern:
//! - Var: check if matches, return replacement or self
//! - Literal/Nullary: return self (no variables)
//! - Regular: recurse into fields
//! - Collection: map substitution over elements
//! - Binder: filter shadowed vars, recurse into body
//! - MultiBinder: filter all shadowed vars, recurse

#![allow(clippy::cmp_owned)]

use crate::ast::grammar::{GrammarItem, GrammarRule, TermParam};
use crate::ast::language::LanguageDef;
use crate::ast::types::{CollectionType, TypeExpr};
use crate::gen::native::{has_native_type, native_type_to_string};
use crate::gen::{generate_literal_label, generate_var_label, is_integer_rule, is_var_rule};
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use syn::Ident;

// =============================================================================
// Variant Kind - Unified representation of AST variants
// =============================================================================

/// Represents a variant of an AST enum for substitution purposes.
/// Abstracts over both old (BNFC) and new (judgement) syntax.
#[derive(Debug, Clone)]
enum VariantKind {
    /// Variable variant: PVar(OrdVar)
    Var { label: Ident },

    /// Literal variant: NumLit(i32)
    Literal { label: Ident },

    /// Nullary constructor: PZero
    Nullary { label: Ident },

    /// Regular constructor with fields: Add(Box<Int>, Box<Int>)
    Regular { label: Ident, fields: Vec<FieldInfo> },

    /// Collection constructor: PPar(HashBag<Proc>)
    Collection {
        label: Ident,
        element_cat: Ident,
        coll_type: CollectionType,
    },

    /// Single binder: PInput(Box<Name>, Scope<Binder<String>, Box<Proc>>)
    Binder {
        label: Ident,
        pre_scope_fields: Vec<FieldInfo>,
        binder_cat: Ident,
        body_cat: Ident,
    },

    /// Multi-binder: PInputs(Vec<Name>, Scope<Vec<Binder<String>>, Box<Proc>>)
    MultiBinder {
        label: Ident,
        pre_scope_fields: Vec<FieldInfo>,
        binder_cat: Ident,
        body_cat: Ident,
    },
}

/// Information about a field in a constructor
#[derive(Debug, Clone)]
struct FieldInfo {
    /// The category of this field (e.g., Proc, Name)
    category: Ident,
    /// Whether this is a collection field
    is_collection: bool,
    /// Collection type if is_collection is true
    coll_type: Option<CollectionType>,
}

// =============================================================================
// Main Entry Point
// =============================================================================

/// Generate substitution methods for all exported categories
pub fn generate_substitution(language: &LanguageDef) -> TokenStream {
    let impls: Vec<TokenStream> = language
        .types
        .iter()
        .map(|lang_type| generate_category_substitution(&lang_type.name, language))
        .collect();

    quote! {
        #(#impls)*
    }
}

/// Generate `substitute_env` methods for all exported categories
///
/// For each category, generates a method that substitutes all environment
/// variables by NAME (not by FreeVar identity). This is different from the
/// capture-avoiding `subst` which compares FreeVar IDs.
pub fn generate_env_substitution(language: &LanguageDef) -> TokenStream {
    let language_name = &language.name;
    let env_name = format_ident!("{}Env", language_name);

    // Generate for all categories (native-type categories still have Var and need substitute_env)
    let categories: Vec<_> = language.types.iter().collect();

    if categories.is_empty() {
        return quote! {};
    }

    let impls: Vec<TokenStream> = categories.iter().map(|export| {
        let cat_name = &export.name;

        // Collect all category fields for cross-category substitution
        let all_subst_calls: Vec<TokenStream> = categories.iter().map(|cat| {
            let field = format_ident!("{}", cat.name.to_string().to_lowercase());
            let method = format_ident!("subst_by_name_{}", cat.name.to_string().to_lowercase());
            quote! {
                result = result.#method(&env.#field.0);
            }
        }).collect();

        // Generate subst_by_name methods for each replacement category
        let subst_by_name_methods: Vec<TokenStream> = categories.iter().map(|repl_cat| {
            let repl_cat_name = &repl_cat.name;
            let method_name = format_ident!("subst_by_name_{}", repl_cat_name.to_string().to_lowercase());

            // Get the variants for this category
            let variants = collect_category_variants(cat_name, language);

            // Generate match arms for each variant
            let match_arms: Vec<TokenStream> = variants.iter().map(|variant| {
                generate_subst_by_name_arm(cat_name, variant, repl_cat_name)
            }).collect();

            quote! {
                /// Substitute variables by name from a map (preserves insertion order)
                fn #method_name(&self, env_map: &indexmap::IndexMap<String, #repl_cat_name>) -> Self {
                    if env_map.is_empty() { return self.clone(); }
                    match self {
                        #(#match_arms),*
                    }
                }
            }
        }).collect();

        quote! {
            impl #cat_name {
                /// Substitute all environment variables in this term by name
                ///
                /// Replaces all free variables whose names match keys in the environment
                /// with their corresponding values. Uses name-based matching (not FreeVar identity).
                /// Iterates until fixed point (no more substitutions possible).
                /// Finally normalizes FreeVar IDs and flattens any nested collections.
                pub fn substitute_env(&self, env: &#env_name) -> Self {
                    let mut result = self.clone();
                    // Iterate until fixed point - keep substituting until no changes
                    // Use Display format for comparison (more stable than Debug for HashBag)
                    // Limit iterations to prevent infinite loops
                    for _ in 0..100 {
                        let prev_str = format!("{}", result);
                        #(#all_subst_calls)*
                        // Check if we've reached fixed point (no more changes)
                        if format!("{}", result) == prev_str {
                            break;
                        }
                    }
                    // Unify FreeVar IDs by name using VAR_CACHE
                    // This ensures all variables with the same pretty_name have the same ID
                    let result = result.unify_freevars();
                    // Normalize to flatten any nested collections (e.g., PPar inside PPar)
                    result.normalize()
                }

                #(#subst_by_name_methods)*

                /// Unify FreeVar IDs by pretty_name using the global VAR_CACHE.
                /// This ensures all variables with the same name have the same FreeVar ID,
                /// which is necessary for Ascent equality checks to work correctly
                /// when terms come from different parsing contexts (e.g., environment vs user input).
                pub fn unify_freevars(&self) -> Self {
                    self.unify_freevars_impl()
                }
            }
        }
    }).collect();

    // Generate unify_freevars_impl methods for each category
    let unify_impls: Vec<TokenStream> = categories
        .iter()
        .map(|export| {
            let cat_name = &export.name;
            let variants = collect_category_variants(cat_name, language);
            let match_arms: Vec<TokenStream> = variants
                .iter()
                .map(|variant| generate_unify_freevars_arm(cat_name, variant, language))
                .collect();

            quote! {
                impl #cat_name {
                    fn unify_freevars_impl(&self) -> Self {
                        match self {
                            #(#match_arms),*
                        }
                    }
                }
            }
        })
        .collect();

    quote! {
        #(#impls)*
        #(#unify_impls)*
    }
}

/// Generate a match arm for unify_freevars
fn generate_unify_freevars_arm(
    category: &Ident,
    variant: &VariantKind,
    language: &LanguageDef,
) -> TokenStream {
    match variant {
        VariantKind::Var { label } => {
            // For Var variants, look up and replace with canonical FreeVar from VAR_CACHE
            quote! {
                #category::#label(mettail_runtime::OrdVar(mettail_runtime::Var::Free(v))) => {
                    // Get or insert canonical FreeVar for this name
                    let canonical = mettail_runtime::get_or_insert_var(v);
                    #category::#label(mettail_runtime::OrdVar(mettail_runtime::Var::Free(canonical)))
                },
                #category::#label(bound) => #category::#label(bound.clone())
            }
        },

        VariantKind::Literal { label } => {
            // String is not Copy; use clone() for str/String to avoid E0507
            let literal_arm = language
                .types
                .iter()
                .find(|t| &t.name == category)
                .and_then(|t| t.native_type.as_ref())
                .map(|ty| {
                    let type_str = native_type_to_string(ty);
                    if type_str == "str" || type_str == "String" {
                        quote! { #category::#label(v) => #category::#label(v.clone()) }
                    } else {
                        quote! { #category::#label(v) => #category::#label(*v) }
                    }
                })
                .unwrap_or_else(|| quote! { #category::#label(v) => #category::#label(*v) });
            literal_arm
        },

        VariantKind::Nullary { label } => {
            quote! { #category::#label => #category::#label }
        },

        VariantKind::Regular { label, fields } => {
            let field_names: Vec<Ident> =
                (0..fields.len()).map(|i| format_ident!("f{}", i)).collect();
            let field_unifies: Vec<TokenStream> = fields
                .iter()
                .zip(field_names.iter())
                .map(|(field, name)| {
                    if field.is_collection {
                        match field.coll_type.as_ref().unwrap_or(&CollectionType::HashBag) {
                            CollectionType::HashBag => {
                                quote! {
                                    {
                                        let mut bag = mettail_runtime::HashBag::new();
                                        for (elem, count) in #name.iter() {
                                            let u = elem.unify_freevars_impl();
                                            for _ in 0..count { bag.insert(u.clone()); }
                                        }
                                        bag
                                    }
                                }
                            },
                            CollectionType::HashSet => {
                                quote! { #name.iter().map(|e| e.unify_freevars_impl()).collect() }
                            },
                            CollectionType::Vec => {
                                quote! { #name.iter().map(|e| e.unify_freevars_impl()).collect() }
                            },
                        }
                    } else {
                        quote! { Box::new((**#name).unify_freevars_impl()) }
                    }
                })
                .collect();

            quote! {
                #category::#label(#(#field_names),*) => {
                    #category::#label(#(#field_unifies),*)
                }
            }
        },

        VariantKind::Collection { label, coll_type, .. } => match coll_type {
            CollectionType::HashBag => {
                quote! {
                    #category::#label(bag) => {
                        let mut new_bag = mettail_runtime::HashBag::new();
                        for (elem, count) in bag.iter() {
                            let u = elem.unify_freevars_impl();
                            for _ in 0..count { new_bag.insert(u.clone()); }
                        }
                        #category::#label(new_bag)
                    }
                }
            },
            CollectionType::HashSet => {
                quote! {
                    #category::#label(elems) => {
                        #category::#label(elems.iter().map(|e| e.unify_freevars_impl()).collect())
                    }
                }
            },
            CollectionType::Vec => {
                quote! {
                    #category::#label(elems) => {
                        #category::#label(elems.iter().map(|e| e.unify_freevars_impl()).collect())
                    }
                }
            },
        },

        VariantKind::Binder { label, pre_scope_fields, .. } => {
            let field_names: Vec<Ident> = (0..pre_scope_fields.len())
                .map(|i| format_ident!("f{}", i))
                .collect();

            let field_unifies: Vec<TokenStream> = pre_scope_fields
                .iter()
                .zip(field_names.iter())
                .map(|(field, name)| {
                    if field.is_collection {
                        quote! { #name.iter().map(|e| e.unify_freevars_impl()).collect::<Vec<_>>() }
                    } else {
                        quote! { Box::new((**#name).unify_freevars_impl()) }
                    }
                })
                .collect();

            let pattern = if field_names.is_empty() {
                quote! { #category::#label(scope) }
            } else {
                quote! { #category::#label(#(#field_names,)* scope) }
            };

            let reconstruction = if field_names.is_empty() {
                quote! { #category::#label(new_scope) }
            } else {
                quote! { #category::#label(#(#field_unifies,)* new_scope) }
            };

            quote! {
                #pattern => {
                    let binder = &scope.inner().unsafe_pattern;
                    let body = &scope.inner().unsafe_body;
                    let new_body = (**body).unify_freevars_impl();
                    let new_scope = mettail_runtime::Scope::new(binder.clone(), Box::new(new_body));
                    #reconstruction
                }
            }
        },

        VariantKind::MultiBinder { label, pre_scope_fields, .. } => {
            let field_names: Vec<Ident> = (0..pre_scope_fields.len())
                .map(|i| format_ident!("f{}", i))
                .collect();

            let field_unifies: Vec<TokenStream> = pre_scope_fields
                .iter()
                .zip(field_names.iter())
                .map(|(field, name)| {
                    if field.is_collection {
                        quote! { #name.iter().map(|e| e.unify_freevars_impl()).collect::<Vec<_>>() }
                    } else {
                        quote! { Box::new((**#name).unify_freevars_impl()) }
                    }
                })
                .collect();

            let pattern = if field_names.is_empty() {
                quote! { #category::#label(scope) }
            } else {
                quote! { #category::#label(#(#field_names,)* scope) }
            };

            let reconstruction = if field_names.is_empty() {
                quote! { #category::#label(new_scope) }
            } else {
                quote! { #category::#label(#(#field_unifies,)* new_scope) }
            };

            quote! {
                #pattern => {
                    let binders = &scope.inner().unsafe_pattern;
                    let body = &scope.inner().unsafe_body;
                    let new_body = (**body).unify_freevars_impl();
                    let new_scope = mettail_runtime::Scope::new(binders.clone(), Box::new(new_body));
                    #reconstruction
                }
            }
        },
    }
}

/// Generate a match arm for name-based substitution
fn generate_subst_by_name_arm(
    category: &Ident,
    variant: &VariantKind,
    repl_cat: &Ident,
) -> TokenStream {
    match variant {
        VariantKind::Var { label } => {
            let same_category = category == repl_cat;

            if same_category {
                // Same category - can substitute by name
                quote! {
                    #category::#label(mettail_runtime::OrdVar(mettail_runtime::Var::Free(v))) => {
                        if let Some(name) = &v.pretty_name {
                            if let Some(replacement) = env_map.get(name) {
                                return replacement.clone();
                            }
                        }
                        self.clone()
                    },
                    #category::#label(_) => self.clone()
                }
            } else {
                // Different category - can't substitute
                quote! { #category::#label(_) => self.clone() }
            }
        },

        VariantKind::Literal { label } => {
            quote! { #category::#label(_) => self.clone() }
        },

        VariantKind::Nullary { label } => {
            quote! { #category::#label => self.clone() }
        },

        VariantKind::Regular { label, fields } => {
            let field_names: Vec<Ident> =
                (0..fields.len()).map(|i| format_ident!("f{}", i)).collect();

            let field_substs: Vec<TokenStream> = fields
                .iter()
                .zip(field_names.iter())
                .map(|(field, name)| {
                    let method =
                        format_ident!("subst_by_name_{}", repl_cat.to_string().to_lowercase());
                    if field.is_collection {
                        match field.coll_type.as_ref().unwrap_or(&CollectionType::HashBag) {
                            CollectionType::HashBag => {
                                quote! {
                                    {
                                        let mut bag = mettail_runtime::HashBag::new();
                                        for (elem, count) in #name.iter() {
                                            let s = elem.#method(env_map);
                                            for _ in 0..count { bag.insert(s.clone()); }
                                        }
                                        bag
                                    }
                                }
                            },
                            CollectionType::HashSet => {
                                quote! { #name.iter().map(|elem| elem.#method(env_map)).collect() }
                            },
                            CollectionType::Vec => {
                                quote! { #name.iter().map(|elem| elem.#method(env_map)).collect() }
                            },
                        }
                    } else {
                        // Regular boxed field - recurse (same pattern as generate_regular_subst_arm)
                        quote! { Box::new((**#name).#method(env_map)) }
                    }
                })
                .collect();

            quote! {
                #category::#label(#(#field_names),*) => {
                    #category::#label(#(#field_substs),*)
                }
            }
        },

        VariantKind::Collection { label, coll_type, .. } => {
            let method = format_ident!("subst_by_name_{}", repl_cat.to_string().to_lowercase());

            match coll_type {
                CollectionType::HashBag => {
                    quote! {
                        #category::#label(bag) => {
                            let mut new_bag = mettail_runtime::HashBag::new();
                            for (elem, count) in bag.iter() {
                                let s = elem.#method(env_map);
                                for _ in 0..count { new_bag.insert(s.clone()); }
                            }
                            #category::#label(new_bag)
                        }
                    }
                },
                CollectionType::HashSet => {
                    quote! {
                        #category::#label(elems) => {
                            #category::#label(elems.iter().map(|e| e.#method(env_map)).collect())
                        }
                    }
                },
                CollectionType::Vec => {
                    quote! {
                        #category::#label(elems) => {
                            #category::#label(elems.iter().map(|e| e.#method(env_map)).collect())
                        }
                    }
                },
            }
        },

        VariantKind::Binder { label, pre_scope_fields, binder_cat, .. } => {
            let body_method =
                format_ident!("subst_by_name_{}", repl_cat.to_string().to_lowercase());
            let should_filter = binder_cat == repl_cat;

            let field_names: Vec<Ident> = (0..pre_scope_fields.len())
                .map(|i| format_ident!("f{}", i))
                .collect();

            let field_substs: Vec<TokenStream> = pre_scope_fields
                .iter()
                .zip(field_names.iter())
                .map(|(field, name)| {
                    let method = format_ident!("subst_by_name_{}", repl_cat.to_string().to_lowercase());
                    if field.is_collection {
                        quote! { #name.iter().map(|elem| elem.#method(env_map)).collect::<Vec<_>>() }
                    } else {
                        // Boxed field
                        quote! { Box::new((**#name).#method(env_map)) }
                    }
                })
                .collect();

            let pattern = if field_names.is_empty() {
                quote! { #category::#label(scope) }
            } else {
                quote! { #category::#label(#(#field_names,)* scope) }
            };

            let reconstruction = if field_names.is_empty() {
                quote! { #category::#label(new_scope) }
            } else {
                quote! { #category::#label(#(#field_substs,)* new_scope) }
            };

            if should_filter {
                // Need to filter out bound variable from env_map
                quote! {
                    #pattern => {
                        let binder = &scope.inner().unsafe_pattern;
                        let body = &scope.inner().unsafe_body;

                        let filtered_env: indexmap::IndexMap<String, #repl_cat> =
                            if let Some(name) = &binder.0.pretty_name {
                                env_map.iter()
                                    .filter(|(k, _)| *k != name)
                                    .map(|(k, v)| (k.clone(), v.clone()))
                                    .collect()
                            } else {
                                env_map.clone()
                            };

                        if filtered_env.is_empty() {
                            self.clone()
                        } else {
                            let new_body = (**body).#body_method(&filtered_env);
                            let new_scope = mettail_runtime::Scope::new(binder.clone(), Box::new(new_body));
                            #reconstruction
                        }
                    }
                }
            } else {
                // No filtering needed - different category binder
                quote! {
                    #pattern => {
                        let binder = &scope.inner().unsafe_pattern;
                        let body = &scope.inner().unsafe_body;
                        let new_body = (**body).#body_method(env_map);
                        let new_scope = mettail_runtime::Scope::new(binder.clone(), Box::new(new_body));
                        #reconstruction
                    }
                }
            }
        },

        VariantKind::MultiBinder { label, pre_scope_fields, binder_cat, .. } => {
            let body_method =
                format_ident!("subst_by_name_{}", repl_cat.to_string().to_lowercase());
            let should_filter = binder_cat == repl_cat;

            let field_names: Vec<Ident> = (0..pre_scope_fields.len())
                .map(|i| format_ident!("f{}", i))
                .collect();

            let field_substs: Vec<TokenStream> = pre_scope_fields
                .iter()
                .zip(field_names.iter())
                .map(|(field, name)| {
                    let method = format_ident!("subst_by_name_{}", repl_cat.to_string().to_lowercase());
                    if field.is_collection {
                        quote! { #name.iter().map(|elem| elem.#method(env_map)).collect::<Vec<_>>() }
                    } else {
                        // Boxed field
                        quote! { Box::new((**#name).#method(env_map)) }
                    }
                })
                .collect();

            let pattern = if field_names.is_empty() {
                quote! { #category::#label(scope) }
            } else {
                quote! { #category::#label(#(#field_names,)* scope) }
            };

            let reconstruction = if field_names.is_empty() {
                quote! { #category::#label(new_scope) }
            } else {
                quote! { #category::#label(#(#field_substs,)* new_scope) }
            };

            if should_filter {
                // Filter out all bound variable names from env_map
                quote! {
                    #pattern => {
                        let binders = &scope.inner().unsafe_pattern;
                        let body = &scope.inner().unsafe_body;

                        let bound_names: std::collections::HashSet<String> = binders.iter()
                            .filter_map(|b| b.0.pretty_name.clone())
                            .collect();
                        let filtered_env: indexmap::IndexMap<String, #repl_cat> = env_map.iter()
                            .filter(|(k, _)| !bound_names.contains(*k))
                            .map(|(k, v)| (k.clone(), v.clone()))
                            .collect();

                        if filtered_env.is_empty() {
                            self.clone()
                        } else {
                            let new_body = (**body).#body_method(&filtered_env);
                            let new_scope = mettail_runtime::Scope::new(binders.clone(), Box::new(new_body));
                            #reconstruction
                        }
                    }
                }
            } else {
                // No filtering needed - different category binder
                quote! {
                    #pattern => {
                        let binders = &scope.inner().unsafe_pattern;
                        let body = &scope.inner().unsafe_body;
                        let new_body = (**body).#body_method(env_map);
                        let new_scope = mettail_runtime::Scope::new(binders.clone(), Box::new(new_body));
                        #reconstruction
                    }
                }
            }
        },
    }
}

/// Generate substitution impl for a single category
fn generate_category_substitution(category: &Ident, language: &LanguageDef) -> TokenStream {
    // Skip native types - they don't have variables
    if has_native_type(category, language).is_some() {
        return quote! {
            impl #category {
                // Native types don't support substitution - they're values, not variables
            }
        };
    }

    // Collect all variants for this category
    let variants = collect_category_variants(category, language);

    // Generate the substitution implementation
    generate_subst_impl(category, &variants, language)
}

// =============================================================================
// Variant Collection
// =============================================================================

/// Collect all variants for a category from grammar rules and auto-generated variants
fn collect_category_variants(category: &Ident, language: &LanguageDef) -> Vec<VariantKind> {
    let mut variants = Vec::new();

    // From grammar rules
    for rule in language.terms.iter().filter(|r| r.category == *category) {
        variants.push(rule_to_variant_kind(rule, language));
    }

    // Auto-generated Var variant (if no explicit Var rule)
    let has_var = variants
        .iter()
        .any(|v| matches!(v, VariantKind::Var { .. }));
    if !has_var {
        variants.push(VariantKind::Var { label: generate_var_label(category) });
    }

    // Auto-generated Literal variant (for native types)
    if let Some(lang_type) = language.get_type(category) {
        if let Some(native_type) = &lang_type.native_type {
            let has_lit = variants
                .iter()
                .any(|v| matches!(v, VariantKind::Literal { .. }));
            if !has_lit {
                variants.push(VariantKind::Literal {
                    label: generate_literal_label(native_type),
                });
            }
        }
    }

    // Auto-generated lambda/Apply variants only for non-native categories
    // (native-only categories like Int don't have Lam/Apply variants in their enum)
    let category_is_native = language
        .get_type(category)
        .and_then(|t| t.native_type.as_ref())
        .is_some();
    if category_is_native {
        return variants;
    }

    // Lambda variants for every non-native domain category
    for domain_lang_type in &language.types {
        // Skip native types (can't use as lambda binder)
        if domain_lang_type.native_type.is_some() {
            continue;
        }

        let domain_name = &domain_lang_type.name;

        // Single-binder lambda: Lam{Domain}
        let lam_label =
            syn::Ident::new(&format!("Lam{}", domain_name), proc_macro2::Span::call_site());
        variants.push(VariantKind::Binder {
            label: lam_label,
            pre_scope_fields: vec![], // No pre-scope fields
            binder_cat: domain_name.clone(),
            body_cat: category.clone(),
        });

        // Multi-binder lambda: MLam{Domain}
        let mlam_label =
            syn::Ident::new(&format!("MLam{}", domain_name), proc_macro2::Span::call_site());
        variants.push(VariantKind::MultiBinder {
            label: mlam_label,
            pre_scope_fields: vec![], // No pre-scope fields
            binder_cat: domain_name.clone(),
            body_cat: category.clone(),
        });

        // Application variant: Apply{Domain}
        let apply_label =
            syn::Ident::new(&format!("Apply{}", domain_name), proc_macro2::Span::call_site());
        variants.push(VariantKind::Regular {
            label: apply_label,
            fields: vec![
                FieldInfo {
                    category: category.clone(),
                    is_collection: false,
                    coll_type: None,
                },
                FieldInfo {
                    category: domain_name.clone(),
                    is_collection: false,
                    coll_type: None,
                },
            ],
        });

        // Multi-application variant: MApply{Domain}
        let mapply_label =
            syn::Ident::new(&format!("MApply{}", domain_name), proc_macro2::Span::call_site());
        variants.push(VariantKind::Regular {
            label: mapply_label,
            fields: vec![
                FieldInfo {
                    category: category.clone(),
                    is_collection: false,
                    coll_type: None,
                },
                FieldInfo {
                    category: domain_name.clone(),
                    is_collection: true,
                    coll_type: Some(CollectionType::Vec),
                },
            ],
        });
    }

    variants
}

/// Convert a grammar rule to a VariantKind
fn rule_to_variant_kind(rule: &GrammarRule, _language: &LanguageDef) -> VariantKind {
    let label = rule.label.clone();

    // Check for Var rule first
    if is_var_rule(rule) {
        return VariantKind::Var { label };
    }

    // Check for Integer/Literal rule
    if is_integer_rule(rule) {
        return VariantKind::Literal { label };
    }

    // Use term_context if available (new syntax)
    if let Some(ctx) = &rule.term_context {
        return variant_kind_from_term_context(&label, ctx);
    }

    // Fall back to old syntax (items + bindings)
    variant_kind_from_items(&label, &rule.items, &rule.bindings)
}

/// Create VariantKind from new-style term_context
fn variant_kind_from_term_context(label: &Ident, ctx: &[TermParam]) -> VariantKind {
    // Check for multi-abstraction
    let multi_abs = ctx.iter().find_map(|p| {
        if let TermParam::MultiAbstraction { ty, .. } = p {
            Some(ty)
        } else {
            None
        }
    });

    if let Some(TypeExpr::Arrow { domain, codomain }) = multi_abs {
        // Multi-binder constructor
        let binder_cat = extract_multi_binder_category(domain);
        let body_cat = extract_base_category(codomain);

        // Collect pre-scope fields (Simple params that are collections)
        let pre_scope_fields: Vec<FieldInfo> = ctx
            .iter()
            .filter_map(|p| {
                if let TermParam::Simple { ty, .. } = p {
                    Some(field_info_from_type_expr(ty))
                } else {
                    None
                }
            })
            .collect();

        return VariantKind::MultiBinder {
            label: label.clone(),
            pre_scope_fields,
            binder_cat,
            body_cat,
        };
    }

    // Check for single abstraction
    let single_abs = ctx.iter().find_map(|p| {
        if let TermParam::Abstraction { ty, .. } = p {
            Some(ty)
        } else {
            None
        }
    });

    if let Some(TypeExpr::Arrow { domain, codomain }) = single_abs {
        // Single binder constructor
        let binder_cat = extract_base_category(domain);
        let body_cat = extract_base_category(codomain);

        // Collect pre-scope fields
        let pre_scope_fields: Vec<FieldInfo> = ctx
            .iter()
            .filter_map(|p| {
                if let TermParam::Simple { ty, .. } = p {
                    Some(field_info_from_type_expr(ty))
                } else {
                    None
                }
            })
            .collect();

        return VariantKind::Binder {
            label: label.clone(),
            pre_scope_fields,
            binder_cat,
            body_cat,
        };
    }

    // Regular constructor - collect all simple params as fields
    let fields: Vec<FieldInfo> = ctx
        .iter()
        .filter_map(|p| {
            if let TermParam::Simple { ty, .. } = p {
                Some(field_info_from_type_expr(ty))
            } else {
                None
            }
        })
        .collect();

    // Check if it's a single collection field
    if fields.len() == 1 && fields[0].is_collection {
        return VariantKind::Collection {
            label: label.clone(),
            element_cat: fields[0].category.clone(),
            coll_type: fields[0]
                .coll_type
                .clone()
                .unwrap_or(CollectionType::HashBag),
        };
    }

    if fields.is_empty() {
        VariantKind::Nullary { label: label.clone() }
    } else {
        VariantKind::Regular { label: label.clone(), fields }
    }
}

/// Create VariantKind from old-style items + bindings
fn variant_kind_from_items(
    label: &Ident,
    items: &[GrammarItem],
    bindings: &[(usize, Vec<usize>)],
) -> VariantKind {
    // Check for collection-only constructor
    let collections: Vec<_> = items
        .iter()
        .filter_map(|item| {
            if let GrammarItem::Collection { element_type, coll_type, .. } = item {
                Some((element_type.clone(), coll_type.clone()))
            } else {
                None
            }
        })
        .collect();

    if collections.len() == 1
        && items
            .iter()
            .filter(|i| !matches!(i, GrammarItem::Terminal(_)))
            .count()
            == 1
    {
        let (element_cat, coll_type) = collections[0].clone();
        return VariantKind::Collection {
            label: label.clone(),
            element_cat,
            coll_type,
        };
    }

    // Check for binder
    if !bindings.is_empty() {
        let (binder_idx, body_indices) = &bindings[0];
        let body_idx = body_indices[0];

        // Get binder category
        let binder_cat = match &items[*binder_idx] {
            GrammarItem::Binder { category } => category.clone(),
            _ => panic!("Binding index doesn't point to a Binder"),
        };

        // Get body category
        let body_cat = match &items[body_idx] {
            GrammarItem::NonTerminal(cat) => cat.clone(),
            _ => panic!("Body index doesn't point to a NonTerminal"),
        };

        // Collect pre-scope fields (fields before the binder)
        let pre_scope_fields: Vec<FieldInfo> = items
            .iter()
            .take(*binder_idx)
            .filter_map(|item| match item {
                GrammarItem::NonTerminal(cat) if cat.to_string() != "Var" => Some(FieldInfo {
                    category: cat.clone(),
                    is_collection: false,
                    coll_type: None,
                }),
                GrammarItem::Collection { element_type, coll_type, .. } => Some(FieldInfo {
                    category: element_type.clone(),
                    is_collection: true,
                    coll_type: Some(coll_type.clone()),
                }),
                _ => None,
            })
            .collect();

        return VariantKind::Binder {
            label: label.clone(),
            pre_scope_fields,
            binder_cat,
            body_cat,
        };
    }

    // Regular constructor - collect fields
    let fields: Vec<FieldInfo> = items
        .iter()
        .filter_map(|item| match item {
            GrammarItem::NonTerminal(cat) if cat.to_string() != "Var" => Some(FieldInfo {
                category: cat.clone(),
                is_collection: false,
                coll_type: None,
            }),
            GrammarItem::Collection { element_type, coll_type, .. } => Some(FieldInfo {
                category: element_type.clone(),
                is_collection: true,
                coll_type: Some(coll_type.clone()),
            }),
            _ => None,
        })
        .collect();

    if fields.is_empty() {
        VariantKind::Nullary { label: label.clone() }
    } else {
        VariantKind::Regular { label: label.clone(), fields }
    }
}

// =============================================================================
// Helper Functions for Type Extraction
// =============================================================================

/// Extract the base category from a TypeExpr
fn extract_base_category(ty: &TypeExpr) -> Ident {
    match ty {
        TypeExpr::Base(ident) => ident.clone(),
        TypeExpr::Collection { element, .. } => extract_base_category(element),
        TypeExpr::Arrow { codomain, .. } => extract_base_category(codomain),
        TypeExpr::MultiBinder(inner) => extract_base_category(inner),
    }
}

/// Extract the binder category from a MultiBinder type (Name* -> ...)
fn extract_multi_binder_category(ty: &TypeExpr) -> Ident {
    match ty {
        TypeExpr::MultiBinder(inner) => extract_base_category(inner),
        _ => extract_base_category(ty),
    }
}

/// Create FieldInfo from a TypeExpr
fn field_info_from_type_expr(ty: &TypeExpr) -> FieldInfo {
    match ty {
        TypeExpr::Base(ident) => FieldInfo {
            category: ident.clone(),
            is_collection: false,
            coll_type: None,
        },
        TypeExpr::Collection { coll_type, element } => FieldInfo {
            category: extract_base_category(element),
            is_collection: true,
            coll_type: Some(coll_type.clone()),
        },
        _ => FieldInfo {
            category: format_ident!("Unknown"),
            is_collection: false,
            coll_type: None,
        },
    }
}

// =============================================================================
// Substitution Implementation Generation
// =============================================================================

/// Generate the full substitution impl block for a category
fn generate_subst_impl(
    category: &Ident,
    variants: &[VariantKind],
    language: &LanguageDef,
) -> TokenStream {
    let category_str = category.to_string();

    // Generate match arms for the main subst method (same-category)
    let match_arms: Vec<TokenStream> = variants
        .iter()
        .map(|v| generate_subst_arm(category, v, category))
        .collect();

    // Generate cross-category methods
    let cross_methods: Vec<TokenStream> = language
        .types
        .iter()
        .filter(|t| t.name != *category)
        .filter(|t| t.native_type.is_none()) // Skip native types
        .map(|t| {
            let repl_cat = &t.name;
            let repl_cat_lower = repl_cat.to_string().to_lowercase();
            let method_name = format_ident!("subst_{}", repl_cat_lower);
            // Backward compatibility aliases
            let substitute_alias = format_ident!("substitute_{}", repl_cat_lower);
            let multi_substitute_alias = format_ident!("multi_substitute_{}", repl_cat_lower);

            let cross_arms: Vec<TokenStream> = variants
                .iter()
                .map(|v| generate_subst_arm(category, v, repl_cat))
                .collect();

            quote! {
                /// Cross-category substitution: substitute #repl_cat values for #repl_cat variables
                pub fn #method_name(
                    &self,
                    vars: &[&mettail_runtime::FreeVar<String>],
                    repls: &[#repl_cat],
                ) -> Self {
                    if vars.is_empty() { return self.clone(); }
                    debug_assert_eq!(vars.len(), repls.len());
                    match self {
                        #(#cross_arms),*
                    }
                }

                /// Single-variable cross-category substitution (backward compatibility)
                #[inline]
                pub fn #substitute_alias(
                    &self,
                    var: &mettail_runtime::FreeVar<String>,
                    replacement: &#repl_cat,
                ) -> Self {
                    self.#method_name(&[var], &[replacement.clone()])
                }

                /// Multi-variable cross-category substitution (backward compatibility alias)
                #[inline]
                pub fn #multi_substitute_alias(
                    &self,
                    vars: &[&mettail_runtime::FreeVar<String>],
                    repls: &[#repl_cat],
                ) -> Self {
                    self.#method_name(vars, repls)
                }
            }
        })
        .collect();

    // Self-alias for uniform cross-category calls
    let self_alias = format_ident!("subst_{}", category_str.to_lowercase());
    let substitute_self_alias = format_ident!("substitute_{}", category_str.to_lowercase());
    let multi_substitute_self_alias =
        format_ident!("multi_substitute_{}", category_str.to_lowercase());

    quote! {
        impl #category {
            /// Single-variable substitution (same category)
            pub fn substitute(
                &self,
                var: &mettail_runtime::FreeVar<String>,
                replacement: &Self,
            ) -> Self {
                self.subst(&[var], &[replacement.clone()])
            }

            /// Multi-variable simultaneous substitution (capture-avoiding)
            pub fn subst(
                &self,
                vars: &[&mettail_runtime::FreeVar<String>],
                repls: &[Self],
            ) -> Self {
                if vars.is_empty() { return self.clone(); }
                debug_assert_eq!(vars.len(), repls.len());
                match self {
                    #(#match_arms),*
                }
            }

            /// Backward compatibility alias for multi_substitute
            #[inline]
            pub fn multi_substitute(
                &self,
                vars: &[&mettail_runtime::FreeVar<String>],
                repls: &[Self],
            ) -> Self {
                self.subst(vars, repls)
            }

            /// Alias for uniform cross-category calls
            #[inline]
            pub fn #self_alias(
                &self,
                vars: &[&mettail_runtime::FreeVar<String>],
                repls: &[Self],
            ) -> Self {
                self.subst(vars, repls)
            }

            /// Single-variable substitution alias (substitute_<category>)
            #[inline]
            pub fn #substitute_self_alias(
                &self,
                var: &mettail_runtime::FreeVar<String>,
                replacement: &Self,
            ) -> Self {
                self.substitute(var, replacement)
            }

            /// Backward compatibility alias for multi_substitute_<category>
            #[inline]
            pub fn #multi_substitute_self_alias(
                &self,
                vars: &[&mettail_runtime::FreeVar<String>],
                repls: &[Self],
            ) -> Self {
                self.subst(vars, repls)
            }

            #(#cross_methods)*
        }
    }
}

// =============================================================================
// Per-Variant Match Arm Generation
// =============================================================================

/// Generate a match arm for a specific variant
fn generate_subst_arm(category: &Ident, variant: &VariantKind, repl_cat: &Ident) -> TokenStream {
    match variant {
        VariantKind::Var { label } => generate_var_subst_arm(category, label, repl_cat),

        VariantKind::Literal { label } => {
            quote! { #category::#label(_) => self.clone() }
        },

        VariantKind::Nullary { label } => {
            quote! { #category::#label => self.clone() }
        },

        VariantKind::Regular { label, fields } => {
            generate_regular_subst_arm(category, label, fields, repl_cat)
        },

        VariantKind::Collection { label, element_cat, coll_type } => {
            generate_collection_subst_arm(category, label, element_cat, coll_type, repl_cat)
        },

        VariantKind::Binder {
            label,
            pre_scope_fields,
            binder_cat,
            body_cat,
        } => generate_binder_subst_arm(
            category,
            label,
            pre_scope_fields,
            binder_cat,
            body_cat,
            repl_cat,
        ),

        VariantKind::MultiBinder {
            label,
            pre_scope_fields,
            binder_cat,
            body_cat,
        } => generate_multi_binder_subst_arm(
            category,
            label,
            pre_scope_fields,
            binder_cat,
            body_cat,
            repl_cat,
        ),
    }
}

/// Generate match arm for Var variant
fn generate_var_subst_arm(category: &Ident, label: &Ident, repl_cat: &Ident) -> TokenStream {
    let same_category = category == repl_cat;

    if same_category {
        // Same category - can substitute
        quote! {
            #category::#label(mettail_runtime::OrdVar(mettail_runtime::Var::Free(v))) => {
                for (i, var) in vars.iter().enumerate() {
                    if v == *var {
                        return repls[i].clone();
                    }
                }
                self.clone()
            }
            #category::#label(_) => self.clone()
        }
    } else {
        // Different category - can't substitute
        quote! { #category::#label(_) => self.clone() }
    }
}

/// Generate match arm for Regular variant
fn generate_regular_subst_arm(
    category: &Ident,
    label: &Ident,
    fields: &[FieldInfo],
    repl_cat: &Ident,
) -> TokenStream {
    let field_names: Vec<Ident> = (0..fields.len()).map(|i| format_ident!("f{}", i)).collect();

    let field_substs: Vec<TokenStream> = fields
        .iter()
        .zip(field_names.iter())
        .map(|(field, name)| {
            let method = subst_method_for_category(&field.category, repl_cat);
            if field.is_collection {
                // Collection field - map over elements
                match field.coll_type.as_ref().unwrap_or(&CollectionType::HashBag) {
                    CollectionType::HashBag => {
                        quote! {
                            {
                                let mut bag = mettail_runtime::HashBag::new();
                                for (elem, count) in #name.iter() {
                                    let s = elem.#method(vars, repls);
                                    for _ in 0..count { bag.insert(s.clone()); }
                                }
                                bag
                            }
                        }
                    },
                    CollectionType::HashSet => {
                        quote! {
                            #name.iter().map(|elem| elem.#method(vars, repls)).collect()
                        }
                    },
                    CollectionType::Vec => {
                        quote! {
                            #name.iter().map(|elem| elem.#method(vars, repls)).collect()
                        }
                    },
                }
            } else {
                // Regular boxed field - recurse
                quote! { Box::new((**#name).#method(vars, repls)) }
            }
        })
        .collect();

    quote! {
        #category::#label(#(#field_names),*) => {
            #category::#label(#(#field_substs),*)
        }
    }
}

/// Generate match arm for Collection variant
fn generate_collection_subst_arm(
    category: &Ident,
    label: &Ident,
    element_cat: &Ident,
    coll_type: &CollectionType,
    repl_cat: &Ident,
) -> TokenStream {
    let method = subst_method_for_category(element_cat, repl_cat);

    match coll_type {
        CollectionType::HashBag => {
            quote! {
                #category::#label(bag) => {
                    let mut new_bag = mettail_runtime::HashBag::new();
                    for (elem, count) in bag.iter() {
                        let s = elem.#method(vars, repls);
                        for _ in 0..count { new_bag.insert(s.clone()); }
                    }
                    #category::#label(new_bag)
                }
            }
        },
        CollectionType::HashSet => {
            quote! {
                #category::#label(set) => {
                    #category::#label(set.iter().map(|elem| elem.#method(vars, repls)).collect())
                }
            }
        },
        CollectionType::Vec => {
            quote! {
                #category::#label(vec) => {
                    #category::#label(vec.iter().map(|elem| elem.#method(vars, repls)).collect())
                }
            }
        },
    }
}

/// Generate match arm for single Binder variant
fn generate_binder_subst_arm(
    category: &Ident,
    label: &Ident,
    pre_scope_fields: &[FieldInfo],
    binder_cat: &Ident,
    body_cat: &Ident,
    repl_cat: &Ident,
) -> TokenStream {
    let should_filter = binder_cat == repl_cat;
    let body_method = subst_method_for_category(body_cat, repl_cat);

    // Generate field names for pre-scope fields
    let field_names: Vec<Ident> = (0..pre_scope_fields.len())
        .map(|i| format_ident!("f{}", i))
        .collect();

    // Generate substitutions for pre-scope fields
    let field_substs: Vec<TokenStream> = pre_scope_fields
        .iter()
        .zip(field_names.iter())
        .map(|(field, name)| {
            let method = subst_method_for_category(&field.category, repl_cat);
            if field.is_collection {
                match field.coll_type.as_ref().unwrap_or(&CollectionType::Vec) {
                    CollectionType::Vec => {
                        quote! { #name.iter().map(|elem| elem.#method(vars, repls)).collect() }
                    },
                    _ => quote! { #name.clone() },
                }
            } else {
                quote! { Box::new((**#name).#method(vars, repls)) }
            }
        })
        .collect();

    let pattern = if field_names.is_empty() {
        quote! { #category::#label(scope) }
    } else {
        quote! { #category::#label(#(#field_names,)* scope) }
    };

    let reconstruction = if field_names.is_empty() {
        quote! { #category::#label(new_scope) }
    } else {
        quote! { #category::#label(#(#field_substs,)* new_scope) }
    };

    if should_filter {
        // Same category binder - need to filter shadowed vars
        quote! {
            #pattern => {
                let binder = &scope.inner().unsafe_pattern;
                let body = &scope.inner().unsafe_body;

                // Filter out shadowed variables
                let (fvars, frepls): (Vec<_>, Vec<_>) = vars.iter()
                    .zip(repls.iter())
                    .filter(|(v, _)| binder.0 != ***v)
                    .map(|(v, r)| (*v, r.clone()))
                    .unzip();

                if fvars.is_empty() {
                    self.clone()
                } else {
                    let new_body = (**body).#body_method(&fvars[..], &frepls);
                    let new_scope = mettail_runtime::Scope::new(binder.clone(), Box::new(new_body));
                    #reconstruction
                }
            }
        }
    } else {
        // Different category binder - no shadowing, just recurse
        quote! {
            #pattern => {
                let binder = &scope.inner().unsafe_pattern;
                let body = &scope.inner().unsafe_body;
                let new_body = (**body).#body_method(vars, repls);
                let new_scope = mettail_runtime::Scope::new(binder.clone(), Box::new(new_body));
                #reconstruction
            }
        }
    }
}

/// Generate match arm for MultiBinder variant
fn generate_multi_binder_subst_arm(
    category: &Ident,
    label: &Ident,
    pre_scope_fields: &[FieldInfo],
    binder_cat: &Ident,
    body_cat: &Ident,
    repl_cat: &Ident,
) -> TokenStream {
    let should_filter = binder_cat == repl_cat;
    let body_method = subst_method_for_category(body_cat, repl_cat);

    // Generate field names for pre-scope fields (typically Vec<Name>)
    let field_names: Vec<Ident> = (0..pre_scope_fields.len())
        .map(|i| format_ident!("f{}", i))
        .collect();

    // Generate substitutions for pre-scope fields
    let field_substs: Vec<TokenStream> = pre_scope_fields
        .iter()
        .zip(field_names.iter())
        .map(|(field, name)| {
            let method = subst_method_for_category(&field.category, repl_cat);
            if field.is_collection {
                quote! { #name.iter().map(|elem| elem.#method(vars, repls)).collect() }
            } else {
                quote! { Box::new((**#name).#method(vars, repls)) }
            }
        })
        .collect();

    let pattern = if field_names.is_empty() {
        quote! { #category::#label(scope) }
    } else {
        quote! { #category::#label(#(#field_names,)* scope) }
    };

    let reconstruction = if field_names.is_empty() {
        quote! { #category::#label(new_scope) }
    } else {
        quote! { #category::#label(#(#field_substs,)* new_scope) }
    };

    if should_filter {
        // Same category binder - filter all shadowed vars
        quote! {
            #pattern => {
                let binders = &scope.inner().unsafe_pattern;
                let body = &scope.inner().unsafe_body;

                // Filter out all variables shadowed by any binder
                let (fvars, frepls): (Vec<_>, Vec<_>) = vars.iter()
                    .zip(repls.iter())
                    .filter(|(v, _)| !binders.iter().any(|b| &b.0 == **v))
                    .map(|(v, r)| (*v, r.clone()))
                    .unzip();

                if fvars.is_empty() {
                    self.clone()
                } else {
                    let new_body = (**body).#body_method(&fvars[..], &frepls);
                    let new_scope = mettail_runtime::Scope::new(binders.clone(), Box::new(new_body));
                    #reconstruction
                }
            }
        }
    } else {
        // Different category binder - no shadowing, just recurse
        quote! {
            #pattern => {
                let binders = &scope.inner().unsafe_pattern;
                let body = &scope.inner().unsafe_body;
                let new_body = (**body).#body_method(vars, repls);
                let new_scope = mettail_runtime::Scope::new(binders.clone(), Box::new(new_body));
                #reconstruction
            }
        }
    }
}

/// Get the substitution method name for a field category
fn subst_method_for_category(field_cat: &Ident, repl_cat: &Ident) -> TokenStream {
    if field_cat == repl_cat {
        quote! { subst }
    } else {
        let method = format_ident!("subst_{}", repl_cat.to_string().to_lowercase());
        quote! { #method }
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::language::LangType;
    use syn::parse_quote;

    #[test]
    fn test_variant_kind_nullary() {
        let rule = GrammarRule {
            label: parse_quote!(PZero),
            category: parse_quote!(Proc),
            items: vec![GrammarItem::Terminal("0".to_string())],
            bindings: vec![],
            term_context: None,
            syntax_pattern: None,
            rust_code: None,
            eval_mode: None,
        };

        let language = LanguageDef {
            name: parse_quote!(Test),
            types: vec![LangType {
                name: parse_quote!(Proc),
                native_type: None,
            }],
            terms: vec![rule.clone()],
            equations: vec![],
            rewrites: vec![],
            semantics: vec![],
        };

        let variant = rule_to_variant_kind(&rule, &language);
        assert!(matches!(variant, VariantKind::Nullary { .. }));
    }

    #[test]
    fn test_generate_simple_substitution() {
        let language = LanguageDef {
            name: parse_quote!(Test),
            types: vec![LangType {
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
                    rust_code: None,
                    eval_mode: None,
                },
                GrammarRule {
                    label: parse_quote!(EVar),
                    category: parse_quote!(Elem),
                    items: vec![GrammarItem::NonTerminal(parse_quote!(Var))],
                    bindings: vec![],
                    term_context: None,
                    syntax_pattern: None,
                    rust_code: None,
                    eval_mode: None,
                },
            ],
            equations: vec![],
            rewrites: vec![],
            semantics: vec![],
        };

        let output = generate_substitution(&language);
        let output_str = output.to_string();

        // Check that it generates substitute method
        assert!(output_str.contains("substitute"));
        assert!(output_str.contains("subst"));
    }
}
