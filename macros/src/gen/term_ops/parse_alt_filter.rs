//! Stage 3.12.8 M2 (2026-05-03): per-category AST visitor for filtering
//! spurious cross-category parse alternatives.
//!
//! Generates a method `is_uniformly_auto_injected(&self) -> bool` per
//! category. Returns `true` exactly when:
//!   - The home-category tree contains at least one auto-injected
//!     wrapper (variant whose backing rule has `is_auto_injected = true`).
//!   - The home-category tree contains zero native literals (e.g.,
//!     `BigRat::RatLit`, `Float::FloatLit`, `Int::NumLit`).
//!
//! `parse_preserving_vars` calls this on each successful per-cat parse
//! before pushing to `successes`. Spurious alternatives like
//! `BigRat::DivBigRat(BigRat::FloatToBigRat(Float::AddFloat(...)),
//! BigRat::FloatToBigRat(Float::FloatLit(3.0)))` (which arise via
//! Stage 3.13 auto-injection wrapping a Float subtree in BigRat
//! casts) get filtered out, leaving only the legitimate Float parse
//! to reach `from_alternatives`.
//!
//! Pre-Stage-3.12.7 these spurious alternatives never reached EOI
//! because cursors that popped past the GSS root were dropped at the
//! Idle handler. Stage 3.12.7's `popped_past_root → Resolved` keeps
//! them alive through to `commit_winner`, requiring this filter at
//! the parse_preserving_vars boundary.
//!
//! ## Recursion strategy
//!
//! Recursive `match self { ... }` mirrors the `is_ground` template.
//! Skips foreign-category sub-trees (auto-injection wrappers wrap a
//! different category's term — that subtree's auto-injection status
//! is governed by ITS home category's visitor when ITS parse runs).
//! Stack-safe for typical parses (depth < 100); pathological depth
//! is bounded by `iterative_drop`-style rewrite if it ever surfaces.

use mettail_ast::language::LanguageDef;
use mettail_ast::types::CollectionType;
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use std::collections::HashSet;
use syn::Ident;

use super::subst::{collect_category_variants, FieldInfo, VariantKind};

/// Cat-A fix (2026-05-13): detect user-declared cross-cat unary cast rules.
/// Shape: `<Source>To<Target> . a:Y |- <triggers> a <triggers> : X` where
/// `Y != X` and `sp.len() >= 3`. Calculator examples: `IntToBool`, `BoolToFloat`,
/// `StrToInt`, `BigintCast`, `BigratCast`, `ProcToBool`, `ProcToStr`, etc.
///
/// Byte-identical to Pass 2c's emission gate in
/// `macros/src/gen/runtime/wpda_codegen/prefix.rs:1041+`, ensuring the marked
/// rule set is exactly the rules Pass 2c synthesizes implicit-cast arms for.
fn is_cross_cat_unary_cast(rule: &mettail_ast::grammar::GrammarRule) -> bool {
    let Some(tc) = rule.term_context.as_ref() else {
        return false;
    };
    if tc.len() != 1 {
        return false;
    }
    let mettail_ast::grammar::TermParam::Simple { ty, .. } = &tc[0] else {
        return false;
    };
    let mettail_ast::types::TypeExpr::Base(source) = ty else {
        return false;
    };
    let Some(sp) = rule.syntax_pattern.as_ref() else {
        return false;
    };
    if sp.len() < 3 {
        return false;
    }
    source.to_string() != rule.category.to_string()
}

/// Generate `is_uniformly_auto_injected()` and `_collect_uniform_flags()`
/// methods for all categories in the language. Plus the inner-enum
/// dispatch on `<LangName>TermInner`.
pub fn generate_parse_alt_filter_methods(language: &LanguageDef) -> TokenStream {
    let inner_enum_name = format_ident!("{}TermInner", language.name);
    let inner_enum_name = &inner_enum_name;
    // Cat-A fix (2026-05-13): include user-declared cross-cat unary cast
    // rules in the auto-inject-equivalent set. These are NonAtomic rules
    // of shape `<Source>To<Target> . a:Y |- <triggers> a <triggers> : X`
    // where `Y != X` (e.g., Calculator's `IntToBool`, `BoolToFloat`,
    // `BigintCast`, `BigratCast`, `ProcToBool`, `ProcToStr`, etc.).
    //
    // Pass 2c (wpda_codegen/prefix.rs:1041+) emits implicit-cast Fork
    // branches in the result category's prefix dispatch for FIRST(source)
    // tokens. These are REQUIRED for internal cross-cat sub-parses inside
    // single-cat `Cat::parse` (e.g., LtBool's RHS in `int(false > b < -N)`
    // wraps an Int via IntToBool to produce a Bool arg). BUT they ALSO
    // create spurious lossy multi-cat parses (`(3r/4r) bitand (1r/4r)`
    // parses as `BigInt::BitAndBigInt(BigintCast(...), BigintCast(...))`
    // alongside the correct `BigRat::BitAndBigRat(...)`).
    //
    // Marking these rules as auto-inject-equivalent in `auto_inj_labels`
    // lets `is_uniformly_auto_injected` flag the BigInt alt (`BitAndBigInt`
    // recursing into `BigintCast`-tagged fields) as spurious. The filter
    // at `language.rs:2702-2716` then drops the BigInt alt when any
    // non-spurious alt (BigRat) survives. The mechanism mirrors how
    // auto-injected `<Source>To<Target>` rules from `auto_inject.rs` are
    // handled today.
    //
    // Predicate (`is_cross_cat_unary_cast`) is byte-identical to Pass 2c's
    // emission gate so the marked rule set exactly matches the arms Pass 2c
    // emits. Pass 2c STAYS in place; WPDS-level internal cross-cat sub-
    // parses continue to work.
    let auto_inj_labels: HashSet<String> = language
        .terms
        .iter()
        .filter(|r| r.is_auto_injected || is_cross_cat_unary_cast(r))
        .map(|r| r.label.to_string())
        .collect();

    // Per-category `impl Cat { ... }` blocks with the visitor methods.
    let cat_impls: Vec<TokenStream> = language
        .types
        .iter()
        .map(|lang_type| {
            let category = &lang_type.name;
            let variants = collect_category_variants(category, language);
            let match_arms: Vec<TokenStream> = variants
                .iter()
                .map(|v| generate_arm(category, v, &auto_inj_labels))
                .collect();
            quote! {
                impl #category {
                    /// Stage 3.12.8 M2 (2026-05-03): returns `true` if this
                    /// term is a "uniformly auto-injected" parse alternative
                    /// — auto-injection wrappers around a foreign category
                    /// with no same-category native literal anchor.
                    ///
                    /// Cat-A v3 refinement (2026-05-13): additionally requires
                    /// `is_ground()`. The auto-inj-no-native-lit shape is only
                    /// spurious when the tree is fully ground — i.e., a lossy
                    /// cast actually fires. Var-containing trees (where env-
                    /// substitution will ground a foreign-cat var later) must
                    /// be KEPT so the var-bearing alt survives the filter and
                    /// reduces correctly post-substitute (e.g.,
                    /// `Float::BoolToFloat(Bool::BVar(x))` with
                    /// `env.bool["x"]=BoolLit(true)` reduces to FloatLit(1.0)
                    /// only if the alt is preserved during parse).
                    pub fn is_uniformly_auto_injected(&self) -> bool {
                        let mut has_auto_inj = false;
                        let mut has_native_lit = false;
                        self._collect_uniform_flags(&mut has_auto_inj, &mut has_native_lit);
                        has_auto_inj && !has_native_lit && self.is_ground()
                    }

                    fn _collect_uniform_flags(
                        &self,
                        has_auto_inj: &mut bool,
                        has_native_lit: &mut bool,
                    ) {
                        match self {
                            #(#match_arms),*
                        }
                    }
                }
            }
        })
        .collect();

    // Inner enum dispatch — emitted only for multi-type languages where
    // the wrapper Inner enum exists. Single-type languages have no
    // wrapper, and `parse_preserving_vars` for them has no successes
    // loop to filter, so this dispatch is unused.
    let inner_impl = if language.types.len() > 1 {
        let inner_arms: Vec<TokenStream> = language
            .types
            .iter()
            .map(|lang_type| {
                let cat = &lang_type.name;
                let variant = format_ident!("{}", cat);
                quote! {
                    #inner_enum_name::#variant(t) => t.is_uniformly_auto_injected()
                }
            })
            .collect();
        quote! {
            impl #inner_enum_name {
                /// Stage 3.12.8 M2 (2026-05-03): forwards to the wrapped
                /// per-category `is_uniformly_auto_injected`. Used by
                /// `parse_preserving_vars` to filter spurious cross-cat
                /// parse alternatives. `Ambiguous` always returns false
                /// (an Ambiguous wrapper is a multi-cat result; per-cat
                /// filtering already happened upstream).
                pub fn is_uniformly_auto_injected(&self) -> bool {
                    match self {
                        #(#inner_arms,)*
                        #inner_enum_name::Ambiguous(_) => false,
                    }
                }
            }
        }
    } else {
        quote! {}
    };

    quote! {
        #(#cat_impls)*
        #inner_impl
    }
}

/// Generate a single match arm for one variant of a category.
fn generate_arm(
    category: &Ident,
    variant: &VariantKind,
    auto_inj_labels: &HashSet<String>,
) -> TokenStream {
    match variant {
        VariantKind::Var { label } => {
            quote! { #category::#label(_) => {} }
        },
        VariantKind::Literal { label } => {
            quote! { #category::#label(_) => { *has_native_lit = true; } }
        },
        VariantKind::Nullary { label } => {
            quote! { #category::#label => {} }
        },
        VariantKind::Regular { label, fields } => {
            let label_str = label.to_string();
            let is_auto_inj = auto_inj_labels.contains(&label_str);
            generate_regular_arm(category, label, fields, is_auto_inj)
        },
        VariantKind::Collection { label, element_cat, coll_type } => {
            // Recurse into elements only if they're same-category.
            let recurse = if element_cat == category {
                collection_walk(quote! { coll }, coll_type)
            } else {
                quote! {}
            };
            quote! {
                #category::#label(coll) => { #recurse }
            }
        },
        VariantKind::Binder { label, pre_scope_fields, body_cat, .. }
        | VariantKind::MultiBinder { label, pre_scope_fields, body_cat, .. } => {
            generate_binder_arm(category, label, pre_scope_fields, body_cat)
        },
    }
}

/// Generate the per-field walk for one Regular constructor.
fn generate_regular_arm(
    category: &Ident,
    label: &Ident,
    fields: &[FieldInfo],
    is_auto_inj: bool,
) -> TokenStream {
    let field_names: Vec<Ident> = (0..fields.len()).map(|i| format_ident!("f{}", i)).collect();

    let recurse_calls: Vec<TokenStream> = fields
        .iter()
        .zip(field_names.iter())
        .filter_map(|(field, name)| field_walk(field, name, category))
        .collect();

    // Wildcard pattern for fields we don't recurse into (predicates,
    // foreign-cat). Use `_` for unused field bindings.
    let pattern_fields: Vec<TokenStream> = field_names
        .iter()
        .zip(fields.iter())
        .map(|(name, field)| {
            // We'll always bind by name; the recurse loop above only
            // emits walks for fields we care about. Unused bindings
            // get suppressed by the `let _ = name;` pattern via the
            // wildcard arm below if needed. Simpler: prefix unused.
            let _ = field;
            quote! { #name }
        })
        .collect();

    let body = if is_auto_inj {
        // Auto-injected wrapper: set has_auto_inj. Don't recurse into
        // foreign-cat children (their auto-inj status is governed by
        // their own home cat's visitor).
        let suppress_unused: Vec<TokenStream> =
            field_names.iter().map(|n| quote! { let _ = #n; }).collect();
        quote! {
            *has_auto_inj = true;
            #(#suppress_unused)*
        }
    } else if recurse_calls.is_empty() {
        // No same-cat recursion needed; suppress unused bindings.
        let suppress_unused: Vec<TokenStream> =
            field_names.iter().map(|n| quote! { let _ = #n; }).collect();
        quote! { #(#suppress_unused)* }
    } else {
        let suppress_unused: Vec<TokenStream> =
            field_names.iter().map(|n| quote! { let _ = #n; }).collect();
        quote! {
            #(#suppress_unused)*
            #(#recurse_calls)*
        }
    };

    quote! {
        #category::#label(#(#pattern_fields),*) => { #body }
    }
}

/// Generate a recursion call for a single field, returning None if
/// the field shouldn't be visited (predicate, or foreign-cat).
fn field_walk(field: &FieldInfo, name: &Ident, home_cat: &Ident) -> Option<TokenStream> {
    if field.is_predicate {
        return None;
    }
    if field.is_optional {
        if field.category != *home_cat {
            return None;
        }
        // Phase 4 #3 (2026-05-12): Optional-Collection — unwrap
        // Option first, then dispatch by collection kind.
        if field.is_collection {
            let coll = field.coll_type.as_ref().unwrap_or(&CollectionType::HashBag);
            let inner_walk = collection_walk(quote! { __c }, coll);
            return Some(quote! {
                if let Some(__c) = #name.as_ref() {
                    #inner_walk
                }
            });
        }
        return Some(quote! {
            if let Some(__b) = #name.as_ref() {
                __b._collect_uniform_flags(has_auto_inj, has_native_lit);
            }
        });
    }
    if field.is_collection {
        if field.category != *home_cat {
            return None;
        }
        let coll = field.coll_type.as_ref().unwrap_or(&CollectionType::HashBag);
        return Some(collection_walk(quote! { #name }, coll));
    }
    // Plain Box<Cat> field. Only recurse if same-cat.
    if field.category != *home_cat {
        return None;
    }
    Some(quote! {
        #name._collect_uniform_flags(has_auto_inj, has_native_lit);
    })
}

/// Generate the per-element walk for a collection.
fn collection_walk(name: TokenStream, coll: &CollectionType) -> TokenStream {
    match coll {
        CollectionType::HashBag => quote! {
            for (__elt, _count) in #name.iter() {
                __elt._collect_uniform_flags(has_auto_inj, has_native_lit);
            }
        },
        CollectionType::Vec | CollectionType::HashSet => quote! {
            for __elt in #name.iter() {
                __elt._collect_uniform_flags(has_auto_inj, has_native_lit);
            }
        },
        CollectionType::HashMap | CollectionType::PathMap => quote! {
            for (__k, __v) in #name.iter() {
                __k._collect_uniform_flags(has_auto_inj, has_native_lit);
                __v._collect_uniform_flags(has_auto_inj, has_native_lit);
            }
        },
    }
}

/// Generate a match arm for Binder/MultiBinder.
fn generate_binder_arm(
    category: &Ident,
    label: &Ident,
    pre_scope_fields: &[FieldInfo],
    body_cat: &Ident,
) -> TokenStream {
    let field_names: Vec<Ident> = (0..pre_scope_fields.len())
        .map(|i| format_ident!("f{}", i))
        .collect();

    let pre_recurses: Vec<TokenStream> = pre_scope_fields
        .iter()
        .zip(field_names.iter())
        .filter_map(|(field, name)| field_walk(field, name, category))
        .collect();

    let body_recurse = if body_cat == category {
        quote! {
            scope.inner().unsafe_body._collect_uniform_flags(has_auto_inj, has_native_lit);
        }
    } else {
        quote! {}
    };

    let pattern = if field_names.is_empty() {
        quote! { #category::#label(scope) }
    } else {
        quote! { #category::#label(#(#field_names,)* scope) }
    };

    // Suppress unused warnings for fields we don't recurse into.
    let suppress_unused: Vec<TokenStream> = field_names
        .iter()
        .zip(pre_scope_fields.iter())
        .filter_map(|(name, field)| {
            if field.category == *category && !field.is_predicate {
                None // already used in recursion
            } else {
                Some(quote! { let _ = #name; })
            }
        })
        .collect();

    let scope_unused = if body_cat == category {
        quote! {}
    } else {
        quote! { let _ = scope; }
    };

    quote! {
        #pattern => {
            #(#pre_recurses)*
            #(#suppress_unused)*
            #body_recurse
            #scope_unused
        }
    }
}
