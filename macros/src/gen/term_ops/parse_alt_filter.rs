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
//! ## Stack-safety and equivalence
//!
//! The generated visitor is an explicit pushdown traversal. It skips
//! foreign-category sub-trees (an auto-injection wrapper's foreign term is
//! governed by that category's visitor when that parse runs) and folds two
//! booleans over the home-category descendant set:
//!
//! ```text
//! has_auto_injected = OR(node is an auto-injected wrapper)
//! has_native_literal = OR(node is a native literal)
//! ```
//!
//! Both joins are associative, commutative, and idempotent. Replacing recursive
//! calls with a LIFO worklist therefore preserves the result without a result
//! stack or combine frames. Encountering a native literal may stop immediately:
//! `has_auto_injected && !has_native_literal` is then false regardless of the
//! unvisited suffix. Native stack usage is independent of term depth.

use crate::gen::term_ops::collection_walk::{
    for_each_subterm, plan_for, CollectionPlan, OrderSensitivity, WalkOrder,
};
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

/// Generate the shared uniform-filter PDA, `is_uniformly_auto_injected()`
/// methods for all categories, and the inner-enum dispatch on
/// `<LangName>TermInner`.
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

    let task_enum = generate_uniform_task_enum(language);
    let engine = generate_uniform_engine(language, &auto_inj_labels);

    // Per-category wrappers seed the shared worklist engine.
    let cat_impls: Vec<TokenStream> = language
        .types
        .iter()
        .map(|lang_type| generate_uniform_wrapper(&lang_type.name))
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
        #task_enum
        #engine
        #(#cat_impls)*
        #inner_impl
    }
}

fn generate_uniform_task_enum(language: &LanguageDef) -> TokenStream {
    let variants: Vec<TokenStream> = language
        .types
        .iter()
        .map(|t| {
            let cat = &t.name;
            let variant = format_ident!("Uniform{}", cat);
            quote! { #variant(*const #cat) }
        })
        .collect();

    quote! {
        /// One home-category node awaiting inspection by the uniformly-injected
        /// alternative filter.
        #[allow(dead_code)]
        enum UniformTask {
            #(#variants),*
        }

        // SAFETY: pointers are derived from the wrapper's live `&self`, are
        // dereferenced only while that borrow remains live, and never leave the
        // invoking thread. These marker impls match the generated PDA task
        // families used by the other term operations.
        unsafe impl Send for UniformTask {}
        unsafe impl Sync for UniformTask {}

        thread_local! {
            /// Reuses the task allocation across calls. A re-entrant call takes
            /// an empty vector while the outer call owns the pooled vector.
            static UNIFORM_TASK_POOL: std::cell::Cell<Vec<UniformTask>> =
                std::cell::Cell::new(Vec::new());
        }
    }
}

fn generate_uniform_engine(
    language: &LanguageDef,
    auto_inj_labels: &HashSet<String>,
) -> TokenStream {
    let handlers: Vec<TokenStream> = language
        .types
        .iter()
        .map(|t| {
            let cat = &t.name;
            let helper = format_ident!("uniform_handle_{}", cat.to_string().to_lowercase());
            let arms: Vec<TokenStream> = collect_category_variants(cat, language)
                .iter()
                .map(|variant| generate_arm(cat, variant, auto_inj_labels, language))
                .collect();
            quote! {
                #[inline(never)]
                #[allow(dead_code, unused_variables, non_snake_case)]
                fn #helper(
                    stack: &mut Vec<UniformTask>,
                    ptr: *const #cat,
                    has_auto_inj: &mut bool,
                    has_native_lit: &mut bool,
                ) {
                    let value = unsafe { &*ptr };
                    match value {
                        #(#arms)*
                    }
                }
            }
        })
        .collect();

    let dispatch: Vec<TokenStream> = language
        .types
        .iter()
        .map(|t| {
            let cat = &t.name;
            let variant = format_ident!("Uniform{}", cat);
            let helper = format_ident!("uniform_handle_{}", cat.to_string().to_lowercase());
            quote! {
                UniformTask::#variant(ptr) => {
                    #helper(stack, ptr, &mut has_auto_inj, &mut has_native_lit);
                }
            }
        })
        .collect();

    quote! {
        #(#handlers)*

        /// Drains the explicit worklist and returns the two disjunctions used by
        /// `is_uniformly_auto_injected`. A native literal is an absorbing
        /// negative result for the caller, so the remaining tasks need not run.
        #[allow(dead_code, unused_variables)]
        fn uniform_flags_iterative(stack: &mut Vec<UniformTask>) -> (bool, bool) {
            let mut has_auto_inj = false;
            let mut has_native_lit = false;
            while let Some(task) = stack.pop() {
                match task {
                    #(#dispatch),*
                }
                if has_native_lit {
                    break;
                }
            }
            (has_auto_inj, has_native_lit)
        }
    }
}

fn generate_uniform_wrapper(category: &Ident) -> TokenStream {
    let task_variant = format_ident!("Uniform{}", category);
    quote! {
        impl #category {
            /// Returns `true` when this is a ground, uniformly auto-injected
            /// alternative with no native literal anchor.
            ///
            /// The flag walk uses a pooled explicit worklist, so native stack
            /// usage is independent of term nesting depth.
            pub fn is_uniformly_auto_injected(&self) -> bool {
                let mut stack = UNIFORM_TASK_POOL.with(|pool| pool.take());
                stack.clear();
                stack.push(UniformTask::#task_variant(self as *const _));
                let (has_auto_inj, has_native_lit) = uniform_flags_iterative(&mut stack);
                // `uniform_flags_iterative` can stop with queued pointers when a
                // native literal makes the final predicate false. Never return
                // those borrowed pointers to the reusable pool.
                stack.clear();
                UNIFORM_TASK_POOL.with(|pool| pool.set(stack));

                // Groundness is intentionally checked last. Var-containing
                // alternatives must survive until environment substitution can
                // ground their foreign-category variables.
                has_auto_inj && !has_native_lit && self.is_ground()
            }
        }
    }
}

/// Generate a single match arm for one variant of a category.
fn generate_arm(
    category: &Ident,
    variant: &VariantKind,
    auto_inj_labels: &HashSet<String>,
    language: &LanguageDef,
) -> TokenStream {
    match variant {
        // ★ #141 G5 — a classification that refuses carries its diagnostic into
        // the emitted code, where `rustc` renders it. See `VariantKind::Refused`.
        VariantKind::Refused { message, .. } => quote! { compile_error!(#message); },
        VariantKind::Var { label } => {
            quote! { #category::#label(_) => {}, }
        },
        // Stage 0 identity — STAYS. This asks "is this alternative a native
        // literal reading?", which is true of a collection literal as well.
        VariantKind::Literal { label } | VariantKind::CollectionLiteral { label, .. } => {
            quote! { #category::#label(_) => { *has_native_lit = true; }, }
        },
        VariantKind::Nullary { label } => {
            quote! { #category::#label => {}, }
        },
        VariantKind::Regular { label, fields } => {
            let label_str = label.to_string();
            let is_auto_inj = auto_inj_labels.contains(&label_str);
            generate_regular_arm(category, label, fields, is_auto_inj, language)
        },
        VariantKind::Collection { label, element_cat, coll_type } => {
            // Recurse into elements only if they're same-category.
            let recurse = if element_cat == category {
                collection_pushes(category, coll_type, &quote! { coll }, language)
            } else {
                quote! {}
            };
            quote! {
                #category::#label(coll) => { #recurse },
            }
        },
        VariantKind::Binder { label, pre_scope_fields, body_cat, .. }
        | VariantKind::MultiBinder { label, pre_scope_fields, body_cat, .. } => {
            generate_binder_arm(category, label, pre_scope_fields, body_cat, language)
        },
    }
}

/// Generate the per-field walk for one Regular constructor.
fn generate_regular_arm(
    category: &Ident,
    label: &Ident,
    fields: &[FieldInfo],
    is_auto_inj: bool,
    language: &LanguageDef,
) -> TokenStream {
    let field_names: Vec<Ident> = (0..fields.len()).map(|i| format_ident!("f{}", i)).collect();

    let recurse_calls: Vec<TokenStream> = fields
        .iter()
        .zip(field_names.iter())
        .filter_map(|(field, name)| field_walk(field, name, category, language))
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
        #category::#label(#(#pattern_fields),*) => { #body },
    }
}

/// Generate a recursion call for a single field, returning None if
/// the field shouldn't be visited (predicate, or foreign-cat).
fn field_walk(
    field: &FieldInfo,
    name: &Ident,
    home_cat: &Ident,
    language: &LanguageDef,
) -> Option<TokenStream> {
    let task_variant = format_ident!("Uniform{}", home_cat);
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
            let inner_walk = collection_pushes(home_cat, coll, &quote! { __c }, language);
            return Some(quote! {
                if let Some(__c) = #name.as_ref() {
                    #inner_walk
                }
            });
        }
        return Some(quote! {
            if let Some(__b) = #name.as_ref() {
                stack.push(UniformTask::#task_variant(__b.as_ref() as *const _));
            }
        });
    }
    if field.is_collection {
        if field.category != *home_cat {
            return None;
        }
        let coll = field.coll_type.as_ref().unwrap_or(&CollectionType::HashBag);
        return Some(collection_pushes(home_cat, coll, &quote! { #name }, language));
    }
    // Plain Box<Cat> field. Only recurse if same-cat.
    if field.category != *home_cat {
        return None;
    }
    Some(quote! {
        stack.push(UniformTask::#task_variant(&**#name as *const _));
    })
}

/// Push every term position of a same-category collection. The two flag joins
/// are order-agnostic, so all collection representations—including PathMap's
/// key plus optional Set value—can use the common element boundary.
fn collection_pushes(
    category: &Ident,
    coll: &CollectionType,
    expression: &TokenStream,
    language: &LanguageDef,
) -> TokenStream {
    match plan_for(category, coll, OrderSensitivity::OrderAgnostic, language) {
        CollectionPlan::PerElement { coll_type, .. } => {
            let task_variant = format_ident!("Uniform{}", category);
            for_each_subterm(&coll_type, expression, WalkOrder::Forward, &|element, _| {
                quote! {
                    stack.push(UniformTask::#task_variant(#element as *const _));
                }
            })
        },
        // `category` is a known language category, so the order-agnostic plan
        // is necessarily per-element.
        CollectionPlan::WholeValue { .. } => quote! {},
    }
}

/// Generate a match arm for Binder/MultiBinder.
fn generate_binder_arm(
    category: &Ident,
    label: &Ident,
    pre_scope_fields: &[FieldInfo],
    body_cat: &Ident,
    language: &LanguageDef,
) -> TokenStream {
    let field_names: Vec<Ident> = (0..pre_scope_fields.len())
        .map(|i| format_ident!("f{}", i))
        .collect();

    let pre_recurses: Vec<TokenStream> = pre_scope_fields
        .iter()
        .zip(field_names.iter())
        .filter_map(|(field, name)| field_walk(field, name, category, language))
        .collect();

    let task_variant = format_ident!("Uniform{}", category);
    let body_recurse = if body_cat == category {
        quote! {
            let __body: *const #category = &*scope.inner().unsafe_body;
            stack.push(UniformTask::#task_variant(__body));
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
        },
    }
}
