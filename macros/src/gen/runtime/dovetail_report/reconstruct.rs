//! Step D of the Dovetail native-fold reduction work (Increment 3): the
//! `Derivation<L, W> → <Cat>` reconstructor — the inverse of the typed lowering
//! ([`super::typed_lowering`]).
//!
//! For each category we emit `__mettail_dovetail_build_<cat>_d(&Rc<Derivation<L,W>>) ->
//! Option<<Cat>>`, which matches the chosen op (`d.op`, a typed `L`) back to the AST
//! constructor, recursing on the already-chosen child derivations (`d.children` — the
//! funded 1-best subtrees the parent's extraction selected, so the tree is consistent).
//! Leaf payloads (literals/vars, and whole `List`/`Map`/`Bag` category values) are read back
//! losslessly; spine sentinels (`FieldOpaque`/`FieldNone`/`BinderArity`) and any op not a root
//! of this category yield `None` — the "stuck child ⇒ no fold" case of `APPLY-NATIVE-FOLD`.
//!
//! Reconstruction is emitted for the structurally-invertible variants: `Var`, `Literal`
//! (including the collection-category `ListLit`/`MapLit`/`BagLit` whole-value leaves),
//! `Nullary`, `Regular` constructors whose fields are all plain (non-optional,
//! non-collection, non-predicate) category children wrapped in `Arc`, and (E2.1) the AC
//! `Collection` (HashBag soup), `Binder`, and `MultiBinder` variants — each the exact
//! structural inverse of the corresponding [`super::typed_lowering`] arm. A `Regular`
//! constructor with a builtin/opaque/optional/predicate field is not invertible here (its
//! lowered child is a sentinel) and reconstructs to `None`, faithfully deferring any fold
//! that would read it; a non-AC (`Vec`/`HashSet`/`HashMap`) collection field likewise lowers
//! to a `FieldOpaque` spine leaf and stays `None`.
//!
//! E2.1 (AC `Collection`/`Binder`/`MultiBinder` inverses):
//! - **AC `Collection` (HashBag soup):** the lowering ([`super::typed_lowering`]
//!   `ac_bag_lowering_typed`) pushes one child PER MULTIPLICITY (`HashBag::iter_elements`
//!   flat-maps `repeat_n(elem, count)`), so the inverse reconstructs each `d.children[i]`
//!   and inserts it via the generated `Cat::insert_into_<label>` auto-flattening helper
//!   (`normalize.rs`), restoring multiplicity faithfully (`{P,P}` → 2 children → multiplicity
//!   2). Only `HashBag` is AC-lowered (and hence invertible); `Vec`/`HashSet`/`HashMap`
//!   collections lower to `FieldOpaque` and stay `None`.
//! - **`Binder`:** children are `[…pre, BinderArity(1), body]`. The inverse verifies the
//!   `BinderArity(1)` marker, reconstructs the pre-scope fields + body, and rebuilds
//!   `Scope::from_parts_unsafe(fresh_binder, Arc::new(body))` with a FRESH `Binder` (the
//!   binder identity was intentionally erased by FIX-A, `typed_lowering.rs`; the body's
//!   positional de-Bruijn `BoundVar` coordinates stay valid, so the result is α-equivalent
//!   to the original — correct, since Dovetail normal forms are α-classes).
//! - **`MultiBinder`:** same with `BinderArity(n)` and `n` fresh binders
//!   (`Vec<Binder<String>>`); the arity is asserted against the marker.
//!
//! Recursive-vs-iterative: these new arms are emitted RECURSIVELY, consistent with the
//! existing recursive `build_fn` they call into (which recurses to term depth, exactly as the
//! `Extractor` derivation it consumes does). A from-scratch iterative-PDA rewrite is not
//! required for E2 correctness and would introduce a new, riskier recursion-elimination class;
//! iterative hardening of the whole file is tracked as a separate follow-up.

use mettail_ast::grammar::NonTerminalKind;
use mettail_ast::language::LanguageDef;
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use syn::Ident;

use super::coll_type_is_ac_bag;
use super::op_enum::{op_enum_ident, op_variant_ident};
use crate::gen::term_ops::subst::{collect_category_variants, FieldInfo, VariantKind};

/// The from-derivation reconstruction fn name for a category (snake-cased to match the
/// `__mettail_dovetail_add_<cat>` lowering convention and satisfy `non_snake_case`).
pub(crate) fn build_fn(category: &Ident) -> Ident {
    format_ident!("__mettail_dovetail_build_{}_d", super::to_snake(&category.to_string()))
}

/// Whether a field is a plain category child (recursively reconstructable): a single
/// non-optional, non-collection, non-predicate, non-opaque-leaf child of an object
/// (non-builtin) category.
///
/// L9-3/L9-4: an opaque-leaf capture (token-text `String` / guest-body
/// `Arc<FltNode>`) is NOT plainly invertible — it was lowered to a LOSSY e-graph
/// leaf (`format!("{}::{:?}", …)`, see `opaque_leaf_expr`), which cannot be
/// parsed back into the payload, and it has no `__mettail_dovetail_build_<leaf>_d`
/// reconstruction fn. A variant carrying one is therefore not structurally
/// invertible; `category_reconstruct` skips it (falls through to `_ => None`).
/// This is sound: such variants (e.g. RhoCalc's inert `PFlt`) never participate in
/// a Dovetail rewrite, so they are never reached for reconstruction.
fn is_plain_category_field(field: &FieldInfo) -> bool {
    !field.is_optional
        && !field.is_collection
        && !field.is_predicate
        && !field.is_opaque_leaf()
        && !NonTerminalKind::classify(&field.category.to_string()).is_builtin()
}

/// Generate `__mettail_dovetail_build_<cat>_d`: reconstruct a `<Cat>` from a derivation tree.
pub(crate) fn category_reconstruct(language: &LanguageDef, category: &Ident) -> TokenStream {
    let enum_id = op_enum_ident(language);
    let fn_name = build_fn(category);

    let mut arms: Vec<TokenStream> = Vec::new();
    for variant in collect_category_variants(category, language) {
        match variant {
            VariantKind::Var { label } | VariantKind::Literal { label } => {
                let v = op_variant_ident(category, &label);
                arms.push(quote! {
                    #enum_id::#v(__p) => ::core::option::Option::Some(#category::#label(__p.clone())),
                });
            },
            VariantKind::Nullary { label } => {
                let v = op_variant_ident(category, &label);
                arms.push(quote! {
                    #enum_id::#v => ::core::option::Option::Some(#category::#label),
                });
            },
            VariantKind::Regular { label, fields } => {
                if fields.is_empty() || !fields.iter().all(is_plain_category_field) {
                    // Not structurally invertible here — falls through to `_ => None`.
                    continue;
                }
                let v = op_variant_ident(category, &label);
                let child_exprs: Vec<TokenStream> = fields
                    .iter()
                    .enumerate()
                    .map(|(i, field)| {
                        let child_build = build_fn(&field.category);
                        quote! {
                            ::std::sync::Arc::new(#child_build(__d.children.get(#i)?)?)
                        }
                    })
                    .collect();
                arms.push(quote! {
                    #enum_id::#v => ::core::option::Option::Some(
                        #category::#label(#(#child_exprs),*)
                    ),
                });
            },
            // (E2.1) AC `Collection` (HashBag soup): the exact inverse of
            // `typed_lowering::ac_bag_lowering_typed`. The lowering pushed one child per
            // MULTIPLICITY (`iter_elements` flat-maps `repeat_n`), so reconstruct every
            // `d.children[i]` and insert it through the generated `Cat::insert_into_<label>`
            // auto-flattening helper (`normalize.rs`), faithfully restoring multiplicity. A
            // stuck child (`build_<elem>_d` → `None`) propagates `None` via `?`, deferring the
            // fold — the "stuck child ⇒ no fold" case of `APPLY-NATIVE-FOLD`. Only `HashBag`
            // is AC-lowered; `Vec`/`HashSet`/`HashMap` lower to `FieldOpaque` and never reach
            // this arm (they have no AC-bag op node), so they correctly stay `None`.
            VariantKind::Collection { label, element_cat, coll_type } => {
                if !coll_type_is_ac_bag(Some(&coll_type)) {
                    // Non-AC collection: lowered as a `FieldOpaque` spine leaf, not invertible.
                    continue;
                }
                let v = op_variant_ident(category, &label);
                let elem_build = build_fn(&element_cat);
                let helper = format_ident!("insert_into_{}", label.to_string().to_lowercase());
                arms.push(quote! {
                    #enum_id::#v => {
                        let mut __bag = ::mettail_runtime::HashBag::<#element_cat>::new();
                        for __child in &__d.children {
                            #category::#helper(&mut __bag, #elem_build(__child)?);
                        }
                        ::core::option::Option::Some(#category::#label(__bag))
                    },
                });
            },
            // (E2.1) `Binder`: the exact inverse of `typed_lowering::binder_arm_typed` with
            // `multi = false`. Lowered children are `[…pre, BinderArity(1), body]`. Reconstruct
            // the pre-scope fields (all plain category children, as in the `Regular` arm), verify
            // the `BinderArity(1)` marker, reconstruct the body via the body category's
            // `build_<body_cat>_d`, then rebuild `Scope::from_parts_unsafe(fresh_binder,
            // Arc::new(body))` exactly as `normalize.rs`'s binder assemble arm — but with a FRESH
            // binder. FIX-A (`typed_lowering.rs`) intentionally erased the original binder identity
            // into an anonymous arity marker; the body's positional de-Bruijn `BoundVar`
            // coordinates remain valid, so the reconstructed scope is α-equivalent to the original
            // (correct — Dovetail normal forms are α-classes). A pre-field/body that is not plainly
            // invertible (`None`) defers the whole reconstruction via `?`.
            VariantKind::Binder { label, pre_scope_fields, body_cat, .. } => {
                if !pre_scope_fields.iter().all(is_plain_category_field) {
                    // A pre-scope field is opaque/optional/predicate/collection — not invertible.
                    continue;
                }
                let v = op_variant_ident(category, &label);
                let body_build = build_fn(&body_cat);
                let pre_exprs: Vec<TokenStream> = pre_scope_fields
                    .iter()
                    .enumerate()
                    .map(|(i, field)| {
                        let child_build = build_fn(&field.category);
                        quote! {
                            ::std::sync::Arc::new(#child_build(__d.children.get(#i)?)?)
                        }
                    })
                    .collect();
                let arity_idx = pre_scope_fields.len();
                let body_idx = pre_scope_fields.len() + 1;
                arms.push(quote! {
                    #enum_id::#v => {
                        // Verify the FIX-A anonymous binder-arity marker (arity 1).
                        match &__d.children.get(#arity_idx)?.op {
                            #enum_id::BinderArity(1u32) => {},
                            _ => return ::core::option::Option::None,
                        }
                        let __body = #body_build(__d.children.get(#body_idx)?)?;
                        let __binder = ::mettail_runtime::Binder(
                            ::mettail_runtime::FreeVar::fresh_unnamed(),
                        );
                        let __scope = ::mettail_runtime::Scope::from_parts_unsafe(
                            __binder,
                            ::std::sync::Arc::new(__body),
                        );
                        ::core::option::Option::Some(
                            #category::#label(#(#pre_exprs,)* __scope)
                        )
                    },
                });
            },
            // (E2.1) `MultiBinder`: the exact inverse of `typed_lowering::binder_arm_typed` with
            // `multi = true`. Lowered children are `[…pre, BinderArity(n), body]`; the scope's
            // pattern is a `Vec<Binder<String>>` of length `n`. Reconstruct the pre-fields + body
            // as above, read `n` from the `BinderArity(n)` marker, and synthesize `n` FRESH binders
            // (same α-equivalence rationale as the single-binder arm). The body de-Bruijn coords
            // index into this `n`-binder scope and stay valid.
            VariantKind::MultiBinder { label, pre_scope_fields, body_cat, .. } => {
                if !pre_scope_fields.iter().all(is_plain_category_field) {
                    continue;
                }
                let v = op_variant_ident(category, &label);
                let body_build = build_fn(&body_cat);
                let pre_exprs: Vec<TokenStream> = pre_scope_fields
                    .iter()
                    .enumerate()
                    .map(|(i, field)| {
                        let child_build = build_fn(&field.category);
                        quote! {
                            ::std::sync::Arc::new(#child_build(__d.children.get(#i)?)?)
                        }
                    })
                    .collect();
                let arity_idx = pre_scope_fields.len();
                let body_idx = pre_scope_fields.len() + 1;
                arms.push(quote! {
                    #enum_id::#v => {
                        // Read the FIX-A anonymous arity-only marker; synthesize that many fresh
                        // binders. (`BinderArity(0)` is degenerate but reconstructs faithfully.)
                        let __arity = match &__d.children.get(#arity_idx)?.op {
                            #enum_id::BinderArity(__n) => *__n as usize,
                            _ => return ::core::option::Option::None,
                        };
                        let __body = #body_build(__d.children.get(#body_idx)?)?;
                        let mut __binders: ::std::vec::Vec<::mettail_runtime::Binder<String>> =
                            ::std::vec::Vec::with_capacity(__arity);
                        for _ in 0..__arity {
                            __binders.push(::mettail_runtime::Binder(
                                ::mettail_runtime::FreeVar::fresh_unnamed(),
                            ));
                        }
                        let __scope = ::mettail_runtime::Scope::from_parts_unsafe(
                            __binders,
                            ::std::sync::Arc::new(__body),
                        );
                        ::core::option::Option::Some(
                            #category::#label(#(#pre_exprs,)* __scope)
                        )
                    },
                });
            },
        }
    }

    quote! {
        // The `_ => None` arm is the faithful "non-invertible op" fallback. For a
        // language whose every op-enum variant is structurally invertible (e.g. a
        // pure-arithmetic composition like MixedMath), the explicit arms cover the
        // enum exhaustively and the catch-all is unreachable — that is correct and
        // benign, so the lint is allowed on this generated reconstructor.
        #[allow(unreachable_patterns)]
        fn #fn_name(
            __d: &::std::rc::Rc<
                ::dovetail::extract::Derivation<#enum_id, ::rigail::TropicalWeight>
            >,
        ) -> ::core::option::Option<#category> {
            match &__d.op {
                #(#arms)*
                _ => ::core::option::Option::None,
            }
        }
    }
}
