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
//! `Nullary`, and `Regular` constructors whose fields are all plain (non-optional,
//! non-collection, non-predicate) category children wrapped in `Arc`. A constructor with a
//! builtin/opaque/optional/binder field is not invertible here (its lowered child is a
//! sentinel) and reconstructs to `None`, faithfully deferring any fold that would read it.

use mettail_ast::grammar::NonTerminalKind;
use mettail_ast::language::LanguageDef;
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use syn::Ident;

use super::op_enum::{op_enum_ident, op_variant_ident};
use crate::gen::term_ops::subst::{collect_category_variants, FieldInfo, VariantKind};

/// The from-derivation reconstruction fn name for a category (snake-cased to match the
/// `__mettail_dovetail_add_<cat>` lowering convention and satisfy `non_snake_case`).
pub(crate) fn build_fn(category: &Ident) -> Ident {
    format_ident!("__mettail_dovetail_build_{}_d", super::to_snake(&category.to_string()))
}

/// Whether a field is a plain category child (recursively reconstructable): a single
/// non-optional, non-collection, non-predicate child of an object (non-builtin) category.
fn is_plain_category_field(field: &FieldInfo) -> bool {
    !field.is_optional
        && !field.is_collection
        && !field.is_predicate
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
            // Collection variants (AC soup), binders, and any other op are not reconstructed
            // here (their fold inputs come via the Literal whole-value leaves above, or they
            // are not on a fold path); they yield `None`.
            VariantKind::Collection { .. }
            | VariantKind::Binder { .. }
            | VariantKind::MultiBinder { .. } => {},
        }
    }

    quote! {
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
