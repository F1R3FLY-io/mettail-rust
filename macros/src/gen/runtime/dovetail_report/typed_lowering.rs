//! Step C of the Dovetail native-fold reduction work (Increment 2): the typed lowering
//! `__mettail_dovetail_add_<cat>(eg: &mut EGraph<L>, term: &Cat) -> EClassId`.
//!
//! This is the typed analogue of [`super::category_lowering`] (the `EGraph<String>` lowering):
//! leaf variants (`Var`/`Literal`/`Nullary`) carry their payload INLINE in the op-enum variant
//! (lossless — so reconstruction is total), and internal nodes (`Regular`/`Binder`/AC-`Collection`)
//! use the typed `<Cat>_<Label>` op identity with `EClassId` children. The String-path structure
//! is mirrored exactly (FIX-A anonymous binder-arity marker; AC bag children sorted by
//! canonical key) so the only change is `String` → typed `L`.
//!
//! Field-level non-category leaves (builtin/predicate/optional-None and non-AC or field-level
//! collections) lower to the spine sentinels `FieldOpaque`/`FieldNone`; they are spine leaves a
//! fold never reads back, so reconstruction returns `None` for them. (RhoCalc's collection
//! folds read whole `List`/`Map`/`Bag` *category* values via the `Literal` arm, and AC soup via
//! the `Collection`-variant arm — both reconstructable.)

use mettail_ast::grammar::NonTerminalKind;
use mettail_ast::language::LanguageDef;
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use syn::Ident;

use super::op_enum::{op_enum_ident, op_variant_ident};
use super::{category_lowering_fn, coll_type_is_ac_bag};
use crate::gen::term_ops::subst::{collect_category_variants, FieldInfo, VariantKind};

/// `eg.add(ENode::leaf(L::FieldOpaque(format!("{:?}", payload))))` — a lossy spine leaf for a
/// builtin/predicate/non-reconstructable field. Reconstruction maps it to `None`.
fn opaque_leaf_typed(enum_id: &Ident, payload: TokenStream) -> TokenStream {
    quote! {
        eg.add(::dovetail::egraph::ENode::leaf(
            #enum_id::FieldOpaque(format!("{:?}", #payload))
        ))
    }
}

/// `eg.add(ENode::leaf(L::FieldNone(i)))` — an absent optional field slot.
fn field_none_typed(enum_id: &Ident, field_index: usize) -> TokenStream {
    let i = field_index as u32;
    quote! {
        eg.add(::dovetail::egraph::ENode::leaf(#enum_id::FieldNone(#i)))
    }
}

/// Typed AC bag lowering: an n-ary node whose op is the constructor's typed variant and whose
/// children are the lowered bag elements (with multiplicity) SORTED by `canonical_class_key`.
fn ac_bag_lowering_typed(
    op: TokenStream,
    element_add: &Ident,
    bag_expr: TokenStream,
) -> TokenStream {
    quote! {
        {
            let __bag = #bag_expr;
            let mut __children: Vec<::dovetail::egraph::EClassId> =
                ::std::vec::Vec::with_capacity(__bag.len());
            for __elem in __bag.iter_elements() {
                __children.push(#element_add(eg, __elem));
            }
            __children.sort_by_cached_key(|__c| eg.canonical_class_key(*__c));
            eg.add(::dovetail::egraph::ENode::new(#op, __children))
        }
    }
}

/// Typed analogue of [`super::field_child_expr`]: a category field recurses; everything else
/// becomes a `FieldOpaque`/`FieldNone` spine sentinel (field-level collections included — see
/// the module doc; RhoCalc's reconstructable collections are categories, not fields).
fn field_child_expr_typed(
    enum_id: &Ident,
    field_index: usize,
    field: &FieldInfo,
    field_var: &Ident,
) -> TokenStream {
    let child_fn = category_lowering_fn(&field.category);
    let field_kind = NonTerminalKind::classify(&field.category.to_string());
    if field_kind.is_builtin() {
        return opaque_leaf_typed(enum_id, quote! { #field_var });
    }

    if field.is_optional {
        if field.is_predicate || field.is_opaque_leaf() {
            // L9-3/L9-4: an optional token-text (`Option<String>`) / guest-body
            // (`Option<Arc<FltNode>>`) capture — the present payload is an opaque
            // e-graph leaf (atomic data, never a recursible subterm), absence a
            // distinct nullary leaf. Mirrors the string-path `field_child_expr`.
            let leaf = opaque_leaf_typed(enum_id, quote! { __pred });
            let none = field_none_typed(enum_id, field_index);
            return quote! {
                match #field_var.as_ref() {
                    Some(__pred) => #leaf,
                    None => #none,
                }
            };
        }
        if field.is_collection {
            let leaf = opaque_leaf_typed(enum_id, quote! { __values });
            let none = field_none_typed(enum_id, field_index);
            return quote! {
                match #field_var.as_ref() {
                    Some(__values) => #leaf,
                    None => #none,
                }
            };
        }
        let none = field_none_typed(enum_id, field_index);
        return quote! {
            match #field_var.as_ref() {
                Some(__inner) => #child_fn(eg, __inner.as_ref()),
                None => #none,
            }
        };
    }

    if field.is_predicate || field.is_opaque_leaf() {
        // L9-3/L9-4: a token-text (`String`) / guest-body (`Arc<FltNode>`)
        // capture lowers to an opaque e-graph leaf — atomic data, never a
        // recursible category child (there is no `__mettail_dovetail_add_flt_node`
        // to call). Mirrors the string-path `field_child_expr`; branch BEFORE the
        // `child_fn` fall-through.
        return opaque_leaf_typed(enum_id, quote! { #field_var });
    }

    if field.is_collection {
        return opaque_leaf_typed(enum_id, quote! { #field_var });
    }

    quote! { #child_fn(eg, #field_var.as_ref()) }
}

fn regular_arm_typed(
    enum_id: &Ident,
    category: &Ident,
    label: &Ident,
    fields: &[FieldInfo],
) -> TokenStream {
    let variant = op_variant_ident(category, label);
    let field_vars: Vec<Ident> = (0..fields.len())
        .map(|i| format_ident!("field_{i}"))
        .collect();
    let child_exprs: Vec<TokenStream> = fields
        .iter()
        .zip(field_vars.iter())
        .enumerate()
        .map(|(i, (field, var))| field_child_expr_typed(enum_id, i, field, var))
        .collect();
    quote! {
        #category::#label(#(#field_vars),*) => {
            let __children = vec![#(#child_exprs),*];
            eg.add(::dovetail::egraph::ENode::new(#enum_id::#variant, __children))
        }
    }
}

fn binder_arm_typed(
    enum_id: &Ident,
    category: &Ident,
    label: &Ident,
    pre_scope_fields: &[FieldInfo],
    multi: bool,
) -> TokenStream {
    let variant = op_variant_ident(category, label);
    let pre_vars: Vec<Ident> = (0..pre_scope_fields.len())
        .map(|i| format_ident!("field_{i}"))
        .collect();
    let scope_var = format_ident!("scope");
    let pre_child_exprs: Vec<TokenStream> = pre_scope_fields
        .iter()
        .zip(pre_vars.iter())
        .enumerate()
        .map(|(i, (field, var))| field_child_expr_typed(enum_id, i, field, var))
        .collect();
    let body_fn = category_lowering_fn(category);
    // (FIX-A) anonymous arity-only binder marker — see `super::binder_arm`.
    let binder_child = if multi {
        quote! {
            eg.add(::dovetail::egraph::ENode::leaf(
                #enum_id::BinderArity(#scope_var.unsafe_pattern().len() as u32)
            ))
        }
    } else {
        quote! {
            eg.add(::dovetail::egraph::ENode::leaf(#enum_id::BinderArity(1u32)))
        }
    };
    quote! {
        #category::#label(#(#pre_vars,)* #scope_var) => {
            let __binder = #binder_child;
            let __body = #body_fn(eg, #scope_var.unsafe_body().as_ref());
            let __children = vec![#(#pre_child_exprs,)* __binder, __body];
            eg.add(::dovetail::egraph::ENode::new(#enum_id::#variant, __children))
        }
    }
}

/// Generate the typed per-category lowering `__mettail_dovetail_add_<cat>(eg, term) -> EClassId`
/// over `EGraph<L>` (the same fn name as the String version; only one is emitted per language).
pub(crate) fn category_lowering_typed(language: &LanguageDef, category: &Ident) -> TokenStream {
    let enum_id = op_enum_ident(language);
    let fn_name = category_lowering_fn(category);
    let arms: Vec<TokenStream> = collect_category_variants(category, language)
        .into_iter()
        .map(|variant| match variant {
            VariantKind::Var { label } | VariantKind::Literal { label } => {
                let v = op_variant_ident(category, &label);
                quote! {
                    #category::#label(value) => {
                        eg.add(::dovetail::egraph::ENode::leaf(#enum_id::#v(value.clone())))
                    }
                }
            },
            VariantKind::Nullary { label } => {
                let v = op_variant_ident(category, &label);
                quote! {
                    #category::#label => {
                        eg.add(::dovetail::egraph::ENode::leaf(#enum_id::#v))
                    }
                }
            },
            VariantKind::Regular { label, fields } => {
                regular_arm_typed(&enum_id, category, &label, &fields)
            },
            VariantKind::Collection { label, element_cat, coll_type } => {
                let v = op_variant_ident(category, &label);
                if coll_type_is_ac_bag(Some(&coll_type)) {
                    let element_add = category_lowering_fn(&element_cat);
                    let body = ac_bag_lowering_typed(
                        quote! { #enum_id::#v },
                        &element_add,
                        quote! { values },
                    );
                    quote! { #category::#label(values) => #body }
                } else {
                    let leaf = opaque_leaf_typed(&enum_id, quote! { values });
                    quote! { #category::#label(values) => #leaf }
                }
            },
            VariantKind::Binder { label, pre_scope_fields, .. } => {
                binder_arm_typed(&enum_id, category, &label, &pre_scope_fields, false)
            },
            VariantKind::MultiBinder { label, pre_scope_fields, .. } => {
                binder_arm_typed(&enum_id, category, &label, &pre_scope_fields, true)
            },
        })
        .collect();

    quote! {
        fn #fn_name(
            eg: &mut ::dovetail::egraph::EGraph<#enum_id>,
            term: &#category,
        ) -> ::dovetail::egraph::EClassId {
            match term {
                #(#arms),*
            }
        }
    }
}
