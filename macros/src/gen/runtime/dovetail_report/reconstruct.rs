//! Step D of the Dovetail native-fold reduction work (Increment 3): the
//! `Derivation<L, W> → <Cat>` reconstructor — the inverse of the typed lowering
//! ([`super::typed_lowering`]).
//!
//! For each category we emit `__mettail_dovetail_build_<cat>_d(&Rc<Derivation<L,W>>) ->
//! Option<<Cat>>`, which matches the chosen op (`d.op`, a typed `L`) back to the AST
//! constructor, recursing on the already-chosen child derivations (`d.children` — the
//! funded 1-best subtrees the parent's extraction selected, so the tree is consistent).
//! Leaf payloads (literals/vars, and whole `List`/`Map`/`Bag` category values) are read back
//! losslessly. `FieldNone(i)` is the exact absence carrier for an invertible optional field;
//! `FieldOpaque`, an ill-indexed absence, and any op not rooted in the expected category yield
//! `None` — the "stuck child ⇒ no fold" case of `APPLY-NATIVE-FOLD`.
//!
//! Reconstruction is emitted for the structurally-invertible variants: `Var`, `Literal`
//! (including the collection-category `ListLit`/`MapLit`/`BagLit` whole-value leaves),
//! `Nullary`, `Regular` constructors whose every field is invertible, and (E2.1) the
//! `Collection`, `Binder`, and `MultiBinder` variants — each the exact structural inverse of
//! the corresponding [`super::typed_lowering`] arm. A `Regular` constructor with a
//! builtin, guest-body, predicate, unordered-collection, or otherwise opaque coefficient is
//! not invertible here and reconstructs to `None`, faithfully deferring any fold that would
//! read it. Optional category children, token text, and ordered sequences are exact: presence
//! uses their normal typed carrier and absence uses indexed `FieldNone(i)`.
//!
//! ★ (#101) A COLLECTION field's invertibility follows its CARRIER, not the blanket "collection
//! ⇒ not invertible" this file used to apply. An ORDERED (`Vec`) field lowers to the labelled
//! `FieldSeq<Elem>(Vec<Elem>)` leaf carrying the whole vector verbatim, so
//! [`ordered_seq_build_fn`] inverts it losslessly and the constructor around it reconstructs;
//! an unordered one (`HashBag`/`HashSet`/`HashMap`/`PathMap` as a FIELD) still lowers to
//! `FieldOpaque` and stays `None`. Keeping the blanket after the lowering changed would leave
//! this classifier asserting something false about the very lowering it inverts — the same
//! "structural rather than informational refusal" (A4) removed for token text.
//!
//! ★ (A4) FIELD-LEVEL, NOT VARIANT-LEVEL. Invertibility is decided once per field by
//! [`SemanticFieldProjection`], and the whole variant is refused only if some projection has
//! no exact inverse. The former predicate answered `bool`, so its single caller could only
//! `continue` the whole variant — which meant a constructor carrying an
//! `OpaqueLeafKind::TokenText` capture beside perfectly ordinary category children was
//! refused ENTIRELY, and the refusal was structural rather than informational: the captured
//! text was already present in the e-graph content key (see [`super::op_enum`]), it merely
//! had no label and no inverse. Token-text fields now rebuild through
//! [`token_text_reconstruct`]; guest-body fields still do not, because an `Arc<FltNode>` has
//! no lossless `Debug` inverse.
//!
//! E2.1 (AC `Collection`/`Binder`/`MultiBinder` inverses):
//! - **AC `Collection` (HashBag soup):** the lowering ([`super::typed_lowering`]
//!   `ac_bag_lowering_typed`) pushes one child PER MULTIPLICITY (`HashBag::iter_elements`
//!   flat-maps `repeat_n(elem, count)`), so the inverse reconstructs each `d.children[i]`
//!   and inserts it via the generated `Cat::insert_into_<label>` auto-flattening helper
//!   (`normalize.rs`), restoring multiplicity faithfully (`{P,P}` → 2 children → multiplicity
//!   2).
//! - **(#101) ORDERED `Collection` (a single-`Vec` constructor):** the lowering emits
//!   `ENode::new(Cat_Label, [seq_leaf])` — a constructor node over the sequence leaf, which is
//!   what restores the constructor identity a bare leaf erased — so the inverse reads child 0
//!   through [`ordered_seq_build_fn`]. `HashSet`/`HashMap`/`PathMap` whole-constructor
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

use mettail_ast::language::LanguageDef;
use mettail_ast::types::CollectionType;
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use syn::Ident;

use super::op_enum::{
    collection_pair_variant_ident, field_seq_variant_ident, field_withheld_variant_ident,
    native_pathmap_mode_variant_ident, native_pathmap_pair_variant_ident,
    op_discriminant_method_ident, op_enum_ident, op_variant_ident, pathmap_mode_variant_ident,
    pathmap_pair_variant_ident,
};
use super::semantic_adapter::{
    SemanticAdapterLayout, SemanticCollectionProjection, SemanticFieldLayout,
    SemanticFieldProjection, SemanticVariantLayout,
};
use crate::gen::native_carrier::NativeRecursiveCarrier;
use crate::gen::term_ops::subst::VariantKind;

/// The from-derivation reconstruction fn name for a category (snake-cased to match the
/// `__mettail_dovetail_add_<cat>` lowering convention and satisfy `non_snake_case`).
pub(crate) fn build_fn(category: &Ident) -> Ident {
    format_ident!("__mettail_dovetail_build_{}_d", super::to_snake(&category.to_string()))
}

/// The fixed name of the token-text inverse (see [`token_text_reconstruct`]). It is NOT
/// derived through [`build_fn`] because a token-text leaf has no CATEGORY to derive from —
/// `FieldInfo::category` is the placeholder ident `String` for such a field, and routing it
/// through `build_fn` would silently collide with a genuine user category named `String`.
pub(crate) fn token_text_build_fn() -> Ident {
    format_ident!("__mettail_dovetail_build_token_text_d")
}

/// (#101) The name of the ORDERED-SEQUENCE inverse for an element category:
/// `Sym` → `__mettail_dovetail_build_seq_sym_d`, returning `Option<Vec<Sym>>`.
///
/// Distinct from [`build_fn`], which returns `Option<Cat>`: a sequence leaf reconstructs a
/// `Vec<Elem>`, not an `Elem`. The `seq_` infix keeps the two namespaces apart even when a
/// language declares categories whose snake-cased names would otherwise collide.
pub(crate) fn ordered_seq_build_fn(element_cat: &Ident) -> Ident {
    format_ident!("__mettail_dovetail_build_seq_{}_d", super::to_snake(&element_cat.to_string()))
}

/// The per-field child expression for a reconstruction arm: the `i`-th derivation child
/// rebuilt at the type the constructor's field expects.
///
/// ⚠ The two arms differ in WRAPPING, and the difference is load-bearing: a category child is
/// stored `Arc<Cat>` (`term_ops/subst.rs`'s field-type derivation), a token-text leaf is stored
/// as a BARE `String` (`OpaqueLeafKind::field_type`). Wrapping the latter would not type-check
/// — which is the desired property: the shapes are checked by the compiler, not by a comment.
///
/// A non-invertible projection emits a compile-time diagnostic; production
/// callers admit only variants for which the shared layout proves every field
/// invertible.
#[cfg(test)]
fn reconstruct_child_expr(enum_id: &Ident, layout: &SemanticFieldLayout) -> TokenStream {
    let i = layout.index();
    let field = layout.field();
    match layout.projection() {
        SemanticFieldProjection::Child => {
            let child_build = build_fn(&field.category);
            quote! {
                ::std::sync::Arc::new(#child_build(__d.children.get(#i)?)?)
            }
        },
        SemanticFieldProjection::TokenText => {
            let text_build = token_text_build_fn();
            quote! {
                #text_build(__d.children.get(#i)?)?
            }
        },
        // (#101) A `Vec<Elem>` field: UNWRAPPED, like the token-text arm — the constructor
        // stores the bare `Vec`, not an `Arc<Vec>`, so wrapping would not type-check. The
        // shapes are checked by the compiler, not by a comment.
        SemanticFieldProjection::OrderedSequence => {
            let seq_build = ordered_seq_build_fn(&field.category);
            quote! {
                #seq_build(__d.children.get(#i)?)?
            }
        },
        // ★★★ (#195) A SEVERED position: the leaf payload IS the `Arc<Cat>` the
        // constructor stores, so the inverse is a `clone()` with NO wrapper and NO recursion.
        SemanticFieldProjection::Withheld => {
            let withheld_build = withheld_build_fn(&field.category);
            quote! {
                #withheld_build(__d.children.get(#i)?)?
            }
        },
        // ★ #141 G9. The gate is `all_fields_invertible`, checked by the CALLER;
        // this function has no way to know it ran. It returns the child expression's
        // tokens, so the refusal simply IS the expression.
        SemanticFieldProjection::OptionalChild => {
            let child_build = build_fn(&field.category);
            let absent_index = i as u32;
            quote! {
                match __d.children.get(#i)? {
                    __child if matches!(
                        &__child.op,
                        #enum_id::FieldNone(__index) if *__index == #absent_index
                    ) && __child.children.is_empty() => None,
                    __child if matches!(&__child.op, #enum_id::FieldNone(_)) =>
                        return ::core::option::Option::None,
                    _ => Some(::std::sync::Arc::new(
                        #child_build(__d.children.get(#i)?)?
                    )),
                }
            }
        },
        SemanticFieldProjection::OptionalTokenText => {
            let text_build = token_text_build_fn();
            let absent_index = i as u32;
            quote! {
                match __d.children.get(#i)? {
                    __child if matches!(
                        &__child.op,
                        #enum_id::FieldNone(__index) if *__index == #absent_index
                    ) && __child.children.is_empty() => None,
                    __child if matches!(&__child.op, #enum_id::FieldNone(_)) =>
                        return ::core::option::Option::None,
                    _ => Some(#text_build(__d.children.get(#i)?)?),
                }
            }
        },
        SemanticFieldProjection::OptionalOrderedSequence => {
            let seq_build = ordered_seq_build_fn(&field.category);
            let absent_index = i as u32;
            quote! {
                match __d.children.get(#i)? {
                    __child if matches!(
                        &__child.op,
                        #enum_id::FieldNone(__index) if *__index == #absent_index
                    ) && __child.children.is_empty() => None,
                    __child if matches!(&__child.op, #enum_id::FieldNone(_)) =>
                        return ::core::option::Option::None,
                    _ => Some(#seq_build(__d.children.get(#i)?)?),
                }
            }
        },
        SemanticFieldProjection::Opaque | SemanticFieldProjection::OptionalOpaque => {
            let message = format!(
                "mettail internal error: the Dovetail inverse reached a NON-INVERTIBLE \
                 field of category `{}`, which `all_fields_invertible` is supposed to \
                 have excluded before this emitter ran. The gate and this emitter have \
                 drifted apart. This is a macro bug, not a grammar bug — please report \
                 it.",
                field.category,
            );
            quote! { compile_error!(#message) }
        },
    }
}

/// (A4) Generate `__mettail_dovetail_build_token_text_d` — the inverse of
/// `typed_lowering::token_text_leaf_typed`.
///
/// ONE arm and a total fallback. The lowering wrote the captured text VERBATIM into
/// `FieldTokenText`, so the inverse is a `clone()`: there is no `Debug` escaping to undo and
/// therefore NO UNESCAPING PARSER anywhere — the property that makes this lossless rather than
/// merely usually-right. Every other op (including the lossy `FieldOpaque`, which a guest-body
/// or predicate field still lowers to) answers `None`, so a fold reading a non-text child
/// DEFERS instead of fabricating a string.
///
/// Emitted only when [`language_has_token_text_leaf`] holds — the same predicate that decides
/// whether the `FieldTokenText` variant exists — so this function can never reference a
/// variant the enum does not have.
pub(crate) fn token_text_reconstruct(
    language: &LanguageDef,
    layout: &SemanticAdapterLayout,
) -> TokenStream {
    if !layout.has_token_text() {
        return quote! {};
    }
    let enum_id = op_enum_ident(language);
    let fn_name = token_text_build_fn();
    quote! {
        // A language whose only token-text field sits on a variant the fold gate never
        // reaches emits this inverse without calling it; that is correct (the capability is
        // present) and must not be a warning.
        #[allow(dead_code)]
        pub(super) fn #fn_name(
            __d: &::dovetail::extract::Derivation<#enum_id, ::rigail::TropicalWeight>,
        ) -> ::core::option::Option<::std::string::String> {
            match &__d.op {
                #enum_id::FieldTokenText(__s) if __d.children.is_empty() => {
                    ::core::option::Option::Some(__s.clone())
                },
                _ => ::core::option::Option::None,
            }
        }
    }
}

/// ★ (#195) The name of the withheld-position inverse for a category:
/// `__mettail_dovetail_build_withheld_<cat>_d`.
pub(crate) fn withheld_build_fn(category: &Ident) -> Ident {
    format_ident!("__mettail_dovetail_build_withheld_{}_d", category.to_string().to_lowercase())
}

/// ★★★ (#195) Generate `__mettail_dovetail_build_withheld_<cat>_d` for each category some
/// `| S ~/> T |-` declaration severs — the inverse of
/// `typed_lowering::withheld_leaf_typed`.
///
/// ONE arm and a total fallback, per category. The lowering wrote the whole `Arc<Cat>`
/// VERBATIM into `FieldWithheld<Cat>`, so the inverse is a `clone()` (an `Arc` bump): there
/// is no `Debug` escaping to undo and therefore NO UNESCAPING PARSER anywhere — the property
/// that makes this lossless rather than merely usually-right. Every other op answers `None`,
/// so a reconstruction reading a non-withheld child at a severed position DEFERS instead of
/// fabricating a subterm.
///
/// Driven by [`WithholdingSet::earned_categories`] — the same derivation that decides which
/// `FieldWithheld*` variants the enum has and which positions the lowering severs — so these
/// functions can never reference a variant the enum does not have, nor go missing for one it
/// does. That three-reader/one-derivation discipline is lifted verbatim from `#101`'s
/// `ordered_seq_element_categories`.
pub(crate) fn withheld_reconstruct(
    language: &LanguageDef,
    layout: &SemanticAdapterLayout,
) -> Vec<TokenStream> {
    let enum_id = op_enum_ident(language);
    layout
        .withheld_categories()
        .cloned()
        .map(|category| {
            let fn_name = withheld_build_fn(&category);
            let v = field_withheld_variant_ident(&category);
            quote! {
                // A language whose severed field sits on a variant no reconstruction reads
                // emits this inverse without calling it; that is correct (the capability is
                // present) and must not be a warning.
                #[allow(dead_code)]
                pub(super) fn #fn_name(
                    __d: &::dovetail::extract::Derivation<#enum_id, ::rigail::TropicalWeight>,
                ) -> ::core::option::Option<::std::sync::Arc<#category>> {
                    match &__d.op {
                        #enum_id::#v(__value) if __d.children.is_empty() => {
                            ::core::option::Option::Some(__value.clone())
                        },
                        _ => ::core::option::Option::None,
                    }
                }
            }
        })
        .collect()
}

/// (#101) Generate `__mettail_dovetail_build_seq_<elem>_d` for each element category that occurs
/// as an ORDERED (`Vec`) collection — the inverse of `typed_lowering::ordered_seq_leaf_typed`.
///
/// ONE arm and a total fallback, per element category. The lowering wrote the whole `Vec<Elem>`
/// VERBATIM into `FieldSeq<Elem>`, so the inverse is a `clone()`: there is no `Debug` escaping
/// to undo and therefore NO UNESCAPING PARSER anywhere — the property that makes this lossless
/// rather than merely usually-right. Every other op (including the lossy `FieldOpaque`, which an
/// unordered collection still lowers to) answers `None`, so a fold reading a non-sequence child
/// DEFERS instead of fabricating a collection.
///
/// Driven by [`ordered_seq_element_categories`] — the same predicate that decides which
/// `FieldSeq*` variants the enum has — so these functions can never reference a variant the enum
/// does not have, nor go missing for one it does.
pub(crate) fn ordered_seq_reconstruct(
    language: &LanguageDef,
    layout: &SemanticAdapterLayout,
) -> Vec<TokenStream> {
    let enum_id = op_enum_ident(language);
    layout
        .ordered_sequence_elements()
        .cloned()
        .map(|element_cat| {
            let fn_name = ordered_seq_build_fn(&element_cat);
            let v = field_seq_variant_ident(&element_cat);
            quote! {
                // A language whose only `Vec` field sits on a variant no fold reads emits this
                // inverse without calling it; that is correct (the capability is present) and
                // must not be a warning.
                #[allow(dead_code)]
                pub(super) fn #fn_name(
                    __d: &::dovetail::extract::Derivation<#enum_id, ::rigail::TropicalWeight>,
                ) -> ::core::option::Option<::std::vec::Vec<#element_cat>> {
                    match &__d.op {
                        #enum_id::#v(__values) if __d.children.is_empty() => {
                            ::core::option::Option::Some(__values.clone())
                        },
                        _ => ::core::option::Option::None,
                    }
                }
            }
        })
        .collect()
}

pub(crate) fn rebuild_value_variant(category: &Ident) -> Ident {
    // Category names are user-defined, whereas the remaining rebuild-value
    // variants are generator-private sentinels.  Keep those namespaces
    // disjoint even for categories such as `Bytes`, `TokenText`, or
    // `PathMapMode`.
    format_ident!("CategoryValue{}", category)
}

fn rebuild_method_suffix(category: &Ident) -> String {
    category
        .to_string()
        .as_bytes()
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect::<Vec<_>>()
        .join("_")
}

/// Type-specific partial eliminator for one injection of the closed rebuild
/// value coproduct.  Assembly calls this method instead of re-emitting the
/// same enum match at every field occurrence.
pub(crate) fn rebuild_value_take_method(category: &Ident) -> Ident {
    format_ident!("__mettail_dovetail_take_category_{}", rebuild_method_suffix(category),)
}

fn rebuild_optional_value_take_method(category: &Ident) -> Ident {
    format_ident!("__mettail_dovetail_take_optional_category_{}", rebuild_method_suffix(category),)
}

fn rebuild_handler_name(category: &Ident) -> Ident {
    format_ident!("__mettail_dovetail_rebuild_handle_{}", super::to_snake(&category.to_string()))
}

fn rebuild_assemble_fn_name(category: &Ident) -> Ident {
    format_ident!("__mettail_dovetail_rebuild_assemble_{}", super::to_snake(&category.to_string()),)
}

/// Category-typed constructor kernel shared by normalization and the generic
/// Dovetail coproduct publisher.  The latter is only an output injection
/// wrapper around this function.
pub(crate) fn rebuild_construct_fn_name(category: &Ident) -> Ident {
    format_ident!(
        "__mettail_dovetail_rebuild_construct_{}",
        super::to_snake(&category.to_string()),
    )
}

pub(crate) fn rebuild_category_tag_const(category: &Ident) -> Ident {
    // Encode the exact UTF-8 spelling so distinct Rust identifiers cannot
    // collide after the uppercase naming convention required for constants.
    let encoded = category
        .to_string()
        .as_bytes()
        .iter()
        .map(|byte| format!("{byte:02X}"))
        .collect::<Vec<_>>()
        .join("_");
    format_ident!("__METTAIL_DOVETAIL_REBUILD_CATEGORY_{encoded}")
}

/// Stable category-local constructor tag shared by scheduling and assembly.
///
/// The tag is the position in `collect_category_variants`, the same exact
/// constructor census consumed by both sites. Refused variants retain a slot so
/// adding or removing invertibility never renumbers any later constructor.
fn rebuild_assemble_tag(layout: &SemanticVariantLayout) -> u32 {
    layout.constructor_tag()
}

fn rebuild_seq_task_variant(category: &Ident) -> Ident {
    format_ident!("BuildSeq{}", category)
}

pub(crate) fn rebuild_seq_value_variant(category: &Ident) -> Ident {
    format_ident!("Seq{}", category)
}

fn rebuild_seq_take_method(category: &Ident) -> Ident {
    format_ident!("__mettail_dovetail_take_sequence_{}", rebuild_method_suffix(category),)
}

fn rebuild_optional_seq_take_method(category: &Ident) -> Ident {
    format_ident!("__mettail_dovetail_take_optional_sequence_{}", rebuild_method_suffix(category),)
}

fn rebuild_withheld_task_variant(category: &Ident) -> Ident {
    format_ident!("BuildWithheld{}", category)
}

pub(crate) fn rebuild_withheld_value_variant(category: &Ident) -> Ident {
    format_ident!("Withheld{}", category)
}

fn rebuild_withheld_take_method(category: &Ident) -> Ident {
    format_ident!("__mettail_dovetail_take_withheld_{}", rebuild_method_suffix(category),)
}

fn layout_has_structural_pathmap(layout: &SemanticAdapterLayout) -> bool {
    layout.categories().iter().any(|category| {
        category
            .variants()
            .iter()
            .any(|variant| match variant.kind() {
                VariantKind::CollectionLiteral {
                    element_cat,
                    coll_type: CollectionType::PathMap,
                    ..
                } => layout.category(element_cat).is_some(),
                VariantKind::RecursiveNativeLiteral { .. } => true,
                _ => false,
            })
    })
}

fn recursive_native_assemble_arm(
    category: &Ident,
    label: &Ident,
    carrier: &NativeRecursiveCarrier,
    tag: u32,
) -> TokenStream {
    let key_category = carrier.key_category();
    let value_category = carrier.value_category();
    let take_key = rebuild_value_take_method(key_category);
    let take_value = rebuild_value_take_method(value_category);
    let payload = carrier.construct(&quote! { __pathmap }, &quote! { __focus });

    quote! {
        #tag => {
            if __value_count < 2usize {
                return ::core::option::Option::None;
            }
            let __first = __values.len().checked_sub(__value_count)?;
            let mut __drained = __values.drain(__first..);
            let __focus = __drained
                .next_back()?
                .__mettail_dovetail_take_bytes()?;
            let __mode = __drained
                .next()?
                .__mettail_dovetail_take_pathmap_mode()?;
            let __pathmap: ::mettail_runtime::PathMapLit<#key_category, #value_category> =
                match __mode {
                    0u8 => {
                        if __drained.next().is_some() {
                            return ::core::option::Option::None;
                        }
                        ::mettail_runtime::PathMapLit::Empty
                    },
                    1u8 => {
                        let mut __set =
                            ::mettail_runtime::HashMapLit::<#key_category, ()>::new();
                        for __value in __drained.by_ref() {
                            let __key = __value.#take_key()?;
                            if __set.insert(__key, ()).is_some() {
                                return ::core::option::Option::None;
                            }
                        }
                        ::mettail_runtime::PathMapLit::Set(__set)
                    },
                    2u8 => {
                        let mut __map = ::mettail_runtime::HashMapLit::<
                            #key_category,
                            #value_category,
                        >::new();
                        while let ::core::option::Option::Some(__key_value) = __drained.next() {
                            let __key = __key_value.#take_key()?;
                            let __value = __drained.next()?.#take_value()?;
                            if __map.insert(__key, __value).is_some() {
                                return ::core::option::Option::None;
                            }
                        }
                        ::mettail_runtime::PathMapLit::Map(__map)
                    },
                    _ => return ::core::option::Option::None,
                };
            drop(__drained);
            ::core::option::Option::Some(#category::#label(#payload))
        }
    }
}

/// One category-local assembly arm for a structural collection literal.  The
/// shared rebuild PDA has already reconstructed every element into typed
/// category values; this arm restores the exact native wrapper and rejects a
/// malformed pair width, duplicate map/set key, or invalid PathMap mode.
fn structural_collection_literal_assemble_arm(
    category: &Ident,
    label: &Ident,
    element_cat: &Ident,
    coll_type: &CollectionType,
    tag: u32,
) -> TokenStream {
    let take_element = rebuild_value_take_method(element_cat);
    let return_result = |collection: TokenStream| {
        quote! {
            ::core::option::Option::Some(#category::#label(#collection))
        }
    };

    match coll_type {
        CollectionType::Vec => {
            let finish = return_result(quote! { __collection });
            quote! {
                #tag => {
                    let __first = __values.len().checked_sub(__value_count)?;
                    let mut __collection = ::std::vec::Vec::<#element_cat>::with_capacity(
                        __value_count,
                    );
                    for __value in __values.drain(__first..) {
                        __collection.push(__value.#take_element()?);
                    }
                    #finish
                }
            }
        },
        CollectionType::HashBag => {
            let finish = return_result(quote! { __collection });
            quote! {
                #tag => {
                    let __first = __values.len().checked_sub(__value_count)?;
                    let mut __collection = ::mettail_runtime::HashBag::<#element_cat>::new();
                    for __value in __values.drain(__first..) {
                        __collection.insert(__value.#take_element()?);
                    }
                    #finish
                }
            }
        },
        CollectionType::HashSet => {
            let finish = return_result(quote! { __collection });
            quote! {
                #tag => {
                    let __first = __values.len().checked_sub(__value_count)?;
                    let mut __collection = ::mettail_runtime::HashSetLit::<#element_cat>::new();
                    for __value in __values.drain(__first..) {
                        let __element = __value.#take_element()?;
                        if !__collection.insert(__element) {
                            return ::core::option::Option::None;
                        }
                    }
                    #finish
                }
            }
        },
        CollectionType::HashMap => {
            let finish = return_result(quote! { __collection });
            quote! {
                #tag => {
                    if __value_count % 2usize != 0usize {
                        return ::core::option::Option::None;
                    }
                    let __first = __values.len().checked_sub(__value_count)?;
                    let mut __drained = __values.drain(__first..);
                    let mut __collection =
                        ::mettail_runtime::HashMapLit::<#element_cat, #element_cat>::new();
                    while let ::core::option::Option::Some(__key_value) = __drained.next() {
                        let __key = __key_value.#take_element()?;
                        let __value = __drained.next()?.#take_element()?;
                        if __collection.insert(__key, __value).is_some() {
                            return ::core::option::Option::None;
                        }
                    }
                    drop(__drained);
                    #finish
                }
            }
        },
        CollectionType::PathMap => {
            let finish = return_result(quote! { __collection });
            quote! {
                #tag => {
                    let __first = __values.len().checked_sub(__value_count)?;
                    let mut __drained = __values.drain(__first..);
                    let __mode = __drained
                        .next()?
                        .__mettail_dovetail_take_pathmap_mode()?;
                    let mut __collection = match __mode {
                        0u8 => {
                            if __drained.next().is_some() {
                                return ::core::option::Option::None;
                            }
                            ::mettail_runtime::PathMapLit::Empty
                        },
                        1u8 => {
                            let mut __entries =
                                ::mettail_runtime::HashMapLit::<#element_cat, ()>::new();
                            for __value in __drained.by_ref() {
                                let __key = __value.#take_element()?;
                                if __entries.insert(__key, ()).is_some() {
                                    return ::core::option::Option::None;
                                }
                            }
                            ::mettail_runtime::PathMapLit::Set(__entries)
                        },
                        2u8 => {
                            let __remaining = __value_count.checked_sub(1usize)?;
                            if __remaining % 2usize != 0usize {
                                return ::core::option::Option::None;
                            }
                            let mut __entries = ::mettail_runtime::HashMapLit::<
                                #element_cat,
                                #element_cat,
                            >::new();
                            while let ::core::option::Option::Some(__key_value) =
                                __drained.next()
                            {
                                let __key = __key_value.#take_element()?;
                                let __value = __drained.next()?.#take_element()?;
                                if __entries.insert(__key, __value).is_some() {
                                    return ::core::option::Option::None;
                                }
                            }
                            ::mettail_runtime::PathMapLit::Map(__entries)
                        },
                        _ => return ::core::option::Option::None,
                    };
                    drop(__drained);
                    #finish
                }
            }
        },
    }
}

/// Schedule one derivation child in the shared reconstruction PDA. Every task carries a raw
/// pointer into the root-owned `Rc<Derivation>` tree and is consumed synchronously.
fn reconstruct_child_task(enum_id: &Ident, layout: &SemanticFieldLayout) -> TokenStream {
    let i = layout.index();
    let field = layout.field();
    match layout.projection() {
        SemanticFieldProjection::Child => {
            let category_tag = rebuild_category_tag_const(&field.category);
            quote! {
                __tasks.push(__MettailDovetailRebuildTask::Visit {
                    category: #category_tag,
                    node: __d.children[#i].as_ref() as *const _,
                });
            }
        },
        SemanticFieldProjection::TokenText => quote! {
            __tasks.push(__MettailDovetailRebuildTask::BuildTokenText(
                __d.children[#i].as_ref() as *const _,
            ));
        },
        SemanticFieldProjection::OrderedSequence => {
            let task = rebuild_seq_task_variant(&field.category);
            quote! {
                __tasks.push(__MettailDovetailRebuildTask::#task(
                    __d.children[#i].as_ref() as *const _,
                ));
            }
        },
        SemanticFieldProjection::Withheld => {
            let task = rebuild_withheld_task_variant(&field.category);
            quote! {
                __tasks.push(__MettailDovetailRebuildTask::#task(
                    __d.children[#i].as_ref() as *const _,
                ));
            }
        },
        SemanticFieldProjection::OptionalChild
        | SemanticFieldProjection::OptionalTokenText
        | SemanticFieldProjection::OptionalOrderedSequence => {
            let absent_index = i as u32;
            let present_task = match layout.projection() {
                SemanticFieldProjection::OptionalChild => {
                    let category_tag = rebuild_category_tag_const(&field.category);
                    quote! {
                        __tasks.push(__MettailDovetailRebuildTask::Visit {
                            category: #category_tag,
                            node: __child.as_ref() as *const _,
                        });
                    }
                },
                SemanticFieldProjection::OptionalTokenText => quote! {
                    __tasks.push(__MettailDovetailRebuildTask::BuildTokenText(
                        __child.as_ref() as *const _,
                    ));
                },
                SemanticFieldProjection::OptionalOrderedSequence => {
                    let task = rebuild_seq_task_variant(&field.category);
                    quote! {
                        __tasks.push(__MettailDovetailRebuildTask::#task(
                            __child.as_ref() as *const _,
                        ));
                    }
                },
                _ => quote! {
                    compile_error!("mettail internal error: non-optional field reached optional reconstruction scheduling");
                },
            };
            quote! {
                let __child = &__d.children[#i];
                match &__child.op {
                    #enum_id::FieldNone(__index)
                        if *__index == #absent_index && __child.children.is_empty() =>
                    {
                        __tasks.push(
                            __MettailDovetailRebuildTask::EmitFieldAbsent(#absent_index),
                        );
                    },
                    #enum_id::FieldNone(_) => return ::core::option::Option::None,
                    _ => { #present_task },
                }
            }
        },
        SemanticFieldProjection::Opaque | SemanticFieldProjection::OptionalOpaque => {
            let message = format!(
                "mettail internal error: reconstruction PDA scheduled non-invertible field `{}`",
                field.category,
            );
            quote! { compile_error!(#message); }
        },
    }
}

/// Closed generated descriptor for one fixed-position field action. Category
/// references use the same dense tag constants as `Visit`; leaf projections
/// retain their exact typed decoder task.
fn rebuild_field_action_descriptor(layout: &SemanticFieldLayout) -> TokenStream {
    let index = layout.index() as u32;
    let category = rebuild_category_tag_const(&layout.field().category);
    match layout.projection() {
        SemanticFieldProjection::Child => {
            quote! { __MettailDovetailRebuildFieldAction::Visit(#category) }
        },
        SemanticFieldProjection::TokenText => {
            quote! { __MettailDovetailRebuildFieldAction::TokenText }
        },
        SemanticFieldProjection::OrderedSequence => {
            quote! { __MettailDovetailRebuildFieldAction::OrderedSequence(#category) }
        },
        SemanticFieldProjection::Withheld => {
            quote! { __MettailDovetailRebuildFieldAction::Withheld(#category) }
        },
        SemanticFieldProjection::OptionalChild => quote! {
            __MettailDovetailRebuildFieldAction::OptionalVisit {
                category: #category,
                index: #index,
            }
        },
        SemanticFieldProjection::OptionalTokenText => quote! {
            __MettailDovetailRebuildFieldAction::OptionalTokenText(#index)
        },
        SemanticFieldProjection::OptionalOrderedSequence => quote! {
            __MettailDovetailRebuildFieldAction::OptionalOrderedSequence {
                category: #category,
                index: #index,
            }
        },
        SemanticFieldProjection::Opaque | SemanticFieldProjection::OptionalOpaque => {
            quote! { __MettailDovetailRebuildFieldAction::Refuse }
        },
    }
}

fn reconstructed_field_pop(layout: &SemanticFieldLayout) -> TokenStream {
    let field_index = layout.index() as u32;
    let field = layout.field();
    match layout.projection() {
        SemanticFieldProjection::Child => {
            let take = rebuild_value_take_method(&field.category);
            quote! {
                ::std::sync::Arc::new(__values.pop()?.#take()?)
            }
        },
        SemanticFieldProjection::TokenText => quote! {
            __values.pop()?.__mettail_dovetail_take_token_text()?
        },
        SemanticFieldProjection::OrderedSequence => {
            let take = rebuild_seq_take_method(&field.category);
            quote! {
                __values.pop()?.#take()?
            }
        },
        SemanticFieldProjection::Withheld => {
            let take = rebuild_withheld_take_method(&field.category);
            quote! {
                __values.pop()?.#take()?
            }
        },
        SemanticFieldProjection::OptionalChild => {
            let take = rebuild_optional_value_take_method(&field.category);
            quote! {
                __values.pop()?.#take(#field_index)?
            }
        },
        SemanticFieldProjection::OptionalTokenText => quote! {
            __values
                .pop()?
                .__mettail_dovetail_take_optional_token_text(#field_index)?
        },
        SemanticFieldProjection::OptionalOrderedSequence => {
            let take = rebuild_optional_seq_take_method(&field.category);
            quote! {
                __values.pop()?.#take(#field_index)?
            }
        },
        SemanticFieldProjection::Opaque | SemanticFieldProjection::OptionalOpaque => {
            let message = format!(
                "mettail internal error: reconstruction PDA assembled non-invertible field `{}`",
                field.category,
            );
            quote! { compile_error!(#message) }
        },
    }
}

/// Generate the pooled heterogeneous PDA shared by all category reconstructors in one typed
/// Dovetail assembly scope. It replaces both self-recursion and cross-category mutual recursion.
pub(crate) fn reconstruction_pda_support(
    language: &LanguageDef,
    layout: &SemanticAdapterLayout,
) -> TokenStream {
    reconstruction_pda_support_mode(language, layout, false)
}

/// Emit the source-neutral typed coproduct, exact eliminators, and category
/// assembly kernel shared by normalization and Dovetail reconstruction.
pub(crate) fn typed_assembly_support(
    language: &LanguageDef,
    layout: &SemanticAdapterLayout,
) -> TokenStream {
    reconstruction_pda_support_mode(language, layout, true)
}

fn reconstruction_pda_support_mode(
    language: &LanguageDef,
    layout: &SemanticAdapterLayout,
    shared_only: bool,
) -> TokenStream {
    let enum_id = op_enum_ident(language);
    let discriminant_method = op_discriminant_method_ident(language);

    let category_tag_consts: Vec<TokenStream> = layout
        .categories()
        .iter()
        .map(|category_layout| {
            let category = category_layout.category();
            let category_tag = rebuild_category_tag_const(category);
            let tag = category_layout.category_tag();
            quote! { const #category_tag: u32 = #tag; }
        })
        .collect();
    let category_values: Vec<TokenStream> = layout
        .categories()
        .iter()
        .map(|category_layout| {
            let category = category_layout.category();
            let value = rebuild_value_variant(category);
            quote! { #value(#category) }
        })
        .collect();
    let rejected_descriptor = quote! {
        __MettailDovetailRebuildDescriptor {
            expected_category: u32::MAX,
            constructor: u32::MAX,
            shape: __MettailDovetailRebuildShape::Refuse,
        }
    };
    let mut descriptor_entries =
        vec![rejected_descriptor; layout.sentinels().end_operator_discriminant() as usize];
    for category_layout in layout.categories() {
        let category_tag = rebuild_category_tag_const(category_layout.category());
        for variant in category_layout.variants() {
            let Some(discriminant) = variant.operator_discriminant() else {
                continue;
            };
            let constructor = variant.constructor_tag();
            let shape = match variant.kind() {
                VariantKind::Regular { fields, .. }
                    if !fields.is_empty() && variant.all_fields_invertible() =>
                {
                    let required_categories: Option<Vec<Ident>> = variant
                        .fields()
                        .iter()
                        .map(|field| match field.projection() {
                            SemanticFieldProjection::Child => Some(field.field().category.clone()),
                            _ => None,
                        })
                        .collect();
                    if let Some(required_categories) = required_categories {
                        let category_tags: Vec<Ident> = required_categories
                            .iter()
                            .map(rebuild_category_tag_const)
                            .collect();
                        let homogeneous = required_categories.first().is_some_and(|first| {
                            required_categories.iter().all(|category| category == first)
                        });
                        if homogeneous {
                            let category = &category_tags[0];
                            let arity = category_tags.len();
                            quote! {
                                __MettailDovetailRebuildShape::HomogeneousRequired {
                                    category: #category,
                                    arity: #arity,
                                }
                            }
                        } else {
                            quote! {
                                __MettailDovetailRebuildShape::Required(&[#(#category_tags),*])
                            }
                        }
                    } else {
                        let actions = variant.fields().iter().map(rebuild_field_action_descriptor);
                        quote! {
                            __MettailDovetailRebuildShape::Fixed(&[#(#actions),*])
                        }
                    }
                },
                VariantKind::Collection { element_cat, .. } => {
                    let element_category = rebuild_category_tag_const(element_cat);
                    match variant
                        .collection_projection()
                        .expect("collection variant must have a checked projection")
                    {
                        SemanticCollectionProjection::AcBag => quote! {
                            __MettailDovetailRebuildShape::AcBag(#element_category)
                        },
                        SemanticCollectionProjection::OrderedSequence => quote! {
                            __MettailDovetailRebuildShape::OrderedSequence(#element_category)
                        },
                        SemanticCollectionProjection::Opaque => {
                            quote! { __MettailDovetailRebuildShape::Refuse }
                        },
                    }
                },
                VariantKind::Binder { body_cat, .. } if variant.all_fields_invertible() => {
                    let body_category = rebuild_category_tag_const(body_cat);
                    if variant.fields().is_empty() {
                        quote! {
                            __MettailDovetailRebuildShape::Binder0 {
                                body_category: #body_category,
                                multi: false,
                            }
                        }
                    } else {
                        let actions = variant.fields().iter().map(rebuild_field_action_descriptor);
                        quote! {
                            __MettailDovetailRebuildShape::Binder {
                                fields: &[#(#actions),*],
                                body_category: #body_category,
                                multi: false,
                            }
                        }
                    }
                },
                VariantKind::MultiBinder { body_cat, .. } if variant.all_fields_invertible() => {
                    let body_category = rebuild_category_tag_const(body_cat);
                    if variant.fields().is_empty() {
                        quote! {
                            __MettailDovetailRebuildShape::Binder0 {
                                body_category: #body_category,
                                multi: true,
                            }
                        }
                    } else {
                        let actions = variant.fields().iter().map(rebuild_field_action_descriptor);
                        quote! {
                            __MettailDovetailRebuildShape::Binder {
                                fields: &[#(#actions),*],
                                body_category: #body_category,
                                multi: true,
                            }
                        }
                    }
                },
                VariantKind::Regular { .. }
                | VariantKind::Binder { .. }
                | VariantKind::MultiBinder { .. } => {
                    quote! { __MettailDovetailRebuildShape::Refuse }
                },
                VariantKind::Refused { .. } => {
                    quote! { __MettailDovetailRebuildShape::Refuse }
                },
                VariantKind::Var { .. }
                | VariantKind::Literal { .. }
                | VariantKind::CollectionLiteral { .. }
                | VariantKind::RecursiveNativeLiteral { .. }
                | VariantKind::Nullary { .. } => {
                    quote! { __MettailDovetailRebuildShape::Legacy }
                },
            };
            descriptor_entries[discriminant as usize] = quote! {
                __MettailDovetailRebuildDescriptor {
                    expected_category: #category_tag,
                    constructor: #constructor,
                    shape: #shape,
                }
            };
        }
    }
    let visit_dispatch: Vec<TokenStream> = layout
        .categories()
        .iter()
        .map(|category_layout| {
            let category = category_layout.category();
            let category_tag = rebuild_category_tag_const(category);
            let handler = rebuild_handler_name(category);
            quote! {
                #category_tag => #handler(__d, __tasks, __values),
            }
        })
        .collect();

    let token_task = quote! { BuildTokenText(*const __MettailDovetailDerivation), };
    let token_value = quote! { TokenText(::std::string::String), };
    let bytes_task = layout
        .has_byte_string()
        .then(|| quote! { EmitBytes(::std::vec::Vec<u8>), });
    let bytes_value = layout
        .has_byte_string()
        .then(|| quote! { Bytes(::std::vec::Vec<u8>), });
    let bytes_dispatch = layout.has_byte_string().then(|| {
        quote! {
            __MettailDovetailRebuildTask::EmitBytes(__bytes) => {
                __values.push(__MettailDovetailRebuildValue::Bytes(__bytes));
            }
        }
    });
    let absent_value = quote! { FieldAbsent(u32), };
    let absent_task = quote! { EmitFieldAbsent(u32), };
    let absent_dispatch = quote! {
        __MettailDovetailRebuildTask::EmitFieldAbsent(__index) => {
            __values.push(__MettailDovetailRebuildValue::FieldAbsent(__index));
        }
    };
    let has_pathmap = layout_has_structural_pathmap(layout);
    let pathmap_mode_task = has_pathmap.then(|| quote! { EmitPathMapMode(u8), });
    let pathmap_mode_value = has_pathmap.then(|| quote! { PathMapMode(u8), });
    let pathmap_mode_dispatch = has_pathmap.then(|| {
        quote! {
            __MettailDovetailRebuildTask::EmitPathMapMode(__mode) => {
                __values.push(__MettailDovetailRebuildValue::PathMapMode(__mode));
            }
        }
    });
    let token_dispatch = if layout.has_token_text() {
        let build = token_text_build_fn();
        quote! {
            __MettailDovetailRebuildTask::BuildTokenText(__ptr) => {
                let __value = #build(unsafe { &*__ptr })?;
                __values.push(__MettailDovetailRebuildValue::TokenText(__value));
            }
        }
    } else {
        quote! {
            __MettailDovetailRebuildTask::BuildTokenText(_) => {
                return ::core::option::Option::None;
            }
        }
    };

    let seq_tasks: Vec<TokenStream> = layout
        .ordered_sequence_elements()
        .map(|category| {
            let task = rebuild_seq_task_variant(category);
            quote! { #task(*const __MettailDovetailDerivation) }
        })
        .collect();
    let seq_values: Vec<TokenStream> = layout
        .ordered_sequence_elements()
        .map(|category| {
            let value = rebuild_seq_value_variant(category);
            quote! { #value(::std::vec::Vec<#category>) }
        })
        .collect();
    let seq_dispatch: Vec<TokenStream> = layout
        .ordered_sequence_elements()
        .map(|category| {
            let task = rebuild_seq_task_variant(category);
            let value = rebuild_seq_value_variant(category);
            let build = ordered_seq_build_fn(category);
            quote! {
                __MettailDovetailRebuildTask::#task(__ptr) => {
                    let __value = #build(unsafe { &*__ptr })?;
                    __values.push(__MettailDovetailRebuildValue::#value(__value));
                }
            }
        })
        .collect();
    let seq_schedule: Vec<TokenStream> = layout
        .ordered_sequence_elements()
        .map(|category| {
            let category_tag = rebuild_category_tag_const(category);
            let task = rebuild_seq_task_variant(category);
            quote! {
                #category_tag => {
                    __tasks.push(__MettailDovetailRebuildTask::#task(__node));
                    ::core::option::Option::Some(())
                },
            }
        })
        .collect();

    let withheld_tasks: Vec<TokenStream> = layout
        .withheld_categories()
        .map(|category| {
            let task = rebuild_withheld_task_variant(category);
            quote! { #task(*const __MettailDovetailDerivation) }
        })
        .collect();
    let withheld_values: Vec<TokenStream> = layout
        .withheld_categories()
        .map(|category| {
            let value = rebuild_withheld_value_variant(category);
            quote! { #value(::std::sync::Arc<#category>) }
        })
        .collect();
    let withheld_dispatch: Vec<TokenStream> = layout
        .withheld_categories()
        .map(|category| {
            let task = rebuild_withheld_task_variant(category);
            let value = rebuild_withheld_value_variant(category);
            let build = withheld_build_fn(category);
            quote! {
                __MettailDovetailRebuildTask::#task(__ptr) => {
                    let __value = #build(unsafe { &*__ptr })?;
                    __values.push(__MettailDovetailRebuildValue::#value(__value));
                }
            }
        })
        .collect();
    let withheld_schedule: Vec<TokenStream> = layout
        .withheld_categories()
        .map(|category| {
            let category_tag = rebuild_category_tag_const(category);
            let task = rebuild_withheld_task_variant(category);
            quote! {
                #category_tag => {
                    __tasks.push(__MettailDovetailRebuildTask::#task(__node));
                    ::core::option::Option::Some(())
                },
            }
        })
        .collect();

    // The rebuild value is a closed typed coproduct.  Emit one partial
    // eliminator per injection and let every assembly site call it.  This is
    // the concrete instance of TypedCoproductEliminators.shared_project: a
    // wrong injection or absence index fails closed without changing the
    // value stack, while the return type remains statically tied to the tag.
    let uses_projection = |category: &Ident, projection: SemanticFieldProjection| {
        layout.categories().iter().any(|category_layout| {
            category_layout.variants().iter().any(|variant| {
                variant.fields().iter().any(|field| {
                    &field.field().category == category && field.projection() == projection
                })
            })
        })
    };
    let uses_any_projection = |projection: SemanticFieldProjection| {
        layout.categories().iter().any(|category_layout| {
            category_layout.variants().iter().any(|variant| {
                variant
                    .fields()
                    .iter()
                    .any(|field| field.projection() == projection)
            })
        })
    };
    let category_eliminators: Vec<TokenStream> = layout
        .categories()
        .iter()
        .map(|category_layout| {
            let category = category_layout.category();
            let value = rebuild_value_variant(category);
            let take = rebuild_value_take_method(category);
            let optional =
                uses_projection(category, SemanticFieldProjection::OptionalChild).then(|| {
                    let take_optional = rebuild_optional_value_take_method(category);
                    quote! {
                        fn #take_optional(
                            self,
                            __expected_index: u32,
                        ) -> ::core::option::Option<
                            ::core::option::Option<::std::sync::Arc<#category>>,
                        > {
                            match self {
                                Self::FieldAbsent(__actual_index)
                                    if __actual_index == __expected_index =>
                                {
                                    ::core::option::Option::Some(
                                        ::core::option::Option::None,
                                    )
                                },
                                Self::FieldAbsent(_) => ::core::option::Option::None,
                                __other => ::core::option::Option::Some(
                                    ::core::option::Option::Some(::std::sync::Arc::new(
                                        __other.#take()?,
                                    )),
                                ),
                            }
                        }
                    }
                });
            quote! {
                fn #take(self) -> ::core::option::Option<#category> {
                    match self {
                        Self::#value(__value) => ::core::option::Option::Some(__value),
                        _ => ::core::option::Option::None,
                    }
                }
                #optional
            }
        })
        .collect();
    let sequence_eliminators: Vec<TokenStream> = layout
        .ordered_sequence_elements()
        .map(|category| {
            let value = rebuild_seq_value_variant(category);
            let take = rebuild_seq_take_method(category);
            let optional =
                uses_projection(category, SemanticFieldProjection::OptionalOrderedSequence).then(
                    || {
                        let take_optional = rebuild_optional_seq_take_method(category);
                        quote! {
                            fn #take_optional(
                                self,
                                __expected_index: u32,
                            ) -> ::core::option::Option<
                                ::core::option::Option<::std::vec::Vec<#category>>,
                            > {
                                match self {
                                    Self::FieldAbsent(__actual_index)
                                        if __actual_index == __expected_index =>
                                    {
                                        ::core::option::Option::Some(::core::option::Option::None)
                                    },
                                    Self::FieldAbsent(_) => ::core::option::Option::None,
                                    __other => ::core::option::Option::Some(
                                        ::core::option::Option::Some(__other.#take()?),
                                    ),
                                }
                            }
                        }
                    },
                );
            quote! {
                fn #take(self) -> ::core::option::Option<::std::vec::Vec<#category>> {
                    match self {
                        Self::#value(__value) => ::core::option::Option::Some(__value),
                        _ => ::core::option::Option::None,
                    }
                }
                #optional
            }
        })
        .collect();
    let withheld_eliminators: Vec<TokenStream> = layout
        .withheld_categories()
        .map(|category| {
            let value = rebuild_withheld_value_variant(category);
            let take = rebuild_withheld_take_method(category);
            quote! {
                fn #take(
                    self,
                ) -> ::core::option::Option<::std::sync::Arc<#category>> {
                    match self {
                        Self::#value(__value) => ::core::option::Option::Some(__value),
                        _ => ::core::option::Option::None,
                    }
                }
            }
        })
        .collect();
    let token_text_eliminators = layout.has_token_text().then(|| {
        let optional = uses_any_projection(SemanticFieldProjection::OptionalTokenText).then(|| {
            quote! {
                fn __mettail_dovetail_take_optional_token_text(
                    self,
                    __expected_index: u32,
                ) -> ::core::option::Option<
                    ::core::option::Option<::std::string::String>,
                > {
                    match self {
                        Self::FieldAbsent(__actual_index)
                            if __actual_index == __expected_index =>
                        {
                            ::core::option::Option::Some(::core::option::Option::None)
                        },
                        Self::FieldAbsent(_) => ::core::option::Option::None,
                        __other => ::core::option::Option::Some(
                            ::core::option::Option::Some(
                                __other.__mettail_dovetail_take_token_text()?,
                            ),
                        ),
                    }
                }
            }
        });
        quote! {
            fn __mettail_dovetail_take_token_text(
                self,
            ) -> ::core::option::Option<::std::string::String> {
                match self {
                    Self::TokenText(__value) => ::core::option::Option::Some(__value),
                    _ => ::core::option::Option::None,
                }
            }
            #optional
        }
    });
    let bytes_eliminator = layout.has_byte_string().then(|| {
        quote! {
            fn __mettail_dovetail_take_bytes(
                self,
            ) -> ::core::option::Option<::std::vec::Vec<u8>> {
                match self {
                    Self::Bytes(__value) => ::core::option::Option::Some(__value),
                    _ => ::core::option::Option::None,
                }
            }
        }
    });
    let pathmap_mode_eliminator = has_pathmap.then(|| {
        quote! {
            fn __mettail_dovetail_take_pathmap_mode(
                self,
            ) -> ::core::option::Option<u8> {
                match self {
                    Self::PathMapMode(__value) => ::core::option::Option::Some(__value),
                    _ => ::core::option::Option::None,
                }
            }
        }
    });
    let has_single_binder = layout.categories().iter().any(|category_layout| {
        category_layout.variants().iter().any(|variant| {
            matches!(variant.kind(), VariantKind::Binder { .. }) && variant.all_fields_invertible()
        })
    });
    let has_multi_binder = layout.categories().iter().any(|category_layout| {
        category_layout.variants().iter().any(|variant| {
            matches!(variant.kind(), VariantKind::MultiBinder { .. })
                && variant.all_fields_invertible()
        })
    });
    let single_binder_eliminator = has_single_binder.then(|| {
        quote! {
            fn __mettail_dovetail_take_single_binder(
                self,
            ) -> ::core::option::Option<
                ::mettail_runtime::Binder<::std::string::String>,
            > {
                match self {
                    Self::SingleBinder(__value) => ::core::option::Option::Some(__value),
                    _ => ::core::option::Option::None,
                }
            }
        }
    });
    let multi_binders_eliminator = has_multi_binder.then(|| {
        quote! {
            fn __mettail_dovetail_take_multi_binders(
                self,
            ) -> ::core::option::Option<::std::vec::Vec<
                ::mettail_runtime::Binder<::std::string::String>,
            >> {
                match self {
                    Self::MultiBinders(__value) => ::core::option::Option::Some(__value),
                    _ => ::core::option::Option::None,
                }
            }
        }
    });

    let mut assemble_dispatch = Vec::<TokenStream>::new();
    let mut assemble_fns = Vec::<TokenStream>::new();
    for category_layout in layout.categories() {
        let category = category_layout.category();
        let category_value = rebuild_value_variant(category);
        let mut category_arms = Vec::<TokenStream>::new();
        for variant_layout in category_layout.variants() {
            match variant_layout.kind().clone() {
                VariantKind::CollectionLiteral { label, element_cat, coll_type }
                    if layout.category(&element_cat).is_some() =>
                {
                    let tag = rebuild_assemble_tag(variant_layout);
                    category_arms.push(structural_collection_literal_assemble_arm(
                        category,
                        &label,
                        &element_cat,
                        &coll_type,
                        tag,
                    ));
                },
                VariantKind::RecursiveNativeLiteral { label, carrier } => {
                    let tag = rebuild_assemble_tag(variant_layout);
                    category_arms
                        .push(recursive_native_assemble_arm(category, &label, &carrier, tag));
                },
                VariantKind::Regular { label, fields }
                    if !fields.is_empty() && variant_layout.all_fields_invertible() =>
                {
                    debug_assert_eq!(fields.len(), variant_layout.fields().len());
                    let tag = rebuild_assemble_tag(variant_layout);
                    let pops: Vec<TokenStream> = fields
                        .iter()
                        .enumerate()
                        .rev()
                        .map(|(i, _field)| {
                            let var = format_ident!("__field_{i}");
                            let pop = reconstructed_field_pop(&variant_layout.fields()[i]);
                            quote! { let #var = #pop; }
                        })
                        .collect();
                    let vars: Vec<Ident> = (0..fields.len())
                        .map(|i| format_ident!("__field_{i}"))
                        .collect();
                    category_arms.push(quote! {
                        #tag => {
                            #(#pops)*
                            ::core::option::Option::Some(
                                #category::#label(#(#vars),*)
                            )
                        }
                    });
                },
                VariantKind::Collection { label, element_cat, .. } => {
                    let tag = rebuild_assemble_tag(variant_layout);
                    match variant_layout
                        .collection_projection()
                        .expect("collection variant must have a checked collection projection")
                    {
                        SemanticCollectionProjection::AcBag => {
                            let take_element = rebuild_value_take_method(&element_cat);
                            let helper =
                                format_ident!("insert_into_{}", label.to_string().to_lowercase());
                            category_arms.push(quote! {
                                #tag => {
                                    let __first = __values.len().checked_sub(__value_count)?;
                                    let mut __bag = ::mettail_runtime::HashBag::<#element_cat>::new();
                                    for __value in __values.drain(__first..) {
                                        let __element = __value.#take_element()?;
                                        #category::#helper(&mut __bag, __element);
                                    }
                                    ::core::option::Option::Some(
                                        #category::#label(__bag)
                                    )
                                }
                            });
                        },
                        SemanticCollectionProjection::OrderedSequence => {
                            let take_sequence = rebuild_seq_take_method(&element_cat);
                            category_arms.push(quote! {
                                #tag => {
                                    let __values_field = __values.pop()?.#take_sequence()?;
                                    ::core::option::Option::Some(
                                        #category::#label(__values_field)
                                    )
                                }
                            });
                        },
                        SemanticCollectionProjection::Opaque => {},
                    }
                },
                VariantKind::Binder { label, pre_scope_fields, body_cat, .. }
                    if variant_layout.all_fields_invertible() =>
                {
                    debug_assert_eq!(pre_scope_fields.len(), variant_layout.fields().len());
                    let tag = rebuild_assemble_tag(variant_layout);
                    let pops: Vec<TokenStream> = pre_scope_fields
                        .iter()
                        .enumerate()
                        .rev()
                        .map(|(i, _field)| {
                            let var = format_ident!("__field_{i}");
                            let pop = reconstructed_field_pop(&variant_layout.fields()[i]);
                            quote! { let #var = #pop; }
                        })
                        .collect();
                    let vars: Vec<Ident> = (0..pre_scope_fields.len())
                        .map(|i| format_ident!("__field_{i}"))
                        .collect();
                    let take_body = rebuild_value_take_method(&body_cat);
                    category_arms.push(quote! {
                        #tag => {
                            #(#pops)*
                            let __binder = __values
                                .pop()?
                                .__mettail_dovetail_take_single_binder()?;
                            let __body = __values.pop()?.#take_body()?;
                            let __scope = ::mettail_runtime::Scope::from_parts_unsafe(
                                __binder,
                                ::std::sync::Arc::new(__body),
                            );
                            ::core::option::Option::Some(
                                #category::#label(#(#vars,)* __scope)
                            )
                        }
                    });
                },
                VariantKind::MultiBinder { label, pre_scope_fields, body_cat, .. }
                    if variant_layout.all_fields_invertible() =>
                {
                    debug_assert_eq!(pre_scope_fields.len(), variant_layout.fields().len());
                    let tag = rebuild_assemble_tag(variant_layout);
                    let pops: Vec<TokenStream> = pre_scope_fields
                        .iter()
                        .enumerate()
                        .rev()
                        .map(|(i, _field)| {
                            let var = format_ident!("__field_{i}");
                            let pop = reconstructed_field_pop(&variant_layout.fields()[i]);
                            quote! { let #var = #pop; }
                        })
                        .collect();
                    let vars: Vec<Ident> = (0..pre_scope_fields.len())
                        .map(|i| format_ident!("__field_{i}"))
                        .collect();
                    let take_body = rebuild_value_take_method(&body_cat);
                    category_arms.push(quote! {
                        #tag => {
                            #(#pops)*
                            let __binders = __values
                                .pop()?
                                .__mettail_dovetail_take_multi_binders()?;
                            let __body = __values.pop()?.#take_body()?;
                            let __scope = ::mettail_runtime::Scope::from_parts_unsafe(
                                __binders,
                                ::std::sync::Arc::new(__body),
                            );
                            ::core::option::Option::Some(
                                #category::#label(#(#vars,)* __scope)
                            )
                        }
                    });
                },
                _ => {},
            }
        }
        if !category_arms.is_empty() {
            let category_tag = rebuild_category_tag_const(category);
            let assemble_fn = rebuild_assemble_fn_name(category);
            let construct_fn = rebuild_construct_fn_name(category);
            assemble_fns.push(quote! {
                #[inline]
                fn #construct_fn(
                    __constructor: u32,
                    __value_base: usize,
                    __value_count: usize,
                    __values: &mut ::std::vec::Vec<__MettailDovetailRebuildValue>,
                ) -> ::core::option::Option<#category> {
                    if __values.len() != __value_base.checked_add(__value_count)? {
                        return ::core::option::Option::None;
                    }
                    match __constructor {
                        #(#category_arms)*
                        _ => ::core::option::Option::None,
                    }
                }

                #[inline]
                fn #assemble_fn(
                    __constructor: u32,
                    __value_base: usize,
                    __value_count: usize,
                    __values: &mut ::std::vec::Vec<__MettailDovetailRebuildValue>,
                ) -> ::core::option::Option<()> {
                    let __reconstructed = #construct_fn(
                        __constructor,
                        __value_base,
                        __value_count,
                        __values,
                    )?;
                    __values.push(
                        __MettailDovetailRebuildValue::#category_value(__reconstructed),
                    );
                    ::core::option::Option::Some(())
                }
            });
            assemble_dispatch.push(quote! {
                #category_tag => #assemble_fn(
                    __constructor,
                    __value_base,
                    __value_count,
                    __values,
                ),
            });
        }
    }

    let shared_support = quote! {
        #(#category_tag_consts)*

        #[derive(::core::clone::Clone)]
        #[allow(dead_code)]
        enum __MettailDovetailRebuildValue {
            #(#category_values,)*
            #token_value
            #bytes_value
            #absent_value
            #pathmap_mode_value
            #(#seq_values,)*
            #(#withheld_values,)*
            SingleBinder(::mettail_runtime::Binder<::std::string::String>),
            MultiBinders(::std::vec::Vec<
                ::mettail_runtime::Binder<::std::string::String>,
            >),
        }

        impl __MettailDovetailRebuildValue {
            #(#category_eliminators)*
            #(#sequence_eliminators)*
            #(#withheld_eliminators)*
            #token_text_eliminators
            #bytes_eliminator
            #pathmap_mode_eliminator
            #single_binder_eliminator
            #multi_binders_eliminator
        }

        #(#assemble_fns)*

        #[inline]
        fn __mettail_dovetail_rebuild_assemble(
            __category: u32,
            __constructor: u32,
            __value_base: usize,
            __value_count: usize,
            __values: &mut ::std::vec::Vec<__MettailDovetailRebuildValue>,
        ) -> ::core::option::Option<()> {
            match __category {
                #(#assemble_dispatch)*
                _ => ::core::option::Option::None,
            }
        }
    };
    if shared_only {
        return shared_support;
    }

    quote! {
        type __MettailDovetailDerivation =
            ::dovetail::extract::Derivation<#enum_id, ::rigail::TropicalWeight>;

        #[derive(::core::clone::Clone, ::core::marker::Copy)]
        enum __MettailDovetailRebuildFieldAction {
            Visit(u32),
            TokenText,
            OrderedSequence(u32),
            Withheld(u32),
            OptionalVisit { category: u32, index: u32 },
            OptionalTokenText(u32),
            OptionalOrderedSequence { category: u32, index: u32 },
            Refuse,
        }

        #[derive(::core::clone::Clone, ::core::marker::Copy)]
        enum __MettailDovetailRebuildShape {
            Legacy,
            Required(&'static [u32]),
            HomogeneousRequired { category: u32, arity: usize },
            Fixed(&'static [__MettailDovetailRebuildFieldAction]),
            AcBag(u32),
            OrderedSequence(u32),
            Binder0 {
                body_category: u32,
                multi: bool,
            },
            Binder {
                fields: &'static [__MettailDovetailRebuildFieldAction],
                body_category: u32,
                multi: bool,
            },
            Refuse,
        }

        #[derive(::core::clone::Clone, ::core::marker::Copy)]
        struct __MettailDovetailRebuildDescriptor {
            expected_category: u32,
            constructor: u32,
            shape: __MettailDovetailRebuildShape,
        }

        static __METTAIL_DOVETAIL_REBUILD_DESCRIPTORS:
            &[__MettailDovetailRebuildDescriptor] = &[#(#descriptor_entries),*];

        #[allow(dead_code)]
        enum __MettailDovetailRebuildTask {
            Visit {
                category: u32,
                node: *const __MettailDovetailDerivation,
            },
            #token_task
            #bytes_task
            #pathmap_mode_task
            #absent_task
            #(#seq_tasks,)*
            #(#withheld_tasks,)*
            MakeSingleBinder,
            MakeMultiBinders(usize),
            Assemble {
                category: u32,
                constructor: u32,
                value_base: usize,
                value_count: usize,
            },
        }

        #[inline]
        fn __mettail_dovetail_rebuild_legacy_visit(
            __category: u32,
            __d: &__MettailDovetailDerivation,
            __tasks: &mut ::std::vec::Vec<__MettailDovetailRebuildTask>,
            __values: &mut ::std::vec::Vec<__MettailDovetailRebuildValue>,
        ) -> ::core::option::Option<()> {
            match __category {
                #(#visit_dispatch)*
                _ => ::core::option::Option::None,
            }
        }

        #[inline]
        fn __mettail_dovetail_rebuild_validate_field(
            __action: __MettailDovetailRebuildFieldAction,
            __child: &__MettailDovetailDerivation,
        ) -> ::core::option::Option<()> {
            let __expected_absence = match __action {
                __MettailDovetailRebuildFieldAction::OptionalVisit { index, .. }
                | __MettailDovetailRebuildFieldAction::OptionalTokenText(index)
                | __MettailDovetailRebuildFieldAction::OptionalOrderedSequence {
                    index,
                    ..
                } => ::core::option::Option::Some(index),
                __MettailDovetailRebuildFieldAction::Refuse => {
                    return ::core::option::Option::None;
                },
                __MettailDovetailRebuildFieldAction::Visit(_)
                | __MettailDovetailRebuildFieldAction::TokenText
                | __MettailDovetailRebuildFieldAction::OrderedSequence(_)
                | __MettailDovetailRebuildFieldAction::Withheld(_) => {
                    ::core::option::Option::None
                },
            };
            if let ::core::option::Option::Some(__expected) = __expected_absence {
                match &__child.op {
                    #enum_id::FieldNone(__index)
                        if *__index == __expected && __child.children.is_empty() => {},
                    #enum_id::FieldNone(_) => return ::core::option::Option::None,
                    _ => {},
                }
            }
            ::core::option::Option::Some(())
        }

        #[inline]
        fn __mettail_dovetail_rebuild_schedule_sequence(
            __category: u32,
            __node: *const __MettailDovetailDerivation,
            __tasks: &mut ::std::vec::Vec<__MettailDovetailRebuildTask>,
        ) -> ::core::option::Option<()> {
            match __category {
                #(#seq_schedule)*
                _ => ::core::option::Option::None,
            }
        }

        #[inline]
        fn __mettail_dovetail_rebuild_schedule_withheld(
            __category: u32,
            __node: *const __MettailDovetailDerivation,
            __tasks: &mut ::std::vec::Vec<__MettailDovetailRebuildTask>,
        ) -> ::core::option::Option<()> {
            match __category {
                #(#withheld_schedule)*
                _ => ::core::option::Option::None,
            }
        }

        #[inline]
        fn __mettail_dovetail_rebuild_schedule_field(
            __action: __MettailDovetailRebuildFieldAction,
            __child: &__MettailDovetailDerivation,
            __tasks: &mut ::std::vec::Vec<__MettailDovetailRebuildTask>,
        ) -> ::core::option::Option<()> {
            let __node = __child as *const _;
            match __action {
                __MettailDovetailRebuildFieldAction::Visit(__category) => {
                    __tasks.push(__MettailDovetailRebuildTask::Visit {
                        category: __category,
                        node: __node,
                    });
                },
                __MettailDovetailRebuildFieldAction::TokenText => {
                    __tasks.push(__MettailDovetailRebuildTask::BuildTokenText(__node));
                },
                __MettailDovetailRebuildFieldAction::OrderedSequence(__category) => {
                    return __mettail_dovetail_rebuild_schedule_sequence(
                        __category,
                        __node,
                        __tasks,
                    );
                },
                __MettailDovetailRebuildFieldAction::Withheld(__category) => {
                    return __mettail_dovetail_rebuild_schedule_withheld(
                        __category,
                        __node,
                        __tasks,
                    );
                },
                __MettailDovetailRebuildFieldAction::OptionalVisit { category, index } => {
                    match &__child.op {
                        #enum_id::FieldNone(__actual) if *__actual == index => {
                            __tasks.push(__MettailDovetailRebuildTask::EmitFieldAbsent(index));
                        },
                        #enum_id::FieldNone(_) => return ::core::option::Option::None,
                        _ => __tasks.push(__MettailDovetailRebuildTask::Visit {
                            category,
                            node: __node,
                        }),
                    }
                },
                __MettailDovetailRebuildFieldAction::OptionalTokenText(index) => {
                    match &__child.op {
                        #enum_id::FieldNone(__actual) if *__actual == index => {
                            __tasks.push(__MettailDovetailRebuildTask::EmitFieldAbsent(index));
                        },
                        #enum_id::FieldNone(_) => return ::core::option::Option::None,
                        _ => __tasks.push(__MettailDovetailRebuildTask::BuildTokenText(__node)),
                    }
                },
                __MettailDovetailRebuildFieldAction::OptionalOrderedSequence {
                    category,
                    index,
                } => match &__child.op {
                    #enum_id::FieldNone(__actual) if *__actual == index => {
                        __tasks.push(__MettailDovetailRebuildTask::EmitFieldAbsent(index));
                    },
                    #enum_id::FieldNone(_) => return ::core::option::Option::None,
                    _ => return __mettail_dovetail_rebuild_schedule_sequence(
                        category,
                        __node,
                        __tasks,
                    ),
                },
                __MettailDovetailRebuildFieldAction::Refuse => {
                    return ::core::option::Option::None;
                },
            }
            ::core::option::Option::Some(())
        }

        #[inline]
        fn __mettail_dovetail_rebuild_visit(
            __category: u32,
            __d: &__MettailDovetailDerivation,
            __tasks: &mut ::std::vec::Vec<__MettailDovetailRebuildTask>,
            __values: &mut ::std::vec::Vec<__MettailDovetailRebuildValue>,
        ) -> ::core::option::Option<()> {
            let __descriptor = *__METTAIL_DOVETAIL_REBUILD_DESCRIPTORS
                .get(__d.op.#discriminant_method() as usize)?;
            if __descriptor.expected_category != __category {
                return ::core::option::Option::None;
            }
            match __descriptor.shape {
                __MettailDovetailRebuildShape::Legacy => {
                    __mettail_dovetail_rebuild_legacy_visit(
                        __category,
                        __d,
                        __tasks,
                        __values,
                    )
                },
                __MettailDovetailRebuildShape::Fixed(__fields) => {
                    if __d.children.len() != __fields.len() {
                        return ::core::option::Option::None;
                    }
                    for (__action, __child) in __fields.iter().copied().zip(&__d.children) {
                        __mettail_dovetail_rebuild_validate_field(__action, __child)?;
                    }
                    __tasks.push(__MettailDovetailRebuildTask::Assemble {
                        category: __category,
                        constructor: __descriptor.constructor,
                        value_base: __values.len(),
                        value_count: __fields.len(),
                    });
                    for (__action, __child) in
                        __fields.iter().copied().zip(&__d.children).rev()
                    {
                        __mettail_dovetail_rebuild_schedule_field(
                            __action,
                            __child,
                            __tasks,
                        )?;
                    }
                    ::core::option::Option::Some(())
                },
                __MettailDovetailRebuildShape::Required(__categories) => {
                    if __d.children.len() != __categories.len() {
                        return ::core::option::Option::None;
                    }
                    __tasks.push(__MettailDovetailRebuildTask::Assemble {
                        category: __category,
                        constructor: __descriptor.constructor,
                        value_base: __values.len(),
                        value_count: __categories.len(),
                    });
                    for (__child_category, __child) in
                        __categories.iter().copied().zip(&__d.children).rev()
                    {
                        __tasks.push(__MettailDovetailRebuildTask::Visit {
                            category: __child_category,
                            node: __child.as_ref() as *const _,
                        });
                    }
                    ::core::option::Option::Some(())
                },
                __MettailDovetailRebuildShape::HomogeneousRequired {
                    category: __child_category,
                    arity: __arity,
                } => {
                    if __d.children.len() != __arity {
                        return ::core::option::Option::None;
                    }
                    __tasks.push(__MettailDovetailRebuildTask::Assemble {
                        category: __category,
                        constructor: __descriptor.constructor,
                        value_base: __values.len(),
                        value_count: __arity,
                    });
                    for __child in __d.children.iter().rev() {
                        __tasks.push(__MettailDovetailRebuildTask::Visit {
                            category: __child_category,
                            node: __child.as_ref() as *const _,
                        });
                    }
                    ::core::option::Option::Some(())
                },
                __MettailDovetailRebuildShape::AcBag(__element_category) => {
                    __tasks.push(__MettailDovetailRebuildTask::Assemble {
                        category: __category,
                        constructor: __descriptor.constructor,
                        value_base: __values.len(),
                        value_count: __d.children.len(),
                    });
                    for __child in __d.children.iter().rev() {
                        __tasks.push(__MettailDovetailRebuildTask::Visit {
                            category: __element_category,
                            node: __child.as_ref() as *const _,
                        });
                    }
                    ::core::option::Option::Some(())
                },
                __MettailDovetailRebuildShape::OrderedSequence(__element_category) => {
                    if __d.children.len() != 1usize {
                        return ::core::option::Option::None;
                    }
                    __tasks.push(__MettailDovetailRebuildTask::Assemble {
                        category: __category,
                        constructor: __descriptor.constructor,
                        value_base: __values.len(),
                        value_count: 1usize,
                    });
                    __mettail_dovetail_rebuild_schedule_sequence(
                        __element_category,
                        __d.children[0usize].as_ref() as *const _,
                        __tasks,
                    )
                },
                __MettailDovetailRebuildShape::Binder0 {
                    body_category: __body_category,
                    multi: __multi,
                } => {
                    if __d.children.len() != 2usize {
                        return ::core::option::Option::None;
                    }
                    let __arity_node = &__d.children[0usize];
                    let __arity = match &__arity_node.op {
                        #enum_id::BinderArity(__arity) if __arity_node.children.is_empty() => {
                            *__arity as usize
                        },
                        _ => return ::core::option::Option::None,
                    };
                    if !__multi && __arity != 1usize {
                        return ::core::option::Option::None;
                    }
                    __tasks.push(__MettailDovetailRebuildTask::Assemble {
                        category: __category,
                        constructor: __descriptor.constructor,
                        value_base: __values.len(),
                        value_count: 2usize,
                    });
                    if __multi {
                        __tasks.push(
                            __MettailDovetailRebuildTask::MakeMultiBinders(__arity),
                        );
                    } else {
                        __tasks.push(__MettailDovetailRebuildTask::MakeSingleBinder);
                    }
                    __tasks.push(__MettailDovetailRebuildTask::Visit {
                        category: __body_category,
                        node: __d.children[1usize].as_ref() as *const _,
                    });
                    ::core::option::Option::Some(())
                },
                __MettailDovetailRebuildShape::Binder {
                    fields: __fields,
                    body_category: __body_category,
                    multi: __multi,
                } => {
                    let __arity_index = __fields.len();
                    let __body_index = __arity_index.checked_add(1usize)?;
                    if __d.children.len() != __body_index.checked_add(1usize)? {
                        return ::core::option::Option::None;
                    }
                    for (__action, __child) in __fields.iter().copied().zip(&__d.children) {
                        __mettail_dovetail_rebuild_validate_field(__action, __child)?;
                    }
                    let __arity_node = &__d.children[__arity_index];
                    let __arity = match &__arity_node.op {
                        #enum_id::BinderArity(__arity) if __arity_node.children.is_empty() => {
                            *__arity as usize
                        },
                        _ => return ::core::option::Option::None,
                    };
                    if !__multi && __arity != 1usize {
                        return ::core::option::Option::None;
                    }
                    __tasks.push(__MettailDovetailRebuildTask::Assemble {
                        category: __category,
                        constructor: __descriptor.constructor,
                        value_base: __values.len(),
                        value_count: __fields.len().checked_add(2usize)?,
                    });
                    for (__action, __child) in
                        __fields.iter().copied().zip(&__d.children).rev()
                    {
                        __mettail_dovetail_rebuild_schedule_field(
                            __action,
                            __child,
                            __tasks,
                        )?;
                    }
                    if __multi {
                        __tasks.push(
                            __MettailDovetailRebuildTask::MakeMultiBinders(__arity),
                        );
                    } else {
                        __tasks.push(__MettailDovetailRebuildTask::MakeSingleBinder);
                    }
                    __tasks.push(__MettailDovetailRebuildTask::Visit {
                        category: __body_category,
                        node: __d.children[__body_index].as_ref() as *const _,
                    });
                    ::core::option::Option::Some(())
                },
                __MettailDovetailRebuildShape::Refuse => ::core::option::Option::None,
            }
        }

        ::std::thread_local! {
            static __METTAIL_DOVETAIL_REBUILD_TASK_POOL:
                ::std::cell::Cell<::std::vec::Vec<__MettailDovetailRebuildTask>> =
                    const { ::std::cell::Cell::new(::std::vec::Vec::new()) };
            static __METTAIL_DOVETAIL_REBUILD_VALUE_POOL:
                ::std::cell::Cell<::std::vec::Vec<__MettailDovetailRebuildValue>> =
                    const { ::std::cell::Cell::new(::std::vec::Vec::new()) };
        }

        fn __mettail_dovetail_rebuild_run(
            __seed: __MettailDovetailRebuildTask,
        ) -> ::core::option::Option<__MettailDovetailRebuildValue> {
            let mut __tasks =
                __METTAIL_DOVETAIL_REBUILD_TASK_POOL.with(|__pool| __pool.take());
            let mut __values =
                __METTAIL_DOVETAIL_REBUILD_VALUE_POOL.with(|__pool| __pool.take());
            __tasks.clear();
            __values.clear();
            __tasks.push(__seed);

            let __result = (|| {
                while let ::core::option::Option::Some(__task) = __tasks.pop() {
                    match __task {
                        __MettailDovetailRebuildTask::Visit { category, node } => {
                            // SAFETY: pointers are into the live root-owned derivation tree and
                            // the synchronous engine drains every task before the root borrow ends.
                            __mettail_dovetail_rebuild_visit(
                                category,
                                unsafe { &*node },
                                &mut __tasks,
                                &mut __values,
                            )?;
                        },
                        #token_dispatch
                        #bytes_dispatch
                        #pathmap_mode_dispatch
                        #absent_dispatch
                        #(#seq_dispatch)*
                        #(#withheld_dispatch)*
                        __MettailDovetailRebuildTask::MakeSingleBinder => {
                            __values.push(__MettailDovetailRebuildValue::SingleBinder(
                                ::mettail_runtime::Binder(
                                    ::mettail_runtime::FreeVar::fresh_unnamed(),
                                ),
                            ));
                        },
                        __MettailDovetailRebuildTask::MakeMultiBinders(__arity) => {
                            let mut __binders = ::std::vec::Vec::with_capacity(__arity);
                            for _ in 0..__arity {
                                __binders.push(::mettail_runtime::Binder(
                                    ::mettail_runtime::FreeVar::fresh_unnamed(),
                                ));
                            }
                            __values.push(__MettailDovetailRebuildValue::MultiBinders(__binders));
                        },
                        __MettailDovetailRebuildTask::Assemble {
                            category,
                            constructor,
                            value_base,
                            value_count,
                        } => {
                            __mettail_dovetail_rebuild_assemble(
                                category,
                                constructor,
                                value_base,
                                value_count,
                                &mut __values,
                            )?;
                        },
                    }
                }
                if __values.len() != 1 {
                    return ::core::option::Option::None;
                }
                __values.pop()
            })();

            __tasks.clear();
            __values.clear();
            __METTAIL_DOVETAIL_REBUILD_TASK_POOL.with(|__pool| __pool.set(__tasks));
            __METTAIL_DOVETAIL_REBUILD_VALUE_POOL.with(|__pool| __pool.set(__values));
            __result
        }
    }
}

/// Every per-category reconstructor for `language`, PLUS the single shared token-text inverse
/// and (#101) one ordered-sequence inverse per `Vec` element category. The complete family is
/// emitted once into the language's shared typed-Dovetail PDA module; report, normal-form, and
/// step-graph entry points all call that same implementation.
pub(crate) fn all_reconstructors(
    language: &LanguageDef,
    layout: &SemanticAdapterLayout,
) -> Vec<TokenStream> {
    let seq = ordered_seq_reconstruct(language, layout);
    // ★ (#195) …and one withheld-position inverse per severed category, collected HERE for
    // exactly the reason the sequence inverses are: the three typed-path assembly sites each
    // emit into their own scope, and adding an inverse to two of the three is the drift shape
    // this file's history already contains once.
    let withheld = withheld_reconstruct(language, layout);
    let mut out = Vec::with_capacity(layout.categories().len() + 2 + seq.len() + withheld.len());
    out.push(reconstruction_pda_support(language, layout));
    out.extend(
        layout
            .categories()
            .iter()
            .map(|category| category_reconstruct(language, category.category(), layout)),
    );
    out.push(token_text_reconstruct(language, layout));
    out.extend(seq);
    out.extend(withheld);
    out
}

fn structural_collection_literal_rebuild_arm(
    enum_id: &Ident,
    category: &Ident,
    label: &Ident,
    element_cat: &Ident,
    coll_type: &CollectionType,
    variant_layout: &SemanticVariantLayout,
    layout: &SemanticAdapterLayout,
) -> TokenStream {
    let op = op_variant_ident(category, label);
    let category_tag = rebuild_category_tag_const(category);
    let tag = rebuild_assemble_tag(variant_layout);
    let element_category_tag = rebuild_category_tag_const(element_cat);

    match coll_type {
        CollectionType::Vec | CollectionType::HashBag | CollectionType::HashSet => quote! {
            &#enum_id::#op => {
                __tasks.push(__MettailDovetailRebuildTask::Assemble {
                    category: #category_tag,
                    constructor: #tag,
                    value_base: __values.len(),
                    value_count: __d.children.len(),
                });
                for __child in __d.children.iter().rev() {
                    __tasks.push(__MettailDovetailRebuildTask::Visit {
                        category: #element_category_tag,
                        node: __child.as_ref() as *const _,
                    });
                }
                ::core::option::Option::Some(())
            },
        },
        CollectionType::HashMap => {
            layout
                .sentinels()
                .collection_pair(mettail_grammar_core::CollectionKind::Map, element_cat)
                .expect("structural Map inverse must have one checked pair sentinel");
            let pair = collection_pair_variant_ident(
                mettail_grammar_core::CollectionKind::Map,
                element_cat,
            );
            quote! {
                &#enum_id::#op => {
                    let __value_count = __d.children.len().checked_mul(2usize)?;
                    for __pair in &__d.children {
                        if !matches!(&__pair.op, &#enum_id::#pair)
                            || __pair.children.len() != 2usize
                        {
                            return ::core::option::Option::None;
                        }
                    }
                    __tasks.push(__MettailDovetailRebuildTask::Assemble {
                        category: #category_tag,
                        constructor: #tag,
                        value_base: __values.len(),
                        value_count: __value_count,
                    });
                    for __pair in __d.children.iter().rev() {
                        __tasks.push(__MettailDovetailRebuildTask::Visit {
                            category: #element_category_tag,
                            node: __pair.children[1usize].as_ref() as *const _,
                        });
                        __tasks.push(__MettailDovetailRebuildTask::Visit {
                            category: #element_category_tag,
                            node: __pair.children[0usize].as_ref() as *const _,
                        });
                    }
                    ::core::option::Option::Some(())
                },
            }
        },
        CollectionType::PathMap => {
            layout
                .sentinels()
                .pathmap_mode(element_cat)
                .expect("structural PathMap inverse must have one checked mode sentinel");
            layout
                .sentinels()
                .pathmap_pair(element_cat)
                .expect("structural PathMap inverse must have one checked pair sentinel");
            let mode = pathmap_mode_variant_ident(element_cat);
            let pair = pathmap_pair_variant_ident(element_cat);
            quote! {
                &#enum_id::#op => {
                    let __mode_child = __d.children.first()?;
                    if !__mode_child.children.is_empty() {
                        return ::core::option::Option::None;
                    }
                    let __mode = match &__mode_child.op {
                        #enum_id::#mode(__mode) if *__mode <= 2u8 => *__mode,
                        _ => return ::core::option::Option::None,
                    };
                    let __entries = &__d.children[1usize..];
                    let __value_count = match __mode {
                        0u8 => {
                            if !__entries.is_empty() {
                                return ::core::option::Option::None;
                            }
                            1usize
                        },
                        1u8 => 1usize.checked_add(__entries.len())?,
                        2u8 => 1usize.checked_add(__entries.len().checked_mul(2usize)?)?,
                        _ => return ::core::option::Option::None,
                    };
                    if __mode == 2u8 {
                        for __pair in __entries {
                            if !matches!(&__pair.op, &#enum_id::#pair)
                                || __pair.children.len() != 2usize
                            {
                                return ::core::option::Option::None;
                            }
                        }
                    }
                    __tasks.push(__MettailDovetailRebuildTask::Assemble {
                        category: #category_tag,
                        constructor: #tag,
                        value_base: __values.len(),
                        value_count: __value_count,
                    });
                    match __mode {
                        0u8 => {},
                        1u8 => {
                            for __child in __entries.iter().rev() {
                                __tasks.push(__MettailDovetailRebuildTask::Visit {
                                    category: #element_category_tag,
                                    node: __child.as_ref() as *const _,
                                });
                            }
                        },
                        2u8 => {
                            for __pair in __entries.iter().rev() {
                                __tasks.push(__MettailDovetailRebuildTask::Visit {
                                    category: #element_category_tag,
                                    node: __pair.children[1usize].as_ref() as *const _,
                                });
                                __tasks.push(__MettailDovetailRebuildTask::Visit {
                                    category: #element_category_tag,
                                    node: __pair.children[0usize].as_ref() as *const _,
                                });
                            }
                        },
                        _ => return ::core::option::Option::None,
                    }
                    __tasks.push(__MettailDovetailRebuildTask::EmitPathMapMode(__mode));
                    ::core::option::Option::Some(())
                },
            }
        },
    }
}

fn recursive_native_rebuild_arm(
    enum_id: &Ident,
    category: &Ident,
    label: &Ident,
    carrier: &NativeRecursiveCarrier,
    variant_layout: &SemanticVariantLayout,
    layout: &SemanticAdapterLayout,
) -> TokenStream {
    let op = op_variant_ident(category, label);
    let category_tag = rebuild_category_tag_const(category);
    let tag = rebuild_assemble_tag(variant_layout);
    let key_category = carrier.key_category();
    let value_category = carrier.value_category();
    layout
        .sentinels()
        .native_pathmap_mode(key_category, value_category)
        .expect("recursive native inverse must have one checked mode sentinel");
    layout
        .sentinels()
        .native_pathmap_pair(key_category, value_category)
        .expect("recursive native inverse must have one checked pair sentinel");
    assert!(
        layout.has_byte_string(),
        "recursive native inverse must have one checked byte-string sentinel",
    );
    let mode = native_pathmap_mode_variant_ident(key_category, value_category);
    let pair = native_pathmap_pair_variant_ident(key_category, value_category);
    let key_category_tag = rebuild_category_tag_const(key_category);
    let value_category_tag = rebuild_category_tag_const(value_category);

    quote! {
        &#enum_id::#op => {
            if __d.children.len() < 2usize {
                return ::core::option::Option::None;
            }
            let __mode_child = __d.children.first()?;
            let __focus_child = __d.children.last()?;
            if !__mode_child.children.is_empty() || !__focus_child.children.is_empty() {
                return ::core::option::Option::None;
            }
            let __mode = match &__mode_child.op {
                #enum_id::#mode(__mode) if *__mode <= 2u8 => *__mode,
                _ => return ::core::option::Option::None,
            };
            let __focus = match &__focus_child.op {
                #enum_id::FieldBytes(__bytes) => __bytes.clone(),
                _ => return ::core::option::Option::None,
            };
            let __entries = &__d.children[1usize..__d.children.len() - 1usize];
            let __value_count = match __mode {
                0u8 => {
                    if !__entries.is_empty() {
                        return ::core::option::Option::None;
                    }
                    2usize
                },
                1u8 => 2usize.checked_add(__entries.len())?,
                2u8 => 2usize.checked_add(__entries.len().checked_mul(2usize)?)?,
                _ => return ::core::option::Option::None,
            };
            if __mode == 2u8 {
                for __pair in __entries {
                    if !matches!(&__pair.op, &#enum_id::#pair)
                        || __pair.children.len() != 2usize
                    {
                        return ::core::option::Option::None;
                    }
                }
            }
            __tasks.push(__MettailDovetailRebuildTask::Assemble {
                category: #category_tag,
                constructor: #tag,
                value_base: __values.len(),
                value_count: __value_count,
            });
            __tasks.push(__MettailDovetailRebuildTask::EmitBytes(__focus));
            match __mode {
                0u8 => {},
                1u8 => {
                    for __child in __entries.iter().rev() {
                        __tasks.push(__MettailDovetailRebuildTask::Visit {
                            category: #key_category_tag,
                            node: __child.as_ref() as *const _,
                        });
                    }
                },
                2u8 => {
                    for __pair in __entries.iter().rev() {
                        __tasks.push(__MettailDovetailRebuildTask::Visit {
                            category: #value_category_tag,
                            node: __pair.children[1usize].as_ref() as *const _,
                        });
                        __tasks.push(__MettailDovetailRebuildTask::Visit {
                            category: #key_category_tag,
                            node: __pair.children[0usize].as_ref() as *const _,
                        });
                    }
                },
                _ => return ::core::option::Option::None,
            }
            __tasks.push(__MettailDovetailRebuildTask::EmitPathMapMode(__mode));
            ::core::option::Option::Some(())
        },
    }
}

/// Generate `__mettail_dovetail_build_<cat>_d`: reconstruct a `<Cat>` from a derivation tree.
pub(crate) fn category_reconstruct(
    language: &LanguageDef,
    category: &Ident,
    layout: &SemanticAdapterLayout,
) -> TokenStream {
    let enum_id = op_enum_ident(language);
    let fn_name = build_fn(category);
    let handler_name = rebuild_handler_name(category);
    let category_tag = rebuild_category_tag_const(category);
    let root_value = rebuild_value_variant(category);
    let take_root = rebuild_value_take_method(category);
    let Some(category_layout) = layout.category(category) else {
        let message = format!("semantic adapter layout is missing category `{category}`");
        return quote! { compile_error!(#message); };
    };

    let mut arms = Vec::<TokenStream>::new();
    for variant_layout in category_layout.variants() {
        // Fixed fields, direct collections, and binders are scheduled from the
        // dense descriptor table in the shared visitor. Keep this typed
        // category handler only for payload leaves, nullaries, and specialized
        // structural/native carriers whose Rust construction remains typed.
        if matches!(
            variant_layout.kind(),
            VariantKind::Regular { .. }
                | VariantKind::Collection { .. }
                | VariantKind::Binder { .. }
                | VariantKind::MultiBinder { .. }
        ) {
            continue;
        }
        match variant_layout.kind().clone() {
            VariantKind::Refused { message, .. } => {
                arms.push(quote! { compile_error!(#message); });
            },
            VariantKind::Var { label } | VariantKind::Literal { label } => {
                let op = op_variant_ident(category, &label);
                arms.push(quote! {
                    #enum_id::#op(__payload) => {
                        if !__d.children.is_empty() {
                            return ::core::option::Option::None;
                        }
                        __values.push(__MettailDovetailRebuildValue::#root_value(
                            #category::#label(__payload.clone()),
                        ));
                        ::core::option::Option::Some(())
                    },
                });
            },
            VariantKind::CollectionLiteral { label, element_cat, coll_type }
                if layout.category(&element_cat).is_some() =>
            {
                arms.push(structural_collection_literal_rebuild_arm(
                    &enum_id,
                    category,
                    &label,
                    &element_cat,
                    &coll_type,
                    variant_layout,
                    layout,
                ));
            },
            VariantKind::CollectionLiteral { label, .. } => {
                let op = op_variant_ident(category, &label);
                arms.push(quote! {
                    #enum_id::#op(__payload) => {
                        if !__d.children.is_empty() {
                            return ::core::option::Option::None;
                        }
                        __values.push(__MettailDovetailRebuildValue::#root_value(
                            #category::#label(__payload.clone()),
                        ));
                        ::core::option::Option::Some(())
                    },
                });
            },
            VariantKind::RecursiveNativeLiteral { label, carrier } => {
                arms.push(recursive_native_rebuild_arm(
                    &enum_id,
                    category,
                    &label,
                    &carrier,
                    variant_layout,
                    layout,
                ));
            },
            VariantKind::Nullary { label } => {
                let op = op_variant_ident(category, &label);
                arms.push(quote! {
                    &#enum_id::#op => {
                        if !__d.children.is_empty() {
                            return ::core::option::Option::None;
                        }
                        __values.push(__MettailDovetailRebuildValue::#root_value(
                            #category::#label,
                        ));
                        ::core::option::Option::Some(())
                    },
                });
            },
            VariantKind::Regular { label, fields }
                if !fields.is_empty() && variant_layout.all_fields_invertible() =>
            {
                debug_assert_eq!(fields.len(), variant_layout.fields().len());
                let op = op_variant_ident(category, &label);
                let assemble_tag = rebuild_assemble_tag(variant_layout);
                let child_count = fields.len();
                let child_tasks: Vec<TokenStream> = fields
                    .iter()
                    .enumerate()
                    .rev()
                    .map(|(i, _field)| {
                        reconstruct_child_task(&enum_id, &variant_layout.fields()[i])
                    })
                    .collect();
                arms.push(quote! {
                    &#enum_id::#op => {
                        if __d.children.len() != #child_count {
                            return ::core::option::Option::None;
                        }
                        __tasks.push(__MettailDovetailRebuildTask::Assemble {
                            category: #category_tag,
                            constructor: #assemble_tag,
                            value_base: __values.len(),
                            value_count: #child_count,
                        });
                        #(#child_tasks)*
                        ::core::option::Option::Some(())
                    },
                });
            },
            VariantKind::Collection { label, element_cat, .. } => {
                let op = op_variant_ident(category, &label);
                let assemble_tag = rebuild_assemble_tag(variant_layout);
                match variant_layout
                    .collection_projection()
                    .expect("collection variant must have a checked collection projection")
                {
                    SemanticCollectionProjection::AcBag => {
                        let element_category_tag = rebuild_category_tag_const(&element_cat);
                        arms.push(quote! {
                            &#enum_id::#op => {
                                __tasks.push(__MettailDovetailRebuildTask::Assemble {
                                    category: #category_tag,
                                    constructor: #assemble_tag,
                                    value_base: __values.len(),
                                    value_count: __d.children.len(),
                                });
                                let __first_child_task = __tasks.len();
                                for __child in &__d.children {
                                    __tasks.push(__MettailDovetailRebuildTask::Visit {
                                        category: #element_category_tag,
                                        node: __child.as_ref() as *const _,
                                    });
                                }
                                __tasks[__first_child_task..].reverse();
                                ::core::option::Option::Some(())
                            },
                        });
                    },
                    SemanticCollectionProjection::OrderedSequence => {
                        let seq_task = rebuild_seq_task_variant(&element_cat);
                        arms.push(quote! {
                            &#enum_id::#op => {
                                if __d.children.len() != 1usize {
                                    return ::core::option::Option::None;
                                }
                                let __child = __d.children.get(0usize)?;
                                __tasks.push(__MettailDovetailRebuildTask::Assemble {
                                    category: #category_tag,
                                    constructor: #assemble_tag,
                                    value_base: __values.len(),
                                    value_count: 1usize,
                                });
                                __tasks.push(__MettailDovetailRebuildTask::#seq_task(
                                    __child.as_ref() as *const _,
                                ));
                                ::core::option::Option::Some(())
                            },
                        });
                    },
                    SemanticCollectionProjection::Opaque => {},
                }
            },
            VariantKind::Binder { label, pre_scope_fields, body_cat, .. }
                if variant_layout.all_fields_invertible() =>
            {
                debug_assert_eq!(pre_scope_fields.len(), variant_layout.fields().len());
                let op = op_variant_ident(category, &label);
                let assemble_tag = rebuild_assemble_tag(variant_layout);
                let body_category_tag = rebuild_category_tag_const(&body_cat);
                let arity_idx = pre_scope_fields.len();
                let body_idx = arity_idx + 1;
                let pre_tasks: Vec<TokenStream> = pre_scope_fields
                    .iter()
                    .enumerate()
                    .rev()
                    .map(|(i, _field)| {
                        reconstruct_child_task(&enum_id, &variant_layout.fields()[i])
                    })
                    .collect();
                arms.push(quote! {
                    &#enum_id::#op => {
                        if __d.children.len() != #body_idx + 1usize {
                            return ::core::option::Option::None;
                        }
                        let __arity_node = __d.children.get(#arity_idx)?;
                        match &__arity_node.op {
                            #enum_id::BinderArity(1u32)
                                if __arity_node.children.is_empty() => {},
                            _ => return ::core::option::Option::None,
                        }
                        let __body = __d.children.get(#body_idx)?;
                        __tasks.push(__MettailDovetailRebuildTask::Assemble {
                            category: #category_tag,
                            constructor: #assemble_tag,
                            value_base: __values.len(),
                            value_count: #body_idx + 1usize,
                        });
                        #(#pre_tasks)*
                        __tasks.push(__MettailDovetailRebuildTask::MakeSingleBinder);
                        __tasks.push(__MettailDovetailRebuildTask::Visit {
                            category: #body_category_tag,
                            node: __body.as_ref() as *const _,
                        });
                        ::core::option::Option::Some(())
                    },
                });
            },
            VariantKind::MultiBinder { label, pre_scope_fields, body_cat, .. }
                if variant_layout.all_fields_invertible() =>
            {
                debug_assert_eq!(pre_scope_fields.len(), variant_layout.fields().len());
                let op = op_variant_ident(category, &label);
                let assemble_tag = rebuild_assemble_tag(variant_layout);
                let body_category_tag = rebuild_category_tag_const(&body_cat);
                let arity_idx = pre_scope_fields.len();
                let body_idx = arity_idx + 1;
                let pre_tasks: Vec<TokenStream> = pre_scope_fields
                    .iter()
                    .enumerate()
                    .rev()
                    .map(|(i, _field)| {
                        reconstruct_child_task(&enum_id, &variant_layout.fields()[i])
                    })
                    .collect();
                arms.push(quote! {
                    &#enum_id::#op => {
                        if __d.children.len() != #body_idx + 1usize {
                            return ::core::option::Option::None;
                        }
                        let __arity_node = __d.children.get(#arity_idx)?;
                        let __arity = match &__arity_node.op {
                            #enum_id::BinderArity(__n)
                                if __arity_node.children.is_empty() => *__n as usize,
                            _ => return ::core::option::Option::None,
                        };
                        let __body = __d.children.get(#body_idx)?;
                        __tasks.push(__MettailDovetailRebuildTask::Assemble {
                            category: #category_tag,
                            constructor: #assemble_tag,
                            value_base: __values.len(),
                            value_count: #body_idx + 1usize,
                        });
                        #(#pre_tasks)*
                        __tasks.push(__MettailDovetailRebuildTask::MakeMultiBinders(__arity));
                        __tasks.push(__MettailDovetailRebuildTask::Visit {
                            category: #body_category_tag,
                            node: __body.as_ref() as *const _,
                        });
                        ::core::option::Option::Some(())
                    },
                });
            },
            _ => {},
        }
    }

    quote! {
        fn #handler_name(
            __d: &__MettailDovetailDerivation,
            __tasks: &mut ::std::vec::Vec<__MettailDovetailRebuildTask>,
            __values: &mut ::std::vec::Vec<__MettailDovetailRebuildValue>,
        ) -> ::core::option::Option<()> {
            match &__d.op {
                #(#arms)*
                _ => ::core::option::Option::None,
            }
        }

        pub(super) fn #fn_name(
            __d: &::std::rc::Rc<__MettailDovetailDerivation>,
        ) -> ::core::option::Option<#category> {
            __mettail_dovetail_rebuild_run(
                __MettailDovetailRebuildTask::Visit {
                    category: #category_tag,
                    node: __d.as_ref() as *const _,
                },
            )?.#take_root()
        }
    }
}

/// Retained only as a bounded executable-oracle emitter for differential equivalence tests.
#[cfg(test)]
#[allow(dead_code)]
fn category_reconstruct_recursive_reference(
    language: &LanguageDef,
    category: &Ident,
) -> TokenStream {
    let enum_id = op_enum_ident(language);
    let fn_name = build_fn(category);
    let layout = SemanticAdapterLayout::derive(language)
        .expect("recursive reconstruction oracle requires a checked semantic layout");
    let category_layout = layout
        .category(category)
        .expect("recursive reconstruction oracle category must be in the semantic layout");

    let mut arms: Vec<TokenStream> = Vec::new();
    for variant_layout in category_layout.variants() {
        match variant_layout.kind().clone() {
            // ★ #141 G5 — see `VariantKind::Refused`.
            VariantKind::Refused { message, .. } => {
                arms.push(quote! { compile_error!(#message); });
            },
            VariantKind::Var { label } | VariantKind::Literal { label } => {
                let v = op_variant_ident(category, &label);
                arms.push(quote! {
                    #enum_id::#v(__p) => {
                        if !__d.children.is_empty() {
                            return ::core::option::Option::None;
                        }
                        ::core::option::Option::Some(#category::#label(__p.clone()))
                    },
                });
            },
            VariantKind::CollectionLiteral { label, element_cat, coll_type }
                if layout.category(&element_cat).is_some() =>
            {
                let v = op_variant_ident(category, &label);
                let elem_build = build_fn(&element_cat);
                let arm = match coll_type {
                    CollectionType::Vec => quote! {
                        &#enum_id::#v => {
                            let mut __collection = ::std::vec::Vec::with_capacity(
                                __d.children.len(),
                            );
                            for __child in &__d.children {
                                __collection.push(#elem_build(__child)?);
                            }
                            ::core::option::Option::Some(#category::#label(__collection))
                        },
                    },
                    CollectionType::HashBag => quote! {
                        &#enum_id::#v => {
                            let mut __collection = ::mettail_runtime::HashBag::new();
                            for __child in &__d.children {
                                __collection.insert(#elem_build(__child)?);
                            }
                            ::core::option::Option::Some(#category::#label(__collection))
                        },
                    },
                    CollectionType::HashSet => quote! {
                        &#enum_id::#v => {
                            let mut __collection = ::mettail_runtime::HashSetLit::new();
                            for __child in &__d.children {
                                if !__collection.insert(#elem_build(__child)?) {
                                    return ::core::option::Option::None;
                                }
                            }
                            ::core::option::Option::Some(#category::#label(__collection))
                        },
                    },
                    CollectionType::HashMap => {
                        let pair = collection_pair_variant_ident(
                            mettail_grammar_core::CollectionKind::Map,
                            &element_cat,
                        );
                        quote! {
                            &#enum_id::#v => {
                                let mut __collection = ::mettail_runtime::HashMapLit::new();
                                for __pair in &__d.children {
                                    if !matches!(&__pair.op, &#enum_id::#pair)
                                        || __pair.children.len() != 2usize
                                    {
                                        return ::core::option::Option::None;
                                    }
                                    let __key = #elem_build(&__pair.children[0usize])?;
                                    let __value = #elem_build(&__pair.children[1usize])?;
                                    if __collection.insert(__key, __value).is_some() {
                                        return ::core::option::Option::None;
                                    }
                                }
                                ::core::option::Option::Some(#category::#label(__collection))
                            },
                        }
                    },
                    CollectionType::PathMap => {
                        let mode = pathmap_mode_variant_ident(&element_cat);
                        let pair = pathmap_pair_variant_ident(&element_cat);
                        quote! {
                            &#enum_id::#v => {
                                let __mode_child = __d.children.first()?;
                                if !__mode_child.children.is_empty() {
                                    return ::core::option::Option::None;
                                }
                                let __mode = match &__mode_child.op {
                                    #enum_id::#mode(__mode) if *__mode <= 2u8 => *__mode,
                                    _ => return ::core::option::Option::None,
                                };
                                let __entries = &__d.children[1usize..];
                                let __collection = match __mode {
                                    0u8 if __entries.is_empty() =>
                                        ::mettail_runtime::PathMapLit::Empty,
                                    1u8 => {
                                        let mut __set = ::mettail_runtime::HashMapLit::new();
                                        for __child in __entries {
                                            if __set.insert(#elem_build(__child)?, ()).is_some() {
                                                return ::core::option::Option::None;
                                            }
                                        }
                                        ::mettail_runtime::PathMapLit::Set(__set)
                                    },
                                    2u8 => {
                                        let mut __map = ::mettail_runtime::HashMapLit::new();
                                        for __pair in __entries {
                                            if !matches!(&__pair.op, &#enum_id::#pair)
                                                || __pair.children.len() != 2usize
                                            {
                                                return ::core::option::Option::None;
                                            }
                                            let __key = #elem_build(
                                                &__pair.children[0usize],
                                            )?;
                                            let __value = #elem_build(
                                                &__pair.children[1usize],
                                            )?;
                                            if __map.insert(__key, __value).is_some() {
                                                return ::core::option::Option::None;
                                            }
                                        }
                                        ::mettail_runtime::PathMapLit::Map(__map)
                                    },
                                    _ => return ::core::option::Option::None,
                                };
                                ::core::option::Option::Some(#category::#label(__collection))
                            },
                        }
                    },
                };
                arms.push(arm);
            },
            VariantKind::CollectionLiteral { label, .. } => {
                let v = op_variant_ident(category, &label);
                arms.push(quote! {
                    #enum_id::#v(__p) => {
                        if !__d.children.is_empty() {
                            return ::core::option::Option::None;
                        }
                        ::core::option::Option::Some(#category::#label(__p.clone()))
                    },
                });
            },
            VariantKind::RecursiveNativeLiteral { label, carrier } => {
                let v = op_variant_ident(category, &label);
                let key_category = carrier.key_category();
                let value_category = carrier.value_category();
                layout
                    .sentinels()
                    .native_pathmap_mode(key_category, value_category)
                    .expect("recursive reference inverse requires a checked mode sentinel");
                layout
                    .sentinels()
                    .native_pathmap_pair(key_category, value_category)
                    .expect("recursive reference inverse requires a checked pair sentinel");
                assert!(
                    layout.has_byte_string(),
                    "recursive reference inverse requires a checked byte-string sentinel",
                );
                let mode = native_pathmap_mode_variant_ident(key_category, value_category);
                let pair = native_pathmap_pair_variant_ident(key_category, value_category);
                let key_build = build_fn(key_category);
                let value_build = build_fn(value_category);
                let payload = carrier.construct(&quote! { __pathmap }, &quote! { __focus });
                arms.push(quote! {
                    &#enum_id::#v => {
                        if __d.children.len() < 2usize {
                            return ::core::option::Option::None;
                        }
                        let __mode_child = __d.children.first()?;
                        let __focus_child = __d.children.last()?;
                        if !__mode_child.children.is_empty()
                            || !__focus_child.children.is_empty()
                        {
                            return ::core::option::Option::None;
                        }
                        let __mode = match &__mode_child.op {
                            #enum_id::#mode(__mode) if *__mode <= 2u8 => *__mode,
                            _ => return ::core::option::Option::None,
                        };
                        let __focus = match &__focus_child.op {
                            #enum_id::FieldBytes(__bytes) => __bytes.clone(),
                            _ => return ::core::option::Option::None,
                        };
                        let __entries =
                            &__d.children[1usize..__d.children.len() - 1usize];
                        let __pathmap = match __mode {
                            0u8 if __entries.is_empty() => {
                                ::mettail_runtime::PathMapLit::Empty
                            },
                            1u8 => {
                                let mut __set = ::mettail_runtime::HashMapLit::new();
                                for __child in __entries {
                                    if __set.insert(#key_build(__child)?, ()).is_some() {
                                        return ::core::option::Option::None;
                                    }
                                }
                                ::mettail_runtime::PathMapLit::Set(__set)
                            },
                            2u8 => {
                                let mut __map = ::mettail_runtime::HashMapLit::new();
                                for __pair in __entries {
                                    if !matches!(&__pair.op, &#enum_id::#pair)
                                        || __pair.children.len() != 2usize
                                    {
                                        return ::core::option::Option::None;
                                    }
                                    let __key = #key_build(&__pair.children[0usize])?;
                                    let __value = #value_build(&__pair.children[1usize])?;
                                    if __map.insert(__key, __value).is_some() {
                                        return ::core::option::Option::None;
                                    }
                                }
                                ::mettail_runtime::PathMapLit::Map(__map)
                            },
                            _ => return ::core::option::Option::None,
                        };
                        ::core::option::Option::Some(#category::#label(#payload))
                    },
                });
            },
            VariantKind::Nullary { label } => {
                let v = op_variant_ident(category, &label);
                arms.push(quote! {
                    &#enum_id::#v => {
                        if !__d.children.is_empty() {
                            return ::core::option::Option::None;
                        }
                        ::core::option::Option::Some(#category::#label)
                    },
                });
            },
            VariantKind::Regular { label, fields } => {
                if fields.is_empty() || !variant_layout.all_fields_invertible() {
                    // Not structurally invertible here — falls through to `_ => None`.
                    continue;
                }
                let v = op_variant_ident(category, &label);
                let child_exprs: Vec<TokenStream> = fields
                    .iter()
                    .enumerate()
                    .map(|(i, _field)| {
                        reconstruct_child_expr(&enum_id, &variant_layout.fields()[i])
                    })
                    .collect();
                let child_count = fields.len();
                arms.push(quote! {
                    &#enum_id::#v => {
                        if __d.children.len() != #child_count {
                            return ::core::option::Option::None;
                        }
                        ::core::option::Option::Some(
                            #category::#label(#(#child_exprs),*)
                        )
                    },
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
            VariantKind::Collection { label, element_cat, .. } => {
                let v = op_variant_ident(category, &label);
                match variant_layout
                    .collection_projection()
                    .expect("collection variant must have a checked collection projection")
                {
                    SemanticCollectionProjection::AcBag => {
                        let elem_build = build_fn(&element_cat);
                        let helper =
                            format_ident!("insert_into_{}", label.to_string().to_lowercase());
                        arms.push(quote! {
                            &#enum_id::#v => {
                                let mut __bag = ::mettail_runtime::HashBag::<#element_cat>::new();
                                for __child in &__d.children {
                                    #category::#helper(&mut __bag, #elem_build(__child)?);
                                }
                                ::core::option::Option::Some(#category::#label(__bag))
                            },
                        });
                    },
                    // (#101) The exact inverse of `typed_lowering`'s ordered `Collection` arm:
                    // that arm emits `ENode::new(Cat_Label, [seq_leaf])`, so child 0 is the
                    // sequence leaf and `build_seq_<elem>_d` reads the whole `Vec` back
                    // losslessly. Emitting it keeps the two sides symmetric — an invertible
                    // lowering with no inverse is the drift this file's history records.
                    SemanticCollectionProjection::OrderedSequence => {
                        let seq_build = ordered_seq_build_fn(&element_cat);
                        arms.push(quote! {
                            &#enum_id::#v => {
                                if __d.children.len() != 1usize {
                                    return ::core::option::Option::None;
                                }
                                let __values = #seq_build(__d.children.get(0usize)?)?;
                                ::core::option::Option::Some(#category::#label(__values))
                            },
                        });
                    },
                    // Unordered non-AC collection (`HashSet`/`HashMap`/`PathMap`): lowered as a
                    // `FieldOpaque` spine leaf, not invertible — falls through to `_ => None`.
                    SemanticCollectionProjection::Opaque => continue,
                }
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
                if !variant_layout.all_fields_invertible() {
                    // A pre-scope field is guest-body/optional/predicate/collection/builtin —
                    // not invertible. (A token-text pre-scope field IS invertible; see
                    // `ReconstructableField::TokenText`.)
                    continue;
                }
                let v = op_variant_ident(category, &label);
                let body_build = build_fn(&body_cat);
                let pre_exprs: Vec<TokenStream> = pre_scope_fields
                    .iter()
                    .enumerate()
                    .map(|(i, _field)| {
                        reconstruct_child_expr(&enum_id, &variant_layout.fields()[i])
                    })
                    .collect();
                let arity_idx = pre_scope_fields.len();
                let body_idx = pre_scope_fields.len() + 1;
                arms.push(quote! {
                    &#enum_id::#v => {
                        if __d.children.len() != #body_idx + 1usize {
                            return ::core::option::Option::None;
                        }
                        // Verify the FIX-A anonymous binder-arity marker (arity 1).
                        let __arity_node = __d.children.get(#arity_idx)?;
                        match &__arity_node.op {
                            #enum_id::BinderArity(1u32)
                                if __arity_node.children.is_empty() => {},
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
                if !variant_layout.all_fields_invertible() {
                    continue;
                }
                let v = op_variant_ident(category, &label);
                let body_build = build_fn(&body_cat);
                let pre_exprs: Vec<TokenStream> = pre_scope_fields
                    .iter()
                    .enumerate()
                    .map(|(i, _field)| {
                        reconstruct_child_expr(&enum_id, &variant_layout.fields()[i])
                    })
                    .collect();
                let arity_idx = pre_scope_fields.len();
                let body_idx = pre_scope_fields.len() + 1;
                arms.push(quote! {
                    &#enum_id::#v => {
                        if __d.children.len() != #body_idx + 1usize {
                            return ::core::option::Option::None;
                        }
                        // Read the FIX-A anonymous arity-only marker; synthesize that many fresh
                        // binders. (`BinderArity(0)` is degenerate but reconstructs faithfully.)
                        let __arity_node = __d.children.get(#arity_idx)?;
                        let __arity = match &__arity_node.op {
                            #enum_id::BinderArity(__n)
                                if __arity_node.children.is_empty() => *__n as usize,
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
        // The `_ => None` arm is the faithful "non-invertible op" fallback. The compact
        // constructor carrier keeps this syntactically reachable even when every declared
        // operator is invertible, so no diagnostic suppression is necessary.
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

#[cfg(test)]
mod factored_assembly_tests {
    use super::*;

    fn fixture() -> LanguageDef {
        syn::parse_str(
            r#"
                name: FactoredRebuild,
                types { Proc },
                terms {
                    PZero . |- "0" : Proc;
                    PDrop . value:Proc |- "*" value : Proc;
                    PMaybe . *opt(value:Proc) |- "?" *opt(value) : Proc;
                    MixedMaybe . head:Proc, *opt(tail:Proc)
                        |- "mixed" head *opt(tail) : Proc;
                    PPar . values:HashBag(Proc) |- "{" values.*sep("|") "}" : Proc;
                    PSeq . values:Vec(Proc) |- "[" values.*sep(",") "]" : Proc;
                },
                equations {},
                rewrites {},
            "#,
        )
        .expect("factored-reconstruction fixture must parse")
    }

    fn compact(tokens: TokenStream) -> String {
        tokens.to_string().split_whitespace().collect()
    }

    fn complete_support(language: &LanguageDef, layout: &SemanticAdapterLayout) -> TokenStream {
        let typed = typed_assembly_support(language, layout);
        let rebuild = reconstruction_pda_support(language, layout);
        quote! { #typed #rebuild }
    }

    #[test]
    fn category_rebuild_values_cannot_collide_with_private_sentinels() {
        for category in [
            "Bytes",
            "TokenText",
            "FieldAbsent",
            "PathMapMode",
            "SingleBinder",
            "MultiBinders",
        ] {
            let category: Ident = syn::parse_str(category).expect("identifier");
            let value = rebuild_value_variant(&category).to_string();
            assert_eq!(value, format!("CategoryValue{category}"));
        }
    }

    #[test]
    fn all_categories_share_one_tagged_visit_and_assembly_task() {
        let language = fixture();
        let layout = SemanticAdapterLayout::derive(&language).expect("semantic layout");
        let generated = compact(complete_support(&language, &layout));

        assert_eq!(
            generated
                .matches(
                    "Assemble{category:u32,constructor:u32,value_base:usize,value_count:usize,}"
                )
                .count(),
            1,
        );
        assert_eq!(
            generated
                .matches("Visit{category:u32,node:*const__MettailDovetailDerivation,}")
                .count(),
            1,
        );
        assert_eq!(
            generated
                .matches("fn__mettail_dovetail_rebuild_assemble_proc(")
                .count(),
            1,
        );
        assert_eq!(
            generated
                .matches("fn__mettail_dovetail_rebuild_assemble(")
                .count(),
            1,
        );
        assert!(!generated.contains("AssembleProc"));
        assert!(!generated.contains("VisitProc("));
        assert!(!generated.contains("rebuild_assemble_proc_p_drop"));
        assert!(generated.contains("if__values.len()!=__value_base.checked_add(__value_count)?"));
        assert!(generated.contains("FieldAbsent(u32)"));
        assert!(generated.contains("EmitFieldAbsent(u32)"));
        assert!(generated.contains(
            "EmitFieldAbsent(__index)=>{__values.push(__MettailDovetailRebuildValue::FieldAbsent(__index));}",
        ));
    }

    #[test]
    fn closed_required_and_binder0_descriptors_use_proved_fast_shapes() {
        let language: LanguageDef = syn::parse_str(
            r#"
                name: ReconstructionFastShapes,
                types { Proc Name },
                terms {
                    Zero . |- "0" : Proc;
                    Name0 . |- "n" : Name;
                    Pair . left:Proc, right:Proc |- "pair" left right : Proc;
                    Cross . name:Name, value:Proc |- "cross" name value : Proc;
                    Bind . ^x.body:[Name -> Proc] |- "bind" x "." body : Proc;
                },
                equations {},
                rewrites {},
            "#,
        )
        .expect("fast-shape fixture must parse");
        let layout = SemanticAdapterLayout::derive(&language).expect("semantic layout");
        let generated = compact(complete_support(&language, &layout));

        assert!(generated.contains(
            "HomogeneousRequired{category:__METTAIL_DOVETAIL_REBUILD_CATEGORY_50_72_6F_63,arity:2usize,}"
        ));
        assert!(generated.contains(
            "Required(&[__METTAIL_DOVETAIL_REBUILD_CATEGORY_4E_61_6D_65,__METTAIL_DOVETAIL_REBUILD_CATEGORY_50_72_6F_63])"
        ));
        assert!(generated.contains(
            "Binder0{body_category:__METTAIL_DOVETAIL_REBUILD_CATEGORY_50_72_6F_63,multi:false,}"
        ));
        assert!(generated.contains("if__d.children.len()!=__arity"));
        assert!(generated.contains("if__d.children.len()!=2usize"));
    }

    #[test]
    fn scheduler_and_dispatcher_share_exact_constructor_tags() {
        let language = fixture();
        let proc = syn::parse_str("Proc").expect("identifier must parse");
        let pdrop = syn::parse_str("PDrop").expect("identifier must parse");
        let ppar = syn::parse_str("PPar").expect("identifier must parse");
        let pseq = syn::parse_str("PSeq").expect("identifier must parse");
        let pmaybe = syn::parse_str("PMaybe").expect("identifier must parse");
        let mixed_maybe = syn::parse_str("MixedMaybe").expect("identifier must parse");
        let layout = SemanticAdapterLayout::derive(&language).expect("semantic layout");
        let proc_layout = layout.category(&proc).expect("Proc layout");
        let pdrop_tag = rebuild_assemble_tag(proc_layout.variant(&pdrop).expect("PDrop layout"));
        let ppar_tag = rebuild_assemble_tag(proc_layout.variant(&ppar).expect("PPar layout"));
        let pseq_tag = rebuild_assemble_tag(proc_layout.variant(&pseq).expect("PSeq layout"));
        let pmaybe_tag = rebuild_assemble_tag(proc_layout.variant(&pmaybe).expect("PMaybe layout"));
        let mixed_maybe_tag = rebuild_assemble_tag(
            proc_layout
                .variant(&mixed_maybe)
                .expect("MixedMaybe layout"),
        );
        assert_ne!(pdrop_tag, ppar_tag);
        assert_ne!(ppar_tag, pseq_tag);

        let support = compact(complete_support(&language, &layout));
        let handler = compact(category_reconstruct(&language, &proc, &layout));
        for tag in [pdrop_tag, ppar_tag, pseq_tag, pmaybe_tag, mixed_maybe_tag] {
            assert!(support.contains(&format!("{tag}u32=>")));
            assert!(support.contains(&format!("constructor:{tag}u32")));
            assert!(!handler.contains(&format!("constructor:{tag}u32")));
        }
        assert!(support.contains("value_count:__d.children.len()"));
        assert!(support.contains("value_count:1usize"));
        assert!(support.contains("value_base:__values.len()"));
        assert!(
            support.contains("expected_category:__METTAIL_DOVETAIL_REBUILD_CATEGORY_50_72_6F_63")
        );
        assert!(support.contains(
            "OptionalVisit{category:__METTAIL_DOVETAIL_REBUILD_CATEGORY_50_72_6F_63,index:0u32"
        ));
        assert!(support.contains(
            "OptionalVisit{category:__METTAIL_DOVETAIL_REBUILD_CATEGORY_50_72_6F_63,index:1u32"
        ));
        assert!(!handler.contains("__values.push(__MettailDovetailRebuildValue::FieldAbsent",));
        assert!(support.contains("if__d.children.len()!=__fields.len()"));
        assert!(support.contains("fn__mettail_dovetail_take_optional_category_50_72_6f_63("));
        assert!(support.contains(".__mettail_dovetail_take_optional_category_50_72_6f_63(0u32)?"));
        assert!(support.contains(".__mettail_dovetail_take_optional_category_50_72_6f_63(1u32)?"));
        assert!(
            support.contains("Self::FieldAbsent(__actual_index)if__actual_index==__expected_index")
        );
        assert!(!support.contains("match__values.pop()?"));
    }

    #[test]
    fn collection_literal_inverse_preserves_pairs_duplicates_and_pathmap_modes() {
        let language = crate::gen::collection_literal_language_for_tests();
        let layout = SemanticAdapterLayout::derive(&language).expect("semantic layout");
        let support = compact(complete_support(&language, &layout));
        assert!(support.contains("PathMapMode(u8)"));
        assert!(support.contains("EmitPathMapMode(u8)"));
        assert!(support.contains("HashSetLit::<Proc>::new()"));
        assert!(support.contains("HashMapLit::<Proc,Proc>::new()"));
        assert!(support.contains("PathMapLit::Set(__entries)"));
        assert!(support.contains("PathMapLit::Map(__entries)"));
        assert!(support.contains("if!__collection.insert(__element)"));
        assert!(support.contains("insert(__key,__value).is_some()"));

        let map: Ident = syn::parse_str("Map").expect("identifier");
        let map_handler = compact(category_reconstruct(&language, &map, &layout));
        assert!(map_handler.contains("CollectionPairMapProc"));
        assert!(map_handler.contains("__pair.children.len()!=2usize"));

        let pathmap: Ident = syn::parse_str("Pathmap").expect("identifier");
        let pathmap_handler = compact(category_reconstruct(&language, &pathmap, &layout));
        assert!(pathmap_handler.contains("PathMapModeProc(__mode)if*__mode<=2u8"));
        assert!(pathmap_handler.contains("PathMapPairProc"));
        assert!(pathmap_handler.contains("EmitPathMapMode(__mode)"));
    }
}
