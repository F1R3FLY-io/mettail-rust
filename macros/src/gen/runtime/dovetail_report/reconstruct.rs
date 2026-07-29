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
//! `Nullary`, `Regular` constructors whose every field is invertible, and (E2.1) the
//! `Collection`, `Binder`, and `MultiBinder` variants — each the exact structural inverse of
//! the corresponding [`super::typed_lowering`] arm. A `Regular` constructor with a
//! builtin/guest-body/optional/predicate field is not invertible here (its lowered child is a
//! lossy or absent sentinel) and reconstructs to `None`, faithfully deferring any fold that
//! would read it.
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
//! ★ (A4) FIELD-LEVEL, NOT VARIANT-LEVEL. Invertibility is decided per FIELD by
//! [`ReconstructableField`] and the whole variant is refused only if some field is
//! `NotInvertible`. The former predicate answered `bool`, so its single caller could only
//! `continue` the WHOLE variant — which meant a constructor carrying an
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

use mettail_ast::grammar::NonTerminalKind;
use mettail_ast::language::LanguageDef;
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use syn::Ident;

use super::op_enum::{
    field_seq_variant_ident, language_has_token_text_leaf, op_enum_ident, op_variant_ident,
    ordered_seq_element_categories,
};
use super::{collection_carrier, CollectionCarrier};
use crate::gen::term_ops::subst::{
    collect_category_variants, FieldInfo, OpaqueLeafKind, VariantKind,
};

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

/// (A4) How a constructor field participates in reconstruction. TOTAL over `FieldInfo`: every
/// field lands in exactly one arm, so a new field shape must be classified here before it can
/// silently make a variant non-invertible.
///
/// This replaces the former `is_plain_category_field` predicate, whose defect was not its
/// answer but its ARITY: it was a `bool`, so the only thing a caller could do with a
/// token-text field was refuse the WHOLE variant. That refusal was STRUCTURAL, not
/// informational — the text was already in the e-graph content key (`typed_lowering`'s
/// `FieldOpaque(format!("{:?}", text))` frames the string's own bytes, so two constructors
/// differing only in the captured name were already distinct e-classes) — it simply had no
/// inverse and no label. With three outcomes the caller can select a per-field builder
/// instead, and only a genuinely non-invertible field refuses the variant.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ReconstructableField {
    /// A plain category child: non-optional, non-collection, non-predicate, non-leaf, of an
    /// object (non-builtin) category. Rebuilt by `build_fn(cat)` and wrapped in `Arc`.
    Category,
    /// (A4) An [`OpaqueLeafKind::TokenText`] capture (`v@Tok`, `m:Ident`). Lowered to
    /// `FieldTokenText(text)` VERBATIM, so [`token_text_build_fn`] inverts it losslessly. The
    /// emitted field type is a BARE `String` (`OpaqueLeafKind::field_type`), so the rebuilt
    /// value is used UNWRAPPED — no `Arc`.
    TokenText,
    /// (#101) A NON-OPTIONAL ORDERED (`Vec`) collection field. Lowered to
    /// `FieldSeq<Elem>(values)` VERBATIM, so [`ordered_seq_build_fn`] inverts it losslessly.
    /// The emitted field type is a BARE `Vec<Elem>`, so the rebuilt value is used UNWRAPPED —
    /// no `Arc`, exactly like [`TokenText`](ReconstructableField::TokenText).
    ///
    /// ★ WHY THIS IS NOT AN EXPANSION OF SCOPE. Before #101 a `Vec` field's lowered child WAS a
    /// lossy `FieldOpaque` sentinel, so `NotInvertible` was the true answer. #101 replaces that
    /// child with a labelled leaf carrying the whole `Vec` verbatim; keeping the field
    /// `NotInvertible` would leave the classifier asserting something false about the very
    /// lowering it is the inverse of. That is precisely the defect (A4) removed for token text:
    /// "the refusal was STRUCTURAL, not informational".
    ///
    /// ⚠ ELEMENTS ARE NOT E-CLASSES. The leaf carries the collection as ONE opaque payload, so
    /// congruence closure sees nothing inside it and no element is reduced. This arm buys
    /// reconstruction, not element reduction.
    OrderedSeq,
    /// Not invertible from the derivation: its lowered child is a lossy/absent spine sentinel.
    /// Covers builtin-category fields, predicate slots, OPTIONAL fields (including optional
    /// collections), UNORDERED collections (`HashBag`/`HashSet`/`HashMap`/`PathMap` — see
    /// [`super::CollectionCarrier`]), and [`OpaqueLeafKind::GuestBody`] (an `Arc<FltNode>` has
    /// no lossless `Debug` inverse). A variant carrying one is skipped by `category_reconstruct`
    /// and falls through to `_ => None` — faithfully deferring any fold that would read it.
    NotInvertible,
}

/// Classify a field for reconstruction. Branches on the leaf FLAG before reading `category`,
/// whose value is a placeholder (`String`/`FltNode`) for leaf fields.
fn classify_reconstructable_field(
    field: &FieldInfo,
    earned_seq_elements: &[Ident],
) -> ReconstructableField {
    // ⚠ OPTIONAL FIRST, and deliberately: `field_child_expr_typed` keeps an optional collection
    // on the lossy `FieldOpaque`/`FieldNone` pair regardless of container, so an
    // `#opt(xs:Vec(T))` has no inverse even after #101. Testing `is_optional` before the
    // container is what keeps this classifier in step with that lowering.
    if field.is_optional || field.is_predicate {
        return ReconstructableField::NotInvertible;
    }
    if field.is_collection {
        // (#101) The container decides: an ORDERED `Vec` field lowers to the invertible
        // `FieldSeq<Elem>` leaf; every other container still lowers to `FieldOpaque`.
        return match collection_carrier(field.coll_type.as_ref()) {
            // ⚠ ...and only when the element category actually EARNED a `FieldSeq*` variant.
            // A `Vec` field of a generator-synthesized HOL `MApply<Domain>` form whose domain
            // occurs nowhere in a declared rule still lowers to `FieldOpaque`
            // (`op_enum::ordered_seq_element_categories` records why), so it is still not
            // invertible — and this classifier must say so rather than promise an inverse the
            // lowering did not emit.
            CollectionCarrier::OrderedSeq
                if earned_seq_elements.iter().any(|e| *e == field.category) =>
            {
                ReconstructableField::OrderedSeq
            },
            CollectionCarrier::OrderedSeq
            | CollectionCarrier::AcBag
            | CollectionCarrier::Opaque => ReconstructableField::NotInvertible,
        };
    }
    match field.opaque_leaf {
        Some(OpaqueLeafKind::TokenText) => ReconstructableField::TokenText,
        Some(OpaqueLeafKind::GuestBody) => ReconstructableField::NotInvertible,
        None if NonTerminalKind::classify(&field.category.to_string()).is_builtin() => {
            ReconstructableField::NotInvertible
        },
        None => ReconstructableField::Category,
    }
}

/// Whether every field of a variant is invertible — the admission test the `Regular` /
/// `Binder` / `MultiBinder` arms apply before emitting a reconstruction arm.
fn all_fields_invertible(fields: &[FieldInfo], earned_seq_elements: &[Ident]) -> bool {
    fields.iter().all(|f| {
        classify_reconstructable_field(f, earned_seq_elements)
            != ReconstructableField::NotInvertible
    })
}

/// The per-field child expression for a reconstruction arm: the `i`-th derivation child
/// rebuilt at the type the constructor's field expects.
///
/// ⚠ The two arms differ in WRAPPING, and the difference is load-bearing: a category child is
/// stored `Arc<Cat>` (`term_ops/subst.rs`'s field-type derivation), a token-text leaf is stored
/// as a BARE `String` (`OpaqueLeafKind::field_type`). Wrapping the latter would not type-check
/// — which is the desired property: the shapes are checked by the compiler, not by a comment.
///
/// Panics only on a `NotInvertible` field, which the callers exclude via
/// [`all_fields_invertible`] before ever reaching here.
fn reconstruct_child_expr(
    field_index: usize,
    field: &FieldInfo,
    earned_seq_elements: &[Ident],
) -> TokenStream {
    let i = field_index;
    match classify_reconstructable_field(field, earned_seq_elements) {
        ReconstructableField::Category => {
            let child_build = build_fn(&field.category);
            quote! {
                ::std::sync::Arc::new(#child_build(__d.children.get(#i)?)?)
            }
        },
        ReconstructableField::TokenText => {
            let text_build = token_text_build_fn();
            quote! {
                #text_build(__d.children.get(#i)?)?
            }
        },
        // (#101) A `Vec<Elem>` field: UNWRAPPED, like the token-text arm — the constructor
        // stores the bare `Vec`, not an `Arc<Vec>`, so wrapping would not type-check. The
        // shapes are checked by the compiler, not by a comment.
        ReconstructableField::OrderedSeq => {
            let seq_build = ordered_seq_build_fn(&field.category);
            quote! {
                #seq_build(__d.children.get(#i)?)?
            }
        },
        ReconstructableField::NotInvertible => unreachable!(
            "reconstruct_child_expr reached a NotInvertible field; callers gate on \
             all_fields_invertible first",
        ),
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
pub(crate) fn token_text_reconstruct(language: &LanguageDef) -> TokenStream {
    if !language_has_token_text_leaf(language) {
        return quote! {};
    }
    let enum_id = op_enum_ident(language);
    let fn_name = token_text_build_fn();
    quote! {
        // A language whose only token-text field sits on a variant the fold gate never
        // reaches emits this inverse without calling it; that is correct (the capability is
        // present) and must not be a warning.
        #[allow(dead_code)]
        fn #fn_name(
            __d: &::std::rc::Rc<
                ::dovetail::extract::Derivation<#enum_id, ::rigail::TropicalWeight>
            >,
        ) -> ::core::option::Option<::std::string::String> {
            match &__d.op {
                #enum_id::FieldTokenText(__s) => {
                    ::core::option::Option::Some(__s.clone())
                },
                _ => ::core::option::Option::None,
            }
        }
    }
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
pub(crate) fn ordered_seq_reconstruct(language: &LanguageDef) -> Vec<TokenStream> {
    let enum_id = op_enum_ident(language);
    ordered_seq_element_categories(language)
        .into_iter()
        .map(|element_cat| {
            let fn_name = ordered_seq_build_fn(&element_cat);
            let v = field_seq_variant_ident(&element_cat);
            quote! {
                // A language whose only `Vec` field sits on a variant no fold reads emits this
                // inverse without calling it; that is correct (the capability is present) and
                // must not be a warning.
                #[allow(dead_code)]
                fn #fn_name(
                    __d: &::std::rc::Rc<
                        ::dovetail::extract::Derivation<#enum_id, ::rigail::TropicalWeight>
                    >,
                ) -> ::core::option::Option<::std::vec::Vec<#element_cat>> {
                    match &__d.op {
                        #enum_id::#v(__values) => {
                            ::core::option::Option::Some(__values.clone())
                        },
                        _ => ::core::option::Option::None,
                    }
                }
            }
        })
        .collect()
}

/// Every per-category reconstructor for `language`, PLUS the single shared token-text inverse
/// and (#101) one ordered-sequence inverse per `Vec` element category.
///
/// The three typed-path assembly sites (`typed_report`'s `generate_dovetail_normal_term`,
/// `generate_step_graph`, `generate_typed_dovetail_report`) each emit the reconstructors into
/// their own scope. Collecting them HERE rather than at each site is what keeps the token-text
/// inverse — and now the sequence inverses — from being added to two of the three: the exact
/// drift shape this file's history already contains once.
pub(crate) fn all_reconstructors(language: &LanguageDef) -> Vec<TokenStream> {
    let seq = ordered_seq_reconstruct(language);
    let mut out = Vec::with_capacity(language.types.len() + 1 + seq.len());
    out.extend(
        language
            .types
            .iter()
            .map(|ty| category_reconstruct(language, &ty.name)),
    );
    out.push(token_text_reconstruct(language));
    out.extend(seq);
    out
}

/// Generate `__mettail_dovetail_build_<cat>_d`: reconstruct a `<Cat>` from a derivation tree.
pub(crate) fn category_reconstruct(language: &LanguageDef, category: &Ident) -> TokenStream {
    let enum_id = op_enum_ident(language);
    let fn_name = build_fn(category);
    // (#101) The element categories that have a `FieldSeq*` variant — the SAME set the lowering
    // consults, so the inverse admits exactly the fields the lowering made invertible.
    let earned_seq_elements = ordered_seq_element_categories(language);

    let mut arms: Vec<TokenStream> = Vec::new();
    for variant in collect_category_variants(category, language) {
        match variant {
            VariantKind::Var { label }
            | VariantKind::Literal { label }
            | VariantKind::CollectionLiteral { label, .. } => {
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
                if fields.is_empty() || !all_fields_invertible(&fields, &earned_seq_elements) {
                    // Not structurally invertible here — falls through to `_ => None`.
                    continue;
                }
                let v = op_variant_ident(category, &label);
                let child_exprs: Vec<TokenStream> = fields
                    .iter()
                    .enumerate()
                    .map(|(i, field)| reconstruct_child_expr(i, field, &earned_seq_elements))
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
                let v = op_variant_ident(category, &label);
                match collection_carrier(Some(&coll_type)) {
                    CollectionCarrier::AcBag => {
                        let elem_build = build_fn(&element_cat);
                        let helper =
                            format_ident!("insert_into_{}", label.to_string().to_lowercase());
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
                    // (#101) The exact inverse of `typed_lowering`'s ordered `Collection` arm:
                    // that arm emits `ENode::new(Cat_Label, [seq_leaf])`, so child 0 is the
                    // sequence leaf and `build_seq_<elem>_d` reads the whole `Vec` back
                    // losslessly. Emitting it keeps the two sides symmetric — an invertible
                    // lowering with no inverse is the drift this file's history records.
                    CollectionCarrier::OrderedSeq => {
                        let seq_build = ordered_seq_build_fn(&element_cat);
                        arms.push(quote! {
                            #enum_id::#v => {
                                let __values = #seq_build(__d.children.get(0usize)?)?;
                                ::core::option::Option::Some(#category::#label(__values))
                            },
                        });
                    },
                    // Unordered non-AC collection (`HashSet`/`HashMap`/`PathMap`): lowered as a
                    // `FieldOpaque` spine leaf, not invertible — falls through to `_ => None`.
                    CollectionCarrier::Opaque => continue,
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
                if !all_fields_invertible(&pre_scope_fields, &earned_seq_elements) {
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
                    .map(|(i, field)| reconstruct_child_expr(i, field, &earned_seq_elements))
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
                if !all_fields_invertible(&pre_scope_fields, &earned_seq_elements) {
                    continue;
                }
                let v = op_variant_ident(category, &label);
                let body_build = build_fn(&body_cat);
                let pre_exprs: Vec<TokenStream> = pre_scope_fields
                    .iter()
                    .enumerate()
                    .map(|(i, field)| reconstruct_child_expr(i, field, &earned_seq_elements))
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
