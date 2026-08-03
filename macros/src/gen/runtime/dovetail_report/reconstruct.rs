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
    field_seq_variant_ident, field_withheld_variant_ident, language_has_token_text_leaf,
    op_enum_ident, op_variant_ident, ordered_seq_element_categories,
};
use super::withholding::{self, WithholdingSet};
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
    /// ★★★ (#195) A **SEVERED** position: a scalar category field some `| S ~/> T |-`
    /// declaration withheld propagation from. Lowered to `FieldWithheld<Cat>(value)` — the
    /// whole subterm VERBATIM inside one nullary leaf — so [`withheld_build_fn`] inverts it
    /// with a `clone()`.
    ///
    /// ★ The field's emitted Rust type is `Arc<Cat>`, exactly as for
    /// [`Category`](ReconstructableField::Category), and the leaf's payload is that same
    /// `Arc<Cat>`; so the rebuilt value is used AS IS — no `Arc::new` wrapper (the payload is
    /// already the `Arc`) and no `build_fn` recursion (there are no children to recurse into,
    /// which is the whole point of severance).
    ///
    /// ⚠ THIS IS WHY SEVERANCE DOES NOT COST RECONSTRUCTABILITY. Routing a withheld field
    /// through the lossy `FieldOpaque` leaf would have been a two-line change and would have
    /// turned every term containing one into a stuck reconstruction — the Turing lesson
    /// (`languages/tests/turing.rs`): a non-invertible carrier makes `dovetail_normal_term`
    /// fail for terms with no redex at all. Carrying the value verbatim keeps the inverse
    /// total, so a withheld position costs exactly propagation and nothing else.
    Withheld,
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
    severed: bool,
) -> ReconstructableField {
    // ★★★ (#195) SEVERANCE FIRST, mirroring `typed_lowering::field_child_expr_typed`'s
    // branch order exactly. The lowering tests severance before every other shape, so the
    // inverse must too, or the two would disagree about which leaf a field produced.
    if severed {
        return ReconstructableField::Withheld;
    }
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
fn all_fields_invertible(
    fields: &[FieldInfo],
    earned_seq_elements: &[Ident],
    owner_label: &Ident,
    withheld: &WithholdingSet,
) -> bool {
    fields.iter().enumerate().all(|(i, f)| {
        classify_reconstructable_field(f, earned_seq_elements, withheld.is_severed(owner_label, i))
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
    owner_label: &Ident,
    withheld: &WithholdingSet,
) -> TokenStream {
    let i = field_index;
    let severed = withheld.is_severed(owner_label, field_index);
    match classify_reconstructable_field(field, earned_seq_elements, severed) {
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
        // ★★★ (#195) A SEVERED position: the leaf payload IS the `Arc<Cat>` the
        // constructor stores, so the inverse is a `clone()` with NO wrapper and NO recursion.
        ReconstructableField::Withheld => {
            let withheld_build = withheld_build_fn(&field.category);
            quote! {
                #withheld_build(__d.children.get(#i)?)?
            }
        },
        // ★ #141 G9. The gate is `all_fields_invertible`, checked by the CALLER;
        // this function has no way to know it ran. It returns the child expression's
        // tokens, so the refusal simply IS the expression.
        ReconstructableField::NotInvertible => {
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
        pub(super) fn #fn_name(
            __d: &::dovetail::extract::Derivation<#enum_id, ::rigail::TropicalWeight>,
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
pub(crate) fn withheld_reconstruct(language: &LanguageDef) -> Vec<TokenStream> {
    let enum_id = op_enum_ident(language);
    withholding::classify_withholdings(language)
        .earned_categories()
        .into_iter()
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
                        #enum_id::#v(__value) => {
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
                pub(super) fn #fn_name(
                    __d: &::dovetail::extract::Derivation<#enum_id, ::rigail::TropicalWeight>,
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

fn rebuild_visit_variant(category: &Ident) -> Ident {
    format_ident!("Visit{}", category)
}

fn rebuild_value_variant(category: &Ident) -> Ident {
    category.clone()
}

fn rebuild_handler_name(category: &Ident) -> Ident {
    format_ident!("__mettail_dovetail_rebuild_handle_{}", super::to_snake(&category.to_string()))
}

fn rebuild_assemble_variant(category: &Ident, label: &Ident) -> Ident {
    format_ident!("Assemble{}{}", category, label)
}

fn rebuild_assemble_fn_name(category: &Ident, label: &Ident) -> Ident {
    format_ident!(
        "__mettail_dovetail_rebuild_assemble_{}_{}",
        super::to_snake(&category.to_string()),
        super::to_snake(&label.to_string()),
    )
}

fn rebuild_seq_task_variant(category: &Ident) -> Ident {
    format_ident!("BuildSeq{}", category)
}

fn rebuild_seq_value_variant(category: &Ident) -> Ident {
    format_ident!("Seq{}", category)
}

fn rebuild_withheld_task_variant(category: &Ident) -> Ident {
    format_ident!("BuildWithheld{}", category)
}

fn rebuild_withheld_value_variant(category: &Ident) -> Ident {
    format_ident!("Withheld{}", category)
}

/// Schedule one derivation child in the shared reconstruction PDA. Every task carries a raw
/// pointer into the root-owned `Rc<Derivation>` tree and is consumed synchronously.
fn reconstruct_child_task(
    field_index: usize,
    field: &FieldInfo,
    earned_seq_elements: &[Ident],
    owner_label: &Ident,
    withheld: &WithholdingSet,
) -> TokenStream {
    let i = field_index;
    let severed = withheld.is_severed(owner_label, field_index);
    match classify_reconstructable_field(field, earned_seq_elements, severed) {
        ReconstructableField::Category => {
            let visit = rebuild_visit_variant(&field.category);
            quote! {
                __tasks.push(__MettailDovetailRebuildTask::#visit(
                    __d.children[#i].as_ref() as *const _,
                ));
            }
        },
        ReconstructableField::TokenText => quote! {
            __tasks.push(__MettailDovetailRebuildTask::BuildTokenText(
                __d.children[#i].as_ref() as *const _,
            ));
        },
        ReconstructableField::OrderedSeq => {
            let task = rebuild_seq_task_variant(&field.category);
            quote! {
                __tasks.push(__MettailDovetailRebuildTask::#task(
                    __d.children[#i].as_ref() as *const _,
                ));
            }
        },
        ReconstructableField::Withheld => {
            let task = rebuild_withheld_task_variant(&field.category);
            quote! {
                __tasks.push(__MettailDovetailRebuildTask::#task(
                    __d.children[#i].as_ref() as *const _,
                ));
            }
        },
        ReconstructableField::NotInvertible => {
            let message = format!(
                "mettail internal error: reconstruction PDA scheduled non-invertible field `{}`",
                field.category,
            );
            quote! { compile_error!(#message); }
        },
    }
}

fn reconstructed_field_pop(
    field_index: usize,
    field: &FieldInfo,
    earned_seq_elements: &[Ident],
    owner_label: &Ident,
    withheld: &WithholdingSet,
) -> TokenStream {
    let severed = withheld.is_severed(owner_label, field_index);
    match classify_reconstructable_field(field, earned_seq_elements, severed) {
        ReconstructableField::Category => {
            let value = rebuild_value_variant(&field.category);
            quote! {
                match __values.pop()? {
                    __MettailDovetailRebuildValue::#value(__value) =>
                        ::std::sync::Arc::new(__value),
                    _ => return ::core::option::Option::None,
                }
            }
        },
        ReconstructableField::TokenText => quote! {
            match __values.pop()? {
                __MettailDovetailRebuildValue::TokenText(__value) => __value,
                _ => return ::core::option::Option::None,
            }
        },
        ReconstructableField::OrderedSeq => {
            let value = rebuild_seq_value_variant(&field.category);
            quote! {
                match __values.pop()? {
                    __MettailDovetailRebuildValue::#value(__value) => __value,
                    _ => return ::core::option::Option::None,
                }
            }
        },
        ReconstructableField::Withheld => {
            let value = rebuild_withheld_value_variant(&field.category);
            quote! {
                match __values.pop()? {
                    __MettailDovetailRebuildValue::#value(__value) => __value,
                    _ => return ::core::option::Option::None,
                }
            }
        },
        ReconstructableField::NotInvertible => {
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
pub(crate) fn reconstruction_pda_support(language: &LanguageDef) -> TokenStream {
    let enum_id = op_enum_ident(language);
    let earned_seq_elements = ordered_seq_element_categories(language);
    let withheld = withholding::classify_withholdings(language);

    let visit_tasks: Vec<TokenStream> = language
        .types
        .iter()
        .map(|ty| {
            let category = &ty.name;
            let visit = rebuild_visit_variant(category);
            quote! { #visit(*const __MettailDovetailDerivation) }
        })
        .collect();
    let category_values: Vec<TokenStream> = language
        .types
        .iter()
        .map(|ty| {
            let category = &ty.name;
            let value = rebuild_value_variant(category);
            quote! { #value(#category) }
        })
        .collect();
    let visit_dispatch: Vec<TokenStream> = language
        .types
        .iter()
        .map(|ty| {
            let category = &ty.name;
            let visit = rebuild_visit_variant(category);
            let handler = rebuild_handler_name(category);
            quote! {
                __MettailDovetailRebuildTask::#visit(__ptr) => {
                    // SAFETY: pointers are into the live root-owned derivation tree and the
                    // synchronous engine drains every task before the root borrow ends.
                    #handler(unsafe { &*__ptr }, &mut __tasks, &mut __values)?;
                }
            }
        })
        .collect();

    let token_task = language_has_token_text_leaf(language)
        .then(|| quote! { BuildTokenText(*const __MettailDovetailDerivation), });
    let token_value = language_has_token_text_leaf(language)
        .then(|| quote! { TokenText(::std::string::String), });
    let token_dispatch = language_has_token_text_leaf(language).then(|| {
        let build = token_text_build_fn();
        quote! {
            __MettailDovetailRebuildTask::BuildTokenText(__ptr) => {
                let __value = #build(unsafe { &*__ptr })?;
                __values.push(__MettailDovetailRebuildValue::TokenText(__value));
            }
        }
    });

    let seq_tasks: Vec<TokenStream> = earned_seq_elements
        .iter()
        .map(|category| {
            let task = rebuild_seq_task_variant(category);
            quote! { #task(*const __MettailDovetailDerivation) }
        })
        .collect();
    let seq_values: Vec<TokenStream> = earned_seq_elements
        .iter()
        .map(|category| {
            let value = rebuild_seq_value_variant(category);
            quote! { #value(::std::vec::Vec<#category>) }
        })
        .collect();
    let seq_dispatch: Vec<TokenStream> = earned_seq_elements
        .iter()
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

    let withheld_categories = withheld.earned_categories();
    let withheld_tasks: Vec<TokenStream> = withheld_categories
        .iter()
        .map(|category| {
            let task = rebuild_withheld_task_variant(category);
            quote! { #task(*const __MettailDovetailDerivation) }
        })
        .collect();
    let withheld_values: Vec<TokenStream> = withheld_categories
        .iter()
        .map(|category| {
            let value = rebuild_withheld_value_variant(category);
            quote! { #value(::std::sync::Arc<#category>) }
        })
        .collect();
    let withheld_dispatch: Vec<TokenStream> = withheld_categories
        .iter()
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

    let mut assemble_tasks = Vec::<TokenStream>::new();
    let mut assemble_dispatch = Vec::<TokenStream>::new();
    let mut assemble_fns = Vec::<TokenStream>::new();
    for ty in &language.types {
        let category = &ty.name;
        let category_value = rebuild_value_variant(category);
        for variant in collect_category_variants(category, language) {
            match variant {
                VariantKind::Regular { label, fields }
                    if !fields.is_empty()
                        && all_fields_invertible(
                            &fields,
                            &earned_seq_elements,
                            &label,
                            &withheld,
                        ) =>
                {
                    let assemble = rebuild_assemble_variant(category, &label);
                    let assemble_fn = rebuild_assemble_fn_name(category, &label);
                    assemble_tasks.push(quote! { #assemble });
                    let pops: Vec<TokenStream> = fields
                        .iter()
                        .enumerate()
                        .rev()
                        .map(|(i, field)| {
                            let var = format_ident!("__field_{i}");
                            let pop = reconstructed_field_pop(
                                i,
                                field,
                                &earned_seq_elements,
                                &label,
                                &withheld,
                            );
                            quote! { let #var = #pop; }
                        })
                        .collect();
                    let vars: Vec<Ident> = (0..fields.len())
                        .map(|i| format_ident!("__field_{i}"))
                        .collect();
                    assemble_fns.push(quote! {
                        fn #assemble_fn(
                            __values: &mut ::std::vec::Vec<__MettailDovetailRebuildValue>,
                        ) -> ::core::option::Option<()> {
                            #(#pops)*
                            __values.push(__MettailDovetailRebuildValue::#category_value(
                                #category::#label(#(#vars),*)
                            ));
                            ::core::option::Option::Some(())
                        }
                    });
                    assemble_dispatch.push(quote! {
                        __MettailDovetailRebuildTask::#assemble => {
                            #assemble_fn(&mut __values)?;
                        }
                    });
                },
                VariantKind::Collection { label, element_cat, coll_type } => {
                    let assemble = rebuild_assemble_variant(category, &label);
                    let assemble_fn = rebuild_assemble_fn_name(category, &label);
                    match collection_carrier(Some(&coll_type)) {
                        CollectionCarrier::AcBag => {
                            assemble_tasks.push(quote! { #assemble(usize) });
                            let elem_value = rebuild_value_variant(&element_cat);
                            let helper =
                                format_ident!("insert_into_{}", label.to_string().to_lowercase());
                            assemble_fns.push(quote! {
                                fn #assemble_fn(
                                    __values: &mut ::std::vec::Vec<
                                        __MettailDovetailRebuildValue,
                                    >,
                                    __child_count: usize,
                                ) -> ::core::option::Option<()> {
                                    let __first = __values.len().checked_sub(__child_count)?;
                                    let mut __bag = ::mettail_runtime::HashBag::<#element_cat>::new();
                                    for __value in __values.drain(__first..) {
                                        let __element = match __value {
                                            __MettailDovetailRebuildValue::#elem_value(__element) =>
                                                __element,
                                            _ => return ::core::option::Option::None,
                                        };
                                        #category::#helper(&mut __bag, __element);
                                    }
                                    __values.push(__MettailDovetailRebuildValue::#category_value(
                                        #category::#label(__bag)
                                    ));
                                    ::core::option::Option::Some(())
                                }
                            });
                            assemble_dispatch.push(quote! {
                                __MettailDovetailRebuildTask::#assemble(__child_count) => {
                                    #assemble_fn(&mut __values, __child_count)?;
                                }
                            });
                        },
                        CollectionCarrier::OrderedSeq => {
                            assemble_tasks.push(quote! { #assemble });
                            let seq_value = rebuild_seq_value_variant(&element_cat);
                            assemble_fns.push(quote! {
                                fn #assemble_fn(
                                    __values: &mut ::std::vec::Vec<
                                        __MettailDovetailRebuildValue,
                                    >,
                                ) -> ::core::option::Option<()> {
                                    let __values_field = match __values.pop()? {
                                        __MettailDovetailRebuildValue::#seq_value(__value) =>
                                            __value,
                                        _ => return ::core::option::Option::None,
                                    };
                                    __values.push(__MettailDovetailRebuildValue::#category_value(
                                        #category::#label(__values_field)
                                    ));
                                    ::core::option::Option::Some(())
                                }
                            });
                            assemble_dispatch.push(quote! {
                                __MettailDovetailRebuildTask::#assemble => {
                                    #assemble_fn(&mut __values)?;
                                }
                            });
                        },
                        CollectionCarrier::Opaque => {},
                    }
                },
                VariantKind::Binder { label, pre_scope_fields, body_cat, .. }
                    if all_fields_invertible(
                        &pre_scope_fields,
                        &earned_seq_elements,
                        &label,
                        &withheld,
                    ) =>
                {
                    let assemble = rebuild_assemble_variant(category, &label);
                    let assemble_fn = rebuild_assemble_fn_name(category, &label);
                    assemble_tasks.push(quote! { #assemble });
                    let pops: Vec<TokenStream> = pre_scope_fields
                        .iter()
                        .enumerate()
                        .rev()
                        .map(|(i, field)| {
                            let var = format_ident!("__field_{i}");
                            let pop = reconstructed_field_pop(
                                i,
                                field,
                                &earned_seq_elements,
                                &label,
                                &withheld,
                            );
                            quote! { let #var = #pop; }
                        })
                        .collect();
                    let vars: Vec<Ident> = (0..pre_scope_fields.len())
                        .map(|i| format_ident!("__field_{i}"))
                        .collect();
                    let body_value = rebuild_value_variant(&body_cat);
                    assemble_fns.push(quote! {
                        fn #assemble_fn(
                            __values: &mut ::std::vec::Vec<__MettailDovetailRebuildValue>,
                        ) -> ::core::option::Option<()> {
                            #(#pops)*
                            let __binder = match __values.pop()? {
                                __MettailDovetailRebuildValue::SingleBinder(__binder) => __binder,
                                _ => return ::core::option::Option::None,
                            };
                            let __body = match __values.pop()? {
                                __MettailDovetailRebuildValue::#body_value(__body) => __body,
                                _ => return ::core::option::Option::None,
                            };
                            let __scope = ::mettail_runtime::Scope::from_parts_unsafe(
                                __binder,
                                ::std::sync::Arc::new(__body),
                            );
                            __values.push(__MettailDovetailRebuildValue::#category_value(
                                #category::#label(#(#vars,)* __scope)
                            ));
                            ::core::option::Option::Some(())
                        }
                    });
                    assemble_dispatch.push(quote! {
                        __MettailDovetailRebuildTask::#assemble => {
                            #assemble_fn(&mut __values)?;
                        }
                    });
                },
                VariantKind::MultiBinder { label, pre_scope_fields, body_cat, .. }
                    if all_fields_invertible(
                        &pre_scope_fields,
                        &earned_seq_elements,
                        &label,
                        &withheld,
                    ) =>
                {
                    let assemble = rebuild_assemble_variant(category, &label);
                    let assemble_fn = rebuild_assemble_fn_name(category, &label);
                    assemble_tasks.push(quote! { #assemble });
                    let pops: Vec<TokenStream> = pre_scope_fields
                        .iter()
                        .enumerate()
                        .rev()
                        .map(|(i, field)| {
                            let var = format_ident!("__field_{i}");
                            let pop = reconstructed_field_pop(
                                i,
                                field,
                                &earned_seq_elements,
                                &label,
                                &withheld,
                            );
                            quote! { let #var = #pop; }
                        })
                        .collect();
                    let vars: Vec<Ident> = (0..pre_scope_fields.len())
                        .map(|i| format_ident!("__field_{i}"))
                        .collect();
                    let body_value = rebuild_value_variant(&body_cat);
                    assemble_fns.push(quote! {
                        fn #assemble_fn(
                            __values: &mut ::std::vec::Vec<__MettailDovetailRebuildValue>,
                        ) -> ::core::option::Option<()> {
                            #(#pops)*
                            let __binders = match __values.pop()? {
                                __MettailDovetailRebuildValue::MultiBinders(__binders) => __binders,
                                _ => return ::core::option::Option::None,
                            };
                            let __body = match __values.pop()? {
                                __MettailDovetailRebuildValue::#body_value(__body) => __body,
                                _ => return ::core::option::Option::None,
                            };
                            let __scope = ::mettail_runtime::Scope::from_parts_unsafe(
                                __binders,
                                ::std::sync::Arc::new(__body),
                            );
                            __values.push(__MettailDovetailRebuildValue::#category_value(
                                #category::#label(#(#vars,)* __scope)
                            ));
                            ::core::option::Option::Some(())
                        }
                    });
                    assemble_dispatch.push(quote! {
                        __MettailDovetailRebuildTask::#assemble => {
                            #assemble_fn(&mut __values)?;
                        }
                    });
                },
                _ => {},
            }
        }
    }

    quote! {
        type __MettailDovetailDerivation =
            ::dovetail::extract::Derivation<#enum_id, ::rigail::TropicalWeight>;

        #[allow(dead_code)]
        enum __MettailDovetailRebuildTask {
            #(#visit_tasks,)*
            #token_task
            #(#seq_tasks,)*
            #(#withheld_tasks,)*
            MakeSingleBinder,
            MakeMultiBinders(usize),
            #(#assemble_tasks,)*
        }

        #[allow(dead_code)]
        enum __MettailDovetailRebuildValue {
            #(#category_values,)*
            #token_value
            #(#seq_values,)*
            #(#withheld_values,)*
            SingleBinder(::mettail_runtime::Binder<::std::string::String>),
            MultiBinders(::std::vec::Vec<
                ::mettail_runtime::Binder<::std::string::String>,
            >),
        }

        #(#assemble_fns)*

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
                        #(#visit_dispatch)*
                        #token_dispatch
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
                        #(#assemble_dispatch)*
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
pub(crate) fn all_reconstructors(language: &LanguageDef) -> Vec<TokenStream> {
    let seq = ordered_seq_reconstruct(language);
    // ★ (#195) …and one withheld-position inverse per severed category, collected HERE for
    // exactly the reason the sequence inverses are: the three typed-path assembly sites each
    // emit into their own scope, and adding an inverse to two of the three is the drift shape
    // this file's history already contains once.
    let withheld = withheld_reconstruct(language);
    let mut out = Vec::with_capacity(language.types.len() + 2 + seq.len() + withheld.len());
    out.push(reconstruction_pda_support(language));
    out.extend(
        language
            .types
            .iter()
            .map(|ty| category_reconstruct(language, &ty.name)),
    );
    out.push(token_text_reconstruct(language));
    out.extend(seq);
    out.extend(withheld);
    out
}

/// Generate `__mettail_dovetail_build_<cat>_d`: reconstruct a `<Cat>` from a derivation tree.
pub(crate) fn category_reconstruct(language: &LanguageDef, category: &Ident) -> TokenStream {
    let enum_id = op_enum_ident(language);
    let fn_name = build_fn(category);
    let handler_name = rebuild_handler_name(category);
    let seed_task = rebuild_visit_variant(category);
    let root_value = rebuild_value_variant(category);
    let earned_seq_elements = ordered_seq_element_categories(language);
    let withheld = withholding::classify_withholdings(language);

    let mut arms = Vec::<TokenStream>::new();
    for variant in collect_category_variants(category, language) {
        match variant {
            VariantKind::Refused { message, .. } => {
                arms.push(quote! { compile_error!(#message); });
            },
            VariantKind::Var { label }
            | VariantKind::Literal { label }
            | VariantKind::CollectionLiteral { label, .. } => {
                let op = op_variant_ident(category, &label);
                arms.push(quote! {
                    #enum_id::#op(__payload) => {
                        __values.push(__MettailDovetailRebuildValue::#root_value(
                            #category::#label(__payload.clone()),
                        ));
                        ::core::option::Option::Some(())
                    },
                });
            },
            VariantKind::Nullary { label } => {
                let op = op_variant_ident(category, &label);
                arms.push(quote! {
                    #enum_id::#op => {
                        __values.push(__MettailDovetailRebuildValue::#root_value(
                            #category::#label,
                        ));
                        ::core::option::Option::Some(())
                    },
                });
            },
            VariantKind::Regular { label, fields }
                if !fields.is_empty()
                    && all_fields_invertible(&fields, &earned_seq_elements, &label, &withheld) =>
            {
                let op = op_variant_ident(category, &label);
                let assemble = rebuild_assemble_variant(category, &label);
                let child_count = fields.len();
                let child_tasks: Vec<TokenStream> = fields
                    .iter()
                    .enumerate()
                    .rev()
                    .map(|(i, field)| {
                        reconstruct_child_task(i, field, &earned_seq_elements, &label, &withheld)
                    })
                    .collect();
                arms.push(quote! {
                    #enum_id::#op => {
                        if __d.children.len() < #child_count {
                            return ::core::option::Option::None;
                        }
                        __tasks.push(__MettailDovetailRebuildTask::#assemble);
                        #(#child_tasks)*
                        ::core::option::Option::Some(())
                    },
                });
            },
            VariantKind::Collection { label, element_cat, coll_type } => {
                let op = op_variant_ident(category, &label);
                let assemble = rebuild_assemble_variant(category, &label);
                match collection_carrier(Some(&coll_type)) {
                    CollectionCarrier::AcBag => {
                        let visit = rebuild_visit_variant(&element_cat);
                        arms.push(quote! {
                            #enum_id::#op => {
                                __tasks.push(__MettailDovetailRebuildTask::#assemble(
                                    __d.children.len(),
                                ));
                                let __first_child_task = __tasks.len();
                                for __child in &__d.children {
                                    __tasks.push(__MettailDovetailRebuildTask::#visit(
                                        __child.as_ref() as *const _,
                                    ));
                                }
                                __tasks[__first_child_task..].reverse();
                                ::core::option::Option::Some(())
                            },
                        });
                    },
                    CollectionCarrier::OrderedSeq => {
                        let seq_task = rebuild_seq_task_variant(&element_cat);
                        arms.push(quote! {
                            #enum_id::#op => {
                                let __child = __d.children.get(0usize)?;
                                __tasks.push(__MettailDovetailRebuildTask::#assemble);
                                __tasks.push(__MettailDovetailRebuildTask::#seq_task(
                                    __child.as_ref() as *const _,
                                ));
                                ::core::option::Option::Some(())
                            },
                        });
                    },
                    CollectionCarrier::Opaque => {},
                }
            },
            VariantKind::Binder { label, pre_scope_fields, body_cat, .. }
                if all_fields_invertible(
                    &pre_scope_fields,
                    &earned_seq_elements,
                    &label,
                    &withheld,
                ) =>
            {
                let op = op_variant_ident(category, &label);
                let assemble = rebuild_assemble_variant(category, &label);
                let body_visit = rebuild_visit_variant(&body_cat);
                let arity_idx = pre_scope_fields.len();
                let body_idx = arity_idx + 1;
                let pre_tasks: Vec<TokenStream> = pre_scope_fields
                    .iter()
                    .enumerate()
                    .rev()
                    .map(|(i, field)| {
                        reconstruct_child_task(i, field, &earned_seq_elements, &label, &withheld)
                    })
                    .collect();
                arms.push(quote! {
                    #enum_id::#op => {
                        match &__d.children.get(#arity_idx)?.op {
                            #enum_id::BinderArity(1u32) => {},
                            _ => return ::core::option::Option::None,
                        }
                        let __body = __d.children.get(#body_idx)?;
                        __tasks.push(__MettailDovetailRebuildTask::#assemble);
                        #(#pre_tasks)*
                        __tasks.push(__MettailDovetailRebuildTask::MakeSingleBinder);
                        __tasks.push(__MettailDovetailRebuildTask::#body_visit(
                            __body.as_ref() as *const _,
                        ));
                        ::core::option::Option::Some(())
                    },
                });
            },
            VariantKind::MultiBinder { label, pre_scope_fields, body_cat, .. }
                if all_fields_invertible(
                    &pre_scope_fields,
                    &earned_seq_elements,
                    &label,
                    &withheld,
                ) =>
            {
                let op = op_variant_ident(category, &label);
                let assemble = rebuild_assemble_variant(category, &label);
                let body_visit = rebuild_visit_variant(&body_cat);
                let arity_idx = pre_scope_fields.len();
                let body_idx = arity_idx + 1;
                let pre_tasks: Vec<TokenStream> = pre_scope_fields
                    .iter()
                    .enumerate()
                    .rev()
                    .map(|(i, field)| {
                        reconstruct_child_task(i, field, &earned_seq_elements, &label, &withheld)
                    })
                    .collect();
                arms.push(quote! {
                    #enum_id::#op => {
                        let __arity = match &__d.children.get(#arity_idx)?.op {
                            #enum_id::BinderArity(__n) => *__n as usize,
                            _ => return ::core::option::Option::None,
                        };
                        let __body = __d.children.get(#body_idx)?;
                        __tasks.push(__MettailDovetailRebuildTask::#assemble);
                        #(#pre_tasks)*
                        __tasks.push(__MettailDovetailRebuildTask::MakeMultiBinders(__arity));
                        __tasks.push(__MettailDovetailRebuildTask::#body_visit(
                            __body.as_ref() as *const _,
                        ));
                        ::core::option::Option::Some(())
                    },
                });
            },
            _ => {},
        }
    }

    quote! {
        #[allow(unreachable_patterns)]
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
            match __mettail_dovetail_rebuild_run(
                __MettailDovetailRebuildTask::#seed_task(__d.as_ref() as *const _),
            )? {
                __MettailDovetailRebuildValue::#root_value(__root) =>
                    ::core::option::Option::Some(__root),
                _ => ::core::option::Option::None,
            }
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
    // (#101) The element categories that have a `FieldSeq*` variant — the SAME set the lowering
    // consults, so the inverse admits exactly the fields the lowering made invertible.
    let earned_seq_elements = ordered_seq_element_categories(language);
    // ★ (#195) The severed-position set — the SAME derivation the lowering consults, so the
    // inverse admits exactly the positions the lowering severed.
    let withheld = withholding::classify_withholdings(language);

    let mut arms: Vec<TokenStream> = Vec::new();
    for variant in collect_category_variants(category, language) {
        match variant {
            // ★ #141 G5 — see `VariantKind::Refused`.
            VariantKind::Refused { message, .. } => {
                arms.push(quote! { compile_error!(#message); });
            },
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
                if fields.is_empty()
                    || !all_fields_invertible(&fields, &earned_seq_elements, &label, &withheld)
                {
                    // Not structurally invertible here — falls through to `_ => None`.
                    continue;
                }
                let v = op_variant_ident(category, &label);
                let child_exprs: Vec<TokenStream> = fields
                    .iter()
                    .enumerate()
                    .map(|(i, field)| {
                        reconstruct_child_expr(i, field, &earned_seq_elements, &label, &withheld)
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
                if !all_fields_invertible(
                    &pre_scope_fields,
                    &earned_seq_elements,
                    &label,
                    &withheld,
                ) {
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
                    .map(|(i, field)| {
                        reconstruct_child_expr(i, field, &earned_seq_elements, &label, &withheld)
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
                if !all_fields_invertible(
                    &pre_scope_fields,
                    &earned_seq_elements,
                    &label,
                    &withheld,
                ) {
                    continue;
                }
                let v = op_variant_ident(category, &label);
                let body_build = build_fn(&body_cat);
                let pre_exprs: Vec<TokenStream> = pre_scope_fields
                    .iter()
                    .enumerate()
                    .map(|(i, field)| {
                        reconstruct_child_expr(i, field, &earned_seq_elements, &label, &withheld)
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
