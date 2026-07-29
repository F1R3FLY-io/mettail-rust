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
//! `Nullary`, `Regular` constructors whose every field is invertible, and (E2.1) the AC
//! `Collection` (HashBag soup), `Binder`, and `MultiBinder` variants — each the exact
//! structural inverse of the corresponding [`super::typed_lowering`] arm. A `Regular`
//! constructor with a builtin/guest-body/optional/predicate/collection field is not
//! invertible here (its lowered child is a lossy or absent sentinel) and reconstructs to
//! `None`, faithfully deferring any fold that would read it; a non-AC
//! (`Vec`/`HashSet`/`HashMap`) collection field likewise lowers to a `FieldOpaque` spine leaf
//! and stays `None`.
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
use super::op_enum::{language_has_token_text_leaf, op_enum_ident, op_variant_ident};
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
    /// Not invertible from the derivation: its lowered child is a lossy/absent spine sentinel.
    /// Covers builtin-category fields, predicate slots, collections, optionals, and
    /// [`OpaqueLeafKind::GuestBody`] (an `Arc<FltNode>` has no lossless `Debug` inverse).
    /// A variant carrying one is skipped by `category_reconstruct` and falls through to
    /// `_ => None` — faithfully deferring any fold that would read it.
    NotInvertible,
}

/// Classify a field for reconstruction. Branches on the leaf FLAG before reading `category`,
/// whose value is a placeholder (`String`/`FltNode`) for leaf fields.
fn classify_reconstructable_field(field: &FieldInfo) -> ReconstructableField {
    if field.is_optional || field.is_collection || field.is_predicate {
        return ReconstructableField::NotInvertible;
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
fn all_fields_invertible(fields: &[FieldInfo]) -> bool {
    fields
        .iter()
        .all(|f| classify_reconstructable_field(f) != ReconstructableField::NotInvertible)
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
fn reconstruct_child_expr(field_index: usize, field: &FieldInfo) -> TokenStream {
    let i = field_index;
    match classify_reconstructable_field(field) {
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

/// Every per-category reconstructor for `language`, PLUS the single shared token-text inverse.
///
/// The three typed-path assembly sites (`typed_report`'s `generate_dovetail_normal_term`,
/// `generate_step_graph`, `generate_typed_dovetail_report`) each emit the reconstructors into
/// their own scope. Collecting them HERE rather than at each site is what keeps the token-text
/// inverse from being added to two of the three — the exact drift shape this file's history
/// already contains once.
pub(crate) fn all_reconstructors(language: &LanguageDef) -> Vec<TokenStream> {
    let mut out = Vec::with_capacity(language.types.len() + 1);
    out.extend(
        language
            .types
            .iter()
            .map(|ty| category_reconstruct(language, &ty.name)),
    );
    out.push(token_text_reconstruct(language));
    out
}

/// Generate `__mettail_dovetail_build_<cat>_d`: reconstruct a `<Cat>` from a derivation tree.
pub(crate) fn category_reconstruct(language: &LanguageDef, category: &Ident) -> TokenStream {
    let enum_id = op_enum_ident(language);
    let fn_name = build_fn(category);

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
                if fields.is_empty() || !all_fields_invertible(&fields) {
                    // Not structurally invertible here — falls through to `_ => None`.
                    continue;
                }
                let v = op_variant_ident(category, &label);
                let child_exprs: Vec<TokenStream> = fields
                    .iter()
                    .enumerate()
                    .map(|(i, field)| reconstruct_child_expr(i, field))
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
                if !all_fields_invertible(&pre_scope_fields) {
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
                    .map(|(i, field)| reconstruct_child_expr(i, field))
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
                if !all_fields_invertible(&pre_scope_fields) {
                    continue;
                }
                let v = op_variant_ident(category, &label);
                let body_build = build_fn(&body_cat);
                let pre_exprs: Vec<TokenStream> = pre_scope_fields
                    .iter()
                    .enumerate()
                    .map(|(i, field)| reconstruct_child_expr(i, field))
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
