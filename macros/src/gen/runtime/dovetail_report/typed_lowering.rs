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
//! Field-level non-category leaves (builtin/predicate/optional-None and unordered field-level
//! collections) lower to the spine sentinels `FieldOpaque`/`FieldNone`; they are spine leaves a
//! fold never reads back, so reconstruction returns `None` for them. (Rholang's collection
//! folds read whole `List`/`Map`/`Bag` *category* values via the `Literal` arm, and AC soup via
//! the `Collection`-variant arm — both reconstructable.)
//!
//! ★ TWO field-level leaves are exceptions, and both are exceptions by KIND, not by blanket.
//! The shape is the same each time: a lowering that carried the value's own bytes but had no
//! LABEL and no INVERSE is given both, so the operand becomes bindable without any change to
//! the equivalence relation over values.
//!
//! * (A4) an [`OpaqueLeafKind::TokenText`] capture (`v@Tok`, `m:Ident`) lowers to
//!   `FieldTokenText(text)` — the text VERBATIM — which `super::reconstruct` inverts
//!   losslessly. [`OpaqueLeafKind::GuestBody`] (`Arc<FltNode>`) and predicate slots keep the
//!   lossy `FieldOpaque`, because an `Arc<FltNode>` has no lossless `Debug` inverse.
//! * (#101) an ORDERED (`Vec`) collection lowers to `FieldSeq<Elem>(Vec<Elem>)` — the whole
//!   vector VERBATIM, one variant per element category — inverted by
//!   `__mettail_dovetail_build_seq_<elem>_d`. `HashSet`/`HashMap`/`PathMap` keep the lossy
//!   `FieldOpaque`, because their `Debug` does not agree with `Eq` and there is therefore no
//!   stored order to invert to. See [`super::CollectionCarrier`] for the total classification.
//!
//! Nothing about INERTNESS changes in either case: every term operation still keys on
//! `FieldInfo::is_opaque_leaf()` / `is_collection`, treats the kinds identically (no descent,
//! no α-conversion, no substitution), and not one line under `crate::gen::term_ops` is touched
//! by the carrier change. ⚠ In particular the ordered carrier makes collection ELEMENTS no more
//! visible to congruence closure than before: the leaf holds the collection as ONE opaque
//! payload, so no element is an e-class and no element is reduced.

use mettail_ast::grammar::NonTerminalKind;
use mettail_ast::language::LanguageDef;
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use syn::Ident;

use super::category_lowering_fn;
use super::op_enum::{op_enum_ident, op_variant_ident, ordered_seq_element_categories};
use crate::gen::term_ops::subst::{
    collect_category_variants, FieldInfo, OpaqueLeafKind, VariantKind,
};

use carrier_handle::{
    resolve_field_carrier, resolve_variant_carrier, AcOp, ResolvedCarrier, SeqLeafOp,
};

/// (#101) ★★ ORDERED vs AC, DISTINGUISHABLE AT THE TYPE LEVEL — not by convention.
///
/// The two collection carriers are lowered by two emitters with two DIFFERENT operand types
/// ([`AcOp`] and [`SeqLeafOp`]), and neither type has a public constructor: the ONLY way to
/// obtain one is [`resolve_variant_carrier`] / [`resolve_field_carrier`], each of which builds
/// it inside the matching [`super::CollectionCarrier`] arm. Handing
/// [`super::ac_bag_lowering_typed`] an ordered operand — the mistake that would license the AC
/// matcher to PERMUTE an ordered sequence — is therefore a compile error IN THE GENERATOR, not
/// a review comment.
///
/// Three independent barriers stand between an ordered `Vec` and a permutation licence:
///
///  1. **These handles.** Two emitters, two operand types, one constructor each.
///  2. **The generated code's own types.** `Pattern::ac(op: L, …)` takes an `L` VALUE.
///     `L::FieldSeq<Elem>` is a TUPLE variant, so naming it without a `Vec<Elem>` yields a
///     *function item*, not an `L` — `Pattern::ac(L::FieldSeqSym, …)` does not compile. The
///     AC ops (`L::<Cat>_<Label>`) are payload-less and *are* expressible as pattern operators.
///  3. **Arity.** The ordered carrier is a LEAF (zero children); the AC carrier is an n-ary
///     node. There is no children vector to permute.
///
/// `super::ac::lower_ac_collection`'s `HashBag`-only check remains in place, now
/// redundant-by-construction rather than load-bearing-by-vigilance.
mod carrier_handle {
    use mettail_ast::types::CollectionType;
    use proc_macro2::TokenStream;
    use quote::quote;
    use syn::Ident;

    use super::super::op_enum::{field_seq_variant_ident, op_variant_ident};
    use super::super::{collection_carrier, CollectionCarrier};

    /// The AC-bag OPERATOR handle: the typed op-enum variant of an n-ary bag node, whose
    /// children the AC matcher is licensed to permute. Its field is private to this module and
    /// the only constructor is the `AcBag` arm of [`resolve_variant_carrier`].
    pub(super) struct AcOp(TokenStream);

    impl AcOp {
        /// The operator expression (`L::<Cat>_<Label>`).
        pub(super) fn tokens(&self) -> &TokenStream {
            &self.0
        }
    }

    /// The ORDERED-SEQUENCE leaf handle: the typed op-enum `FieldSeq<Elem>` tuple variant, a
    /// payload-bearing LEAF with zero children. Its field is private to this module and the only
    /// constructors are the `OrderedSeq` arms of [`resolve_variant_carrier`] /
    /// [`resolve_field_carrier`].
    pub(super) struct SeqLeafOp(TokenStream);

    impl SeqLeafOp {
        /// The leaf-constructor expression (`L::FieldSeq<Elem>`), applied to the payload.
        pub(super) fn tokens(&self) -> &TokenStream {
            &self.0
        }
    }

    /// A collection carrier RESOLVED at one lowering site, carrying the handle that site's
    /// emitter needs.
    pub(super) enum ResolvedCarrier {
        AcBag(AcOp),
        OrderedSeq(SeqLeafOp),
        /// No labelled carrier: the lossy `FieldOpaque(Debug)` spine leaf, with no inverse.
        Opaque,
    }

    /// Resolve the carrier of a **whole-constructor** collection
    /// ([`crate::gen::term_ops::subst::VariantKind::Collection`], e.g. `PPar . ps:HashBag(Proc)`
    /// or a single-`Vec` constructor). Both the AC operator and the ordered leaf are reachable
    /// here, because the constructor itself supplies the n-ary bag node's op identity.
    /// `earned` is [`super::super::op_enum::ordered_seq_element_categories`] for the language —
    /// the element categories that actually HAVE a `FieldSeq*` variant. Consulting it here (and
    /// in [`resolve_field_carrier`]) is what makes it impossible to emit a leaf whose op-enum
    /// variant does not exist.
    pub(super) fn resolve_variant_carrier(
        enum_id: &Ident,
        coll_type: &CollectionType,
        category: &Ident,
        label: &Ident,
        element_cat: &Ident,
        earned: &[Ident],
    ) -> ResolvedCarrier {
        match collection_carrier(Some(coll_type)) {
            CollectionCarrier::AcBag => {
                let v = op_variant_ident(category, label);
                ResolvedCarrier::AcBag(AcOp(quote! { #enum_id::#v }))
            },
            // A whole-constructor collection is always a DECLARED rule, so its element category
            // is necessarily earned; the check is kept so both resolvers obey one rule rather
            // than one obeying it and the other assuming it.
            CollectionCarrier::OrderedSeq if earned.iter().any(|e| e == element_cat) => {
                let v = field_seq_variant_ident(element_cat);
                ResolvedCarrier::OrderedSeq(SeqLeafOp(quote! { #enum_id::#v }))
            },
            CollectionCarrier::OrderedSeq | CollectionCarrier::Opaque => ResolvedCarrier::Opaque,
        }
    }

    /// Resolve the carrier of a collection **FIELD** of a `Regular`/`Binder` constructor
    /// (`shift_right . l:Vec(Sym), h:Sym, r:Vec(Sym)`).
    ///
    /// ⚠ An `AcBag` FIELD resolves to `Opaque` here, and that is UNCHANGED behaviour, not a new
    /// refusal: the typed path has never AC-lowered a HashBag *field* — only a whole-constructor
    /// `VariantKind::Collection` — because a field has no op identity of its own to serve as the
    /// bag node's operator. (The `EGraph<String>` path does AC-lower such a field, using the
    /// synthesized `"<owner>::field<i>::collection"` label; giving the typed path an equivalent
    /// would change the e-graph SHAPE of every language that has one, which is a different
    /// change from #101 and is not made here. The corpus has zero HashBag fields today — every
    /// `HashBag(Proc)` in the tree is a whole-constructor `PPar`. (Rholang's `PParInternal`
    /// was a second such constructor until 2026-07-29, when it was deleted as a vestige; the
    /// "zero HashBag fields" claim is unaffected, since it was a whole-constructor too.)
    /// ⚠ A `Vec` field whose element category has NOT earned a carrier (see
    /// [`super::super::op_enum::ordered_seq_element_categories`] — the generator-synthesized HOL
    /// `MApply<Domain>` forms are the only such fields) resolves to `Opaque`, keeping the exact
    /// lowering it had before #101. Consulting `earned` here is what makes it impossible to emit
    /// a leaf whose op-enum variant does not exist.
    pub(super) fn resolve_field_carrier(
        enum_id: &Ident,
        coll_type: Option<&CollectionType>,
        element_cat: &Ident,
        earned: &[Ident],
    ) -> ResolvedCarrier {
        match collection_carrier(coll_type) {
            CollectionCarrier::OrderedSeq if earned.iter().any(|e| e == element_cat) => {
                let v = field_seq_variant_ident(element_cat);
                ResolvedCarrier::OrderedSeq(SeqLeafOp(quote! { #enum_id::#v }))
            },
            CollectionCarrier::OrderedSeq
            | CollectionCarrier::AcBag
            | CollectionCarrier::Opaque => ResolvedCarrier::Opaque,
        }
    }
}

/// `eg.add(ENode::leaf(L::FieldOpaque(format!("{:?}", payload))))` — a lossy spine leaf for a
/// builtin/predicate/non-reconstructable field. Reconstruction maps it to `None`.
fn opaque_leaf_typed(enum_id: &Ident, payload: TokenStream) -> TokenStream {
    quote! {
        eg.add(::dovetail::egraph::ENode::leaf(
            #enum_id::FieldOpaque(format!("{:?}", #payload))
        ))
    }
}

/// (A4) `eg.add(ENode::leaf(L::FieldTokenText(text.clone())))` — the LABELLED, INVERTIBLE
/// token-text leaf, carrying the captured text VERBATIM.
///
/// `payload` must evaluate to a `&String` (the bare `String` field borrowed by the match arm,
/// or the `Some(_)` inner of an `Option<String>` field); `.clone()` is the whole conversion —
/// there is no `Debug` framing to undo, which is precisely what makes
/// `reconstruct::__mettail_dovetail_build_token_text_d` a lossless inverse.
///
/// ⚠ This is emitted ONLY for a field stamped [`OpaqueLeafKind::TokenText`], never for
/// [`OpaqueLeafKind::GuestBody`] (an `Arc<FltNode>` has no lossless `Debug` inverse) and never
/// for a predicate/builtin/collection field. That per-KIND split is the entire content of the
/// change: `OpaqueLeafKind` exists to carry exactly this sort of per-kind difference
/// (`term_ops/subst.rs`'s `OpaqueLeafKind::field_type` is its first use), and every INERTNESS
/// site — `Eq`/`Hash`/`Ord`/`subst`/`normalize`/`semantic_hash`/`display`/`is_ground`/
/// `term_depth`/`Drop`/`match_pattern` — keys on `FieldInfo::is_opaque_leaf()` and is untouched.
fn token_text_leaf_typed(enum_id: &Ident, payload: TokenStream) -> TokenStream {
    quote! {
        eg.add(::dovetail::egraph::ENode::leaf(
            #enum_id::FieldTokenText(#payload.clone())
        ))
    }
}

/// (#101) `eg.add(ENode::leaf(L::FieldSeq<Elem>(values.clone())))` — the LABELLED, INVERTIBLE
/// ORDERED-SEQUENCE leaf, carrying the whole `Vec<Elem>` VERBATIM.
///
/// `payload` must evaluate to a `&Vec<Elem>` (the field borrowed by the match arm); `.clone()`
/// is the whole conversion — there is no `Debug` framing to undo, which is precisely what makes
/// `reconstruct::__mettail_dovetail_build_seq_<elem>_d` a lossless inverse with NO UNESCAPING
/// PARSER anywhere. That is the property separating "lossless" from "usually right".
///
/// ★ THE E-GRAPH CONTENT KEY IS UNCHANGED BY THIS SWAP. `opaque_leaf_typed` writes
/// `FieldOpaque(format!("{:?}", values))` and the enum's `write_content` frames those Debug
/// bytes; this writes `FieldSeq<Elem>(values.clone())` and frames `format!("{:?}", …)` of the
/// same value. The PAYLOAD bytes are byte-for-byte identical, so the equivalence relation over
/// collection values does not move — only the discriminant (which strictly REDUCES aliasing:
/// `FieldOpaque` shares one discriminant across `Vec` payloads, builtin ints, predicates and
/// guest bodies) and the existence of an inverse.
///
/// ⚠ Emitted ONLY for a `Vec` ([`super::CollectionCarrier::OrderedSeq`]). A `HashSet`/`HashMap`/
/// `PathMap` keeps `FieldOpaque`, because their `Debug` does not agree with `Eq` — there is no
/// stored order to invert to, and a labelled leaf would claim an inverse that does not exist.
fn ordered_seq_leaf_typed(op: &SeqLeafOp, payload: TokenStream) -> TokenStream {
    let ctor = op.tokens();
    quote! {
        eg.add(::dovetail::egraph::ENode::leaf(#ctor(#payload.clone())))
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
fn ac_bag_lowering_typed(op: &AcOp, element_add: &Ident, bag_expr: TokenStream) -> TokenStream {
    let op = op.tokens();
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
/// the module doc; Rholang's reconstructable collections are categories, not fields).
fn field_child_expr_typed(
    enum_id: &Ident,
    field_index: usize,
    field: &FieldInfo,
    field_var: &Ident,
    earned_seq_elements: &[Ident],
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
            //
            // (A4) A PRESENT token-text payload takes the LABELLED, INVERTIBLE leaf; a
            // guest-body or a predicate keeps the lossy `FieldOpaque`. Absence is the same
            // `FieldNone(i)` nullary leaf either way, so `Option<String>` reconstructs as
            // `Some(text)`/`None` losslessly once the present arm is invertible.
            let leaf = match field.opaque_leaf {
                Some(OpaqueLeafKind::TokenText) => {
                    token_text_leaf_typed(enum_id, quote! { __pred })
                },
                Some(OpaqueLeafKind::GuestBody) | None => {
                    opaque_leaf_typed(enum_id, quote! { __pred })
                },
            };
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
        // capture lowers to an e-graph LEAF — atomic data, never a recursible
        // category child (there is no `__mettail_dovetail_add_flt_node` to call).
        // Mirrors the string-path `field_child_expr`; branch BEFORE the `child_fn`
        // fall-through.
        //
        // (A4) The two opaque-leaf KINDS part company here, and only here:
        //   • `TokenText` → `FieldTokenText(text)`, labelled and INVERTIBLE;
        //   • `GuestBody` → `FieldOpaque(Debug)`, still non-invertible — an
        //     `Arc<FltNode>` has no lossless `Debug` inverse, so promoting it would
        //     be a lie about recoverability rather than a capability.
        // A predicate slot (`?g:Guard`) keeps `FieldOpaque` for the same reason.
        return match field.opaque_leaf {
            Some(OpaqueLeafKind::TokenText) => {
                token_text_leaf_typed(enum_id, quote! { #field_var })
            },
            Some(OpaqueLeafKind::GuestBody) | None => {
                opaque_leaf_typed(enum_id, quote! { #field_var })
            },
        };
    }

    if field.is_collection {
        // (#101) An ORDERED (`Vec`) collection field takes the LABELLED, INVERTIBLE sequence
        // leaf; every other container keeps the lossy `FieldOpaque`. See
        // [`carrier_handle::resolve_field_carrier`] for why a `HashBag` FIELD stays opaque on
        // this path (unchanged behaviour — the typed path AC-lowers only whole-constructor
        // collections).
        return match resolve_field_carrier(
            enum_id,
            field.coll_type.as_ref(),
            &field.category,
            earned_seq_elements,
        ) {
            ResolvedCarrier::OrderedSeq(seq) => ordered_seq_leaf_typed(&seq, quote! { #field_var }),
            // `AcBag` is UNREACHABLE from `resolve_field_carrier` (it maps a HashBag field to
            // `Opaque`); the arm is written out rather than wildcarded so that changing that
            // mapping forces this site to state what it wants instead of inheriting a silent
            // opaque leaf.
            ResolvedCarrier::AcBag(_) | ResolvedCarrier::Opaque => {
                opaque_leaf_typed(enum_id, quote! { #field_var })
            },
        };
    }

    quote! { #child_fn(eg, #field_var.as_ref()) }
}

fn regular_arm_typed(
    enum_id: &Ident,
    category: &Ident,
    label: &Ident,
    fields: &[FieldInfo],
    earned_seq_elements: &[Ident],
) -> TokenStream {
    let variant = op_variant_ident(category, label);
    let field_vars: Vec<Ident> = (0..fields.len())
        .map(|i| format_ident!("field_{i}"))
        .collect();
    let child_exprs: Vec<TokenStream> = fields
        .iter()
        .zip(field_vars.iter())
        .enumerate()
        .map(|(i, (field, var))| {
            field_child_expr_typed(enum_id, i, field, var, earned_seq_elements)
        })
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
    earned_seq_elements: &[Ident],
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
        .map(|(i, (field, var))| {
            field_child_expr_typed(enum_id, i, field, var, earned_seq_elements)
        })
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
    // (#101) The element categories that have a `FieldSeq*` variant. Computed ONCE per
    // category lowering and threaded to every field site, so a leaf can never name a variant
    // the enum does not have.
    let earned_seq_elements = ordered_seq_element_categories(language);
    let arms: Vec<TokenStream> = collect_category_variants(category, language)
        .into_iter()
        .map(|variant| match variant {
            // ★ #141 G5 — see `VariantKind::Refused`.
            VariantKind::Refused { message, .. } => quote! { compile_error!(#message); },
            VariantKind::Var { label }
            | VariantKind::Literal { label }
            | VariantKind::CollectionLiteral { label, .. } => {
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
                regular_arm_typed(&enum_id, category, &label, &fields, &earned_seq_elements)
            },
            VariantKind::Collection { label, element_cat, coll_type } => {
                let v = op_variant_ident(category, &label);
                match resolve_variant_carrier(
                    &enum_id,
                    &coll_type,
                    category,
                    &label,
                    &element_cat,
                    &earned_seq_elements,
                ) {
                    ResolvedCarrier::AcBag(op) => {
                        let element_add = category_lowering_fn(&element_cat);
                        let body = ac_bag_lowering_typed(&op, &element_add, quote! { values });
                        quote! { #category::#label(values) => #body }
                    },
                    // (#101) ★ A single-`Vec` constructor gets a CONSTRUCTOR NODE over the
                    // sequence leaf — `ENode::new(Cat_Label, [seq_leaf])` — not the bare leaf
                    // this arm used to emit.
                    //
                    // The bare leaf ERASED CONSTRUCTOR IDENTITY: its only content was the
                    // payload's `Debug`, so two DISTINCT single-`Vec` constructors of one
                    // category with equal payloads hash-consed into the SAME e-class, and a
                    // rewrite keyed on one of them matched the other. Wrapping the leaf in the
                    // constructor's own op restores identity while leaving the payload bytes
                    // untouched, and it is what lets a fold on such a constructor use the
                    // ordinary positional `Pattern::app(op, [var xs])` LHS — child 0 IS the
                    // sequence leaf.
                    //
                    // ⚠ ZERO CORPUS INSTANCES: every `VariantKind::Collection` in the tree is a
                    // `HashBag` (`PPar`). The claim is therefore pinned by the live
                    // `SeqCarrierDemo` fixture, not by the corpus.
                    ResolvedCarrier::OrderedSeq(seq) => {
                        let leaf = ordered_seq_leaf_typed(&seq, quote! { values });
                        quote! {
                            #category::#label(values) => {
                                let __seq = #leaf;
                                eg.add(::dovetail::egraph::ENode::new(
                                    #enum_id::#v,
                                    vec![__seq],
                                ))
                            }
                        }
                    },
                    ResolvedCarrier::Opaque => {
                        let leaf = opaque_leaf_typed(&enum_id, quote! { values });
                        quote! { #category::#label(values) => #leaf }
                    },
                }
            },
            VariantKind::Binder { label, pre_scope_fields, .. } => binder_arm_typed(
                &enum_id,
                category,
                &label,
                &pre_scope_fields,
                false,
                &earned_seq_elements,
            ),
            VariantKind::MultiBinder { label, pre_scope_fields, .. } => binder_arm_typed(
                &enum_id,
                category,
                &label,
                &pre_scope_fields,
                true,
                &earned_seq_elements,
            ),
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
