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

use mettail_ast::language::LanguageDef;
use mettail_ast::types::CollectionType;
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use syn::Ident;

use super::category_lowering_fn;
use super::op_enum::{
    collection_pair_variant_ident, field_withheld_variant_ident, native_pathmap_mode_variant_ident,
    native_pathmap_pair_variant_ident, op_enum_ident, op_variant_ident, pathmap_mode_variant_ident,
    pathmap_pair_variant_ident,
};
use super::semantic_adapter::{
    SemanticAdapterLayout, SemanticFieldLayout, SemanticFieldProjection, SemanticVariantLayout,
};
use crate::gen::native_carrier::NativeRecursiveCarrier;
use crate::gen::term_ops::subst::{FieldInfo, VariantKind};

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
    use proc_macro2::TokenStream;
    use quote::quote;
    use syn::Ident;

    use super::super::op_enum::{field_seq_variant_ident, op_variant_ident};
    use super::super::semantic_adapter::{SemanticCollectionProjection, SemanticFieldProjection};

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
        category: &Ident,
        label: &Ident,
        element_cat: &Ident,
        projection: SemanticCollectionProjection,
    ) -> ResolvedCarrier {
        match projection {
            SemanticCollectionProjection::AcBag => {
                let v = op_variant_ident(category, label);
                ResolvedCarrier::AcBag(AcOp(quote! { #enum_id::#v }))
            },
            SemanticCollectionProjection::OrderedSequence => {
                let v = field_seq_variant_ident(element_cat);
                ResolvedCarrier::OrderedSeq(SeqLeafOp(quote! { #enum_id::#v }))
            },
            SemanticCollectionProjection::Opaque => ResolvedCarrier::Opaque,
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
        element_cat: &Ident,
        projection: SemanticFieldProjection,
    ) -> ResolvedCarrier {
        match projection {
            SemanticFieldProjection::OrderedSequence
            | SemanticFieldProjection::OptionalOrderedSequence => {
                let v = field_seq_variant_ident(element_cat);
                ResolvedCarrier::OrderedSeq(SeqLeafOp(quote! { #enum_id::#v }))
            },
            SemanticFieldProjection::Child
            | SemanticFieldProjection::OptionalChild
            | SemanticFieldProjection::Withheld
            | SemanticFieldProjection::TokenText
            | SemanticFieldProjection::OptionalTokenText
            | SemanticFieldProjection::Opaque
            | SemanticFieldProjection::OptionalOpaque => ResolvedCarrier::Opaque,
        }
    }
}

/// `eg.add(ENode::leaf(L::FieldOpaque(format!("{:?}", payload))))` — a lossy spine leaf for a
/// builtin/predicate/non-reconstructable field. Reconstruction maps it to `None`.
fn opaque_leaf_typed(enum_id: &Ident, payload: TokenStream) -> TokenStream {
    quote! { #enum_id::FieldOpaque(format!("{:?}", #payload)) }
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
    quote! { #enum_id::FieldTokenText(#payload.clone()) }
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
    quote! { #ctor(#payload.clone()) }
}

/// ★★★ (#195) `eg.add(ENode::leaf(L::FieldWithheld<Cat>(value.clone())))` — the LABELLED,
/// INVERTIBLE **withheld-position** leaf, carrying the field's whole subterm VERBATIM.
///
/// `payload` must evaluate to an `&Arc<Cat>` (the field borrowed by the match arm);
/// `.clone()` is an `Arc` bump and the whole conversion — there is no `Debug` framing to
/// undo, which is what makes `reconstruct::withheld_reconstruct` a total, lossless inverse
/// with NO unescaping parser anywhere.
///
/// ★ THIS IS THE ONLY BRANCH THAT CHANGES THE EQUIVALENCE RELATION, and changing it is the
/// point. Every other labelled-leaf swap in this module (`FieldTokenText` (A4),
/// `FieldSeq<Elem>` (#101)) was byte-for-byte equivalence-preserving: the payload bytes were
/// already what `FieldOpaque` framed, and only the label and the inverse were new. Here the
/// field STOPS being a child e-class, which is exactly what withholding means — see
/// `withholding`'s Theorem W1 and
/// `dovetail/formal/rocq/theories/Lowering/CongruenceWithholding.v`.
///
/// ⚠ Emitted ONLY for a position some `| S ~/> T |-` declaration severs
/// (`WithholdingSet::is_severed`). No production language declares one, so every shipped
/// language's lowering is byte-identical across #195; the mechanism is pinned by the live
/// `languages/tests/definitions/congruence_withholding_demo.rs` fixture instead of by the
/// production corpus.
fn withheld_leaf_typed(enum_id: &Ident, category: &Ident, payload: TokenStream) -> TokenStream {
    let variant = field_withheld_variant_ident(category);
    quote! { #enum_id::#variant(#payload.clone()) }
}

/// `eg.add(ENode::leaf(L::FieldNone(i)))` — an absent optional field slot.
fn field_none_typed(enum_id: &Ident, field_index: usize) -> TokenStream {
    let i = field_index as u32;
    quote! { #enum_id::FieldNone(#i) }
}

/// Typed AC bag lowering task schedule: visit elements in the same iteration order as the
/// recursive reference, then assemble after sorting their e-class ids by canonical key.
fn ac_bag_lowering_typed(op: &AcOp, element_cat: &Ident, bag_expr: TokenStream) -> TokenStream {
    let op = op.tokens();
    let element_task = format_ident!("Visit{}", element_cat);
    quote! {
        {
            let __bag = #bag_expr;
            __tasks.push(__MettailDovetailLowerTask::Assemble {
                op: #op,
                child_count: __bag.len(),
                canonicalize: true,
            });
            let __first_child_task = __tasks.len();
            for __elem in __bag.iter_elements() {
                __tasks.push(__MettailDovetailLowerTask::#element_task(
                    __elem as *const _,
                ));
            }
            __tasks[__first_child_task..].reverse();
        }
    }
}

/// Lower a native collection-literal category through the exact structural
/// projection already described by [`SemanticAdapterLayout`].  Recursive
/// elements become category visits; map entries receive an explicit pair node;
/// and PathMap receives a first-child mode leaf plus pair nodes in map mode.
/// Unordered children are sorted only by the e-graph's exact [`ContentKey`].
fn collection_literal_lowering_typed(
    enum_id: &Ident,
    category: &Ident,
    label: &Ident,
    element_cat: &Ident,
    coll_type: &CollectionType,
    layout: &SemanticAdapterLayout,
) -> TokenStream {
    let op = op_variant_ident(category, label);

    // A native collection of scalars (Rholang Bytes is Vec<u8>) has no
    // generated category visit task.  It remains one exact scalar coefficient;
    // StructuralV2 applies to the term-bearing collection domain.
    if layout.category(element_cat).is_none() {
        return quote! {
            #category::#label(value) => {
                __tasks.push(__MettailDovetailLowerTask::Leaf(
                    #enum_id::#op(value.clone()),
                ));
            }
        };
    }

    let visit = lower_task_variant(element_cat);
    match coll_type {
        CollectionType::Vec => quote! {
            #category::#label(value) => {
                __tasks.push(__MettailDovetailLowerTask::Assemble {
                    op: #enum_id::#op,
                    child_count: value.len(),
                    canonicalize: false,
                });
                for __element in value.iter().rev() {
                    __tasks.push(__MettailDovetailLowerTask::#visit(
                        __element as *const _,
                    ));
                }
            }
        },
        CollectionType::HashBag => quote! {
            #category::#label(value) => {
                let __elements: ::std::vec::Vec<_> = value.iter_elements().collect();
                __tasks.push(__MettailDovetailLowerTask::Assemble {
                    op: #enum_id::#op,
                    child_count: __elements.len(),
                    canonicalize: true,
                });
                for __element in __elements.into_iter().rev() {
                    __tasks.push(__MettailDovetailLowerTask::#visit(
                        __element as *const _,
                    ));
                }
            }
        },
        CollectionType::HashSet => quote! {
            #category::#label(value) => {
                let __elements: ::std::vec::Vec<_> = value.iter().collect();
                __tasks.push(__MettailDovetailLowerTask::Assemble {
                    op: #enum_id::#op,
                    child_count: __elements.len(),
                    canonicalize: true,
                });
                for __element in __elements.into_iter().rev() {
                    __tasks.push(__MettailDovetailLowerTask::#visit(
                        __element as *const _,
                    ));
                }
            }
        },
        CollectionType::HashMap => {
            layout
                .sentinels()
                .collection_pair(mettail_grammar_core::CollectionKind::Map, element_cat)
                .expect("structural Map literal must have one checked pair sentinel");
            let pair = collection_pair_variant_ident(
                mettail_grammar_core::CollectionKind::Map,
                element_cat,
            );
            quote! {
                #category::#label(value) => {
                    let __entries: ::std::vec::Vec<_> = value.iter().collect();
                    __tasks.push(__MettailDovetailLowerTask::Assemble {
                        op: #enum_id::#op,
                        child_count: __entries.len(),
                        canonicalize: true,
                    });
                    for (__key, __value) in __entries.into_iter().rev() {
                        __tasks.push(__MettailDovetailLowerTask::Assemble {
                            op: #enum_id::#pair,
                            child_count: 2,
                            canonicalize: false,
                        });
                        __tasks.push(__MettailDovetailLowerTask::#visit(
                            __value as *const _,
                        ));
                        __tasks.push(__MettailDovetailLowerTask::#visit(
                            __key as *const _,
                        ));
                    }
                }
            }
        },
        CollectionType::PathMap => {
            layout
                .sentinels()
                .pathmap_mode(element_cat)
                .expect("structural PathMap literal must have one checked mode sentinel");
            layout
                .sentinels()
                .pathmap_pair(element_cat)
                .expect("structural PathMap literal must have one checked pair sentinel");
            let mode = pathmap_mode_variant_ident(element_cat);
            let pair = pathmap_pair_variant_ident(element_cat);
            quote! {
                #category::#label(value) => {
                    let __entries: ::std::vec::Vec<_> = value.iter().collect();
                    let __mode = match value.mode() {
                        ::mettail_runtime::PathMapMode::Empty => 0u8,
                        ::mettail_runtime::PathMapMode::Set => 1u8,
                        ::mettail_runtime::PathMapMode::Map => 2u8,
                    };
                    __tasks.push(__MettailDovetailLowerTask::AssemblePathMap {
                        op: #enum_id::#op,
                        child_count: __entries.len() + 1usize,
                    });
                    for __entry in __entries.into_iter().rev() {
                        match __entry {
                            ::mettail_runtime::PathMapEntryRef::Set(__key) => {
                                __tasks.push(__MettailDovetailLowerTask::#visit(
                                    __key as *const _,
                                ));
                            },
                            ::mettail_runtime::PathMapEntryRef::Map(__key, __value) => {
                                __tasks.push(__MettailDovetailLowerTask::Assemble {
                                    op: #enum_id::#pair,
                                    child_count: 2,
                                    canonicalize: false,
                                });
                                __tasks.push(__MettailDovetailLowerTask::#visit(
                                    __value as *const _,
                                ));
                                __tasks.push(__MettailDovetailLowerTask::#visit(
                                    __key as *const _,
                                ));
                            },
                        }
                    }
                    // LIFO: the mode is visited first and remains the first
                    // ordered child while only the entry suffix is sorted.
                    __tasks.push(__MettailDovetailLowerTask::Leaf(
                        #enum_id::#mode(__mode),
                    ));
                }
            }
        },
    }
}

/// Lower a recursive native zipper through the same closed PathMap product as
/// the canonical semantic image. The ordered root children are mode, an
/// exact-key-canonical entry suffix, and the uninterpreted focus bytes.
fn recursive_native_lowering_typed(
    enum_id: &Ident,
    category: &Ident,
    label: &Ident,
    carrier: &NativeRecursiveCarrier,
    layout: &SemanticAdapterLayout,
) -> TokenStream {
    let op = op_variant_ident(category, label);
    let key_category = carrier.key_category();
    let value_category = carrier.value_category();
    layout
        .sentinels()
        .native_pathmap_mode(key_category, value_category)
        .expect("recursive native carrier must have one checked mode sentinel");
    layout
        .sentinels()
        .native_pathmap_pair(key_category, value_category)
        .expect("recursive native carrier must have one checked pair sentinel");
    assert!(
        layout.has_byte_string(),
        "recursive native carrier must have one checked byte-string sentinel",
    );
    let mode = native_pathmap_mode_variant_ident(key_category, value_category);
    let pair = native_pathmap_pair_variant_ident(key_category, value_category);
    let visit_key = lower_task_variant(key_category);
    let visit_value = lower_task_variant(value_category);
    let pathmap = carrier.pathmap_ref(&quote! { value });
    let focus = carrier.focus_ref(&quote! { value });

    quote! {
        #category::#label(value) => {
            let __pathmap = #pathmap;
            let __entries: ::std::vec::Vec<_> = __pathmap.iter().collect();
            let __mode = match __pathmap.mode() {
                ::mettail_runtime::PathMapMode::Empty => 0u8,
                ::mettail_runtime::PathMapMode::Set => 1u8,
                ::mettail_runtime::PathMapMode::Map => 2u8,
            };
            __tasks.push(__MettailDovetailLowerTask::AssembleNativePathMap {
                op: #enum_id::#op,
                entry_count: __entries.len(),
            });
            // LIFO: focus is emitted after every entry but remains the final
            // ordered child, outside the canonicalized entry suffix.
            __tasks.push(__MettailDovetailLowerTask::Leaf(
                #enum_id::FieldBytes((#focus).clone()),
            ));
            for __entry in __entries.into_iter().rev() {
                let __key = __entry.key();
                if let ::core::option::Option::Some(__value) = __entry.value() {
                    __tasks.push(__MettailDovetailLowerTask::Assemble {
                        op: #enum_id::#pair,
                        child_count: 2,
                        canonicalize: false,
                    });
                    __tasks.push(__MettailDovetailLowerTask::#visit_value(
                        __value as *const _,
                    ));
                    __tasks.push(__MettailDovetailLowerTask::#visit_key(
                        __key as *const _,
                    ));
                } else {
                    __tasks.push(__MettailDovetailLowerTask::#visit_key(
                        __key as *const _,
                    ));
                }
            }
            __tasks.push(__MettailDovetailLowerTask::Leaf(
                #enum_id::#mode(__mode),
            ));
        }
    }
}

/// Typed analogue of [`super::field_child_expr`]: a category field recurses; everything else
/// becomes a `FieldOpaque`/`FieldNone` spine sentinel (field-level collections included — see
/// the module doc; Rholang's reconstructable collections are categories, not fields).
fn field_child_expr_typed(
    enum_id: &Ident,
    layout: &SemanticFieldLayout,
    field_var: &Ident,
) -> TokenStream {
    let field_index = layout.index();
    let field = layout.field();
    let child_task = format_ident!("Visit{}", field.category);
    match layout.projection() {
        SemanticFieldProjection::Opaque => {
            let leaf = opaque_leaf_typed(enum_id, quote! { #field_var });
            quote! { __tasks.push(__MettailDovetailLowerTask::Leaf(#leaf)); }
        },
        SemanticFieldProjection::Withheld => {
            let leaf = withheld_leaf_typed(enum_id, &field.category, quote! { #field_var });
            quote! { __tasks.push(__MettailDovetailLowerTask::Leaf(#leaf)); }
        },
        SemanticFieldProjection::TokenText => {
            let leaf = token_text_leaf_typed(enum_id, quote! { #field_var });
            quote! { __tasks.push(__MettailDovetailLowerTask::Leaf(#leaf)); }
        },
        SemanticFieldProjection::OptionalTokenText => {
            let leaf = token_text_leaf_typed(enum_id, quote! { __value });
            let none = field_none_typed(enum_id, field_index);
            quote! {
                match #field_var.as_ref() {
                    Some(__value) => __tasks.push(__MettailDovetailLowerTask::Leaf(#leaf)),
                    None => __tasks.push(__MettailDovetailLowerTask::Leaf(#none)),
                }
            }
        },
        SemanticFieldProjection::OptionalOpaque => {
            let leaf = opaque_leaf_typed(enum_id, quote! { __value });
            let none = field_none_typed(enum_id, field_index);
            quote! {
                match #field_var.as_ref() {
                    Some(__value) => __tasks.push(__MettailDovetailLowerTask::Leaf(#leaf)),
                    None => __tasks.push(__MettailDovetailLowerTask::Leaf(#none)),
                }
            }
        },
        SemanticFieldProjection::OptionalOrderedSequence => {
            let leaf = match resolve_field_carrier(enum_id, &field.category, layout.projection()) {
                ResolvedCarrier::OrderedSeq(seq) => {
                    ordered_seq_leaf_typed(&seq, quote! { __values })
                },
                ResolvedCarrier::AcBag(_) | ResolvedCarrier::Opaque => {
                    opaque_leaf_typed(enum_id, quote! { __values })
                },
            };
            let none = field_none_typed(enum_id, field_index);
            quote! {
                match #field_var.as_ref() {
                    Some(__values) => {
                        __tasks.push(__MettailDovetailLowerTask::Leaf(#leaf));
                    },
                    None => __tasks.push(__MettailDovetailLowerTask::Leaf(#none)),
                }
            }
        },
        SemanticFieldProjection::Child => quote! {
            __tasks.push(__MettailDovetailLowerTask::#child_task(
                #field_var.as_ref() as *const _,
            ));
        },
        SemanticFieldProjection::OptionalChild => {
            let none = field_none_typed(enum_id, field_index);
            quote! {
                match #field_var.as_ref() {
                    Some(__inner) => __tasks.push(__MettailDovetailLowerTask::#child_task(
                        __inner.as_ref() as *const _,
                    )),
                    None => __tasks.push(__MettailDovetailLowerTask::Leaf(#none)),
                }
            }
        },
        SemanticFieldProjection::OrderedSequence => {
            let leaf = match resolve_field_carrier(enum_id, &field.category, layout.projection()) {
                ResolvedCarrier::OrderedSeq(seq) => {
                    ordered_seq_leaf_typed(&seq, quote! { #field_var })
                },
                ResolvedCarrier::AcBag(_) | ResolvedCarrier::Opaque => {
                    opaque_leaf_typed(enum_id, quote! { #field_var })
                },
            };
            quote! { __tasks.push(__MettailDovetailLowerTask::Leaf(#leaf)); }
        },
    }
}

fn regular_arm_typed(
    enum_id: &Ident,
    category: &Ident,
    label: &Ident,
    fields: &[FieldInfo],
    layout: &SemanticVariantLayout,
) -> TokenStream {
    debug_assert_eq!(fields.len(), layout.fields().len());
    let variant = op_variant_ident(category, label);
    let field_vars: Vec<Ident> = (0..fields.len())
        .map(|i| format_ident!("field_{i}"))
        .collect();
    let child_tasks: Vec<TokenStream> = fields
        .iter()
        .zip(field_vars.iter())
        .enumerate()
        .rev()
        .map(|(i, (_field, var))| field_child_expr_typed(enum_id, &layout.fields()[i], var))
        .collect();
    let child_count = fields.len();
    quote! {
        #category::#label(#(#field_vars),*) => {
            __tasks.push(__MettailDovetailLowerTask::Assemble {
                op: #enum_id::#variant,
                child_count: #child_count,
                canonicalize: false,
            });
            #(#child_tasks)*
        }
    }
}

fn binder_arm_typed(
    enum_id: &Ident,
    category: &Ident,
    body_category: &Ident,
    label: &Ident,
    pre_scope_fields: &[FieldInfo],
    multi: bool,
    layout: &SemanticVariantLayout,
) -> TokenStream {
    debug_assert_eq!(pre_scope_fields.len(), layout.fields().len());
    let variant = op_variant_ident(category, label);
    let pre_vars: Vec<Ident> = (0..pre_scope_fields.len())
        .map(|i| format_ident!("field_{i}"))
        .collect();
    let scope_var = format_ident!("scope");
    let pre_child_tasks: Vec<TokenStream> = pre_scope_fields
        .iter()
        .zip(pre_vars.iter())
        .enumerate()
        .rev()
        .map(|(i, (_field, var))| field_child_expr_typed(enum_id, &layout.fields()[i], var))
        .collect();
    // The scope codomain is an independent typed category.  Deriving this
    // task from the enclosing constructor category permits a cross-category
    // body pointer to be dereferenced as the wrong generated enum type.
    let body_task = format_ident!("Visit{}", body_category);
    // (FIX-A) anonymous arity-only binder marker — see `super::binder_arm`.
    let binder_child = if multi {
        quote! { #enum_id::BinderArity(#scope_var.unsafe_pattern().len() as u32) }
    } else {
        quote! { #enum_id::BinderArity(1u32) }
    };
    let child_count = pre_scope_fields.len() + 2;
    quote! {
        #category::#label(#(#pre_vars,)* #scope_var) => {
            __tasks.push(__MettailDovetailLowerTask::Assemble {
                op: #enum_id::#variant,
                child_count: #child_count,
                canonicalize: false,
            });
            __tasks.push(__MettailDovetailLowerTask::#body_task(
                #scope_var.unsafe_body().as_ref() as *const _,
            ));
            __tasks.push(__MettailDovetailLowerTask::Leaf(#binder_child));
            #(#pre_child_tasks)*
        }
    }
}

fn lower_task_variant(category: &Ident) -> Ident {
    format_ident!("Visit{}", category)
}

fn lower_handler_name(category: &Ident) -> Ident {
    format_ident!("__mettail_dovetail_lower_handle_{}", super::to_snake(&category.to_string()))
}

/// Generate the one pooled PDA shared by every typed category lowering in an assembly scope.
/// `Leaf` and `Assemble` retain the recursive reference's exact postorder e-graph insertion;
/// category pointers are borrowed from the live root and drained synchronously.
pub(crate) fn lowering_pda_support(
    language: &LanguageDef,
    layout: &SemanticAdapterLayout,
) -> TokenStream {
    let enum_id = op_enum_ident(language);
    let visits: Vec<TokenStream> = layout
        .categories()
        .iter()
        .map(|category_layout| {
            let category = category_layout.category();
            let visit = lower_task_variant(category);
            quote! { #visit(*const #category) }
        })
        .collect();
    let dispatch: Vec<TokenStream> = layout
        .categories()
        .iter()
        .map(|category_layout| {
            let category = category_layout.category();
            let visit = lower_task_variant(category);
            let handler = lower_handler_name(category);
            quote! {
                __MettailDovetailLowerTask::#visit(__ptr) => {
                    // SAFETY: all pointers originate below one live root borrow and this
                    // synchronous engine drains the task stack before that borrow can end.
                    #handler(unsafe { &*__ptr }, &mut __tasks);
                }
            }
        })
        .collect();

    quote! {
        enum __MettailDovetailLowerTask {
            #(#visits,)*
            Leaf(#enum_id),
            Assemble {
                op: #enum_id,
                child_count: usize,
                canonicalize: bool,
            },
            AssemblePathMap {
                op: #enum_id,
                child_count: usize,
            },
            AssembleNativePathMap {
                op: #enum_id,
                entry_count: usize,
            },
        }

        ::std::thread_local! {
            static __METTAIL_DOVETAIL_LOWER_TASK_POOL:
                ::std::cell::Cell<::std::vec::Vec<__MettailDovetailLowerTask>> =
                    const { ::std::cell::Cell::new(::std::vec::Vec::new()) };
            static __METTAIL_DOVETAIL_LOWER_VALUE_POOL:
                ::std::cell::Cell<::std::vec::Vec<(
                    ::dovetail::egraph::EClassId,
                    ::dovetail::key::ContentKey,
                )>> =
                    const { ::std::cell::Cell::new(::std::vec::Vec::new()) };
        }

        fn __mettail_dovetail_lower_run(
            eg: &mut ::dovetail::egraph::EGraph<#enum_id>,
            __seed: __MettailDovetailLowerTask,
        ) -> ::dovetail::egraph::EClassId {
            let mut __tasks = __METTAIL_DOVETAIL_LOWER_TASK_POOL.with(|__pool| __pool.take());
            let mut __values = __METTAIL_DOVETAIL_LOWER_VALUE_POOL.with(|__pool| __pool.take());
            __tasks.clear();
            __values.clear();
            __tasks.push(__seed);

            while let ::core::option::Option::Some(__task) = __tasks.pop() {
                match __task {
                    #(#dispatch)*
                    __MettailDovetailLowerTask::Leaf(__op) => {
                        let __key = ::dovetail::key::ContentKey::tree(
                            &__op,
                            ::std::vec::Vec::new(),
                        );
                        let __class = eg.add(::dovetail::egraph::ENode::leaf(__op));
                        __values.push((__class, __key));
                    },
                    __MettailDovetailLowerTask::Assemble {
                        op,
                        child_count,
                        canonicalize,
                    } => {
                        let __first = __values.len().checked_sub(child_count).expect(
                            "generated Dovetail lowering PDA lost a child e-class",
                        );
                        let mut __children = __values.split_off(__first);
                        if canonicalize {
                            __children.sort_by(|__left, __right| __left.1.cmp(&__right.1));
                        }
                        let mut __child_classes = ::std::vec::Vec::with_capacity(child_count);
                        let mut __child_keys = ::std::vec::Vec::with_capacity(child_count);
                        for (__class, __key) in __children {
                            __child_classes.push(__class);
                            __child_keys.push(__key);
                        }
                        let __key = ::dovetail::key::ContentKey::tree(&op, __child_keys);
                        let __class = eg.add(::dovetail::egraph::ENode::new(op, __child_classes));
                        __values.push((__class, __key));
                    },
                    __MettailDovetailLowerTask::AssemblePathMap { op, child_count } => {
                        let __first = __values.len().checked_sub(child_count).expect(
                            "generated PathMap lowering PDA lost a structural child",
                        );
                        let mut __children = __values.split_off(__first);
                        assert!(
                            !__children.is_empty(),
                            "generated PathMap lowering requires a mode child",
                        );
                        __children[1..].sort_by(|__left, __right| __left.1.cmp(&__right.1));
                        let mut __child_classes = ::std::vec::Vec::with_capacity(child_count);
                        let mut __child_keys = ::std::vec::Vec::with_capacity(child_count);
                        for (__class, __key) in __children {
                            __child_classes.push(__class);
                            __child_keys.push(__key);
                        }
                        let __key = ::dovetail::key::ContentKey::tree(&op, __child_keys);
                        let __class = eg.add(::dovetail::egraph::ENode::new(op, __child_classes));
                        __values.push((__class, __key));
                    },
                    __MettailDovetailLowerTask::AssembleNativePathMap { op, entry_count } => {
                        let __child_count = entry_count.checked_add(2).expect(
                            "generated native PathMap child count overflowed",
                        );
                        let __first = __values.len().checked_sub(__child_count).expect(
                            "generated native PathMap lowering PDA lost a structural child",
                        );
                        let mut __children = __values.split_off(__first);
                        let __entry_end = 1usize.checked_add(entry_count).expect(
                            "generated native PathMap entry boundary overflowed",
                        );
                        __children[1..__entry_end]
                            .sort_by(|__left, __right| __left.1.cmp(&__right.1));
                        let mut __child_classes =
                            ::std::vec::Vec::with_capacity(__child_count);
                        let mut __child_keys = ::std::vec::Vec::with_capacity(__child_count);
                        for (__class, __key) in __children {
                            __child_classes.push(__class);
                            __child_keys.push(__key);
                        }
                        let __key = ::dovetail::key::ContentKey::tree(&op, __child_keys);
                        let __class = eg.add(::dovetail::egraph::ENode::new(op, __child_classes));
                        __values.push((__class, __key));
                    },
                }
            }

            assert_eq!(
                __values.len(),
                1,
                "generated Dovetail lowering PDA must produce exactly one root e-class",
            );
            let (__root, __root_key) =
                __values.pop().expect("root-result count checked above");
            drop(__root_key);
            __tasks.clear();
            __values.clear();
            __METTAIL_DOVETAIL_LOWER_TASK_POOL.with(|__pool| __pool.set(__tasks));
            __METTAIL_DOVETAIL_LOWER_VALUE_POOL.with(|__pool| __pool.set(__values));
            __root
        }
    }
}

/// Generate the typed per-category lowering `__mettail_dovetail_add_<cat>(eg, term) -> EClassId`
/// over `EGraph<L>` (the same fn name as the String version; only one is emitted per language).
pub(crate) fn category_lowering_typed(
    language: &LanguageDef,
    category: &Ident,
    layout: &SemanticAdapterLayout,
) -> TokenStream {
    let enum_id = op_enum_ident(language);
    let fn_name = category_lowering_fn(category);
    let handler_name = lower_handler_name(category);
    let seed_task = lower_task_variant(category);
    let Some(category_layout) = layout.category(category) else {
        let message = format!("semantic adapter layout is missing category `{category}`");
        return quote! { compile_error!(#message); };
    };
    let arms: Vec<TokenStream> = category_layout
        .variants()
        .iter()
        .map(|variant_layout| match variant_layout.kind().clone() {
            // ★ #141 G5 — see `VariantKind::Refused`.
            VariantKind::Refused { message, .. } => quote! { compile_error!(#message); },
            VariantKind::Var { label } | VariantKind::Literal { label } => {
                let v = op_variant_ident(category, &label);
                quote! {
                    #category::#label(value) => {
                        __tasks.push(__MettailDovetailLowerTask::Leaf(
                            #enum_id::#v(value.clone()),
                        ));
                    }
                }
            },
            VariantKind::CollectionLiteral { label, element_cat, coll_type } => {
                collection_literal_lowering_typed(
                    &enum_id,
                    category,
                    &label,
                    &element_cat,
                    &coll_type,
                    layout,
                )
            },
            VariantKind::RecursiveNativeLiteral { label, carrier } => {
                recursive_native_lowering_typed(&enum_id, category, &label, &carrier, layout)
            },
            VariantKind::Nullary { label } => {
                let v = op_variant_ident(category, &label);
                quote! {
                    #category::#label => {
                        __tasks.push(__MettailDovetailLowerTask::Leaf(#enum_id::#v));
                    }
                }
            },
            VariantKind::Regular { label, fields } => {
                regular_arm_typed(&enum_id, category, &label, &fields, variant_layout)
            },
            VariantKind::Collection { label, element_cat, .. } => {
                let v = op_variant_ident(category, &label);
                match resolve_variant_carrier(
                    &enum_id,
                    category,
                    &label,
                    &element_cat,
                    variant_layout
                        .collection_projection()
                        .expect("collection variant must have a checked collection projection"),
                ) {
                    ResolvedCarrier::AcBag(op) => {
                        let body = ac_bag_lowering_typed(&op, &element_cat, quote! { values });
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
                                __tasks.push(__MettailDovetailLowerTask::Assemble {
                                    op: #enum_id::#v,
                                    child_count: 1,
                                    canonicalize: false,
                                });
                                __tasks.push(__MettailDovetailLowerTask::Leaf(#leaf));
                            }
                        }
                    },
                    ResolvedCarrier::Opaque => {
                        let leaf = opaque_leaf_typed(&enum_id, quote! { values });
                        quote! {
                            #category::#label(values) => {
                                __tasks.push(__MettailDovetailLowerTask::Leaf(#leaf));
                            }
                        }
                    },
                }
            },
            VariantKind::Binder { label, pre_scope_fields, body_cat, .. } => binder_arm_typed(
                &enum_id,
                category,
                &body_cat,
                &label,
                &pre_scope_fields,
                false,
                variant_layout,
            ),
            VariantKind::MultiBinder { label, pre_scope_fields, body_cat, .. } => binder_arm_typed(
                &enum_id,
                category,
                &body_cat,
                &label,
                &pre_scope_fields,
                true,
                variant_layout,
            ),
        })
        .collect();

    quote! {
        fn #handler_name(
            term: &#category,
            __tasks: &mut ::std::vec::Vec<__MettailDovetailLowerTask>,
        ) {
            match term {
                #(#arms),*
            }
        }

        pub(super) fn #fn_name(
            eg: &mut ::dovetail::egraph::EGraph<#enum_id>,
            term: &#category,
        ) -> ::dovetail::egraph::EClassId {
            __mettail_dovetail_lower_run(
                eg,
                __MettailDovetailLowerTask::#seed_task(term as *const _),
            )
        }
    }
}

#[cfg(test)]
mod structural_collection_literal_tests {
    use super::*;

    fn compact(tokens: TokenStream) -> String {
        tokens.to_string().split_whitespace().collect()
    }

    #[test]
    fn lowering_emits_exact_value_pair_and_pathmap_shapes() {
        let language = crate::gen::collection_literal_language_for_tests();
        let layout = SemanticAdapterLayout::derive(&language).expect("semantic layout");

        let list: Ident = syn::parse_str("List").expect("identifier");
        let list_tokens = compact(category_lowering_typed(&language, &list, &layout));
        assert!(list_tokens.contains("List::ListLit(value)"));
        assert!(list_tokens.contains("canonicalize:false"));
        assert!(list_tokens.contains("VisitProc(__elementas*const_,)"));
        assert!(!list_tokens.contains("List_ListLit(value.clone())"));

        for category_name in ["Bag", "Set"] {
            let category: Ident = syn::parse_str(category_name).expect("identifier");
            let tokens = compact(category_lowering_typed(&language, &category, &layout));
            assert!(tokens.contains("canonicalize:true"));
            assert!(tokens.contains("VisitProc(__elementas*const_,)"));
        }

        let map: Ident = syn::parse_str("Map").expect("identifier");
        let map_tokens = compact(category_lowering_typed(&language, &map, &layout));
        assert!(map_tokens.contains("CollectionPairMapProc"));
        assert!(map_tokens.contains("child_count:2usize") || map_tokens.contains("child_count:2"));
        assert!(map_tokens.contains("canonicalize:true"));

        let pathmap: Ident = syn::parse_str("Pathmap").expect("identifier");
        let pathmap_tokens = compact(category_lowering_typed(&language, &pathmap, &layout));
        assert!(pathmap_tokens.contains("AssemblePathMap"));
        assert!(pathmap_tokens.contains("PathMapModeProc(__mode)"));
        assert!(pathmap_tokens.contains("PathMapPairProc"));
        assert!(pathmap_tokens.contains("PathMapMode::Empty=>0u8"));
        assert!(pathmap_tokens.contains("PathMapMode::Set=>1u8"));
        assert!(pathmap_tokens.contains("PathMapMode::Map=>2u8"));

        let support = compact(lowering_pda_support(&language, &layout));
        assert!(support.contains("ContentKey::tree"));
        assert!(!support.contains("canonical_class_key"));
    }

    #[test]
    fn cross_category_binder_uses_its_declared_body_visit_type() {
        let language: LanguageDef = syn::parse_str(
            r#"
                name: CrossCategoryBinder,
                types { Wrapper Proc Name },
                terms {
                    Nil . |- "0" : Proc;
                    NameLit . |- "n" : Name;
                    Wrap . ^x.body:[Name -> Proc]
                        |- "wrap" x "." body : Wrapper;
                },
                equations {},
                rewrites {},
            "#,
        )
        .expect("cross-category binder fixture must parse");
        let layout = SemanticAdapterLayout::derive(&language).expect("semantic layout");
        let wrapper: Ident = syn::parse_str("Wrapper").expect("identifier");
        let tokens = compact(category_lowering_typed(&language, &wrapper, &layout));
        let wrap_arm = tokens
            .split("Wrapper::Wrap(scope)=>")
            .nth(1)
            .and_then(|rest| rest.split("Wrapper::WVar").next())
            .expect("Wrap arm must be emitted before the generated variable arm");

        assert!(wrap_arm.contains("__MettailDovetailLowerTask::VisitProc("));
        assert!(
            !wrap_arm.contains("__MettailDovetailLowerTask::VisitWrapper("),
            "cross-category Wrap body was routed through Wrapper: {wrap_arm}",
        );
    }
}
