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
use super::op_enum::{
    field_withheld_variant_ident, op_enum_ident, op_variant_ident, ordered_seq_element_categories,
};
use super::withholding::{self, WithholdingSet};
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
/// `withholding`'s Theorem W1 and `macros/formal/rocq/CongruenceWithholding.v`.
///
/// ⚠ Emitted ONLY for a position some `| S ~/> T |-` declaration severs
/// (`WithholdingSet::is_severed`). No production language declares one, so every shipped
/// language's lowering is byte-identical across #195; the mechanism is pinned by the live
/// `CongruenceWithholdingDemo` fixture instead of by the corpus.
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

/// Typed analogue of [`super::field_child_expr`]: a category field recurses; everything else
/// becomes a `FieldOpaque`/`FieldNone` spine sentinel (field-level collections included — see
/// the module doc; Rholang's reconstructable collections are categories, not fields).
fn field_child_expr_typed(
    enum_id: &Ident,
    owner_label: &Ident,
    field_index: usize,
    field: &FieldInfo,
    field_var: &Ident,
    earned_seq_elements: &[Ident],
    withheld: &WithholdingSet,
) -> TokenStream {
    let child_task = format_ident!("Visit{}", field.category);
    let field_kind = NonTerminalKind::classify(&field.category.to_string());
    // ★★★ (#195) SEVERANCE — the FIRST branch, and it must be first.
    //
    // A `| S ~/> T |-` declaration says this position is NOT an evaluation context. On an
    // e-graph that can only be honoured by taking the position out of the child-e-class
    // world (Theorem W1: once two children merge, two parent e-nodes with equal canonical
    // child vectors are the SAME hashcons key, so propagation through a child position is
    // an identity the data structure IS, not a policy it applies). So instead of
    // `__mettail_dovetail_add_<cat>(eg, …)` — which would hand the field's e-class id to
    // the parent e-node — the field's VALUE travels whole inside one nullary leaf.
    //
    // Consequences, all three of them intended and all three measured by
    // `languages/tests/congruence_declaration_witness.rs`:
    //   • the matcher cannot see inside the field (a leaf has no children), so no rule
    //     fires under it;
    //   • funded 1-best extraction cannot substitute a rewritten member for it, so the
    //     reported normal form keeps the subterm as written;
    //   • reconstruction is LOSSLESS anyway, because the payload IS the value
    //     (`reconstruct::withheld_reconstruct` is a `clone()`), so a term with a withheld
    //     field still has a normal form to compare — unlike the lossy `FieldOpaque` leaf,
    //     which would have turned every such term into a stuck reconstruction.
    //
    // ⚠ Placed before the builtin/predicate/collection branches because
    // `withholding::severable` REFUSES every one of those shapes by name: reaching this
    // branch already implies a plain scalar category field, and the ordering makes the
    // implication a fact about the code rather than a claim about the classifier.
    if withheld.is_severed(owner_label, field_index) {
        let leaf = withheld_leaf_typed(enum_id, &field.category, quote! { #field_var });
        return quote! { __tasks.push(__MettailDovetailLowerTask::Leaf(#leaf)); };
    }
    if field_kind.is_builtin() {
        let leaf = opaque_leaf_typed(enum_id, quote! { #field_var });
        return quote! { __tasks.push(__MettailDovetailLowerTask::Leaf(#leaf)); };
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
                    Some(__pred) => __tasks.push(__MettailDovetailLowerTask::Leaf(#leaf)),
                    None => __tasks.push(__MettailDovetailLowerTask::Leaf(#none)),
                }
            };
        }
        if field.is_collection {
            let leaf = opaque_leaf_typed(enum_id, quote! { __values });
            let none = field_none_typed(enum_id, field_index);
            return quote! {
                match #field_var.as_ref() {
                    Some(__values) => __tasks.push(__MettailDovetailLowerTask::Leaf(#leaf)),
                    None => __tasks.push(__MettailDovetailLowerTask::Leaf(#none)),
                }
            };
        }
        let none = field_none_typed(enum_id, field_index);
        return quote! {
            match #field_var.as_ref() {
                Some(__inner) => __tasks.push(__MettailDovetailLowerTask::#child_task(
                    __inner.as_ref() as *const _,
                )),
                None => __tasks.push(__MettailDovetailLowerTask::Leaf(#none)),
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
        let leaf = match field.opaque_leaf {
            Some(OpaqueLeafKind::TokenText) => {
                token_text_leaf_typed(enum_id, quote! { #field_var })
            },
            Some(OpaqueLeafKind::GuestBody) | None => {
                opaque_leaf_typed(enum_id, quote! { #field_var })
            },
        };
        return quote! { __tasks.push(__MettailDovetailLowerTask::Leaf(#leaf)); };
    }

    if field.is_collection {
        // (#101) An ORDERED (`Vec`) collection field takes the LABELLED, INVERTIBLE sequence
        // leaf; every other container keeps the lossy `FieldOpaque`. See
        // [`carrier_handle::resolve_field_carrier`] for why a `HashBag` FIELD stays opaque on
        // this path (unchanged behaviour — the typed path AC-lowers only whole-constructor
        // collections).
        let leaf = match resolve_field_carrier(
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
        return quote! { __tasks.push(__MettailDovetailLowerTask::Leaf(#leaf)); };
    }

    quote! {
        __tasks.push(__MettailDovetailLowerTask::#child_task(
            #field_var.as_ref() as *const _,
        ));
    }
}

fn regular_arm_typed(
    enum_id: &Ident,
    category: &Ident,
    label: &Ident,
    fields: &[FieldInfo],
    earned_seq_elements: &[Ident],
    withheld: &WithholdingSet,
) -> TokenStream {
    let variant = op_variant_ident(category, label);
    let field_vars: Vec<Ident> = (0..fields.len())
        .map(|i| format_ident!("field_{i}"))
        .collect();
    let child_tasks: Vec<TokenStream> = fields
        .iter()
        .zip(field_vars.iter())
        .enumerate()
        .rev()
        .map(|(i, (field, var))| {
            field_child_expr_typed(enum_id, label, i, field, var, earned_seq_elements, withheld)
        })
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
    label: &Ident,
    pre_scope_fields: &[FieldInfo],
    multi: bool,
    earned_seq_elements: &[Ident],
    withheld: &WithholdingSet,
) -> TokenStream {
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
        .map(|(i, (field, var))| {
            field_child_expr_typed(enum_id, label, i, field, var, earned_seq_elements, withheld)
        })
        .collect();
    let body_task = format_ident!("Visit{}", category);
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
pub(crate) fn lowering_pda_support(language: &LanguageDef) -> TokenStream {
    let enum_id = op_enum_ident(language);
    let visits: Vec<TokenStream> = language
        .types
        .iter()
        .map(|ty| {
            let category = &ty.name;
            let visit = lower_task_variant(category);
            quote! { #visit(*const #category) }
        })
        .collect();
    let dispatch: Vec<TokenStream> = language
        .types
        .iter()
        .map(|ty| {
            let category = &ty.name;
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
        }

        ::std::thread_local! {
            static __METTAIL_DOVETAIL_LOWER_TASK_POOL:
                ::std::cell::Cell<::std::vec::Vec<__MettailDovetailLowerTask>> =
                    const { ::std::cell::Cell::new(::std::vec::Vec::new()) };
            static __METTAIL_DOVETAIL_LOWER_VALUE_POOL:
                ::std::cell::Cell<::std::vec::Vec<::dovetail::egraph::EClassId>> =
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
                        __values.push(eg.add(::dovetail::egraph::ENode::leaf(__op)));
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
                            __children.sort_by_cached_key(|__child| {
                                eg.canonical_class_key(*__child)
                            });
                        }
                        __values.push(eg.add(::dovetail::egraph::ENode::new(op, __children)));
                    },
                }
            }

            assert_eq!(
                __values.len(),
                1,
                "generated Dovetail lowering PDA must produce exactly one root e-class",
            );
            let __root = __values.pop().expect("root-result count checked above");
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
pub(crate) fn category_lowering_typed(language: &LanguageDef, category: &Ident) -> TokenStream {
    let enum_id = op_enum_ident(language);
    let fn_name = category_lowering_fn(category);
    let handler_name = lower_handler_name(category);
    let seed_task = lower_task_variant(category);
    // (#101) The element categories that have a `FieldSeq*` variant. Computed ONCE per
    // category lowering and threaded to every field site, so a leaf can never name a variant
    // the enum does not have.
    let earned_seq_elements = ordered_seq_element_categories(language);
    // ★ (#195) The severed-position set. Computed ONCE per category lowering and threaded
    // to every field site, from the SAME derivation `op_enum` and `reconstruct` read, so a
    // severed leaf can never name a variant the enum does not have.
    let withheld = withholding::classify_withholdings(language);
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
                        __tasks.push(__MettailDovetailLowerTask::Leaf(
                            #enum_id::#v(value.clone()),
                        ));
                    }
                }
            },
            VariantKind::Nullary { label } => {
                let v = op_variant_ident(category, &label);
                quote! {
                    #category::#label => {
                        __tasks.push(__MettailDovetailLowerTask::Leaf(#enum_id::#v));
                    }
                }
            },
            VariantKind::Regular { label, fields } => regular_arm_typed(
                &enum_id,
                category,
                &label,
                &fields,
                &earned_seq_elements,
                &withheld,
            ),
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
            VariantKind::Binder { label, pre_scope_fields, .. } => binder_arm_typed(
                &enum_id,
                category,
                &label,
                &pre_scope_fields,
                false,
                &earned_seq_elements,
                &withheld,
            ),
            VariantKind::MultiBinder { label, pre_scope_fields, .. } => binder_arm_typed(
                &enum_id,
                category,
                &label,
                &pre_scope_fields,
                true,
                &earned_seq_elements,
                &withheld,
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
