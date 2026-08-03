//! Step B of the Dovetail native-fold reduction work (Increment 2): the per-language
//! **typed op-enum** carried by the e-graph on the fold-bearing path.
//!
//! The production Dovetail report compiler lowers a term into `EGraph<String>`, stringifying
//! literal payloads via lossy `{:?}` Debug with no inverse back to a typed term — so a fold
//! body cannot run on the reduced children, and (a latent bug) two `Eq`-equal `Map`/`Bag`
//! values can stringify differently and fail to dedup.
//!
//! For fold-bearing languages we instead carry a generated `<Lang>DovetailOp` enum: one
//! variant per `(category, constructor)` with literal/var **payloads inline** (lossless), so
//! reconstruction is total and the fold body runs on typed children. This module emits the
//! enum, its `unsafe impl ::dovetail::key::SemanticHash` (the exact, `Eq`-agreeing e-graph
//! content key — framed discriminant + framed payload bytes), and its `Display` (the
//! runtime-report projection label).
//!
//! Step B emits the enum + impls but does NOT wire them into `dovetail_report_for` (Step F).
//! The op-enum is generic substrate; the engine (`EGraph<L>`, `Extractor`, `report`) is
//! already generic over `L` and untouched.
//!
//! Payload-type derivation MIRRORS `crate::gen::types::enums` (the AST enum generator) so the
//! op-enum payloads match the AST variant field types exactly; a divergence is a build error
//! at the Step-C lowering site, never silent.

use mettail_ast::language::{CollectionCategory, LanguageDef};
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use syn::Ident;

use crate::gen::native::NativeType;
use crate::gen::term_ops::subst::{collect_category_variants, rule_to_variant_kind, VariantKind};

/// The generated op-enum identifier for a language (e.g. `RholangDovetailOp`).
pub(crate) fn op_enum_ident(language: &LanguageDef) -> Ident {
    format_ident!("{}DovetailOp", language.name)
}

/// The op-enum variant identifier for a `(category, constructor-label)` pair, e.g.
/// `Proc_IntBinProc`, `Int_NumLit`. The `<Cat>_<Label>` shape guarantees uniqueness across
/// categories (two categories may share a constructor label only by accident; the category
/// prefix disambiguates) and lets reconstruction recover BOTH the AST enum and the variant.
pub(crate) fn op_variant_ident(category: &Ident, label: &Ident) -> Ident {
    format_ident!("{}_{}", category, label)
}

/// The element category of a collection native type (`Vec<Proc>` → `Proc`,
/// `HashBag<Proc>` → `Proc`, `HashMap<Proc, Proc>` → `Proc`): the first generic argument.
fn collection_element_type(native_type: &syn::Type) -> Option<TokenStream> {
    if let syn::Type::Path(type_path) = native_type {
        let seg = type_path.path.segments.last()?;
        if let syn::PathArguments::AngleBracketed(args) = &seg.arguments {
            if let Some(syn::GenericArgument::Type(elem)) = args.args.first() {
                return Some(quote! { #elem });
            }
        }
    }
    None
}

/// The Rust payload type the AST enum carries for a category's `Literal` variant.
///
/// MIRRORS `crate::gen::types::enums` (native: `str`→`String`, `f64`→`CanonicalFloat64`,
/// `f32`→`CanonicalFloat32`, else the native type as-is; collection: `List`→`Vec<elem>`,
/// `Bag`→`HashBag<elem>`, `Map`→`HashMapLit<elem, elem>`). Returns `None` for a category
/// with no native type (no auto-generated `Literal` variant).
fn literal_payload_type(language: &LanguageDef, category: &Ident) -> Option<TokenStream> {
    let lang_type = language.get_type(category)?;
    let native_type = lang_type.native_type.as_ref()?;

    if let Some(collection_kind) = &lang_type.collection_kind {
        let elem = collection_element_type(native_type).unwrap_or_else(|| quote! { #native_type });
        return Some(match collection_kind {
            CollectionCategory::List(_) => quote! { #native_type },
            CollectionCategory::Bag(_) | CollectionCategory::Set(_) => quote! { #native_type },
            CollectionCategory::Map(_) => {
                quote! { ::mettail_runtime::HashMapLit<#elem, #elem> }
            },
            // Set/map optionality is a homogeneous container mode, so the AST
            // carries `PathMapLit<E, E>` rather than a per-entry optional value.
            CollectionCategory::Pathmap(_) => {
                quote! { ::mettail_runtime::PathMapLit<#elem, #elem> }
            },
        });
    }

    Some(match NativeType::from_syn_type(native_type) {
        NativeType::Str => quote! { ::std::string::String },
        NativeType::Float64 => quote! { ::mettail_runtime::CanonicalFloat64 },
        NativeType::Float32 => quote! { ::mettail_runtime::CanonicalFloat32 },
        _ => quote! { #native_type },
    })
}

/// The `SemanticHash::write_content` byte-writing expression for a `Literal` payload bound as
/// `__p`, dispatched on the canonical (`Eq`-agreeing) byte form for the payload type. Integers
/// use two's-complement LE; floats and the big-numeric/fixed wrappers use their `Eq`-agreeing
/// `to_canonical_bytes` (Step A); `Vec` collections use ordered `Debug`; `Map`/`Bag` use their
/// SORTED `Display` (the fix for the `{:?}` order bug — `Display` is canonical/sorted).
fn literal_payload_write_content(language: &LanguageDef, category: &Ident) -> TokenStream {
    let lang_type = match language.get_type(category) {
        Some(t) => t,
        None => return quote! { ::dovetail::key::write_framed(out, &[]); },
    };

    if let Some(collection_kind) = &lang_type.collection_kind {
        return match collection_kind {
            // Ordered: Debug is deterministic + Eq-agreeing for an ordered Vec.
            CollectionCategory::List(_) => quote! {
                ::dovetail::key::write_framed(out, format!("{:?}", __p).as_bytes());
            },
            // Unordered: HashBag/HashMapLit Display is SORTED (Eq-agreeing); Debug is NOT.
            CollectionCategory::Bag(_)
            | CollectionCategory::Map(_)
            | CollectionCategory::Set(_)
            | CollectionCategory::Pathmap(_) => quote! {
                ::dovetail::key::write_framed(out, format!("{}", __p).as_bytes());
            },
        };
    }

    let native_type = match lang_type.native_type.as_ref() {
        Some(t) => t,
        None => return quote! { ::dovetail::key::write_framed(out, &[]); },
    };

    match NativeType::from_syn_type(native_type) {
        NativeType::Bool => quote! {
            ::dovetail::key::write_framed(out, &[if *__p { 1u8 } else { 0u8 }]);
        },
        NativeType::Str => quote! {
            ::dovetail::key::write_framed(out, __p.as_bytes());
        },
        NativeType::Float32 | NativeType::Float64 => quote! {
            ::dovetail::key::write_framed(out, &__p.to_canonical_bytes());
        },
        NativeType::CanonicalBigInt
        | NativeType::CanonicalBigRat
        | NativeType::CanonicalFixedPoint => quote! {
            ::dovetail::key::write_framed(out, &__p.to_canonical_bytes());
        },
        NativeType::Int8
        | NativeType::Int16
        | NativeType::Int32
        | NativeType::Int64
        | NativeType::Int128
        | NativeType::Isize
        | NativeType::UInt8
        | NativeType::UInt16
        | NativeType::UInt32
        | NativeType::UInt64
        | NativeType::UInt128
        | NativeType::Usize => quote! {
            ::dovetail::key::write_framed(out, &__p.to_le_bytes());
        },
        // Vec collection field used as a category native type, or any other wrapper: ordered
        // Debug (deterministic). Map/Bag are handled by the collection_kind branch above.
        _ => quote! {
            ::dovetail::key::write_framed(out, format!("{:?}", __p).as_bytes());
        },
    }
}

/// One emitted variant of the op-enum, with everything the enum/impl generators need.
struct OpVariant {
    /// `<Cat>_<Label>`.
    ident: Ident,
    /// Inline payload type, if this variant carries one (`Var`/`Literal`).
    payload: Option<TokenStream>,
    /// Stable discriminant (enumeration ordinal), framed first in `write_content`.
    disc: u32,
    /// `write_content` body for the payload (empty for payload-less variants).
    write_payload: TokenStream,
    /// `Display` rendering (mirrors the String-path label form).
    display: String,
}

/// Collect every op-enum variant for a language: one per `(category, constructor)` across all
/// categories, plus the spine sentinels (`BinderArity`, `FieldNone`, `FieldOpaque`) the
/// lowering emits for binder-arity markers and optional/opaque field slots.
///
/// ★ #141 G5 — also returns the classification REFUSALS (`VariantKind::Refused`)
/// as `compile_error!` items. A refusing classification declares no op-enum
/// variant, so without a second return value the diagnostic would have nowhere
/// to go and the build would fail instead with a cascade of "no variant named …"
/// errors pointing away from the cause. EMPTY for every grammar whose rules
/// classify, which is every shipped one.
fn collect_op_variants(language: &LanguageDef) -> (Vec<OpVariant>, Vec<TokenStream>) {
    // ★ (#195) The categories some `| S ~/> T |-` declaration severs. Computed ONCE here
    // and read below, from the SAME derivation `typed_lowering` and `reconstruct` read.
    let withheld = super::withholding::classify_withholdings(language).earned_categories();
    let mut variants = Vec::new();
    let mut refusals: Vec<TokenStream> = Vec::new();
    let mut disc: u32 = 0;
    let mut push = |ident: Ident,
                    payload: Option<TokenStream>,
                    write_payload: TokenStream,
                    display: String| {
        let v = OpVariant {
            ident,
            payload,
            disc,
            write_payload,
            display,
        };
        disc += 1;
        variants.push(v);
    };

    let lang = language.name.to_string();
    for lang_type in &language.types {
        let category = &lang_type.name;
        let cat = category.to_string();
        for variant in collect_category_variants(category, language) {
            match variant {
                // ★ #141 G5. A classification that refuses declares no op-enum
                // variant; the diagnostic is emitted beside the enum instead, so
                // the build fails with the message rather than with a cascade of
                // "no variant named …" errors. See `VariantKind::Refused`.
                VariantKind::Refused { message, .. } => {
                    refusals.push(quote! { compile_error!(#message); });
                },
                VariantKind::Var { label } => {
                    let ident = op_variant_ident(category, &label);
                    let display = format!("{lang}::{cat}::{label}");
                    push(
                        ident,
                        Some(quote! { ::mettail_runtime::OrdVar }),
                        // OrdVar Debug agrees with Eq (it includes the variable identity) and
                        // matches the String-path var key form.
                        quote! { ::dovetail::key::write_framed(out, format!("{:?}", __p).as_bytes()); },
                        display,
                    );
                },
                // Stage 0 identity — STAYS.
                VariantKind::Literal { label } | VariantKind::CollectionLiteral { label, .. } => {
                    let ident = op_variant_ident(category, &label);
                    let payload = literal_payload_type(language, category);
                    let write_payload = literal_payload_write_content(language, category);
                    let display = format!("{lang}::{cat}::{label}");
                    push(ident, payload, write_payload, display);
                },
                VariantKind::Nullary { label }
                | VariantKind::Regular { label, .. }
                | VariantKind::Collection { label, .. }
                | VariantKind::Binder { label, .. }
                | VariantKind::MultiBinder { label, .. } => {
                    let ident = op_variant_ident(category, &label);
                    let display = format!("{lang}::{cat}::{label}");
                    // Children are EClassIds (Regular/Binder) or AC bag members (Collection);
                    // the op carries only its identity (the framed discriminant).
                    push(ident, None, quote! {}, display);
                },
            }
        }
    }

    // Spine sentinels (not (cat, ctor) variants): a binder-position arity marker (FIX-A
    // alpha-canonical: contributes arity only), an absent optional field, and an opaque
    // builtin/predicate field leaf. These are leaves of the spine, never a category root.
    push(
        format_ident!("BinderArity"),
        Some(quote! { u32 }),
        quote! { ::dovetail::key::write_framed(out, &__p.to_le_bytes()); },
        "<binder-arity>".to_string(),
    );
    push(
        format_ident!("FieldNone"),
        Some(quote! { u32 }),
        quote! { ::dovetail::key::write_framed(out, &__p.to_le_bytes()); },
        "<field-none>".to_string(),
    );
    push(
        format_ident!("FieldOpaque"),
        Some(quote! { ::std::string::String }),
        quote! { ::dovetail::key::write_framed(out, __p.as_bytes()); },
        "<field-opaque>".to_string(),
    );
    // (A4) The LABELLED, INVERTIBLE token-text leaf. Appended AFTER `FieldOpaque` so no
    // existing discriminant moves — every other language's op-enum key bytes are unchanged
    // — and emitted ONLY for a language that actually has an `OpaqueLeafKind::TokenText`
    // field, so a language without one produces byte-identical output.
    //
    // ★ WHAT THIS ADDS, given the text was ALREADY in the key. `opaque_leaf_typed` writes
    // `FieldOpaque(format!("{:?}", payload))`, and for a token-text field the payload IS the
    // `String`, so `l.foo()` and `l.bar()` already hash-cons to DIFFERENT e-classes today.
    // What was missing is (i) a LABEL — `FieldOpaque` is shared with builtin ints, `Vec`
    // payloads, predicates and guest bodies, so provenance is unrecoverable — and (ii) an
    // INVERSE. This variant supplies both: the discriminant names the kind, and the payload
    // is the text VERBATIM (not `Debug`-escaped), so `reconstruct`'s
    // `__mettail_dovetail_build_token_text_d` is a total, lossless inverse with no
    // unescaping parser anywhere.
    if language_has_token_text_leaf(language) {
        push(
            format_ident!("FieldTokenText"),
            Some(quote! { ::std::string::String }),
            // The text VERBATIM. `String: Eq` is byte equality, so framed UTF-8 bytes are
            // exactly `Eq`-agreeing — the `SemanticHash` contract this enum's `unsafe impl`
            // states. (`FieldOpaque` frames `Debug` bytes for the same reason: `Debug` on a
            // `String` is injective, just lossy to invert.)
            quote! { ::dovetail::key::write_framed(out, __p.as_bytes()); },
            "<field-token-text>".to_string(),
        );
    }

    // (#101) The LABELLED, INVERTIBLE ORDERED-SEQUENCE leaf, one variant per element category
    // that actually occurs as a `Vec` element. Appended AFTER `FieldTokenText` so **no existing
    // discriminant moves** — a language with no `Vec`-bearing constructor produces byte-identical
    // output — and emitted from [`ordered_seq_element_categories`], the same derivation
    // `typed_lowering` and `reconstruct` read, so the variant, the lowering and the inverse can
    // never disagree about existence.
    //
    // ★ WHAT THIS ADDS, GIVEN THE BYTES ARE ALREADY THERE. `typed_lowering::opaque_leaf_typed`
    // writes `FieldOpaque(format!("{:?}", values))` today, and `write_content` then frames those
    // Debug bytes — so `[0,1]` and `[1,0]` ALREADY hash-cons to different e-classes. What was
    // missing is (i) a LABEL — one `FieldOpaque` discriminant is shared across `Vec` payloads,
    // builtin ints, predicates and guest bodies, so provenance is unrecoverable — and (ii) an
    // INVERSE. This supplies both, and it strictly REDUCES aliasing: each element category now
    // has its own discriminant. The payload bytes are byte-for-byte what `FieldOpaque` wrote
    // (`format!("{:?}", …)` on the same value), so the equivalence relation over collection
    // values is UNCHANGED; only the label and the inverse are new.
    //
    // ⚠ ORDERED ONLY. `HashSet`/`HashMap`/`PathMap` are NOT here: their `Debug` does not agree
    // with `Eq` (which is why the collection-LITERAL writer above routes them through sorted
    // `Display`), so there is no order to invert to. See [`super::CollectionCarrier`].
    for element_cat in ordered_seq_element_categories(language) {
        let display = format!("<field-seq-{element_cat}>");
        push(
            field_seq_variant_ident(&element_cat),
            Some(quote! { ::std::vec::Vec<#element_cat> }),
            // The ordered `Debug` of the whole `Vec` — EXACTLY the bytes `FieldOpaque` frames
            // for this same payload today. `Vec<E>: Eq` is elementwise equality in order and the
            // generated `Debug` is an in-order rendering of the same elements, so the framed
            // bytes are `Eq`-agreeing — the `SemanticHash` contract this enum's `unsafe impl`
            // states.
            quote! { ::dovetail::key::write_framed(out, format!("{:?}", __p).as_bytes()); },
            display,
        );
    }

    // ★★★ (#195) The LABELLED, INVERTIBLE **WITHHELD-POSITION** leaf, one variant per
    // category that some `| S ~/> T |-` declaration severs. Appended AFTER `FieldSeq*` so
    // **no existing discriminant moves** — a language declaring no withholding produces
    // byte-identical output, which is the change's strongest control — and emitted from
    // [`super::withholding::WithholdingSet::earned_categories`], the same derivation the
    // lowering and the inverse read, so the variant, the leaf and the inverse can never
    // disagree about existence.
    //
    // ★ WHY THIS VARIANT MUST EXIST AT ALL (Theorem W1). An e-graph's e-node identity is
    // `(operator, canonical child e-class ids)`. If a position holds a child e-class id
    // then, the moment two children merge, the two parent e-nodes become the SAME hashcons
    // key and inhabit the same e-class — so propagation through that position is not a
    // policy the engine applies, it is an identity the data structure IS. Withholding is
    // therefore realizable only by taking the position OUT of the child-e-class world: the
    // field's value travels whole, inside one nullary leaf. See
    // `dovetail/formal/rocq/theories/Lowering/CongruenceWithholding.v`.
    //
    // ⚠ THE PAYLOAD IS THE VALUE, and its content bytes are the category's own
    // ALPHA-CANONICAL `semantic_hash` write stream — not `format!("{:?}", …)`. `Debug`
    // prints a `Scope`'s raw binder names, so it distinguishes α-equivalent terms that `Eq`
    // identifies; framing `Debug` bytes for a category payload would therefore VIOLATE the
    // `SemanticHash` contract this enum's `unsafe impl` states (two values write the same
    // bytes iff they are observationally equal). `FramedSemanticKeyHasher` records the exact
    // framed stream rather than reducing it to a `u64`, so the key stays collision-free.
    for category in withheld.iter() {
        let display = format!("<field-withheld-{category}>");
        push(
            field_withheld_variant_ident(category),
            Some(quote! { ::std::sync::Arc<#category> }),
            quote! {
                let mut __hasher = ::mettail_runtime::FramedSemanticKeyHasher::default();
                __p.semantic_hash(&mut __hasher);
                ::dovetail::key::write_framed(out, &__hasher.into_key());
            },
            display,
        );
    }

    (variants, refusals)
}

/// ★ (#195) The op-enum variant identifier for the withheld-position leaf of a category:
/// `Proc` → `FieldWithheldProc`.
///
/// ⚠ Distinct from the `<Cat>_<Label>` constructor-variant form ([`op_variant_ident`]),
/// which always contains an underscore, from `FieldSeq*` ([`field_seq_variant_ident`]), and
/// from every spine sentinel (`BinderArity`, `FieldNone`, `FieldOpaque`, `FieldTokenText`)
/// — so no category can collide with an existing variant.
pub(crate) fn field_withheld_variant_ident(category: &Ident) -> Ident {
    format_ident!("FieldWithheld{}", category)
}

/// (#101) The op-enum variant identifier for the ordered-sequence leaf of an element category:
/// `Sym` → `FieldSeqSym`, `Proc` → `FieldSeqProc`.
///
/// ⚠ Distinct from the `<Cat>_<Label>` constructor-variant form ([`op_variant_ident`]), which
/// always contains an underscore, and from every spine sentinel (`BinderArity`, `FieldNone`,
/// `FieldOpaque`, `FieldTokenText`) — all of which lack the `FieldSeq` prefix. So no element
/// category can collide with an existing variant.
pub(crate) fn field_seq_variant_ident(element_cat: &Ident) -> Ident {
    format_ident!("FieldSeq{}", element_cat)
}

/// (#101) Every element category that EARNS the ordered-sequence carrier, in a DETERMINISTIC,
/// deduplicated order.
///
/// ★ THE single predicate that decides which `FieldSeq*` variants exist, read by every emitter
/// that can mention one — the enum ([`collect_op_variants`]), the lowering
/// (`typed_lowering::field_child_expr_typed` / the `Collection` arm), and the inverse
/// (`reconstruct::ordered_seq_reconstruct`) — so the three can never disagree about existence.
/// The carrier is a property of the ELEMENT CATEGORY, not of an individual field: once a
/// category earns one, every `Vec` of it in the language uses it, which is what keeps the three
/// emitters consistent by construction rather than by three matching conditions.
///
/// ★★ EARNED FROM **DECLARED** RULES (`language.terms` via
/// [`crate::gen::term_ops::subst::rule_to_variant_kind`]), in exactly the three positions the
/// typed lowering emits a sequence leaf at:
///
///  1. a NON-OPTIONAL `Vec` field of a `Regular` constructor;
///  2. a NON-OPTIONAL `Vec` field in a `Binder`/`MultiBinder`'s pre-scope fields;
///  3. a `VariantKind::Collection` constructor whose container is `Vec`.
///
/// ⚠ WHY DECLARED RULES AND NOT `collect_category_variants` — MEASURED, NOT STYLISTIC.
/// `collect_category_variants` additionally synthesizes the higher-order-logic application
/// forms `MApply<Domain>(Arc<Cat>, Vec<Domain>)` for every pair `compute_hol_domain_pairs`
/// flags. Those have NO grammar rule, NO surface syntax, and are never a fold operand, so a
/// labelled carrier buys them nothing — and giving each its own `Vec<Domain>` payload adds one
/// nesting level per CATEGORY to the op enum's type graph. Measured on Rholang that is 15
/// synthesized domains beside 4 declared ones, and it pushes auto-trait resolution for
/// `static … OnceLock<CompiledRuleSet<RholangDovetailOp>>` over the recursion limit:
/// `E0275: overflow evaluating the requirement Arc<WriteZipperLit>: Send`, reproducibly, in the
/// integration-test compilation unit. Restricting the set to declared rules keeps every one of
/// those synthesized fields on the `FieldOpaque` leaf they already used — zero behavioural
/// change for them, since they were `NotInvertible` before and stay so.
///
/// ⚠ OPTIONAL collection fields are EXCLUDED, deliberately: `field_child_expr_typed` keeps them
/// on the lossy `FieldOpaque` leaf (an absent collection is a `FieldNone` sentinel, and #94
/// found zero corpus instances of `#opt(xs:Vec(T))`), so admitting them here would emit a
/// variant nothing writes and an inverse nothing calls.
pub(crate) fn ordered_seq_element_categories(language: &LanguageDef) -> Vec<Ident> {
    fn ordered_field_element(field: &crate::gen::term_ops::subst::FieldInfo) -> Option<Ident> {
        if field.is_optional || !field.is_collection {
            return None;
        }
        match super::collection_carrier(field.coll_type.as_ref()) {
            super::CollectionCarrier::OrderedSeq => Some(field.category.clone()),
            super::CollectionCarrier::AcBag | super::CollectionCarrier::Opaque => None,
        }
    }

    let mut out: Vec<Ident> = Vec::new();
    let mut push_unique = |cat: Ident| {
        if !out.iter().any(|seen| *seen == cat) {
            out.push(cat);
        }
    };
    for rule in &language.terms {
        match rule_to_variant_kind(rule, language) {
            // ★ #141 G5. This walk collects the element CATEGORIES a lowering
            // needs; a rule whose classification refuses contributes none, and
            // the refusal itself is emitted by `op_enum_variants` from the same
            // classification. See `VariantKind::Refused`.
            VariantKind::Refused { .. } => {},
            VariantKind::Regular { fields, .. } => {
                for cat in fields.iter().filter_map(ordered_field_element) {
                    push_unique(cat);
                }
            },
            VariantKind::Binder { pre_scope_fields, .. }
            | VariantKind::MultiBinder { pre_scope_fields, .. } => {
                for cat in pre_scope_fields.iter().filter_map(ordered_field_element) {
                    push_unique(cat);
                }
            },
            VariantKind::Collection { element_cat, ref coll_type, .. } => {
                if super::collection_carrier(Some(coll_type))
                    == super::CollectionCarrier::OrderedSeq
                {
                    push_unique(element_cat);
                }
            },
            VariantKind::Var { .. }
            | VariantKind::Literal { .. }
            | VariantKind::CollectionLiteral { .. }
            | VariantKind::Nullary { .. } => {},
        }
    }
    out
}

/// Whether ANY constructor of `language` carries an [`OpaqueLeafKind::TokenText`] field — a
/// `v@Tok` token-text capture or an `m:Ident` mid-rule parameter (both stamp the same kind;
/// see `FieldInfo::opaque_leaf`).
///
/// ★ This is THE single predicate that decides whether the `FieldTokenText` op-enum variant
/// exists, and it is therefore read by every emitter that can mention it — the enum
/// ([`collect_op_variants`]), the inverse (`reconstruct::token_text_reconstruct`) — so the
/// variant and its inverse can never disagree about existence. The lowering
/// (`typed_lowering::field_child_expr_typed`) branches PER FIELD instead, which is sound
/// because a field stamped `TokenText` implies this predicate holds.
///
/// It walks `collect_category_variants` — the SAME derivation every emitter consumes — rather
/// than re-deriving field kinds from `LanguageDef`, so it cannot drift from what is emitted.
pub(crate) fn language_has_token_text_leaf(language: &LanguageDef) -> bool {
    fn is_token_text(field: &crate::gen::term_ops::subst::FieldInfo) -> bool {
        field.opaque_leaf == Some(crate::gen::term_ops::subst::OpaqueLeafKind::TokenText)
    }
    language.types.iter().any(|lang_type| {
        collect_category_variants(&lang_type.name, language)
            .iter()
            .any(|variant| match variant {
                VariantKind::Regular { fields, .. } => fields.iter().any(is_token_text),
                VariantKind::Binder { pre_scope_fields, .. }
                | VariantKind::MultiBinder { pre_scope_fields, .. } => {
                    pre_scope_fields.iter().any(is_token_text)
                },
                // ★ #141 G5. The predicate asks "does any variant carry a
                // token-text field?"; a refusal carries no fields, so the honest
                // answer is `false` and the refusal is reported by the emitter
                // that owns it. See `VariantKind::Refused`.
                VariantKind::Refused { .. }
                | VariantKind::Var { .. }
                | VariantKind::Literal { .. }
                | VariantKind::CollectionLiteral { .. }
                | VariantKind::Nullary { .. }
                | VariantKind::Collection { .. } => false,
            })
    })
}

/// Generate the typed op-enum + its `SemanticHash` + `Display` for a language (Step B).
///
/// The `SemanticHash` writes a framed discriminant (cross-variant injectivity — two variants
/// never alias) followed by the framed, `Eq`-agreeing payload bytes; this is the exact e-graph
/// content key (`unsafe` trait: a key disagreeing with `Eq` would silently fail dedup).
pub(crate) fn generate_dovetail_op_enum(language: &LanguageDef) -> TokenStream {
    let enum_ident = op_enum_ident(language);
    let (variants, op_variant_refusals) = collect_op_variants(language);

    let enum_variants = variants.iter().map(|v| {
        let ident = &v.ident;
        match &v.payload {
            Some(ty) => quote! { #ident(#ty) },
            None => quote! { #ident },
        }
    });

    let sh_arms = variants.iter().map(|v| {
        let ident = &v.ident;
        let disc = v.disc;
        if v.payload.is_some() {
            let write_payload = &v.write_payload;
            quote! {
                Self::#ident(__p) => {
                    ::dovetail::key::write_framed(out, &#disc.to_le_bytes());
                    #write_payload
                }
            }
        } else {
            quote! {
                Self::#ident => {
                    ::dovetail::key::write_framed(out, &#disc.to_le_bytes());
                }
            }
        }
    });

    let display_arms = variants.iter().map(|v| {
        let ident = &v.ident;
        let display = &v.display;
        if v.payload.is_some() {
            quote! { Self::#ident(__p) => write!(f, "{}({:?})", #display, __p), }
        } else {
            quote! { Self::#ident => write!(f, "{}", #display), }
        }
    });

    // Every emitted item is gated on `dovetail-codegen` (it references `::dovetail`): a
    // `#[cfg]` attribute applies only to the NEXT item, so each of the three carries its own.
    quote! {
        #[cfg(feature = "dovetail-codegen")]
        #[derive(::core::clone::Clone, ::core::cmp::PartialEq, ::core::cmp::Eq, ::core::hash::Hash)]
        #[allow(non_camel_case_types)]
        pub enum #enum_ident {
            #(#enum_variants),*
        }

        // SAFETY: `write_content` writes a framed discriminant unique per variant followed by
        // the framed, `Eq`-agreeing payload bytes (integers two's-complement LE; floats and
        // big-numerics via `to_canonical_bytes`; Map/Bag via sorted `Display`; vars/Vec via
        // `Debug`). Two values produce identical bytes iff they are `Eq`-equal, and the
        // framing makes the composite injective — satisfying the `SemanticHash` contract.
        #[cfg(feature = "dovetail-codegen")]
        unsafe impl ::dovetail::key::SemanticHash for #enum_ident {
            fn write_content(&self, out: &mut ::std::vec::Vec<u8>) {
                match self {
                    #(#sh_arms)*
                }
            }
        }

        #[cfg(feature = "dovetail-codegen")]
        impl ::core::fmt::Display for #enum_ident {
            fn fmt(&self, f: &mut ::core::fmt::Formatter<'_>) -> ::core::fmt::Result {
                match self {
                    #(#display_arms)*
                }
            }
        }

        // ★ #141 G5 — the classification refusals. EMPTY for every grammar whose
        // rules classify; non-empty, each is a `compile_error!` naming the rule.
        #(#op_variant_refusals)*
    }
}
