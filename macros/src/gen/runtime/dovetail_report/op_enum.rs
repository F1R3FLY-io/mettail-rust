//! Step B of the Dovetail native-fold reduction work (Increment 2): the per-language
//! **typed op-enum** carried by the e-graph on the fold-bearing path.
//!
//! The production Dovetail report compiler lowers a term into `EGraph<String>`, stringifying
//! literal payloads via lossy `{:?}` Debug with no inverse back to a typed term — so a fold
//! body cannot run on the reduced children, and (a latent bug) two `Eq`-equal `Map`/`Bag`
//! values can stringify differently and fail to dedup.
//!
//! For fold-bearing languages we instead carry a generated `<Lang>DovetailOp`: typed enum
//! variants retain scalar literal/var **payloads inline** (lossless), while payload-free constructors
//! use one opaque stable-discriminant carrier exposed through associated constants bearing the
//! original `(category, constructor)` names. Reconstruction remains total and fold bodies run on
//! typed children without making rustc instantiate thousands of equivalent unit variants. This
//! module emits that representation, its `unsafe impl ::dovetail::key::SemanticHash` (the exact,
//! `Eq`-agreeing e-graph content key — framed discriminant + framed payload bytes), and its
//! `Display` (the runtime-report projection label).
//!
//! Term-bearing collection literals are payload-free constructor nodes whose
//! exact children are emitted by the shared structural lowering PDA.  Only a
//! collection of non-category scalars remains an inline payload: it has no
//! recursive semantic children and its native carrier is already its exact
//! scalar codec.  This is the StructuralV2 key ABI; reader-facing `Display` and
//! `Debug` are never semantic identity for term-bearing collections.
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
use crate::gen::term_ops::subst::VariantKind;

use super::semantic_adapter::{SemanticAdapterLayout, SemanticSentinelIdentity};

/// The generated op-enum identifier for a language (e.g. `RholangDovetailOp`).
pub(crate) fn op_enum_ident(language: &LanguageDef) -> Ident {
    format_ident!("{}DovetailOp", language.name)
}

/// Private stable-discriminant accessor shared by generated table consumers.
pub(crate) fn op_discriminant_method_ident(language: &LanguageDef) -> Ident {
    format_ident!(
        "__mettail_{}_dovetail_stable_discriminant",
        super::to_snake(&language.name.to_string())
    )
}

/// The op-enum variant identifier for a `(category, constructor-label)` pair, e.g.
/// `Proc_IntBinProc`, `Int_NumLit`. The `<Cat>_<Label>` shape guarantees uniqueness across
/// categories (two categories may share a constructor label only by accident; the category
/// prefix disambiguates) and lets reconstruction recover BOTH the AST enum and the variant.
pub(crate) fn op_variant_ident(category: &Ident, label: &Ident) -> Ident {
    format_ident!("{}_{}", category, label)
}

/// Whether `category` is closed parser data rather than an object-language
/// semantic node.  Dovetail emits operators only for semantic categories;
/// object constructors may retain data fields as opaque coefficients.
pub(crate) fn is_closed_data_category(language: &LanguageDef, category: &Ident) -> bool {
    super::semantic_adapter::is_closed_data_category(language, category)
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
fn collect_op_variants(
    language: &LanguageDef,
    layout: &SemanticAdapterLayout,
) -> (Vec<OpVariant>, Vec<TokenStream>) {
    fn push_variant(
        variants: &mut Vec<OpVariant>,
        disc: u32,
        ident: Ident,
        payload: Option<TokenStream>,
        write_payload: TokenStream,
        display: String,
    ) {
        variants.push(OpVariant {
            ident,
            payload,
            disc,
            write_payload,
            display,
        });
    }

    let mut variants = Vec::new();
    let mut refusals: Vec<TokenStream> = Vec::new();

    let lang = language.name.to_string();
    for category_layout in layout.categories() {
        let category = category_layout.category();
        let cat = category.to_string();
        for variant_layout in category_layout.variants() {
            let variant = variant_layout.kind().clone();
            match variant {
                // ★ #141 G5. A classification that refuses declares no op-enum
                // variant; the diagnostic is emitted beside the enum instead, so
                // the build fails with the message rather than with a cascade of
                // "no variant named …" errors. See `VariantKind::Refused`.
                VariantKind::Refused { message, .. } => {
                    refusals.push(quote! { compile_error!(#message); });
                },
                VariantKind::Var { label } => {
                    let disc = variant_layout
                        .operator_discriminant()
                        .expect("accepted semantic variant must have an operator discriminant");
                    let ident = op_variant_ident(category, &label);
                    let display = format!("{lang}::{cat}::{label}");
                    push_variant(
                        &mut variants,
                        disc,
                        ident,
                        Some(quote! { ::mettail_runtime::OrdVar }),
                        // OrdVar Debug agrees with Eq (it includes the variable identity) and
                        // matches the String-path var key form.
                        quote! { ::dovetail::key::write_framed(out, format!("{:?}", __p).as_bytes()); },
                        display,
                    );
                },
                VariantKind::Literal { label } => {
                    let disc = variant_layout
                        .operator_discriminant()
                        .expect("accepted semantic variant must have an operator discriminant");
                    let ident = op_variant_ident(category, &label);
                    let payload = literal_payload_type(language, category);
                    let write_payload = literal_payload_write_content(language, category);
                    let display = format!("{lang}::{cat}::{label}");
                    push_variant(&mut variants, disc, ident, payload, write_payload, display);
                },
                VariantKind::CollectionLiteral { label, element_cat, .. } => {
                    let disc = variant_layout
                        .operator_discriminant()
                        .expect("accepted semantic variant must have an operator discriminant");
                    let ident = op_variant_ident(category, &label);
                    let display = format!("{lang}::{cat}::{label}");
                    if layout.category(&element_cat).is_some() {
                        // StructuralV2: recursive elements are exact child nodes.
                        push_variant(&mut variants, disc, ident, None, quote! {}, display);
                    } else {
                        // A collection of closed Rust scalars has no category task to visit.
                        // Its exact native carrier remains one scalar coefficient.
                        let payload = literal_payload_type(language, category);
                        let write_payload = literal_payload_write_content(language, category);
                        push_variant(&mut variants, disc, ident, payload, write_payload, display);
                    }
                },
                VariantKind::Nullary { label }
                | VariantKind::RecursiveNativeLiteral { label, .. }
                | VariantKind::Regular { label, .. }
                | VariantKind::Collection { label, .. }
                | VariantKind::Binder { label, .. }
                | VariantKind::MultiBinder { label, .. } => {
                    let disc = variant_layout
                        .operator_discriminant()
                        .expect("accepted semantic variant must have an operator discriminant");
                    let ident = op_variant_ident(category, &label);
                    let display = format!("{lang}::{cat}::{label}");
                    // Children are EClassIds (Regular/Binder) or AC bag members (Collection);
                    // the op carries only its identity (the framed discriminant).
                    push_variant(&mut variants, disc, ident, None, quote! {}, display);
                },
            }
        }
    }
    let sentinels = layout.sentinels();
    debug_assert_eq!(variants.len(), sentinels.first_operator_discriminant() as usize);

    // These are leaves of the Dovetail spine rather than category roots.  The
    // shared layout has already paired every identity with its checked stable
    // discriminant, so this emitter does no counting or ordering of its own.
    for sentinel in sentinels.entries() {
        let disc = sentinel.operator_discriminant();
        let (ident, payload, write_payload, display) = match sentinel.identity() {
            SemanticSentinelIdentity::BinderArity => (
                format_ident!("BinderArity"),
                Some(quote! { u32 }),
                quote! { ::dovetail::key::write_framed(out, &__p.to_le_bytes()); },
                "<binder-arity>".to_string(),
            ),
            SemanticSentinelIdentity::FieldNone => (
                format_ident!("FieldNone"),
                Some(quote! { u32 }),
                quote! { ::dovetail::key::write_framed(out, &__p.to_le_bytes()); },
                "<field-none>".to_string(),
            ),
            SemanticSentinelIdentity::FieldOpaque => (
                format_ident!("FieldOpaque"),
                Some(quote! { ::std::string::String }),
                quote! { ::dovetail::key::write_framed(out, __p.as_bytes()); },
                "<field-opaque>".to_string(),
            ),
            SemanticSentinelIdentity::FieldTokenText => (
                format_ident!("FieldTokenText"),
                Some(quote! { ::std::string::String }),
                quote! { ::dovetail::key::write_framed(out, __p.as_bytes()); },
                "<field-token-text>".to_string(),
            ),
            SemanticSentinelIdentity::FieldBytes => (
                format_ident!("FieldBytes"),
                Some(quote! { ::std::vec::Vec<u8> }),
                quote! { ::dovetail::key::write_framed(out, __p); },
                "<field-bytes>".to_string(),
            ),
            SemanticSentinelIdentity::OrderedSequence { element_category } => (
                field_seq_variant_ident(element_category),
                Some(quote! { ::std::vec::Vec<#element_category> }),
                quote! {
                    ::dovetail::key::write_framed(out, format!("{:?}", __p).as_bytes());
                },
                format!("<field-seq-{element_category}>"),
            ),
            SemanticSentinelIdentity::Withheld { category } => (
                field_withheld_variant_ident(category),
                Some(quote! { ::std::sync::Arc<#category> }),
                quote! {
                    let mut __hasher = ::mettail_runtime::FramedSemanticKeyHasher::default();
                    __p.semantic_hash(&mut __hasher);
                    ::dovetail::key::write_framed(out, &__hasher.into_key());
                },
                format!("<field-withheld-{category}>"),
            ),
            SemanticSentinelIdentity::Variable { category } => (
                field_variable_variant_ident(category),
                Some(quote! { ::std::vec::Vec<u8> }),
                quote! { ::dovetail::key::write_framed(out, __p); },
                format!("<field-variable-{category}>"),
            ),
            SemanticSentinelIdentity::CollectionPair { kind, element_category } => (
                collection_pair_variant_ident(*kind, element_category),
                None,
                quote! {},
                format!("<collection-pair-{kind:?}-{element_category}>"),
            ),
            SemanticSentinelIdentity::PathMapMode { element_category } => (
                pathmap_mode_variant_ident(element_category),
                Some(quote! { u8 }),
                quote! { ::dovetail::key::write_framed(out, &[*__p]); },
                format!("<pathmap-mode-{element_category}>"),
            ),
            SemanticSentinelIdentity::PathMapPair { element_category } => (
                pathmap_pair_variant_ident(element_category),
                None,
                quote! {},
                format!("<pathmap-pair-{element_category}>"),
            ),
            SemanticSentinelIdentity::NativePathMapMode { key_category, value_category } => (
                native_pathmap_mode_variant_ident(key_category, value_category),
                Some(quote! { u8 }),
                quote! { ::dovetail::key::write_framed(out, &[*__p]); },
                format!("<native-pathmap-mode-{key_category}-{value_category}>"),
            ),
            SemanticSentinelIdentity::NativePathMapPair { key_category, value_category } => (
                native_pathmap_pair_variant_ident(key_category, value_category),
                None,
                quote! {},
                format!("<native-pathmap-pair-{key_category}-{value_category}>"),
            ),
        };
        push_variant(&mut variants, disc, ident, payload, write_payload, display);
    }

    debug_assert_eq!(variants.len(), sentinels.end_operator_discriminant() as usize);

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

/// Canonical variable-leaf identifier for one semantic category.  These
/// machine-only leaves are appended after every legacy sentinel, so adding the
/// canonical image projection cannot renumber an existing operator.
pub(crate) fn field_variable_variant_ident(category: &Ident) -> Ident {
    format_ident!("FieldVariable{}", category)
}

/// Canonical payload-free operator for one homogeneous map pair role. Both
/// dimensions are present in the Rust identifier because the semantic-machine
/// validator forbids reusing one auxiliary discriminant for incompatible
/// `(collection kind, key category, value category)` roles.
pub(crate) fn collection_pair_variant_ident(
    kind: mettail_grammar_core::CollectionKind,
    element_category: &Ident,
) -> Ident {
    let kind = match kind {
        mettail_grammar_core::CollectionKind::Bag => "Bag",
        mettail_grammar_core::CollectionKind::Set => "Set",
        mettail_grammar_core::CollectionKind::List => "List",
        mettail_grammar_core::CollectionKind::Map => "Map",
        mettail_grammar_core::CollectionKind::PathMap => "PathMap",
    };
    format_ident!("CollectionPair{}{}", kind, element_category)
}

pub(crate) fn pathmap_mode_variant_ident(element_category: &Ident) -> Ident {
    format_ident!("PathMapMode{}", element_category)
}

pub(crate) fn pathmap_pair_variant_ident(element_category: &Ident) -> Ident {
    format_ident!("PathMapPair{}", element_category)
}

pub(crate) fn native_pathmap_mode_variant_ident(
    key_category: &Ident,
    value_category: &Ident,
) -> Ident {
    format_ident!("NativePathMapMode{}{}", key_category, value_category)
}

pub(crate) fn native_pathmap_pair_variant_ident(
    key_category: &Ident,
    value_category: &Ident,
) -> Ident {
    format_ident!("NativePathMapPair{}{}", key_category, value_category)
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
///  1. a required or optional `Vec` field of a `Regular` constructor;
///  2. a required or optional `Vec` field in a `Binder`/`MultiBinder`'s pre-scope fields;
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
/// Exact optional ordered-sequence fields are included: their present arm uses
/// the same labelled `FieldSeq*` leaf and their absent arm uses the indexed
/// `FieldNone` leaf. Unordered optional collections remain opaque and therefore
/// do not earn a carrier.
#[cfg(test)]
#[allow(dead_code)]
pub(crate) fn ordered_seq_element_categories(language: &LanguageDef) -> Vec<Ident> {
    super::semantic_adapter::derive_ordered_sequence_elements(language)
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
#[cfg(test)]
#[allow(dead_code)]
pub(crate) fn language_has_token_text_leaf(language: &LanguageDef) -> bool {
    super::semantic_adapter::derive_token_text(language)
}

/// Generate the typed op-enum + its `SemanticHash` + `Display` for a language (Step B).
///
/// The `SemanticHash` writes a framed discriminant (cross-variant injectivity — two variants
/// never alias) followed by the framed, `Eq`-agreeing payload bytes; this is the exact e-graph
/// content key (`unsafe` trait: a key disagreeing with `Eq` would silently fail dedup).
#[cfg(test)]
pub(crate) fn generate_dovetail_op_enum(language: &LanguageDef) -> TokenStream {
    let layout = match SemanticAdapterLayout::derive(language) {
        Ok(layout) => layout,
        Err(error) => {
            let message = error.to_string();
            return quote! { compile_error!(#message); };
        },
    };
    generate_dovetail_op_enum_from_layout(language, &layout)
}

pub(crate) fn generate_dovetail_op_enum_from_layout(
    language: &LanguageDef,
    layout: &SemanticAdapterLayout,
) -> TokenStream {
    let enum_ident = op_enum_ident(language);
    let discriminant_method = op_discriminant_method_ident(language);
    let (variants, op_variant_refusals) = collect_op_variants(language, layout);
    let constructor_id_ident = format_ident!("__{}DovetailConstructorId", language.name);
    let label_table_ident =
        format_ident!("__METTAIL_{}_DOVETAIL_OP_LABELS", language.name.to_string().to_uppercase());

    let payload_variants = variants.iter().filter(|variant| variant.payload.is_some());
    let enum_variants = payload_variants.clone().map(|v| {
        let ident = &v.ident;
        let ty = v.payload.as_ref().expect("filtered payload variant");
        quote! { #ident(#ty) }
    });

    let constructor_constants = variants
        .iter()
        .filter(|variant| variant.payload.is_none())
        .map(|v| {
            let ident = &v.ident;
            let disc = v.disc;
            quote! {
                pub const #ident: Self = Self::__GeneratedConstructor(#constructor_id_ident(#disc));
            }
        });

    let discriminant_arms = variants
        .iter()
        .filter(|variant| variant.payload.is_some())
        .map(|variant| {
            let ident = &variant.ident;
            let disc = variant.disc;
            quote! { Self::#ident(..) => #disc, }
        });

    let sh_arms = payload_variants.clone().map(|v| {
        let ident = &v.ident;
        let disc = v.disc;
        let write_payload = &v.write_payload;
        quote! {
            Self::#ident(__p) => {
                ::dovetail::key::write_framed(out, &#disc.to_le_bytes());
                #write_payload
            }
        }
    });

    let display_arms = payload_variants.map(|v| {
        let ident = &v.ident;
        let display = &v.display;
        quote! { Self::#ident(__p) => write!(f, "{}({:?})", #display, __p), }
    });
    let labels = variants.iter().map(|variant| &variant.display);

    // Every emitted item is gated on `dovetail-codegen` (it references `::dovetail`): a `#[cfg]`
    // attribute applies only to the NEXT item, so each item carries its own. The constructor-id
    // tuple field is private. Because its public type is not re-exported from the generated
    // concern module, downstream code can pattern-match the associated constants but cannot
    // forge a discriminant that collides with a typed payload variant.
    quote! {
        #[cfg(feature = "dovetail-codegen")]
        #[doc(hidden)]
        #[derive(::core::clone::Clone, ::core::marker::Copy, ::core::cmp::PartialEq,
                 ::core::cmp::Eq, ::core::hash::Hash)]
        pub struct #constructor_id_ident(u32);

        #[cfg(feature = "dovetail-codegen")]
        #[derive(::core::clone::Clone, ::core::cmp::PartialEq, ::core::cmp::Eq, ::core::hash::Hash)]
        #[allow(non_camel_case_types)]
        pub enum #enum_ident {
            #[doc(hidden)]
            __GeneratedConstructor(#constructor_id_ident),
            #(#enum_variants),*
        }

        #[cfg(feature = "dovetail-codegen")]
        #[allow(non_upper_case_globals)]
        impl #enum_ident {
            #(#constructor_constants)*

            #[inline]
            pub(crate) fn #discriminant_method(&self) -> u32 {
                match self {
                    Self::__GeneratedConstructor(__id) => __id.0,
                    #(#discriminant_arms)*
                }
            }
        }

        #[cfg(feature = "dovetail-codegen")]
        const #label_table_ident: &[&str] = &[#(#labels),*];

        // SAFETY: the opaque constructor id and every typed payload variant retain their original
        // stable discriminant. `write_content` writes that framed discriminant followed, for a
        // payload, by the same framed Eq-agreeing bytes as before (integers two's-complement LE;
        // floats and big-numerics via `to_canonical_bytes`; Map/Bag via sorted `Display`; vars/Vec
        // via `Debug`). The constructor-id field is private and its type is sealed inside this
        // concern, so no caller can forge an id that collides with a payload discriminant. Two
        // constructible values therefore produce identical bytes iff they are Eq-equal.
        #[cfg(feature = "dovetail-codegen")]
        unsafe impl ::dovetail::key::SemanticHash for #enum_ident {
            fn write_content(&self, out: &mut ::std::vec::Vec<u8>) {
                match self {
                    Self::__GeneratedConstructor(__id) => {
                        ::dovetail::key::write_framed(out, &__id.0.to_le_bytes());
                    }
                    #(#sh_arms)*
                }
            }
        }

        #[cfg(feature = "dovetail-codegen")]
        impl ::core::fmt::Display for #enum_ident {
            fn fmt(&self, f: &mut ::core::fmt::Formatter<'_>) -> ::core::fmt::Result {
                match self {
                    Self::__GeneratedConstructor(__id) => {
                        let __label = #label_table_ident
                            .get(__id.0 as usize)
                            .copied()
                            .ok_or(::core::fmt::Error)?;
                        f.write_str(__label)
                    }
                    #(#display_arms)*
                }
            }
        }

        // ★ #141 G5 — the classification refusals. EMPTY for every grammar whose
        // rules classify; non-empty, each is a `compile_error!` naming the rule.
        #(#op_variant_refusals)*
    }
}

#[cfg(test)]
mod compact_encoding_tests {
    use super::*;

    fn fixture() -> LanguageDef {
        syn::parse_str(
            r#"
                name: CompactOp,
                types { Proc ![i64] as Int },
                terms {
                    PZero . |- "0" : Proc;
                    AddInt . left:Int, right:Int |- left "+" right : Int ![left + right] fold;
                },
                equations {},
                rewrites {},
            "#,
        )
        .expect("compact-op fixture must parse")
    }

    #[derive(Clone, Copy, PartialEq, Eq, Hash)]
    struct ExampleId(u32);

    #[derive(Clone, PartialEq, Eq, Hash)]
    enum ExampleOp {
        Constructor(ExampleId),
        Payload(String),
    }

    #[allow(non_upper_case_globals)]
    impl ExampleOp {
        const Unit: Self = Self::Constructor(ExampleId(7));
    }

    #[test]
    fn an_associated_constant_preserves_borrowed_unit_pattern_matching() {
        let unit = ExampleOp::Unit;
        let payload = ExampleOp::Payload("x".to_owned());
        assert!(matches!(&unit, &ExampleOp::Unit));
        assert!(!matches!(&payload, &ExampleOp::Unit));
    }

    #[test]
    fn generated_enum_keeps_payloads_typed_and_compacts_unit_operators() {
        let generated = generate_dovetail_op_enum(&fixture());
        let file: syn::File = syn::parse2(generated).expect("generated op items must parse");
        let op_enum = file
            .items
            .iter()
            .find_map(|item| match item {
                syn::Item::Enum(item) if item.ident == "CompactOpDovetailOp" => Some(item),
                _ => None,
            })
            .expect("generated op enum must exist");
        let enum_variants: std::collections::BTreeSet<_> = op_enum
            .variants
            .iter()
            .map(|variant| variant.ident.to_string())
            .collect();

        assert!(enum_variants.contains("__GeneratedConstructor"));
        assert!(enum_variants.contains("Proc_PVar"));
        assert!(enum_variants.contains("Int_NumLit"));
        assert!(!enum_variants.contains("Proc_PZero"));
        assert!(!enum_variants.contains("Int_AddInt"));

        let associated_constants: std::collections::BTreeSet<_> = file
            .items
            .iter()
            .filter_map(|item| match item {
                syn::Item::Impl(item) => Some(item),
                _ => None,
            })
            .flat_map(|item| item.items.iter())
            .filter_map(|item| match item {
                syn::ImplItem::Const(item) => Some(item.ident.to_string()),
                _ => None,
            })
            .collect();
        assert!(associated_constants.contains("Proc_PZero"));
        assert!(associated_constants.contains("Int_AddInt"));
        assert!(!associated_constants.contains("Proc_PVar"));
        assert!(!associated_constants.contains("Int_NumLit"));

        let discriminant_method = op_discriminant_method_ident(&fixture()).to_string();
        assert!(file
            .items
            .iter()
            .filter_map(|item| match item {
                syn::Item::Impl(item) => Some(item),
                _ => None,
            })
            .flat_map(|item| item.items.iter())
            .any(|item| {
                matches!(item, syn::ImplItem::Fn(method)
                if method.sig.ident.to_string() == discriminant_method)
            }));
    }

    #[test]
    fn constructor_identifier_field_is_not_publicly_forgeable() {
        let generated = generate_dovetail_op_enum(&fixture());
        let file: syn::File = syn::parse2(generated).expect("generated op items must parse");
        let id_struct = file
            .items
            .iter()
            .find_map(|item| match item {
                syn::Item::Struct(item)
                    if item.ident.to_string().ends_with("DovetailConstructorId") =>
                {
                    Some(item)
                },
                _ => None,
            })
            .expect("opaque constructor id must exist");
        let field = id_struct
            .fields
            .iter()
            .next()
            .expect("constructor id has one field");
        assert!(matches!(field.vis, syn::Visibility::Inherited));
    }

    #[test]
    fn stable_discriminants_and_labels_remain_one_shared_census() {
        let language = fixture();
        let layout = SemanticAdapterLayout::derive(&language).expect("layout must derive");
        let (variants, refusals) = collect_op_variants(&language, &layout);
        assert!(refusals.is_empty());
        let mut discriminants = std::collections::BTreeSet::new();
        for (ordinal, variant) in variants.iter().enumerate() {
            assert_eq!(variant.disc as usize, ordinal);
            assert!(discriminants.insert(variant.disc));
            assert!(!variant.display.is_empty());
        }
        for sentinel in layout.sentinels().entries() {
            let emitted = &variants[sentinel.operator_discriminant() as usize];
            assert_eq!(emitted.disc, sentinel.operator_discriminant());
            let expected_ident = match sentinel.identity() {
                SemanticSentinelIdentity::BinderArity => format_ident!("BinderArity"),
                SemanticSentinelIdentity::FieldNone => format_ident!("FieldNone"),
                SemanticSentinelIdentity::FieldOpaque => format_ident!("FieldOpaque"),
                SemanticSentinelIdentity::FieldTokenText => format_ident!("FieldTokenText"),
                SemanticSentinelIdentity::FieldBytes => format_ident!("FieldBytes"),
                SemanticSentinelIdentity::OrderedSequence { element_category } => {
                    field_seq_variant_ident(element_category)
                },
                SemanticSentinelIdentity::Withheld { category } => {
                    field_withheld_variant_ident(category)
                },
                SemanticSentinelIdentity::Variable { category } => {
                    field_variable_variant_ident(category)
                },
                SemanticSentinelIdentity::CollectionPair { kind, element_category } => {
                    collection_pair_variant_ident(*kind, element_category)
                },
                SemanticSentinelIdentity::PathMapMode { element_category } => {
                    pathmap_mode_variant_ident(element_category)
                },
                SemanticSentinelIdentity::PathMapPair { element_category } => {
                    pathmap_pair_variant_ident(element_category)
                },
                SemanticSentinelIdentity::NativePathMapMode { key_category, value_category } => {
                    native_pathmap_mode_variant_ident(key_category, value_category)
                },
                SemanticSentinelIdentity::NativePathMapPair { key_category, value_category } => {
                    native_pathmap_pair_variant_ident(key_category, value_category)
                },
            };
            assert_eq!(emitted.ident, expected_ident);
        }
    }

    #[test]
    fn map_pair_sentinel_is_emitted_from_the_shared_collection_census() {
        let language = crate::gen::collection_literal_language_for_tests();
        let layout = SemanticAdapterLayout::derive(&language).expect("layout must derive");
        let proc_category: Ident = syn::parse_str("Proc").expect("identifier");
        let sentinel = layout
            .sentinels()
            .collection_pair(mettail_grammar_core::CollectionKind::Map, &proc_category)
            .expect("Map/Proc pair sentinel");
        let (variants, refusals) = collect_op_variants(&language, &layout);
        assert!(refusals.is_empty());
        let emitted = &variants[sentinel.operator_discriminant() as usize];
        assert_eq!(
            emitted.ident,
            collection_pair_variant_ident(
                mettail_grammar_core::CollectionKind::Map,
                &proc_category,
            )
        );
        assert!(emitted.payload.is_none());
    }

    #[test]
    fn term_bearing_collection_literals_are_payload_free_structural_operators() {
        let language = crate::gen::collection_literal_language_for_tests();
        let layout = SemanticAdapterLayout::derive(&language).expect("layout must derive");
        let (variants, refusals) = collect_op_variants(&language, &layout);
        assert!(refusals.is_empty());

        for (category_name, label_name) in crate::gen::COLLECTION_LITERAL_TEST_CATEGORIES {
            let category: Ident = syn::parse_str(category_name).expect("category identifier");
            let label: Ident = syn::parse_str(label_name).expect("literal identifier");
            let variant = layout
                .category(&category)
                .and_then(|category| category.variant(&label))
                .expect("collection literal must be in the shared census");
            let emitted = &variants[variant
                .operator_discriminant()
                .expect("collection literal has a stable operator")
                as usize];
            assert!(
                emitted.payload.is_none(),
                "{category_name}::{label_name} must carry elements as structural children",
            );
        }
    }

    #[test]
    fn non_category_scalar_collection_retains_its_exact_inline_codec() {
        let language: LanguageDef = syn::parse_str(
            r#"
                name: ScalarCollectionOp,
                types { Proc ![Vec<u8>] as Bytes },
                terms { PZero . |- "0" : Proc; },
                equations {},
                rewrites {},
            "#,
        )
        .expect("scalar collection fixture must parse");
        let layout = SemanticAdapterLayout::derive(&language).expect("layout must derive");
        let (variants, refusals) = collect_op_variants(&language, &layout);
        assert!(refusals.is_empty());
        let bytes: Ident = syn::parse_str("Bytes").expect("identifier");
        let lit: Ident = syn::parse_str("BytesLit").expect("identifier");
        let variant = layout
            .category(&bytes)
            .and_then(|category| category.variant(&lit))
            .expect("Bytes literal must be in the shared census");
        let emitted = &variants[variant
            .operator_discriminant()
            .expect("Bytes literal has a stable operator")
            as usize];
        assert!(emitted.payload.is_some());
    }

    #[test]
    fn pathmap_mode_and_pair_sentinels_are_emitted_from_the_shared_collection_census() {
        let language = crate::gen::collection_literal_language_for_tests();
        let layout = SemanticAdapterLayout::derive(&language).expect("layout must derive");
        let proc_category: Ident = syn::parse_str("Proc").expect("identifier");
        let mode = layout
            .sentinels()
            .pathmap_mode(&proc_category)
            .expect("PathMap/Proc mode sentinel");
        let pair = layout
            .sentinels()
            .pathmap_pair(&proc_category)
            .expect("PathMap/Proc pair sentinel");
        let (variants, refusals) = collect_op_variants(&language, &layout);
        assert!(refusals.is_empty());
        let emitted_mode = &variants[mode.operator_discriminant() as usize];
        assert_eq!(emitted_mode.ident, pathmap_mode_variant_ident(&proc_category));
        assert_eq!(
            emitted_mode
                .payload
                .as_ref()
                .map(ToString::to_string)
                .as_deref(),
            Some("u8")
        );
        let emitted_pair = &variants[pair.operator_discriminant() as usize];
        assert_eq!(emitted_pair.ident, pathmap_pair_variant_ident(&proc_category));
        assert!(emitted_pair.payload.is_none());
    }
}
