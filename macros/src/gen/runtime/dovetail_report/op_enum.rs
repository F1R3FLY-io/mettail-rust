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
use crate::gen::term_ops::subst::{collect_category_variants, VariantKind};

/// The generated op-enum identifier for a language (e.g. `RhoCalcDovetailOp`).
pub(crate) fn op_enum_ident(language: &LanguageDef) -> Ident {
    format_ident!("{}DovetailOp", language.name)
}

/// The op-enum variant identifier for a `(category, constructor-label)` pair, e.g.
/// `Proc_IntBinProc`, `Int_NumLit`. The `<Cat>_<Label>` shape guarantees uniqueness across
/// categories (two categories may share a constructor label only by accident; the category
/// prefix disambiguates) and lets reconstruction recover BOTH the AST enum and the variant.
fn op_variant_ident(category: &Ident, label: &Ident) -> Ident {
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
        let elem = collection_element_type(native_type)
            .unwrap_or_else(|| quote! { #native_type });
        return Some(match collection_kind {
            CollectionCategory::List(_) => quote! { #native_type },
            CollectionCategory::Bag(_) => quote! { #native_type },
            CollectionCategory::Map(_) => {
                quote! { ::mettail_runtime::HashMapLit<#elem, #elem> }
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
            CollectionCategory::Bag(_) | CollectionCategory::Map(_) => quote! {
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
fn collect_op_variants(language: &LanguageDef) -> Vec<OpVariant> {
    let mut variants = Vec::new();
    let mut disc: u32 = 0;
    let mut push = |ident: Ident,
                    payload: Option<TokenStream>,
                    write_payload: TokenStream,
                    display: String| {
        let v = OpVariant { ident, payload, disc, write_payload, display };
        disc += 1;
        variants.push(v);
    };

    let lang = language.name.to_string();
    for lang_type in &language.types {
        let category = &lang_type.name;
        let cat = category.to_string();
        for variant in collect_category_variants(category, language) {
            match variant {
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
                VariantKind::Literal { label } => {
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

    variants
}

/// Generate the typed op-enum + its `SemanticHash` + `Display` for a language (Step B).
///
/// The `SemanticHash` writes a framed discriminant (cross-variant injectivity — two variants
/// never alias) followed by the framed, `Eq`-agreeing payload bytes; this is the exact e-graph
/// content key (`unsafe` trait: a key disagreeing with `Eq` would silently fail dedup).
pub(crate) fn generate_dovetail_op_enum(language: &LanguageDef) -> TokenStream {
    let enum_ident = op_enum_ident(language);
    let variants = collect_op_variants(language);

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

    quote! {
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
        unsafe impl ::dovetail::key::SemanticHash for #enum_ident {
            fn write_content(&self, out: &mut ::std::vec::Vec<u8>) {
                match self {
                    #(#sh_arms)*
                }
            }
        }

        impl ::core::fmt::Display for #enum_ident {
            fn fmt(&self, f: &mut ::core::fmt::Formatter<'_>) -> ::core::fmt::Result {
                match self {
                    #(#display_arms)*
                }
            }
        }
    }
}
