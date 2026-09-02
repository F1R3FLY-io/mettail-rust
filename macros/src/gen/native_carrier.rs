//! Closed classification of native carriers that structurally contain terms.
//!
//! Native scalar aliases are leaves, while ordinary collection aliases are
//! classified by their declared `collection_kind`.  Any other native type that
//! embeds a declared language category must have an entry in this closed
//! algebra.  Unknown recursive carriers are rejected during generation instead
//! of being silently cloned, compared, hashed, or lowered as opaque values.

use std::collections::BTreeSet;

use mettail_ast::language::LanguageDef;
use proc_macro2::TokenStream;
use quote::{quote, ToTokens};
use syn::{GenericArgument, Ident, PathArguments, Type};

/// Ownership wrapper used by the generated enum payload.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum NativeCarrierStorage {
    Direct,
    Arc,
}

/// Read and write access remain different typed constructors even though both
/// carry the same structural zipper product.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ZipperAccess {
    Read,
    Write,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum NativeCarrierWalkOrder {
    Forward,
    ReverseForLifo,
}

/// Finite recursive-native carrier algebra shared by every generator.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum NativeRecursiveCarrier {
    Zipper {
        storage: NativeCarrierStorage,
        access: ZipperAccess,
        key_category: Ident,
        value_category: Ident,
    },
}

impl NativeRecursiveCarrier {
    pub(crate) fn runtime_constructor_name(&self) -> &'static str {
        match self {
            Self::Zipper { access: ZipperAccess::Read, .. } => "ReadZipperLit",
            Self::Zipper { access: ZipperAccess::Write, .. } => "WriteZipperLit",
        }
    }

    pub(crate) fn key_category(&self) -> &Ident {
        match self {
            Self::Zipper { key_category, .. } => key_category,
        }
    }

    pub(crate) fn value_category(&self) -> &Ident {
        match self {
            Self::Zipper { value_category, .. } => value_category,
        }
    }

    pub(crate) fn storage(&self) -> NativeCarrierStorage {
        match self {
            Self::Zipper { storage, .. } => *storage,
        }
    }

    /// Borrow the PathMap component from a binding to a generated native
    /// payload. The binding itself is normally borrowed by an enum match.
    pub(crate) fn pathmap_ref(&self, binding: &TokenStream) -> TokenStream {
        match self.storage() {
            NativeCarrierStorage::Direct => quote! { &(#binding).0 },
            NativeCarrierStorage::Arc => quote! { &(#binding).as_ref().0 },
        }
    }

    /// Borrow the exact focus bytes from a generated native payload binding.
    pub(crate) fn focus_ref(&self, binding: &TokenStream) -> TokenStream {
        match self.storage() {
            NativeCarrierStorage::Direct => quote! { &(#binding).1 },
            NativeCarrierStorage::Arc => quote! { &(#binding).as_ref().1 },
        }
    }

    /// Construct the exact payload from an already rebuilt PathMap and focus.
    pub(crate) fn construct(&self, pathmap: &TokenStream, focus: &TokenStream) -> TokenStream {
        let constructor = match self {
            Self::Zipper { access: ZipperAccess::Read, .. } => {
                quote! { mettail_runtime::ReadZipperLit }
            },
            Self::Zipper { access: ZipperAccess::Write, .. } => {
                quote! { mettail_runtime::WriteZipperLit }
            },
        };
        let direct = quote! { #constructor(#pathmap, #focus) };
        match self.storage() {
            NativeCarrierStorage::Direct => direct,
            NativeCarrierStorage::Arc => quote! { std::sync::Arc::new(#direct) },
        }
    }

    /// Emit one callback for every recursive term position. Zipper PathMaps
    /// retain their homogeneous Empty/Set/Map topology: set entries visit a key
    /// only, map entries visit key then value, and reverse order is the exact
    /// LIFO inverse of that flat sequence.
    pub(crate) fn for_each_borrowed_subterm(
        &self,
        binding: &TokenStream,
        order: NativeCarrierWalkOrder,
        subterm: &dyn Fn(&Ident, &TokenStream) -> TokenStream,
    ) -> TokenStream {
        let pathmap = self.pathmap_ref(binding);
        let key_category = self.key_category();
        let value_category = self.value_category();
        let key_body = subterm(key_category, &quote! { __native_key });
        let value_body = subterm(value_category, &quote! { __native_value });
        match order {
            NativeCarrierWalkOrder::Forward => quote! {
                for __native_entry in (#pathmap).iter() {
                    let __native_key = __native_entry.key();
                    #key_body
                    if let Some(__native_value) = __native_entry.value() {
                        #value_body
                    }
                }
            },
            NativeCarrierWalkOrder::ReverseForLifo => quote! {
                {
                    let __native_entries: Vec<_> = (#pathmap).iter().collect();
                    for __native_entry in __native_entries.into_iter().rev() {
                        let __native_key = __native_entry.key();
                        if let Some(__native_value) = __native_entry.value() {
                            #value_body
                        }
                        #key_body
                    }
                }
            },
        }
    }
}

/// Classify the native payload of `category`.
///
/// `Ok(None)` means the native value is either non-recursive or an ordinary
/// declared collection handled by `VariantKind::CollectionLiteral`.  `Err`
/// means the native type contains language terms but no closed carrier codec is
/// available; generation must fail rather than erase those terms.
pub(crate) fn native_recursive_carrier_for_category(
    category: &Ident,
    language: &LanguageDef,
) -> Result<Option<NativeRecursiveCarrier>, String> {
    let Some(lang_type) = language.get_type(category) else {
        return Ok(None);
    };
    let Some(native_type) = lang_type.native_type.as_ref() else {
        return Ok(None);
    };

    // Collection literals have their own closed carrier classification.  This
    // branch is structural metadata, not a category-name exception.
    if lang_type.collection_kind.is_some() {
        return Ok(None);
    }

    classify_native_type(native_type, language)
}

fn classify_native_type(
    native_type: &Type,
    language: &LanguageDef,
) -> Result<Option<NativeRecursiveCarrier>, String> {
    let (storage, structural_type) = strip_arc(native_type)?;
    if let Some(segment) = type_path_last_segment(structural_type) {
        let access = match segment.ident.to_string().as_str() {
            "ReadZipperLit" => Some(ZipperAccess::Read),
            "WriteZipperLit" => Some(ZipperAccess::Write),
            _ => None,
        };
        if let Some(access) = access {
            let categories = exactly_two_type_arguments(segment)?;
            let key_category = category_ident(categories[0], language)?;
            let value_category = category_ident(categories[1], language)?;
            return Ok(Some(NativeRecursiveCarrier::Zipper {
                storage,
                access,
                key_category,
                value_category,
            }));
        }
    }

    let declared: BTreeSet<String> = language
        .types
        .iter()
        .map(|ty| ty.name.to_string())
        .collect();
    let references = declared_category_references(native_type, &declared)?;
    if references.is_empty() {
        return Ok(None);
    }

    Err(format!(
        "native category carrier `{}` embeds recursive language categories [{}] but has no closed NativeRecursiveCarrier descriptor",
        native_type.to_token_stream(),
        references.into_iter().collect::<Vec<_>>().join(", "),
    ))
}

fn strip_arc(native_type: &Type) -> Result<(NativeCarrierStorage, &Type), String> {
    let Some(segment) = type_path_last_segment(native_type) else {
        return Ok((NativeCarrierStorage::Direct, native_type));
    };
    if segment.ident != "Arc" {
        return Ok((NativeCarrierStorage::Direct, native_type));
    }
    let PathArguments::AngleBracketed(arguments) = &segment.arguments else {
        return Err("Arc native carrier must have exactly one type argument".to_owned());
    };
    let mut types = arguments.args.iter().filter_map(|argument| match argument {
        GenericArgument::Type(ty) => Some(ty),
        _ => None,
    });
    let Some(inner) = types.next() else {
        return Err("Arc native carrier must have exactly one type argument".to_owned());
    };
    if types.next().is_some() || arguments.args.len() != 1 {
        return Err("Arc native carrier must have exactly one type argument".to_owned());
    }
    Ok((NativeCarrierStorage::Arc, inner))
}

fn type_path_last_segment(native_type: &Type) -> Option<&syn::PathSegment> {
    let Type::Path(type_path) = native_type else {
        return None;
    };
    type_path.path.segments.last()
}

fn exactly_two_type_arguments(segment: &syn::PathSegment) -> Result<[&Type; 2], String> {
    let PathArguments::AngleBracketed(arguments) = &segment.arguments else {
        return Err(format!("{} must have exactly two category type arguments", segment.ident));
    };
    let types: Vec<&Type> = arguments
        .args
        .iter()
        .map(|argument| match argument {
            GenericArgument::Type(ty) => Ok(ty),
            _ => Err(format!("{} accepts category type arguments only", segment.ident)),
        })
        .collect::<Result<_, _>>()?;
    types.try_into().map_err(|types: Vec<&Type>| {
        format!(
            "{} must have exactly two category type arguments, found {}",
            segment.ident,
            types.len()
        )
    })
}

fn category_ident(native_type: &Type, language: &LanguageDef) -> Result<Ident, String> {
    let Some(segment) = type_path_last_segment(native_type) else {
        return Err(format!(
            "recursive native carrier argument `{}` is not a declared category type",
            native_type.to_token_stream()
        ));
    };
    if !matches!(segment.arguments, PathArguments::None) {
        return Err(format!(
            "recursive native carrier argument `{}` must be a bare declared category",
            native_type.to_token_stream()
        ));
    }
    let category = segment.ident.clone();
    if language.get_type(&category).is_none() {
        return Err(format!(
            "recursive native carrier references undeclared category `{category}`"
        ));
    }
    Ok(category)
}

/// Iteratively enumerate category identifiers mentioned by a concrete Rust
/// type.  Unsupported type syntax fails closed because the generator cannot
/// prove that it contains no recursive term position.
fn declared_category_references(
    root: &Type,
    declared: &BTreeSet<String>,
) -> Result<BTreeSet<String>, String> {
    let mut pending = vec![root];
    let mut found = BTreeSet::new();

    while let Some(ty) = pending.pop() {
        match ty {
            Type::Path(type_path) => {
                if let Some(qself) = &type_path.qself {
                    pending.push(&qself.ty);
                }
                for segment in &type_path.path.segments {
                    let name = segment.ident.to_string();
                    if declared.contains(&name) {
                        found.insert(name);
                    }
                    match &segment.arguments {
                        PathArguments::None => {},
                        PathArguments::AngleBracketed(arguments) => {
                            for argument in &arguments.args {
                                match argument {
                                    GenericArgument::Type(argument_type) => {
                                        pending.push(argument_type);
                                    },
                                    GenericArgument::AssocType(assoc) => pending.push(&assoc.ty),
                                    GenericArgument::Lifetime(_)
                                    | GenericArgument::Const(_)
                                    | GenericArgument::AssocConst(_)
                                    | GenericArgument::Constraint(_) => {},
                                    _ => {
                                        return Err(format!(
                                            "unsupported generic argument in native carrier `{}`",
                                            root.to_token_stream()
                                        ));
                                    },
                                }
                            }
                        },
                        PathArguments::Parenthesized(arguments) => {
                            pending.extend(arguments.inputs.iter());
                            if let syn::ReturnType::Type(_, output) = &arguments.output {
                                pending.push(output);
                            }
                        },
                    }
                }
            },
            Type::Array(array) => pending.push(&array.elem),
            Type::Group(group) => pending.push(&group.elem),
            Type::Paren(paren) => pending.push(&paren.elem),
            Type::Ptr(pointer) => pending.push(&pointer.elem),
            Type::Reference(reference) => pending.push(&reference.elem),
            Type::Slice(slice) => pending.push(&slice.elem),
            Type::Tuple(tuple) => pending.extend(tuple.elems.iter()),
            Type::Infer(_) | Type::Never(_) => {},
            Type::BareFn(_)
            | Type::ImplTrait(_)
            | Type::Macro(_)
            | Type::TraitObject(_)
            | Type::Verbatim(_) => {
                return Err(format!(
                    "unsupported native carrier type syntax `{}`; recursive-category erasure cannot be ruled out",
                    root.to_token_stream()
                ));
            },
            _ => {
                return Err(format!(
                    "unsupported native carrier type syntax `{}`; recursive-category erasure cannot be ruled out",
                    root.to_token_stream()
                ));
            },
        }
    }
    Ok(found)
}

#[cfg(test)]
mod tests {
    use super::*;
    use mettail_ast::language::{CategoryRole, LangType};
    use quote::format_ident;

    fn language() -> LanguageDef {
        let mut language = LanguageDef {
            name: format_ident!("CarrierDemo"),
            options: Default::default(),
            extends_names: Vec::new(),
            include_names: Vec::new(),
            mixin_names: Vec::new(),
            types: Vec::new(),
            refinement_types: Vec::new(),
            token_defs: Vec::new(),
            mode_defs: Vec::new(),
            sync_constraints: Vec::new(),
            tree_invariants: Vec::new(),
            terms: Vec::new(),
            equations: Vec::new(),
            rewrites: Vec::new(),
            logic: None,
            guard_config: None,
        };
        for name in ["Proc", "Name"] {
            language.types.push(LangType {
                name: format_ident!("{}", name),
                role: CategoryRole::Object,
                native_type: None,
                collection_kind: None,
            });
        }
        language
    }

    #[test]
    fn recognizes_direct_and_arc_zipper_products() {
        let language = language();
        let direct: Type = syn::parse_str("mettail_runtime::ReadZipperLit<Proc, Name>")
            .expect("fixture type parses");
        let shared: Type =
            syn::parse_str("std::sync::Arc<mettail_runtime::WriteZipperLit<Name, Proc>>")
                .expect("fixture type parses");

        assert_eq!(
            classify_native_type(&direct, &language).expect("known carrier"),
            Some(NativeRecursiveCarrier::Zipper {
                storage: NativeCarrierStorage::Direct,
                access: ZipperAccess::Read,
                key_category: format_ident!("Proc"),
                value_category: format_ident!("Name"),
            })
        );
        assert_eq!(
            classify_native_type(&shared, &language).expect("known carrier"),
            Some(NativeRecursiveCarrier::Zipper {
                storage: NativeCarrierStorage::Arc,
                access: ZipperAccess::Write,
                key_category: format_ident!("Name"),
                value_category: format_ident!("Proc"),
            })
        );
    }

    #[test]
    fn accepts_nonrecursive_native_scalars() {
        let language = language();
        let bytes: Type = syn::parse_str("Vec<u8>").expect("fixture type parses");
        assert_eq!(classify_native_type(&bytes, &language), Ok(None));
    }

    #[test]
    fn rejects_unknown_recursive_native_carriers() {
        let language = language();
        let unknown: Type =
            syn::parse_str("ForeignCarrier<Vec<Proc>>").expect("fixture type parses");
        let error = classify_native_type(&unknown, &language)
            .expect_err("unknown recursive carrier must fail closed");
        assert!(error.contains("Proc"));
        assert!(error.contains("no closed NativeRecursiveCarrier descriptor"));
    }
}
