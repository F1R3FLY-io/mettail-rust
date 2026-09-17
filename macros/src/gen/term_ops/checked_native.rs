//! Compile-time capability checks for the enum emitter's actual native payloads.
//!
//! Family names are not checked-trait evidence: `foreign::i64` and a wrapper
//! ending in `BigInt` must not inherit a primitive or runtime implementation.
//! Unknown aliases stay outside this checked profile; ordinary emission is
//! unaffected. Rust still resolves and checks the selected concrete types.

use mettail_ast::language::LanguageDef;
use syn::{GenericArgument, Ident, PathArguments, Type};

#[derive(Clone, Copy)]
pub(super) enum LeafCapability {
    Binding,
    Hash,
    Comparison,
}

pub(super) fn literal_supported(
    category: &Ident,
    label: &Ident,
    language: &LanguageDef,
    capability: LeafCapability,
) -> bool {
    crate::gen::types::enums::native_variant_payload(category, label, language)
        .is_some_and(|payload| leaf_supported(&payload, capability))
}

fn ungroup(mut ty: &Type) -> &Type {
    loop {
        ty = match ty {
            Type::Group(group) => &group.elem,
            Type::Paren(paren) => &paren.elem,
            _ => return ty,
        };
    }
}

fn path_matches(ty: &Type, names: &[&str]) -> bool {
    let Type::Path(ty) = ungroup(ty) else {
        return false;
    };
    ty.qself.is_none()
        && ty.path.segments.len() == names.len()
        && ty
            .path
            .segments
            .iter()
            .zip(names)
            .enumerate()
            .all(|(index, (segment, name))| {
                segment.ident == *name
                    && (index + 1 == names.len()
                        || matches!(segment.arguments, PathArguments::None))
            })
}

fn plain_path(ty: &Type, names: &[&str]) -> bool {
    path_matches(ty, names)
        && matches!(ungroup(ty), Type::Path(path)
            if path.path.segments.last().is_some_and(|last| matches!(last.arguments, PathArguments::None)))
}

fn primitive(ty: &Type, name: &str) -> bool {
    plain_path(ty, &[name])
        || plain_path(ty, &["core", "primitive", name])
        || plain_path(ty, &["std", "primitive", name])
}

fn generic_arguments<'a>(
    ty: &'a Type,
    names: &[&str],
    arity: usize,
) -> Option<&'a syn::punctuated::Punctuated<GenericArgument, syn::Token![,]>> {
    if !path_matches(ty, names) {
        return None;
    }
    let Type::Path(path) = ungroup(ty) else {
        return None;
    };
    let PathArguments::AngleBracketed(arguments) = &path.path.segments.last()?.arguments else {
        return None;
    };
    (arguments.args.len() == arity
        && arguments
            .args
            .iter()
            .all(|arg| matches!(arg, GenericArgument::Type(_))))
    .then_some(&arguments.args)
}

fn vector_element(ty: &Type) -> Option<&Type> {
    for name in [&["Vec"][..], &["std", "vec", "Vec"], &["alloc", "vec", "Vec"]] {
        if let Some(arguments) = generic_arguments(ty, name, 1) {
            if let Some(GenericArgument::Type(element)) = arguments.first() {
                return Some(element);
            }
        }
    }
    None
}

pub(super) fn leaf_supported(ty: &Type, capability: LeafCapability) -> bool {
    let ty = ungroup(ty);
    if plain_path(ty, &["std", "string", "String"])
        || plain_path(ty, &["alloc", "string", "String"])
        || primitive(ty, "i64")
        || primitive(ty, "bool")
    {
        return true;
    }
    match capability {
        LeafCapability::Comparison => false,
        LeafCapability::Hash => primitive(ty, "u8") || primitive(ty, "usize"),
        LeafCapability::Binding => {
            matches!(ty, Type::Tuple(tuple) if tuple.elems.is_empty())
                || [
                    "char", "i8", "i16", "i32", "i128", "isize", "u8", "u16", "u32", "u64", "u128",
                    "usize", "f32", "f64",
                ]
                .iter()
                .any(|name| primitive(ty, name))
                || [
                    "CanonicalFloat32",
                    "CanonicalFloat64",
                    "CanonicalBigInt",
                    "CanonicalBigRat",
                    "CanonicalFixedPoint",
                ]
                .iter()
                .any(|name| plain_path(ty, &["mettail_runtime", name]))
                || (crate::gen::native::is_byte_vector(ty)
                    && vector_element(ty).is_some_and(|element| primitive(element, "u8")))
        },
    }
}

/// Only default constructions used by the existing selected dummy recipe.
/// Empty container defaults do not require an element's default. Arc nesting
/// does, and is checked iteratively rather than through recursive type walks.
pub(super) fn default_supported(mut ty: &Type) -> bool {
    loop {
        ty = ungroup(ty);
        if leaf_supported(ty, LeafCapability::Binding) || vector_element(ty).is_some() {
            return true;
        }
        if generic_arguments(ty, &["Option"], 1).is_some()
            || generic_arguments(ty, &["std", "option", "Option"], 1).is_some()
            || generic_arguments(ty, &["core", "option", "Option"], 1).is_some()
        {
            return true;
        }
        for (name, arity) in [
            ("HashBag", 1),
            ("HashSetLit", 1),
            ("HashMapLit", 2),
            ("PathMapLit", 2),
            ("ReadZipperLit", 2),
            ("WriteZipperLit", 2),
        ] {
            if generic_arguments(ty, &["mettail_runtime", name], arity).is_some() {
                return true;
            }
        }
        let arc = generic_arguments(ty, &["std", "sync", "Arc"], 1)
            .or_else(|| generic_arguments(ty, &["alloc", "sync", "Arc"], 1));
        match arc.and_then(|arguments| arguments.first()) {
            Some(GenericArgument::Type(inner)) => ty = inner,
            _ => return false,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn leaf_capabilities_match_concrete_runtime_implementations() {
        for (source, binding, hash, comparison) in [
            ("i64", true, true, true),
            ("std::primitive::i64", true, true, true),
            ("bool", true, true, true),
            ("std::string::String", true, true, true),
            ("usize", true, true, false),
            ("u8", true, true, false),
            ("u32", true, false, false),
            ("()", true, false, false),
            ("mettail_runtime::CanonicalBigInt", true, false, false),
            ("mettail_runtime::CanonicalFloat64", true, false, false),
            ("std::vec::Vec<u8>", true, false, false),
            ("Vec<foreign::u8>", false, false, false),
            ("foreign::Vec<u8>", false, false, false),
            ("foreign::i64", false, false, false),
            ("foreign::bool", false, false, false),
            ("foreign::String", false, false, false),
            ("ForeignBigInt", false, false, false),
        ] {
            let ty = syn::parse_str(source).expect("native carrier type");
            assert_eq!(leaf_supported(&ty, LeafCapability::Binding), binding, "{source}");
            assert_eq!(leaf_supported(&ty, LeafCapability::Hash), hash, "{source}");
            assert_eq!(leaf_supported(&ty, LeafCapability::Comparison), comparison, "{source}");
        }
    }

    #[test]
    fn selected_defaults_follow_only_owning_arc_dependencies() {
        for source in [
            "Vec<Unknown>",
            "Option<Unknown>",
            "mettail_runtime::HashBag<Proc>",
            "mettail_runtime::HashSetLit<Proc>",
            "mettail_runtime::HashMapLit<Proc, Proc>",
            "mettail_runtime::PathMapLit<Proc, Proc>",
            "std::sync::Arc<mettail_runtime::ReadZipperLit<Proc, Proc>>",
            "std::sync::Arc<std::sync::Arc<Vec<Unknown>>>",
        ] {
            assert!(
                default_supported(&syn::parse_str(source).expect("default carrier")),
                "{source}"
            );
        }
        for source in [
            "Unknown",
            "std::sync::Arc<Unknown>",
            "foreign::HashBag<Proc>",
            "foreign::Arc<Vec<Proc>>",
            "std::collections::HashSet<Proc>",
            "mettail_runtime::HashMapLit<Proc>",
        ] {
            assert!(
                !default_supported(&syn::parse_str(source).expect("unsupported carrier")),
                "{source}"
            );
        }
    }
}
