//! Frozen observations of the original constructor-label helpers, before relocation.

use crate::gen::native::{
    is_byte_vector, native_type_to_string, NativeType, NativeTypeFromSynType,
};
use crate::gen::{generate_literal_label, generate_var_label};

fn native(source: &str) -> syn::Type {
    syn::parse_str(source).expect("constructor-label native fixture must parse as a syn type")
}

#[test]
fn original_constructor_label_scalar_classification_and_labels() {
    use NativeType::*;
    let rows = [
        ("i8", Int8, "NumLit"),
        ("i16", Int16, "NumLit"),
        ("i32", Int32, "NumLit"),
        ("i64", Int64, "NumLit"),
        ("i128", Int128, "NumLit"),
        ("isize", Isize, "NumLit"),
        ("u8", UInt8, "NumLit"),
        ("u16", UInt16, "NumLit"),
        ("u32", UInt32, "NumLit"),
        ("u64", UInt64, "NumLit"),
        ("u128", UInt128, "NumLit"),
        ("usize", Usize, "NumLit"),
        ("f32", Float32, "FloatLit"),
        ("f64", Float64, "FloatLit"),
        ("bool", Bool, "BoolLit"),
        ("str", Str, "StringLit"),
        ("String", Str, "StringLit"),
        ("CanonicalBigInt", CanonicalBigInt, "NumLit"),
        ("UserBigInt", CanonicalBigInt, "NumLit"),
        ("CanonicalBigRat", CanonicalBigRat, "RatLit"),
        ("CanonicalFixedPoint", CanonicalFixedPoint, "FixedLit"),
    ];
    for (source, expected, label) in rows {
        assert_eq!(NativeType::from_type_str(source), expected, "{source}");
        let ty = native(source);
        assert_eq!(NativeType::from_syn_type(&ty), expected, "{source}");
        assert_eq!(generate_literal_label(&ty).to_string(), label, "{source}");
    }
}

#[test]
fn original_constructor_label_collection_and_opaque_spellings() {
    use NativeType::*;
    let rows = [
        ("Vec<Proc>", VecCollection, "ListLit"),
        ("HashBag<Proc>", HashBagCollection, "BagLit"),
        ("HashSet<Proc>", HashSetCollection, "BagLit"),
        ("HashMapLit<Name, Proc>", HashMapLitCollection, "MapLit"),
        ("HashMap<Name, Proc>", HashMapCollection, "MapLit"),
        ("HashSetLit", Other("HashSetLit".into()), "SetLit"),
        ("PathMapLit", Other("PathMapLit".into()), "PathmapLit"),
        ("hashsetlit", Other("hashsetlit".into()), "Lit"),
        ("BigRat", Other("BigRat".into()), "Lit"),
        ("Fixed", Other("Fixed".into()), "Lit"),
        ("Arc<HashSetLit>", Other("Arc".into()), "Lit"),
        ("Wrapper", Other("Wrapper".into()), "Lit"),
    ];
    for (source, expected, label) in rows {
        let ty = native(source);
        assert_eq!(NativeType::from_syn_type(&ty), expected, "{source}");
        assert_eq!(generate_literal_label(&ty).to_string(), label, "{source}");
    }
}

#[test]
fn original_constructor_label_all_native_predicates() {
    use NativeType::*;
    let rows = [
        (Int8, 1),
        (Int16, 1),
        (Int32, 1),
        (Int64, 1),
        (Int128, 1),
        (Isize, 1),
        (UInt8, 1),
        (UInt16, 1),
        (UInt32, 1),
        (UInt64, 1),
        (UInt128, 1),
        (Usize, 1),
        (Float32, 2),
        (Float64, 2),
        (Bool, 0),
        (Str, 4),
        (CanonicalBigInt, 1),
        (CanonicalBigRat, 0),
        (CanonicalFixedPoint, 0),
        (VecCollection, 8),
        (HashBagCollection, 8),
        (HashSetCollection, 8),
        (HashMapLitCollection, 8),
        (HashMapCollection, 8),
        (Other("Vec<u8>".into()), 0),
    ];
    assert_eq!(rows.len(), 25);
    for (kind, expected) in rows {
        let flags = u8::from(kind.is_integer())
            | (u8::from(kind.is_float()) << 1)
            | (u8::from(kind.is_string()) << 2)
            | (u8::from(kind.is_collection()) << 3);
        assert_eq!(flags, expected, "{kind:?}");
    }
}

#[test]
fn original_constructor_label_byte_probe_keeps_exact_shallow_gates() {
    let rows = [
        ("Vec<u8>", true, "BytesLit"),
        ("std::vec::Vec<core::primitive::u8>", true, "BytesLit"),
        ("<T as Trait>::Vec<u8>", true, "BytesLit"),
        ("Vec<u8<T>>", true, "BytesLit"),
        ("Vec<u8,>", true, "BytesLit"),
        ("Vec<Proc>", false, "ListLit"),
        ("Vec<u8, u8>", false, "ListLit"),
        ("Vec<&u8>", false, "ListLit"),
        ("Vec", false, "ListLit"),
        ("&Vec<u8>", false, "Lit"),
        ("HashBag<u8>", false, "BagLit"),
    ];
    for (source, bytes, label) in rows {
        let ty = native(source);
        assert_eq!(is_byte_vector(&ty), bytes, "{source}");
        assert_eq!(generate_literal_label(&ty).to_string(), label, "{source}");
        if bytes {
            assert_eq!(NativeType::from_syn_type(&ty), NativeType::VecCollection, "{source}");
        }
    }
}

#[test]
fn original_constructor_label_last_segment_and_unsupported_shapes() {
    let ty = native("some::module::HashSetLit");
    assert_eq!(native_type_to_string(&ty), "HashSetLit");
    assert_eq!(NativeType::from_syn_type(&ty), NativeType::Other("HashSetLit".into()));
    assert_eq!(generate_literal_label(&ty).to_string(), "SetLit");
    assert_eq!(
        NativeType::from_type_str("some::module::HashSetLit"),
        NativeType::Other("some::module::HashSetLit".into()),
    );
    for source in ["&str", "(u8, u8)", "[u8; 4]", "!"] {
        let ty = native(source);
        assert_eq!(native_type_to_string(&ty), "unknown", "{source}");
        assert_eq!(NativeType::from_syn_type(&ty), NativeType::Other("unknown".into()));
        assert_eq!(generate_literal_label(&ty).to_string(), "Lit", "{source}");
    }
    let empty_path = syn::Type::Path(syn::TypePath {
        qself: None,
        path: syn::Path {
            leading_colon: None,
            segments: Default::default(),
        },
    });
    assert_eq!(native_type_to_string(&empty_path), "unknown");
    assert!(!is_byte_vector(&empty_path));
    assert_eq!(generate_literal_label(&empty_path).to_string(), "Lit");
}

#[test]
fn original_constructor_label_var_unicode_and_raw_spelling() {
    for (source, expected) in [
        ("Proc", "PVar"),
        ("name", "NVar"),
        ("ßuffix", "SSVar"),
        ("éclair", "ÉVar"),
        ("δelta", "ΔVar"),
        ("_private", "_Var"),
        ("r#type", "RVar"),
    ] {
        let ident: syn::Ident =
            syn::parse_str(source).expect("Var-label fixture must be an identifier");
        assert_eq!(generate_var_label(&ident).to_string(), expected, "{source}");
    }
}
