//! Frozen ORIGINAL NativeKind methods, before their neutral-core relocation.
//! Expected tables are source snapshots, not recomputed numeric width rules.
//! The language wildcard also brings the planned AST extension trait into scope
//! after relocation without changing any original behavior assertion.
use mettail_ast::language::*;
use syn::{parse_quote, Type};

const KINDS: [NativeKind; 20] = [
    NativeKind::Int8,
    NativeKind::Int16,
    NativeKind::Int32,
    NativeKind::Int64,
    NativeKind::Int128,
    NativeKind::Isize,
    NativeKind::UInt8,
    NativeKind::UInt16,
    NativeKind::UInt32,
    NativeKind::UInt64,
    NativeKind::UInt128,
    NativeKind::Usize,
    NativeKind::Float32,
    NativeKind::Float64,
    NativeKind::Bool,
    NativeKind::Str,
    NativeKind::CanonicalBigInt,
    NativeKind::CanonicalBigRat,
    NativeKind::CanonicalFixedPoint,
    NativeKind::Other,
];

fn lossless_golden() -> [&'static [NativeKind]; 20] {
    use NativeKind::*;
    [
        &[Int16, Int32, Int64, Int128, CanonicalBigInt, CanonicalBigRat],
        &[Int32, Int64, Int128, CanonicalBigInt, CanonicalBigRat],
        &[Int64, Int128, CanonicalBigInt, CanonicalBigRat],
        &[Int128, CanonicalBigInt, CanonicalBigRat],
        &[CanonicalBigInt, CanonicalBigRat],
        &[Int128, CanonicalBigInt, CanonicalBigRat],
        &[
            UInt16,
            UInt32,
            UInt64,
            UInt128,
            Int16,
            Int32,
            Int64,
            Int128,
            CanonicalBigInt,
            CanonicalBigRat,
        ],
        &[UInt32, UInt64, UInt128, Int32, Int64, Int128, CanonicalBigInt, CanonicalBigRat],
        &[UInt64, UInt128, Int64, Int128, CanonicalBigInt, CanonicalBigRat],
        &[UInt128, Int128, CanonicalBigInt, CanonicalBigRat],
        &[CanonicalBigInt, CanonicalBigRat],
        &[UInt128, Int128, CanonicalBigInt, CanonicalBigRat],
        &[Float64, CanonicalBigRat],
        &[CanonicalBigRat],
        &[
            Int8,
            Int16,
            Int32,
            Int64,
            Int128,
            Isize,
            UInt8,
            UInt16,
            UInt32,
            UInt64,
            UInt128,
            Usize,
            CanonicalBigInt,
            CanonicalBigRat,
        ],
        &[],
        &[CanonicalBigRat],
        &[],
        &[CanonicalBigRat],
        &[],
    ]
}

fn lossy_golden() -> [&'static [NativeKind]; 20] {
    use NativeKind::*;
    [
        &[UInt8, UInt16, UInt32, UInt64, UInt128, Usize, Float32, Float64],
        &[UInt8, UInt16, UInt32, UInt64, UInt128, Usize, Float32, Float64],
        &[UInt8, UInt16, UInt32, UInt64, UInt128, Usize, Float32, Float64],
        &[UInt8, UInt16, UInt32, UInt64, UInt128, Usize, Float32, Float64],
        &[UInt8, UInt16, UInt32, UInt64, UInt128, Usize, Float32, Float64],
        &[UInt8, UInt16, UInt32, UInt64, UInt128, Usize, Float32, Float64],
        &[Float32, Float64],
        &[Float32, Float64],
        &[Float32, Float64],
        &[Float32, Float64],
        &[Float32, Float64],
        &[Float32, Float64],
        &[
            Int8,
            Int16,
            Int32,
            Int64,
            Int128,
            Isize,
            UInt8,
            UInt16,
            UInt32,
            UInt64,
            UInt128,
            Usize,
            CanonicalFixedPoint,
        ],
        &[
            Int8,
            Int16,
            Int32,
            Int64,
            Int128,
            Isize,
            UInt8,
            UInt16,
            UInt32,
            UInt64,
            UInt128,
            Usize,
            CanonicalFixedPoint,
        ],
        &[Float32, Float64],
        &[],
        &[
            Int8, Int16, Int32, Int64, Int128, Isize, UInt8, UInt16, UInt32, UInt64, UInt128,
            Usize, Float32, Float64,
        ],
        &[
            CanonicalBigInt,
            Int8,
            Int16,
            Int32,
            Int64,
            Int128,
            Isize,
            UInt8,
            UInt16,
            UInt32,
            UInt64,
            UInt128,
            Usize,
            Float32,
            Float64,
            CanonicalFixedPoint,
        ],
        &[
            Int8,
            Int16,
            Int32,
            Int64,
            Int128,
            Isize,
            UInt8,
            UInt16,
            UInt32,
            UInt64,
            UInt128,
            Usize,
            Float32,
            Float64,
            CanonicalBigInt,
        ],
        &[],
    ]
}

#[test]
fn native_kind_original_twenty_variants_integer_and_token_family_tables() {
    let variants = [
        ("Int8", true, Some("Integer")),
        ("Int16", true, Some("Integer")),
        ("Int32", true, Some("Integer")),
        ("Int64", true, Some("Integer")),
        ("Int128", true, Some("Integer")),
        ("Isize", true, Some("Integer")),
        ("UInt8", true, Some("Integer")),
        ("UInt16", true, Some("Integer")),
        ("UInt32", true, Some("Integer")),
        ("UInt64", true, Some("Integer")),
        ("UInt128", true, Some("Integer")),
        ("Usize", true, Some("Integer")),
        ("Float32", false, Some("Float")),
        ("Float64", false, Some("Float")),
        ("Bool", false, Some("Boolean")),
        ("Str", false, Some("StringLit")),
        ("CanonicalBigInt", true, None),
        ("CanonicalBigRat", false, None),
        ("CanonicalFixedPoint", false, None),
        ("Other", false, None),
    ];
    let mut identities = std::collections::HashSet::new();
    for (index, (kind, (name, integer, token))) in KINDS.into_iter().zip(variants).enumerate() {
        assert_eq!(kind as usize, index, "original enum declaration order");
        assert_eq!(format!("{kind:?}"), name);
        assert!(identities.insert(kind), "all twenty Eq/Hash identities are distinct");
        assert_eq!(kind.is_integer(), integer, "{kind:?}");
        assert_eq!(kind.standard_token_variant(), token, "{kind:?}");
    }
    assert_eq!(identities.len(), 20);
}

#[test]
fn native_kind_original_last_segment_exact_names_and_suffix_boundary() {
    use NativeKind::*;
    for (text, expected) in [
        ("i8", Int8),
        ("i16", Int16),
        ("i32", Int32),
        ("i64", Int64),
        ("i128", Int128),
        ("isize", Isize),
        ("u8", UInt8),
        ("u16", UInt16),
        ("u32", UInt32),
        ("u64", UInt64),
        ("u128", UInt128),
        ("usize", Usize),
        ("f32", Float32),
        ("f64", Float64),
        ("bool", Bool),
        ("str", Str),
        ("String", Str),
        ("CanonicalBigRat", CanonicalBigRat),
        ("CanonicalFixedPoint", CanonicalFixedPoint),
        ("CanonicalBigInt", CanonicalBigInt),
        ("BigInt", CanonicalBigInt),
        ("UserBigInt", CanonicalBigInt),
        ("CanonicalBigRatBigInt", CanonicalBigInt),
        ("UserBigRat", Other),
        ("UserCanonicalBigRat", Other),
        ("UserCanonicalFixedPoint", Other),
        ("BigRat", Other),
        ("Fixed", Other),
        ("bigint", Other),
        ("BIGINT", Other),
        ("BigInteger", Other),
        ("Opaque", Other),
        ("r#String", Other),
        ("r#BigInt", CanonicalBigInt),
    ] {
        let native: Type = syn::parse_str(text).expect("well-formed frozen native type fixture");
        assert_eq!(NativeKind::from_syn_type(&native), expected, "{text}");
    }
}

#[test]
fn native_kind_original_path_shape_ignores_prefix_arguments_and_qself() {
    use NativeKind::*;
    let cases: [(Type, NativeKind); 7] = [
        (parse_quote!(module::i32), Int32),
        (parse_quote!(module::CanonicalBigRat), CanonicalBigRat),
        (parse_quote!(module::UserBigInt<Opaque>), CanonicalBigInt),
        (parse_quote!(module::Vec<CanonicalBigInt>), Other),
        (parse_quote!(<T as Trait>::i32), Int32),
        (parse_quote!(<T as Trait>::CanonicalFixedPoint), CanonicalFixedPoint),
        (parse_quote!(::module::String), Str),
    ];
    for (native, expected) in cases {
        assert_eq!(NativeKind::from_syn_type(&native), expected);
    }
    let empty_path = Type::Path(syn::TypePath {
        qself: None,
        path: syn::Path {
            leading_colon: None,
            segments: Default::default(),
        },
    });
    assert_eq!(NativeKind::from_syn_type(&empty_path), Other);
}

#[test]
fn native_kind_original_non_path_types_do_not_recurse() {
    let cases: [Type; 10] = [
        parse_quote!(&i32),
        parse_quote!(*const i32),
        parse_quote!([i32; 4]),
        parse_quote!([i32]),
        parse_quote!((i32,)),
        parse_quote!((i32)),
        parse_quote!(fn() -> i32),
        parse_quote!(_),
        parse_quote!(!),
        Type::Group(syn::TypeGroup {
            group_token: Default::default(),
            elem: Box::new(parse_quote!(CanonicalBigInt)),
        }),
    ];
    for native in cases {
        assert_eq!(NativeKind::from_syn_type(&native), NativeKind::Other);
    }
    assert_eq!(
        NativeKind::from_syn_type(&Type::Verbatim(quote::quote!(CanonicalBigInt))),
        NativeKind::Other,
    );
}

#[test]
fn native_kind_original_ordered_lossless_and_lossy_tables() {
    for ((kind, lossless), lossy) in KINDS.into_iter().zip(lossless_golden()).zip(lossy_golden()) {
        assert_eq!(kind.lossless_targets(), lossless, "lossless row {kind:?}");
        assert_eq!(kind.lossy_targets(), lossy, "lossy row {kind:?}");
    }
}

#[test]
fn native_kind_original_promotion_queue_order_distance_and_seen_behavior() {
    // In the CURRENT original table, every reachable target is already in the
    // direct source row. This is a golden of its BFS output, not permission to
    // replace the original queue, seen-vector, or saturating distance update.
    for (kind, targets) in KINDS.into_iter().zip(lossless_golden()) {
        let expected: Vec<_> = targets
            .iter()
            .copied()
            .map(|target| (target, 1_u8))
            .collect();
        let actual = kind.lossless_promotion_chain();
        assert_eq!(actual, expected, "ordered promotion roster {kind:?}");
        assert!(!actual.iter().any(|(target, _)| *target == kind), "source is initially seen");
        let distinct: std::collections::HashSet<_> =
            actual.iter().map(|(target, _)| *target).collect();
        assert_eq!(actual.len(), distinct.len(), "shared successors are emitted once");
    }
}
