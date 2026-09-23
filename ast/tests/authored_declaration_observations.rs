//! Frozen source observations for the coordinated retained-header extension.
//! These tests call the existing parser/classifier; they do not construct a
//! parallel classifier or claim runtime decoder/payload correspondence.
use mettail_ast::language::{CollectionCategory, LanguageDef, NativeKind, NativeKindFromSynType};
use quote::quote;

#[test]
fn original_native_kind_census_preserves_all_twenty_variants_and_literal_families() {
    use NativeKind::*;
    let cases = [
        ("i8", Int8, Some("Integer"), true),
        ("i16", Int16, Some("Integer"), true),
        ("i32", Int32, Some("Integer"), true),
        ("i64", Int64, Some("Integer"), true),
        ("i128", Int128, Some("Integer"), true),
        ("isize", Isize, Some("Integer"), true),
        ("u8", UInt8, Some("Integer"), true),
        ("u16", UInt16, Some("Integer"), true),
        ("u32", UInt32, Some("Integer"), true),
        ("u64", UInt64, Some("Integer"), true),
        ("u128", UInt128, Some("Integer"), true),
        ("usize", Usize, Some("Integer"), true),
        ("f32", Float32, Some("Float"), false),
        ("f64", Float64, Some("Float"), false),
        ("bool", Bool, Some("Boolean"), false),
        ("str", Str, Some("StringLit"), false),
        ("CanonicalBigInt", CanonicalBigInt, None, true),
        ("CanonicalBigRat", CanonicalBigRat, None, false),
        ("CanonicalFixedPoint", CanonicalFixedPoint, None, false),
        ("UserPayload", Other, None, false),
    ];
    for (source, expected, token, integer) in cases {
        let ty: syn::Type = syn::parse_str(source).expect("native census case is a Rust type");
        let actual = NativeKind::from_syn_type(&ty);
        assert_eq!(actual, expected, "native source {source}");
        assert_eq!(actual.standard_token_variant(), token, "token family for {source}");
        assert_eq!(actual.is_integer(), integer, "integer observation for {source}");
    }
}

#[test]
fn original_native_classifier_uses_only_last_path_segment_and_rejects_nonpaths() {
    use NativeKind::*;
    for (source, expected) in [
        ("std::string::String", Str),
        ("host::CustomBigInt", CanonicalBigInt),
        ("host::BigIntExtra", Other),
        ("host::CanonicalBigRat", CanonicalBigRat),
        ("host::CustomBigRat", Other),
        ("host::CanonicalFixedPoint", CanonicalFixedPoint),
        ("host::i32<T>", Int32),
        ("&str", Other),
        ("[i32; 2]", Other),
        ("(i32, i32)", Other),
        ("fn() -> i32", Other),
        ("!", Other),
    ] {
        let ty: syn::Type = syn::parse_str(source).expect("path-shape census case parses");
        assert_eq!(NativeKind::from_syn_type(&ty), expected, "source {source}");
    }
    let empty_path = syn::Type::Path(syn::TypePath {
        qself: None,
        path: syn::Path {
            leading_colon: None,
            segments: Default::default(),
        },
    });
    assert_eq!(NativeKind::from_syn_type(&empty_path), Other);
}

#[test]
fn empty_rule_language_still_has_ordered_categories_and_distinct_native_presence() {
    let language: LanguageDef = syn::parse2(quote! {
        name: Retained,
        types { Plain ![UserPayload] as Wrapped ![i8] as Tiny data Closed },
        terms { }
    })
    .expect("declaration-only language parses without any grammar rule");
    assert!(language.terms.is_empty());
    let observations: Vec<_> = language
        .types
        .iter()
        .map(|category| {
            (
                category.name.to_string(),
                category.is_data(),
                category.native_type.as_ref().map(NativeKind::from_syn_type),
            )
        })
        .collect();
    assert_eq!(
        observations,
        vec![
            ("Plain".into(), false, None),
            ("Wrapped".into(), false, Some(NativeKind::Other)),
            ("Tiny".into(), false, Some(NativeKind::Int8)),
            ("Closed".into(), true, None),
        ]
    );
}

#[test]
fn literal_roster_follows_explicit_tokens_and_keeps_shared_family_occurrences() {
    let language: LanguageDef = syn::parse2(quote! {
        name: Retained,
        types { ![i8] as Tiny ![u32] as Wide ![CanonicalBigInt] as Big Plain },
        literals {
            Tiny { pattern: "tiny"; eval: ![tiny_eval(text)]; }
            Wide { pattern: "wide"; eval: ![wide_eval(text)]; }
            Big { pattern: "big"; eval: ![big_eval(text)]; }
            Plain { pattern: "plain"; eval: ![plain_eval(text)]; }
        },
        tokens {
            Explicit = "explicit" : Tiny ![explicit_eval(text)];
            NoEval = "none";
        },
        terms { }
    })
    .expect("literal and explicit token source fixture parses");
    let observations: Vec<_> = language
        .token_defs
        .iter()
        .map(|token| {
            (
                token.name.to_string(),
                token.category.as_ref().map(ToString::to_string),
                token.from_literals,
                token.rust_code.is_some(),
                token.pattern.as_str(),
            )
        })
        .collect();
    assert_eq!(
        observations,
        vec![
            ("Explicit".into(), Some("Tiny".into()), false, true, "explicit"),
            ("NoEval".into(), None, false, false, "none"),
            ("Integer".into(), Some("Tiny".into()), true, true, "tiny"),
            ("Integer".into(), Some("Wide".into()), true, true, "wide"),
            ("Big".into(), Some("Big".into()), true, true, "big"),
            ("Plain".into(), Some("Plain".into()), true, true, "plain"),
        ]
    );
    assert_eq!(language.token_defs[2].name, language.token_defs[3].name);
    assert_ne!(language.token_defs[2].category, language.token_defs[3].category);
}

#[test]
fn raw_mode_names_push_targets_and_nested_rosters_are_not_execution_qualified_names() {
    let language: LanguageDef = syn::parse2(quote! {
        name: Retained,
        types { Proc },
        tokens {
            Open = "open" push(body);
            raw mode body {
                Chunk = "chunk";
                Nested = "nested" push(body);
                Leave = "leave" pop;
            }
            mode other { Chunk = "other" push(body); }
        },
        terms { }
    })
    .expect("raw and ordinary mode declarations parse");
    assert_eq!(language.token_defs.len(), 1);
    assert_eq!(language.token_defs[0].name, "Open");
    assert_eq!(
        language.token_defs[0]
            .push_mode
            .as_ref()
            .expect("Open pushes body"),
        "body"
    );
    assert_eq!(
        language
            .mode_defs
            .iter()
            .map(|mode| mode.name.to_string())
            .collect::<Vec<_>>(),
        ["body", "other"]
    );
    assert!(language.mode_defs[0].raw);
    assert!(!language.mode_defs[1].raw);
    let body = &language.mode_defs[0].token_defs;
    assert_eq!(
        body.iter()
            .map(|token| token.name.to_string())
            .collect::<Vec<_>>(),
        ["Chunk", "Nested", "Leave"]
    );
    assert!(body[0].push_mode.is_none());
    assert_eq!(body[1].push_mode.as_ref().expect("Nested pushes body"), "body");
    assert!(body[2].is_pop);
    assert_eq!(body[0].name, language.mode_defs[1].token_defs[0].name);
    assert!(body.iter().all(|token| !token.from_literals));
}

#[test]
fn declared_collection_kind_and_all_delimiter_fields_remain_separate_from_native_type() {
    let language: LanguageDef = syn::parse2(quote! {
        name: Retained,
        types {
            ![UserPayload] as Map ["map-open", "map-close", ";", "=>"]
            ![UserPayload] as List ["", "]", "|"]
        },
        terms { }
    })
    .expect("collection declaration observations parse");
    let map = &language.types[0];
    assert_eq!(
        NativeKind::from_syn_type(map.native_type.as_ref().expect("Map has native type")),
        NativeKind::Other
    );
    let Some(CollectionCategory::Map(delimiters)) = &map.collection_kind else {
        panic!("Map declaration must retain its original declared collection variant");
    };
    assert_eq!(
        (
            &*delimiters.open,
            &*delimiters.close,
            &*delimiters.sep,
            delimiters.key_val_sep.as_deref()
        ),
        ("map-open", "map-close", ";", Some("=>"))
    );
    let Some(CollectionCategory::List(delimiters)) = &language.types[1].collection_kind else {
        panic!("List declaration must retain its original declared collection variant");
    };
    assert_eq!(
        (
            &*delimiters.open,
            &*delimiters.close,
            &*delimiters.sep,
            delimiters.key_val_sep.as_deref()
        ),
        ("", "]", "|", None)
    );
}
