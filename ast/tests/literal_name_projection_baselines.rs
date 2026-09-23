//! Original inline literal-name selector span/clone baselines.
//! Existing authored-declaration baselines cover names, roster order and flags;
//! these add only the original-name span and raw-clone distinctions.
use mettail_ast::language::LanguageDef;

#[test]
fn literal_name_original_mapped_name_uses_literal_occurrence_span() {
    let language: LanguageDef = syn::parse_str(
        r#"
        name: MappedSpan,
        types { ![i32] as r#Tiny },
        literals {
            r#Tiny { pattern: "tiny"; eval: ![tiny_eval(text)]; }
        },
        terms { }
        "#,
    )
    .expect("original mapped-name source fixture parses");
    let token = &language.token_defs[0];
    let original = token
        .category
        .as_ref()
        .expect("literal retains its original category");
    assert_eq!(original.to_string(), "r#Tiny");
    assert_eq!(token.name.to_string(), "Integer");
    assert_eq!(token.name.span().start(), original.span().start());
    assert_eq!(token.name.span().end(), original.span().end());
    assert_ne!(token.name.span().start(), language.types[0].name.span().start());
}

#[test]
fn literal_name_original_fallback_clones_raw_name_and_literal_span() {
    let language: LanguageDef = syn::parse_str(
        r#"
        name: CloneSpan,
        types { r#Plain ![OpaqueCarrier] as r#Opaque ![CanonicalBigInt] as r#Big },
        literals {
            r#Plain { pattern: "plain"; eval: ![plain_eval(text)]; }
            r#Opaque { pattern: "opaque"; eval: ![opaque_eval(text)]; }
            r#Big { pattern: "big"; eval: ![big_eval(text)]; }
        },
        terms { }
        "#,
    )
    .expect("original fallback source fixture parses");
    for (index, expected) in ["r#Plain", "r#Opaque", "r#Big"].into_iter().enumerate() {
        let token = &language.token_defs[index];
        let original = token
            .category
            .as_ref()
            .expect("literal retains its original category");
        assert_eq!(token.name, *original);
        assert_eq!(token.name.to_string(), expected);
        assert_eq!(token.name.span().start(), original.span().start());
        assert_eq!(token.name.span().end(), original.span().end());
        assert_ne!(token.name.span().start(), language.types[index].name.span().start());
    }
}
