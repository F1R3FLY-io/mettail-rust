//! Frozen original native-family election and FIRST/home row behavior.
//! These call the original helpers; expected rows are literal quotations, not
//! a second native classifier or a parser for generated token text.
use super::*;
use mettail_ast::language::{CategoryRole, LangType, TokenDef};
use proc_macro2::Span;
use syn::parse_quote;

fn rows_text(rows: Vec<(TokenStream, Option<TokenStream>)>) -> Vec<(String, Option<String>)> {
    rows.into_iter()
        .map(|(pattern, guard)| (pattern.to_string(), guard.map(|value| value.to_string())))
        .collect()
}

fn guarded(pattern: TokenStream) -> (TokenStream, Option<TokenStream>) {
    (pattern, Some(quote! { __cat == "Value" }))
}

fn declaration(native: Option<Type>) -> LangType {
    LangType {
        name: Ident::new("Value", Span::call_site()),
        role: CategoryRole::Object,
        native_type: native,
        collection_kind: None,
    }
}

fn literal_token(name: &str) -> TokenDef {
    TokenDef {
        name: Ident::new(name, Span::call_site()),
        pattern: "original-pattern".into(),
        category: Some(Ident::new("Value", Span::call_site())),
        rust_code: Some(quote! { original_eval(text) }),
        priority: None,
        push_mode: None,
        is_pop: false,
        stream: None,
        from_literals: true,
    }
}

#[test]
fn native_first_baseline_all_original_native_kinds() {
    for kind in [
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
        NativeKind::CanonicalBigInt,
    ] {
        assert_eq!(literal_family_for(&kind), Some(LiteralFamily::Integer));
    }
    for (kind, family) in [
        (NativeKind::CanonicalBigRat, LiteralFamily::Rational),
        (NativeKind::CanonicalFixedPoint, LiteralFamily::FixedPoint),
        (NativeKind::Float32, LiteralFamily::Float),
        (NativeKind::Float64, LiteralFamily::Float),
        (NativeKind::Bool, LiteralFamily::Boolean),
        (NativeKind::Str, LiteralFamily::String),
    ] {
        assert_eq!(literal_family_for(&kind), Some(family));
    }
    assert_eq!(literal_family_for(&NativeKind::Other), None);
}

#[test]
fn native_first_baseline_integer_context_and_kind_matrix() {
    let typed = vec![
        guarded(quote! { Some(mettail_prattail::automata::TokenKind::IntegerLit(__cat)) }),
        guarded(quote! { Some(mettail_prattail::automata::TokenKind::Custom(__cat)) }),
    ];
    let mut with_bare = typed.clone();
    with_bare.push((quote! { Some(mettail_prattail::automata::TokenKind::Integer) }, None));
    // None is deliberately accepted in FIRST. Every unrelated Some kind is
    // deliberately rejected, even when the supplied family is Integer.
    for (kind, first_bare) in [
        (None, true),
        (Some(NativeKind::Int8), true),
        (Some(NativeKind::Int16), true),
        (Some(NativeKind::Int32), true),
        (Some(NativeKind::Int64), true),
        (Some(NativeKind::Int128), true),
        (Some(NativeKind::Isize), true),
        (Some(NativeKind::UInt8), true),
        (Some(NativeKind::UInt16), true),
        (Some(NativeKind::UInt32), true),
        (Some(NativeKind::UInt64), true),
        (Some(NativeKind::UInt128), true),
        (Some(NativeKind::Usize), true),
        (Some(NativeKind::CanonicalBigInt), false),
        (Some(NativeKind::CanonicalBigRat), false),
        (Some(NativeKind::CanonicalFixedPoint), false),
        (Some(NativeKind::Float32), false),
        (Some(NativeKind::Float64), false),
        (Some(NativeKind::Bool), false),
        (Some(NativeKind::Str), false),
        (Some(NativeKind::Other), false),
    ] {
        assert_eq!(
            rows_text(literal_patterned_pattern_and_guard_for_kind(
                "Value",
                LiteralFamily::Integer,
                kind.as_ref(),
                EmissionContext::FirstSet,
            )),
            rows_text(if first_bare {
                with_bare.clone()
            } else {
                typed.clone()
            }),
            "FIRST integer decision for {kind:?}",
        );
        assert_eq!(
            rows_text(literal_patterned_pattern_and_guard_for_kind(
                "Value",
                LiteralFamily::Integer,
                kind.as_ref(),
                EmissionContext::HomeCategory,
            )),
            rows_text(with_bare.clone()),
            "home integer decision for {kind:?}",
        );
    }
}

#[test]
fn native_first_baseline_other_families_exact_order_and_guards() {
    let fixtures = [
        (
            LiteralFamily::Rational,
            vec![
                guarded(quote! { Some(mettail_prattail::automata::TokenKind::RationalLit(__cat)) }),
                guarded(quote! { Some(mettail_prattail::automata::TokenKind::Custom(__cat)) }),
            ],
        ),
        (
            LiteralFamily::FixedPoint,
            vec![
                guarded(
                    quote! { Some(mettail_prattail::automata::TokenKind::FixedPointLit(__cat)) },
                ),
                guarded(quote! { Some(mettail_prattail::automata::TokenKind::Custom(__cat)) }),
            ],
        ),
        (
            LiteralFamily::Float,
            vec![(
                quote! {
                    Some(mettail_prattail::automata::TokenKind::Float)
                },
                None,
            )],
        ),
        (
            LiteralFamily::Boolean,
            vec![(
                quote! {
                    Some(mettail_prattail::automata::TokenKind::True)
                    | Some(mettail_prattail::automata::TokenKind::False)
                    | Some(mettail_prattail::automata::TokenKind::BooleanLit)
                },
                None,
            )],
        ),
        (
            LiteralFamily::String,
            vec![(
                quote! {
                    Some(mettail_prattail::automata::TokenKind::StringLit)
                },
                None,
            )],
        ),
        (
            LiteralFamily::Custom,
            vec![guarded(quote! {
                Some(mettail_prattail::automata::TokenKind::Custom(__cat))
            })],
        ),
    ];
    for (family, expected) in fixtures {
        assert!(home_polymorphic_token_arm(family).is_none());
        for context in [EmissionContext::HomeCategory, EmissionContext::FirstSet] {
            for kind in [None, Some(NativeKind::Int32), Some(NativeKind::Other)] {
                assert_eq!(
                    rows_text(literal_patterned_pattern_and_guard_for_kind(
                        "Value",
                        family,
                        kind.as_ref(),
                        context,
                    )),
                    rows_text(expected.clone()),
                    "exact row order/guards for {family:?} {context:?} {kind:?}",
                );
            }
        }
    }
    assert_eq!(
        home_polymorphic_token_arm(LiteralFamily::Integer)
            .expect("Integer has the sole original bare home arm")
            .to_string(),
        quote! { Some(mettail_prattail::automata::TokenKind::Integer) }.to_string(),
    );
}

#[test]
fn native_first_baseline_first_eligible_token_preserves_payload_identity() {
    let mut language = crate::gen::empty_language_for_tests();
    language
        .types
        .push(declaration(Some(parse_quote!(OpaqueCarrier))));
    let mut not_literals = literal_token("NotLiterals");
    not_literals.from_literals = false;
    let mut no_eval = literal_token("NoEval");
    no_eval.rust_code = None;
    let mut no_category = literal_token("NoCategory");
    no_category.category = None;
    let mut wrong_category = literal_token("WrongCategory");
    wrong_category.category = Some(Ident::new("Other", Span::call_site()));
    let first = literal_token("FirstEligible");
    let mut later = literal_token("LaterEligible");
    later.rust_code = Some(quote! { later_eval_must_not_win(text) });
    language.token_defs = vec![not_literals, no_eval, no_category, wrong_category, first, later];
    let selected = declared_literal_token_def("Value", &language)
        .expect("the fifth declaration is the first eligible literal");
    assert!(std::ptr::eq(selected, &language.token_defs[4]));
    assert_eq!(selected.name, "FirstEligible");
    assert_eq!(literal_family_for_category("Value", &language), Some(LiteralFamily::Custom));
    assert!(declared_literal_token_def("Missing", &language).is_none());
}

#[test]
fn native_first_baseline_category_first_match_and_native_presence() {
    let mut language = crate::gen::empty_language_for_tests();
    language.token_defs.push(literal_token("ValueToken"));
    assert_eq!(literal_family_for_category("Value", &language), None);
    language.types.push(declaration(None));
    language.types.push(declaration(Some(parse_quote!(i32))));
    assert_eq!(literal_family_for_category("Value", &language), None);
    language.types[0].native_type = Some(parse_quote!(OpaqueCarrier));
    assert_eq!(literal_family_for_category("Value", &language), Some(LiteralFamily::Custom));
    language.token_defs.clear();
    assert_eq!(literal_family_for_category("Value", &language), None);
    language.types[0].native_type = Some(parse_quote!(i32));
    assert_eq!(literal_family_for_category("Value", &language), Some(LiteralFamily::Integer));
    language
        .token_defs
        .push(literal_token("CustomCannotOverrideBuiltin"));
    assert_eq!(literal_family_for_category("Value", &language), Some(LiteralFamily::Integer));
}
