use super::*;
use crate::gen::runtime::wpda_codegen::authored_capture::{capture_language, capture_rules};
use crate::gen::runtime::wpda_codegen::guest_mode_descriptor_baselines as guest_fixtures;
use mettail_grammar_core::AuthoredRuleId;
use mettail_prattail::wpda_rule_analysis::authored::AuthoredRuleReader;
use mettail_prattail::wpda_rule_analysis::authored_binder::{
    derive_authored_binder, AuthoredBinderError,
};
use mettail_prattail::wpda_rule_analysis::binder::BinderNumericError;
use std::convert::Infallible;

pub(super) fn classify_owned(rule: &GrammarRule, language: &LanguageDef) -> Option<BinderShape> {
    let mut source = language.clone();
    source.terms = vec![rule.clone()];
    let captured = capture_language(&source).expect("capture the original rule and declarations");
    let reader = AuthoredRuleReader::new(&captured.store).expect("captured reader");
    derive_authored_binder(&reader, AuthoredRuleId(captured.roots[0]), |_, _, _| {
        Ok::<_, Infallible>(())
    })
    .expect("representable owned binder derivation")
}

fn assert_language_parity(rule: &GrammarRule, language: &LanguageDef) -> BinderShape {
    let original = classify_binder_in(rule, language).expect("original accepts fixture");
    let owned = classify_owned(rule, language).expect("owned accepts fixture");
    assert_eq!(format!("{owned:?}"), format!("{original:?}"));
    owned
}

#[test]
fn retained_guest_modes_preserve_order_duplicates_and_first_opener() {
    let mut flagged = guest_fixtures::token("Flagged", Some("Guest"));
    flagged.is_pop = true;
    flagged.stream = Some(id("comments"));
    flagged.from_literals = true;
    let mut source = guest_fixtures::language(
        vec![guest_fixtures::token("Open", Some("Guest"))],
        vec![guest_fixtures::mode(
            "Guest",
            vec![
                guest_fixtures::token("Z", Some("Guest")),
                guest_fixtures::token("Subregion", Some("Comment")),
                guest_fixtures::token("Plain", None),
                guest_fixtures::token("A", Some("Guest")),
                guest_fixtures::token("Z", Some("Guest")),
                flagged,
            ],
        )],
    );
    for expected in [vec!["Z", "A", "Z", "Flagged"], Vec::new()] {
        let mid = rule(Vec::new(), vec![literal("start"), guest()]);
        let shape = assert_language_parity(&mid, &source);
        let [BinderPosition::GuestBodyCapture { nested_open_kinds, .. }] = &shape.positions[..]
        else {
            panic!("expected a mid-rule guest capture");
        };
        assert_eq!(nested_open_kinds, &expected);

        let nested = rule(
            Vec::new(),
            vec![literal("start"), SyntaxExpr::Op(PatternOp::Opt { inner: vec![guest()] })],
        );
        let shape = assert_language_parity(&nested, &source);
        let [BinderPosition::OptionalGroup { positions, .. }] = &shape.positions[..] else {
            panic!("expected an optional guest group");
        };
        let [BinderPosition::GuestBodyCapture { nested_open_kinds, .. }] = &positions[..] else {
            panic!("expected the nested guest capture");
        };
        assert_eq!(nested_open_kinds, &expected);

        let leading = assert_language_parity(&rule(Vec::new(), vec![guest()]), &source);
        assert!(leading.positions.is_empty());
        assert!(matches!(leading.action_args.as_slice(), [ActionArgKind::GuestBody { .. }]));
        source
            .token_defs
            .insert(0, guest_fixtures::token("Open", None));
    }
}

#[test]
fn binder_slot_kind_controls_retained_declared_separator() {
    use mettail_ast::language::{CollectionCategory, LangType};

    let mut source = language();
    let mut delimiters = CollectionCategory::map_defaults();
    delimiters.key_val_sep = Some(String::new());
    source.types.push(LangType {
        name: id("Expr"),
        role: Default::default(),
        native_type: None,
        collection_kind: Some(CollectionCategory::Map(delimiters)),
    });
    for (slot_kind, expected) in [(CollectionType::Vec, None), (CollectionType::HashMap, Some(""))]
    {
        let fixture = rule(
            vec![simple("items", collection(slot_kind, "Name"))],
            vec![literal("start"), sep("items")],
        );
        let shape = assert_language_parity(&fixture, &source);
        let [BinderPosition::ParamParse { collection: Some(info), .. }] = &shape.positions[..]
        else {
            panic!("expected collection slot");
        };
        assert_eq!(info.key_val_separator.as_deref(), expected);
    }
    source.types.insert(
        0,
        LangType {
            name: id("Expr"),
            role: Default::default(),
            native_type: None,
            collection_kind: None,
        },
    );
    let fixture = rule(
        vec![simple("items", collection(CollectionType::HashMap, "Name"))],
        vec![literal("start"), sep("items")],
    );
    let shape = assert_language_parity(&fixture, &source);
    let [BinderPosition::ParamParse { collection: Some(info), .. }] = &shape.positions[..] else {
        panic!("expected collection slot");
    };
    assert_eq!(info.key_val_separator.as_deref(), Some(":"));
}

#[test]
fn missing_header_and_denial_precede_rule_observation() {
    let fixture = rule(Vec::new(), vec![token(None)]);
    let captured = capture_rules(&[fixture.clone()]).expect("header-free capture");
    let reader = AuthoredRuleReader::new(&captured.store).expect("captured reader");
    let result = derive_authored_binder(
        &reader,
        AuthoredRuleId(u32::MAX),
        |_, _, _| -> Result<(), Infallible> {
            panic!("missing header must precede admission");
        },
    );
    assert!(matches!(result, Err(AuthoredBinderError::MissingDeclarations)));

    let mut source = language();
    source.terms = vec![fixture];
    let captured = capture_language(&source).expect("language capture");
    let reader = AuthoredRuleReader::new(&captured.store).expect("captured reader");
    let mut calls = 0;
    let result =
        derive_authored_binder(&reader, AuthoredRuleId(u32::MAX), |observed, rule, header| {
            calls += 1;
            assert!(std::ptr::eq(observed, &reader));
            assert!(std::ptr::eq(header, captured.store.declarations().expect("retained header")));
            assert_eq!(rule, AuthoredRuleId(u32::MAX));
            Err(7)
        });
    assert!(matches!(result, Err(AuthoredBinderError::Admission(7))));
    assert_eq!(calls, 1);
}

#[test]
fn owned_numeric_refusal_is_not_structural_nonmatch() {
    let mut syntax = vec![literal("start")];
    syntax.extend((0..256).map(|_| param("value")));
    let mut source = language();
    source.terms = vec![rule(vec![simple("value", base("Expr"))], syntax)];
    let captured = capture_language(&source).expect("capture over-width fixture");
    let reader = AuthoredRuleReader::new(&captured.store).expect("captured reader");
    let mut calls = 0;
    let result = derive_authored_binder(&reader, AuthoredRuleId(captured.roots[0]), |_, _, _| {
        calls += 1;
        Ok::<_, Infallible>(())
    });
    assert!(matches!(
        result,
        Err(AuthoredBinderError::Numeric(BinderNumericError::FinalActionArity))
    ));
    assert_eq!(calls, 1);
}
