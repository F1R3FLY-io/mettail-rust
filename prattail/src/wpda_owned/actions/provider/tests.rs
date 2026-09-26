use super::*;
use crate::automata::TokenKind;
use crate::runtime_backend::{compile_parser_image, RUNTIME_COMPILER_ABI, RUNTIME_UNICODE_ABI};
use crate::wpda_owned::source::SourceAdapterLimits;
use crate::wpda_runtime::WpdaTokenSource;
use mettail_grammar_core as core;

#[test]
fn collection_action_slot_borrows_direct_or_single_separated_payload_unchanged() {
    let collection = SyntaxItem::Collection {
        slot: "pieces".into(),
        key: None,
        element: CategoryId(7),
        separator: "inner".into(),
        kind: CollectionKind::List,
        key_value_separator: None,
    };
    let direct = collection_action_slot(&collection).expect("direct collection slot");
    assert_eq!((*direct.0, *direct.1), (CategoryId(7), CollectionKind::List));
    for separator in [",", "::", "λ", ""] {
        let wrapped = SyntaxItem::Separated {
            source: Box::new(collection.clone()),
            separator: separator.into(),
        };
        let original = wrapped.clone();
        let borrowed = collection_action_slot(&wrapped).expect("one separated collection slot");
        assert_eq!(borrowed, direct);
        // The caller's existing category/kind checks observe the exact payload.
        assert_ne!(*borrowed.0, CategoryId(8));
        assert_ne!(*borrowed.1, CollectionKind::Set);
        let SyntaxItem::Separated { source, .. } = &wrapped else {
            panic!("fixture is a separated wrapper");
        };
        let SyntaxItem::Collection { element, kind, .. } = source.as_ref() else {
            panic!("fixture wraps the original collection");
        };
        assert!(std::ptr::eq(borrowed.0, element));
        assert!(std::ptr::eq(borrowed.1, kind));
        assert_eq!(wrapped, original, "borrowing must not rewrite wrapper semantics");
    }
}

#[test]
fn collection_action_slot_refuses_keyed_nested_mapped_and_noncollection_sources() {
    let collection = SyntaxItem::Collection {
        slot: "pieces".into(),
        key: None,
        element: CategoryId(7),
        separator: String::new(),
        kind: CollectionKind::List,
        key_value_separator: None,
    };
    let mut keyed = collection.clone();
    let SyntaxItem::Collection { key, .. } = &mut keyed else {
        panic!("fixture is a collection");
    };
    *key = Some(CategoryId(3));
    let separated = SyntaxItem::Separated {
        source: Box::new(collection.clone()),
        separator: ",".into(),
    };
    let mapped = SyntaxItem::Mapped {
        source: Box::new(collection),
        bindings: vec!["piece".into()],
        body: Vec::new(),
    };
    for unsupported in [
        keyed,
        separated,
        mapped,
        SyntaxItem::Category {
            category: CategoryId(7),
            slot: "piece".into(),
        },
        SyntaxItem::Token(TokenId(0)),
    ] {
        // A nested Separated is refused, while a direct one is the supported case.
        if !matches!(&unsupported, SyntaxItem::Separated { .. }) {
            assert!(collection_action_slot(&unsupported).is_none());
        }
        let wrapped = SyntaxItem::Separated {
            source: Box::new(unsupported),
            separator: "outer".into(),
        };
        assert!(collection_action_slot(&wrapped).is_none());
    }
}

#[test]
fn provider_uses_actual_nonunit_source_boundaries_and_refuses_missing_context() {
    let mut grammar = core::GrammarCoreV1::new("ActionContext");
    grammar.categories.push(core::Category {
        id: core::CategoryId(0),
        name: "Expr".into(),
        carrier: core::Carrier::Dynamic,
        primary: true,
        admits_variables: false,
    });
    grammar.tokens.push(core::TokenDefinition {
        id: core::TokenId(0),
        name: "keyword".into(),
        pattern: core::TokenPattern::Literal("long".into()),
        category: Some(core::CategoryId(0)),
        evaluation: None,
        priority: 1,
        mode: core::ModeId(0),
        channel: "main".into(),
        transition: core::ModeTransition::default(),
        decoder: core::TokenDecoder::Text,
        reservation: core::Reservation::None,
    });
    grammar.modes[0].token_ids.push(core::TokenId(0));
    let mut coincident = grammar.tokens[0].clone();
    coincident.id = core::TokenId(1);
    coincident.name = "coincident-unit".into();
    coincident.decoder = core::TokenDecoder::Unit;
    grammar.tokens.push(coincident);
    grammar.modes[0].token_ids.push(core::TokenId(1));
    grammar.reductions.push(ReductionPlan {
        output_category: core::CategoryId(0),
        constructor: core::ConstructorId(0),
        input_arity: 0,
        fields: vec![],
        evaluation: None,
        evaluation_mode: None,
        tier: None,
    });
    grammar.productions.push(core::Production {
        authored: None,
        id: core::ProductionId(0),
        constructor: core::ConstructorId(0),
        label: "Long".into(),
        result: core::CategoryId(0),
        syntax: vec![core::SyntaxItem::Token(core::TokenId(0))],
        precedence: core::Precedence::default(),
        classification: core::ProductionClass::default(),
        reduction: 0,
        provenance: None,
    });
    let image = compile_parser_image(&grammar).expect("fixture image");
    let host = core::DefaultRuntimeHost;
    let parser = core::RuntimeParser::new(
        &grammar,
        &image,
        RUNTIME_COMPILER_ABI,
        RUNTIME_UNICODE_ABI,
        &host,
    )
    .expect("fixture parser");
    let session = parser.lexical_session("long").expect("lex once");
    let source = OwnedTokenSource::new(
        &session,
        SourceAdapterLimits { nodes: 16, edges: 16, text_bytes: 128 },
        |_, text| Ok::<_, std::convert::Infallible>(TokenKind::Fixed(text.into())),
    )
    .expect("source");
    let provider = OwnedActionProvider {
        semantic_keys: None,
        source: &source,
        core_categories: vec![core::CategoryId(0)],
        rows: vec![vec![Row {
            plan: Some(&grammar.reductions[0]),
            expected: vec![ANY_CAT],
            ignore_keyword: true,
            decode_literal: false,
            variable_category: None,
            literal_category: None,
            literal_token: None,
            inputs: Vec::new(),
            production: Some(core::ProductionId(0)),
            category_children: Vec::new(),
        }]],
    };
    let args = || {
        vec![ActionArg::Token {
            kind: TokenKind::Fixed("long".into()),
            text: "long".into(),
            pos: 0,
            occurrence: None,
        }]
    };
    let mut builder = SemanticBuilder::new();
    assert!(matches!(
        provider.execute_action(0, 0, &mut builder, args()),
        Err(ActionInvocationError::MissingActionContext)
    ));
    assert!(matches!(
        provider.execute_action_with_context(0, 0, &mut builder, args(), ActionContext::default()),
        Err(ActionInvocationError::MissingActionContext)
    ));
    assert_eq!(builder.len(), 0);
    let end = source.next_pos(0, 0).expect("accepted keyword edge");
    assert_eq!(source.position(end).unwrap().offset, 4);
    provider
        .execute_action_with_context(
            0,
            0,
            &mut builder,
            args(),
            ActionContext {
                source_positions: Some((0, end as u32)),
                result_category: Some(0),
            },
        )
        .expect("known context");
    let (value, _) = builder.top_term().expect("published carrier");
    let term = value.downcast_ref::<OwnedTerm>().expect("owned term");
    assert_eq!(term.span, SourceSpan { start: 0, end: 4 });
    let core::DynamicValue::Term(ref syntax) = term.syntax else {
        panic!("constructor")
    };
    assert_eq!(syntax.span, term.span);
    let mut invalid = SemanticBuilder::new();
    assert!(matches!(
        provider.execute_action_with_context(
            0,
            0,
            &mut invalid,
            args(),
            ActionContext {
                source_positions: Some((0, u32::MAX)),
                result_category: Some(0)
            }
        ),
        Err(ActionInvocationError::InvalidActionContext)
    ));
    assert_eq!(invalid.len(), 0);

    let mut literals = OwnedActionProvider {
        semantic_keys: None,
        source: &source,
        core_categories: vec![core::CategoryId(0)],
        rows: vec![vec![Row {
            plan: None,
            expected: vec![ANY_CAT],
            ignore_keyword: false,
            decode_literal: true,
            variable_category: None,
            literal_category: Some(core::CategoryId(0)),
            literal_token: None,
            inputs: Vec::new(),
            production: None,
            category_children: Vec::new(),
        }]],
    };
    let context = ActionContext {
        source_positions: Some((0, end as u32)),
        result_category: Some(0),
    };
    let mut missing = SemanticBuilder::new();
    assert!(matches!(
        literals.execute_action_with_context(0, 0, &mut missing, args(), context),
        Err(ActionInvocationError::MissingTokenOccurrence)
    ));
    assert_eq!(missing.len(), 0);
    for index in 0..2 {
        let edge = source
            .token_occurrence(0, index)
            .expect("both coincident declarations survive");
        let mut selected = args();
        let ActionArg::Token { occurrence, .. } = &mut selected[0] else {
            unreachable!()
        };
        *occurrence = Some(index as u32);
        let mut output = SemanticBuilder::new();
        literals
            .execute_action_with_context(0, 0, &mut output, selected, context)
            .expect("selected decoder");
        let (value, _) = output.top_term().unwrap();
        let term = value.downcast_ref::<OwnedTerm>().unwrap();
        let expected = match edge.token.0 {
            0 => core::DynamicValue::Text("long".into()),
            1 => core::DynamicValue::Unit,
            _ => panic!("no substituted token identity"),
        };
        assert_eq!(term.value, expected);
        assert_eq!(term.syntax, expected);
        assert_eq!(term.span, SourceSpan { start: 0, end: 4 });
    }
    assert!(source.token_occurrence(0, 2).is_none());
    let mut invalid_args = args();
    let ActionArg::Token { occurrence, .. } = &mut invalid_args[0] else {
        unreachable!()
    };
    *occurrence = Some(u32::MAX);
    assert!(matches!(
        literals.execute_action_with_context(0, 0, &mut missing, invalid_args, context),
        Err(ActionInvocationError::InvalidTokenOccurrence)
    ));
    assert_eq!(missing.len(), 0);

    let mut selected = args();
    let ActionArg::Token { occurrence, .. } = &mut selected[0] else {
        unreachable!()
    };
    *occurrence = Some(0);
    literals.rows[0][0].literal_category = Some(core::CategoryId(1));
    assert!(matches!(
        literals.execute_action_with_context(0, 0, &mut missing, selected.clone(), context),
        Err(ActionInvocationError::InvalidTokenOccurrence)
    ));
    literals.rows[0][0].literal_category = Some(core::CategoryId(0));
    let ActionArg::Token { text, .. } = &mut selected[0] else {
        unreachable!()
    };
    *text = "changed".into();
    assert!(matches!(
        literals.execute_action_with_context(0, 0, &mut missing, selected, context),
        Err(ActionInvocationError::InvalidTokenOccurrence)
    ));
    assert_eq!(missing.len(), 0);

    let mut plan = grammar.reductions[0].clone();
    plan.input_arity = 2;
    plan.fields = vec![core::FieldSource::Input(0), core::FieldSource::Input(1)];
    let collections = OwnedActionProvider {
        semantic_keys: None,
        source: &source,
        core_categories: vec![core::CategoryId(0)],
        rows: vec![vec![Row {
            plan: Some(&plan),
            expected: vec![ANY_CAT, ANY_CAT],
            ignore_keyword: false,
            decode_literal: false,
            variable_category: None,
            literal_category: None,
            literal_token: None,
            inputs: vec![
                Input::Collection { category: 0, kind: CollectionKind::List },
                Input::Collection { category: 0, kind: CollectionKind::List },
            ],
            production: Some(core::ProductionId(0)),
            category_children: Vec::new(),
        }]],
    };
    let item = |number| ActionArg::Term {
        value: std::sync::Arc::new(OwnedTerm {
            category: 0,
            production: None,
            syntax: DynamicValue::Text(format!("s{number}")),
            value: DynamicValue::Integer(number),
            span: SourceSpan { start: 0, end: 4 },
        }),
        type_name: "OwnedTerm",
    };
    let selected = |items| {
        ActionArg::SelectedCollection(
            crate::wpda_runtime::SelectedCollection::new(items).expect("selected terms"),
        )
    };
    let result = SemanticBuilder::invoke_selected_action_with(
        collections.action_signature(0, 0).unwrap(),
        vec![selected(vec![item(1), item(2), item(1)]), selected(vec![item(3)])],
        |builder, args| collections.execute_action_with_context(0, 0, builder, args, context),
    )
    .expect("original LIFO frame must accept reverse drains")
    .expect("published reduction")
    .try_into_term::<OwnedTerm>()
    .unwrap();
    assert_eq!(result.production, Some(core::ProductionId(0)));
    let DynamicValue::Term(ref value) = result.value else {
        panic!("reduction")
    };
    assert_eq!(
        value.fields,
        vec![
            DynamicValue::Collection {
                kind: CollectionKind::List,
                entries: vec![
                    DynamicValue::Integer(1),
                    DynamicValue::Integer(2),
                    DynamicValue::Integer(1)
                ]
            },
            DynamicValue::Collection {
                kind: CollectionKind::List,
                entries: vec![DynamicValue::Integer(3)]
            },
        ]
    );
    let DynamicValue::Term(ref syntax) = result.syntax else {
        panic!("syntax")
    };
    assert_eq!(
        syntax.fields,
        vec![
            DynamicValue::Collection {
                kind: CollectionKind::List,
                entries: vec![
                    DynamicValue::Text("s1".into()),
                    DynamicValue::Text("s2".into()),
                    DynamicValue::Text("s1".into())
                ]
            },
            DynamicValue::Collection {
                kind: CollectionKind::List,
                entries: vec![DynamicValue::Text("s3".into())]
            },
        ]
    );
}
