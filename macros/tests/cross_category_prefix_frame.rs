use std::sync::Arc;

use proptest::prelude::*;

mettail_macros::language! {
    name: CrossCategoryPrefixFrame,
    options { emit_tests: false, emit_simulator: false, emit_blockly: false },
    types { noadmit Value noadmit Name },
    terms {
        Empty . |- "empty" : Value;
        Unit . |- "(" ")" : Value;
        Word . |- text@Ident : Name;
        Unquote . name:Name |- "*" name : Value;
        Quote . value:Value |- "@" value : Name prefix(220);
        QuoteMarked . value:Value |- "@" "[" value "]" : Name;
        Loose . value:Value |- "#" value : Name prefix(0);
        LooseMarked . value:Value |- "#" "[" value "]" : Name;
        Tight . value:Value |- "~" value : Value prefix(220);
        TightMarked . value:Value |- "~" "[" value "]" : Value;
        Method . receiver:Value, method:Ident, arguments:Vec(Value)
            |- receiver "." method "(" arguments.*sep(",") ")" : Value;
    },
    equations {},
    rewrites {},
}

#[test]
fn foreign_prefix_postfix_tail_obeys_the_enclosing_prefix_floor() {
    let receiver = Value::Unquote(Arc::new(Name::Word("a".into())));
    let method = Value::Method(Arc::new(receiver), "call".into(), vec![Value::Empty]);
    let expected = Name::Quote(Arc::new(method));
    let bare = "@*a.call(empty)";
    assert!(Name::__all_with_weights_monolithic(bare).is_err());
    assert!(Name::parse(bare).is_err(), "the facade must preserve the declared prefix floor");
    let grouped = "@(*a.call(empty))";
    let (readings, _) = Name::__all_with_weights_monolithic(grouped).expect("grouped main parser");
    assert!(readings.contains(&expected));
    assert_eq!(Name::parse(grouped).expect("grouped facade"), expected);
    assert_eq!(expected.to_string(), grouped);
}

#[test]
fn a_literal_primary_does_not_absorb_a_local_postfix_tail() {
    assert_eq!(
        Value::parse_via_wpda_in_lexer_mode("empty", None).expect("default entry"),
        Value::Empty
    );
    assert!(Value::parse_via_wpda_in_lexer_mode("empty", Some("missing")).is_err());
    assert!(Value::parse_via_wpda_all_with_weights_in_lexer_mode("empty", Some("missing")).is_err());
    let expected = Name::Quote(Arc::new(Value::Method(
        Arc::new(Value::Unit),
        "call".into(),
        vec![Value::Empty],
    )));
    assert!(Name::parse("@().call(empty)").is_err());
    let source = expected.to_string();
    assert_eq!(Name::parse(&source).expect("grouped facade"), expected);
    let (readings, _) = Name::__all_with_weights_monolithic(&source).expect("grouped main parser");
    assert!(readings.contains(&expected));
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(64))]

    #[test]
    fn isolated_prefix_preserves_floor_payload_and_span(
        word in "[A-Z]{1,5}", method in "[a-z]{1,5}",
        unit in any::<bool>(), depth in 1usize..4, high_floor in 220u8..=255,
    ) {
        let mut body = if unit {
            Value::Unit
        } else {
            Value::Unquote(Arc::new(Name::Word(word)))
        };
        for _ in 0..depth {
            body = Value::Method(Arc::new(body), method.clone(), vec![Value::Empty]);
        }
        let source = body.to_string();
        let zero = Value::__all_with_weights_monolithic_at_min_bp(&source, 0)
            .map_err(|error| TestCaseError::fail(format!("zero floor {source:?}: {error:?}")))?;
        let original = Value::__all_with_weights_monolithic(&source)
            .map_err(|error| TestCaseError::fail(format!("original {source:?}: {error:?}")))?;
        prop_assert_eq!(zero, original);
        prop_assert!(Value::__all_with_weights_monolithic_at_min_bp(&source, high_floor).is_err());
        prop_assert!(Value::__parse_via_wpda_monolithic_at_min_bp(&source, high_floor).is_err());
        let grouped = format!("({source})");
        let (readings, weights) = Value::__all_with_weights_monolithic_at_min_bp(&grouped, high_floor)
            .map_err(|error| TestCaseError::fail(format!("grouped floor {grouped:?}: {error:?}")))?;
        let unrestricted = Value::__all_with_weights_monolithic(&grouped)
            .map_err(|error| TestCaseError::fail(format!("grouped zero floor {grouped:?}: {error:?}")))?;
        prop_assert_eq!((&readings, &weights), (&unrestricted.0, &unrestricted.1));
        prop_assert!(readings.contains(&body));
        prop_assert_eq!(readings.len(), weights.len());
        let chosen = Value::__parse_via_wpda_monolithic_at_min_bp(&grouped, high_floor)
            .map_err(|error| TestCaseError::fail(format!("grouped single {grouped:?}: {error:?}")))?;
        prop_assert_eq!(&chosen, &body);
        let bare_quote = format!("@{source}");
        prop_assert!(Name::__all_with_weights_monolithic(&bare_quote).is_err());
        prop_assert!(Name::parse_via_wpda_all_with_weights(&bare_quote).is_err());
        prop_assert!(Name::parse_via_wpda(&bare_quote).is_err());
        let grouped_quote = format!("@({source})");
        let expected = Name::Quote(Arc::new(body.clone()));
        let (readings, _) = Name::parse_via_wpda_all_with_weights(&grouped_quote)
            .map_err(|error| TestCaseError::fail(format!("quote all {grouped_quote:?}: {error:?}")))?;
        prop_assert!(readings.contains(&expected));
        prop_assert_eq!(Name::parse_via_wpda(&grouped_quote).expect("grouped quote"), expected);
        let loose = format!("#{source}");
        let expected = Name::Loose(Arc::new(body));
        let (readings, _) = Name::parse_via_wpda_all_with_weights(&loose)
            .map_err(|error| TestCaseError::fail(format!("loose all {loose:?}: {error:?}")))?;
        prop_assert!(readings.contains(&expected));
        prop_assert_eq!(Name::parse_via_wpda(&loose).expect("zero-floor quote"), expected);
        let trailing = format!("{grouped} stray");
        prop_assert!(Value::__all_with_weights_monolithic_at_min_bp(&trailing, high_floor).is_err());
        prop_assert!(Value::__parse_via_wpda_monolithic_at_min_bp(&trailing, high_floor).is_err());
    }

    #[test]
    fn local_prefix_keeps_postfix_outside_its_operand(method in "[a-z]{1,5}") {
        let body = Value::Method(Arc::new(Value::Unit), method.clone(), vec![Value::Empty]);
        let wrong = Value::Tight(Arc::new(body.clone()));
        let expected = Value::Method(
            Arc::new(Value::Tight(Arc::new(Value::Unit))), method, vec![Value::Empty],
        );
        let bare = format!("~{body}");
        let (readings, _) = Value::parse_via_wpda_all_with_weights(&bare)
            .map_err(|error| TestCaseError::fail(format!("local prefix {bare:?}: {error:?}")))?;
        prop_assert!(readings.contains(&expected));
        prop_assert!(!readings.contains(&wrong));
        prop_assert_eq!(Value::parse_via_wpda(&bare).expect("local prefix single"), expected);
        let grouped = format!("~({body})");
        prop_assert_eq!(Value::parse_via_wpda(&grouped).expect("grouped local prefix"), wrong);
    }
}

mod inactive_floor {
    use super::*;

    mettail_macros::language! {
        name: InactivePrefixFloor,
        options { emit_tests: false, emit_simulator: false, emit_blockly: false },
        types { noadmit Expr noadmit Label },
        terms {
            Atom . |- text@Ident : Expr;
            LabelText . |- text@Ident : Label;
            Drop . label:Label |- "*" label : Expr;
            DropMarked . label:Label |- "*" "[" label "]" : Expr;
            Emit . label:Label, body:Expr |- label "!" "(" body ")" : Expr;
            Quote . body:Expr |- "@" "(" body ")" : Label;
            QuoteShort . body:Expr |- "@" body : Label ![{ Label::Quote(Arc::new(body.clone())) }] fold prefix(220) canonical;
            Group . label:Label |- "(" label ")" : Label ![{ label.clone() }] fold;
            Add . left:Expr, right:Expr |- left "+" right : Expr;
        },
        equations {},
        rewrites {},
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(64))]

        #[test]
        fn inactive_floor_preserves_isolated_operand_selection(
            word in "[A-Z]{1,5}", right in "[A-Z]{1,5}", floor in 0u8..=2,
        ) {
            let operand = format!("(@({word}))");
            let chosen = Label::parse(&operand).expect("isolated label");
            let expected = Expr::Drop(Arc::new(chosen));
            let source = format!("*{operand}");
            prop_assert_eq!(Expr::parse(&source).expect("isolated prefix"), expected);
            let specific = Label::Group(Arc::new(Label::Quote(Arc::new(Expr::Atom(word)))));
            let expected = Expr::Add(
                Arc::new(Expr::Drop(Arc::new(specific))), Arc::new(Expr::Atom(right.clone())),
            );
            let source = format!("{source} + {right}");
            let (readings, weights) = Expr::parse_via_wpda_all_with_weights(&source)
                .expect("prefix in addition");
            prop_assert!(readings.contains(&expected), "missing {:?} in {:?}", expected, readings);
            prop_assert_eq!(readings.len(), weights.len());
            prop_assert_eq!(
                Expr::__all_with_weights_monolithic_at_min_bp(&source, floor).expect("inactive floor"),
                Expr::__all_with_weights_monolithic_at_min_bp(&source, 0).expect("zero floor"),
            );
        }
    }
}
