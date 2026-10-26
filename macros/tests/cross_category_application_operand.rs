use std::sync::Arc;

use proptest::prelude::*;

mettail_macros::language! {
    name: ApplicationOperand,
    options { emit_tests: false, emit_simulator: false, emit_blockly: false },
    types { noadmit Value data Head noadmit Envelope },
    terms {
        Empty . |- "empty" : Value;
        HeadName . |- name@Ident : Head;
        Difference . left:Value, right:Value |- left "-" right : Value;
        Application . head:Head, arguments:Vec(Value)
            |- head "(" arguments.*sep(",") ")" : Value;
        Reference . head:Head |- head : Value;
        EnvelopeValue . body:Value |- "mark" body : Envelope prefix(0);
    },
    equations {},
    rewrites {},
}

#[test]
fn application_operand_keeps_its_enclosing_continuation() {
    let application = Value::Application(Arc::new(Head::HeadName("A".into())), Vec::new());
    let difference = Value::Difference(Arc::new(Value::Empty), Arc::new(application.clone()));
    let mut failures = Vec::new();
    for (source, expected) in [
        ("A()", &application),
        ("empty - A()", &difference),
        ("(empty - A())", &difference),
    ] {
        match Value::__all_with_weights_monolithic(source) {
            Ok((terms, _)) if terms.contains(expected) => {},
            other => failures.push(format!("main parser {source:?}: {other:?}")),
        }
        match Value::parse(source) {
            Ok(actual) if &actual == expected => {},
            other => failures.push(format!("facade {source:?}: {other:?}")),
        }
    }
    let expected = Envelope::EnvelopeValue(Arc::new(difference));
    match Envelope::parse("mark empty - A()") {
        Ok(actual) if actual == expected => {},
        other => failures.push(format!("envelope: {other:?}")),
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

fn value_sources() -> impl Strategy<Value = (String, Value)> {
    Just(("empty".to_owned(), Value::Empty)).prop_recursive(3, 20, 3, |inner| {
        prop_oneof![
            (inner.clone(), inner.clone()).prop_map(
                |((left_source, left), (right_source, right))| {
                    (
                        format!("({left_source} - {right_source})"),
                        Value::Difference(Arc::new(left), Arc::new(right)),
                    )
                }
            ),
            ("[A-Z]{1,4}", proptest::collection::vec(inner, 0..3)).prop_map(|(name, arguments)| {
                let source = format!(
                    "{}({})",
                    name,
                    arguments
                        .iter()
                        .map(|(source, _)| source.as_str())
                        .collect::<Vec<_>>()
                        .join(",")
                );
                let value = Value::Application(
                    Arc::new(Head::HeadName(name)),
                    arguments.into_iter().map(|(_, value)| value).collect(),
                );
                (source, value)
            }),
        ]
    })
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(64))]

    #[test]
    fn leading_application_preserves_nested_operands_and_enclosing_context(
        (source, expected) in value_sources(),
    ) {
        for input in [source.clone(), format!("({source})")] {
            let (readings, _) = Value::__all_with_weights_monolithic(&input)
                .map_err(|error| TestCaseError::fail(format!("main parser {input:?}: {error:?}")))?;
            prop_assert!(readings.contains(&expected), "main parser {input:?}: {readings:?}");
            let actual = Value::parse(&input)
                .map_err(|error| TestCaseError::fail(format!("facade {input:?}: {error:?}")))?;
            prop_assert_eq!(&actual, &expected);
        }
        let input = format!("mark {source}");
        let actual = Envelope::parse(&input)
            .map_err(|error| TestCaseError::fail(format!("envelope {input:?}: {error:?}")))?;
        prop_assert_eq!(actual, Envelope::EnvelopeValue(Arc::new(expected)));
    }
}
