use std::sync::Arc;

use proptest::prelude::*;

mettail_macros::language! {
    name: PrefixPostfixOperand,
    options { emit_tests: false, emit_simulator: false, emit_blockly: false },
    types { noadmit Value noadmit Name noadmit Marker noadmit Envelope },
    terms {
        Empty . |- "empty" : Value;
        Unit . |- "(" ")" : Value;
        SigilEmpty . |- "@" "empty" "!" "(" ")" : Value;
        Inspect . receiver:Value, payload:Value |- receiver "[" payload "]" : Value;
        Method . receiver:Value, arguments:Vec(Value)
            |- receiver "." name@Ident "(" arguments.*sep(",") ")" : Value;
        Quote . value:Value |- "@" value : Name prefix(220);
        Mark . value:Value |- "#" value : Marker prefix(220);
        Take . name:Name |- "<-" name : Envelope;
        Send . name:Name, payload:Value |- name "!" "(" payload ")" : Value;
    },
    equations {},
    rewrites {},
}

#[test]
fn prefix_operands_retain_postfix_tails() {
    let mut failures = Vec::new();
    for value in sample_operands() {
        let quote = Name::Quote(Arc::new(value.clone()));
        let source = quote.to_string();
        match Name::parse(&source) {
            Ok(actual) if actual == quote => {},
            other => failures.push(format!("quote {source:?}: {other:?}")),
        }
        match Name::__all_with_weights_monolithic(&source) {
            Ok((terms, _)) if terms.contains(&quote) => {},
            other => failures.push(format!("main quote {source:?}: {other:?}")),
        }
        let marked = Marker::Mark(Arc::new(value));
        let source = marked.to_string();
        match Marker::parse(&source) {
            Ok(actual) if actual == marked => {},
            other => failures.push(format!("mark {source:?}: {other:?}")),
        }
        let envelope = Envelope::Take(Arc::new(quote));
        let source = envelope.to_string();
        match Envelope::parse(&source) {
            Ok(actual) if actual == envelope => {},
            other => failures.push(format!("envelope {source:?}: {other:?}")),
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

fn sample_operands() -> [Value; 4] {
    [
        Value::Inspect(Arc::new(Value::Unit), Arc::new(Value::Empty)),
        Value::Inspect(Arc::new(Value::SigilEmpty), Arc::new(Value::Empty)),
        Value::Method(Arc::new(Value::Unit), "A".into(), Vec::new()),
        Value::Method(Arc::new(Value::SigilEmpty), "A".into(), Vec::new()),
    ]
}

#[test]
fn quoted_postfix_channel_preserves_enclosing_send() {
    let mut failures = Vec::new();
    for value in sample_operands() {
        let quote = Name::Quote(Arc::new(value));
        let send = Value::Send(Arc::new(quote.clone()), Arc::new(Value::Empty));
        let source = send.to_string();
        match Value::parse(&source) {
            Ok(actual) if actual == send => {},
            other => failures.push(format!("send {source:?}: {other:?}")),
        }
        match Value::__all_with_weights_monolithic(&source) {
            Ok((terms, _)) if terms.contains(&send) => {},
            other => failures.push(format!("main send {source:?}: {other:?}")),
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

fn postfix_values() -> impl Strategy<Value = Value> {
    prop_oneof![Just(Value::Empty), Just(Value::Unit), Just(Value::SigilEmpty)].prop_recursive(
        2,
        12,
        3,
        |inner| {
            prop_oneof![
                (inner.clone(), inner.clone()).prop_map(|(receiver, payload)| Value::Inspect(
                    Arc::new(receiver),
                    Arc::new(payload)
                )),
                (inner.clone(), "[A-Z]{1,4}", proptest::collection::vec(inner, 0..3)).prop_map(
                    |(receiver, name, arguments)| Value::Method(
                        Arc::new(receiver),
                        name,
                        arguments
                    )
                ),
            ]
        },
    )
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(64))]

    #[test]
    fn enclosing_send_preserves_complete_postfix_trees(value in postfix_values()) {
        let expected = Value::Send(Arc::new(Name::Quote(Arc::new(value))), Arc::new(Value::Empty));
        let source = expected.to_string();
        let (readings, _) = Value::__all_with_weights_monolithic(&source)
            .map_err(|error| TestCaseError::fail(format!("main send {source:?}: {error:?}")))?;
        prop_assert!(readings.contains(&expected));
        let actual = Value::parse(&source)
            .map_err(|error| TestCaseError::fail(format!("send {source:?}: {error:?}")))?;
        prop_assert_eq!(actual, expected);
    }

    #[test]
    fn prefix_roundtrip_preserves_complete_postfix_trees(value in postfix_values()) {
        let unwrapped = format!("@() [{value}]");
        prop_assert!(Name::parse(&unwrapped).is_err(), "an ungrouped local tail must remain outside the prefix operand");
        let quote = Name::Quote(Arc::new(value.clone()));
        let source = quote.to_string();
        let (readings, _) = Name::__all_with_weights_monolithic(&source)
            .map_err(|error| TestCaseError::fail(format!("main quote {source:?}: {error:?}")))?;
        prop_assert!(readings.contains(&quote));
        let actual = Name::parse(&source)
            .map_err(|error| TestCaseError::fail(format!("quote {source:?}: {error:?}")))?;
        prop_assert_eq!(actual, quote);
        let mark = Marker::Mark(Arc::new(value));
        let source = mark.to_string();
        let actual = Marker::parse(&source)
            .map_err(|error| TestCaseError::fail(format!("mark {source:?}: {error:?}")))?;
        prop_assert_eq!(actual, mark);
    }
}

#[test]
fn parenthesized_quoted_postfix_channel_preserves_enclosing_send() {
    let mut failures = Vec::new();
    for value in sample_operands() {
        let quote = Name::Quote(Arc::new(value));
        let expected = Value::Send(Arc::new(quote.clone()), Arc::new(Value::Empty));
        let source = format!("({quote})!(empty)");
        match Value::__all_with_weights_monolithic(&source) {
            Ok((readings, _)) if readings.contains(&expected) => {},
            other => failures.push(format!("main {source:?}: {other:?}")),
        }
        match Value::parse(&source) {
            Ok(actual) if actual == expected => {},
            other => failures.push(format!("facade {source:?}: {other:?}")),
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}
