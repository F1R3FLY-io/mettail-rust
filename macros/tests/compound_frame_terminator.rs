use std::sync::Arc;

use proptest::prelude::*;

mettail_macros::language! {
    name: CompoundFrameTerminator,
    options { emit_tests: false, emit_simulator: false, emit_blockly: false },
    types { noadmit Value noadmit Tag },
    terms {
        Empty . |- "empty" : Value;
        TagLeaf . |- "tag" : Tag;
        Hash . value:Value |- "#" value : Tag prefix(220);
        Equal . left:Value, right:Value |- left "==" right : Value;
        Remainder . left:Value, right:Value |- left "%" right : Value;
        Less . left:Value, right:Value |- left "<" right : Value;
        Greater . left:Value, right:Value |- left ">" right : Value;
        Frame . body:Value, tag:Tag |- "<%" body "%>" "[" tag "]" : Value;
    },
    equations {},
    rewrites {},
}

#[test]
fn compound_frame_terminator_preserves_operator_bodies() {
    let mut failures = Vec::new();
    for body in [Value::Empty, Value::Equal(Arc::new(Value::Empty), Arc::new(Value::Empty))] {
        let expected = Value::Frame(Arc::new(body), Arc::new(Tag::TagLeaf));
        let source = expected.to_string();
        match Value::parse(&source) {
            Ok(actual) if actual == expected => {},
            other => failures.push(format!("facade {source:?}: {other:?}")),
        }
        match Value::__all_with_weights_monolithic(&source) {
            Ok((values, _)) if values.contains(&expected) => {},
            other => failures.push(format!("main {source:?}: {other:?}")),
        }
        let tagged = Tag::Hash(Arc::new(expected));
        let source = tagged.to_string();
        match Tag::parse(&source) {
            Ok(actual) if actual == tagged => {},
            other => failures.push(format!("tagged {source:?}: {other:?}")),
        }
    }
    for source in [
        "<%empty == empty%>[tag]",
        "<%empty == empty %>[tag]",
        "<% empty == empty %> [tag]",
    ] {
        if let Err(error) = Value::parse(source) {
            failures.push(format!("spacing {source:?}: {error}"));
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

fn frame_bodies() -> impl Strategy<Value = Value> {
    Just(Value::Empty).prop_recursive(3, 20, 2, |inner| {
        prop_oneof![
            (inner.clone(), inner.clone())
                .prop_map(|(a, b)| Value::Equal(Arc::new(a), Arc::new(b))),
            (inner.clone(), inner.clone())
                .prop_map(|(a, b)| Value::Remainder(Arc::new(a), Arc::new(b))),
            (inner.clone(), inner.clone()).prop_map(|(a, b)| Value::Less(Arc::new(a), Arc::new(b))),
            (inner.clone(), inner.clone())
                .prop_map(|(a, b)| Value::Greater(Arc::new(a), Arc::new(b))),
            inner.prop_map(|body| Value::Frame(Arc::new(body), Arc::new(Tag::TagLeaf))),
        ]
    })
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(64))]

    #[test]
    fn compound_closers_preserve_recursive_operator_trees(body in frame_bodies()) {
        let expected = Value::Frame(Arc::new(body), Arc::new(Tag::TagLeaf));
        let source = expected.to_string();
        let (readings, _) = Value::__all_with_weights_monolithic(&source)
            .map_err(|error| TestCaseError::fail(format!("main {source:?}: {error:?}")))?;
        prop_assert!(readings.contains(&expected));
        let actual = Value::parse(&source)
            .map_err(|error| TestCaseError::fail(format!("facade {source:?}: {error:?}")))?;
        prop_assert_eq!(&actual, &expected);
        let tagged = Tag::Hash(Arc::new(expected));
        let source = tagged.to_string();
        let (readings, _) = Tag::__all_with_weights_monolithic(&source)
            .map_err(|error| TestCaseError::fail(format!("tag main {source:?}: {error:?}")))?;
        prop_assert!(readings.contains(&tagged));
        let actual = Tag::parse(&source)
            .map_err(|error| TestCaseError::fail(format!("tag facade {source:?}: {error:?}")))?;
        prop_assert_eq!(actual, tagged);
    }
}

#[test]
fn returning_preserves_required_literal_validation() {
    for source in [
        "<%empty == empty>[tag]",
        "<%empty == empty%[tag]",
        "<%empty == empty%>[tag",
        "empty%>[tag]",
    ] {
        assert!(Value::parse(source).is_err(), "malformed frame accepted: {source:?}");
        assert!(
            Value::__all_with_weights_monolithic(source).is_err(),
            "main accepted malformed frame: {source:?}"
        );
    }
}
