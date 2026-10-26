use proptest::prelude::*;
use std::sync::Arc;

mettail_macros::language! {
    name: PrefixReadback,
    options { emit_tests: false, emit_simulator: false, emit_blockly: false },
    types { noadmit Value noadmit Envelope },
    terms {
        Zero . |- "z" : Value;
        One . |- "o" : Value;
        Add . left:Value, right:Value |- left "+" right : Value;
        Mul . left:Value, right:Value |- left "*" right : Value;
        Explicit . body:Value |- "#" body : Envelope prefix(220);
        Inferred . body:Value |- "tag" body : Envelope;
    },
    equations {},
    rewrites {},
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(64))]

    #[test]
    fn foreign_prefix_roundtrips_infix_operands(
        choices in proptest::collection::vec((any::<bool>(), any::<bool>()), 1..10),
    ) {
        let mut value = Value::Zero;
        for (multiply, one) in choices {
            let right = if one { Value::One } else { Value::Zero };
            value = if multiply {
                Value::Mul(Arc::new(value), Arc::new(right))
            } else {
                Value::Add(Arc::new(value), Arc::new(right))
            };
        }
        for expected in [Envelope::Explicit(Arc::new(value.clone())), Envelope::Inferred(Arc::new(value))] {
            let source = expected.to_string();
            let parsed = Envelope::parse(&source).unwrap_or_else(|error| {
                panic!("foreign prefix surface {source:?} failed: {error:?}")
            });
            prop_assert_eq!(parsed, expected);
        }
    }
}
