use proptest::prelude::*;
use std::sync::Arc;

mettail_macros::language! {
    name: AdjacentFrames,
    options { emit_tests: false, emit_simulator: false, emit_blockly: false },
    types { noadmit Item ![String] as TextValue },
    terms {
        Empty . |- "{" "}" : Item;
        Atom . |- "a" : Item;
        Text . |- raw@StringLiteral : Item;
        Word . |- raw@Ident : Item;
        Wrap . body:Item |- "(" "wrap" body ")" : Item;
        Pair . left:Item, right:Item |- "(" "pair" left right ")" : Item;
        Triple . first:Item, second:Item, third:Item
            |- "(" "triple" first second third ")" : Item;
        Delimited . left:Item, right:Item
            |- "(" "separated" left "," right ")" : Item;
        ManyThen . items:Vec(Item), last:Item
            |- "(" "many" items.*sep(",") last ")" : Item;
    },
    equations {},
    rewrites {},
}

fn item_strategy() -> impl Strategy<Value = Item> {
    prop_oneof![
        Just(Item::Empty),
        Just(Item::Atom),
        Just(Item::Text(r#""punctuation , () [] {} λ""#.into())),
        Just(Item::Word("letters".into())),
    ]
    .prop_recursive(3, 20, 3, |inner| {
        prop_oneof![
            inner.clone().prop_map(|body| Item::Wrap(Arc::new(body))),
            (inner.clone(), inner.clone())
                .prop_map(|(left, right)| { Item::Pair(Arc::new(left), Arc::new(right)) }),
            (inner.clone(), inner.clone(), inner.clone()).prop_map(|(first, second, third)| {
                Item::Triple(Arc::new(first), Arc::new(second), Arc::new(third))
            }),
            (inner.clone(), inner)
                .prop_map(|(left, right)| { Item::Delimited(Arc::new(left), Arc::new(right)) }),
        ]
    })
}

#[test]
fn adjacent_operands_are_accepted_by_the_existing_main_parser() {
    for source in ["(pair {} {})", "(triple {} a {})", "(separated {}, {})"] {
        let (terms, _) = Item::__all_with_weights_monolithic(source)
            .unwrap_or_else(|error| panic!("main parser rejected {source:?}: {error}"));
        assert!(!terms.is_empty(), "{source:?}: {terms:?}");
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(64))]

    #[test]
    fn adjacent_lists_preserve_empty_and_nonempty_operands(
        items in proptest::collection::vec(item_strategy(), 0..4),
        last in item_strategy(),
    ) {
        for expected in [
            Item::ManyThen(Vec::new(), Arc::new(last.clone())),
            Item::ManyThen(items, Arc::new(last)),
        ] {
            let source = expected.to_string();
            let actual = Item::parse(&source).expect("adjacent list and scalar operands");
            prop_assert_eq!(actual, expected);
        }
    }

    #[test]
    fn adjacent_boundaries_never_split_one_token(
        identifier in "z{2,24}",
        payload in "[a-zA-Z ,(){}\\[\\]]{0,24}",
    ) {
        let quoted = format!("{payload} λ");
        for source in [format!("(pair {identifier})"), format!("(pair {quoted:?})")] {
            prop_assert!(Item::parse(&source).is_err(), "split a token: {:?}", source);
            prop_assert!(Item::__all_with_weights_monolithic(&source).is_err());
        }
    }

    #[test]
    fn adjacent_operands_preserve_the_complete_tree(expected in item_strategy()) {
        let source = expected.to_string();
        let parsed = Item::parse(&source).unwrap_or_else(|error| {
            panic!("frame {source:?} failed: {error}")
        });
        prop_assert_eq!(parsed, expected);
    }
}

#[test]
fn adjacent_boundaries_preserve_empty_lists_and_token_spans() {
    let empty_list = Item::ManyThen(Vec::new(), Arc::new(Item::Empty));
    let one_item = Item::ManyThen(vec![Item::Atom], Arc::new(Item::Empty));
    for expected in [empty_list, one_item] {
        let source = expected.to_string();
        assert_eq!(Item::parse(&source).expect("list operand boundary"), expected);
    }
    assert_eq!(
        Item::parse("(pair {}{})").expect("adjacent bracketed operands"),
        Item::Pair(Arc::new(Item::Empty), Arc::new(Item::Empty)),
    );
    for source in ["(pair zz)", "(pair \"two words\")", "(pair {} )"] {
        assert!(Item::parse(source).is_err(), "split a single operand: {source:?}");
        assert!(Item::__all_with_weights_monolithic(source).is_err(), "main parser: {source:?}");
    }
}
