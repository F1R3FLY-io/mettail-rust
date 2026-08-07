use std::collections::{HashMap, HashSet};

use mettail_prattail::decision_tree::{DecisionTreeBuilder, PatternElement};
use mettail_prattail::grammar::ir::{CollectionKind, RDRuleInfo, RDSyntaxItem};
use mettail_prattail::prediction::first_of_rd_suffix;
use mettail_prattail::token_id::TokenIdMap;

const DEPTH: usize = 20_000;
const STACK_BYTES: usize = 256 * 1024;

#[derive(Clone, Debug)]
#[allow(dead_code)]
enum RecursiveOracle {
    Terminal(String),
    NonTerminal {
        category: String,
        param_name: String,
    },
    IdentCapture {
        param_name: String,
    },
    TokenKindCapture {
        param_name: String,
        kind_name: String,
    },
    Binder {
        param_name: String,
        binder_category: String,
    },
    Collection {
        param_name: String,
        element_category: String,
        separator: String,
        kind: CollectionKind,
        key_val_separator: Option<String>,
    },
    SepList {
        collection_name: String,
        element_category: String,
        separator: String,
        kind: CollectionKind,
    },
    Sep {
        body: Box<RecursiveOracle>,
        separator: String,
        kind: CollectionKind,
    },
    Map {
        body_items: Vec<RecursiveOracle>,
    },
    Zip {
        left_name: String,
        right_name: String,
        left_category: String,
        right_category: String,
        body: Box<RecursiveOracle>,
    },
    BinderCollection {
        param_name: String,
        separator: String,
    },
    Optional {
        inner: Vec<RecursiveOracle>,
    },
    GuardExpression {
        param_name: String,
    },
}

fn nested_optional(depth: usize) -> RDSyntaxItem {
    let mut item = RDSyntaxItem::Terminal("leaf".into());
    for _ in 0..depth {
        item = RDSyntaxItem::Optional { inner: vec![item] };
    }
    item
}

fn optional_depth(item: &RDSyntaxItem) -> usize {
    let mut depth = 0;
    let mut current = item;
    loop {
        match current {
            RDSyntaxItem::Optional { inner } if inner.len() == 1 => {
                depth += 1;
                current = &inner[0];
            },
            RDSyntaxItem::Terminal(text) if text == "leaf" => return depth,
            other => panic!("unexpected RD syntax-item chain node: {other:?}"),
        }
    }
}

#[test]
fn rd_syntax_item_lifecycle_matches_the_recursive_derive_oracle() {
    let actual = RDSyntaxItem::Optional {
        inner: vec![RDSyntaxItem::Map {
            body_items: vec![
                RDSyntaxItem::Sep {
                    body: Box::new(RDSyntaxItem::Terminal("x".into())),
                    separator: ",".into(),
                    kind: CollectionKind::Vec,
                },
                RDSyntaxItem::Zip {
                    left_name: "left".into(),
                    right_name: "right".into(),
                    left_category: "Name".into(),
                    right_category: "Proc".into(),
                    body: Box::new(RDSyntaxItem::GuardExpression { param_name: "g".into() }),
                },
            ],
        }],
    };
    let oracle = RecursiveOracle::Optional {
        inner: vec![RecursiveOracle::Map {
            body_items: vec![
                RecursiveOracle::Sep {
                    body: Box::new(RecursiveOracle::Terminal("x".into())),
                    separator: ",".into(),
                    kind: CollectionKind::Vec,
                },
                RecursiveOracle::Zip {
                    left_name: "left".into(),
                    right_name: "right".into(),
                    left_category: "Name".into(),
                    right_category: "Proc".into(),
                    body: Box::new(RecursiveOracle::GuardExpression { param_name: "g".into() }),
                },
            ],
        }],
    };

    assert_eq!(format!("{actual:?}"), format!("{oracle:?}"));
    assert_eq!(format!("{:?}", actual.clone()), format!("{oracle:?}"));
}

#[test]
fn rd_syntax_item_and_rule_lifecycle_are_stack_safe_at_depth_20k() {
    std::thread::Builder::new()
        .stack_size(STACK_BYTES)
        .spawn(|| {
            let item = nested_optional(DEPTH);
            let cloned = item.clone();
            assert_eq!(optional_depth(&item), DEPTH);
            assert_eq!(optional_depth(&cloned), DEPTH);
            assert!(format!("{item:?}").starts_with("Optional { inner: [Optional { inner: ["));

            let rule = RDRuleInfo {
                label: "Deep".into(),
                category: "Proc".into(),
                items: vec![cloned],
                has_binder: false,
                has_multi_binder: false,
                is_collection: false,
                collection_type: None,
                separator: None,
                prefix_bp: None,
                eval_mode: None,
            };
            let cloned_rule = rule.clone();
            assert!(format!("{cloned_rule:?}").contains("label: \"Deep\""));

            drop(cloned_rule);
            drop(rule);
            drop(item);
        })
        .expect("spawn depth-gate thread")
        .join()
        .expect("RD syntax-item stack-safety gate");
}

#[test]
fn rd_pattern_and_first_set_walkers_are_stack_safe_at_depth_20k() {
    std::thread::Builder::new()
        .stack_size(STACK_BYTES)
        .spawn(|| {
            let mut token_ids = TokenIdMap::new();
            token_ids.get_or_insert("KwLeaf");
            let builder =
                DecisionTreeBuilder::new(token_ids, HashMap::new(), Vec::new(), HashSet::new());
            let rule = RDRuleInfo {
                label: "DeepDispatch".into(),
                category: "Proc".into(),
                items: vec![nested_optional(DEPTH)],
                has_binder: false,
                has_multi_binder: false,
                is_collection: false,
                collection_type: None,
                separator: None,
                prefix_bp: None,
                eval_mode: None,
            };

            let pattern = builder.pattern_from_rd_rule(&rule);
            assert_eq!(pattern.len(), DEPTH * 2 + 1);
            assert_eq!(
                pattern
                    .iter()
                    .filter(|element| matches!(element, PatternElement::OptionalStart))
                    .count(),
                DEPTH
            );
            assert_eq!(
                pattern
                    .iter()
                    .filter(|element| matches!(element, PatternElement::OptionalEnd))
                    .count(),
                DEPTH
            );

            let (first, nullable) = first_of_rd_suffix(&rule.items, &HashMap::new());
            assert!(first.contains("KwLeaf"));
            assert!(nullable);
        })
        .expect("spawn RD walker depth-gate thread")
        .join()
        .expect("RD walker stack-safety gate");
}
