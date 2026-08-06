use mettail_prattail::grammar::ir::CollectionKind;
use mettail_prattail::structural_types::collect_structural_child_categories;
use mettail_prattail::vpa::build_alphabet_from_syntax;
use mettail_prattail::SyntaxItemSpec;

const DEPTH: usize = 20_000;
const STACK_BYTES: usize = 256 * 1024;

#[derive(Clone, Debug)]
#[allow(dead_code)]
enum RecursiveOracle {
    Terminal(String),
    Map {
        body_items: Vec<RecursiveOracle>,
    },
    Sep {
        body: Box<RecursiveOracle>,
        separator: String,
        kind: CollectionKind,
    },
    Zip {
        left_name: String,
        right_name: String,
        left_category: String,
        right_category: String,
        body: Box<RecursiveOracle>,
    },
    Optional {
        inner: Vec<RecursiveOracle>,
    },
}

fn nested_optional(depth: usize) -> SyntaxItemSpec {
    let mut item = SyntaxItemSpec::Terminal("leaf".into());
    for _ in 0..depth {
        item = SyntaxItemSpec::Optional { inner: vec![item] };
    }
    item
}

fn optional_depth(item: &SyntaxItemSpec) -> usize {
    let mut depth = 0;
    let mut current = item;
    loop {
        match current {
            SyntaxItemSpec::Optional { inner } if inner.len() == 1 => {
                depth += 1;
                current = &inner[0];
            },
            SyntaxItemSpec::Terminal(text) if text == "leaf" => return depth,
            other => panic!("unexpected syntax-item chain node: {other:?}"),
        }
    }
}

#[test]
fn syntax_item_lifecycle_and_rd_lowering_match_recursive_oracles() {
    let actual = SyntaxItemSpec::Optional {
        inner: vec![SyntaxItemSpec::Map {
            body_items: vec![
                SyntaxItemSpec::Sep {
                    body: Box::new(SyntaxItemSpec::Terminal("x".into())),
                    separator: ",".into(),
                    kind: CollectionKind::Vec,
                },
                SyntaxItemSpec::Zip {
                    left_name: "left".into(),
                    right_name: "right".into(),
                    left_category: "Name".into(),
                    right_category: "Proc".into(),
                    body: Box::new(SyntaxItemSpec::Terminal("z".into())),
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
                    body: Box::new(RecursiveOracle::Terminal("z".into())),
                },
            ],
        }],
    };

    assert_eq!(format!("{actual:?}"), format!("{oracle:?}"));
    assert_eq!(format!("{:?}", actual.clone()), format!("{oracle:?}"));
    assert_eq!(
        format!("{:?}", actual.to_recursive_descent_item()),
        "Optional { inner: [Map { body_items: [Sep { body: Terminal(\"x\"), separator: \",\", kind: Vec }, Zip { left_name: \"left\", right_name: \"right\", left_category: \"Name\", right_category: \"Proc\", body: Terminal(\"z\") }] }] }"
    );
}

#[test]
fn syntax_item_traversals_are_stack_safe_at_depth_20k() {
    std::thread::Builder::new()
        .stack_size(STACK_BYTES)
        .spawn(|| {
            let item = nested_optional(DEPTH);
            let cloned = item.clone();
            assert_eq!(optional_depth(&cloned), DEPTH);
            assert!(format!("{item:?}").starts_with("Optional { inner: [Optional { inner: ["));

            let lowered = item.to_recursive_descent_item();
            assert!(format!("{lowered:?}").starts_with("Optional { inner: [Optional { inner: ["));

            let mut categories = Vec::new();
            collect_structural_child_categories(std::slice::from_ref(&cloned), &mut categories);
            assert!(categories.is_empty());

            let grammar = vec![("Deep".into(), "Proc".into(), vec![cloned])];
            let alphabet = build_alphabet_from_syntax(&grammar);
            assert!(alphabet.internal_symbols.contains("leaf"));

            drop(alphabet);
            drop(grammar);
            drop(lowered);
            drop(item);
        })
        .expect("spawn syntax-item depth-gate thread")
        .join()
        .expect("syntax-item stack-safety gate");
}
