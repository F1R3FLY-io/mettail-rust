use mettail_ast::language::TreeConstraintExpr;

#[allow(dead_code)]
#[derive(Debug)]
enum TreeConstraintOracle<'tree> {
    ForallChildren {
        symbol: &'tree String,
        body: Box<TreeConstraintOracle<'tree>>,
    },
    ExistsChild,
    Not(Box<TreeConstraintOracle<'tree>>),
    Match(&'tree [String]),
    Atom(&'tree String),
    And(Box<TreeConstraintOracle<'tree>>, Box<TreeConstraintOracle<'tree>>),
    Or(Box<TreeConstraintOracle<'tree>>, Box<TreeConstraintOracle<'tree>>),
}

fn recursive_debug_oracle(expression: &TreeConstraintExpr) -> TreeConstraintOracle<'_> {
    match expression {
        TreeConstraintExpr::ForallChildren { symbol, body } => {
            TreeConstraintOracle::ForallChildren {
                symbol,
                body: Box::new(recursive_debug_oracle(body)),
            }
        },
        TreeConstraintExpr::ExistsChild => TreeConstraintOracle::ExistsChild,
        TreeConstraintExpr::Not(inner) => {
            TreeConstraintOracle::Not(Box::new(recursive_debug_oracle(inner)))
        },
        TreeConstraintExpr::Match(symbols) => TreeConstraintOracle::Match(symbols),
        TreeConstraintExpr::Atom(symbol) => TreeConstraintOracle::Atom(symbol),
        TreeConstraintExpr::And(left, right) => TreeConstraintOracle::And(
            Box::new(recursive_debug_oracle(left)),
            Box::new(recursive_debug_oracle(right)),
        ),
        TreeConstraintExpr::Or(left, right) => TreeConstraintOracle::Or(
            Box::new(recursive_debug_oracle(left)),
            Box::new(recursive_debug_oracle(right)),
        ),
    }
}

fn rich_expression() -> TreeConstraintExpr {
    TreeConstraintExpr::And(
        Box::new(TreeConstraintExpr::ForallChildren {
            symbol: "Branch\nNode".to_owned(),
            body: Box::new(TreeConstraintExpr::Not(Box::new(TreeConstraintExpr::Atom(
                "Nested\"Leaf".to_owned(),
            )))),
        }),
        Box::new(TreeConstraintExpr::Or(
            Box::new(TreeConstraintExpr::ExistsChild),
            Box::new(TreeConstraintExpr::Match(vec!["Leaf".to_owned(), "Nil".to_owned()])),
        )),
    )
}

#[test]
fn tree_constraint_debug_matches_derived_debug() {
    let expression = rich_expression();
    assert_eq!(format!("{expression:?}"), format!("{:?}", recursive_debug_oracle(&expression)),);
    assert_eq!(
        format!("{expression:#?}"),
        format!("{:#?}", recursive_debug_oracle(&expression)),
    );
}

#[test]
fn tree_constraint_lifecycle_handles_depth_20k_on_a_256k_stack() {
    const DEPTH: usize = 20_000;
    std::thread::Builder::new()
        .name("tree-constraint-lifecycle-small-stack".into())
        .stack_size(256 * 1024)
        .spawn(|| {
            let mut expression = TreeConstraintExpr::Atom("Leaf".to_owned());
            for depth in 0..DEPTH {
                expression = if depth % 2 == 0 {
                    TreeConstraintExpr::Not(Box::new(expression))
                } else {
                    TreeConstraintExpr::ForallChildren {
                        symbol: "Branch".to_owned(),
                        body: Box::new(expression),
                    }
                };
            }
            let cloned = expression.clone();
            let rendered = format!("{expression:?}");
            assert!(rendered.starts_with("ForallChildren { symbol: \"Branch\", body: Not("));
            assert!(rendered.contains("Atom(\"Leaf\")"));
            drop(cloned);
            drop(expression);
        })
        .expect("small-stack tree-constraint lifecycle thread must spawn")
        .join()
        .expect("tree-constraint lifecycle PDAs must not overflow the native stack");
}
