use std::collections::HashMap;

use mettail_prattail::morphism::{translate_term, TheoryMorphism};
use mettail_prattail::structural_types::{parse_structural_predicate, RankedAlphabet};
use mettail_prattail::sym_tree::TreePred;

const DEPTH: usize = 20_000;
const SMALL_STACK_BYTES: usize = 256 * 1024;

fn deeply_nested_term(head: &str, leaf: &str) -> String {
    let mut term = String::with_capacity(head.len() * DEPTH + leaf.len() + DEPTH * 2);
    for _ in 0..DEPTH {
        term.push_str(head);
        term.push('(');
    }
    term.push_str(leaf);
    for _ in 0..DEPTH {
        term.push(')');
    }
    term
}

#[test]
fn morphism_translation_is_linear_and_stack_safe_at_depth_twenty_thousand() {
    std::thread::Builder::new()
        .name("morphism-term-stack-gate".into())
        .stack_size(SMALL_STACK_BYTES)
        .spawn(|| {
            let mut morphism = TheoryMorphism::new("deep", "source", "target");
            morphism.map_operation("Next", "N");
            morphism.map_operation("Leaf", "L");

            let source = deeply_nested_term("Next", "Leaf");
            let expected = deeply_nested_term("N", "L");
            assert_eq!(translate_term(&morphism, &source), Ok(expected));
        })
        .expect("spawn morphism term stack gate")
        .join()
        .expect("morphism term translation overflowed or panicked");
}

#[test]
fn structural_pattern_parser_is_stack_safe_at_depth_twenty_thousand() {
    std::thread::Builder::new()
        .name("structural-pattern-stack-gate".into())
        .stack_size(SMALL_STACK_BYTES)
        .spawn(|| {
            let alphabet = RankedAlphabet {
                arities: HashMap::from([("Next".into(), 1), ("Leaf".into(), 0)]),
                ..Default::default()
            };
            let predicate = format!("x == {}", deeply_nested_term("Next", "Leaf"));
            let (pattern, is_equality) = parse_structural_predicate(&predicate, &alphabet)
                .expect("deep structural pattern must parse");
            assert!(is_equality);

            let mut depth = 0;
            let mut current = &pattern;
            loop {
                match current {
                    TreePred::Node { constructor, children, .. }
                        if constructor == "Next" && children.len() == 1 =>
                    {
                        depth += 1;
                        current = &children[0];
                    },
                    TreePred::Node { constructor, children, .. }
                        if constructor == "Leaf" && children.is_empty() =>
                    {
                        break;
                    },
                    other => panic!("unexpected deep structural pattern node: {other:?}"),
                }
            }
            assert_eq!(depth, DEPTH);
        })
        .expect("spawn structural pattern stack gate")
        .join()
        .expect("structural pattern parsing overflowed or panicked");
}

#[test]
fn malformed_parentheses_are_rejected_consistently() {
    let morphism = TheoryMorphism::new("strict", "source", "target");
    assert!(translate_term(&morphism, "F(x))").is_err());
    assert!(translate_term(&morphism, "F((x)").is_err());

    let alphabet = RankedAlphabet {
        arities: HashMap::from([("F".into(), 1)]),
        ..Default::default()
    };
    assert!(parse_structural_predicate("v == F(x))", &alphabet).is_none());
    assert!(parse_structural_predicate("v == F((x)", &alphabet).is_none());
}
