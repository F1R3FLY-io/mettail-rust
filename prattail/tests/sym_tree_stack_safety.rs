use mettail_prattail::sym_tree::{SymTerm, TreeAlgebra, TreePred};
use mettail_prattail::symbolic::{BooleanAlgebra, IntervalAlgebra, IntervalPred};
use std::collections::hash_map::DefaultHasher;
use std::collections::{HashMap, HashSet};
use std::hash::{Hash, Hasher};

const DEPTH: usize = 20_000;
const SMALL_STACK_BYTES: usize = 256 * 1024;

fn on_small_stack(test: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .name("symbolic-tree-small-stack".to_string())
        .stack_size(SMALL_STACK_BYTES)
        .spawn(test)
        .expect("spawn symbolic tree small-stack gate")
        .join()
        .expect("symbolic tree small-stack gate panicked");
}

fn hash(value: &impl Hash) -> u64 {
    let mut hasher = DefaultHasher::new();
    value.hash(&mut hasher);
    hasher.finish()
}

fn tree_algebra() -> TreeAlgebra<IntervalAlgebra> {
    TreeAlgebra::new(
        IntervalAlgebra::new(0, 100),
        HashMap::from([("Leaf".to_string(), 0), ("Next".to_string(), 1)]),
        HashSet::from(["Leaf".to_string()]),
    )
}

fn deep_term(payload: i64) -> SymTerm<i64> {
    let mut term = SymTerm::leaf("Leaf", payload);
    for _ in 0..DEPTH {
        term = SymTerm::node("Next", vec![term]);
    }
    term
}

fn deep_predicate() -> TreePred<IntervalPred> {
    let mut predicate = TreePred::Node {
        constructor: "Leaf".to_string(),
        payload_guard: Some(IntervalPred::Range(10, 20)),
        children: Vec::new(),
    };
    for _ in 0..DEPTH {
        predicate = TreePred::Node {
            constructor: "Next".to_string(),
            payload_guard: None,
            children: vec![predicate],
        };
    }
    predicate
}

#[test]
fn symbolic_term_and_tree_predicate_pipeline_are_stack_safe_at_depth_20k() {
    on_small_stack(|| {
        let term = deep_term(15);
        let term_clone = term.clone();
        assert_eq!(term, term_clone);
        assert_eq!(hash(&term), hash(&term_clone));
        let term_debug = format!("{term:?}");
        assert!(term_debug.starts_with("SymTerm { constructor: \"Next\""));
        assert!(term_debug.contains("payload: Some(15)"));
        assert!(term_debug.ends_with("] }"));

        let predicate = deep_predicate();
        let predicate_clone = predicate.clone();
        assert_eq!(predicate, predicate_clone);
        assert_eq!(hash(&predicate), hash(&predicate_clone));
        let predicate_debug = format!("{predicate:?}");
        assert!(predicate_debug.starts_with("Node { constructor: \"Next\""));
        assert!(predicate_debug.contains("payload_guard: Some(Range(10, 20))"));
        assert!(predicate_debug.ends_with("] }"));

        let algebra = tree_algebra();
        assert!(algebra.evaluate(&predicate, &term));
        assert!(!algebra.evaluate(&predicate, &deep_term(25)));
        assert!(algebra.is_satisfiable(&predicate));
        let witness = algebra
            .witness(&predicate)
            .expect("deep symbolic tree predicate has a witness");
        assert!(algebra.evaluate(&predicate, &witness));

        drop(witness);
        drop(predicate_clone);
        drop(predicate);
        drop(term_clone);
        drop(term);
    });
}

#[test]
fn symbolic_tree_debug_preserves_compact_derived_contracts() {
    let term = SymTerm::node("Pair", vec![SymTerm::leaf("Leaf", 7), SymTerm::constant("Nil")]);
    assert_eq!(
        format!("{term:?}"),
        "SymTerm { constructor: \"Pair\", payload: None, children: [SymTerm { constructor: \"Leaf\", payload: Some(7), children: [] }, SymTerm { constructor: \"Nil\", payload: None, children: [] }] }"
    );

    let predicate = TreePred::Not(Box::new(TreePred::Node {
        constructor: "Pair".to_string(),
        payload_guard: None::<IntervalPred>,
        children: vec![TreePred::Wild, TreePred::False],
    }));
    assert_eq!(
        format!("{predicate:?}"),
        "Not(Node { constructor: \"Pair\", payload_guard: None, children: [Wild, False] })"
    );
}
