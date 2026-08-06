use std::collections::hash_map::DefaultHasher;
use std::collections::HashMap;
use std::hash::{Hash, Hasher};

use mettail_prattail::unification::{TermExpr, TermSignature};

const DEPTH: usize = 20_000;
const STACK_BYTES: usize = 256 * 1024;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum RecursiveOracle {
    Var(usize),
    Const(String),
    App { head: String, args: Vec<RecursiveOracle> },
}

fn nested(depth: usize) -> TermExpr {
    let mut term = TermExpr::Var(0);
    for _ in 0..depth {
        term = TermExpr::App { head: "f".into(), args: vec![term] };
    }
    term
}

#[test]
fn term_lifecycle_matches_the_recursive_derive_and_display_oracles() {
    let actual = TermExpr::App {
        head: "pair".into(),
        args: vec![TermExpr::Var(3), TermExpr::Const("a".into())],
    };
    let oracle = RecursiveOracle::App {
        head: "pair".into(),
        args: vec![RecursiveOracle::Var(3), RecursiveOracle::Const("a".into())],
    };

    assert_eq!(format!("{actual:?}"), format!("{oracle:?}"));
    assert_eq!(actual.to_string(), "pair(x3, a)");

    let mut actual_hash = DefaultHasher::new();
    actual.hash(&mut actual_hash);
    let mut oracle_hash = DefaultHasher::new();
    oracle.hash(&mut oracle_hash);
    assert_eq!(actual_hash.finish(), oracle_hash.finish());
    assert_eq!(actual, actual.clone());
}

#[test]
fn term_lifecycle_substitution_and_signature_are_stack_safe_at_depth_20k() {
    std::thread::Builder::new()
        .stack_size(STACK_BYTES)
        .spawn(|| {
            let term = nested(DEPTH);
            let cloned = term.clone();
            assert_eq!(term, cloned);

            let mut left_hash = DefaultHasher::new();
            term.hash(&mut left_hash);
            let mut right_hash = DefaultHasher::new();
            cloned.hash(&mut right_hash);
            assert_eq!(left_hash.finish(), right_hash.finish());
            assert!(format!("{term:?}").starts_with("App { head: \"f\", args: ["));
            assert!(term.to_string().starts_with("f(f(f("));

            let mut substitution = HashMap::new();
            substitution.insert(0, TermExpr::Var(1));
            substitution.insert(1, TermExpr::Const("resolved".into()));
            let applied = term.apply_substitution(&substitution);
            assert!(applied.to_string().contains("resolved"));

            let mut signature = TermSignature::new();
            signature.add_constructor("f", 1);
            assert!(signature.is_well_formed(&term));

            drop(applied);
            drop(cloned);
            drop(term);
        })
        .expect("spawn depth-gate thread")
        .join()
        .expect("unification term stack-safety gate");
}
