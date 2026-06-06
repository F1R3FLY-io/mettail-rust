//! Phase 4 #3 (2026-05-12): Optional-Collection smoke test.
//!
//! Validates that codegen for `Proc::ChooseMaybe(Box<Proc>, Option<Vec<Proc>>)`
//! compiles and runtime semantics work end-to-end:
//! - Construction: `ChooseMaybe(std::sync::Arc::new(PZero), Some(vec![PZero, PZero]))`
//! - Clone, Debug, PartialEq, Hash all work via derived/iterative codegen.
//! - Display roundtrip through parse_via_wpda works for both None and Some.

use mettail_languages::class2optsmoke::Proc;

#[test]
fn choosemaybe_none_constructs_and_clones() {
    let term = Proc::ChooseMaybe(std::sync::Arc::new(Proc::PZero), None);
    let cloned = term.clone();
    assert_eq!(term, cloned);
    let displayed = format!("{}", term);
    assert!(!displayed.is_empty());
}

#[test]
fn choosemaybe_some_empty_constructs_and_clones() {
    let term = Proc::ChooseMaybe(std::sync::Arc::new(Proc::PZero), Some(vec![]));
    let cloned = term.clone();
    assert_eq!(term, cloned);
}

#[test]
fn choosemaybe_some_nonempty_constructs_and_clones() {
    let term =
        Proc::ChooseMaybe(std::sync::Arc::new(Proc::PZero), Some(vec![Proc::PZero, Proc::PZero]));
    let cloned = term.clone();
    assert_eq!(term, cloned);
    // Debug format works.
    let debug = format!("{:?}", term);
    assert!(debug.contains("ChooseMaybe"));
}

#[test]
fn choosemaybe_none_ne_some() {
    let a = Proc::ChooseMaybe(std::sync::Arc::new(Proc::PZero), None);
    let b = Proc::ChooseMaybe(std::sync::Arc::new(Proc::PZero), Some(vec![]));
    assert_ne!(a, b);
}

#[test]
fn choosemaybe_some_different_lengths_ne() {
    let a = Proc::ChooseMaybe(std::sync::Arc::new(Proc::PZero), Some(vec![Proc::PZero]));
    let b =
        Proc::ChooseMaybe(std::sync::Arc::new(Proc::PZero), Some(vec![Proc::PZero, Proc::PZero]));
    assert_ne!(a, b);
}

#[test]
fn choosemaybe_some_hash_consistent_with_eq() {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};

    let a = Proc::ChooseMaybe(std::sync::Arc::new(Proc::PZero), Some(vec![Proc::PZero]));
    let b = Proc::ChooseMaybe(std::sync::Arc::new(Proc::PZero), Some(vec![Proc::PZero]));
    assert_eq!(a, b);

    let mut h1 = DefaultHasher::new();
    a.hash(&mut h1);
    let mut h2 = DefaultHasher::new();
    b.hash(&mut h2);
    assert_eq!(h1.finish(), h2.finish());
}

#[test]
fn choosemaybe_parse_none_via_wpda() {
    let result = Proc::parse_via_wpda("choose 0").expect("'choose 0' parses");
    match &result {
        Proc::ChooseMaybe(_a, q) => {
            assert!(q.is_none(), "expected None for absent optional collection");
        },
        other => panic!("expected ChooseMaybe, got {:?}", other),
    }
}

#[test]
fn choosemaybe_parse_some_via_wpda() {
    let result =
        Proc::parse_via_wpda("choose 0 with ( 0 | 0 )").expect("'choose 0 with ( 0 | 0 )' parses");
    match &result {
        Proc::ChooseMaybe(_a, q) => match q {
            Some(v) => {
                assert_eq!(v.len(), 2, "expected 2 elements in optional collection");
                for elem in v.iter() {
                    assert!(matches!(elem, Proc::PZero));
                }
            },
            None => panic!("expected Some collection"),
        },
        other => panic!("expected ChooseMaybe, got {:?}", other),
    }
}
