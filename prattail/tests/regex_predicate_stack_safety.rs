use mettail_prattail::regex_sfa::{compile, RegexPred};
use mettail_prattail::symbolic::{IntervalAlgebra, IntervalPred};
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

const DEPTH: usize = 20_000;
const SMALL_STACK_BYTES: usize = 256 * 1024;

fn on_small_stack(test: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .name("regex-predicate-small-stack".to_string())
        .stack_size(SMALL_STACK_BYTES)
        .spawn(test)
        .expect("spawn regex predicate small-stack gate")
        .join()
        .expect("regex predicate small-stack gate panicked");
}

fn hash(value: &impl Hash) -> u64 {
    let mut hasher = DefaultHasher::new();
    value.hash(&mut hasher);
    hasher.finish()
}

fn element() -> RegexPred<IntervalPred> {
    RegexPred::Elem(IntervalPred::Range(0, 10))
}

fn deep_right_skewed_concatenation() -> RegexPred<IntervalPred> {
    let mut predicate = element();
    for _ in 0..DEPTH {
        predicate = RegexPred::Concat(Box::new(element()), Box::new(predicate));
    }
    predicate
}

fn deep_complement() -> RegexPred<IntervalPred> {
    let mut predicate = element();
    for _ in 0..DEPTH {
        predicate = RegexPred::Compl(Box::new(predicate));
    }
    predicate
}

#[test]
fn regex_lifecycle_and_compilation_are_stack_safe_at_depth_20k() {
    on_small_stack(|| {
        let predicate = deep_right_skewed_concatenation();
        let cloned = predicate.clone();
        assert_eq!(predicate, cloned);
        assert_eq!(hash(&predicate), hash(&cloned));

        let debug = format!("{predicate:?}");
        assert!(debug.starts_with("Concat(Elem(Range(0, 10)), Concat("));
        assert!(debug.ends_with(&")".repeat(DEPTH)));

        let algebra = IntervalAlgebra::new(0, 100);
        let automaton = compile(&algebra, &predicate);
        assert_eq!(automaton.states.len(), 2 * (DEPTH + 1));
        assert!(!automaton.is_empty());
        assert!(automaton.accepts(&vec![5; DEPTH + 1]));
        assert!(!automaton.accepts(&vec![5; DEPTH]));

        drop(cloned);
        drop(predicate);
    });
}

#[test]
fn regex_unary_lifecycle_is_stack_safe_at_depth_20k() {
    on_small_stack(|| {
        let predicate = deep_complement();
        let cloned = predicate.clone();
        assert_eq!(predicate, cloned);
        assert_eq!(hash(&predicate), hash(&cloned));

        let debug = format!("{predicate:?}");
        assert!(debug.starts_with("Compl(Compl("));
        assert!(debug.ends_with(&")".repeat(DEPTH)));

        drop(cloned);
        drop(predicate);
    });
}

#[test]
fn regex_debug_preserves_the_compact_derived_contract() {
    let predicate = RegexPred::Inter(
        Box::new(RegexPred::Alt(
            Box::new(RegexPred::<IntervalPred>::Epsilon),
            Box::new(RegexPred::Star(Box::new(element()))),
        )),
        Box::new(RegexPred::Compl(Box::new(RegexPred::Length(2, Some(4))))),
    );
    assert_eq!(
        format!("{predicate:?}"),
        "Inter(Alt(Epsilon, Star(Elem(Range(0, 10)))), Compl(Length(2, Some(4))))"
    );
}
