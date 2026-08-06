use mettail_prattail::string_algebra::{StrPred, StringAlgebra};
use mettail_prattail::symbolic::{BooleanAlgebra, CharClassPred};
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

const DEPTH: usize = 20_000;
const SMALL_STACK_BYTES: usize = 256 * 1024;

fn on_small_stack(test: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .name("string-predicate-small-stack".to_string())
        .stack_size(SMALL_STACK_BYTES)
        .spawn(test)
        .expect("spawn string predicate small-stack gate")
        .join()
        .expect("string predicate small-stack gate panicked");
}

fn hash(value: &impl Hash) -> u64 {
    let mut hasher = DefaultHasher::new();
    value.hash(&mut hasher);
    hasher.finish()
}

fn atom() -> StrPred {
    StrPred::Literal("x".to_string())
}

fn deep_right_skewed_concatenation() -> StrPred {
    let mut predicate = atom();
    for _ in 0..DEPTH {
        predicate = StrPred::Concat(Box::new(atom()), Box::new(predicate));
    }
    predicate
}

fn deep_complement() -> StrPred {
    let mut predicate = atom();
    for _ in 0..DEPTH {
        predicate = StrPred::Compl(Box::new(predicate));
    }
    predicate
}

#[test]
fn string_lifecycle_desugaring_and_decision_are_stack_safe_at_depth_20k() {
    on_small_stack(|| {
        let predicate = deep_right_skewed_concatenation();
        let cloned = predicate.clone();
        assert_eq!(predicate, cloned);
        assert_eq!(hash(&predicate), hash(&cloned));

        let debug = format!("{predicate:?}");
        assert!(debug.starts_with("Concat(Literal(\"x\"), Concat("));
        assert!(debug.ends_with(&")".repeat(DEPTH)));

        let algebra = StringAlgebra::new();
        assert!(algebra.evaluate(&predicate, &"x".repeat(DEPTH + 1)));
        assert!(!algebra.evaluate(&predicate, &"x".repeat(DEPTH)));
        let witness = algebra
            .witness(&predicate)
            .expect("deep string concatenation has a witness");
        assert_eq!(witness.len(), DEPTH + 1);

        drop(cloned);
        drop(predicate);
    });
}

#[test]
fn string_unary_lifecycle_is_stack_safe_at_depth_20k() {
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
fn string_debug_preserves_the_compact_derived_contract() {
    let predicate = StrPred::Inter(
        Box::new(StrPred::Alt(
            Box::new(StrPred::Epsilon),
            Box::new(StrPred::Star(Box::new(StrPred::Class(CharClassPred::Range('a', 'z'))))),
        )),
        Box::new(StrPred::Compl(Box::new(StrPred::Length(2, Some(4))))),
    );
    assert_eq!(
        format!("{predicate:?}"),
        "Inter(Alt(Epsilon, Star(Class(Range('a', 'z')))), Compl(Length(2, Some(4))))"
    );
}
