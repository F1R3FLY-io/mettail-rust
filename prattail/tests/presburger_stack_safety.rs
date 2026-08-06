use mettail_prattail::presburger::{
    evaluate_presburger_checked, is_satisfiable_nfa, IntAssignment, LinearConstraint,
    PresburgerNfa, PresburgerPred,
};
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

const DEPTH: usize = 20_000;
const SMALL_STACK_BYTES: usize = 256 * 1024;

fn on_small_stack(test: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .name("presburger-small-stack".to_string())
        .stack_size(SMALL_STACK_BYTES)
        .spawn(test)
        .expect("spawn Presburger small-stack gate")
        .join()
        .expect("Presburger small-stack gate panicked");
}

fn hash(value: &impl Hash) -> u64 {
    let mut hasher = DefaultHasher::new();
    value.hash(&mut hasher);
    hasher.finish()
}

#[test]
fn presburger_lifecycle_evaluation_nnf_and_compilation_are_stack_safe_at_depth_20k() {
    on_small_stack(|| {
        let mut pred = PresburgerPred::leq(vec![(0, 1)], 0);
        for _ in 0..DEPTH {
            pred = PresburgerPred::Not(Box::new(pred));
        }

        let cloned = pred.clone();
        assert_eq!(pred, cloned);
        assert_eq!(hash(&pred), hash(&cloned));
        assert_eq!(pred.num_vars(), 1);
        assert_eq!(
            evaluate_presburger_checked(&pred, &IntAssignment::new(vec![-1]), 2),
            Some(true)
        );

        let display = pred.to_string();
        assert!(display.starts_with("~(~("));
        assert!(display.ends_with(&")".repeat(DEPTH)));
        let debug = format!("{pred:?}");
        assert!(debug.starts_with("Not(Not("));
        assert!(debug.ends_with(&")".repeat(DEPTH)));

        let nfa = PresburgerNfa::from_pred(&pred, 2);
        assert!(nfa.is_nonempty());

        drop(nfa);
        drop(cloned);
        drop(pred);
    });
}

#[test]
fn nested_existentials_restore_shadowed_bindings_on_a_small_stack() {
    on_small_stack(|| {
        let mut pred = PresburgerPred::leq(vec![(0, 1)], 0);
        for _ in 0..DEPTH {
            pred = PresburgerPred::Exists { var: 0, body: Box::new(pred) };
        }

        assert_eq!(pred.num_vars(), 1);
        assert_eq!(
            evaluate_presburger_checked(&pred, &IntAssignment::new(vec![99]), 1),
            Some(true)
        );
        drop(pred);
    });
}

#[test]
fn skewed_conjunction_compiles_without_native_stack_growth() {
    on_small_stack(|| {
        let mut pred = PresburgerPred::leq(vec![(0, 1)], 0);
        for _ in 0..DEPTH {
            pred = PresburgerPred::And(Box::new(pred), Box::new(PresburgerPred::True));
        }

        assert_eq!(evaluate_presburger_checked(&pred, &IntAssignment::new(vec![0]), 1), Some(true));
        assert!(is_satisfiable_nfa(&pred, 1));
        drop(pred);
    });
}

#[test]
fn presburger_debug_and_display_preserve_their_compact_contracts() {
    let pred = PresburgerPred::Exists {
        var: 2,
        body: Box::new(PresburgerPred::Or(
            Box::new(PresburgerPred::Atom(LinearConstraint::new(vec![(0, 1)], 3))),
            Box::new(PresburgerPred::Not(Box::new(PresburgerPred::False))),
        )),
    };
    assert_eq!(
        format!("{pred:?}"),
        "Exists { var: 2, body: Or(Atom(LinearConstraint { terms: [(0, 1)], rhs: 3 }), Not(False)) }"
    );
    assert_eq!(pred.to_string(), "(exists x2. (x0 <= 3 \\/ ~(false)))");
}
