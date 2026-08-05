use mettail_prattail::sft::OutputTerm;
use mettail_prattail::symbolic::IntervalAlgebra;

type Term = OutputTerm<IntervalAlgebra, IntervalAlgebra>;
const DEPTH: usize = 20_000;
const SMALL_STACK_BYTES: usize = 256 * 1024;

#[test]
fn output_term_lifecycle_application_and_composition_are_stack_safe_at_depth_20k() {
    std::thread::Builder::new()
        .name("output-term-small-stack".to_string())
        .stack_size(SMALL_STACK_BYTES)
        .spawn(|| {
            let mut term = Term::Id;
            for _ in 0..DEPTH {
                term = Term::Concat(Box::new(term), Box::new(Term::Eps));
            }

            let cloned = term.clone();
            assert_eq!(term, cloned);
            assert_eq!(term.apply(&7), [7]);
            assert!(format!("{term:?}").starts_with("Concat(Concat("));

            let composed = term.then(&Term::Id);
            assert_eq!(composed.apply(&11), [11]);

            drop(cloned);
            drop(composed);
            drop(term);
        })
        .expect("spawn output-term small-stack gate")
        .join()
        .expect("output-term small-stack gate panicked");
}

#[test]
fn output_term_debug_preserves_the_compact_contract() {
    let term = Term::Concat(Box::new(Term::Id), Box::new(Term::Const(vec![2, 3])));
    assert_eq!(format!("{term:?}"), "Concat(Id, Const([2, 3]))");
    assert_eq!(term.apply(&1), [1, 2, 3]);
}
