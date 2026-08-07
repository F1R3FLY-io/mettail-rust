use mettail_prattail::alternating::{evaluate_word, AlternatingAutomaton, BranchingMode};
use mettail_prattail::logict::multiset_partitions;
use mettail_prattail::sft::{OutputFunction, SymbolicFiniteTransducer};
use mettail_prattail::sym_tree::SymTerm;
use mettail_prattail::sym_tree_transducer::{
    OutputBuilder, PayloadOut, SymbolicTreeTransducer, TransducerRule,
};
use mettail_prattail::symbolic::{IntervalAlgebra, IntervalPred};

const DEPTH: usize = 20_000;
const SMALL_STACK_BYTES: usize = 256 * 1024;

fn on_small_stack(test_name: &str, test: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .name(test_name.to_string())
        .stack_size(SMALL_STACK_BYTES)
        .spawn(test)
        .expect("spawn small-stack gate")
        .join()
        .expect("small-stack gate overflowed or panicked");
}

#[test]
fn alternating_word_evaluation_uses_constant_native_stack_and_linear_space() {
    on_small_stack("alternating-word-stack-gate", || {
        let mut automaton = AlternatingAutomaton::new();
        let state = automaton.add_state(BranchingMode::Existential, 0);
        automaton.initial_state = Some(state);
        automaton.add_transition(state, Some("a".into()), vec![state]);

        let word = vec!["a"; DEPTH];
        assert!(evaluate_word(&automaton, &word).0);
    });
}

#[test]
fn multiset_partition_pda_handles_twenty_thousand_distinct_items() {
    on_small_stack("multiset-partition-stack-gate", || {
        let items: Vec<(usize, usize)> = (0..DEPTH).map(|item| (item, 1)).collect();
        let partitions = multiset_partitions(&items, DEPTH).collect_all();

        assert_eq!(partitions.len(), 1);
        assert_eq!(partitions[0].selected_count, DEPTH);
        assert_eq!(partitions[0].selected.len(), DEPTH);
        assert!(partitions[0].remainder.is_empty());
    });
}

fn cycle_sft(size: usize) -> SymbolicFiniteTransducer<IntervalAlgebra, IntervalAlgebra> {
    let algebra = IntervalAlgebra::new(0, 1);
    let mut transducer = SymbolicFiniteTransducer::new(algebra.clone(), algebra);
    let states: Vec<_> = (0..size)
        .map(|index| transducer.add_state(true, Some(format!("q{index}"))))
        .collect();
    transducer.set_initial(states[0]);
    for index in 0..size {
        transducer.add_transition(
            states[index],
            states[(index + 1) % size],
            IntervalPred::True,
            OutputFunction::Constant(vec![0]),
        );
    }
    transducer
}

#[test]
fn sft_output_equivalence_walks_a_deep_product_cycle_on_a_small_stack() {
    on_small_stack("sft-equivalence-stack-gate", || {
        // Coprime cycle lengths force 139 * 149 = 20,711 distinct product
        // states before the traversal revisits its initial pair.
        let left = cycle_sft(139);
        let right = cycle_sft(149);
        assert_eq!(left.is_equivalent_functional(&right), Ok(true));
    });
}

#[test]
fn symbolic_tree_transduction_is_stack_safe_at_depth_twenty_thousand() {
    on_small_stack("symbolic-transducer-stack-gate", || {
        let algebra = IntervalAlgebra::new(0, 1);
        let mut transducer = SymbolicTreeTransducer::new(algebra.clone(), algebra);
        let state = transducer.add_state();
        transducer.set_accepting(state);
        transducer.register("Leaf", 0);
        transducer.register("Next", 1);
        transducer.add_rule(TransducerRule {
            constructor: "Leaf".into(),
            payload_guard: None,
            child_states: Vec::new(),
            target: state,
            output: OutputBuilder::Build {
                constructor: "Unit".into(),
                payload: PayloadOut::Structural,
                children: Vec::new(),
            },
        });
        transducer.add_rule(TransducerRule {
            constructor: "Next".into(),
            payload_guard: None,
            child_states: vec![state],
            target: state,
            output: OutputBuilder::Build {
                constructor: "Unit".into(),
                payload: PayloadOut::Structural,
                children: Vec::new(),
            },
        });

        let mut input = SymTerm::constant("Leaf");
        for _ in 0..DEPTH {
            input = SymTerm::node("Next", vec![input]);
        }

        let outputs = transducer.transduce(&input);
        assert_eq!(outputs.len(), 1);
        assert_eq!(outputs[0].constructor, "Unit");
        assert!(outputs[0].children.is_empty());
    });
}
