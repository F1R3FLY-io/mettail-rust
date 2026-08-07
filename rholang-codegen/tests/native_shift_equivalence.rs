use mettail_ast::types::CollectionType;
use mettail_rholang_codegen::{
    bound_var_par, reflect_ground_term_par, shift_reflected_par_by, GroundTerm, NativeShiftSpec,
    BOUND_VAR_REFLECT_LABEL, FREE_VAR_REFLECT_LABEL, LAMBDA_REFLECT_LABEL,
    PEANO_SUCC_REFLECT_LABEL, PEANO_ZERO_REFLECT_LABEL, SHIFT_RESERVED_LABEL,
};
use models::rhoapi::expr::ExprInstance;
use proptest::prelude::*;
use prost::Message;

const FP: &str = "mettail-langdef-v1:native-shift-equivalence";

fn peano(mut value: usize) -> GroundTerm {
    let mut term = GroundTerm::nullary(PEANO_ZERO_REFLECT_LABEL);
    while value > 0 {
        term = GroundTerm::new(PEANO_SUCC_REFLECT_LABEL, vec![term]);
        value -= 1;
    }
    term
}

fn bound(value: usize) -> GroundTerm {
    GroundTerm::new(BOUND_VAR_REFLECT_LABEL, vec![peano(value)])
}

fn lambda(body: GroundTerm) -> GroundTerm {
    GroundTerm::new(LAMBDA_REFLECT_LABEL, vec![body])
}

fn recursive_reference_shift(term: &GroundTerm, cutoff: usize, amount: usize) -> GroundTerm {
    if term.constructor == BOUND_VAR_REFLECT_LABEL {
        fn decode(term: &GroundTerm) -> usize {
            if term.constructor == PEANO_ZERO_REFLECT_LABEL {
                0
            } else {
                1 + decode(&term.children[0])
            }
        }
        let index = decode(&term.children[0]);
        return if index >= cutoff {
            bound(index + amount)
        } else {
            term.clone()
        };
    }
    if term.constructor == FREE_VAR_REFLECT_LABEL {
        return term.clone();
    }
    if term.constructor == LAMBDA_REFLECT_LABEL {
        return lambda(recursive_reference_shift(&term.children[0], cutoff + 1, amount));
    }
    let children = term
        .children
        .iter()
        .map(|child| recursive_reference_shift(child, cutoff, amount))
        .collect();
    GroundTerm {
        constructor: term.constructor.clone(),
        children,
        coll_type: term.coll_type.clone(),
    }
}

fn arbitrary_term() -> impl Strategy<Value = GroundTerm> {
    let leaf = prop_oneof![
        (0usize..8).prop_map(bound),
        (0usize..8).prop_map(|index| GroundTerm::new(
            FREE_VAR_REFLECT_LABEL,
            vec![GroundTerm::nullary(format!("x{index}"))],
        )),
    ];
    leaf.prop_recursive(5, 96, 4, |inner| {
        prop_oneof![
            inner.clone().prop_map(lambda),
            (inner.clone(), inner.clone())
                .prop_map(|(left, right)| GroundTerm::new("Pair", vec![left, right])),
            prop::collection::vec(inner, 0..5).prop_map(|elements| GroundTerm::collection(
                CollectionType::HashBag,
                "PPar",
                elements,
            )),
        ]
    })
}

proptest! {
    #![proptest_config(ProptestConfig {
        cases: 256,
        failure_persistence: None,
        ..ProptestConfig::default()
    })]

    #[test]
    fn generated_pda_matches_the_recursive_oracle(
        term in arbitrary_term(),
        amount in 1usize..16,
    ) {
        let spec = NativeShiftSpec::new(
            FP,
            [("Pair".to_owned(), 2)],
            ["PPar".to_owned()],
        );
        let actual = shift_reflected_par_by(&reflect_ground_term_par(&term, FP), amount, &spec)
            .expect("the generated corpus is inside the declared shift domain");
        let expected = reflect_ground_term_par(&recursive_reference_shift(&term, 0, amount), FP);
        prop_assert_eq!(actual.encode_to_vec(), expected.encode_to_vec());
    }
}

#[test]
fn single_pass_pda_matches_recursive_composed_shift_on_positional_and_hashbag_terms() {
    let positional = GroundTerm::new(
        "C",
        vec![
            bound(0),
            lambda(bound(0)),
            lambda(bound(1)),
            GroundTerm::new(FREE_VAR_REFLECT_LABEL, vec![GroundTerm::nullary("x")]),
        ],
    );
    let bag = GroundTerm::collection(
        CollectionType::HashBag,
        "PPar",
        vec![positional.clone(), bound(3), lambda(bound(1))],
    );
    let root = GroundTerm::new("Root", vec![positional, bag]);
    let spec = NativeShiftSpec::new(
        FP,
        [("C".to_owned(), 4), ("Root".to_owned(), 2)],
        ["PPar".to_owned()],
    );

    for amount in 1..=8 {
        let actual = shift_reflected_par_by(&reflect_ground_term_par(&root, FP), amount, &spec)
            .expect("the production PDA accepts the reference corpus");
        let expected = reflect_ground_term_par(&recursive_reference_shift(&root, 0, amount), FP);
        assert_eq!(actual.encode_to_vec(), expected.encode_to_vec());
    }
}

#[test]
fn unsupported_reserved_subject_preserves_the_old_stall_domain() {
    let reserved = reflect_ground_term_par(&GroundTerm::nullary(SHIFT_RESERVED_LABEL), FP);
    let spec = NativeShiftSpec::new(FP, [], []);
    assert!(shift_reflected_par_by(&reserved, 1, &spec).is_err());
}

#[test]
fn language_specific_domain_rejects_unknown_objects_arities_bag_ops_and_nil() {
    let spec = NativeShiftSpec::new(FP, [("Pair".to_owned(), 2)], ["PPar".to_owned()]);
    let unknown = GroundTerm::new("Unknown", vec![bound(0)]);
    assert!(shift_reflected_par_by(&reflect_ground_term_par(&unknown, FP), 1, &spec).is_err());

    let wrong_arity = GroundTerm::new("Pair", vec![bound(0)]);
    assert!(shift_reflected_par_by(&reflect_ground_term_par(&wrong_arity, FP), 1, &spec).is_err());

    let foreign_bag = GroundTerm::collection(CollectionType::HashBag, "Other", vec![bound(0)]);
    assert!(shift_reflected_par_by(&reflect_ground_term_par(&foreign_bag, FP), 1, &spec).is_err());

    let binder_only = NativeShiftSpec::new(FP, [], []);
    assert!(shift_reflected_par_by(&models::rhoapi::Par::default(), 1, &binder_only).is_err());
}

#[test]
fn hereditary_ground_guard_precedes_constructor_dispatch_like_the_old_receiver() {
    let ground_unknown = reflect_ground_term_par(&GroundTerm::nullary("Unknown"), FP);
    let spec = NativeShiftSpec::new(FP, [], []);
    assert_eq!(shift_reflected_par_by(&ground_unknown, 10_000, &spec), Ok(ground_unknown));
}

#[test]
fn twenty_thousand_level_shift_and_protobuf_encoding_fit_a_256k_native_stack() {
    std::thread::Builder::new()
        .name("native-shift-stack-gate".to_owned())
        .stack_size(256 * 1024)
        .spawn(|| {
            const DEPTH: usize = 20_000;
            const AMOUNT: usize = 7;

            let mut term = bound(DEPTH);
            for _ in 0..DEPTH {
                term = lambda(term);
            }
            let reflected = reflect_ground_term_par(&term, FP);
            let spec = NativeShiftSpec::new(FP, [], []);
            let shifted = shift_reflected_par_by(&reflected, AMOUNT, &spec)
                .expect("the iterative shift PDA accepts the deep term");

            let mut leaf = &shifted;
            for _ in 0..DEPTH {
                let [expr] = leaf.exprs.as_slice() else {
                    panic!("lambda reflection is one EList");
                };
                let Some(ExprInstance::EListBody(list)) = expr.expr_instance.as_ref() else {
                    panic!("lambda reflection is an EList");
                };
                leaf = list.ps.last().expect("lambda has a body");
            }
            assert_eq!(leaf, &bound_var_par(DEPTH + AMOUNT, FP));

            // This explicitly exercises the generated protobuf serializer on the deep result;
            // it must use the target worktree's stack-safe generated PDA, not Rust recursion.
            let bytes = shifted.encode_to_vec();
            assert!(!bytes.is_empty());
        })
        .expect("spawn native-shift stack gate")
        .join()
        .expect("native shift, comparison, serialization, or Drop overflowed");
}
