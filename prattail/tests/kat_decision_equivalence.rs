use std::collections::HashMap;

use mettail_prattail::kat::{check_equivalence_exact, BooleanTest, KatExpr};
use mettail_prattail::symbolic::{eval_test_public, BooleanAlgebra, KatBooleanAlgebra};

fn valuation(bits: usize) -> HashMap<String, bool> {
    HashMap::from([("p".to_string(), bits & 1 != 0), ("q".to_string(), bits & 2 != 0)])
}

fn exhaustive_boolean_witness(predicate: &BooleanTest) -> Option<HashMap<String, bool>> {
    (0..4)
        .map(valuation)
        .find(|candidate| eval_test_public(predicate, candidate))
}

fn max_actions(expression: &KatExpr) -> usize {
    match expression {
        KatExpr::Zero | KatExpr::One | KatExpr::Test(_) => 0,
        KatExpr::Action(_) => 1,
        KatExpr::Seq(left, right) => max_actions(left) + max_actions(right),
        KatExpr::Alt(left, right) => max_actions(left).max(max_actions(right)),
        KatExpr::Star(_) => panic!("the finite-language oracle accepts only star-free expressions"),
    }
}

fn accepts_guarded_substring(
    expression: &KatExpr,
    valuations: &[HashMap<String, bool>],
    actions: &[&str],
    start: usize,
    end: usize,
) -> bool {
    match expression {
        KatExpr::Zero => false,
        KatExpr::One => start == end,
        KatExpr::Test(predicate) => start == end && eval_test_public(predicate, &valuations[start]),
        KatExpr::Action(action) => end == start + 1 && action == actions[start],
        KatExpr::Seq(left, right) => (start..=end).any(|middle| {
            accepts_guarded_substring(left, valuations, actions, start, middle)
                && accepts_guarded_substring(right, valuations, actions, middle, end)
        }),
        KatExpr::Alt(left, right) => {
            accepts_guarded_substring(left, valuations, actions, start, end)
                || accepts_guarded_substring(right, valuations, actions, start, end)
        },
        KatExpr::Star(_) => panic!("the finite-language oracle accepts only star-free expressions"),
    }
}

fn oracle_equivalent(left: &KatExpr, right: &KatExpr) -> bool {
    let maximum = max_actions(left).max(max_actions(right));
    for length in 0..=maximum {
        let action_words = 1usize << length;
        let valuation_words = 1usize << (2 * (length + 1));
        for action_bits in 0..action_words {
            let actions: Vec<_> = (0..length)
                .map(|index| {
                    if action_bits & (1 << index) == 0 {
                        "a"
                    } else {
                        "b"
                    }
                })
                .collect();
            for valuation_bits in 0..valuation_words {
                let valuations: Vec<_> = (0..=length)
                    .map(|index| valuation((valuation_bits >> (2 * index)) & 3))
                    .collect();
                let left_accepts =
                    accepts_guarded_substring(left, &valuations, &actions, 0, length);
                let right_accepts =
                    accepts_guarded_substring(right, &valuations, &actions, 0, length);
                if left_accepts != right_accepts {
                    return false;
                }
            }
        }
    }
    true
}

#[test]
fn iterative_boolean_search_matches_exhaustive_truth_tables() {
    let algebra = KatBooleanAlgebra::new(vec!["p".to_string(), "q".to_string()]);
    let p = BooleanTest::atom("p");
    let q = BooleanTest::atom("q");
    let predicates = vec![
        BooleanTest::True,
        BooleanTest::False,
        p.clone(),
        BooleanTest::not(p.clone()),
        BooleanTest::and(p.clone(), q.clone()),
        BooleanTest::or(p.clone(), q.clone()),
        BooleanTest::and(p.clone(), BooleanTest::not(p.clone())),
        BooleanTest::or(
            BooleanTest::and(p.clone(), q.clone()),
            BooleanTest::and(BooleanTest::not(p), BooleanTest::not(q)),
        ),
    ];

    for predicate in predicates {
        let expected = exhaustive_boolean_witness(&predicate);
        let actual = algebra.witness(&predicate);
        assert_eq!(actual.is_some(), expected.is_some());
        if let Some(witness) = actual {
            assert!(algebra.evaluate(&predicate, &witness));
        }
    }
}

#[test]
fn partial_derivative_equivalence_matches_a_guarded_string_oracle() {
    let p = || KatExpr::test(BooleanTest::atom("p"));
    let q = || KatExpr::test(BooleanTest::atom("q"));
    let a = || KatExpr::action("a");
    let b = || KatExpr::action("b");
    let expressions = vec![
        KatExpr::Zero,
        KatExpr::One,
        p(),
        q(),
        a(),
        b(),
        KatExpr::seq(p(), a()),
        KatExpr::seq(a(), q()),
        KatExpr::seq(a(), b()),
        KatExpr::alt(a(), b()),
        KatExpr::alt(KatExpr::seq(p(), a()), KatExpr::seq(q(), b())),
        KatExpr::seq(KatExpr::alt(a(), b()), a()),
    ];

    for left in &expressions {
        for right in &expressions {
            assert_eq!(
                check_equivalence_exact(left, right),
                oracle_equivalent(left, right),
                "exact decision disagreed for {left} and {right}",
            );
        }
    }
}
