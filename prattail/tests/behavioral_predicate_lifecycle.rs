#[path = "support/behavioral_pred_recursive_oracle.rs"]
mod recursive_oracle;

use mettail_prattail::behavioral_algebra::BehavioralFormula;
use mettail_prattail::behavioral_pred::{BehavioralPred, PredArg, QuantifiedDomain, Quantifier};
use recursive_oracle::representative_cases;
use std::cmp::Ordering;
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

fn hash(value: &impl Hash) -> u64 {
    let mut hasher = DefaultHasher::new();
    value.hash(&mut hasher);
    hasher.finish()
}

#[test]
fn iterative_behavioral_operations_match_the_recursive_oracle() {
    let cases = representative_cases();
    for oracle in &cases {
        let production = oracle.to_production();
        let checked = production
            .try_clone_with(&mut |_, _, _| Ok::<(), &'static str>(()))
            .expect("unlimited checked clone");
        assert_eq!(checked, oracle.to_production());
        assert_eq!(production, oracle.to_production());
        assert_eq!(format!("{production:?}"), format!("{oracle:?}"));
        assert_eq!(production.to_string(), oracle.to_string());
        assert_eq!(hash(&production), hash(oracle));
        assert_eq!(production.free_vars(), oracle.free_vars());

        let expected_substitution = oracle.substitute_var("x", "renamed").to_production();
        assert_eq!(production.substitute_var("x", "renamed"), expected_substitution);
        assert_eq!(production.to_behavioral_formula(), oracle.to_behavioral_formula());
    }

    for left in &cases {
        for right in &cases {
            let production_left = left.to_production();
            let production_right = right.to_production();
            assert_eq!(production_left == production_right, left == right);
            assert_eq!(production_left.cmp(&production_right), left.cmp(right));
        }
    }
}

#[test]
fn behavioral_lifecycle_handles_depth_20k_on_a_256k_stack() {
    const DEPTH: usize = 20_000;
    std::thread::Builder::new()
        .name("behavioral-lifecycle-pda-small-stack".into())
        .stack_size(256 * 1024)
        .spawn(|| {
            let mut predicate = BehavioralPred::RelationQuery {
                relation_name: "ready".into(),
                args: vec![PredArg::Var("x".into())],
                negated: false,
            };
            for _ in 0..DEPTH {
                predicate = BehavioralPred::Not(Box::new(predicate));
            }

            let cloned = predicate.clone();
            assert_eq!(predicate, cloned);
            assert_eq!(predicate.cmp(&cloned), Ordering::Equal);
            assert_eq!(hash(&predicate), hash(&cloned));
            assert!(format!("{predicate:?}").ends_with(&")".repeat(DEPTH)));
            assert!(predicate.to_string().ends_with(&")".repeat(DEPTH + 1)));
            assert_eq!(predicate.free_vars(), ["x".to_owned()].into_iter().collect());

            let substituted = predicate.substitute_var("x", "renamed");
            assert_eq!(substituted.free_vars(), ["renamed".to_owned()].into_iter().collect());

            let formula = predicate.to_behavioral_formula().expect("Not spine lowers");
            dismantle_not_formula(formula, DEPTH);
            drop(substituted);
            let expected = BehavioralPred::And(Box::new(cloned), Box::new(BehavioralPred::Top));
            let source = BehavioralPred::And(Box::new(predicate), Box::new(BehavioralPred::Top));
            // Initialization/outer Visit/scheduling: 3 callbacks. Each Not:
            // 2 descent + 3 assembly callbacks. ready(x): 8 callbacks.
            // Refuse the right Visit with the full deep left result owned.
            let reject_at = 3 + 5 * DEPTH + 8 + 1;
            let mut calls = 0;
            let failed = source.try_clone_with(&mut |_, _, _| {
                calls += 1;
                if calls == reject_at {
                    Err("right child refused")
                } else {
                    Ok(())
                }
            });
            assert!(matches!(failed, Err("right child refused")));
            assert_eq!(calls, reject_at);
            assert_eq!(source, expected);
            let retried = source
                .try_clone_with(&mut |_, _, _| Ok::<(), &'static str>(()))
                .expect("retry after deep partial-result cleanup");
            assert_eq!(retried, expected);
            drop(retried);
            drop(source);
            drop(expected);
        })
        .expect("small-stack worker spawns")
        .join()
        .expect("behavioral lifecycle must not overflow the native stack");
}

type Charges = (usize, usize, usize);
type CheckedCopy = (Result<BehavioralPred, &'static str>, Charges, usize);

fn checked_copy(
    source: &BehavioralPred,
    limits: Charges,
    cancelled_call: Option<usize>,
) -> CheckedCopy {
    let mut used = (0, 0, 0);
    let mut calls = 0;
    let result = source.try_clone_with(&mut |work, records, bytes| {
        calls += 1;
        if cancelled_call == Some(calls) {
            return Err("cancelled");
        }
        if work > limits.0 - used.0 || records > limits.1 - used.1 || bytes > limits.2 - used.2 {
            return Err("limit");
        }
        used.0 += work;
        used.1 += records;
        used.2 += bytes;
        Ok(())
    });
    (result, used, calls)
}

#[test]
fn checked_clone_exact_admission_and_every_callback_refusal() {
    let source = representative_cases()
        .into_iter()
        .map(|oracle| oracle.to_production())
        .find(|predicate| matches!(predicate, BehavioralPred::AcMatch { .. }))
        .expect("existing AcMatch corpus fixture");
    let original = source.clone();
    // Existing fixture: bag Var("bag"), elements StringLit("a"), Var("x"),
    // rest Some("tail"). Three argument copies, one vector, one rest string.
    let expected_trace = [
        (0, 3, 0),
        (1, 0, 0),
        (4, 2, 0),
        (0, 1, 0),
        (1, 0, 0),
        (1, 0, 0),
        (1, 0, 3), // bag
        (2, 1, 0),
        (0, 2, 0), // vector and two slots
        (1, 0, 0),
        (1, 0, 0),
        (1, 0, 1), // "a"
        (1, 0, 0),
        (1, 0, 0),
        (1, 0, 1), // x
        (2, 1, 4), // rest
    ];
    let total = (18, 10, 9);
    let mut observed = Vec::new();
    let result = source
        .try_clone_with(&mut |w, r, b| {
            observed.push((w, r, b));
            Ok::<(), &'static str>(())
        })
        .expect("checked fixture clone");
    assert_eq!(observed.as_slice(), expected_trace.as_slice());
    assert_eq!(result, original);
    let (result, used, calls) = checked_copy(&source, total, None);
    assert_eq!(result.expect("exact budget"), original);
    assert_eq!((used, calls), (total, 16));
    for limits in [(17, 10, 9), (18, 9, 9), (18, 10, 8)] {
        let (result, used, calls) = checked_copy(&source, limits, None);
        assert_eq!(result, Err("limit"));
        assert_eq!((used, calls), ((16, 9, 5), 16));
        assert_eq!(source, original);
    }
    for cancelled in 1..=expected_trace.len() {
        let (result, used, calls) = checked_copy(&source, total, Some(cancelled));
        assert_eq!(result, Err("cancelled"));
        let prefix = expected_trace[..cancelled - 1]
            .iter()
            .fold((0, 0, 0), |(w, r, b), &(dw, dr, db)| (w + dw, r + dr, b + db));
        assert_eq!((used, calls), (prefix, cancelled));
        assert_eq!(source, original);
    }
    assert_eq!(checked_copy(&source, total, None).0.expect("retry"), original);
}

#[test]
fn checked_quantified_copy_refuses_after_body_pop_and_covers_flat_domains() {
    for domain in [
        None,
        Some(QuantifiedDomain::Bounded(3)),
        Some(QuantifiedDomain::Named("x".into())),
        Some(QuantifiedDomain::Enumerated(vec![
            PredArg::StringLit("first".into()),
            PredArg::Var("x".into()),
        ])),
    ] {
        let source = BehavioralPred::Quantified {
            quantifier: Quantifier::ForAll,
            var: "x".into(),
            domain,
            body: Box::new(BehavioralPred::Not(Box::new(BehavioralPred::Top))),
        };
        let original = source.clone();
        let (copied, _, count) = checked_copy(&source, (usize::MAX, usize::MAX, usize::MAX), None);
        assert_eq!(copied.expect("all domain variants"), original);
        // Fixed control prefix: 3 outer setup + 2 Not descent + 2 Top +
        // 3 Not assembly + 3 quantified assembly = 13 callbacks.
        // Callback 14 inspects the domain, after the body has been popped.
        for cancel in 14..=count {
            let (result, _, calls) =
                checked_copy(&source, (usize::MAX, usize::MAX, usize::MAX), Some(cancel));
            assert_eq!(result, Err("cancelled"));
            assert_eq!(calls, cancel);
            assert_eq!(source, original);
        }
        assert_eq!(source.substitute_var("x", "renamed"), original, "shadowed domain and body");
        assert_eq!(
            checked_copy(&source, (usize::MAX, usize::MAX, usize::MAX), None)
                .0
                .expect("retry"),
            original
        );
    }
    let source = BehavioralPred::AcMatch {
        bag: PredArg::IntLit(1),
        elements: vec![],
        rest: None,
    };
    assert_eq!(
        checked_copy(&source, (usize::MAX, usize::MAX, usize::MAX), None)
            .0
            .expect("empty AC payload"),
        source
    );
}

fn dismantle_not_formula(formula: BehavioralFormula, expected_depth: usize) {
    let mut depth = 0;
    let mut cursor = &formula;
    loop {
        match cursor {
            BehavioralFormula::Not(inner) => {
                cursor = inner;
                depth += 1;
            },
            BehavioralFormula::Relation { name, args } => {
                assert_eq!(name, "ready");
                assert_eq!(args.len(), 1);
                break;
            },
            _ => panic!("expected a Not formula spine ending in ready(x)"),
        }
    }
    assert_eq!(depth, expected_depth);
}
