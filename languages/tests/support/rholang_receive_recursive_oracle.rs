//! Bounded recursive references for direct surface receive traversals.
//!
//! Production uses loops and explicit continuation stacks. These equations remain test-only and
//! are exercised only on shallow values for exact differential checks.

use super::*;
use std::sync::Arc;

fn name_pattern_to_proc_recursive(name: &Name) -> Proc {
    match name {
        Name::NVar(var) => Proc::PVar(var.clone()),
        Name::NQuote(proc) | Name::NQuoteShort(proc) => proc.as_ref().clone(),
        Name::NQuoteNil => Proc::PZero,
        Name::NParen(inner) => name_pattern_to_proc_recursive(inner),
        _ => Proc::Err,
    }
}

fn normalize_quote_name_recursive(name: &Name) -> Name {
    match name {
        Name::NQuoteNil => Name::NQuote(Arc::new(Proc::PZero)),
        Name::NQuoteShort(proc) => Name::NQuote(Arc::new(proc.as_ref().clone())),
        Name::NParen(inner) => Name::NParen(Arc::new(normalize_quote_name_recursive(inner))),
        other => other.clone(),
    }
}

fn eval_guard_disposition_recursive(cond: &Proc) -> GuardDisposition {
    use GuardDisposition::{Blocks, Declines, Fires};
    match cond {
        Proc::CastBool(value) => match value.as_ref() {
            Bool::BoolLit(value) => GuardDisposition::from_decided(*value),
            _ => Declines,
        },
        Proc::And(left, right) => match eval_guard_disposition_recursive(left) {
            Declines => Declines,
            Blocks => Blocks,
            Fires => eval_guard_disposition_recursive(right),
        },
        Proc::Or(left, right) => match eval_guard_disposition_recursive(left) {
            Declines => Declines,
            Fires => Fires,
            Blocks => eval_guard_disposition_recursive(right),
        },
        Proc::Implies(left, right) => match eval_guard_disposition_recursive(left) {
            Declines => Declines,
            Blocks => Fires,
            Fires => eval_guard_disposition_recursive(right),
        },
        Proc::Matches(target, formula) => GuardDisposition::from_verdict(
            crate::rholang::formula::host_matches_verdict(target, formula),
        ),
        Proc::Not(inner) => eval_guard_disposition_recursive(inner).negate(),
        Proc::Eq(left, right) => {
            match crate::rholang::runtime::compare_collection_equality(left, right) {
                Some(value) => GuardDisposition::from_decided(value),
                None => GuardDisposition::from_verdict(
                    eval_cmp_order(left, right).map(|order| order == Ordering::Equal),
                ),
            }
        },
        Proc::Ne(left, right) => {
            match crate::rholang::runtime::compare_collection_equality(left, right) {
                Some(value) => GuardDisposition::from_decided(!value),
                None => GuardDisposition::from_verdict(
                    eval_cmp_order(left, right).map(|order| order != Ordering::Equal),
                ),
            }
        },
        Proc::Gt(left, right) => GuardDisposition::from_verdict(
            eval_cmp_order(left, right).map(|order| order == Ordering::Greater),
        ),
        Proc::Lt(left, right) => GuardDisposition::from_verdict(
            eval_cmp_order(left, right).map(|order| order == Ordering::Less),
        ),
        Proc::GtEq(left, right) => GuardDisposition::from_verdict(
            eval_cmp_order(left, right)
                .map(|order| order == Ordering::Greater || order == Ordering::Equal),
        ),
        Proc::LtEq(left, right) => GuardDisposition::from_verdict(
            eval_cmp_order(left, right)
                .map(|order| order == Ordering::Less || order == Ordering::Equal),
        ),
        _ => Declines,
    }
}

fn flatten_parallel_into_recursive(bag: &mut HashBag<Proc>, proc: &Proc) {
    match proc {
        Proc::PPar(elements) => {
            for (element, count) in elements.iter() {
                for _ in 0..count {
                    flatten_parallel_into_recursive(bag, element);
                }
            }
        },
        Proc::PParInfix(left, right) => {
            flatten_parallel_into_recursive(bag, left);
            flatten_parallel_into_recursive(bag, right);
        },
        other => bag.insert(other.clone()),
    }
}

fn int(value: i64) -> Proc {
    Proc::CastInt(Arc::new(Int::NumLit(value)))
}

fn boolean(value: bool) -> Proc {
    Proc::CastBool(Arc::new(Bool::BoolLit(value)))
}

#[test]
fn receive_direct_drivers_match_the_bounded_recursive_oracles() {
    let names = [
        Name::NQuoteNil,
        Name::NQuoteShort(Arc::new(int(1))),
        Name::NParen(Arc::new(Name::NQuoteNil)),
        Name::NParen(Arc::new(Name::NParen(Arc::new(Name::NQuoteShort(Arc::new(int(2))))))),
    ];
    for (index, name) in names.iter().enumerate() {
        assert_eq!(
            name_pattern_to_proc(name),
            name_pattern_to_proc_recursive(name),
            "name pattern differs at corpus index {index}"
        );
        assert_eq!(
            normalize_quote_name(name),
            normalize_quote_name_recursive(name),
            "quote normalization differs at corpus index {index}"
        );
    }

    let guards = [
        boolean(true),
        boolean(false),
        Proc::And(Arc::new(boolean(false)), Arc::new(Proc::PZero)),
        Proc::And(Arc::new(boolean(true)), Arc::new(Proc::PZero)),
        Proc::Or(Arc::new(boolean(true)), Arc::new(Proc::PZero)),
        Proc::Or(Arc::new(boolean(false)), Arc::new(Proc::PZero)),
        Proc::Implies(Arc::new(boolean(false)), Arc::new(Proc::PZero)),
        Proc::Implies(Arc::new(boolean(true)), Arc::new(Proc::PZero)),
        Proc::Not(Arc::new(Proc::PZero)),
        Proc::Eq(Arc::new(int(2)), Arc::new(int(2))),
        Proc::Lt(Arc::new(int(1)), Arc::new(int(2))),
    ];
    for (index, guard) in guards.iter().enumerate() {
        assert_eq!(
            eval_guard_disposition(guard),
            eval_guard_disposition_recursive(guard),
            "guard disposition differs at corpus index {index}"
        );
    }

    let mut nested_bag = HashBag::new();
    nested_bag.insert(Proc::PParInfix(Arc::new(int(1)), Arc::new(int(2))));
    nested_bag.insert(int(3));
    let parallel = Proc::PParInfix(
        Arc::new(Proc::PPar(nested_bag)),
        Arc::new(Proc::PParInfix(Arc::new(int(4)), Arc::new(int(5)))),
    );
    let mut driven = HashBag::new();
    let mut recursive = HashBag::new();
    flatten_parallel_into(&mut driven, &parallel);
    flatten_parallel_into_recursive(&mut recursive, &parallel);
    assert_eq!(driven, recursive);
}

#[test]
fn receive_direct_drivers_are_stack_safe_at_depth_20k() {
    const DEPTH: usize = 20_000;
    std::thread::Builder::new()
        .name("surface-receive-direct-256k".to_string())
        .stack_size(256 * 1024)
        .spawn(|| {
            let mut name = Name::NQuoteNil;
            for _ in 0..DEPTH {
                name = Name::NParen(Arc::new(name));
            }
            assert_eq!(name_pattern_to_proc(&name), Proc::PZero);
            let mut normalized = normalize_quote_name(&name);
            for _ in 0..DEPTH {
                let Name::NParen(inner) = &normalized else {
                    panic!("quote normalization changed the parenthesis spine")
                };
                normalized = inner.as_ref().clone();
            }
            assert!(matches!(normalized, Name::NQuote(_)));

            let mut guard = boolean(true);
            for _ in 0..DEPTH {
                guard = Proc::Not(Arc::new(guard));
            }
            assert_eq!(eval_guard_disposition(&guard), GuardDisposition::Fires);

            let mut parallel = int(0);
            for value in 1..=DEPTH {
                parallel = Proc::PParInfix(Arc::new(parallel), Arc::new(int(value as i64)));
            }
            let mut flat = HashBag::new();
            flatten_parallel_into(&mut flat, &parallel);
            assert_eq!(flat.len(), DEPTH + 1);
        })
        .expect("spawn receive direct depth gate")
        .join()
        .expect("receive direct drivers must not overflow or panic");
}
