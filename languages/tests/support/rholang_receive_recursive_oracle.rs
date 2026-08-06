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

fn merge_pp_parallel_recursive(left: Proc, right: Proc) -> Proc {
    fn flatten(bag: &mut HashBag<Proc>, proc: Proc) {
        match &proc {
            Proc::PPar(elements) => {
                for (element, count) in elements.iter() {
                    for _ in 0..count {
                        flatten(bag, element.clone());
                    }
                }
            },
            _ => bag.insert(proc),
        }
    }

    let mut bag = HashBag::new();
    flatten(&mut bag, left);
    flatten(&mut bag, right);
    Proc::PPar(bag)
}

fn collect_pattern_bindings_recursive(
    pattern: &Proc,
    value: &Proc,
    env: &mut HashMap<FreeVar<String>, Proc>,
) -> bool {
    match (pattern, value) {
        (Proc::PVar(OrdVar(Var::Free(free))), value) => {
            if let Some(bound) = env.get(free) {
                bound.term_eq(value)
            } else {
                env.insert(free.clone(), value.clone());
                true
            }
        },
        (Proc::CastList(pattern_list), Proc::CastList(value_list)) => {
            match (pattern_list.as_ref(), value_list.as_ref()) {
                (List::ListLit(patterns), List::ListLit(values)) => {
                    patterns.len() == values.len()
                        && patterns.iter().zip(values.iter()).all(|(pattern, value)| {
                            collect_pattern_bindings_recursive(pattern, value, env)
                        })
                },
                _ => pattern.term_eq(value),
            }
        },
        (Proc::CastBag(pattern_bag), Proc::CastBag(value_bag)) => {
            match (pattern_bag.as_ref(), value_bag.as_ref()) {
                (Bag::BagLit(pattern_items), Bag::BagLit(value_items)) => {
                    match_bag_pattern_recursive(pattern_items, value_items, env)
                },
                _ => pattern.term_eq(value),
            }
        },
        (Proc::CastMap(pattern_map), Proc::CastMap(value_map)) => {
            match (pattern_map.as_ref(), value_map.as_ref()) {
                (Map::MapLit(pattern_entries), Map::MapLit(value_entries)) => {
                    pattern_entries.len() == value_entries.len()
                        && pattern_entries.iter().all(|(key, pattern_value)| {
                            value_entries
                                .get(key)
                                .map(|value| {
                                    collect_pattern_bindings_recursive(pattern_value, value, env)
                                })
                                .unwrap_or(false)
                        })
                },
                _ => pattern.term_eq(value),
            }
        },
        (Proc::CastPathmap(pattern_map), Proc::CastPathmap(value_map)) => {
            match (pattern_map.as_ref(), value_map.as_ref()) {
                (Pathmap::PathmapLit(pattern_entries), Pathmap::PathmapLit(value_entries)) => {
                    collect_pathmap_pattern_bindings_recursive(pattern_entries, value_entries, env)
                },
                _ => pattern.term_eq(value),
            }
        },
        (Proc::CastReadZipper(pattern_zipper), Proc::CastReadZipper(value_zipper)) => {
            match (pattern_zipper.as_ref(), value_zipper.as_ref()) {
                (ReadZipper::Lit(pattern_lit), ReadZipper::Lit(value_lit)) => {
                    let pattern_lit = pattern_lit.as_ref();
                    let value_lit = value_lit.as_ref();
                    pattern_lit.1 == value_lit.1
                        && collect_pathmap_pattern_bindings_recursive(
                            &pattern_lit.0,
                            &value_lit.0,
                            env,
                        )
                },
                _ => pattern.term_eq(value),
            }
        },
        (Proc::CastWriteZipper(pattern_zipper), Proc::CastWriteZipper(value_zipper)) => {
            match (pattern_zipper.as_ref(), value_zipper.as_ref()) {
                (WriteZipper::Lit(pattern_lit), WriteZipper::Lit(value_lit)) => {
                    let pattern_lit = pattern_lit.as_ref();
                    let value_lit = value_lit.as_ref();
                    pattern_lit.1 == value_lit.1
                        && collect_pathmap_pattern_bindings_recursive(
                            &pattern_lit.0,
                            &value_lit.0,
                            env,
                        )
                },
                _ => pattern.term_eq(value),
            }
        },
        (Proc::CastSet(pattern_set), Proc::CastSet(value_set)) => {
            match (pattern_set.as_ref(), value_set.as_ref()) {
                (Set::SetLit(pattern_items), Set::SetLit(value_items)) => {
                    match_set_pattern_recursive(pattern_items, value_items, env)
                },
                _ => pattern.term_eq(value),
            }
        },
        _ => pattern.term_eq(value),
    }
}

fn collect_pathmap_pattern_bindings_recursive(
    pattern: &crate::rholang::pathmap::ProcPathMap,
    value: &crate::rholang::pathmap::ProcPathMap,
    env: &mut HashMap<FreeVar<String>, Proc>,
) -> bool {
    use mettail_runtime::PathMapEntryRef;

    pattern.mode() == value.mode()
        && pattern.len() == value.len()
        && pattern.iter().all(|pattern_entry| {
            let Some(value_entry) = value.entry(pattern_entry.key()) else {
                return false;
            };
            match (pattern_entry, value_entry) {
                (PathMapEntryRef::Set(_), PathMapEntryRef::Set(_)) => true,
                (PathMapEntryRef::Map(_, pattern_value), PathMapEntryRef::Map(_, value)) => {
                    collect_pattern_bindings_recursive(pattern_value, value, env)
                },
                _ => false,
            }
        })
}

fn match_set_pattern_recursive(
    pattern: &mettail_runtime::HashSetLit<Proc>,
    value: &mettail_runtime::HashSetLit<Proc>,
    env: &mut HashMap<FreeVar<String>, Proc>,
) -> bool {
    if pattern.len() != value.len() {
        return false;
    }
    let mut remaining: Vec<Proc> = value.iter().cloned().collect();
    for pattern_element in pattern.iter() {
        let mut matched = false;
        for (index, value_element) in remaining.iter().enumerate() {
            let mut trial = env.clone();
            if collect_pattern_bindings_recursive(pattern_element, value_element, &mut trial) {
                *env = trial;
                remaining.remove(index);
                matched = true;
                break;
            }
        }
        if !matched {
            return false;
        }
    }
    true
}

fn match_bag_pattern_recursive(
    pattern: &HashBag<Proc>,
    value: &HashBag<Proc>,
    env: &mut HashMap<FreeVar<String>, Proc>,
) -> bool {
    let patterns: Vec<Proc> = pattern.iter_elements().cloned().collect();
    let values: Vec<Proc> = value.iter_elements().cloned().collect();
    if patterns.len() != values.len() {
        return false;
    }

    fn backtrack(
        index: usize,
        patterns: &[Proc],
        values: &[Proc],
        used: &mut [bool],
        env: &mut HashMap<FreeVar<String>, Proc>,
    ) -> bool {
        if index == patterns.len() {
            return true;
        }
        for candidate in 0..values.len() {
            if used[candidate] {
                continue;
            }
            let mut trial = env.clone();
            if collect_pattern_bindings_recursive(&patterns[index], &values[candidate], &mut trial)
            {
                used[candidate] = true;
                if backtrack(index + 1, patterns, values, used, &mut trial) {
                    *env = trial;
                    return true;
                }
                used[candidate] = false;
            }
        }
        false
    }

    backtrack(0, &patterns, &values, &mut vec![false; values.len()], env)
}

fn int(value: i64) -> Proc {
    Proc::CastInt(Arc::new(Int::NumLit(value)))
}

fn boolean(value: bool) -> Proc {
    Proc::CastBool(Arc::new(Bool::BoolLit(value)))
}

fn list(items: Vec<Proc>) -> Proc {
    Proc::CastList(Arc::new(List::ListLit(items)))
}

fn map(entries: impl IntoIterator<Item = (Proc, Proc)>) -> Proc {
    Proc::CastMap(Arc::new(Map::MapLit(mettail_runtime::HashMapLit::from_iter(entries))))
}

fn pathmap_map(entries: impl IntoIterator<Item = (Proc, Proc)>) -> Proc {
    Proc::CastPathmap(Arc::new(Pathmap::PathmapLit(mettail_runtime::PathMapLit::from_map_iter(
        entries,
    ))))
}

fn pathmap_set(keys: impl IntoIterator<Item = Proc>) -> Proc {
    Proc::CastPathmap(Arc::new(Pathmap::PathmapLit(mettail_runtime::PathMapLit::from_set_iter(
        keys,
    ))))
}

fn set(items: impl IntoIterator<Item = Proc>) -> Proc {
    Proc::CastSet(Arc::new(Set::SetLit(items.into_iter().collect())))
}

fn bag(items: impl IntoIterator<Item = Proc>) -> Proc {
    Proc::CastBag(Arc::new(Bag::BagLit(items.into_iter().collect())))
}

fn pattern_var(name: &str) -> Proc {
    Proc::PVar(OrdVar(Var::Free(FreeVar::fresh_named(name))))
}

fn assert_pattern_equivalent(pattern: &Proc, value: &Proc, label: &str) {
    let mut driven = HashMap::new();
    let mut recursive = HashMap::new();
    let driven_result = collect_pattern_bindings(pattern, value, &mut driven);
    let recursive_result = collect_pattern_bindings_recursive(pattern, value, &mut recursive);
    assert_eq!(driven_result, recursive_result, "result differs for {label}");
    assert_eq!(driven, recursive, "bindings differ for {label}");
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
    nested_bag.insert_n(Proc::PParInfix(Arc::new(int(1)), Arc::new(int(2))), 3);
    nested_bag.insert(int(3));
    let parallel = Proc::PParInfix(
        Arc::new(Proc::PPar(nested_bag)),
        Arc::new(Proc::PParInfix(Arc::new(int(4)), Arc::new(int(5)))),
    );
    let mut driven = HashBag::new();
    let mut recursive = HashBag::new();
    crate::rholang::runtime::flatten_proc_parallel_into(&mut driven, &parallel);
    flatten_parallel_into_recursive(&mut recursive, &parallel);
    assert_eq!(driven, recursive);

    let mut left_elements = HashBag::new();
    left_elements.insert(Proc::PParInfix(Arc::new(int(6)), Arc::new(int(7))));
    left_elements.insert(int(8));
    let left = Proc::PPar(left_elements);
    let mut right_elements = HashBag::new();
    right_elements.insert(int(9));
    let right = Proc::PPar(right_elements);
    assert_eq!(
        crate::rholang::runtime::merge_pp_parallel(left.clone(), right.clone()),
        merge_pp_parallel_recursive(left, right),
    );
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
            crate::rholang::runtime::flatten_proc_parallel_into(&mut flat, &parallel);
            assert_eq!(flat.len(), DEPTH + 1);

            // This is the production left-fold shape. Each merge must retain the accumulated
            // bag and its hash summary; rebuilding all prior members would make this quadratic.
            let mut merged = int(0);
            for value in 1..=DEPTH {
                merged = crate::rholang::runtime::merge_pp_parallel(merged, int(value as i64));
            }
            let Proc::PPar(elements) = &merged else {
                panic!("parallel merge must return PPar")
            };
            assert_eq!(elements.len(), DEPTH + 1);
        })
        .expect("spawn receive direct depth gate")
        .join()
        .expect("receive direct drivers must not overflow or panic");
}

#[test]
fn receive_collection_matcher_matches_the_bounded_recursive_oracle() {
    use crate::rholang::zipper::{ReadZipperLit, WriteZipperLit};

    let repeated = pattern_var("repeated");
    assert_pattern_equivalent(
        &list(vec![repeated.clone(), list(vec![repeated.clone()])]),
        &list(vec![int(7), list(vec![int(7)])]),
        "nested list with a repeated binder",
    );
    assert_pattern_equivalent(
        &list(vec![repeated.clone(), int(2)]),
        &list(vec![int(1), int(3)]),
        "list failure after a successful binding",
    );

    let map_binder = pattern_var("map-value");
    assert_pattern_equivalent(
        &map([(int(1), list(vec![map_binder]))]),
        &map([(int(1), list(vec![int(9)]))]),
        "ordered map value",
    );

    let path_binder = pattern_var("path-value");
    let path_pattern = pathmap_map([(list(vec![int(1)]), list(vec![path_binder]))]);
    let path_value = pathmap_map([(list(vec![int(1)]), list(vec![int(11)]))]);
    assert_pattern_equivalent(&path_pattern, &path_value, "path-map value");
    assert_pattern_equivalent(
        &pathmap_set([list(vec![int(1)])]),
        &pathmap_set([list(vec![int(1)])]),
        "path-map set mode",
    );
    assert_pattern_equivalent(
        &pathmap_set([list(vec![int(1)])]),
        &pathmap_map([(list(vec![int(1)]), int(11))]),
        "path-map mode mismatch",
    );

    let Proc::CastPathmap(read_pattern) = &path_pattern else {
        unreachable!()
    };
    let Pathmap::PathmapLit(read_pattern_map) = read_pattern.as_ref() else {
        unreachable!()
    };
    let read_pattern_map = read_pattern_map.clone();
    let Proc::CastPathmap(read_value) = &path_value else {
        unreachable!()
    };
    let Pathmap::PathmapLit(read_value_map) = read_value.as_ref() else {
        unreachable!()
    };
    let read_value_map = read_value_map.clone();
    let read_pattern = Proc::CastReadZipper(Arc::new(ReadZipper::Lit(Arc::new(ReadZipperLit(
        read_pattern_map.clone(),
        vec![1, 2],
    )))));
    let read_value = Proc::CastReadZipper(Arc::new(ReadZipper::Lit(Arc::new(ReadZipperLit(
        read_value_map.clone(),
        vec![1, 2],
    )))));
    assert_pattern_equivalent(&read_pattern, &read_value, "read zipper");
    let write_pattern = Proc::CastWriteZipper(Arc::new(WriteZipper::Lit(Arc::new(
        WriteZipperLit(read_pattern_map, vec![3, 4]),
    ))));
    let write_value = Proc::CastWriteZipper(Arc::new(WriteZipper::Lit(Arc::new(WriteZipperLit(
        read_value_map,
        vec![3, 5],
    )))));
    assert_pattern_equivalent(&write_pattern, &write_value, "write zipper focus mismatch");

    let set_left = pattern_var("set-left");
    let set_right = pattern_var("set-right");
    assert_pattern_equivalent(
        &set([set_left, set_right]),
        &set([int(13), int(17)]),
        "greedy set matching",
    );

    let bag_binder = pattern_var("bag-value");
    assert_pattern_equivalent(
        &bag([bag_binder.clone(), int(1)]),
        &bag([int(1), int(2)]),
        "bag search with a successful permutation",
    );
    assert_pattern_equivalent(
        &bag([bag_binder.clone(), bag_binder]),
        &bag([int(1), int(2)]),
        "bag search exhausting repeated-binder permutations",
    );

    assert_pattern_equivalent(
        &list(vec![map([(
            int(1),
            pathmap_map([(list(vec![int(2)]), bag([pattern_var("nested")]))]),
        )])]),
        &list(vec![map([(int(1), pathmap_map([(list(vec![int(2)]), bag([int(23)]))]))])]),
        "heterogeneous collection nesting",
    );
}

#[test]
fn receive_collection_matcher_is_stack_safe_on_deep_and_wide_inputs() {
    const DEPTH: usize = 20_000;
    const BAG_WIDTH: usize = 4_096;
    std::thread::Builder::new()
        .name("surface-receive-collections-256k".to_string())
        .stack_size(256 * 1024)
        .spawn(|| {
            let mut pattern = int(0);
            let mut value = int(0);
            for _ in 0..DEPTH {
                pattern = list(vec![pattern]);
                value = list(vec![value]);
            }
            assert!(collect_pattern_bindings(&pattern, &value, &mut HashMap::new(),));
            drop(pattern);
            drop(value);

            let key = int(0);
            let mut pattern = int(1);
            let mut value = int(1);
            for _ in 0..DEPTH {
                pattern = map([(key.clone(), pattern)]);
                value = map([(key.clone(), value)]);
            }
            assert!(collect_pattern_bindings(&pattern, &value, &mut HashMap::new(),));
            drop(pattern);
            drop(value);

            let path = list(vec![int(0)]);
            let mut pattern = int(2);
            let mut value = int(2);
            for _ in 0..DEPTH {
                pattern = pathmap_map([(path.clone(), pattern)]);
                value = pathmap_map([(path.clone(), value)]);
            }
            assert!(collect_pattern_bindings(&pattern, &value, &mut HashMap::new(),));
            drop(pattern);
            drop(value);

            let pattern = bag((0..BAG_WIDTH).map(|index| int(index as i64)));
            let value = pattern.clone();
            assert!(collect_pattern_bindings(&pattern, &value, &mut HashMap::new(),));
        })
        .expect("spawn receive collection depth gate")
        .join()
        .expect("receive collection matcher must not overflow or panic");
}
