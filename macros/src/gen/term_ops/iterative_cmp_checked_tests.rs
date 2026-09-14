//! Checked comparison over the existing production-layout Hash fixture.
use super::*;
use crate::gen::term_ops::iterative_hash::checked_tests::{fixture_language, literal_label};

fn compact(tokens: TokenStream) -> String {
    tokens.to_string().split_whitespace().collect()
}

fn ordered(source: &str, needles: &[&str]) {
    let mut rest = source;
    for needle in needles {
        let index = rest
            .find(needle)
            .unwrap_or_else(|| panic!("missing {needle} in {source}"));
        rest = &rest[index + needle.len()..];
    }
}

#[test]
fn checked_companion_has_no_tls_and_checks_support_before_alias_or_indices() {
    let language = fixture_language();
    let generated = generate_checked_iterative_cmp(&language);
    let items = syn::parse2::<syn::File>(generated.clone()).expect("checked companion syntax");
    let tokens = compact(generated);
    assert!(!tokens.contains("thread_local!"));
    assert!(!tokens.contains(".try_with("));
    assert!(!tokens.contains("std::cell::Cell"));
    for (name, suffix) in [
        ("checked_eq_handle_proc", "std::ptr::eq(left_ptr,right_ptr)"),
        ("checked_cmp_handle_proc", "letl_idx=variant_index_proc(left)"),
    ] {
        let body = items
            .items
            .iter()
            .find_map(|item| match item {
                syn::Item::Fn(item) if item.sig.ident == name => Some(&item.block),
                _ => None,
            })
            .expect("checked category helper");
        let body = compact(quote! { #body });
        ordered(
            &body,
            &[
                "checked_cmp_handle_proc_support(unsafe{&*left_ptr})",
                "checked_cmp_handle_proc_support(unsafe{&*right_ptr})",
                suffix,
            ],
        );
        if name == "checked_eq_handle_proc" {
            ordered(&body, &["std::ptr::eq(left_ptr,right_ptr)", "variant_index_proc(left)"]);
        }
    }
}

#[test]
fn checked_comparison_captures_actual_production_layout_executable() {
    let language = fixture_language();
    let declarations =
        syn::parse2::<syn::File>(crate::gen::types::enums::generate_ast_enums(&language))
            .expect("production enum declarations");
    let enum_types: Vec<_> = declarations
        .items
        .into_iter()
        .filter_map(|item| match item {
            syn::Item::Enum(mut item) if language.types.iter().any(|ty| ty.name == item.ident) => {
                item.attrs.clear();
                Some(item)
            },
            _ => None,
        })
        .collect();
    assert_eq!(enum_types.len(), language.types.len());
    let ordinary_clone = crate::gen::term_ops::iterative_clone::generate_iterative_clone(&language);
    let ordinary_cmp = generate_iterative_cmp(&language);
    let ordinary_hash = crate::gen::term_ops::iterative_hash::generate_iterative_hash(&language);
    let ordinary_drop = crate::gen::term_ops::iterative_drop::generate_iterative_drop(&language);
    let checked = generate_checked_iterative_cmp(&language);
    let proc_var = crate::gen::generate_var_label(&format_ident!("Proc"));
    let int_literal = literal_label(&language, "Int");
    let bool_literal = literal_label(&language, "Bool");
    let text_literal = literal_label(&language, "Text");
    let list_literal = literal_label(&language, "List");
    let bag_literal = literal_label(&language, "Bag");
    let map_literal = literal_label(&language, "Map");
    let set_literal = literal_label(&language, "Set");
    let pathmap_literal = literal_label(&language, "Pathmap");
    let bytes_literal = literal_label(&language, "Bytes");
    let fixture = quote! {
        #![allow(dead_code, unused_variables, unreachable_patterns, non_snake_case)]
        use std::cmp::Ordering;
        use std::hash::{Hash, Hasher};
        use std::sync::Arc;
        use mettail_runtime::{Binder, BindingFailure, CheckedIterativeComparison,
            FltNode, FltTemplateBounds, FreeVar, NativeComparisonFailure, OrdVar, Scope, Var};
        #(#enum_types)*
        #ordinary_clone #ordinary_cmp #ordinary_hash #ordinary_drop #checked

        #[derive(Clone, Copy, Debug, PartialEq, Eq)]
        enum Answer { Equality(bool), Ordering(Ordering) }

        fn native<T: Ord>(left: &T, right: &T, ordering: bool) -> Answer {
            if ordering { Answer::Ordering(left.cmp(right)) }
            else { Answer::Equality(left == right) }
        }

        fn run<T: CheckedIterativeComparison, E>(left: &T, right: &T, ordering: bool,
            reserve: &mut impl FnMut(usize, usize) -> Result<(), E>,
        ) -> Result<Answer, NativeComparisonFailure<E>> {
            if ordering { left.try_cmp_iterative(right, reserve).map(Answer::Ordering) }
            else { left.try_eq_iterative(right, reserve).map(Answer::Equality) }
        }

        fn exercise<T: CheckedIterativeComparison>(left: &T, right: &T) {
            for ordering in [false, true] {
                let expected = native(left, right, ordering);
                let mut trace = Vec::new();
                assert_eq!(run(left, right, ordering, &mut |w,u| {
                    trace.push((w,u)); Ok::<_, usize>(())
                }), Ok(expected));
                let total = trace.iter().fold((0usize,0usize), |(w,u),(x,y)| (
                    w.checked_add(*x).expect("fixture work fits"),
                    u.checked_add(*y).expect("fixture units fit"),
                ));
                assert!(total.0 > 0 && total.1 > 0);
                for stop in 1..=trace.len() {
                    let mut observed = Vec::new();
                    let result = run(left, right, ordering, &mut |w,u| {
                        observed.push((w,u));
                        if observed.len() == stop { Err(stop) } else { Ok(()) }
                    });
                    assert!(matches!(result, Err(NativeComparisonFailure::Admission(
                        BindingFailure::Reservation(n))) if n == stop));
                    assert_eq!(observed, trace[..stop]);
                }
                for limit in [(total.0-1,total.1), (total.0,total.1-1), total] {
                    let mut used = (0usize,0usize);
                    let result = run(left, right, ordering, &mut |w,u| {
                        if w > limit.0-used.0 || u > limit.1-used.1 { return Err(0usize); }
                        used.0 += w; used.1 += u; Ok(())
                    });
                    if limit == total { assert_eq!(result, Ok(expected)); assert_eq!(used, total); }
                    else { assert!(matches!(result, Err(NativeComparisonFailure::Admission(
                        BindingFailure::Reservation(0))))); }
                }
                assert_eq!(native(left, right, ordering), expected, "borrowed source preserved");
            }
        }

        fn refuse<T: CheckedIterativeComparison>(left: &T, right: &T,
            category: &str, constructor: &str, root_callbacks: Option<usize>,
        ) {
            for ordering in [false, true] {
                let mut trace = Vec::new();
                let result = run(left, right, ordering, &mut |w,u| {
                    trace.push((w,u)); Ok::<_, ()>(())
                });
                assert!(matches!(result, Err(NativeComparisonFailure::UnsupportedConstructor {
                    category: c, constructor: k,
                }) if c == category && k == constructor));
                if let Some(count) = root_callbacks {
                    // Root header, root push, pop, dispatch, then paid operand
                    // support probes. No alias or discriminant charge is reached.
                    assert_eq!(trace.len(), count);
                    assert_eq!(&trace[..2], &[(2,4),(2,4)]);
                    assert!(trace[2..].iter().all(|entry| *entry == (1,0)));
                }
            }
        }

        fn guest(selector: FreeVar<String>) -> Arc<FltNode> {
            Arc::new(FltNode {
                selector: OrdVar(Var::Free(selector)), selector_name: "guest".into(),
                category: "Proc".into(), open_src: "`".into(), body_src: "λ".into(),
                holes: Vec::new(), pieces: vec![mettail_runtime::FltTemplatePiece::Text {
                    text: "λ".into(), range: mettail_runtime::FltSourceRange::new(0,2),
                }], close_src: "`".into(), bounds: FltTemplateBounds::default(), position: 7,
            })
        }

        fn terminal_drain_refusal_is_not_a_completed_ordering() {
            let left = Proc::PPair(Arc::new(Proc::PToken("a".into())),
                Arc::new(Proc::PToken("unvisited tail".into())));
            let right = Proc::PPair(Arc::new(Proc::PToken("b".into())),
                Arc::new(Proc::PToken("unvisited tail".into())));
            let mut trace = Vec::new();
            assert_eq!(left.try_cmp_iterative(&right, &mut |w,u| {
                trace.push((w,u)); Ok::<_, usize>(())
            }), Ok(Ordering::Less));
            // First-child mismatch leaves one child pending: begin, its
            // pop/discard route, then the terminal empty pop.
            assert_eq!(&trace[trace.len()-4..], &[(1,0);4]);
            let mut seen = 0;
            let result = left.try_cmp_iterative(&right, &mut |_,_| {
                seen += 1; if seen == trace.len() { Err("terminal") } else { Ok(()) }
            });
            assert!(matches!(result, Err(NativeComparisonFailure::Admission(
                BindingFailure::Reservation("terminal")))));
            assert_eq!(seen, trace.len());
            exercise(&left, &right);
        }

        fn map(entries: impl IntoIterator<Item = (Proc, Proc)>) -> Map {
            let mut result = mettail_runtime::HashMapLit::new();
            for (key, value) in entries { result.insert(key, value); }
            Map::#map_literal(result)
        }

        fn token(text: &str) -> Proc { Proc::PToken(text.into()) }

        fn map_proc(value: Map) -> Proc {
            // Existing generated application constructor, not a new fixture term.
            Proc::ApplyMap(Arc::new(Proc::PZero), Arc::new(value))
        }

        fn bag(entries: impl IntoIterator<Item = (Proc, usize)>) -> mettail_runtime::HashBag<Proc> {
            let mut result = mettail_runtime::HashBag::new();
            for (key, count) in entries { result.insert_n(key, count); }
            result
        }

        fn bag_cases() {
            let empty = Proc::PBag(bag([]));
            exercise(&empty, &empty);
            exercise(&empty, &Proc::PBag(bag([])));
            let left = Proc::PBag(bag([(token("a"), 2), (token("b"), 1)]));
            let permuted = Proc::PBag(bag([(token("b"), 1), (token("a"), 1), (token("a"), 1)]));
            assert_eq!(left.cmp(&permuted), Ordering::Equal);
            exercise(&left, &permuted);
            exercise(&empty, &left);
            exercise(&left, &empty);
            let changed = Proc::PBag(bag([(token("a"), 1), (token("b"), 2)]));
            assert_ne!(left.cmp(&changed), Ordering::Equal);
            exercise(&left, &changed);
            exercise(&changed, &left);
            let short = Proc::PBag(bag([(token("z"), 1)]));
            let long = Proc::PBag(bag([(token("a"), 2)]));
            assert_eq!(short.cmp(&long), Ordering::Less, "stored total precedes key order");
            exercise(&short, &long);
            exercise(&long, &short);
            exercise(&Bag::#bag_literal(bag([(token("a"), 3)])),
                &Bag::#bag_literal(bag([(token("a"), 3)])));
            exercise(&Proc::PBag(bag([(token("a"), usize::MAX)])),
                &Proc::PBag(bag([(token("a"), usize::MAX)])));
            exercise(&Proc::PBag(bag([(token("a"), usize::MAX)])),
                &Proc::PBag(bag([(token("b"), usize::MAX)])));

            let mut sparse = bag((0..64).map(|id| (token(&id.to_string()), 1)));
            let history = sparse.historical_capacity();
            for id in 0..60 { assert!(sparse.remove(&token(&id.to_string()))); }
            assert_eq!(sparse.historical_capacity(), history);
            assert!(history > sparse.distinct_len());
            let dense = bag((60..64).map(|id| (token(&id.to_string()), 1)));
            exercise(&Proc::PBag(sparse), &Proc::PBag(dense));

            let transported = |total, count| {
                let source = bag([(token("source"), total)]);
                Proc::PBag(source.rebuild_binding_entries([(token("a"), count)]))
            };
            exercise(&transported(7, 5), &transported(7, 6));
            exercise(&transported(7, 5), &transported(8, 5));
            exercise(&transported(7, 5), &transported(7, 5));
            let nested = |value: &str| Proc::PBag(bag([
                (map_proc(map([(Proc::PBag(bag([(token("key"), 2)])),
                    Proc::PBag(bag([(token(value), 3)])))])), 2),
                (token("other"), 1),
            ]));
            exercise(&nested("a"), &nested("a"));
            exercise(&nested("a"), &nested("b"));
            let scoped = |value| Proc::PMulti(Vec::new(),
                Scope::from_parts_unsafe(Vec::new(), Arc::new(nested(value))));
            exercise(&scoped("a"), &scoped("a"));
            exercise(&scoped("a"), &scoped("b"));

            let predicate = |name: &str| Proc::PPredicate(mettail_runtime::BehavioralPred::RelationQuery {
                relation_name: name.into(), args: Vec::new(), negated: false,
            });
            refuse(&Proc::PBag(bag([(predicate("left"), 1)])),
                &Proc::PBag(bag([(predicate("right"), 1)])), "Proc", "PPredicate", None);
        }

        fn malformed_bag_cases() {
            let source = bag([(token("source"), 7)]);
            let zero = Proc::PBag(source.rebuild_binding_entries([(token("a"), 0)]));
            let overflow = Proc::PBag(source.rebuild_binding_entries([
                (token("a"), usize::MAX), (token("b"), 1),
            ]));
            let healthy = Proc::PBag(bag([(token("healthy"), 1)]));
            // Distinct operands avoid the permitted root-alias equality shortcut.
            // Unequal stored totals must not skip validation of either roster.
            for (bad, size_overflow) in [(&zero, false), (&overflow, true)] {
                for (left, right) in [(bad, &healthy), (&healthy, bad)] {
                    for ordering in [false, true] {
                        let mut trace = Vec::new();
                        let result = run(left, right, ordering, &mut |w,u| {
                            trace.push((w,u)); Ok::<_, usize>(())
                        });
                        match (size_overflow, result) {
                            (false, Err(NativeComparisonFailure::InvalidCollectionInput(_))) => {},
                            (true, Err(NativeComparisonFailure::Admission(BindingFailure::SizeOverflow))) => {},
                            other => panic!("named malformed Bag refusal: {other:?}"),
                        }
                        for stop in 1..=trace.len() {
                            let mut seen = Vec::new();
                            let result = run(left, right, ordering, &mut |w,u| {
                                seen.push((w,u)); if seen.len() == stop { Err(stop) } else { Ok(()) }
                            });
                            assert!(matches!(result, Err(NativeComparisonFailure::Admission(
                                BindingFailure::Reservation(n))) if n == stop));
                            assert_eq!(seen, trace[..stop]);
                        }
                    }
                }
            }
            match (&zero, &overflow) {
                (Proc::PBag(zero), Proc::PBag(overflow)) => {
                    assert_eq!(zero.len(), 7);
                    assert_eq!(zero.iter().next().expect("retained zero record").1, 0);
                    assert_eq!(overflow.len(), 7);
                    assert_eq!(overflow.count(&token("a")), usize::MAX);
                    assert_eq!(overflow.count(&token("b")), 1);
                },
                _ => panic!("original Bag constructors preserved"),
            }
        }

        fn map_cases() {
            let empty = map([]);
            exercise(&empty, &empty);
            exercise(&empty, &map([]));
            let singleton = map([(token("a"), token("value"))]);
            exercise(&empty, &singleton);
            exercise(&singleton, &empty);
            let left = map([(token("z"), token("last")), (token("a"), token("first")), (token("m"), token("middle"))]);
            let permuted = map([(token("m"), token("middle")), (token("z"), token("last")), (token("a"), token("first"))]);
            assert!(left == permuted);
            assert_eq!(left.cmp(&permuted), Ordering::Equal);
            exercise(&left, &permuted);
            for changed in [
                map([(token("a"), token("first")), (token("n"), token("middle")), (token("z"), token("last"))]),
                map([(token("m"), token("middle")), (token("z"), token("last")), (token("a"), token("changed first"))]),
                map([(token("z"), token("changed last")), (token("a"), token("first")), (token("m"), token("middle"))]),
            ] {
                exercise(&left, &changed);
                exercise(&changed, &left);
            }
            let nested = || map_proc(map([(token("inner"), token("a"))]));
            exercise(&map([(token("outer"), nested())]), &map([(token("outer"), nested())]));
            exercise(&map([(token("outer"), nested())]),
                &map([(token("outer"), map_proc(map([(token("inner"), token("b"))])))]));

            // Inner nonEqual key comparisons belong to the outer sorting
            // continuation; they must never be published as the root answer.
            let nested_key = |value: &str| map_proc(map([(token("inner"), token(value))]));
            let left = map([(nested_key("z"), token("Z")), (nested_key("a"), token("A"))]);
            let right = map([(nested_key("a"), token("A")), (nested_key("z"), token("Z"))]);
            assert!(left == right);
            assert_eq!(left.cmp(&right), Ordering::Equal);
            exercise(&left, &right);
            exercise(&right, &left);
            let changed = map([(nested_key("a"), token("A")), (nested_key("z"), token("different"))]);
            exercise(&left, &changed);
        }

        fn map_owner(left: &mettail_runtime::HashMapLit<Proc, Proc>,
            right: &mettail_runtime::HashMapLit<Proc, Proc>) -> mettail_runtime::CheckedCollectionCmpPda {
            let mut reserve = |_,_| Ok::<_, usize>(());
            let left = left.try_comparison_roster(&mut reserve).expect("left fixture roster");
            let right = right.try_comparison_roster(&mut reserve).expect("right fixture roster");
            mettail_runtime::CheckedCollectionCmpPda::try_new(Ordering::Equal, left, right, &mut reserve)
                .expect("fixture collection owner")
        }

        fn paid_cmp_stack() -> Vec<CheckedCmpTask<usize>> {
            mettail_runtime::reserve_binding_parts(2, 1, 0, &mut |_,_| Ok::<_, usize>(()))
                .expect("fixture stack header");
            Vec::new()
        }

        fn map_owner_is_pushed_before_its_requested_child() {
            let mut left = mettail_runtime::HashMapLit::new();
            let mut right = mettail_runtime::HashMapLit::new();
            left.insert(token("a"), token("left value"));
            right.insert(token("b"), token("right value"));
            let mut stack = paid_cmp_stack();
            let mut trace = Vec::new();
            assert_eq!(checked_cmp_resume_collection_proc(&mut stack, map_owner(&left, &right),
                None, &mut |w,u| { trace.push((w,u)); Ok::<_, usize>(()) }), Ok(None));
            assert_eq!(&trace[trace.len()-2..], &[(2,4), (2,4)]);
            assert_eq!(stack.len(), 2);
            assert!(matches!(&stack[0], CheckedCmpTask::ResumeCollection(..)));
            let (left_key, _) = left.iter().next().expect("left source key");
            let (right_key, _) = right.iter().next().expect("right source key");
            match &stack[1] {
                CheckedCmpTask::CmpProc(l,r) => {
                    assert_eq!(*l, left_key as *const Proc);
                    assert_eq!(*r, right_key as *const Proc);
                }
                _ => panic!("requested typed child must be above its owner"),
            }
            drop(stack);
            for stop in [trace.len()-1, trace.len()] {
                let mut stack = paid_cmp_stack();
                let mut seen = Vec::new();
                let result = checked_cmp_resume_collection_proc(&mut stack, map_owner(&left, &right),
                    None, &mut |w,u| {
                        seen.push((w,u)); if seen.len() == stop { Err(stop) } else { Ok(()) }
                    });
                assert!(matches!(result, Err(NativeComparisonFailure::Admission(
                    BindingFailure::Reservation(n))) if n == stop));
                assert_eq!(seen, trace[..stop]);
                if stop == trace.len()-1 {
                    assert!(stack.is_empty(), "refused owner shell publishes neither task");
                } else {
                    assert_eq!(stack.len(), 1);
                    assert!(matches!(&stack[0], CheckedCmpTask::ResumeCollection(..)),
                        "child-shell refusal leaves only the already-paid owning continuation");
                }
                // Public error return drops its local stack. This disposes
                // only flat prepaid records and owners, never borrowed keys.
                drop(stack);
                assert_eq!(seen, trace[..stop], "cleanup performs no extra reservation");
            }
            assert_eq!(left.iter().count(), 1);
            assert_eq!(right.iter().count(), 1);
        }

        fn compare_original_proc_child(stack: &mut Vec<CheckedCmpTask<usize>>,
            expected_left: &Proc, expected_right: &Proc) -> Ordering {
            match stack.pop().expect("original requested child") {
                CheckedCmpTask::CmpProc(left, right) => {
                    assert_eq!(left, expected_left as *const Proc);
                    assert_eq!(right, expected_right as *const Proc);
                    checked_cmp_handle_proc(stack, left, right, &mut |_,_| Ok::<_, usize>(()))
                        .expect("actual generated child handler")
                },
                _ => panic!("request must dispatch the original typed Proc pair"),
            }
        }

        fn resume_original_proc_owner(stack: &mut Vec<CheckedCmpTask<usize>>,
            answer: Ordering) -> Option<Ordering> {
            match stack.pop().expect("original retained owner") {
                CheckedCmpTask::ResumeCollection(machine, resume) => {
                    assert!(std::ptr::fn_addr_eq(resume,
                        checked_cmp_resume_collection_proc::<usize> as CheckedCollectionCmpResume<usize>));
                    resume(stack, machine, Some(answer), &mut |_,_| Ok::<_, usize>(()))
                        .expect("actual retained callback")
                },
                _ => panic!("child result must return to its original owning continuation"),
            }
        }

        fn secondary_dispatch_preserves_the_distinct_lower_parked_owner() {
            let nested_key = || map_proc(map([(token("inner key"), token("inner value"))]));
            let mut left = mettail_runtime::HashMapLit::new();
            let mut right = mettail_runtime::HashMapLit::new();
            left.insert(nested_key(), token("a outer value"));
            right.insert(nested_key(), token("z outer value"));
            let (left_key, left_value) = left.iter().next().expect("original left outer pair");
            let (right_key, right_value) = right.iter().next().expect("original right outer pair");
            let (left_head, left_map) = match left_key {
                Proc::ApplyMap(head, map) => (head.as_ref(), map.as_ref()),
                _ => panic!("fixture original nested Map key"),
            };
            let (right_head, right_map) = match right_key {
                Proc::ApplyMap(head, map) => (head.as_ref(), map.as_ref()),
                _ => panic!("fixture original nested Map key"),
            };
            let left_inner = match left_map {
                Map::#map_literal(entries) => entries.iter().next().expect("left inner pair"),
                _ => panic!("fixture original Map literal"),
            };
            let right_inner = match right_map {
                Map::#map_literal(entries) => entries.iter().next().expect("right inner pair"),
                _ => panic!("fixture original Map literal"),
            };
            let mut stack = paid_cmp_stack();
            assert_eq!(checked_cmp_resume_collection_proc(&mut stack, map_owner(&left, &right),
                None, &mut |_,_| Ok::<_, usize>(())), Ok(None));
            assert_eq!(stack.len(), 2);

            // Run the real generated constructor handlers. Their original
            // children create the inner Map Start above the parked outer owner.
            assert_eq!(compare_original_proc_child(&mut stack, left_key, right_key), Ordering::Equal);
            assert_eq!(stack.len(), 3);
            assert_eq!(compare_original_proc_child(&mut stack, left_head, right_head), Ordering::Equal);
            match stack.pop().expect("original Map child") {
                CheckedCmpTask::CmpMap(lhs, rhs) => {
                    assert_eq!(lhs, left_map as *const Map);
                    assert_eq!(rhs, right_map as *const Map);
                    assert_eq!(checked_cmp_handle_map(&mut stack, lhs, rhs,
                        &mut |_,_| Ok::<_, usize>(())), Ok(Ordering::Equal));
                },
                _ => panic!("ApplyMap must retain its original typed Map child"),
            }
            match stack.pop().expect("inner Map Start") {
                CheckedCmpTask::StartCollection(machine, resume) => {
                    assert!(std::ptr::fn_addr_eq(resume,
                        checked_cmp_resume_collection_proc::<usize> as CheckedCollectionCmpResume<usize>));
                    assert_eq!(resume(&mut stack, machine, None,
                        &mut |_,_| Ok::<_, usize>(())), Ok(None));
                },
                _ => panic!("generated Map factory must produce its original owning Start"),
            }
            assert_eq!(stack.len(), 3);
            assert!(matches!(&stack[0], CheckedCmpTask::ResumeCollection(..)));
            assert!(matches!(&stack[1], CheckedCmpTask::ResumeCollection(..)));
            assert_eq!(compare_original_proc_child(&mut stack, left_inner.0, right_inner.0), Ordering::Equal);
            assert_eq!(resume_original_proc_owner(&mut stack, Ordering::Equal), None);
            assert_eq!(stack.len(), 3);
            // Primary Equal must request the original values, not reissue keys.
            assert_eq!(compare_original_proc_child(&mut stack, left_inner.1, right_inner.1), Ordering::Equal);
            let completed_child = resume_original_proc_owner(&mut stack, Ordering::Equal)
                .expect("inner Map completes at its own return boundary");
            assert_eq!(completed_child, Ordering::Equal);
            assert_eq!(stack.len(), 1, "only the distinct original outer owner remains");

            // Its retained primary request must still name the OUTER pair.
            // Feeding the actual completed child answer reveals that pair's
            // original secondary pointers, checking this did not restart or
            // substitute the inner machine for the parked continuation.
            assert_eq!(resume_original_proc_owner(&mut stack, completed_child), None);
            assert_eq!(stack.len(), 2);
            let answer = compare_original_proc_child(&mut stack, left_value, right_value);
            assert_eq!(answer, Ordering::Less);
            assert_eq!(resume_original_proc_owner(&mut stack, answer), Some(Ordering::Less));
            assert!(stack.is_empty());
            assert_eq!((left.iter().count(), right.iter().count()), (1, 1));
        }

        fn unstarted_map_is_discarded_during_outer_delivery() {
            // These keys would refuse checked comparison if an unstarted
            // deferred collection were incorrectly resumed during delivery.
            let predicate = |name: &str| Proc::PPredicate(mettail_runtime::BehavioralPred::RelationQuery {
                relation_name: name.into(), args: Vec::new(), negated: false,
            });
            let mut left = mettail_runtime::HashMapLit::new();
            let mut right = mettail_runtime::HashMapLit::new();
            left.insert(predicate("left unstarted"), Proc::PZero);
            right.insert(predicate("right unstarted"), Proc::PZero);
            let prepared = || {
                let owner = map_owner(&left, &right);
                let mut stack = paid_cmp_stack();
                mettail_runtime::reserve_binding_parts(2, 1, 0, &mut |_,_| Ok::<_, usize>(()))
                    .expect("fixture Start shell");
                stack.push(CheckedCmpTask::StartCollection(owner, checked_cmp_resume_collection_proc));
                mettail_runtime::reserve_binding_parts(2, 1, 0, &mut |_,_| Ok::<_, usize>(()))
                    .expect("fixture verdict shell");
                stack.push(CheckedCmpTask::Verdict(Ordering::Less));
                stack
            };
            let mut trace = Vec::new();
            let mut stack = prepared();
            assert_eq!(checked_cmp_iterative(&mut stack, &mut |w,u| {
                trace.push((w,u)); Ok::<_, usize>(())
            }), Ok(Ordering::Less));
            assert!(stack.is_empty());
            assert!(!trace.is_empty());
            assert!(trace.iter().all(|charge| *charge == (1,0)),
                "discarding an unstarted owner is routing only, with no resumption or child task");
            for stop in 1..=trace.len() {
                let mut stack = prepared();
                let mut seen = Vec::new();
                let result = checked_cmp_iterative(&mut stack, &mut |w,u| {
                    seen.push((w,u)); if seen.len() == stop { Err(stop) } else { Ok(()) }
                });
                assert!(matches!(result, Err(NativeComparisonFailure::Admission(
                    BindingFailure::Reservation(n))) if n == stop),
                    "terminal delivery refusal must withhold the known Less verdict");
                assert_eq!(seen, trace[..stop]);
                drop(stack);
                assert_eq!(seen, trace[..stop]);
            }
            assert_eq!(left.iter().count(), 1);
            assert_eq!(right.iter().count(), 1);
        }

        fn deep_map(bottom: &str) -> Proc {
            let mut value = token(bottom);
            for _ in 0..20_000 {
                value = map_proc(map([(token("key"), value)]));
            }
            value
        }

        fn deep_bag(bottom: &str) -> Proc {
            let mut value = token(bottom);
            for _ in 0..20_000 { value = Proc::PBag(bag([(value, 1)])); }
            value
        }

        fn deep(bottom: &str) -> Proc {
            let mut value = Proc::PToken(bottom.into());
            for depth in 0..20_000 {
                value = if depth % 2 == 0 { Proc::PVector(vec![value]) }
                else { Proc::PMulti(Vec::new(), Scope::from_parts_unsafe(Vec::new(), Arc::new(value))) };
            }
            value
        }

        fn deep_small_stack() {
            std::thread::Builder::new().stack_size(256 * 1024).spawn(|| {
                for build in [deep as fn(&str) -> Proc, deep_map as fn(&str) -> Proc,
                    deep_bag as fn(&str) -> Proc] {
                // Independent trees prevent Arc aliasing from hiding traversal.
                let left = build("a"); let equal = build("a"); let different = build("b");
                for right in [&equal, &different] {
                    for ordering in [false, true] {
                        let expected = native(&left, right, ordering);
                        let mut calls = 0usize; let mut total = (0usize,0usize);
                        assert_eq!(run(&left, right, ordering, &mut |w,u| {
                            calls += 1;
                            total.0 = total.0.checked_add(w).expect("deep work fits");
                            total.1 = total.1.checked_add(u).expect("deep units fit");
                            Ok::<_, usize>(())
                        }), Ok(expected));
                        assert!(calls > 20_000);
                        for stop in [1, calls/2, calls] {
                            let mut seen = 0usize;
                            let result = run(&left, right, ordering, &mut |_,_| {
                                seen += 1; if seen == stop { Err(stop) } else { Ok(()) }
                            });
                            assert!(matches!(result, Err(NativeComparisonFailure::Admission(
                                BindingFailure::Reservation(n))) if n == stop));
                            assert_eq!(seen, stop);
                        }
                        for limit in [(total.0-1,total.1), (total.0,total.1-1), total] {
                            let mut used = (0usize,0usize);
                            let result = run(&left, right, ordering, &mut |w,u| {
                                if w > limit.0-used.0 || u > limit.1-used.1 { return Err(0usize); }
                                used.0 += w; used.1 += u; Ok(())
                            });
                            if limit == total { assert_eq!(result, Ok(expected)); assert_eq!(used, total); }
                            else { assert!(matches!(result, Err(NativeComparisonFailure::Admission(
                                BindingFailure::Reservation(0))))); }
                        }
                    }
                }
                drop((left, equal, different));
                }
            }).expect("spawn checked comparison worker").join().expect("20k small-stack comparison");
        }

        fn main() {
            assert!(mettail_runtime::CHECKED_NATIVE_COMPARISON_PROFILE_AVAILABLE);
            exercise(&Proc::PZero, &Proc::PZero);
            exercise(&Proc::PZero, &Proc::PToken("different constructor".into()));
            for (left,right) in [(i64::MIN,i64::MAX), (0,0), (7,-7)] {
                exercise(&Int::#int_literal(left), &Int::#int_literal(right));
            }
            for left in [false,true] { for right in [false,true] {
                exercise(&Bool::#bool_literal(left), &Bool::#bool_literal(right));
            }}
            for (left,right) in [("",""), ("a","ab"), ("ab","ac"), ("λ","μ")] {
                exercise(&Text::#text_literal(left.into()), &Text::#text_literal(right.into()));
            }
            let free = FreeVar::fresh_named("diagnostic identity hint");
            let variable = Proc::#proc_var(OrdVar(Var::Free(free.clone())));
            exercise(&variable, &variable.clone());
            exercise(&variable, &Proc::#proc_var(OrdVar(Var::Free(FreeVar::fresh_named("other")))));
            let bound = Proc::#proc_var(OrdVar(Var::Bound(mettail_runtime::BoundVar {
                scope: moniker::ScopeOffset(3), binder: moniker::BinderIndex(2),
                pretty_name: Some("ignored".into()),
            })));
            exercise(&variable, &bound); exercise(&bound, &bound.clone());
            let child = Arc::new(Proc::PToken("child".into()));
            let guest = guest(free.clone());
            let values = vec![
                Proc::PScalars(Arc::new(Int::#int_literal(-7)), Arc::new(Bool::#bool_literal(true)),
                    Arc::new(Text::#text_literal("text".into()))),
                Proc::PPair(child.clone(), child.clone()),
                Proc::PGuest(guest.clone()),
                Proc::PMixed("prefix".into(), child.clone(), guest.clone(), "suffix".into()),
                Proc::POptionalVec(None), Proc::POptionalVec(Some(Vec::new())),
                Proc::POptionalVec(Some(vec![Proc::PZero, Proc::PToken("last".into())])),
                Proc::PSingle(Arc::new(Proc::PZero),
                    Scope::from_parts_unsafe(Binder(free.clone()), child.clone())),
                Proc::PMulti(vec![Proc::PZero],
                    Scope::from_parts_unsafe(vec![Binder(free.clone())], child.clone())),
            ];
            for value in &values { exercise(value, value); exercise(value, &value.clone()); }
            exercise(&Proc::POptionalVec(None), &Proc::POptionalVec(Some(Vec::new())));
            exercise(&Proc::POptionalVec(Some(vec![Proc::PZero])),
                &Proc::POptionalVec(Some(vec![Proc::PToken("different".into())])));
            exercise(&Proc::PMixed("prefix".into(), Arc::new(Proc::PToken("a".into())),
                    guest.clone(), "z".into()),
                &Proc::PMixed("prefix".into(), Arc::new(Proc::PToken("b".into())),
                    guest.clone(), "a".into()));
            exercise(&Proc::PSingle(Arc::new(Proc::PZero),
                    Scope::from_parts_unsafe(Binder(free.clone()), child.clone())),
                &Proc::PSingle(Arc::new(Proc::PZero),
                    Scope::from_parts_unsafe(Binder(FreeVar::fresh_named("other")), child.clone())));
            exercise(&Proc::PMulti(Vec::new(), Scope::from_parts_unsafe(Vec::new(), child.clone())),
                &Proc::PMulti(Vec::new(), Scope::from_parts_unsafe(vec![Binder(free)], child.clone())));
            for width in [0,1,3] {
                let left = Proc::PVector((0..width).map(|i| Proc::PToken(i.to_string())).collect());
                exercise(&left, &left.clone());
                exercise(&left, &Proc::PVector(Vec::new()));
            }
            exercise(&List::#list_literal(vec![Proc::PZero, Proc::PToken("a".into())]),
                &List::#list_literal(vec![Proc::PZero, Proc::PToken("b".into())]));

            let predicate = Proc::PPredicate(mettail_runtime::BehavioralPred::RelationQuery {
                relation_name: "unadmitted".into(), args: Vec::new(), negated: false,
            });
            refuse(&predicate, &predicate, "Proc", "PPredicate", Some(5));
            refuse(&predicate, &Proc::PZero, "Proc", "PPredicate", Some(5));
            refuse(&Proc::PZero, &predicate, "Proc", "PPredicate", Some(6));
            let predicate = Arc::new(predicate);
            refuse(&Proc::PUnary(predicate.clone()), &Proc::PUnary(predicate),
                "Proc", "PPredicate", None);
            let optional = Proc::POptional("prefix".into(), None, None, None);
            refuse(&optional, &optional, "Proc", "POptional", Some(5));
            bag_cases();
            malformed_bag_cases();
            map_cases();
            map_owner_is_pushed_before_its_requested_child();
            secondary_dispatch_preserves_the_distinct_lower_parked_owner();
            unstarted_map_is_discarded_during_outer_delivery();
            let set = Set::#set_literal(mettail_runtime::HashSetLit::new());
            refuse(&set, &set, "Set", stringify!(#set_literal), Some(5));
            let pathmap = Pathmap::#pathmap_literal(mettail_runtime::PathMapLit::new());
            refuse(&pathmap, &pathmap, "Pathmap", stringify!(#pathmap_literal), Some(5));
            let bytes = Bytes::#bytes_literal(vec![0,1,255]);
            refuse(&bytes, &bytes, "Bytes", stringify!(#bytes_literal), Some(5));
            terminal_drain_refusal_is_not_a_completed_ordering();
            deep_small_stack();
            println!("checked generated Eq/Ord native parity, all small cutpoints, exact limits, local unsupported gates and 20k small-stack traversal verified");
        }
    };
    syn::parse2::<syn::File>(fixture.clone()).expect("actual checked comparison fixture syntax");
    if std::env::var_os("METTAIL_CAPTURE_CHECKED_CMP").is_some() {
        let directory = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../target/verification/cmp-emitter");
        std::fs::create_dir_all(&directory).expect("create checked comparison fixture directory");
        std::fs::write(directory.join("checked.rs"), fixture.to_string())
            .expect("capture actual checked comparison fixture");
    }
}
