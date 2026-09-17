use super::*;
use crate::gen::term_ops::iterative_hash::checked_tests::{fixture_language, literal_label};

#[test]
fn capture_original_layout_contribution_worklist() {
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
    let inspection = contribution::generate_comparison_contribution_inspection(&language);
    let map_literal = literal_label(&language, "Map");
    let source = inspection.to_string();
    for forbidden in ["try_native_", "thread_local!", "sort_by", "try_resume", "Ordering ::"] {
        assert!(!source.contains(forbidden), "inspection executes {forbidden}");
    }
    let fixture = quote! {
        #![allow(dead_code, unused_variables, unreachable_patterns, non_snake_case)]
        use std::cmp::Ordering;
        use std::hash::{Hash, Hasher};
        use std::sync::Arc;
        use mettail_runtime::{Binder, BindingFailure, FltNode, FreeVar,
            NativeComparisonFailure, OrdVar, Scope, Var};
        use mettail_runtime::binding_receipt::BindingCharge;
        #(#enum_types)*
        #ordinary_clone #ordinary_cmp #ordinary_hash #ordinary_drop #inspection

        fn inspect(left: &Proc, right: &Proc, mode: InspectCmpContributionMode) -> BindingCharge {
            inspect_comparison_contributions_proc(left, right, mode, &mut |_, _| Ok::<_, ()>(()))
                .expect("original-layout metadata inspection")
        }
        fn exercise_scaled_root(left: &Proc, right: &Proc, mode: InspectCmpContributionMode) {
            let once = inspect(left, right, mode);
            for factor in [0, 1, 3] {
                let result = inspect_cmp_contribution_worklist(
                    InspectCmpContributionTask::CmpProc(left, right), mode, factor,
                    &mut |_, _| Ok::<_, ()>(()),
                ).expect("scaled root inspection");
                assert_eq!(result, once.checked_scale(factor).expect("scaled complete allowance"));
            }
        }
        fn exercise_cuts(left: &Proc, right: &Proc, mode: InspectCmpContributionMode) {
            let mut trace = Vec::new();
            let expected = inspect_comparison_contributions_proc(left, right, mode, &mut |w, u| {
                trace.push((w, u)); Ok::<_, usize>(())
            }).expect("complete inspection trace");
            for limit in 0..trace.len() {
                let mut prefix = Vec::new();
                let result = inspect_comparison_contributions_proc(left, right, mode, &mut |w, u| {
                    prefix.push((w, u));
                    if prefix.len() > limit { Err(limit) } else { Ok(()) }
                });
                assert_eq!(result, Err(NativeComparisonFailure::Admission(
                    BindingFailure::Reservation(limit))));
                assert_eq!(prefix, trace[..=limit]);
            }
            assert_eq!(expected, inspect(left, right, mode));
        }
        fn bag(entries: impl IntoIterator<Item=(Proc, usize)>) -> Proc {
            let mut values = mettail_runtime::HashBag::new();
            for (term, count) in entries { values.insert_n(term, count); }
            Proc::PBag(values)
        }
        fn exercise_collection_components() {
            use InspectCmpContributionMode::{Eq, Ord};
            for n in 0usize..=3 {
                for m in 0usize..=3 {
                    let width = n + m;
                    let pairs = n * n.saturating_sub(1) + m * m.saturating_sub(1);
                    for mode in [Eq, Ord] {
                        let (extra_work, extra_records) = match mode { Eq => (20, 2), Ord => (0, 0) };
                        for factor in [0, 1, 3] {
                            for (source, work, records) in [
                                (InspectCmpCollectionSource::Map,
                                    41 * pairs + 40 * width + 67 + extra_work,
                                    2 * pairs + 4 * width + 6 + extra_records),
                                (InspectCmpCollectionSource::Bag { left_scan: 19, right_scan: 37 },
                                    32 * pairs + 31 * width + 65 + 19 + 37 + extra_work,
                                    pairs + 3 * width + 6 + extra_records),
                            ] {
                                for limit in 0usize..=9 {
                                    let mut state = BindingCharge::ZERO;
                                    let mut trace = Vec::new();
                                    let result = inspect_cmp_add_collection_overhead(
                                        &mut state, n, m, source, mode, factor, &mut |w, u| {
                                            trace.push((w, u));
                                            if trace.len() > limit { Err(limit) } else { Ok(()) }
                                        },
                                    );
                                    assert_eq!(trace, vec![(1, 0); (limit + 1).min(9)]);
                                    if limit < 9 {
                                        assert_eq!(result, Err(NativeComparisonFailure::Admission(
                                            BindingFailure::Reservation(limit))));
                                    } else {
                                        assert_eq!(result, Ok(()));
                                        assert_eq!(state, BindingCharge::new(work * factor, records * factor, 0)
                                            .expect("component sum fits"));
                                    }
                                }
                            }
                        }
                    }
                }
            }
            for (n, m, source, factor) in [
                (usize::MAX, 1, InspectCmpCollectionSource::Map, 0),
                (usize::MAX, 0, InspectCmpCollectionSource::Map, 1),
                (0, 0, InspectCmpCollectionSource::Bag { left_scan: usize::MAX, right_scan: 0 }, 0),
                (0, 0, InspectCmpCollectionSource::Map, usize::MAX),
            ] {
                let mut state = BindingCharge::ZERO;
                let result = inspect_cmp_add_collection_overhead(
                    &mut state, n, m, source, Eq, factor, &mut |_, _| Ok::<_, ()>(()),
                );
                assert_eq!(result, Err(NativeComparisonFailure::Admission(BindingFailure::SizeOverflow)));
                let mut calls = 0;
                let result = inspect_cmp_add_collection_overhead(
                    &mut state, n, m, source, Eq, factor, &mut |w, u| {
                        calls += 1; assert_eq!((w, u), (1, 0)); Err::<(), _>(17u8)
                    },
                );
                assert_eq!(result, Err(NativeComparisonFailure::Admission(BindingFailure::Reservation(17))));
                assert_eq!(calls, 1, "refusal precedes even invalid arithmetic");
            }
        }
        fn exercise_original_pair_cursor() {
            let keys = [Proc::PZero, Proc::PUnary(Arc::new(Proc::PZero)), Proc::PVector(vec![])];
            let values = [Proc::PVector(vec![]), Proc::PZero, Proc::PUnary(Arc::new(Proc::PZero))];
            let left = [(&keys[0], &values[0]), (&keys[0], &values[1])];
            let right = [(&keys[2], &values[2]), (&keys[1], &values[0]), (&keys[2], &values[2])];
            let constructor: fn(*const (), *const ()) -> InspectCmpContributionTask =
                |left, right| InspectCmpContributionTask::CmpProc(left.cast(), right.cast());
            for (n, m) in [(2usize, 3usize), (0, 3), (1, 1), (0, 0), (2, 0)] {
                let mut reserve = |_, _| Ok::<_, ()>(());
                let mut left_roster = mettail_runtime::CheckedCmpRoster::try_with_capacity(n, &mut reserve)
                    .expect("paid left roster");
                let mut right_roster = mettail_runtime::CheckedCmpRoster::try_with_capacity(m, &mut reserve)
                    .expect("paid right roster");
                for &(key, value) in &left[..n] {
                    left_roster.try_push_pair(key, value, &mut reserve).expect("left original pair");
                }
                for &(key, value) in &right[..m] {
                    right_roster.try_push_pair(key, value, &mut reserve).expect("right original pair");
                }
                mettail_runtime::reserve_binding_parts(2, 1, 0, &mut reserve).expect("stack header");
                let mut stack = Vec::new();
                let mut state = BindingCharge::ZERO;
                inspect_cmp_schedule_collection(&mut stack, &mut state, left_roster, right_roster,
                    InspectCmpCollectionSource::Map,
                    constructor, Some(constructor), InspectCmpContributionMode::Eq, 3, &mut reserve)
                    .expect("schedule original pair families");
                assert_eq!(stack.len(), 1);
                let frame = stack.pop().expect("one cursor frame");
                assert!(matches!(frame.mode, InspectCmpContributionMode::Eq));
                assert_eq!(frame.factor, 3);
                let InspectCmpContributionTask::Collection(mut cursor) = frame.task
                    else { panic!("scheduled task is not the original cursor") };
                assert_eq!(cursor.widths, [n, m]);
                let factors = [3 * n * n.saturating_sub(1), 3 * m * m.saturating_sub(1), 3 * (n + m)];
                assert_eq!(cursor.factors, factors);
                if (n, m) == (2, 3) { assert_eq!(factors, [6, 18, 15]); }
                let mut expected = Vec::new();
                for (lhs, rhs, factor) in [
                    (&left[..n], &left[..n], factors[0]),
                    (&right[..m], &right[..m], factors[1]),
                    (&left[..n], &right[..m], factors[2]),
                ] {
                    if factor == 0 { continue; }
                    for &(lk, lv) in lhs {
                        for &(rk, rv) in rhs {
                            expected.push(((lk as *const Proc).cast::<()>(), (rk as *const Proc).cast::<()>(),
                                (lv as *const Proc).cast::<()>(), (rv as *const Proc).cast::<()>(), factor));
                        }
                    }
                }
                let mut observed = Vec::new();
                while let Some(pair) = cursor.try_next(&mut reserve).expect("next original directed occurrence") {
                    let (lv, rv) = pair.secondary.expect("both original secondary operands");
                    observed.push((pair.primary.0, pair.primary.1, lv, rv, pair.factor));
                    if let Some(family) = cursor.family {
                        let (rows, cols, factor) = cursor.dimensions(family);
                        if rows > 0 && cols > 0 && factor > 0 {
                            assert!(cursor.row < rows && cursor.col < cols);
                        }
                    }
                }
                assert_eq!(observed, expected, "original row-major occurrences for widths {n}/{m}");
                if (n, m) == (2, 3) {
                    assert_eq!(observed.len(), 4 + 9 + 6);
                    assert_eq!(observed[4], observed[6], "aliased original RR occurrences are not deduplicated");
                    assert_eq!(observed[0].0, observed[1].0);
                    assert_eq!(observed[0].1, observed[1].1);
                    assert_ne!(observed[0].3, observed[1].3, "secondary identity stays paired with its occurrence");
                }
                assert!(cursor.family.is_none());
                assert!(cursor.try_next(&mut reserve).expect("stable terminal cursor").is_none());
            }
        }
        fn exercise_native_sort_cursor() {
            let keys = [Proc::PZero, Proc::PUnary(Arc::new(Proc::PZero))];
            let values = [Proc::PVector(vec![]), Proc::PZero, Proc::PUnary(Arc::new(Proc::PZero))];
            let entries = [(&keys[0], &values[0]), (&keys[1], &values[2]), (&keys[0], &values[1])];
            let constructor: fn(*const (), *const ()) -> InspectCmpContributionTask =
                |left, right| InspectCmpContributionTask::CmpProc(left.cast(), right.cast());
            for width in 0usize..=3 {
                let build = |reserve: &mut dyn FnMut(usize, usize) -> Result<(), usize>| {
                    let mut forwarded = |w, u| reserve(w, u);
                    let mut original = mettail_runtime::CheckedCmpRoster::try_with_capacity(width, &mut forwarded)?;
                    for &(key, value) in &entries[..width] {
                        original.try_push_pair(key, value, &mut forwarded)?;
                    }
                    InspectCmpPairCursor::try_for_map_hash(original, constructor, constructor, &mut forwarded)
                };
                let mut trace = Vec::new();
                let mut cursor = build(&mut |w, u| { trace.push((w, u)); Ok(()) })
                    .expect("original native-sort roster");
                let factor = if width < 2 { 0 } else { 10 * width * width + 32 * width };
                assert_eq!(cursor.widths, [width, 0]);
                assert_eq!(cursor.factors, [factor, 0, 0]);
                let mut observed = Vec::new();
                while let Some(pair) = cursor.try_next(&mut |_, _| Ok::<_, ()>(())).expect("original pair") {
                    observed.push((pair.primary, pair.secondary, pair.factor));
                }
                let mut expected = Vec::new();
                if width >= 2 {
                    for &(left_key, left_value) in &entries[..width] {
                        for &(right_key, right_value) in &entries[..width] {
                            expected.push(((left_key as *const Proc as *const (), right_key as *const Proc as *const ()),
                                Some((left_value as *const Proc as *const (), right_value as *const Proc as *const ())), factor));
                        }
                    }
                }
                assert_eq!(observed, expected, "only original directed LL occurrences");
                for limit in 0..trace.len() {
                    let mut prefix = Vec::new();
                    let result = build(&mut |w, u| {
                        prefix.push((w, u));
                        if prefix.len() > limit { Err(limit) } else { Ok(()) }
                    });
                    match result {
                        Err(NativeComparisonFailure::Admission(BindingFailure::Reservation(error))) =>
                            assert_eq!(error, limit),
                        _ => panic!("factory must stop at original reservation refusal"),
                    }
                    assert_eq!(prefix, trace[..=limit]);
                }
            }
        }
        fn main() {
            use InspectCmpContributionMode::{Eq, Ord};
            exercise_collection_components();
            exercise_original_pair_cursor();
            exercise_native_sort_cursor();
            let zero = Proc::PZero;
            assert_eq!(inspect(&zero, &zero, Eq), BindingCharge::new(25, 3, 0).expect("root"));
            // The fixed handler envelope includes IndexCmp on an Ord
            // variant mismatch, even though the recipe returns no verdict.
            let other_variant = Proc::PUnary(Arc::new(Proc::PZero));
            for mode in [Eq, Ord] {
                for (left, right) in [(&zero, &other_variant), (&other_variant, &zero)] {
                    assert_eq!(inspect(left, right, mode),
                        BindingCharge::new(25, 3, 0).expect("unequal variant envelope"));
                    exercise_cuts(left, right, mode);
                }
            }
            let shared = Arc::new(Proc::PZero);
            let pair = Proc::PPair(shared.clone(), shared.clone());
            assert_eq!(inspect(&pair, &pair, Eq), BindingCharge::new(47, 5, 0).expect("two occurrences"));
            // A mismatched vector ends its recipe, not the pending sibling job.
            let left = Proc::PPair(Arc::new(Proc::PUnary(shared.clone())), Arc::new(Proc::PVector(vec![])));
            let right = Proc::PPair(Arc::new(Proc::PUnary(shared)), Arc::new(Proc::PVector(vec![Proc::PZero])));
            assert_eq!(inspect(&left, &right, Eq), BindingCharge::new(61, 6, 0).expect("queued sibling"));
            for mode in [Eq, Ord] { exercise_cuts(&left, &right, mode); }
            for mode in [Eq, Ord] { exercise_scaled_root(&left, &right, mode); }
            let binder = FreeVar::fresh_named("x".to_owned());
            let single = Proc::PSingle(Arc::new(Proc::PZero),
                Scope::from_parts_unsafe(Binder(binder.clone()), Arc::new(Proc::PZero)));
            let multi = Proc::PMulti(vec![Proc::PZero],
                Scope::from_parts_unsafe(vec![Binder(binder)], Arc::new(Proc::PZero)));
            for mode in [Eq, Ord] {
                exercise_cuts(&single, &single, mode);
                exercise_cuts(&multi, &multi, mode);
            }
            // Compressed repetition counts must not become that many jobs.
            let one = bag([(Proc::PZero, 1)]);
            let repeated = bag([(Proc::PZero, usize::MAX)]);
            for mode in [Eq, Ord] {
                assert_eq!(inspect(&one, &one, mode), inspect(&repeated, &repeated, mode));
                exercise_cuts(&one, &one, mode);
            }
            let source = mettail_runtime::HashBag::<Proc>::new();
            let zero_count = Proc::PBag(source.rebuild_binding_entries([(Proc::PZero, 0)]));
            let overflowing_count = Proc::PBag(source.rebuild_binding_entries([
                (Proc::PZero, usize::MAX), (Proc::PUnary(Arc::new(Proc::PZero)), 1),
            ]));
            for mode in [Eq, Ord] {
                for invalid in [&zero_count, &overflowing_count] {
                    let result = inspect_comparison_contributions_proc(
                        invalid, &one, mode, &mut |_, _| Ok::<_, ()>(()),
                    );
                    assert!(matches!(result,
                        Err(NativeComparisonFailure::InvalidCollectionInput(_)) |
                        Err(NativeComparisonFailure::Admission(BindingFailure::SizeOverflow))));
                }
            }
            let mut entries = mettail_runtime::HashMapLit::new();
            entries.insert(Proc::PZero, Proc::PUnary(Arc::new(Proc::PZero)));
            let map = Proc::ApplyMap(Arc::new(Proc::PZero), Arc::new(Map::#map_literal(entries)));
            let nested = bag([(map, 2)]);
            for mode in [Eq, Ord] {
                exercise_cuts(&nested, &nested, mode);
                exercise_scaled_root(&nested, &nested, mode);
            }
            std::thread::Builder::new().stack_size(256 * 1024).spawn(|| {
                let mut value = Proc::PZero;
                for _ in 0..20_000 { value = Proc::PUnary(Arc::new(value)); }
                for mode in [Eq, Ord] {
                    let charge = inspect(&value, &value, mode);
                    assert_eq!(charge, BindingCharge::new(25 + 11 * 20_000, 3 + 20_000, 0)
                        .expect("iterative unary inventory"));
                }
            }).expect("small-stack worker").join().expect("stack-safe worklist and cleanup");
            println!("original-layout comparison contribution worklist preserves modes, jobs and cuts");
        }
    };
    syn::parse2::<syn::File>(fixture.clone()).expect("original-layout inspection fixture syntax");
    if std::env::var_os("METTAIL_CAPTURE_CHECKED_CMP").is_some() {
        let directory = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../target/verification/cmp-emitter");
        std::fs::create_dir_all(&directory).expect("create fixture directory");
        std::fs::write(directory.join("worklist-contributions.rs"), fixture.to_string())
            .expect("capture original-layout worklist");
    }
}
