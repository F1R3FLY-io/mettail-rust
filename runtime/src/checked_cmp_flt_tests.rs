//! Native comparison parity and paid metadata schedules for raw FLT carriers.
//! Fixture construction is outside admission; these tests do not validate templates.

use super::*;
use crate::{FltHole, FltHoleId, FltNode, FltSourceRange, FltTemplateBounds, FltTemplatePiece};
use std::sync::Arc;

fn empty_node() -> FltNode {
    FltNode {
        selector: OrdVar(Var::Free(crate::FreeVar::fresh_named("s".to_owned()))),
        selector_name: String::new(),
        category: String::new(),
        open_src: String::new(),
        body_src: String::new(),
        holes: Vec::new(),
        pieces: Vec::new(),
        close_src: String::new(),
        bounds: FltTemplateBounds::default(),
        position: 0,
    }
}

fn populated_node() -> FltNode {
    let mut node = empty_node();
    node.selector_name = "s".into();
    node.category = "Proc".into();
    node.open_src = "`".into();
    node.body_src = "x${h}".into();
    node.close_src = "`".into();
    node.holes.push(FltHole {
        id: FltHoleId(0),
        name: "h".into(),
        category: Some("Proc".into()),
        first_occurrence: FltSourceRange::new(1, 5),
    });
    node.pieces = vec![
        FltTemplatePiece::Text {
            text: "x".into(),
            range: FltSourceRange::new(0, 1),
        },
        FltTemplatePiece::Hole {
            id: FltHoleId(0),
            range: FltSourceRange::new(1, 5),
        },
    ];
    node
}

fn strings(node: &FltNode) -> [&String; 5] {
    [
        &node.selector_name,
        &node.category,
        &node.open_src,
        &node.body_src,
        &node.close_src,
    ]
}

// Independent transcription of the closed source table, not production cost
// helpers. Each pair contains equality and ordering work respectively.
fn string_cost(left: &str, right: &str) -> [usize; 2] {
    [
        6 + 2 * if left.len() == right.len() {
            left.len()
        } else {
            0
        },
        9 + 2 * left.len().min(right.len()),
    ]
}

fn hole_cost(left: &FltHole, right: &FltHole) -> [usize; 2] {
    let name = string_cost(&left.name, &right.name);
    let category = match (&left.category, &right.category) {
        (Some(left), Some(right)) => {
            let work = string_cost(left, right);
            [6 + work[0], 6 + work[1]]
        },
        _ => [5, 5],
    };
    [16 + name[0] + category[0], 16 + name[1] + category[1]]
}

fn piece_cost(left: &FltTemplatePiece, right: &FltTemplatePiece) -> [usize; 2] {
    match (left, right) {
        (FltTemplatePiece::Text { text: left, .. }, FltTemplatePiece::Text { text: right, .. }) => {
            let work = string_cost(left, right);
            [14 + work[0], 14 + work[1]]
        },
        (FltTemplatePiece::Hole { .. }, FltTemplatePiece::Hole { .. }) => [18, 18],
        _ => [5, 5],
    }
}

fn vector_cost<T>(
    left: &[T],
    right: &[T],
    cost: fn(&T, &T) -> [usize; 2],
) -> ([usize; 2], [usize; 2]) {
    let equal_width = left.len() == right.len();
    let mut work = [7, 11];
    for (left, right) in left.iter().zip(right) {
        let pair = cost(left, right);
        if equal_width {
            work[0] += 3 + pair[0];
        }
        work[1] += 4 + pair[1];
    }
    (
        work,
        [if equal_width { left.len() + 1 } else { 0 }, left.len().min(right.len()) + 1],
    )
}

fn expected(node: &FltNode, other: &FltNode) -> ([usize; 3], [usize; 3]) {
    let selector = match (&node.selector.0, &other.selector.0) {
        (Var::Free(_), Var::Free(_)) => [14, 68],
        (Var::Bound(_), Var::Bound(_)) => [19, 14],
        _ => [7, 5],
    };
    let mut work = [29 + selector[0], 29 + selector[1]];
    for (left, right) in strings(node).into_iter().zip(strings(other)) {
        let pair = string_cost(left, right);
        work[0] += pair[0];
        work[1] += pair[1];
    }
    let (holes, hole_steps) = vector_cost(&node.holes, &other.holes, hole_cost);
    let (pieces, piece_steps) = vector_cost(&node.pieces, &other.pieces, piece_cost);
    work[0] += holes[0] + pieces[0];
    work[1] += holes[1] + pieces[1];
    let inspections = [1 + hole_steps[0] + piece_steps[0], 1 + hole_steps[1] + piece_steps[1]];
    (
        [work[0], work[0] + 1, work[1]],
        [inspections[0], inspections[0], inspections[1]],
    )
}

// Constant-time source-storage checks, not a proof of no temporary allocation.
fn storage(node: &FltNode) -> [(usize, usize, usize); 7] {
    let mut result = [(0, 0, 0); 7];
    for (slot, text) in result.iter_mut().zip(strings(node)) {
        *slot = (text.as_ptr() as usize, text.len(), text.capacity());
    }
    result[5] = (node.holes.as_ptr() as usize, node.holes.len(), node.holes.capacity());
    result[6] = (node.pieces.as_ptr() as usize, node.pieces.len(), node.pieces.capacity());
    result
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Outcome {
    Boolean(bool),
    Ordering(Ordering),
}

fn check<T: CheckedNativeEqualityLeaf + CheckedNativeOrderingLeaf>(
    left: &T,
    right: &T,
    work: [usize; 3],
    inspections: [usize; 3],
    every_cutpoint: bool,
    invariant: impl Fn(),
) {
    for op in 0..3 {
        let native = match op {
            0 => Outcome::Boolean(PartialEq::eq(left, right)),
            1 => Outcome::Boolean(PartialEq::ne(left, right)),
            _ => Outcome::Ordering(Ord::cmp(left, right)),
        };
        let run = |reserve: &mut dyn FnMut(usize, usize) -> Result<(), usize>| match op {
            0 => left
                .try_native_eq(right, &mut |w, u| reserve(w, u))
                .map(Outcome::Boolean),
            1 => left
                .try_native_ne(right, &mut |w, u| reserve(w, u))
                .map(Outcome::Boolean),
            _ => left
                .try_native_cmp(right, &mut |w, u| reserve(w, u))
                .map(Outcome::Ordering),
        };
        let inspect = |reserve: &mut dyn FnMut(usize, usize) -> Result<(), usize>| match op {
            0 => left.try_inspect_native_eq_work(right, &mut |w, u| reserve(w, u)),
            1 => left.try_inspect_native_ne_work(right, &mut |w, u| reserve(w, u)),
            _ => left.try_inspect_native_cmp_work(right, &mut |w, u| reserve(w, u)),
        };
        // Check the exact existing metadata prefix independently of execution.
        let mut inspection_trace = Vec::new();
        assert_eq!(
            inspect(&mut |w, u| {
                invariant();
                inspection_trace.push((w, u));
                Ok(())
            }),
            Ok(work[op])
        );
        assert_eq!(inspection_trace, vec![(1, 0); inspections[op]]);
        let inspection_stops: Vec<_> = match every_cutpoint {
            true => (0..inspections[op]).collect(),
            false => vec![0, inspections[op] / 2, inspections[op] - 1],
        };
        for stop in inspection_stops {
            let mut seen = Vec::new();
            let result = inspect(&mut |w, u| {
                invariant();
                let index = seen.len();
                seen.push((w, u));
                match index == stop {
                    true => Err(stop),
                    false => Ok(()),
                }
            });
            assert_eq!(
                result,
                Err(NativeComparisonFailure::Admission(BindingFailure::Reservation(stop)))
            );
            assert_eq!(seen, inspection_trace[..=stop]);
        }
        for limit in [0, inspections[op] - 1, inspections[op]] {
            let mut remaining = limit;
            let result = inspect(&mut |w, u| {
                invariant();
                assert_eq!(u, 0);
                remaining = remaining.checked_sub(w).ok_or(limit)?;
                Ok(())
            });
            assert_eq!(remaining, 0);
            match limit == inspections[op] {
                true => assert_eq!(result, Ok(work[op])),
                false => assert_eq!(
                    result,
                    Err(NativeComparisonFailure::Admission(BindingFailure::Reservation(limit)))
                ),
            }
        }
        let mut expected_trace = vec![(1, 0); inspections[op]];
        expected_trace.push((work[op], 0));
        let mut seen = Vec::new();
        assert_eq!(
            run(&mut |w, u| {
                invariant();
                seen.push((w, u));
                Ok(())
            }),
            Ok(native)
        );
        assert_eq!(seen, expected_trace);
        let stops: Vec<_> = if every_cutpoint {
            (0..expected_trace.len()).collect()
        } else {
            vec![0, inspections[op] / 2, inspections[op]]
        };
        for stop in stops {
            let mut seen = Vec::new();
            let mut spent = 0;
            let result = run(&mut |w, u| {
                invariant();
                let index = seen.len();
                seen.push((w, u));
                if index == stop {
                    Err(stop)
                } else {
                    spent += w;
                    Ok(())
                }
            });
            assert_eq!(
                result,
                Err(NativeComparisonFailure::Admission(BindingFailure::Reservation(stop)))
            );
            assert_eq!(seen, expected_trace[..=stop]);
            assert_eq!(
                spent,
                expected_trace[..stop]
                    .iter()
                    .map(|entry| entry.0)
                    .sum::<usize>()
            );
        }
        let total = work[op] + inspections[op];
        for limit in [total - 1, total] {
            let mut remaining = limit;
            let result = run(&mut |w, u| {
                invariant();
                assert_eq!(u, 0);
                remaining = remaining.checked_sub(w).ok_or(limit)?;
                Ok(())
            });
            if limit == total {
                assert_eq!(result, Ok(native));
                assert_eq!(remaining, 0);
            } else {
                assert_eq!(
                    result,
                    Err(NativeComparisonFailure::Admission(BindingFailure::Reservation(limit)))
                );
                assert_eq!(remaining, work[op] - 1);
            }
        }
        invariant();
    }
}

#[test]
#[cfg(mettail_checked_native_comparison_profile)]
fn flt_comparisons_cover_every_top_level_field_and_actual_byte_extent() {
    assert!(CHECKED_NATIVE_COMPARISON_PROFILE_AVAILABLE);
    let empty = empty_node();
    assert_eq!(expected(&empty, &empty), ([87, 88, 164], [3, 3, 3]));
    check_values(&empty, &empty.clone(), true);
    let set_text = |node: &mut FltNode, index: usize, text: &str| {
        let fields = [
            &mut node.selector_name,
            &mut node.category,
            &mut node.open_src,
            &mut node.body_src,
            &mut node.close_src,
        ];
        *fields
            .into_iter()
            .nth(index)
            .expect("five native String fields") = text.to_owned();
    };
    for index in 0..5 {
        for (left, right) in [
            ("", "a"),
            ("λ", "μ"),
            ("ab", "ac"),
            ("ab", "cb"),
            ("abc", "ab"),
            ("a\0b", "a\0c"),
        ] {
            let mut node = empty.clone();
            let mut other = empty.clone();
            set_text(&mut node, index, left);
            set_text(&mut other, index, right);
            check_values(&node, &other, true);
            check_values(&other, &node, true);
        }
    }
    let mut hinted = empty.clone();
    let Var::Free(free) = &mut hinted.selector.0 else {
        panic!("free fixture selector")
    };
    free.pretty_name = Some("ignored".repeat(10_000));
    assert_eq!(empty, hinted);
    check_values(&empty, &hinted, true);
    let mut bound = empty.clone();
    bound.selector = OrdVar(Var::Bound(crate::BoundVar {
        scope: moniker::ScopeOffset(u32::MAX),
        binder: moniker::BinderIndex(0),
        pretty_name: None,
    }));
    check_values(&empty, &bound, true);
    check_values(&bound, &empty, true);
    let mut other_bound = bound.clone();
    let Var::Bound(variable) = &mut other_bound.selector.0 else {
        panic!("bound selector")
    };
    variable.binder = moniker::BinderIndex(u32::MAX);
    check_values(&bound, &other_bound, true);

    let node = populated_node();
    // Root strings: E54/C69; hole E44/C50; pieces E22+18/C25+18.
    assert_eq!(expected(&node, &node), ([204, 205, 293], [6, 6, 6]));
    check_values(&node, &node.clone(), true);
    for index in 0..6 {
        let mut other = node.clone();
        match index {
            0 => other.bounds.source_bytes = usize::MAX,
            1 => other.bounds.body_bytes = usize::MAX,
            2 => other.bounds.piece_count = usize::MAX,
            3 => other.bounds.hole_declarations = usize::MAX,
            4 => other.bounds.hole_occurrences = usize::MAX,
            _ => other.position = usize::MAX,
        }
        assert_eq!(expected(&node, &other), expected(&node, &node));
        assert_ne!(node, other, "native comparison includes claimed bounds and position");
        check_values(&node, &other, true);
    }
}

#[test]
#[cfg(mettail_checked_native_comparison_profile)]
fn flt_holes_pieces_and_ranges_keep_native_fields_without_validation() {
    let node = populated_node();
    for index in 0..8 {
        let mut other = node.clone();
        let hole = &mut other.holes[0];
        match index {
            0 => hole.id = FltHoleId(u32::MAX),
            1 => hole.name = "".into(),
            2 => hole.name = "λ".into(),
            3 => hole.category = None,
            4 => hole.category = Some(String::new()),
            5 => hole.category = Some("λ".into()),
            6 => hole.first_occurrence.start = usize::MAX,
            _ => hole.first_occurrence.end = 0,
        }
        check_values(&node, &other, true);
        check_values(&other, &node, true);
    }
    let mut no_category = node.clone();
    no_category.holes[0].category = None;
    check_values(&no_category, &no_category.clone(), true);
    for piece_index in 0..2 {
        for start in [true, false] {
            let mut other = node.clone();
            let range = match &mut other.pieces[piece_index] {
                FltTemplatePiece::Text { range, .. } | FltTemplatePiece::Hole { range, .. } => {
                    range
                },
            };
            if start {
                range.start = usize::MAX;
            } else {
                range.end = usize::MAX;
            }
            assert_ne!(node, other, "both native piece ranges participate in comparison");
            check_values(&node, &other, true);
        }
    }
    let pieces = [
        FltTemplatePiece::Text {
            text: "".into(),
            range: FltSourceRange::new(0, 0),
        },
        FltTemplatePiece::Text {
            text: "λ".into(),
            range: FltSourceRange::new(usize::MAX, 0),
        },
        FltTemplatePiece::Text {
            text: "aa".into(),
            range: FltSourceRange::new(0, usize::MAX),
        },
        FltTemplatePiece::Hole {
            id: FltHoleId(0),
            range: FltSourceRange::new(0, 1),
        },
        FltTemplatePiece::Hole {
            id: FltHoleId(u32::MAX),
            range: FltSourceRange::new(usize::MAX, 0),
        },
    ];
    for left in &pieces {
        for right in &pieces {
            let mut node = node.clone();
            let mut other = node.clone();
            node.pieces = vec![left.clone()];
            other.pieces = vec![right.clone()];
            check_values(&node, &other, true);
        }
    }
}

#[test]
#[cfg(mettail_checked_native_comparison_profile)]
fn flt_vector_equality_skips_unequal_widths_but_ordering_admits_the_common_prefix() {
    let base = populated_node();
    for holes in [true, false] {
        for (left_width, right_width) in [(0, 0), (0, 2), (2, 0), (1, 2), (2, 1), (2, 2)] {
            let mut left = base.clone();
            let mut right = base.clone();
            if holes {
                left.holes = vec![base.holes[0].clone(); left_width];
                right.holes = vec![base.holes[0].clone(); right_width];
            } else {
                left.pieces = vec![base.pieces[0].clone(); left_width];
                right.pieces = vec![base.pieces[0].clone(); right_width];
            }
            check_values(&left, &right, true);
        }
    }
    let mut misleading = base.clone();
    misleading.bounds = FltTemplateBounds {
        source_bytes: usize::MAX,
        body_bytes: usize::MAX,
        piece_count: usize::MAX,
        hole_declarations: usize::MAX,
        hole_occurrences: usize::MAX,
    };
    assert_eq!(expected(&base, &misleading), expected(&base, &base));
    check_values(&base, &misleading, true);
}

#[test]
#[cfg(mettail_checked_native_comparison_profile)]
fn shared_arc_equality_uses_only_its_header_but_ordering_still_walks() {
    let shared = Arc::new(populated_node());
    check_shared(&shared, true);
}

#[test]
#[cfg(mettail_checked_native_comparison_profile)]
fn wide_flat_flt_comparison_and_refusal_use_a_small_native_stack() {
    std::thread::Builder::new()
        .stack_size(256 * 1024)
        .spawn(|| {
            let mut node = populated_node();
            node.holes = vec![node.holes[0].clone(); 20_000];
            node.pieces = (0..20_000)
                .map(|index| node.pieces[index % 2].clone())
                .collect();
            let mut other = node.clone();
            let FltTemplatePiece::Hole { id, .. } = other.pieces.last_mut().expect("wide pieces")
            else {
                panic!("alternating fixture ends in a hole")
            };
            *id = FltHoleId(u32::MAX);
            // Sample cutpoints here; exhaustive small cases above avoid quadratic work.
            check_values(&node, &other, false);
            check_shared(&Arc::new(node), false);
        })
        .expect("spawn flat FLT small-stack test")
        .join()
        .expect("flat FLT test completes");
}

#[test]
fn unsupported_profile_refuses_real_flt_operands_before_any_work_or_action() {
    fn refused<T: sealed::Leaf>(left: &T, right: &T) {
        for operation in
            [ComparisonOperation::Eq, ComparisonOperation::Ne, ComparisonOperation::Cmp]
        {
            let mut reservations = 0;
            let mut actions = 0;
            let result = admit_comparison(
                left,
                right,
                operation,
                &mut |_, _| {
                    reservations += 1;
                    Ok::<_, usize>(())
                },
                false,
                |_, _| {
                    actions += 1;
                    0u8
                },
            );
            assert_eq!(result, Err(NativeComparisonFailure::UnsupportedProfile));
            assert_eq!((reservations, actions), (0, 0));
        }
    }
    let node = populated_node();
    refused(&node, &node);
    let shared = Arc::new(node);
    refused(&shared, &shared);
}

fn check_values(left: &FltNode, right: &FltNode, every_cutpoint: bool) {
    let (work, inspections) = expected(left, right);
    let left_storage = storage(left);
    let right_storage = storage(right);
    check(left, right, work, inspections, every_cutpoint, || {
        assert_eq!(storage(left), left_storage);
        assert_eq!(storage(right), right_storage);
    });
    let left = Arc::new(left.clone());
    let right = Arc::new(right.clone());
    assert!(!Arc::ptr_eq(&left, &right));
    let left_storage = storage(&left);
    let right_storage = storage(&right);
    check(
        &left,
        &right,
        [4 + work[0], 5 + work[0], 2 + work[2]],
        inspections,
        every_cutpoint,
        || {
            assert_eq!(Arc::strong_count(&left), 1);
            assert_eq!(Arc::strong_count(&right), 1);
            assert_eq!(storage(&left), left_storage);
            assert_eq!(storage(&right), right_storage);
        },
    );
}

fn check_shared(shared: &Arc<FltNode>, every_cutpoint: bool) {
    let before = Arc::strong_count(shared);
    let alias = Arc::clone(shared);
    assert!(Arc::ptr_eq(shared, &alias));
    let source_storage = storage(shared);
    let (work, inspections) = expected(shared, shared);
    check(
        shared,
        &alias,
        [3, 3, 2 + work[2]],
        [1, 1, inspections[2]],
        every_cutpoint,
        || {
            assert_eq!(Arc::strong_count(shared), before + 1);
            assert_eq!(Arc::strong_count(&alias), before + 1);
            assert_eq!(storage(shared), source_storage);
        },
    );
    drop(alias);
    assert_eq!(Arc::strong_count(shared), before);
}

#[test]
#[cfg(mettail_checked_native_comparison_profile)]
fn flt_selector_identity_and_both_unequal_vectors_keep_their_distinct_paths() {
    let node = empty_node();
    let distinct_uid = empty_node();
    assert_ne!(node.selector, distinct_uid.selector);
    check_values(&node, &distinct_uid, true);
    let populated = populated_node();
    let mut no_entries = populated.clone();
    no_entries.holes.clear();
    no_entries.pieces.clear();
    assert_eq!(expected(&populated, &no_entries), ([111, 112, 188], [1, 1, 3]));
    check_values(&populated, &no_entries, true);
    check_values(&no_entries, &populated, true);
    for differing_index in 0..2 {
        let mut left = populated.clone();
        left.holes = vec![left.holes[0].clone(); 2];
        let mut right = left.clone();
        right.holes[differing_index].id = FltHoleId(u32::MAX);
        check_values(&left, &right, true);
    }
}
