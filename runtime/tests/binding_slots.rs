//! IndexedCopySlots correspondence with non-Clone owned values.
use std::cell::Cell;
use std::rc::Rc;

use mettail_runtime::{
    append_binding_slots, take_binding_slot, write_binding_slot, BindingFailure, BindingSlotError,
};

#[derive(Debug, PartialEq, Eq)]
enum ResultValue {
    Term(u32),
    Metadata(u32),
}

fn term(value: &ResultValue) -> bool {
    matches!(value, ResultValue::Term(_))
}

fn admit(_: usize, _: usize) -> Result<(), &'static str> {
    Ok(())
}

#[test]
fn appended_ranges_preserve_prefix_and_are_disjoint() {
    let mut slots = vec![Some(ResultValue::Metadata(7))];
    let mut charges = Vec::new();
    for (count, expected) in [(0, 1), (2, 1), (3, 3)] {
        assert_eq!(
            append_binding_slots(&mut slots, count, &mut |work, units| {
                charges.push((work, units));
                admit(work, units)
            }),
            Ok(expected),
        );
    }
    assert_eq!(charges, [(0, 0), (2, 8), (3, 12)]);
    assert_eq!(slots[0], Some(ResultValue::Metadata(7)));
    assert_eq!(slots.len(), 6);
    assert!(slots[1..].iter().all(Option::is_none));
}

#[test]
fn allocation_limits_and_overflow_refuse_before_storage_changes() {
    for limit in [(1usize, 8usize), (2, 7), (2, 8)] {
        let mut slots = vec![Some(ResultValue::Metadata(7))];
        let mut calls = 0;
        let outcome = append_binding_slots(&mut slots, 2, &mut |work, units| {
            calls += 1;
            if work > limit.0 || units > limit.1 {
                Err("limit")
            } else {
                Ok(())
            }
        });
        assert_eq!(calls, 1);
        assert_eq!(slots[0], Some(ResultValue::Metadata(7)));
        if limit == (2, 8) {
            assert_eq!(outcome, Ok(1));
            assert_eq!(slots.len(), 3);
        } else {
            assert_eq!(outcome, Err(BindingFailure::Reservation("limit")));
            assert_eq!(slots.len(), 1);
        }
    }
    let mut slots = vec![Some(ResultValue::Metadata(7))];
    for count in [usize::MAX, usize::MAX / 4 + 1] {
        let mut calls = 0;
        assert_eq!(
            append_binding_slots(&mut slots, count, &mut |_, _| {
                calls += 1;
                Ok::<(), &'static str>(())
            }),
            Err(BindingFailure::SizeOverflow),
        );
        assert_eq!(calls, 0);
        assert_eq!(slots, [Some(ResultValue::Metadata(7))]);
    }
    assert_eq!(
        append_binding_slots(&mut slots, 0, &mut |_, _| Err("cancelled")),
        Err(BindingFailure::Reservation("cancelled")),
    );
    assert_eq!(slots, [Some(ResultValue::Metadata(7))]);
}

#[test]
fn write_checks_category_bounds_and_occupancy_without_overwriting() {
    let mut slots = vec![Some(ResultValue::Metadata(7)), None];
    for (slot, value, expected) in [
        (1, ResultValue::Metadata(5), BindingSlotError::WrongCategory { slot: 1 }),
        (2, ResultValue::Term(5), BindingSlotError::OutOfBounds { slot: 2, len: 2 }),
        (0, ResultValue::Term(5), BindingSlotError::Occupied { slot: 0 }),
    ] {
        assert_eq!(
            write_binding_slot(&mut slots, slot, value, term, &mut admit),
            Err(BindingFailure::Slot(expected)),
        );
        assert_eq!(slots, [Some(ResultValue::Metadata(7)), None]);
    }
    assert_eq!(
        write_binding_slot(
            &mut slots,
            1,
            ResultValue::Term(5),
            |_| { panic!("cancelled write must not inspect the value") },
            &mut |_, _| Err("cancelled")
        ),
        Err(BindingFailure::Reservation("cancelled")),
    );
    assert_eq!(slots, [Some(ResultValue::Metadata(7)), None]);
    let mut charges = Vec::new();
    write_binding_slot(&mut slots, 1, ResultValue::Term(5), term, &mut |work, units| {
        charges.push((work, units));
        admit(work, units)
    })
    .expect("admitted fill");
    assert_eq!(charges, [(1, 0)]);
    assert_eq!(slots, [Some(ResultValue::Metadata(7)), Some(ResultValue::Term(5))]);
    assert_eq!(
        write_binding_slot(&mut slots, 1, ResultValue::Term(9), term, &mut admit),
        Err(BindingFailure::Slot(BindingSlotError::Occupied { slot: 1 })),
    );
    assert_eq!(slots[1], Some(ResultValue::Term(5)));
}

#[test]
fn takes_validate_before_removal_and_preserve_order_and_repetitions() {
    let mut slots = vec![Some(ResultValue::Metadata(7)), None];
    for (slot, expected) in [
        (0, BindingSlotError::WrongCategory { slot: 0 }),
        (1, BindingSlotError::Empty { slot: 1 }),
        (2, BindingSlotError::OutOfBounds { slot: 2, len: 2 }),
    ] {
        assert_eq!(
            take_binding_slot(&mut slots, slot, term, &mut admit),
            Err(BindingFailure::Slot(expected)),
        );
        assert_eq!(slots, [Some(ResultValue::Metadata(7)), None]);
    }
    slots[1] = Some(ResultValue::Term(3));
    assert_eq!(
        take_binding_slot(
            &mut slots,
            1,
            |_| { panic!("cancelled take must not inspect or consume the value") },
            &mut |_, _| Err("cancelled")
        ),
        Err(BindingFailure::Reservation("cancelled")),
    );
    assert_eq!(slots[1], Some(ResultValue::Term(3)));
    slots.push(Some(ResultValue::Term(3)));
    slots.push(Some(ResultValue::Term(8)));
    slots.push(Some(ResultValue::Metadata(9)));
    let mut output = Vec::with_capacity(3);
    let mut charges = Vec::new();
    for index in 1..4 {
        output.push(
            take_binding_slot(&mut slots, index, term, &mut |work, units| {
                charges.push((work, units));
                admit(work, units)
            })
            .expect("prepared contiguous range"),
        );
    }
    assert_eq!(output, [ResultValue::Term(3), ResultValue::Term(3), ResultValue::Term(8)]);
    assert_eq!(charges, [(1, 0), (1, 0), (1, 0)]);
    assert_eq!(
        slots,
        [Some(ResultValue::Metadata(7)), None, None, None, Some(ResultValue::Metadata(9))]
    );
    assert_eq!(
        take_binding_slot(&mut slots, 1, term, &mut admit),
        Err(BindingFailure::Slot(BindingSlotError::Empty { slot: 1 })),
    );
}

#[test]
fn refused_write_drops_only_incoming_value_and_failed_take_keeps_owner() {
    struct Tracked(Rc<Cell<usize>>);
    impl Drop for Tracked {
        fn drop(&mut self) {
            self.0.set(self.0.get() + 1);
        }
    }
    let dropped = Rc::new(Cell::new(0));
    let mut slots = vec![Some(Tracked(dropped.clone()))];
    assert_eq!(
        write_binding_slot(&mut slots, 0, Tracked(dropped.clone()), |_| true, &mut admit),
        Err(BindingFailure::Slot(BindingSlotError::Occupied { slot: 0 })),
    );
    assert_eq!(dropped.get(), 1);
    assert!(matches!(
        take_binding_slot(&mut slots, 0, |_| false, &mut admit),
        Err(BindingFailure::Slot(BindingSlotError::WrongCategory { slot: 0 })),
    ));
    assert_eq!(dropped.get(), 1);
    let taken = take_binding_slot(&mut slots, 0, |_| true, &mut admit)
        .unwrap_or_else(|error| panic!("valid take: {error:?}"));
    assert!(slots[0].is_none());
    drop(slots);
    assert_eq!(dropped.get(), 1);
    drop(taken);
    assert_eq!(dropped.get(), 2);
}
