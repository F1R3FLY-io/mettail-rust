//! Const projection into the existing preparation reservation convention.
//!
//! Event counts and semantic Cost(G) grades are not interchangeable. This
//! module projects the former into logical preparation work, records and bytes;
//! the caller still owns the one reservation callback. A dummy bundle pays only
//! for that selected replacement recipe, not an arbitrary category value.

use super::{Counts, Event, Receipt, ReceiptOverflow, EVENTS};
use crate::checked_binding::BINDING_RECORD_UNITS;
use crate::{reserve_binding_parts, BindingFailure};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ChargeOverflow {
    Work,
    Records,
    OwnedBytes,
    RetentionUnits,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DummyChargeError {
    Counts(ReceiptOverflow),
    Projection(ChargeOverflow),
}

macro_rules! checked_charge {
    ($expression:expr) => {
        match $expression {
            Ok(value) => value,
            Err(error) => return Err(error),
        }
    };
}

const fn add(
    left: usize,
    right: usize,
    component: ChargeOverflow,
) -> Result<usize, ChargeOverflow> {
    match left.checked_add(right) {
        Some(value) => Ok(value),
        None => Err(component),
    }
}

const fn scale(
    value: usize,
    factor: usize,
    component: ChargeOverflow,
) -> Result<usize, ChargeOverflow> {
    match value.checked_mul(factor) {
        Some(value) => Ok(value),
        None => Err(component),
    }
}

/// An immutable charge with representable final work and retention totals.
///
/// Base work excludes owned bytes: [`Self::reserve`] delegates their single
/// addition to the existing [`reserve_binding_parts`] convention. Private
/// fields prevent constructing an unchecked total through a struct literal.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BindingCharge {
    work: usize,
    records: usize,
    owned_bytes: usize,
}

impl BindingCharge {
    pub const ZERO: Self = Self { work: 0, records: 0, owned_bytes: 0 };

    pub const fn new(
        work: usize,
        records: usize,
        owned_bytes: usize,
    ) -> Result<Self, ChargeOverflow> {
        checked_charge!(add(work, owned_bytes, ChargeOverflow::Work));
        let record_units =
            checked_charge!(scale(records, BINDING_RECORD_UNITS, ChargeOverflow::RetentionUnits));
        checked_charge!(add(record_units, owned_bytes, ChargeOverflow::RetentionUnits));
        Ok(Self { work, records, owned_bytes })
    }

    pub const fn base_work(self) -> usize {
        self.work
    }
    pub const fn records(self) -> usize {
        self.records
    }
    pub const fn owned_bytes(self) -> usize {
        self.owned_bytes
    }

    pub const fn checked_add(self, other: Self) -> Result<Self, ChargeOverflow> {
        let work = checked_charge!(add(self.work, other.work, ChargeOverflow::Work));
        let records = checked_charge!(add(self.records, other.records, ChargeOverflow::Records));
        let bytes =
            checked_charge!(add(self.owned_bytes, other.owned_bytes, ChargeOverflow::OwnedBytes));
        Self::new(work, records, bytes)
    }

    /// Add future-operation parts after paying for this fixed-size inspection.
    ///
    /// This reserves one metadata work group, not the operation described by
    /// the parts. It reuses [`Self::new`] and [`Self::checked_add`], including
    /// the final work/retention projection checks; no native Hash, Eq or Ord
    /// operation is performed. Both admission and arithmetic failure leave
    /// this accumulator unchanged, while earlier metadata charges stay spent.
    /// The caller must separately pay for retaining this accumulator and for
    /// eventual execution against the same source and audited cost profile.
    /// A representable charge is accounting data, not execution authority.
    pub fn try_accumulate_parts<E>(
        &mut self,
        work: usize,
        records: usize,
        owned_bytes: usize,
        reserve: &mut impl FnMut(usize, usize) -> Result<(), E>,
    ) -> Result<(), BindingFailure<E>> {
        // NativeInspectionAccumulation.v: precharge the fixed metadata group,
        // check every component/projection, then commit exactly once.
        reserve(1, 0).map_err(BindingFailure::Reservation)?;
        let more =
            Self::new(work, records, owned_bytes).map_err(|_| BindingFailure::SizeOverflow)?;
        let next = self
            .checked_add(more)
            .map_err(|_| BindingFailure::SizeOverflow)?;
        *self = next;
        Ok(())
    }

    pub const fn checked_scale(self, factor: usize) -> Result<Self, ChargeOverflow> {
        let work = checked_charge!(scale(self.work, factor, ChargeOverflow::Work));
        let records = checked_charge!(scale(self.records, factor, ChargeOverflow::Records));
        let bytes = checked_charge!(scale(self.owned_bytes, factor, ChargeOverflow::OwnedBytes));
        Self::new(work, records, bytes)
    }

    /// The concrete projection proved in GeneratedDummyCleanupReservation.v.
    /// This fixed event loop is intended for const table construction, not a
    /// repeated dependency walk during source preparation.
    pub const fn from_counts(counts: Counts) -> Result<Self, ChargeOverflow> {
        let mut work = 0;
        let mut records = 0;
        let mut bytes = 0;
        let mut index = 0;
        while index < EVENTS.len() {
            let event = EVENTS[index];
            let count = counts.get(event);
            match event {
                Event::ConstructCategory
                | Event::AllocateArc
                | Event::PushDropTask
                | Event::AcquirePool => {
                    work = checked_charge!(add(work, count, ChargeOverflow::Work));
                    records = checked_charge!(add(records, count, ChargeOverflow::Records));
                },
                Event::EnterDestructor
                | Event::ExtractChildren
                | Event::HandleField
                | Event::PopDropTask
                | Event::CheckArcOwner
                | Event::ReleaseFieldArc
                | Event::ReturnPool
                | Event::NativeWork => {
                    work = checked_charge!(add(work, count, ChargeOverflow::Work));
                },
                Event::NativeRecord => {
                    records = checked_charge!(add(records, count, ChargeOverflow::Records));
                },
                Event::OwnedByte => {
                    bytes = checked_charge!(add(bytes, count, ChargeOverflow::OwnedBytes));
                },
            }
            index += 1;
        }
        Self::new(work, records, bytes)
    }

    /// Reserve the precomputed triple through the caller's existing meter.
    /// This contains no event loop and does not construct any replacement.
    pub fn reserve<E>(
        self,
        reserve: &mut impl FnMut(usize, usize) -> Result<(), E>,
    ) -> Result<(), BindingFailure<E>> {
        reserve_binding_parts(self.work, self.records, self.owned_bytes, reserve)
    }
}

impl Receipt {
    /// Construction plus normal cleanup of THIS SELECTED DUMMY only.
    ///
    /// A parent that installs this dummy inside a replacement Arc must also
    /// pay its own Arc/control events. The original child's construction and
    /// cleanup remain its producer's responsibility; do not pay them twice.
    pub const fn replacement_charge(self) -> Result<BindingCharge, DummyChargeError> {
        let counts = match self.construction.checked_add(self.normal_drop) {
            Ok(counts) => counts,
            Err(error) => return Err(DummyChargeError::Counts(error)),
        };
        match BindingCharge::from_counts(counts) {
            Ok(charge) => Ok(charge),
            Err(error) => Err(DummyChargeError::Projection(error)),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::binding_receipt::{compose, LocalReceipt};

    const LEAF_CHARGE: Result<BindingCharge, DummyChargeError> =
        match compose(LocalReceipt::ZERO, &[]) {
            Ok(receipt) => receipt.replacement_charge(),
            Err(error) => Err(DummyChargeError::Counts(error)),
        };

    #[test]
    fn paid_accumulation_reserves_metadata_not_future_execution() {
        let mut charge = BindingCharge::new(3, 2, 5).expect("initial charge");
        let mut inspection = Vec::new();
        charge
            .try_accumulate_parts(7, 4, 9, &mut |work, units| {
                inspection.push((work, units));
                Ok::<_, ()>(())
            })
            .expect("representable sum");
        assert_eq!(charge, BindingCharge::new(10, 6, 14).expect("exact sum"));
        assert_eq!(inspection, [(1, 0)]);
        let unchanged = charge;
        charge
            .try_accumulate_parts(0, 0, 0, &mut |work, units| {
                inspection.push((work, units));
                Ok::<_, ()>(())
            })
            .expect("zero parts still pay metadata");
        assert_eq!(charge, unchanged);
        assert_eq!(inspection, [(1, 0), (1, 0)]);
        let mut execution = Vec::new();
        charge
            .reserve(&mut |work, units| {
                execution.push((work, units));
                Ok::<_, ()>(())
            })
            .expect("future work requires a separate reservation");
        assert_eq!(execution, [(24, 38)]);
    }

    #[test]
    fn paid_accumulation_moves_reservation_error_and_keeps_accumulator() {
        struct ErrorPayload(u8);
        let payload = Box::new(ErrorPayload(41));
        let address = std::ptr::from_ref(payload.as_ref());
        let mut pending = Some(payload);
        let mut calls = 0;
        let before = BindingCharge::new(2, 3, 5).expect("initial charge");
        let mut charge = before;
        let result =
            charge.try_accumulate_parts(usize::MAX, usize::MAX, usize::MAX, &mut |w, u| {
                assert_eq!((w, u), (1, 0));
                calls += 1;
                Err(pending.take().expect("only one metadata reservation"))
            });
        let Err(BindingFailure::Reservation(error)) = result else {
            panic!("reservation refusal must precede overflowing arithmetic")
        };
        assert_eq!(std::ptr::from_ref(error.as_ref()), address);
        assert_eq!(error.0, 41);
        assert_eq!(calls, 1);
        assert_eq!(charge, before);
    }

    #[test]
    fn paid_accumulation_matches_wide_arithmetic_at_projection_boundaries() {
        let values = [0, 1, usize::MAX / 4, usize::MAX / 4 + 1, usize::MAX - 1, usize::MAX];
        for work in values {
            for records in values {
                for bytes in values {
                    let Ok(before) = BindingCharge::new(work, records, bytes) else {
                        continue;
                    };
                    for more_work in values {
                        for more_records in values {
                            for more_bytes in values {
                                let expected_work = work as u128 + more_work as u128;
                                let expected_records = records as u128 + more_records as u128;
                                let expected_bytes = bytes as u128 + more_bytes as u128;
                                let fits = expected_work + expected_bytes <= usize::MAX as u128
                                    && 4 * expected_records + expected_bytes <= usize::MAX as u128;
                                let mut charge = before;
                                let mut calls = 0;
                                let result = charge.try_accumulate_parts(
                                    more_work,
                                    more_records,
                                    more_bytes,
                                    &mut |w, u| {
                                        assert_eq!((w, u), (1, 0));
                                        calls += 1;
                                        Ok::<_, ()>(())
                                    },
                                );
                                assert_eq!(calls, 1, "overflow retains the metadata charge");
                                if fits {
                                    assert_eq!(result, Ok(()));
                                    assert_eq!(charge.base_work() as u128, expected_work);
                                    assert_eq!(charge.records() as u128, expected_records);
                                    assert_eq!(charge.owned_bytes() as u128, expected_bytes);
                                } else {
                                    assert_eq!(result, Err(BindingFailure::SizeOverflow));
                                    assert_eq!(charge, before, "no partial accumulator update");
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn every_event_has_the_declared_work_record_byte_projection() {
        use Event::*;
        for event in EVENTS {
            let expected = match event {
                ConstructCategory | AllocateArc | PushDropTask | AcquirePool => (1, 1, 0),
                NativeRecord => (0, 1, 0),
                OwnedByte => (0, 0, 1),
                EnterDestructor | ExtractChildren | HandleField | PopDropTask | CheckArcOwner
                | ReleaseFieldArc | ReturnPool | NativeWork => (1, 0, 0),
            };
            let charge =
                BindingCharge::from_counts(Counts::singleton(event, 1)).expect("single event");
            assert_eq!((charge.base_work(), charge.records(), charge.owned_bytes()), expected);
        }
    }

    #[test]
    fn bytes_are_added_once_and_the_existing_callback_owns_refusal() {
        let charge = BindingCharge::new(1, 1, 5).expect("small charge");
        let mut calls = Vec::new();
        let result = charge.reserve(&mut |work, units| {
            calls.push((work, units));
            Err("cancelled")
        });
        assert_eq!(result, Err(BindingFailure::Reservation("cancelled")));
        assert_eq!(calls, [(6, 9)]);
        let byte_only = BindingCharge::from_counts(Counts::singleton(Event::OwnedByte, 5))
            .expect("byte-only charge");
        byte_only
            .reserve(&mut |work, units| {
                assert_eq!((work, units), (5, 5));
                Ok::<_, ()>(())
            })
            .expect("existing reservation convention");
    }

    #[test]
    fn projection_rejects_event_sums_and_final_word_overflow() {
        assert_eq!(BindingCharge::new(usize::MAX, 0, 1), Err(ChargeOverflow::Work));
        let records = usize::MAX / BINDING_RECORD_UNITS;
        assert!(BindingCharge::new(0, records, usize::MAX % BINDING_RECORD_UNITS).is_ok());
        assert_eq!(
            BindingCharge::new(0, records, BINDING_RECORD_UNITS),
            Err(ChargeOverflow::RetentionUnits)
        );
        let counts = Counts::singleton(Event::ConstructCategory, 1)
            .checked_add(Counts::singleton(Event::NativeRecord, usize::MAX))
            .expect("separate events");
        assert_eq!(BindingCharge::from_counts(counts), Err(ChargeOverflow::Records));
        let counts = Counts::singleton(Event::HandleField, usize::MAX)
            .checked_add(Counts::singleton(Event::NativeWork, 1))
            .expect("separate events");
        assert_eq!(BindingCharge::from_counts(counts), Err(ChargeOverflow::Work));
    }

    #[test]
    fn charge_composition_is_checked_and_does_not_saturate() {
        let charge = BindingCharge::new(2, 3, 5).expect("small charge");
        assert_eq!(charge.checked_add(charge), BindingCharge::new(4, 6, 10));
        assert_eq!(charge.checked_scale(2), charge.checked_add(charge));
        assert_eq!(charge.checked_scale(0), Ok(BindingCharge::ZERO));
        assert_eq!(charge.checked_scale(usize::MAX), Err(ChargeOverflow::Work));
        let byte_max = BindingCharge::new(0, 0, usize::MAX).expect("representable all-byte charge");
        assert_eq!(byte_max.checked_scale(2), Err(ChargeOverflow::OwnedBytes));
        assert_eq!(byte_max.checked_add(byte_max), Err(ChargeOverflow::OwnedBytes));
    }

    #[test]
    fn dummy_bundle_is_const_and_keeps_count_and_projection_errors_distinct() {
        assert_eq!(LEAF_CHARGE, Ok(BindingCharge::new(6, 2, 0).expect("leaf bundle")));
        let count_overflow = Receipt {
            construction: Counts::singleton(Event::NativeWork, usize::MAX),
            normal_drop: Counts::singleton(Event::NativeWork, 1),
            ..Receipt::ZERO
        };
        assert_eq!(
            count_overflow.replacement_charge(),
            Err(DummyChargeError::Counts(ReceiptOverflow { event: Event::NativeWork }))
        );
        let units_overflow = Receipt {
            construction: Counts::singleton(Event::NativeRecord, usize::MAX),
            ..Receipt::ZERO
        };
        assert_eq!(
            units_overflow.replacement_charge(),
            Err(DummyChargeError::Projection(ChargeOverflow::RetentionUnits))
        );
    }
}
