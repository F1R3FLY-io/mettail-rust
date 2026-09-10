//! Arithmetic receipts for already-selected finite dummy recipes.
//!
//! This is the C/X/A/P/N algebra in `GeneratedDummyCleanupReservation.v`.
//! No default selection, event weights, reservation callback, or allocator
//! model lives here. Children are previously computed receipts, supplied once
//! per field occurrence. Normal cleanup assumes an available empty work pool.

mod charge;
mod defaults;
pub use charge::{BindingCharge, ChargeOverflow, DummyChargeError};

/// Unweighted events in the selected-dummy cleanup model.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(usize)]
pub enum Event {
    ConstructCategory,
    EnterDestructor,
    ExtractChildren,
    HandleField,
    PushDropTask,
    PopDropTask,
    AllocateArc,
    CheckArcOwner,
    ReleaseFieldArc,
    AcquirePool,
    ReturnPool,
    NativeWork,
    NativeRecord,
    OwnedByte,
}

pub const EVENT_COUNT: usize = Event::OwnedByte as usize + 1;
pub const EVENTS: [Event; EVENT_COUNT] = [
    Event::ConstructCategory,
    Event::EnterDestructor,
    Event::ExtractChildren,
    Event::HandleField,
    Event::PushDropTask,
    Event::PopDropTask,
    Event::AllocateArc,
    Event::CheckArcOwner,
    Event::ReleaseFieldArc,
    Event::AcquirePool,
    Event::ReturnPool,
    Event::NativeWork,
    Event::NativeRecord,
    Event::OwnedByte,
];

/// The named event's multiplicity does not fit the target's `usize`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ReceiptOverflow {
    pub event: Event,
}

// Const-compatible propagation without the Try trait.
macro_rules! checked_receipt {
    ($expression:expr) => {
        match $expression {
            Ok(value) => value,
            Err(error) => return Err(error),
        }
    };
}

const fn add(event: Event, left: usize, right: usize) -> Result<usize, ReceiptOverflow> {
    match left.checked_add(right) {
        Some(value) => Ok(value),
        None => Err(ReceiptOverflow { event }),
    }
}

const fn sum(event: Event, parts: &[usize]) -> Result<usize, ReceiptOverflow> {
    let mut result = 0;
    let mut index = 0;
    while index < parts.len() {
        result = checked_receipt!(add(event, result, parts[index]));
        index += 1;
    }
    Ok(result)
}

const fn occurrences(event: Event, wanted: Event, count: usize) -> usize {
    if event as usize == wanted as usize {
        count
    } else {
        0
    }
}

/// A fixed-size vector of nonnegative event multiplicities, not prices.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Counts([usize; EVENT_COUNT]);

impl Counts {
    pub const ZERO: Self = Self([0; EVENT_COUNT]);

    pub const fn singleton(event: Event, count: usize) -> Self {
        let mut result = Self::ZERO;
        result.0[event as usize] = count;
        result
    }

    pub const fn get(&self, event: Event) -> usize {
        self.0[event as usize]
    }

    pub const fn checked_add(self, other: Self) -> Result<Self, ReceiptOverflow> {
        let mut result = Self::ZERO;
        let mut index = 0;
        while index < EVENT_COUNT {
            result.0[index] = checked_receipt!(add(EVENTS[index], self.0[index], other.0[index]));
            index += 1;
        }
        Ok(result)
    }

    pub const fn checked_scale(self, factor: usize) -> Result<Self, ReceiptOverflow> {
        let mut result = Self::ZERO;
        let mut index = 0;
        while index < EVENT_COUNT {
            result.0[index] = match self.0[index].checked_mul(factor) {
                Some(value) => value,
                None => return Err(ReceiptOverflow { event: EVENTS[index] }),
            };
            index += 1;
        }
        Ok(result)
    }
}

/// Local effects only: excludes category, traversal, pool, and ChildArc events
/// explicitly contributed by [`compose`]. Native defaults need their own
/// source-backed contracts; a type's Clone cost is not its Default cost.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LocalReceipt {
    pub construction: Counts,
    pub extraction: Counts,
    pub field_glue: Counts,
}

impl LocalReceipt {
    pub const ZERO: Self = Self {
        construction: Counts::ZERO,
        extraction: Counts::ZERO,
        field_glue: Counts::ZERO,
    };

    /// Combine independently described fields without merging their phases.
    pub const fn checked_add(self, other: Self) -> Result<Self, ReceiptOverflow> {
        Ok(Self {
            construction: checked_receipt!(self.construction.checked_add(other.construction)),
            extraction: checked_receipt!(self.extraction.checked_add(other.extraction)),
            field_glue: checked_receipt!(self.field_glue.checked_add(other.field_glue)),
        })
    }
}

/// Construction and cleanup of one specific native default value.
///
/// Extraction is deliberately absent: replacing or iterating a field is an
/// operation of its generated constructor, not a property of `Default`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DefaultReceipt {
    pub construction: Counts,
    pub field_glue: Counts,
}

impl DefaultReceipt {
    pub const ZERO: Self = Self {
        construction: Counts::ZERO,
        field_glue: Counts::ZERO,
    };

    pub const fn checked_add(self, other: Self) -> Result<Self, ReceiptOverflow> {
        Ok(Self {
            construction: checked_receipt!(self.construction.checked_add(other.construction)),
            field_glue: checked_receipt!(self.field_glue.checked_add(other.field_glue)),
        })
    }

    pub const fn into_local(self) -> LocalReceipt {
        LocalReceipt {
            construction: self.construction,
            extraction: Counts::ZERO,
            field_glue: self.field_glue,
        }
    }
}

/// Explicit, source-backed contract for an approved native type's default.
///
/// This describes `Self::default()` and cleanup of that freshly constructed
/// value only. It says nothing about copying or destroying arbitrary instances.
/// There is no blanket `Default` implementation and no type-name classifier.
/// A compound contract must propagate arithmetic overflow without saturating.
pub trait BindingDefaultReceipt: Default {
    const DEFAULT_RECEIPT: Result<DefaultReceipt, ReceiptOverflow>;
}

/// Infer the resolved payload type from the actual selected unary constructor.
/// The function pointer is never called and no default value is constructed.
///
/// ```
/// use mettail_runtime::binding_receipt::{default_local_for, LocalReceipt, ReceiptOverflow};
/// enum Category { Text(String) }
/// const RECEIPT: Result<LocalReceipt, ReceiptOverflow> = default_local_for(Category::Text);
/// assert!(RECEIPT.is_ok());
/// ```
///
/// A suggestive name and `Default` do not supply a receipt contract:
///
/// ```compile_fail
/// use mettail_runtime::binding_receipt::default_local_for;
/// #[derive(Default)]
/// struct CustomBigInt;
/// enum Category { Integer(CustomBigInt) }
/// let _ = default_local_for(Category::Integer);
/// ```
pub const fn default_local_for<T: BindingDefaultReceipt, C>(
    _constructor: fn(T) -> C,
) -> Result<LocalReceipt, ReceiptOverflow> {
    Ok(checked_receipt!(T::DEFAULT_RECEIPT).into_local())
}

/// Infer a regular field's actual type through a nonexecuted borrowed projection.
/// This avoids reconstructing enum payload types independently in the emitter.
pub const fn default_field_local<C, T: BindingDefaultReceipt>(
    _field: for<'a> fn(&'a C) -> &'a T,
) -> Result<LocalReceipt, ReceiptOverflow> {
    Ok(checked_receipt!(T::DEFAULT_RECEIPT).into_local())
}

/// Separate construction and cleanup contexts from the finite-recipe model.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Receipt {
    pub construction: Counts,
    pub extraction: Counts,
    pub active_drop: Counts,
    pub popped_drop: Counts,
    pub normal_drop: Counts,
}

impl Receipt {
    pub const ZERO: Self = Self {
        construction: Counts::ZERO,
        extraction: Counts::ZERO,
        active_drop: Counts::ZERO,
        popped_drop: Counts::ZERO,
        normal_drop: Counts::ZERO,
    };
}

/// Compose already-computed children without recursion or allocation.
///
/// Each child field contributes once, including repeated dependencies. Summing
/// the child projections precedes applying the five model recurrences. Every
/// nonnegative sum is checked; overflow returns no partial receipt. Arbitrary
/// externally constructed receipts need not satisfy the model's invariants.
pub const fn compose(
    local: LocalReceipt,
    children: &[Receipt],
) -> Result<Receipt, ReceiptOverflow> {
    let arity = children.len();
    let mut result = Receipt::ZERO;
    let mut event_index = 0;
    while event_index < EVENT_COUNT {
        let event = EVENTS[event_index];
        let mut child_c = 0;
        let mut child_a = 0;
        let mut child_p = 0;
        let mut child_n = 0;
        let mut child_index = 0;
        while child_index < children.len() {
            let child = &children[child_index];
            child_c = checked_receipt!(add(event, child_c, child.construction.get(event)));
            child_a = checked_receipt!(add(event, child_a, child.active_drop.get(event)));
            child_p = checked_receipt!(add(event, child_p, child.popped_drop.get(event)));
            child_n = checked_receipt!(add(event, child_n, child.normal_drop.get(event)));
            child_index += 1;
        }

        let enter = occurrences(event, Event::EnterDestructor, 1);
        let pop = occurrences(event, Event::PopDropTask, 1);
        let arcs = occurrences(event, Event::AllocateArc, arity);
        let x = checked_receipt!(sum(
            event,
            &[
                occurrences(event, Event::ExtractChildren, 1),
                local.extraction.get(event),
                arcs,
                occurrences(event, Event::CheckArcOwner, arity),
                occurrences(event, Event::PushDropTask, arity),
                child_c,
            ]
        ));
        let glue = checked_receipt!(sum(
            event,
            &[local.field_glue.get(event), occurrences(event, Event::ReleaseFieldArc, arity),]
        ));

        result.construction.0[event_index] = checked_receipt!(sum(
            event,
            &[
                occurrences(event, Event::ConstructCategory, 1),
                local.construction.get(event),
                arcs,
                child_c,
            ]
        ));
        result.extraction.0[event_index] = x;
        result.active_drop.0[event_index] = checked_receipt!(sum(event, &[enter, glue, child_a]));
        result.popped_drop.0[event_index] =
            checked_receipt!(sum(event, &[pop, x, child_p, enter, glue, child_a]));
        result.normal_drop.0[event_index] = checked_receipt!(sum(
            event,
            &[
                enter,
                occurrences(event, Event::AcquirePool, 1),
                x,
                child_p,
                pop,
                occurrences(event, Event::ReturnPool, 1),
                glue,
                child_n,
            ]
        ));
        event_index += 1;
    }
    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::*;

    const LEAF: Result<Receipt, ReceiptOverflow> = compose(LocalReceipt::ZERO, &[]);
    const UNARY: Result<Receipt, ReceiptOverflow> = match LEAF {
        Ok(child) => compose(LocalReceipt::ZERO, &[child]),
        Err(error) => Err(error),
    };

    fn counts(entries: &[(Event, usize)]) -> Counts {
        entries.iter().fold(Counts::ZERO, |total, &(event, count)| {
            total
                .checked_add(Counts::singleton(event, count))
                .expect("small fixture counts")
        })
    }

    #[test]
    fn leaf_recurrence_and_const_evaluation() {
        use Event::*;
        let leaf = LEAF.expect("constant leaf receipt");
        assert_eq!(leaf.construction, counts(&[(ConstructCategory, 1)]));
        assert_eq!(leaf.extraction, counts(&[(ExtractChildren, 1)]));
        assert_eq!(leaf.active_drop, counts(&[(EnterDestructor, 1)]));
        assert_eq!(
            leaf.popped_drop,
            counts(&[(PopDropTask, 1), (ExtractChildren, 1), (EnterDestructor, 1),])
        );
        assert_eq!(
            leaf.normal_drop,
            counts(&[
                (EnterDestructor, 1),
                (AcquirePool, 1),
                (ExtractChildren, 1),
                (PopDropTask, 1),
                (ReturnPool, 1),
            ])
        );
        assert_eq!(UNARY, compose(LocalReceipt::ZERO, &[leaf]));
    }

    #[test]
    fn unary_and_repeated_children_have_exact_receipts() {
        use Event::*;
        let leaf = LEAF.expect("constant leaf receipt");
        for (arity, receipt) in [
            (1, UNARY.expect("constant unary receipt")),
            (2, compose(LocalReceipt::ZERO, &[leaf, leaf]).expect("repeated leaf receipt")),
        ] {
            assert_eq!(
                receipt.construction,
                counts(&[(ConstructCategory, 1 + arity), (AllocateArc, arity),])
            );
            assert_eq!(
                receipt.extraction,
                counts(&[
                    (ExtractChildren, 1),
                    (AllocateArc, arity),
                    (CheckArcOwner, arity),
                    (PushDropTask, arity),
                    (ConstructCategory, arity),
                ])
            );
            assert_eq!(
                receipt.active_drop,
                counts(&[(EnterDestructor, 1 + arity), (ReleaseFieldArc, arity),])
            );
            assert_eq!(
                receipt.popped_drop,
                counts(&[
                    (PopDropTask, 1 + arity),
                    (ExtractChildren, 1 + arity),
                    (EnterDestructor, 1 + 2 * arity),
                    (ReleaseFieldArc, arity),
                    (AllocateArc, arity),
                    (CheckArcOwner, arity),
                    (PushDropTask, arity),
                    (ConstructCategory, arity),
                ])
            );
            assert_eq!(
                receipt.normal_drop,
                counts(&[
                    (EnterDestructor, 1 + 2 * arity),
                    (AcquirePool, 1 + arity),
                    (ReturnPool, 1 + arity),
                    (PopDropTask, 1 + 2 * arity),
                    (ExtractChildren, 1 + 2 * arity),
                    (ReleaseFieldArc, arity),
                    (AllocateArc, arity),
                    (CheckArcOwner, arity),
                    (PushDropTask, arity),
                    (ConstructCategory, arity),
                ])
            );
        }
    }

    #[test]
    fn local_components_flow_into_the_correct_receipts() {
        use Event::*;
        let receipt = compose(
            LocalReceipt {
                construction: Counts::singleton(NativeWork, 2),
                extraction: Counts::singleton(HandleField, 3),
                field_glue: Counts::singleton(OwnedByte, 5),
            },
            &[],
        )
        .expect("small local receipt");
        assert_eq!(receipt.construction.get(NativeWork), 2);
        assert_eq!(receipt.extraction.get(HandleField), 3);
        assert_eq!(receipt.active_drop.get(OwnedByte), 5);
        assert_eq!(receipt.popped_drop.get(HandleField), 3);
        assert_eq!(receipt.popped_drop.get(OwnedByte), 5);
        assert_eq!(receipt.normal_drop.get(HandleField), 3);
        assert_eq!(receipt.normal_drop.get(OwnedByte), 5);
    }

    #[test]
    fn local_field_addition_keeps_phases_separate_and_checks_each() {
        let field = LocalReceipt {
            construction: Counts::singleton(Event::NativeWork, 2),
            extraction: Counts::singleton(Event::NativeWork, 3),
            field_glue: Counts::singleton(Event::NativeWork, 5),
        };
        let repeated = field.checked_add(field).expect("small repeated fields");
        assert_eq!(repeated.construction.get(Event::NativeWork), 4);
        assert_eq!(repeated.extraction.get(Event::NativeWork), 6);
        assert_eq!(repeated.field_glue.get(Event::NativeWork), 10);
        for phase in 0..3 {
            let maximum = Counts::singleton(Event::NativeWork, usize::MAX);
            let mut overflow = LocalReceipt::ZERO;
            match phase {
                0 => overflow.construction = maximum,
                1 => overflow.extraction = maximum,
                _ => overflow.field_glue = maximum,
            }
            assert_eq!(
                overflow.checked_add(field),
                Err(ReceiptOverflow { event: Event::NativeWork })
            );
        }
    }

    #[test]
    fn overflow_is_typed_and_inputs_remain_unchanged() {
        let maximum = Counts::singleton(Event::NativeWork, usize::MAX);
        let overflow = Err(ReceiptOverflow { event: Event::NativeWork });
        assert_eq!(maximum.checked_add(Counts::singleton(Event::NativeWork, 1)), overflow);
        assert_eq!(maximum.checked_scale(2), overflow);
        assert_eq!(maximum.checked_scale(0), Ok(Counts::ZERO));
        assert_eq!(maximum.checked_scale(1), Ok(maximum));
        assert_eq!(maximum.get(Event::NativeWork), usize::MAX);
        let local = LocalReceipt {
            construction: Counts::singleton(Event::ConstructCategory, usize::MAX),
            ..LocalReceipt::ZERO
        };
        assert_eq!(compose(local, &[]), Err(ReceiptOverflow { event: Event::ConstructCategory }));
        let child = Receipt { construction: maximum, ..Receipt::ZERO };
        assert_eq!(
            compose(LocalReceipt::ZERO, &[child, child]),
            Err(ReceiptOverflow { event: Event::NativeWork })
        );
    }

    #[test]
    fn unused_child_extraction_does_not_cause_spurious_overflow() {
        let child = Receipt {
            extraction: Counts::singleton(Event::NativeWork, usize::MAX),
            ..Receipt::ZERO
        };
        assert_eq!(
            compose(LocalReceipt::ZERO, &[child, child]),
            compose(LocalReceipt::ZERO, &[Receipt::ZERO, Receipt::ZERO])
        );
    }

    #[test]
    fn deep_dependency_chain_uses_constant_call_stack() {
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(|| {
                let mut receipt = LEAF.expect("constant leaf receipt");
                // Cubic normal-cleanup growth can overflow earlier on 32-bit
                // targets. A typed refusal remains valid there.
                for depth in 0..20_000 {
                    match compose(LocalReceipt::ZERO, &[receipt]) {
                        Ok(next) => {
                            for event in EVENTS {
                                assert!(next.active_drop.get(event) <= next.normal_drop.get(event));
                            }
                            receipt = next;
                        },
                        Err(_) => {
                            assert!(usize::BITS < 64, "20,000-level receipt fits a 64-bit target");
                            assert!(depth > 16, "exercise a chain, not only a leaf");
                            break;
                        },
                    }
                }
            })
            .expect("spawn bounded-stack test")
            .join()
            .expect("receipt worker");
    }
}
