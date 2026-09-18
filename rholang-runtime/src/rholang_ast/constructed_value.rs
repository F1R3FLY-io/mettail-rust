//! Constructor-time annotations of the existing owned node values.
//!
//! The receipt is retained shape, not permission to allocate or execute. Each
//! caller still admits the native constructor before calling these adapters.
//! No constructor below scans its finished Par or changes its native fields.

use super::construction_receipt::{NativeHead, NativeReceipt, ReceiptError};
use super::{preparation_scope, RholangAstLowerError, StorageReservation, Target};
use mettail_rholang_frontend::construction::CheckedBoundReference;
use models::rhoapi::Par;
use models::rust::utils::new_elist_par;

pub(crate) struct ConstructedValue {
    pub(crate) par: Par,
    pub(crate) receipt: NativeReceipt,
}

pub(super) fn receipt_error(error: ReceiptError) -> RholangAstLowerError {
    match error {
        ReceiptError::Overflow => RholangAstLowerError::PreparationSizeOverflow,
        ReceiptError::IncompleteMapPair { .. } => {
            RholangAstLowerError::UnsupportedProc("native map receipt has an incomplete pair")
        },
    }
}

impl ConstructedValue {
    pub(super) fn empty() -> Self {
        Self {
            par: Target::empty(),
            receipt: NativeReceipt::empty(),
        }
    }

    pub(super) fn integer(value: i64) -> Result<Self, RholangAstLowerError> {
        let receipt = NativeReceipt::construct(NativeHead::Plain, 0, []).map_err(receipt_error)?;
        Ok(Self { par: Target::integer(value), receipt })
    }

    pub(super) fn boolean(value: bool) -> Result<Self, RholangAstLowerError> {
        let receipt = NativeReceipt::construct(NativeHead::Plain, 0, []).map_err(receipt_error)?;
        Ok(Self { par: Target::boolean(value), receipt })
    }

    pub(crate) fn text(value: String) -> Result<Self, RholangAstLowerError> {
        let receipt = NativeReceipt::construct(NativeHead::Payload { bytes: value.len() }, 0, [])
            .map_err(receipt_error)?;
        Ok(Self { par: Target::text(value), receipt })
    }

    pub(super) fn bound(reference: CheckedBoundReference) -> Result<Self, RholangAstLowerError> {
        let receipt = NativeReceipt::construct(NativeHead::Plain, reference.metadata_bytes(), [])
            .map_err(receipt_error)?;
        Ok(Self { par: Target::bound(reference), receipt })
    }

    pub(super) fn wildcard(connective: bool) -> Result<Self, RholangAstLowerError> {
        let receipt = NativeReceipt::construct(NativeHead::Plain, 0, []).map_err(receipt_error)?;
        Ok(Self {
            par: Target::wildcard(connective),
            receipt,
        })
    }

    /// The caller admits native copies and cleanup before transferring operands;
    /// this method computes only the retained-output annotation.
    pub(super) fn append(self, right: Self) -> Result<Self, RholangAstLowerError> {
        let receipt = self.receipt.append(&right.receipt).map_err(receipt_error)?;
        Ok(Self {
            par: Target::append(self.par, right.par),
            receipt,
        })
    }

    /// DDL wire lists intentionally retain a closed summary. Child metadata is
    /// owned inside the list; it must not become the list's outer summary.
    pub(crate) fn closed_list(
        children: Vec<Self>,
        reserve: &mut StorageReservation<'_>,
    ) -> Result<Self, RholangAstLowerError> {
        let count = children.len();
        let steps = count
            .checked_add(1)
            .ok_or(RholangAstLowerError::PreparationSizeOverflow)?;
        preparation_scope::reserve_parts(steps, 0, 0, reserve)?;
        let receipt = NativeReceipt::construct(
            NativeHead::List { remainder: false },
            0,
            children.iter().map(|child| &child.receipt),
        )
        .map_err(receipt_error)?;
        // A consuming projection, not a clone of any child or a new tree walk.
        // Pay its roster and moves even if Vec's in-place collection reuses it.
        preparation_scope::reserve_parts(steps, steps, 0, reserve)?;
        let pars = children.into_iter().map(|child| child.par).collect();
        Ok(Self {
            par: new_elist_par(pars, Vec::new(), false, None, Vec::new(), false),
            receipt,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::super::construction_receipt::NativeCounts;
    use super::*;
    use mettail_rholang_codegen::DynamicReflectionError;
    use prost::Message;

    #[test]
    fn scalar_annotations_preserve_native_bytes_and_bound_metadata() {
        let values = [
            (ConstructedValue::empty(), Target::empty(), 0, 0, 0),
            (ConstructedValue::integer(-42).expect("integer"), Target::integer(-42), 1, 0, 0),
            (
                ConstructedValue::boolean(true).expect("boolean"),
                Target::boolean(true),
                1,
                0,
                0,
            ),
            (
                ConstructedValue::text("λ\\n".into()).expect("text"),
                Target::text("λ\\n".into()),
                1,
                4,
                0,
            ),
            (
                ConstructedValue::wildcard(true).expect("wildcard"),
                Target::wildcard(true),
                1,
                0,
                0,
            ),
            (
                ConstructedValue::bound(CheckedBoundReference::new(18, 17).expect("reference"))
                    .expect("bound"),
                Target::bound(CheckedBoundReference::new(18, 17).expect("reference")),
                1,
                0,
                18,
            ),
        ];
        for (actual, expected, heads, payload_bytes, outer_metadata_bytes) in values {
            assert_eq!(actual.par.encode_to_vec(), expected.encode_to_vec());
            assert_eq!(actual.receipt.outer_metadata_bytes, outer_metadata_bytes);
            assert_eq!(
                actual.receipt.owned,
                NativeCounts {
                    heads,
                    payload_bytes,
                    ..NativeCounts::default()
                }
            );
        }
    }

    #[test]
    fn closed_list_retains_child_metadata_without_union_or_copy() {
        let child = ConstructedValue::bound(CheckedBoundReference::new(18, 17).expect("reference"))
            .expect("bound");
        let expected = new_elist_par(vec![child.par.clone()], vec![], false, None, vec![], false);
        let actual = ConstructedValue::closed_list(vec![child], &mut |_, _| Ok(()))
            .expect("annotated closed list");
        assert_eq!(actual.par.encode_to_vec(), expected.encode_to_vec());
        assert_eq!(actual.receipt.outer_metadata_bytes, 0);
        assert_eq!(
            actual.receipt.owned,
            NativeCounts {
                heads: 2,
                metadata_bytes: 18,
                descendant_pars: 1,
                ..NativeCounts::default()
            }
        );
    }

    #[test]
    fn asymmetric_append_preserves_native_bytes_and_separates_copy_from_retained_counts() {
        let left = ConstructedValue::closed_list(
            vec![ConstructedValue::text("left".into()).expect("text")],
            &mut |_, _| Ok(()),
        )
        .expect("list");
        let right = ConstructedValue::bound(CheckedBoundReference::new(18, 17).expect("reference"))
            .expect("bound");
        let expected = Target::append(left.par.clone(), right.par.clone());
        let copied = left
            .receipt
            .append_copy_counts(&right.receipt)
            .expect("copy shape");
        let result = left.append(right).expect("append");
        assert_eq!(result.par.encode_to_vec(), expected.encode_to_vec());
        assert_eq!(result.receipt.outer_metadata_bytes, 18);
        assert_eq!(result.receipt.owned.heads, 3);
        assert_eq!(result.receipt.owned.descendant_pars, 1);
        assert_eq!(result.receipt.owned.payload_bytes, 4);
        assert_eq!(copied.heads, 5);
        assert_eq!(copied.descendant_pars, 2);
        assert_eq!(copied.payload_bytes, 8);
    }

    #[test]
    fn receipt_and_projection_reservations_refuse_before_returning_a_value() {
        for cut in 0..2 {
            let mut calls = 0;
            let result = ConstructedValue::closed_list(
                vec![ConstructedValue::text("payload".into()).expect("text")],
                &mut |_, _| {
                    let call = calls;
                    calls += 1;
                    if call == cut {
                        Err(RholangAstLowerError::Preparation(DynamicReflectionError::Cancelled))
                    } else {
                        Ok(())
                    }
                },
            );
            assert!(matches!(
                result,
                Err(RholangAstLowerError::Preparation(DynamicReflectionError::Cancelled))
            ));
            assert_eq!(calls, cut + 1);
        }
    }

    #[test]
    fn annotation_overflow_refuses_before_projecting_owned_children() {
        let mut calls = 0;
        let child = ConstructedValue {
            par: Target::text("owned until refusal".into()),
            receipt: NativeReceipt {
                outer_metadata_bytes: 0,
                owned: NativeCounts {
                    descendant_pars: usize::MAX,
                    ..NativeCounts::default()
                },
            },
        };
        let result = ConstructedValue::closed_list(vec![child], &mut |_, _| {
            calls += 1;
            Ok(())
        });
        assert!(matches!(result, Err(RholangAstLowerError::PreparationSizeOverflow)));
        assert_eq!(calls, 1, "overflow precedes the native-child projection");
    }

    #[test]
    fn annotation_work_and_storage_obey_exact_and_one_under_limits() {
        let mut required = (0, 0);
        ConstructedValue::closed_list(
            vec![ConstructedValue::text("payload".into()).expect("text")],
            &mut |work, units| {
                required.0 += work;
                required.1 += units;
                Ok(())
            },
        )
        .expect("measure the two annotation actions");
        for (work, units, success) in [
            (required.0, required.1, true),
            (required.0 - 1, required.1, false),
            (required.0, required.1 - 1, false),
            (0, required.1, false),
            (required.0, 0, false),
        ] {
            let mut remaining = (work, units);
            let result = ConstructedValue::closed_list(
                vec![ConstructedValue::text("payload".into()).expect("text")],
                &mut |work, units| {
                    let next = remaining
                        .0
                        .checked_sub(work)
                        .zip(remaining.1.checked_sub(units));
                    match next {
                        Some(next) => {
                            remaining = next;
                            Ok(())
                        },
                        None => Err(RholangAstLowerError::Preparation(
                            DynamicReflectionError::Cancelled,
                        )),
                    }
                },
            );
            assert_eq!(result.is_ok(), success);
            if success {
                assert_eq!(remaining, (0, 0));
            }
        }
    }

    #[test]
    fn deeply_nested_closed_lists_accumulate_receipts_and_drop_on_small_stack() {
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(|| {
                let mut value = ConstructedValue::text("λ".into()).expect("leaf");
                for _ in 0..20_000 {
                    value = ConstructedValue::closed_list(vec![value], &mut |_, _| Ok(()))
                        .expect("list");
                }
                assert_eq!(value.receipt.owned.heads, 20_001);
                assert_eq!(value.receipt.owned.descendant_pars, 20_000);
                assert_eq!(value.receipt.owned.payload_bytes, 2);
                drop(value);
            })
            .expect("small-stack worker")
            .join()
            .expect("iterative construction and native drop");
    }
}
