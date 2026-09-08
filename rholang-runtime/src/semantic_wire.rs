//! Bounded structural transport for installed semantic operations.
//!
//! Scalar schedule v1 reserves sixteen logical bytes for a materialized value
//! descriptor and visits it once. A wide integer additionally materializes and
//! visits nine signed big-endian bytes. These are logical boundary reservations,
//! not Rust layout, protobuf size, physical RSS or semantic execution charges.
//! Scalar decoding borrows its input and reserves no new payload. All callers retain
//! one cumulative `ReflectedCodecBudget` across the complete operation.

use crate::language_install::{exact_expr, signed_i128};
use mettail_rholang_codegen::{DynamicReflectionError, ReflectedCodecBudget};
use models::rhoapi::{expr::ExprInstance, Par};
use models::rust::utils::{new_gbigint_expr, new_gint_par};
use num_bigint::BigInt;

mod completion;
mod ordering;
mod receipt;
mod request;
pub use completion::{decode_limits_v1, decode_usage_v1, encode_limits_v1, SemanticWireUsage};
pub(crate) use completion::{CompletionPermit, DiagnosticDomain, ReplyBody, StickyCancellation};
pub(crate) use ordering::sort_results;
pub(crate) use receipt::encode_results_v1;
pub(crate) use receipt::reserve_reply_payload;
pub use receipt::{decode_receipt_v1, encode_receipt_v1};
pub(crate) use request::OwnedSemanticRequest;

const VALUE_DESCRIPTOR_BYTES: usize = 16;

#[derive(Debug, PartialEq, Eq)]
pub enum SemanticWireError {
    Shape(&'static str),
    IntegerRange,
    NonCanonicalInteger,
    Resource(DynamicReflectionError),
}

impl From<DynamicReflectionError> for SemanticWireError {
    fn from(error: DynamicReflectionError) -> Self {
        Self::Resource(error)
    }
}

/// Encode the full unsigned-64 domain without narrowing it to signed-64.
/// The boundary above i64::MAX always has exactly nine signed positive bytes.
pub fn encode_u64<C: FnMut() -> bool>(
    value: u64,
    budget: &mut ReflectedCodecBudget<'_, C>,
) -> Result<Par, SemanticWireError> {
    match i64::try_from(value) {
        Ok(small) => {
            budget.charge(1, VALUE_DESCRIPTOR_BYTES)?;
            Ok(new_gint_par(small, Vec::new(), false))
        },
        Err(_) => {
            budget.charge(10, VALUE_DESCRIPTOR_BYTES + 9)?;
            Ok(Par::default()
                .with_exprs(vec![new_gbigint_expr(BigInt::from(value).to_signed_bytes_be())]))
        },
    }
}

/// Read only canonical scalar envelopes. In particular, the bounded signed
/// decoder is never invoked on an arbitrarily long caller-provided BigInt.
pub fn decode_u64<C: FnMut() -> bool>(
    value: &Par,
    budget: &mut ReflectedCodecBudget<'_, C>,
) -> Result<u64, SemanticWireError> {
    budget.charge(1, 0)?;
    if !value.locally_free.is_empty() || value.connective_used {
        return Err(SemanticWireError::Shape("integer has nonliteral metadata"));
    }
    match exact_expr(value) {
        Some(ExprInstance::GInt(value)) => {
            u64::try_from(*value).map_err(|_| SemanticWireError::IntegerRange)
        },
        Some(ExprInstance::GBigInt(bytes)) => {
            if bytes.len() != 9 || bytes[0] != 0 {
                return Err(SemanticWireError::NonCanonicalInteger);
            }
            budget.charge(9, 0)?;
            let value = signed_i128(bytes)
                .and_then(|value| u64::try_from(value).ok())
                .ok_or(SemanticWireError::IntegerRange)?;
            if value <= i64::MAX as u64 {
                return Err(SemanticWireError::NonCanonicalInteger);
            }
            Ok(value)
        },
        _ => Err(SemanticWireError::Shape("expected a single integer literal")),
    }
}

/// Checked dense-coordinate conversion; truncation is never an ABI rule.
pub fn decode_u32<C: FnMut() -> bool>(
    value: &Par,
    budget: &mut ReflectedCodecBudget<'_, C>,
) -> Result<u32, SemanticWireError> {
    u32::try_from(decode_u64(value, budget)?).map_err(|_| SemanticWireError::IntegerRange)
}

/// Checked host-index conversion, including on narrower host architectures.
pub fn decode_usize<C: FnMut() -> bool>(
    value: &Par,
    budget: &mut ReflectedCodecBudget<'_, C>,
) -> Result<usize, SemanticWireError> {
    usize::try_from(decode_u64(value, budget)?).map_err(|_| SemanticWireError::IntegerRange)
}

#[cfg(test)]
mod tests {
    use super::*;
    use models::rust::utils::new_gint_expr;

    fn round_trip(value: u64) {
        let mut work = 7;
        let mut cancel = || false;
        let wide = value > i64::MAX as u64;
        let units = if wide { 10 } else { 1 };
        let bytes = if wide { 25 } else { 16 };
        let mut budget = ReflectedCodecBudget::new(&mut work, 7 + 2 * units, bytes, &mut cancel);
        let encoded = encode_u64(value, &mut budget).expect("exact encoding allowance");
        assert_eq!(budget.remaining_bytes(), 0);
        match exact_expr(&encoded).expect("one literal") {
            ExprInstance::GInt(actual) => {
                assert!(!wide);
                assert_eq!(*actual as u64, value);
            },
            ExprInstance::GBigInt(actual) => {
                assert!(wide);
                assert_eq!(actual.len(), 9);
                assert_eq!(actual[0], 0);
                assert!(actual[1] >= 128, "the zero sign byte is necessary");
                assert_eq!(&actual[1..], value.to_be_bytes());
            },
            _ => panic!("wrong scalar variant"),
        }
        assert_eq!(decode_u64(&encoded, &mut budget), Ok(value));
        assert_eq!(budget.work_used(), 7 + 2 * units);
    }

    #[test]
    fn semantic_wire_scalar_full_width_round_trips() {
        for value in [
            0,
            1,
            127,
            128,
            255,
            256,
            u32::MAX as u64,
            u32::MAX as u64 + 1,
            i64::MAX as u64 - 1,
            i64::MAX as u64,
            i64::MAX as u64 + 1,
            u64::MAX,
        ] {
            round_trip(value);
        }
        let mut value = 0x243f6a8885a308d3_u64;
        for _ in 0..10_000 {
            value = value
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            round_trip(value);
        }
    }

    #[test]
    fn semantic_wire_scalar_rejects_noncanonical_and_executable_envelopes() {
        let bigint = |bytes| Par::default().with_exprs(vec![new_gbigint_expr(bytes)]);
        let mut malformed = vec![
            Par::default(),
            new_gint_par(-1, Vec::new(), false),
            bigint(vec![]),
            bigint(vec![0]),
            bigint(vec![0; 8]),
            bigint(vec![0; 9]),
            bigint(vec![0; 10]),
            bigint(vec![0xff; 9]),
            bigint(vec![0; 100_000]),
        ];
        let integer = new_gint_par(7, Vec::new(), false);
        let mut sidecar = integer.clone();
        sidecar.sends.push(Default::default());
        malformed.push(sidecar);
        let mut sidecar = integer.clone();
        sidecar.conditionals.push(Default::default());
        malformed.push(sidecar);
        let mut sidecar = integer.clone();
        sidecar.exprs.push(new_gint_expr(8));
        malformed.push(sidecar);
        let mut metadata = integer.clone();
        metadata.locally_free.push(1);
        malformed.push(metadata);
        let mut metadata = integer;
        metadata.connective_used = true;
        malformed.push(metadata);
        for value in malformed {
            let mut work = 0;
            let mut cancel = || false;
            let mut budget = ReflectedCodecBudget::new(&mut work, 10, 0, &mut cancel);
            assert!(decode_u64(&value, &mut budget).is_err());
            assert!(budget.work_used() <= 10);
        }
    }

    #[test]
    fn semantic_wire_scalar_preserves_limits_and_cancellation() {
        for (value, units, bytes) in [(1, 1, 16), (u64::MAX, 10, 25)] {
            for (work_limit, byte_limit, expected) in [
                (7 + units - 1, bytes, DynamicReflectionError::WorkLimit),
                (7 + units, bytes - 1, DynamicReflectionError::PayloadByteLimit),
            ] {
                let mut work = 7;
                let mut cancel = || false;
                let mut budget =
                    ReflectedCodecBudget::new(&mut work, work_limit, byte_limit, &mut cancel);
                assert_eq!(
                    encode_u64(value, &mut budget),
                    Err(SemanticWireError::Resource(expected))
                );
                assert_eq!((budget.work_used(), budget.remaining_bytes()), (7, byte_limit));
            }
            let mut work = 7;
            let mut cancel = || true;
            let mut budget = ReflectedCodecBudget::new(&mut work, 7 + units, bytes, &mut cancel);
            assert_eq!(
                encode_u64(value, &mut budget),
                Err(SemanticWireError::Resource(DynamicReflectionError::Cancelled))
            );
            assert_eq!(budget.work_used(), 7);
        }
        let value = Par::default()
            .with_exprs(vec![new_gbigint_expr(BigInt::from(u64::MAX).to_signed_bytes_be())]);
        for stop in [1, 2] {
            let mut calls = 0;
            let mut work = 7;
            let mut cancel = || {
                calls += 1;
                calls == stop
            };
            let mut budget = ReflectedCodecBudget::new(&mut work, 17, 0, &mut cancel);
            assert_eq!(
                decode_u64(&value, &mut budget),
                Err(SemanticWireError::Resource(DynamicReflectionError::Cancelled))
            );
            assert_eq!(budget.work_used(), if stop == 1 { 7 } else { 8 });
        }
    }

    #[test]
    fn semantic_wire_scalar_checks_coordinate_and_host_width() {
        for value in [u32::MAX as u64, u32::MAX as u64 + 1, u64::MAX] {
            let mut work = 0;
            let mut cancel = || false;
            let mut budget = ReflectedCodecBudget::new(&mut work, 100, 25, &mut cancel);
            let encoded = encode_u64(value, &mut budget).expect("encode");
            assert_eq!(
                decode_u32(&encoded, &mut budget),
                u32::try_from(value).map_err(|_| SemanticWireError::IntegerRange)
            );
            assert_eq!(
                decode_usize(&encoded, &mut budget),
                usize::try_from(value).map_err(|_| SemanticWireError::IntegerRange)
            );
        }
    }
}
