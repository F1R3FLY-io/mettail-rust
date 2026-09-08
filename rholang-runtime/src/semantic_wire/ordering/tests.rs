use super::*;
use crate::language_install::{exact_expr, exact_list, wire_list};
use crate::semantic_service::tests::transport_receipt;
use crate::semantic_wire::{decode_receipt_v1, encode_receipt_v1, encode_u64};
use mettail_dovetail_runtime::SemanticIntrinsicOpcodeV1;
use mettail_grammar_core::{SemanticEffectClassV1, TheorySortId};
use models::rhoapi::{expr::ExprInstance, Par};
use models::rust::utils::{new_gbytearray_par, new_gint_par};
use num_bigint::BigInt;

// Independent wire-level oracle. Its recursion is bounded by the fixed receipt
// schema; production comparison does not construct or traverse these keys.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Key {
    UInt(BigInt),
    Bytes(Vec<u8>),
    Tuple(Vec<Key>),
}

impl Key {
    fn read(value: &Par) -> Self {
        if let Some(children) = exact_list(value) {
            return Self::Tuple(children.iter().map(Self::read).collect());
        }
        match exact_expr(value).unwrap() {
            ExprInstance::GInt(n) => Self::UInt(BigInt::from(*n)),
            ExprInstance::GBigInt(n) => Self::UInt(BigInt::from_signed_bytes_be(n)),
            ExprInstance::GByteArray(b) => Self::Bytes(b.clone()),
            other => panic!("unexpected receipt field {other:?}"),
        }
    }

    fn wire(&self) -> Par {
        match self {
            Self::UInt(n) => {
                with_budget(|budget| encode_u64(u64::try_from(n).unwrap(), budget)).unwrap()
            },
            Self::Bytes(b) => new_gbytearray_par(b.clone(), Vec::new(), false),
            Self::Tuple(children) => wire_list(children.iter().map(Self::wire).collect()),
        }
    }

    // Mutate every leaf, including late fields in every duplicate proof. Invalid
    // enum tags and fingerprint lengths are rejected by the existing decoder.
    fn variants(&self) -> Vec<Self> {
        match self {
            Self::UInt(n) => [0, 1, u32::MAX as u64, i64::MAX as u64, u64::MAX]
                .into_iter()
                .map(BigInt::from)
                .filter(|v| v != n)
                .map(Self::UInt)
                .collect(),
            Self::Bytes(b) => {
                let mut out = Vec::new();
                if !b.is_empty() {
                    let mut first = b.clone();
                    first[0] ^= 1;
                    out.push(Self::Bytes(first));
                    let mut last = b.clone();
                    *last.last_mut().unwrap() ^= 1;
                    out.push(Self::Bytes(last));
                    out.push(Self::Bytes(b[..b.len() - 1].to_vec()));
                }
                let mut longer = b.clone();
                longer.push(0);
                out.push(Self::Bytes(longer));
                out
            },
            Self::Tuple(children) => {
                let mut out = Vec::new();
                for (i, child) in children.iter().enumerate() {
                    for changed in child.variants() {
                        let mut fields = children.clone();
                        fields[i] = changed;
                        out.push(Self::Tuple(fields));
                    }
                }
                // Covers roster lengths/multiplicity as well as scalar leaves.
                if let Some(first) = children.first() {
                    let mut longer = children.clone();
                    longer.push(first.clone());
                    out.push(Self::Tuple(longer));
                    out.push(Self::Tuple(children[1..].to_vec()));
                }
                out
            },
        }
    }
}

fn with_budget<T>(f: impl FnOnce(&mut ReflectedCodecBudget<'_, fn() -> bool>) -> T) -> T {
    let mut work = 0;
    let mut cancel: fn() -> bool = || false;
    f(&mut ReflectedCodecBudget::new(&mut work, u64::MAX, usize::MAX, &mut cancel))
}

fn key(receipt: &SemanticTransitionReceipt) -> Key {
    Key::read(&with_budget(|b| encode_receipt_v1(receipt.clone(), b)).unwrap())
}

fn compare(a: &SemanticTransitionReceipt, b: &SemanticTransitionReceipt) -> Ordering {
    with_budget(|budget| Comparator { budget }.result_key(a, b)).unwrap()
}

#[test]
fn semantic_wire_order_matches_complete_wire_oracle_for_every_leaf() {
    let mut base = transport_receipt();
    base.resource = SemanticResourceReceipt::Checked {
        grade_sort: TheorySortId(4),
        grade: vec![5, 6],
        cost_image_fingerprint: [7; 32],
    };
    let original = key(&base);
    let mut checked = 0;
    let mut covered = [false; 13];
    for changed in original.variants() {
        let wire = changed.wire();
        let Ok(receipt) = with_budget(|b| decode_receipt_v1(&wire, b)) else {
            continue;
        };
        let expected = base
            .output
            .cmp(&receipt.output)
            .then_with(|| original.cmp(&changed));
        assert_eq!(compare(&base, &receipt), expected);
        assert_eq!(compare(&receipt, &base), expected.reverse());
        assert_ne!(expected, Ordering::Equal, "a changed field was lost");
        let (Key::Tuple(before), Key::Tuple(after)) = (&original, &changed) else {
            unreachable!()
        };
        for (index, (a, b)) in before.iter().zip(after).enumerate() {
            covered[index] |= a != b;
        }
        checked += 1;
    }
    assert_eq!(checked, 483, "valid mutations of the fixed all-variant fixture");
    assert!(covered.into_iter().all(|field| field), "missing receipt fields: {covered:?}");
    assert_eq!(compare(&base, &base), Ordering::Equal);

    let mut variants = Vec::new();
    for class in [
        SemanticEffectClassV1::Pure,
        SemanticEffectClassV1::Structural,
        SemanticEffectClassV1::Behavioral,
        SemanticEffectClassV1::Resource,
        SemanticEffectClassV1::External,
    ] {
        for opcode in [
            SemanticIntrinsicOpcodeV1::ExactTermEq,
            SemanticIntrinsicOpcodeV1::Utf8AtEnd,
            SemanticIntrinsicOpcodeV1::Utf8ScalarAt,
            SemanticIntrinsicOpcodeV1::Utf8Slice,
            SemanticIntrinsicOpcodeV1::CheckedNatAdd,
            SemanticIntrinsicOpcodeV1::Utf8ConcatMany,
        ] {
            for graded in [false, true] {
                let mut receipt = base.clone();
                receipt.effect_class = class;
                if !graded {
                    receipt.resource = SemanticResourceReceipt::NoSemanticGrade;
                }
                let SemanticPremiseReceipt::Intrinsic { receipt: intrinsic, .. } =
                    &mut receipt.premises[4]
                else {
                    unreachable!()
                };
                intrinsic.opcode = opcode;
                variants.push((key(&receipt), receipt));
            }
        }
    }
    for (ak, a) in &variants {
        for (bk, b) in &variants {
            assert_eq!(compare(a, b), ak.cmp(bk));
        }
    }
}

fn records(count: usize) -> Vec<SemanticServiceResult> {
    (0..count)
        .map(|i| {
            let mut receipt = transport_receipt();
            receipt.output = vec![((count - i) % 3) as u8];
            receipt.work = (i % 5) as u64;
            SemanticServiceResult {
                term: new_gint_par(i as i64, Vec::new(), false),
                receipt,
            }
        })
        .collect()
}

fn identities(values: &[SemanticServiceResult]) -> Vec<usize> {
    values
        .iter()
        .map(|r| match exact_expr(&r.term).unwrap() {
            ExprInstance::GInt(n) => *n as usize,
            _ => unreachable!(),
        })
        .collect()
}

#[test]
fn semantic_wire_sort_is_stable_canonical_and_moves_whole_records() {
    for count in 0..70 {
        let mut values = records(count);
        let originals: Vec<_> = values.iter().map(|r| r.receipt.clone()).collect();
        let keys: Vec<_> = originals
            .iter()
            .map(|r| (r.output.clone(), key(r)))
            .collect();
        let mut expected: Vec<_> = (0..count).collect();
        expected.sort_by(|&a, &b| keys[a].cmp(&keys[b]));
        with_budget(|b| sort_results(&mut values, b)).unwrap();
        assert_eq!(identities(&values), expected);
        for (result, &identity) in values.iter().zip(&expected) {
            assert_eq!(result.receipt, originals[identity]);
        }
        with_budget(|b| sort_results(&mut values, b)).unwrap();
        assert_eq!(identities(&values), expected);
    }
}

#[test]
fn semantic_wire_sort_permuted_inputs_preserve_canonical_receipts_and_local_stability() {
    let count = 37;
    let mut baseline = records(count);
    with_budget(|b| sort_results(&mut baseline, b)).unwrap();
    let canonical: Vec<_> = baseline.iter().map(|r| r.receipt.clone()).collect();
    for seed in 0..8 {
        let mut values = records(count);
        if seed == 0 {
            values.reverse();
        } else {
            let mut random = seed as u64;
            for end in (1..count).rev() {
                random = random.wrapping_mul(6364136223846793005).wrapping_add(1);
                values.swap(end, (random % (end + 1) as u64) as usize);
            }
        }
        let incoming = identities(&values);
        let mut expected = incoming.clone();
        let original = records(count);
        let keys: Vec<_> = original
            .iter()
            .map(|r| (r.receipt.output.clone(), key(&r.receipt)))
            .collect();
        expected.sort_by(|&a, &b| keys[a].cmp(&keys[b]));
        with_budget(|b| sort_results(&mut values, b)).unwrap();
        assert_eq!(identities(&values), expected);
        for (result, receipt) in values.iter().zip(&canonical) {
            assert_eq!(&result.receipt, receipt);
        }
        for key in &keys {
            let before: Vec<_> = incoming
                .iter()
                .copied()
                .filter(|&id| &keys[id] == key)
                .collect();
            let after: Vec<_> = identities(&values)
                .into_iter()
                .filter(|&id| &keys[id] == key)
                .collect();
            assert_eq!(after, before, "equal-key records lost their incoming order");
        }
    }
}

#[test]
fn semantic_wire_sort_exact_limits_and_every_cancellation_checkpoint() {
    let count = 7;
    let bytes = 32 + 16 * count;
    let mut values = records(count);
    let originals: Vec<_> = values.iter().map(|r| r.receipt.clone()).collect();
    let mut work = 7;
    let mut calls = 0;
    let mut cancel = || {
        calls += 1;
        false
    };
    let mut budget = ReflectedCodecBudget::new(&mut work, u64::MAX, bytes, &mut cancel);
    sort_results(&mut values, &mut budget).unwrap();
    assert_eq!(budget.remaining_bytes(), 0);
    let exact_work = budget.work_used();
    let expected = identities(&values);
    for (limit, payload, error) in [
        (exact_work, bytes, None),
        (exact_work - 1, bytes, Some(DynamicReflectionError::WorkLimit)),
        (exact_work, bytes - 1, Some(DynamicReflectionError::PayloadByteLimit)),
    ] {
        let mut values = records(count);
        let mut work = 7;
        let mut cancel = || false;
        let mut budget = ReflectedCodecBudget::new(&mut work, limit, payload, &mut cancel);
        let result = sort_results(&mut values, &mut budget);
        match error {
            None => {
                result.unwrap();
                assert_eq!(identities(&values), expected);
            },
            Some(error) => {
                assert_eq!(result, Err(SemanticWireError::Resource(error)));
                assert_eq!(identities(&values), (0..count).collect::<Vec<_>>());
            },
        }
        assert!(budget.work_used() <= limit);
    }
    for stop in 1..=calls {
        let mut values = records(count);
        let mut work = 7;
        let mut calls = 0;
        let mut cancel = || {
            calls += 1;
            calls == stop
        };
        let mut budget = ReflectedCodecBudget::new(&mut work, exact_work, bytes, &mut cancel);
        assert_eq!(
            sort_results(&mut values, &mut budget),
            Err(SemanticWireError::Resource(DynamicReflectionError::Cancelled))
        );
        assert!(budget.work_used() <= exact_work);
        let ids = identities(&values);
        let mut sorted = ids.clone();
        sorted.sort();
        assert_eq!(sorted, (0..count).collect::<Vec<_>>());
        for (result, id) in values.iter().zip(ids) {
            assert_eq!(result.receipt, originals[id], "cancellation unpaired a record");
        }
    }
}

#[test]
fn semantic_wire_order_chunk_boundaries_and_bounded_early_exit() {
    for length in [
        0,
        1,
        ACCOUNTING_CHUNK_BYTES - 1,
        ACCOUNTING_CHUNK_BYTES,
        ACCOUNTING_CHUNK_BYTES + 1,
        3 * ACCOUNTING_CHUNK_BYTES,
    ] {
        let a = vec![7; length];
        let mut b = a.clone();
        b.push(0);
        let mut work = 7;
        let mut cancel = || false;
        let exact = 8 + 2 * length as u64;
        let mut budget = ReflectedCodecBudget::new(&mut work, exact, 0, &mut cancel);
        assert_eq!(Comparator { budget: &mut budget }.bytes(&a, &b), Ok(Ordering::Less));
        assert_eq!(budget.work_used(), exact);
        if length > 0 {
            b[length - 1] = 6;
            assert_eq!(
                with_budget(|budget| Comparator { budget }.bytes(&a, &b)),
                Ok(Ordering::Greater)
            );
        }
    }
    let a = vec![0; 3 * ACCOUNTING_CHUNK_BYTES];
    let mut b = a.clone();
    b[0] = 1;
    let mut work = 0;
    let mut cancel = || false;
    let exact = 1 + 2 * ACCOUNTING_CHUNK_BYTES as u64;
    let mut budget = ReflectedCodecBudget::new(&mut work, exact, 0, &mut cancel);
    assert_eq!(Comparator { budget: &mut budget }.bytes(&a, &b), Ok(Ordering::Less));
    assert_eq!(budget.work_used(), exact);
}

#[test]
fn semantic_wire_order_second_chunk_refusal_retains_prior_work() {
    let a = vec![7; ACCOUNTING_CHUNK_BYTES + 1];
    let mut b = a.clone();
    b[ACCOUNTING_CHUNK_BYTES] = 8;
    let prefix = 7;
    let after_first_chunk = prefix + 1 + 2 * ACCOUNTING_CHUNK_BYTES as u64;
    for cancel_second in [false, true] {
        let mut work = prefix;
        let mut calls = 0;
        let mut cancel = || {
            calls += 1;
            cancel_second && calls == 3
        };
        let limit = after_first_chunk + if cancel_second { 2 } else { 1 };
        let mut budget = ReflectedCodecBudget::new(&mut work, limit, 0, &mut cancel);
        let expected = if cancel_second {
            DynamicReflectionError::Cancelled
        } else {
            DynamicReflectionError::WorkLimit
        };
        assert_eq!(
            Comparator { budget: &mut budget }.bytes(&a, &b),
            Err(SemanticWireError::Resource(expected))
        );
        assert_eq!(budget.work_used(), after_first_chunk);
        assert_eq!(budget.remaining_bytes(), 0);
    }
}

#[test]
fn semantic_wire_permutation_rejects_invalid_indices_before_moving() {
    for order in [vec![0, 0, 2], vec![0, 1, 3], vec![0, 1]] {
        let mut values = vec!["a", "b", "c"];
        let mut scratch = Vec::with_capacity(3);
        assert!(with_budget(|b| reorder(&mut values, &order, &mut scratch, b)).is_err());
        assert_eq!(values, ["a", "b", "c"]);
    }
    let mut values = vec![0, 1, 2];
    assert!(with_budget(|b| reorder(&mut values, &[2, 0, 1], &mut Vec::new(), b)).is_err());
    assert_eq!(values, [0, 1, 2]);
}

#[test]
fn semantic_wire_order_large_rosters_on_small_stack() {
    std::thread::Builder::new()
        .stack_size(128 * 1024)
        .spawn(|| {
            let mut a = transport_receipt();
            a.premises = (0..20_000).map(|_| a.premises[0].clone()).collect();
            let mut b = a.clone();
            b.work -= 1;
            assert_eq!(compare(&a, &b), Ordering::Greater);
            let mut values = records(4097);
            // Large result count, but no need to clone the large proof corpus into
            // every result to exercise iterative merge and cyclic movement.
            with_budget(|b| sort_results(&mut values, b)).unwrap();
            for pair in values.windows(2) {
                assert_ne!(compare(&pair[0].receipt, &pair[1].receipt), Ordering::Greater);
            }
        })
        .unwrap()
        .join()
        .unwrap();
}
