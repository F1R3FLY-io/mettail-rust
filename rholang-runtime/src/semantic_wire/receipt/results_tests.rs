use super::*;
use crate::semantic_service::tests::transport_receipt;
use models::rust::utils::new_gint_par;

fn results() -> Vec<SemanticServiceResult> {
    [2, 1, 1, 3]
        .into_iter()
        .map(|n| {
            let mut receipt = transport_receipt();
            receipt.output = vec![n];
            SemanticServiceResult {
                term: new_gint_par(i64::from(n), Vec::new(), false),
                receipt,
            }
        })
        .collect()
}

fn encode(wl: u64, bl: usize, stop: usize) -> (Result<Par>, u64, usize, usize) {
    let mut work = 7;
    let mut calls = 0;
    let mut cancel = || {
        calls += 1;
        calls == stop
    };
    let mut budget = ReflectedCodecBudget::new(&mut work, wl, bl, &mut cancel);
    let result = encode_results_v1(results(), &mut budget);
    let remaining = budget.finish();
    (result, work, bl - remaining, calls)
}

#[test]
fn semantic_wire_results_retain_sorted_pairs_complete_receipts_and_duplicates() {
    let (encoded, _, _, _) = encode(1_000_000, 1_000_000, 0);
    let encoded = encoded.unwrap();
    let items = exact_list(&encoded).unwrap();
    assert_eq!(items.len(), 4);
    let mut work = 0;
    let mut cancel = || false;
    let mut budget = ReflectedCodecBudget::new(&mut work, 1_000_000, 1_000_000, &mut cancel);
    for (item, n) in items.iter().zip([1, 1, 2, 3]) {
        let pair = exact_list(item).unwrap();
        assert_eq!(pair.len(), 2);
        assert_eq!(pair[0], new_gint_par(i64::from(n), Vec::new(), false));
        let mut expected = transport_receipt();
        expected.output = vec![n];
        assert_eq!(decode_receipt_v1(&pair[1], &mut budget).unwrap(), expected);
    }
}

#[test]
fn semantic_wire_results_exact_quotas_and_every_cancel_refuse_partial_output() {
    let (_, work, bytes, calls) = encode(1_000_000, 1_000_000, 0);
    assert!(encode(work, bytes, 0).0.is_ok());
    for (wl, bl) in [(work - 1, bytes), (work, bytes - 1)] {
        let (out, used, payload, _) = encode(wl, bl, 0);
        assert!(matches!(out, Err(SemanticWireError::Resource(_))));
        assert!(used <= wl);
        assert!(payload <= bl);
    }
    for stop in 1..=calls {
        let (out, used, payload, _) = encode(work, bytes, stop);
        assert!(matches!(
            out,
            Err(SemanticWireError::Resource(DynamicReflectionError::Cancelled))
        ));
        assert!(used <= work);
        assert!(payload <= bytes);
    }
}

#[test]
fn semantic_wire_results_reject_open_metadata_and_preserve_empty_roster() {
    let mut work = 0;
    let mut cancel = || false;
    let mut budget = ReflectedCodecBudget::new(&mut work, 1_000_000, 1_000_000, &mut cancel);
    let empty = encode_results_v1(Vec::new(), &mut budget).unwrap();
    assert_eq!(exact_list(&empty).unwrap().len(), 0);
    assert_eq!(budget.work_used(), 1);
    assert_eq!(budget.remaining_bytes(), 1_000_000 - VALUE_DESCRIPTOR_BYTES);
    for kind in 0..2 {
        let mut values = results();
        if kind == 0 {
            values[3].term.locally_free.push(1);
        } else {
            values[3].term.connective_used = true;
        }
        assert!(matches!(
            encode_results_v1(values, &mut budget),
            Err(SemanticWireError::Shape("semantic result term is not closed"))
        ));
    }
}

#[test]
fn semantic_wire_results_move_and_drop_deep_terms_on_small_stack() {
    std::thread::Builder::new()
        .stack_size(128 * 1024)
        .spawn(|| {
            let mut term = Par::default();
            for _ in 0..20_000 {
                term = wire_list(vec![term]);
            }
            let original = exact_list(&term).unwrap().as_ptr();
            let values = vec![SemanticServiceResult { term, receipt: transport_receipt() }];
            let mut work = 0;
            let mut cancel = || false;
            let mut budget =
                ReflectedCodecBudget::new(&mut work, 1_000_000, 1_000_000, &mut cancel);
            let encoded = encode_results_v1(values, &mut budget).unwrap();
            let pair = exact_list(&exact_list(&encoded).unwrap()[0]).unwrap();
            assert_eq!(exact_list(&pair[0]).unwrap().as_ptr(), original);
            drop(encoded);
        })
        .unwrap()
        .join()
        .unwrap();
}
