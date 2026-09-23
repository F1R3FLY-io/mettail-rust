//! Frozen against the original canonical admission gate, before authored capture.
//! These call the production gate, not a second admission implementation.
use mettail_elab::canonical::{
    admit_canonical_value, RhoValue, MAX_CANONICAL_COLLECTION_ITEMS, MAX_CANONICAL_STRING_BYTES,
    MAX_CANONICAL_TOTAL_STRING_BYTES, MAX_CANONICAL_VALUE_NODES,
};
use std::collections::BTreeMap;

fn rejected(value: &RhoValue, message: String) {
    let error = admit_canonical_value(value).expect_err("original gate must refuse");
    assert_eq!(error.path, "$");
    assert_eq!(error.message, message);
}

#[test]
fn original_node_count_includes_the_container_and_accepts_the_exact_limit() {
    let exact = RhoValue::List(vec![RhoValue::Nil; MAX_CANONICAL_VALUE_NODES - 1]);
    admit_canonical_value(&exact).expect("exact canonical boundary must be admitted");
    drop(exact);
    let over = RhoValue::List(vec![RhoValue::Nil; MAX_CANONICAL_VALUE_NODES]);
    rejected(&over, format!("canonical value exceeds {MAX_CANONICAL_VALUE_NODES} nodes"));
}

#[test]
fn original_collection_count_refuses_before_visiting_oversized_children() {
    let mut items = vec![RhoValue::Nil; MAX_CANONICAL_COLLECTION_ITEMS + 1];
    items[0] = RhoValue::String("x".repeat(MAX_CANONICAL_STRING_BYTES + 1));
    rejected(
        &RhoValue::List(items),
        format!("canonical value exceeds {MAX_CANONICAL_COLLECTION_ITEMS} collection items"),
    );
}

#[test]
fn original_individual_string_gate_counts_utf8_bytes_and_accepts_exact_limit() {
    let exact = "é".repeat(MAX_CANONICAL_STRING_BYTES / 2);
    assert_eq!(exact.len(), MAX_CANONICAL_STRING_BYTES);
    admit_canonical_value(&RhoValue::String(exact.clone()))
        .expect("exact canonical boundary must be admitted");
    rejected(
        &RhoValue::String(exact + "x"),
        format!("canonical string exceeds {MAX_CANONICAL_STRING_BYTES} bytes"),
    );
}

#[test]
fn original_total_string_gate_counts_each_occurrence_not_distinct_values() {
    let count = MAX_CANONICAL_TOTAL_STRING_BYTES / MAX_CANONICAL_STRING_BYTES;
    let mut values: Vec<_> = (0..count)
        .map(|_| RhoValue::String("x".repeat(MAX_CANONICAL_STRING_BYTES)))
        .collect();
    values.push(RhoValue::String(String::new()));
    let mut exact = RhoValue::List(values);
    admit_canonical_value(&exact).expect("exact canonical boundary must be admitted");
    if let RhoValue::List(values) = &mut exact {
        values.push(RhoValue::String("x".into()));
    }
    rejected(
        &exact,
        format!("canonical strings exceed {MAX_CANONICAL_TOTAL_STRING_BYTES} total bytes"),
    );
}

#[test]
fn original_map_keys_are_charged_before_their_values() {
    let count = MAX_CANONICAL_TOTAL_STRING_BYTES / MAX_CANONICAL_STRING_BYTES;
    let values: Vec<_> = (0..count)
        .map(|_| RhoValue::String("x".repeat(MAX_CANONICAL_STRING_BYTES)))
        .collect();
    rejected(
        &RhoValue::Map(BTreeMap::from([("k".into(), RhoValue::List(values))])),
        format!("canonical strings exceed {MAX_CANONICAL_TOTAL_STRING_BYTES} total bytes"),
    );
    rejected(
        &RhoValue::Map(BTreeMap::from([(
            "k".repeat(MAX_CANONICAL_STRING_BYTES + 1),
            RhoValue::List(vec![RhoValue::Nil; MAX_CANONICAL_COLLECTION_ITEMS + 1]),
        )])),
        format!("canonical string exceeds {MAX_CANONICAL_STRING_BYTES} bytes"),
    );
}
