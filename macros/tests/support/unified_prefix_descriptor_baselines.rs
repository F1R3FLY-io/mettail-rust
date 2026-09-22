//! Frozen baselines for the original prefix bucket and initiating-row helpers.
//! These call the production helpers directly; no parallel derivation is used.

use super::*;
use std::collections::{BTreeMap, HashMap};

fn first() -> super::super::factoring::SpineDisposition {
    super::super::factoring::SpineDisposition::GroupFirst {
        spine_id: 91,
        body_src_idx: 92,
        weight_rule_idx: 93,
    }
}

#[test]
fn original_bucket_order_is_first_key_occurrence_and_descriptors_append() {
    let mut buckets = BTreeMap::new();
    let mut order = Vec::new();
    let z = quote! { Some(Z) };
    let a = quote! { Some(A) };
    let guard = quote! { ready && enabled };
    insert_unified_descriptor(
        &mut buckets,
        &mut order,
        z.clone(),
        None,
        UnifiedDescriptor::NullaryLiteralRun { rule_idx: 7 },
    );
    insert_unified_descriptor(
        &mut buckets,
        &mut order,
        a.clone(),
        Some(guard.clone()),
        UnifiedDescriptor::LeadingCategory { rule_idx: 8, source_src_idx: 9 },
    );
    insert_unified_descriptor(
        &mut buckets,
        &mut order,
        z.clone(),
        None,
        UnifiedDescriptor::CrossCatPrefixUnary {
            rule_idx: 10,
            source_src_idx: 11,
            operand_bp: 255,
        },
    );
    insert_unified_descriptor(
        &mut buckets,
        &mut order,
        a.clone(),
        None,
        UnifiedDescriptor::NullaryLiteralRun { rule_idx: 12 },
    );
    let z_key = (z.to_string(), String::new());
    let guarded_a_key = (a.to_string(), guard.to_string());
    let a_key = (a.to_string(), String::new());
    assert_eq!(order, vec![z_key.clone(), guarded_a_key.clone(), a_key.clone()]);
    assert_eq!(
        buckets.keys().cloned().collect::<Vec<_>>(),
        vec![a_key, guarded_a_key, z_key.clone()]
    );
    let bucket = buckets.get(&z_key).expect("original z bucket");
    assert_eq!(bucket.pat.to_string(), z.to_string());
    assert!(bucket.extra_guard.is_none());
    assert!(matches!(
        bucket.descs.as_slice(),
        [
            UnifiedDescriptor::NullaryLiteralRun { rule_idx: 7 },
            UnifiedDescriptor::CrossCatPrefixUnary {
                rule_idx: 10,
                source_src_idx: 11,
                operand_bp: 255
            },
        ]
    ));
}

#[test]
fn original_empty_guard_key_collision_retains_first_payload_in_both_directions() {
    for first_has_guard in [false, true] {
        let mut buckets = BTreeMap::new();
        let mut order = Vec::new();
        let first_guard = first_has_guard.then(TokenStream::new);
        let second_guard = (!first_has_guard).then(TokenStream::new);
        insert_unified_descriptor(
            &mut buckets,
            &mut order,
            quote! { (x) },
            first_guard,
            UnifiedDescriptor::NullaryLiteralRun { rule_idx: 4 },
        );
        insert_unified_descriptor(
            &mut buckets,
            &mut order,
            quote! { (x) },
            second_guard,
            UnifiedDescriptor::NullaryLiteralRun { rule_idx: 4 },
        );
        assert_eq!(order.len(), 1);
        let bucket = buckets.values().next().expect("one original bucket");
        assert_eq!(bucket.extra_guard.is_some(), first_has_guard);
        assert!(matches!(
            bucket.descs.as_slice(),
            [
                UnifiedDescriptor::NullaryLiteralRun { rule_idx: 4 },
                UnifiedDescriptor::NullaryLiteralRun { rule_idx: 4 },
            ]
        ));
    }
}

#[test]
fn original_bucket_key_retains_token_delimiters_and_guard_text() {
    let mut buckets = BTreeMap::new();
    let mut order = Vec::new();
    for (pattern, guard) in [
        (quote! { (x) }, None),
        (quote! { [x] }, None),
        (quote! { (x) }, Some(quote! { false })),
    ] {
        insert_unified_descriptor(
            &mut buckets,
            &mut order,
            pattern,
            guard,
            UnifiedDescriptor::NullaryLiteralRun { rule_idx: 0 },
        );
    }
    assert_eq!(buckets.len(), 3);
    assert_eq!(
        order,
        vec![
            (quote! { (x) }.to_string(), String::new()),
            (quote! { [x] }.to_string(), String::new()),
            (quote! { (x) }.to_string(), quote! { false }.to_string()),
        ]
    );
}

#[test]
fn original_initiating_rows_preserve_static_ordinal_and_skip_group_rest() {
    let mut rows = super::super::fork_emission::ForkEmissionOrdinalModel::new();
    let dispositions = HashMap::from([(5, super::super::factoring::SpineDisposition::GroupRest)]);
    // A members entry alone is ignored for an undispositioned rule.
    let members = HashMap::from([(4, vec![99])]);
    assert!(record_initiating_rule_rows(
        &mut rows,
        65535,
        4,
        65535,
        &dispositions,
        &members,
        "static"
    )
    .is_none());
    let before = format!("{rows:?}");
    assert!(record_initiating_rule_rows(
        &mut rows,
        65535,
        5,
        0,
        &dispositions,
        &members,
        "skipped"
    )
    .is_none());
    assert_eq!(format!("{rows:?}"), before);
    assert_eq!(rows.site2_ordinal(65535, 4), Some(65535));
    assert_eq!(rows.site2_ordinal(65535, 99), None);
    assert_eq!(rows.census_keys(), vec![(65535, 4)]);
}

#[test]
fn original_group_first_records_ordered_duplicate_members_not_leader() {
    let mut rows = super::super::fork_emission::ForkEmissionOrdinalModel::new();
    rows.record_site2_row(2, 8, 1, "seed");
    let dispositions = HashMap::from([(3, first())]);
    let members = HashMap::from([(3, vec![8, 7, 8, 8])]);
    assert!(
        record_initiating_rule_rows(&mut rows, 2, 3, 6, &dispositions, &members, "group").is_none()
    );
    assert_eq!(rows.site2_ordinal(2, 3), None);
    assert_eq!(rows.site2_ordinal(2, 7), Some(6));
    assert!(rows.is_ambiguous_multi_bucket(2, 8));
    assert_eq!(rows.site2_row_count(), 1);
    assert_eq!(rows.ambiguous_rule_count(), 1);
    assert!(format!("{rows:?}").contains("[\"seed@1\", \"group@6\", \"group@6\", \"group@6\"]"));
    // An explicitly empty member list succeeds without recording even the leader.
    let before = format!("{rows:?}");
    let empty = HashMap::from([(3, Vec::new())]);
    assert!(
        record_initiating_rule_rows(&mut rows, 2, 3, 9, &dispositions, &empty, "empty").is_none()
    );
    assert_eq!(format!("{rows:?}"), before);
}

#[test]
fn original_missing_members_refusal_preserves_accumulator_and_exact_error() {
    let mut rows = super::super::fork_emission::ForkEmissionOrdinalModel::new();
    rows.record_site2_row(1, 2, 3, "previous");
    rows.record_site2_row(1, 2, 4, "conflict");
    let before = format!("{rows:?}");
    let error = record_initiating_rule_rows(
        &mut rows,
        12,
        34,
        56,
        &HashMap::from([(34, first())]),
        &HashMap::new(),
        "missing",
    )
    .expect("missing GroupFirst members produce compile_error");
    assert_eq!(format!("{rows:?}"), before);
    let message = "mettail: task #10 item 1 — the rule at category index \
        12, rule index 34 is dispositioned \
        `GroupFirst` by the S1 factoring model but has no `group_members` \
        entry, so the fork emission cannot derive the site-2 rows its \
        members are owed. The two halves of the factoring model disagree; \
        this is a macro bug, not a grammar bug — please report it.";
    assert_eq!(error.to_string(), quote! { compile_error!(#message); }.to_string());
}
