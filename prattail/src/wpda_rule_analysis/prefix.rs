//! Original unified prefix bucket and initiating-row derivation.
//!
//! Token quotation stays in the macro adapter. These helpers retain the original
//! formatter-key ordering, first payload, duplicate descriptors, lazy factoring
//! observations, and existing fork-emission accumulator. They neither discover
//! grammar rules nor select parse candidates.
//!
//! `UnifiedPrefixDescriptorProjection.v` verifies this relocation boundary and
//! finite call sequences. Callers still supply the original static positions;
//! allocation and arbitrary formatter/reader lawfulness remain caller obligations.

use super::fork_emission::ForkEmissionOrdinalModel;
use std::collections::BTreeMap;

/// One original unified dispatch bucket, independent of token quotation.
pub struct UnifiedBucket<P, D> {
    pub pat: P,
    pub extra_guard: Option<P>,
    pub descs: Vec<D>,
}

/// Insert exactly as the original macro helper: first-key order, first payload,
/// and every incoming descriptor. An absent guard and an empty-rendering guard
/// have the same key but retain the first guard's original Option payload.
pub fn insert_unified_descriptor<P: ToString, D>(
    unified_buckets: &mut BTreeMap<(String, String), UnifiedBucket<P, D>>,
    unified_order: &mut Vec<(String, String)>,
    pattern: P,
    extra_guard: Option<P>,
    desc: D,
) {
    let pat_str = pattern.to_string();
    let guard_str = extra_guard
        .as_ref()
        .map(|g| g.to_string())
        .unwrap_or_default();
    let key = (pat_str, guard_str);
    if !unified_buckets.contains_key(&key) {
        unified_order.push(key.clone());
    }
    let entry = unified_buckets.entry(key).or_insert_with(|| UnifiedBucket {
        pat: pattern,
        extra_guard,
        descs: Vec::new(),
    });
    entry.descs.push(desc);
}

/// Only the existing factoring tags read by initiating-row recording.
/// The three GroupFirst payload indices remain with the factoring consumer.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum InitiatingRuleDisposition {
    GroupFirst,
    GroupRest,
}

/// The original missing-members refusal, before any rows from this call are
/// recorded. Earlier calls' accumulated rows remain untouched.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MissingInitiatingRuleMembers {
    pub category_src_idx: u16,
    pub rule_idx: u16,
}

/// Record the original initiating rows using the existing shared accumulator.
/// Member lookup occurs only for GroupFirst; members retain order and duplicates.
/// GroupRest does not renumber any static positions supplied by the caller.
#[allow(clippy::too_many_arguments)]
#[must_use]
pub fn record_initiating_rule_rows<'members>(
    fork_rows: &mut ForkEmissionOrdinalModel,
    category_src_idx: u16,
    rule_idx: u16,
    branch_position: u16,
    disposition: impl FnOnce(u16) -> Option<InitiatingRuleDisposition>,
    group_members: impl FnOnce(u16) -> Option<&'members [u16]>,
    bucket_tag: &str,
) -> Option<MissingInitiatingRuleMembers> {
    match disposition(rule_idx) {
        Some(InitiatingRuleDisposition::GroupFirst) => {
            let Some(members) = group_members(rule_idx) else {
                return Some(MissingInitiatingRuleMembers { category_src_idx, rule_idx });
            };
            for &member in members {
                fork_rows.record_site2_row(category_src_idx, member, branch_position, bucket_tag);
            }
            None
        },
        Some(InitiatingRuleDisposition::GroupRest) => None,
        None => {
            fork_rows.record_site2_row(category_src_idx, rule_idx, branch_position, bucket_tag);
            None
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::cell::RefCell;

    #[test]
    fn owned_payloads_keep_first_allocation_guard_and_insertion_order() {
        let mut buckets = BTreeMap::new();
        let mut order = Vec::new();
        let first = String::from("z");
        let first_allocation = first.as_ptr();
        insert_unified_descriptor(&mut buckets, &mut order, first, Some(String::new()), 8);
        insert_unified_descriptor(&mut buckets, &mut order, String::from("a"), None, 9);
        insert_unified_descriptor(&mut buckets, &mut order, String::from("z"), None, 8);
        assert_eq!(
            order,
            vec![(String::from("z"), String::new()), (String::from("a"), String::new())]
        );
        let bucket = buckets
            .get(&(String::from("z"), String::new()))
            .expect("first bucket");
        assert_eq!(bucket.pat.as_ptr(), first_allocation);
        assert_eq!(bucket.extra_guard, Some(String::new()));
        assert_eq!(bucket.descs, vec![8, 8]);
        assert_eq!(buckets.keys().map(|key| key.0.as_str()).collect::<Vec<_>>(), vec!["a", "z"]);
    }

    #[test]
    fn group_rest_and_ordinary_rule_never_read_members() {
        for disposition in [Some(InitiatingRuleDisposition::GroupRest), None] {
            let calls = RefCell::new(Vec::new());
            let mut rows = ForkEmissionOrdinalModel::new();
            let error = record_initiating_rule_rows(
                &mut rows,
                u16::MAX,
                4,
                u16::MAX,
                |rule| {
                    calls.borrow_mut().push(rule);
                    disposition
                },
                |_| panic!("members lookup must stay lazy"),
                "static-position",
            );
            assert_eq!(error, None);
            assert_eq!(*calls.borrow(), vec![4]);
            assert_eq!(rows.site2_ordinal(u16::MAX, 4), disposition.is_none().then_some(u16::MAX));
            assert_eq!(rows.site2_row_count(), usize::from(disposition.is_none()));
        }
    }

    #[test]
    fn group_first_reads_in_order_and_preserves_duplicate_accumulator_observations() {
        let calls = RefCell::new(Vec::new());
        let members = [8, 7, 8, 8];
        let mut rows = ForkEmissionOrdinalModel::new();
        rows.record_site2_row(2, 8, 1, "seed");
        let error = record_initiating_rule_rows(
            &mut rows,
            2,
            3,
            6,
            |rule| {
                calls.borrow_mut().push(("disposition", rule));
                Some(InitiatingRuleDisposition::GroupFirst)
            },
            |rule| {
                calls.borrow_mut().push(("members", rule));
                Some(&members)
            },
            "group",
        );
        assert_eq!(error, None);
        assert_eq!(*calls.borrow(), vec![("disposition", 3), ("members", 3)]);
        let (derived, ambiguous) = rows.into_parts();
        assert_eq!(derived.len(), 1);
        let member = derived.get(&(2, 7)).expect("one derived member");
        assert_eq!(member.emission_ordinal, 6);
        assert_eq!(member.bucket_tag, "group");
        assert_eq!(ambiguous.len(), 1);
        assert_eq!(
            ambiguous.get(&(2, 8)).expect("duplicate member history"),
            &vec![
                String::from("seed@1"),
                String::from("group@6"),
                String::from("group@6"),
                String::from("group@6")
            ]
        );
    }

    #[test]
    fn missing_and_empty_members_preserve_prefix_but_have_distinct_outcomes() {
        for members in [None, Some(&[][..])] {
            let calls = RefCell::new(Vec::new());
            let mut rows = ForkEmissionOrdinalModel::new();
            rows.record_site2_row(1, 2, 3, "first");
            rows.record_site2_row(1, 2, 4, "conflicting");
            let before = format!("{rows:?}");
            let error = record_initiating_rule_rows(
                &mut rows,
                12,
                34,
                56,
                |rule| {
                    calls.borrow_mut().push(("disposition", rule));
                    Some(InitiatingRuleDisposition::GroupFirst)
                },
                |rule| {
                    calls.borrow_mut().push(("members", rule));
                    members
                },
                "unused",
            );
            assert_eq!(*calls.borrow(), vec![("disposition", 34), ("members", 34)]);
            assert_eq!(
                error,
                members
                    .is_none()
                    .then_some(MissingInitiatingRuleMembers { category_src_idx: 12, rule_idx: 34 })
            );
            assert_eq!(format!("{rows:?}"), before);
        }
    }
}
