use super::*;
use crate::binding_power::InfixOperator;
use crate::wpda_rule_analysis::mixfix::{build_mixfix_factoring_with, GroupedOp};
use std::cell::Cell;
use std::collections::BTreeMap;

#[test]
fn encoded_allocation_is_exact_and_overflow_does_not_advance() {
    for (start, id, after) in [(0, 0xf800, 1), (2046, 65534, 2047), (2047, 65535, 2048)] {
        let mut ordinal = start;
        assert_eq!(allocate_spine_id(&mut ordinal), Some(id));
        assert_eq!(ordinal, after);
    }
    for start in [2048, u16::MAX] {
        let mut ordinal = start;
        assert_eq!(allocate_spine_id(&mut ordinal), None);
        assert_eq!(ordinal, start);
    }
}

fn prefix_partition(group_count: u16) -> (Vec<CategoryFactoring>, usize) {
    let per_cat = [vec![(); usize::from(group_count) * 2]];
    let casts = Cell::new(0);
    let partition = build_prefix_factoring_with(
        &per_cat,
        false,
        0xfe00,
        |_, rules| {
            rules
                .iter()
                .enumerate()
                .map(|(index, _)| {
                    let rule_idx =
                        u16::try_from(index).expect("regression roster fits source width");
                    (
                        format!("trigger_{}", index / 2),
                        CandidateMember {
                            kind: MemberKind::Nullary,
                            rule_idx,
                            items: vec![
                                SpineItem::Literal { text: "(".into(), required_top_cat: None },
                                SpineItem::Literal {
                                    text: (index % 2).to_string(),
                                    required_top_cat: None,
                                },
                            ],
                            truncated: false,
                            total_positions: 2,
                            body_src_idx: None,
                            mixfix_coords: vec![],
                        },
                    )
                })
                .collect()
        },
        |_| {
            casts.set(casts.get() + 1);
            false
        },
    );
    (partition, casts.get())
}

#[test]
fn original_recovery_ceiling_remains_strict() {
    let (below, below_casts) = prefix_partition(1535);
    assert_eq!(below_casts, 3070);
    assert!(below[0].refusals.is_empty());
    assert_eq!(
        below[0]
            .buckets
            .iter()
            .map(|bucket| bucket.groups.len())
            .sum::<usize>(),
        1535
    );
    let (at, at_casts) = prefix_partition(1536);
    assert_eq!(at_casts, 3072);
    assert_eq!(
        at[0]
            .buckets
            .iter()
            .map(|bucket| bucket.groups.len())
            .sum::<usize>(),
        1536
    );
    assert!(at[0]
        .refusals
        .iter()
        .any(|refusal| refusal.contains("recovery-branch")));
    assert!(!at[0]
        .refusals
        .iter()
        .any(|refusal| refusal.contains("cannot allocate")));
}

#[test]
fn prefix_4098_rule_overflow_is_hard_refusal_without_wrapped_group() {
    let (partition, casts) = prefix_partition(2049);
    assert_eq!(casts, 4098, "all original cast observations must still run");
    let groups: Vec<_> = partition[0]
        .buckets
        .iter()
        .flat_map(|bucket| &bucket.groups)
        .collect();
    assert_eq!(groups.len(), 2048);
    assert_eq!(groups.last().expect("representable prefix exists").spine_id, u16::MAX);
    assert!(groups.iter().all(|group| group.spine_id >= SPINE_RULE_BASE));
    assert!(partition[0]
        .buckets
        .last()
        .expect("failed bucket retained")
        .groups
        .is_empty());
    assert!(partition[0]
        .refusals
        .iter()
        .any(|refusal| refusal.contains("cannot allocate spine ordinal 2048")));
    assert!(partition[0]
        .refusals
        .iter()
        .any(|refusal| refusal.contains("recovery-branch")));
}

#[test]
fn mixfix_continuation_overflow_keeps_suffix_callbacks_and_hard_refusal() {
    let ops: Vec<_> = (0..4)
        .map(|index| InfixOperator {
            terminal: format!("trigger_{}", index / 2),
            category: "Term".into(),
            result_category: "Term".into(),
            left_bp: 1,
            right_bp: 2,
            label: format!("Rule{index}"),
            is_cross_category: false,
            is_postfix: false,
            is_mixfix: true,
            mixfix_parts: vec![],
            nullary_literals: vec!["(".into(), (index % 2).to_string()],
        })
        .collect();
    let grouped: BTreeMap<_, _> = (0..2)
        .map(|bucket| {
            (
                (0, format!("trigger_{bucket}")),
                (bucket * 2..bucket * 2 + 2)
                    .map(|index| GroupedOp {
                        op: &ops[index],
                        result_src_idx: 0,
                        rule_idx: u16::try_from(index)
                            .expect("four-rule fixture fits source width"),
                    })
                    .collect(),
            )
        })
        .collect();
    for seed in [2047, 2048] {
        // Only group count is observed when seeding the existing mixfix ordinal.
        let prefix = [CategoryFactoring {
            category_src_idx: 0,
            refusals: vec![],
            buckets: vec![FactoringBucket {
                leading_literal: "prefix".into(),
                cohort_size: 0,
                groups: (0..seed)
                    .map(|ordinal| SpineGroup {
                        spine_id: SPINE_RULE_BASE + ordinal,
                        body_src_idx: 0,
                        roots: vec![],
                    })
                    .collect(),
                ineligible: vec![],
                singletons: vec![],
            }],
        }];
        let casts = Cell::new(0);
        let result = build_mixfix_factoring_with(
            &["Term".into()],
            &[vec![(); 4]],
            &prefix,
            &grouped,
            16,
            0xfe00,
            |_, _, _, _| Ok::<_, ()>(0),
            |_| {
                casts.set(casts.get() + 1);
                false
            },
        );
        assert_eq!(casts.get(), 4, "later cohort callbacks must still run");
        let groups: Vec<_> = result
            .iter()
            .flat_map(|fact| &fact.buckets)
            .flat_map(|bucket| &bucket.groups)
            .collect();
        assert_eq!(groups.len(), usize::from(seed == 2047));
        if let Some(group) = groups.first() {
            assert_eq!(group.spine_id, u16::MAX);
        }
        assert!(result
            .iter()
            .flat_map(|fact| &fact.refusals)
            .any(|refusal| refusal.contains("cannot allocate spine ordinal 2048")));
    }
}
