//! Pin the original prefix partition at its borrowed discovery/cast boundary.

use std::cell::RefCell;

use mettail_prattail::wpda_rule_analysis::factoring::{
    build_prefix_factoring_with, prefix_identity_partition, CandidateMember, CategoryFactoring,
    FactoringBucket, GroupMember, IneligibleGroup, IneligibleReason, MemberCommit, MemberKind,
    SingletonMember, SingletonReason, SpineGroup, SpineItem, SpinePosMap, SpineTree, LIMIT_REFUSAL,
    SPINE_RULE_BASE,
};

// Deliberately neither Clone nor Copy: discovery and cast checks borrow source rules.
struct Rule {
    cast: bool,
}

fn literal(text: &str) -> SpineItem {
    SpineItem::Literal {
        text: text.into(),
        required_top_cat: None,
    }
}

fn member(
    kind: MemberKind,
    rule_idx: u16,
    items: Vec<SpineItem>,
    body: Option<u16>,
) -> CandidateMember {
    CandidateMember {
        kind,
        rule_idx,
        total_positions: items.len(),
        items,
        truncated: false,
        body_src_idx: body,
        mixfix_coords: vec![],
    }
}

fn singleton_bucket(trigger: &str, entries: &[(u16, SingletonReason)]) -> FactoringBucket {
    FactoringBucket {
        leading_literal: trigger.into(),
        cohort_size: entries.len(),
        groups: vec![],
        ineligible: vec![],
        singletons: entries
            .iter()
            .map(|&(rule_idx, reason)| SingletonMember { rule_idx, reason })
            .collect(),
    }
}

fn assert_partition(actual: &[CategoryFactoring], expected: &[CategoryFactoring]) {
    assert_eq!(format!("{actual:?}"), format!("{expected:?}"));
}

#[test]
fn prefix_callbacks_follow_category_then_bucket_member_order_and_borrow_original_rules() {
    let per_cat = vec![
        vec![],
        vec![
            Rule { cast: true },
            Rule { cast: false },
            Rule { cast: true },
            Rule { cast: false },
        ],
        vec![],
    ];
    let effects = RefCell::new(vec![]);
    let actual = build_prefix_factoring_with(
        &per_cat,
        true,
        0xfe00,
        |cat, rules| {
            effects.borrow_mut().push(format!("discover:{cat}"));
            assert!(std::ptr::eq(rules, per_cat[cat as usize].as_slice()));
            if cat != 1 {
                return vec![];
            }
            vec![
                ("z".into(), member(MemberKind::Nullary, 2, vec![], None)),
                ("a".into(), member(MemberKind::Nullary, 0, vec![literal("cast")], None)),
                ("z".into(), member(MemberKind::Nullary, 3, vec![], None)),
                ("a".into(), member(MemberKind::Nullary, 1, vec![literal("lone")], None)),
            ]
        },
        |rule| {
            let index = per_cat[1]
                .iter()
                .position(|source| std::ptr::eq(source, rule))
                .expect("original borrowed rule");
            effects.borrow_mut().push(format!("cast:{index}"));
            rule.cast
        },
    );
    assert_eq!(
        *effects.borrow(),
        ["discover:0", "discover:1", "cast:2", "cast:3", "cast:0", "cast:1", "discover:2"]
    );
    assert_partition(
        &actual,
        &[
            CategoryFactoring {
                category_src_idx: 0,
                buckets: vec![],
                refusals: vec![],
            },
            CategoryFactoring {
                category_src_idx: 1,
                buckets: vec![
                    singleton_bucket(
                        "z",
                        &[(2, SingletonReason::CastMachinery), (3, SingletonReason::EmptySequence)],
                    ),
                    singleton_bucket(
                        "a",
                        &[(0, SingletonReason::CastMachinery), (1, SingletonReason::LoneRootChild)],
                    ),
                ],
                refusals: vec![],
            },
            CategoryFactoring {
                category_src_idx: 2,
                buckets: vec![],
                refusals: vec![],
            },
        ],
    );
}

fn missing_mixfix_coordinate(rule_idx: u16, depth: usize) -> String {
    format!(
        "{LIMIT_REFUSAL} the mixfix member at rule index {rule_idx} recorded 0 spine \
         coordinates but leafs at depth {depth}, so the discovery walk and \
         the item list disagree. This is a macro bug, not a grammar bug — \
         please report it."
    )
}

#[test]
fn prefix_retains_tree_diagnostics_before_ineligibility_and_body_categories_in_first_seen_order() {
    let per_cat =
        vec![vec![Rule { cast: false }, Rule { cast: false }, Rule { cast: false }], vec![]];
    for accept_continue in [false, true] {
        let actual = build_prefix_factoring_with(
            &per_cat,
            accept_continue,
            0xfe00,
            |cat, _| {
                if cat != 0 {
                    return vec![];
                }
                vec![
                    (
                        "trigger".into(),
                        member(MemberKind::Mixfix, 2, vec![literal("root")], Some(9)),
                    ),
                    (
                        "trigger".into(),
                        member(
                            MemberKind::Mixfix,
                            0,
                            vec![literal("root"), literal("left")],
                            Some(2),
                        ),
                    ),
                    (
                        "trigger".into(),
                        member(
                            MemberKind::Mixfix,
                            1,
                            vec![literal("root"), literal("right")],
                            Some(9),
                        ),
                    ),
                ]
            },
            |rule| rule.cast,
        );
        let (reason, refusals) = if accept_continue {
            (
                IneligibleReason::NonUniformBodySrc { body_src_idxs: vec![9, 2] },
                vec![
                    missing_mixfix_coordinate(2, 1),
                    missing_mixfix_coordinate(0, 2),
                    missing_mixfix_coordinate(1, 2),
                ],
            )
        } else {
            (
                IneligibleReason::InteriorAccept { accepting_rule_idxs: vec![2] },
                vec![missing_mixfix_coordinate(0, 2), missing_mixfix_coordinate(1, 2)],
            )
        };
        assert_partition(
            &actual,
            &[
                CategoryFactoring {
                    category_src_idx: 0,
                    buckets: vec![FactoringBucket {
                        leading_literal: "trigger".into(),
                        cohort_size: 3,
                        groups: vec![],
                        ineligible: vec![IneligibleGroup {
                            reason,
                            member_rule_idxs: vec![2, 0, 1],
                        }],
                        singletons: vec![],
                    }],
                    refusals,
                },
                CategoryFactoring {
                    category_src_idx: 1,
                    buckets: vec![],
                    refusals: vec![],
                },
            ],
        );
    }
}

#[test]
fn prefix_identity_keeps_discovery_order_without_indexing_invalid_rule_handles() {
    let per_cat = vec![vec![], vec![Rule { cast: true }]];
    let calls = RefCell::new(vec![]);
    let actual = prefix_identity_partition(&per_cat, |cat, rules| {
        calls.borrow_mut().push(cat);
        assert!(std::ptr::eq(rules, per_cat[cat as usize].as_slice()));
        if cat == 0 {
            vec![
                ("z".into(), member(MemberKind::Nullary, u16::MAX, vec![], None)),
                (
                    "a".into(),
                    member(MemberKind::Nullary, u16::MAX - 1, vec![literal("unused")], None),
                ),
                ("z".into(), member(MemberKind::Nullary, u16::MAX - 2, vec![], None)),
            ]
        } else {
            vec![("other".into(), member(MemberKind::Nullary, 42, vec![], None))]
        }
    });
    assert_eq!(*calls.borrow(), [0, 1]);
    assert_partition(
        &actual,
        &[
            CategoryFactoring {
                category_src_idx: 0,
                buckets: vec![
                    singleton_bucket(
                        "z",
                        &[
                            (u16::MAX, SingletonReason::FactoringDisabled),
                            (u16::MAX - 2, SingletonReason::FactoringDisabled),
                        ],
                    ),
                    singleton_bucket("a", &[(u16::MAX - 1, SingletonReason::FactoringDisabled)]),
                ],
                refusals: vec![],
            },
            CategoryFactoring {
                category_src_idx: 1,
                buckets: vec![singleton_bucket(
                    "other",
                    &[(42, SingletonReason::FactoringDisabled)],
                )],
                refusals: vec![],
            },
        ],
    );
}

fn expected_nullary_group(
    spine_id: u16,
    body_src_idx: u16,
    root: &str,
    rule_idxs: [u16; 2],
) -> SpineGroup {
    SpineGroup {
        spine_id,
        body_src_idx,
        roots: vec![SpineTree::Interior {
            item: literal(root),
            children: ["left", "right"]
                .into_iter()
                .zip(rule_idxs)
                .map(|(text, rule_idx)| SpineTree::Leaf {
                    item: literal(text),
                    member: GroupMember {
                        kind: MemberKind::Nullary,
                        rule_idx,
                        leaf_depth: 2,
                        commit: MemberCommit::Nullary { rule_idx, completed_idx: 0, sub_pos: 2 },
                        pos_map: SpinePosMap::Nullary { sub_pos_at_depth: vec![0, 1, 2] },
                        has_post_spine_remainder: false,
                    },
                })
                .collect(),
        }],
    }
}

#[test]
fn prefix_eligible_group_ids_follow_bucket_order_and_reset_for_each_category() {
    let per_cat = vec![
        (0..4).map(|_| Rule { cast: false }).collect(),
        (0..2).map(|_| Rule { cast: false }).collect(),
    ];
    let actual = build_prefix_factoring_with(
        &per_cat,
        true,
        0xfe00,
        |cat, _| {
            if cat == 0 {
                vec![
                    (
                        "z".into(),
                        member(
                            MemberKind::Nullary,
                            0,
                            vec![literal("root-z"), literal("left")],
                            None,
                        ),
                    ),
                    (
                        "a".into(),
                        member(
                            MemberKind::Nullary,
                            2,
                            vec![literal("root-a"), literal("left")],
                            None,
                        ),
                    ),
                    (
                        "z".into(),
                        member(
                            MemberKind::Nullary,
                            1,
                            vec![literal("root-z"), literal("right")],
                            None,
                        ),
                    ),
                    (
                        "a".into(),
                        member(
                            MemberKind::Nullary,
                            3,
                            vec![literal("root-a"), literal("right")],
                            None,
                        ),
                    ),
                ]
            } else {
                vec![
                    (
                        "z".into(),
                        member(
                            MemberKind::Nullary,
                            0,
                            vec![literal("root-z"), literal("left")],
                            None,
                        ),
                    ),
                    (
                        "z".into(),
                        member(
                            MemberKind::Nullary,
                            1,
                            vec![literal("root-z"), literal("right")],
                            None,
                        ),
                    ),
                ]
            }
        },
        |rule| rule.cast,
    );
    assert_partition(
        &actual,
        &[
            CategoryFactoring {
                category_src_idx: 0,
                buckets: vec![
                    FactoringBucket {
                        leading_literal: "z".into(),
                        cohort_size: 2,
                        groups: vec![expected_nullary_group(SPINE_RULE_BASE, 0, "root-z", [0, 1])],
                        ineligible: vec![],
                        singletons: vec![],
                    },
                    FactoringBucket {
                        leading_literal: "a".into(),
                        cohort_size: 2,
                        groups: vec![expected_nullary_group(
                            SPINE_RULE_BASE + 1,
                            0,
                            "root-a",
                            [2, 3],
                        )],
                        ineligible: vec![],
                        singletons: vec![],
                    },
                ],
                refusals: vec![],
            },
            CategoryFactoring {
                category_src_idx: 1,
                buckets: vec![FactoringBucket {
                    leading_literal: "z".into(),
                    cohort_size: 2,
                    groups: vec![expected_nullary_group(SPINE_RULE_BASE, 1, "root-z", [0, 1])],
                    ineligible: vec![],
                    singletons: vec![],
                }],
                refusals: vec![],
            },
        ],
    );
}
