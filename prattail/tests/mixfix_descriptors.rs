//! Borrowed callbacks and finite-slice contracts of the mixfix boundary.

use std::cell::RefCell;
use std::collections::HashMap;

use mettail_prattail::binding_power::{BindingPowerTable, InfixOperator, MixfixPart, MixfixRep};
use mettail_prattail::wpda_rule_analysis::factoring::{
    IneligibleReason, SingletonMember, SingletonReason, SPINE_RULE_BASE,
};
use mettail_prattail::wpda_rule_analysis::mixfix::{
    build_mixfix_factoring_with, group_ops_by_cat_terminal, mixfix_identity_partition,
    mixfix_spine_parts_len_rows, MixfixBucket, MixfixFactoring,
};

// Neither Clone nor Copy: cast checks must borrow the original rule row.
struct Rule {
    cast: bool,
}

fn op(label: &str, category: &str, trigger: &str, bp: u8) -> InfixOperator {
    InfixOperator {
        terminal: trigger.into(),
        category: category.into(),
        result_category: category.into(),
        left_bp: bp,
        right_bp: bp + 1,
        label: label.into(),
        is_cross_category: false,
        is_postfix: false,
        is_mixfix: true,
        mixfix_parts: vec![],
        nullary_literals: vec![],
    }
}

fn part(category: &str, preceding: &[&str], following: &[&str]) -> MixfixPart {
    MixfixPart {
        operand_category: category.into(),
        param_name: "operand".into(),
        preceding_terminals: preceding.iter().map(|text| (*text).into()).collect(),
        following_terminals: following.iter().map(|text| (*text).into()).collect(),
        repetition: None,
        capture_kind: None,
    }
}

#[derive(Debug, PartialEq)]
enum Event {
    Resolve(String, &'static str, String),
    Cast(usize),
}

fn item_call(label: &str, category: &str) -> Event {
    Event::Resolve(label.into(), "a mixfix cohort's operand position", category.into())
}

fn action_call(label: &str, category: &str) -> Event {
    Event::Resolve(label.into(), "a mixfix cohort's action entry", category.into())
}

#[test]
fn resolution_precedes_casts_and_missing_coordinates_do_not_borrow_rules() {
    let categories = vec!["Owner".into(), "Guest".into()];
    let per_cat = vec![
        vec![
            Rule { cast: false },
            Rule { cast: false },
            Rule { cast: true },
            Rule { cast: false },
        ],
        vec![],
    ];
    let mut table = BindingPowerTable::new();
    table.operators = ["Good", "Bad", "Rep", "MissingRule", "MissingCategory", "Capture"]
        .into_iter()
        .map(|label| op(label, "Owner", "!", 2))
        .collect();
    table.operators[0].mixfix_parts = vec![part("Guest", &["good"], &[])];
    table.operators[1].mixfix_parts = vec![part("Unknown", &["bad"], &[])];
    let mut repetition = part("Unknown", &["not-consumed"], &[]);
    repetition.repetition = Some(MixfixRep {
        separator: ",".into(),
        min: 0,
        close: vec![],
    });
    table.operators[2].mixfix_parts = vec![repetition];
    table.operators[3].mixfix_parts = vec![part("Guest", &["missing-rule"], &[])];
    table.operators[4].mixfix_parts = vec![part("Guest", &["missing-category"], &[])];
    let mut capture = part("Ident", &[], &[]);
    capture.capture_kind = Some("Ident".into());
    table.operators[5].mixfix_parts = vec![capture, part("Guest", &["after-capture"], &[])];
    let labels = HashMap::from([
        (("Owner".into(), "Good".into()), (0, 0)),
        (("Owner".into(), "Bad".into()), (0, 1)),
        (("Owner".into(), "Rep".into()), (0, 2)),
        (("Owner".into(), "MissingRule".into()), (0, 77)),
        (("Owner".into(), "MissingCategory".into()), (9, 0)),
        (("Owner".into(), "Capture".into()), (0, 3)),
    ]);
    let grouped = group_ops_by_cat_terminal(&table, &categories, &labels);
    let effects = RefCell::new(vec![]);
    let actual = build_mixfix_factoring_with(
        &categories,
        &per_cat,
        &[],
        &grouped,
        usize::MAX,
        0xfe00,
        |name, observed_categories, context, label| {
            assert!(std::ptr::eq(observed_categories, categories.as_slice()));
            effects
                .borrow_mut()
                .push(Event::Resolve(label.into(), context, name.into()));
            if name == "Guest" {
                Ok(1)
            } else {
                Err(())
            }
        },
        |rule| {
            let index = per_cat[0]
                .iter()
                .position(|source| std::ptr::eq(source, rule))
                .expect("original rule borrow");
            effects.borrow_mut().push(Event::Cast(index));
            rule.cast
        },
    );
    assert_eq!(
        effects.into_inner(),
        vec![
            item_call("Good", "Guest"),
            action_call("Good", "Guest"),
            item_call("Bad", "Unknown"),
            action_call("Bad", "Unknown"),
            item_call("MissingRule", "Guest"),
            action_call("MissingRule", "Guest"),
            item_call("MissingCategory", "Guest"),
            action_call("MissingCategory", "Guest"),
            action_call("Capture", "Guest"),
            Event::Cast(0),
            Event::Cast(2),
            Event::Cast(3),
        ]
    );
    let expected = vec![MixfixFactoring {
        dispatch_cat_src_idx: 0,
        buckets: vec![MixfixBucket {
            trigger: "!".into(),
            slice: vec![(2, 0, 0), (2, 0, 1), (2, 0, 2), (2, 0, 77), (2, 9, 0), (2, 0, 3)],
            groups: vec![],
            ineligible: vec![],
            singletons: vec![
                SingletonMember {
                    rule_idx: 2,
                    reason: SingletonReason::CastMachinery,
                },
                SingletonMember {
                    rule_idx: 3,
                    reason: SingletonReason::EmptySequence,
                },
                SingletonMember {
                    rule_idx: 0,
                    reason: SingletonReason::LoneRootChild,
                },
                SingletonMember {
                    rule_idx: 77,
                    reason: SingletonReason::LoneRootChild,
                },
                SingletonMember {
                    rule_idx: 0,
                    reason: SingletonReason::LoneRootChild,
                },
            ],
        }],
        refusals: vec![],
    }];
    assert_eq!(format!("{actual:?}"), format!("{expected:?}"));
}

#[test]
fn finite_cap_follows_tier_filter_but_absorbability_uses_all_operator_keys() {
    let categories = vec!["Owner".into(), "Guest".into()];
    let per_cat = vec![(0..4).map(|_| Rule { cast: false }).collect(), vec![Rule { cast: false }]];
    let mut table = BindingPowerTable::new();
    table.operators = vec![
        op("Binary", "Owner", "!", 2),
        op("A", "Owner", "!", 4),
        op("B", "Owner", "!", 6),
        op("BeyondCap", "Owner", "!", 8),
        op("Plus", "Guest", "+", 10),
    ];
    table.operators[0].is_mixfix = false;
    table.operators[1].mixfix_parts = vec![part("Guest", &["("], &["+"])];
    table.operators[2].mixfix_parts = vec![part("Guest", &["("], &["end"])];
    table.operators[3].mixfix_parts = vec![part("Unknown", &["unvisited"], &[])];
    table.operators[4].is_mixfix = false;
    let labels = HashMap::from([
        (("Owner".into(), "Binary".into()), (0, 0)),
        (("Owner".into(), "A".into()), (0, 1)),
        (("Owner".into(), "B".into()), (0, 2)),
        (("Owner".into(), "BeyondCap".into()), (0, 3)),
        (("Guest".into(), "Plus".into()), (1, 0)),
    ]);
    let grouped = group_ops_by_cat_terminal(&table, &categories, &labels);
    let effects = RefCell::new(vec![]);
    let actual = build_mixfix_factoring_with(
        &categories,
        &per_cat,
        &[],
        &grouped,
        2,
        0xfe00,
        |name, _, context, label| {
            assert_eq!(name, "Guest");
            effects
                .borrow_mut()
                .push(Event::Resolve(label.into(), context, name.into()));
            Ok::<_, ()>(1)
        },
        |rule| {
            let index = per_cat[0]
                .iter()
                .position(|source| std::ptr::eq(source, rule))
                .expect("selected original rule");
            effects.borrow_mut().push(Event::Cast(index));
            false
        },
    );
    assert_eq!(
        effects.into_inner(),
        vec![
            item_call("A", "Guest"),
            action_call("A", "Guest"),
            item_call("B", "Guest"),
            action_call("B", "Guest"),
            Event::Cast(1),
            Event::Cast(2),
        ]
    );
    assert_eq!(actual.len(), 1);
    assert!(actual[0].refusals.is_empty());
    assert_eq!(actual[0].dispatch_cat_src_idx, 0);
    assert_eq!(actual[0].buckets.len(), 1);
    let bucket = &actual[0].buckets[0];
    assert_eq!(bucket.trigger, "!");
    assert_eq!(bucket.slice, vec![(4, 0, 1), (6, 0, 2)]);
    assert!(bucket.groups.is_empty() && bucket.singletons.is_empty());
    assert_eq!(bucket.ineligible.len(), 1);
    assert_eq!(bucket.ineligible[0].member_rule_idxs, vec![1, 2]);
    assert_eq!(
        bucket.ineligible[0].reason,
        IneligibleReason::OperandAbsorbableDivergence { texts: vec!["+".into()] }
    );
    assert!(mixfix_spine_parts_len_rows(&actual).is_empty());
    let identity = mixfix_identity_partition(&grouped, 2);
    assert_eq!(identity.len(), 1);
    assert_eq!(identity[0].buckets.len(), 1);
    let off = &identity[0].buckets[0];
    assert_eq!(off.slice, bucket.slice);
    assert!(off.groups.is_empty() && off.ineligible.is_empty());
    assert_eq!(
        off.singletons
            .iter()
            .map(|s| (s.rule_idx, s.reason))
            .collect::<Vec<_>>(),
        vec![(1, SingletonReason::FactoringDisabled), (2, SingletonReason::FactoringDisabled)]
    );
    assert!(mixfix_identity_partition(&grouped, 0).is_empty());
    let empty = build_mixfix_factoring_with(
        &categories,
        &per_cat,
        &[],
        &grouped,
        0,
        0xfe00,
        |_, _, _, _| -> Result<u16, ()> { panic!("zero cap resolves no operand") },
        |_| panic!("zero cap borrows no rule"),
    );
    assert!(empty.is_empty());
}

#[test]
fn spine_parts_rows_follow_partition_order_not_result_category_order() {
    let categories = vec!["Left".into(), "Right".into()];
    let per_cat = vec![
        vec![Rule { cast: false }, Rule { cast: false }],
        vec![Rule { cast: false }, Rule { cast: false }],
    ];
    let mut table = BindingPowerTable::new();
    table.operators = vec![
        op("RightA", "Left", "z", 8),
        op("RightB", "Left", "z", 4),
        op("LeftA", "Right", "a", 6),
        op("LeftB", "Right", "a", 2),
    ];
    for (index, operator) in table.operators.iter_mut().enumerate() {
        operator.result_category = if index < 2 { "Right" } else { "Left" }.into();
        operator.is_cross_category = true;
        operator.nullary_literals = vec!["(".into(), if index % 2 == 0 { "a" } else { "b" }.into()];
    }
    let labels = HashMap::from([
        (("Right".into(), "RightA".into()), (1, 0)),
        (("Right".into(), "RightB".into()), (1, 1)),
        (("Left".into(), "LeftA".into()), (0, 0)),
        (("Left".into(), "LeftB".into()), (0, 1)),
    ]);
    let grouped = group_ops_by_cat_terminal(&table, &categories, &labels);
    let actual = build_mixfix_factoring_with(
        &categories,
        &per_cat,
        &[],
        &grouped,
        2,
        0xfe00,
        |_, _, _, _| -> Result<u16, ()> { panic!("nullary members resolve no operand") },
        |_| false,
    );
    assert_eq!(actual.len(), 2);
    assert!(actual.iter().all(|fact| fact.refusals.is_empty()));
    assert_eq!(
        mixfix_spine_parts_len_rows(&actual),
        vec![(1, SPINE_RULE_BASE), (0, SPINE_RULE_BASE)]
    );
    for (index, fact) in actual.iter().enumerate() {
        assert_eq!(fact.dispatch_cat_src_idx, index as u16);
        assert_eq!(fact.buckets.len(), 1);
        let bucket = &fact.buckets[0];
        assert_eq!(bucket.groups.len(), 1);
        assert!(bucket.ineligible.is_empty() && bucket.singletons.is_empty());
        let group = &bucket.groups[0];
        assert_eq!(group.expected_cats_union, vec![index as u16]);
        assert_eq!(group.fixb_literal.as_deref(), Some("("));
        assert_eq!(group.min_member_rule_idx, 0);
        assert_eq!(group.min_l_bp, if index == 0 { 4 } else { 2 });
    }
}
