//! Callback and owner-index contracts of the relocated original discovery loops.

use std::cell::{Cell, RefCell};
use std::collections::HashMap;

use mettail_prattail::binding_power::BindingPowerTable;
use mettail_prattail::wpda_rule_analysis::binder::{
    build_prefix_bp_map_with, BinderPosition, BinderShape,
};
use mettail_prattail::wpda_rule_analysis::factoring::{
    discover_prefix_members_with, MemberKind, PrefixAtomicObservation, SpineItem,
};

// Neither Clone nor Copy: the callbacks must borrow the caller's original row.
struct Rule {
    index: usize,
    trigger: String,
}

fn shape(positions: Vec<BinderPosition>) -> BinderShape {
    BinderShape {
        label: "SharedBoundary".into(),
        result_cat: "Owner".into(),
        leading_category: None,
        leading_ident_capture: None,
        positions,
        is_multi: false,
        has_binder: false,
        action_arity: 0,
        action_args: vec![],
        body_cat: None,
        param_cats: vec![],
    }
}

#[test]
fn discovery_borrows_rules_and_preserves_lazy_callback_order_and_full_members() {
    let rules: Vec<_> = (0..8)
        .map(|index| Rule {
            index,
            trigger: if index == 5 { "(" } else { "call" }.into(),
        })
        .collect();
    let calls = RefCell::new(vec![]);
    let members = discover_prefix_members_with(
        &["Guest".into(), "Owner".into()],
        1,
        &rules,
        &HashMap::from([((1, 6), 9)]),
        |rule| {
            assert!(std::ptr::eq(rule, &rules[rule.index]));
            calls.borrow_mut().push(("atomic", rule.index));
            match rule.index {
                0 => PrefixAtomicObservation::CrossCatPrefixUnary,
                1 => PrefixAtomicObservation::NullaryLiteralRun {
                    trigger: "(".into(),
                    trailing_literals: vec!["unit".into(), ")".into()],
                },
                2 => PrefixAtomicObservation::CrossCatProjection,
                _ => PrefixAtomicObservation::Other,
            }
        },
        |rule| {
            assert!(std::ptr::eq(rule, &rules[rule.index]));
            calls.borrow_mut().push(("binder", rule.index));
            if rule.index == 3 {
                None
            } else {
                Some(shape(vec![
                    BinderPosition::Literal("<".into()),
                    BinderPosition::ParamParse {
                        cat: if rule.index == 7 { "Unknown" } else { "Guest" }.into(),
                        collection: None,
                    },
                    BinderPosition::Literal(">".into()),
                ]))
            }
        },
        |rule| {
            assert!(std::ptr::eq(rule, &rules[rule.index]));
            calls.borrow_mut().push(("leading", rule.index));
            (rule.index != 4).then_some(rule.trigger.as_str())
        },
    );
    assert_eq!(
        calls.into_inner(),
        vec![
            ("atomic", 0),
            ("atomic", 1),
            ("atomic", 2),
            ("atomic", 3),
            ("binder", 3),
            ("atomic", 4),
            ("binder", 4),
            ("leading", 4),
            ("atomic", 5),
            ("binder", 5),
            ("leading", 5),
            ("atomic", 6),
            ("binder", 6),
            ("leading", 6),
            ("atomic", 7),
            ("binder", 7),
            ("leading", 7),
        ]
    );
    assert_eq!(members.len(), 3);
    let (trigger, nullary) = &members[0];
    assert_eq!(trigger, "(");
    assert_eq!(nullary.kind, MemberKind::Nullary);
    assert_eq!(nullary.rule_idx, 1);
    assert_eq!(nullary.total_positions, 2);
    assert_eq!(nullary.body_src_idx, None);
    assert!(!nullary.truncated);
    assert_eq!(
        nullary.items,
        vec![
            SpineItem::Literal {
                text: "unit".into(),
                required_top_cat: None
            },
            SpineItem::Literal { text: ")".into(), required_top_cat: None },
        ]
    );
    let (trigger, binder) = &members[1];
    assert_eq!(trigger, "call");
    assert_eq!(binder.kind, MemberKind::Binder);
    assert_eq!(binder.rule_idx, 6);
    assert_eq!(binder.total_positions, 3);
    assert_eq!(binder.body_src_idx, Some(0));
    assert!(!binder.truncated);
    assert_eq!(
        binder.items,
        vec![
            SpineItem::Literal { text: "<".into(), required_top_cat: None },
            SpineItem::ParamParse { cat_src_idx: 0, cur_bp: 9 },
            SpineItem::Literal {
                text: ">".into(),
                required_top_cat: Some(0)
            },
        ]
    );
    let (trigger, truncated) = &members[2];
    assert_eq!(trigger, "call");
    assert_eq!(truncated.kind, MemberKind::Binder);
    assert_eq!(truncated.rule_idx, 7);
    assert_eq!(truncated.total_positions, 3);
    assert_eq!(truncated.body_src_idx, Some(1));
    assert!(truncated.truncated);
    assert_eq!(
        truncated.items,
        vec![SpineItem::Literal { text: "<".into(), required_top_cat: None },]
    );
    assert!(members
        .iter()
        .all(|(_, member)| member.mixfix_coords.is_empty()));
}

#[test]
fn empty_discovery_calls_no_classifier_or_literal_reader() {
    let rules: Vec<Rule> = vec![];
    let members = discover_prefix_members_with(
        &[],
        0,
        &rules,
        &HashMap::new(),
        |_| panic!("empty discovery must not classify atomic rules"),
        |_| panic!("empty discovery must not classify binder rules"),
        |_| panic!("empty discovery must not read leading syntax"),
    );
    assert!(members.is_empty());
}

#[test]
fn prefix_bp_reads_only_eligible_metadata_in_original_nested_row_order() {
    let rows: Vec<Vec<Rule>> = vec![
        vec![],
        (0..3)
            .map(|index| Rule { index, trigger: "Owner".into() })
            .collect(),
        vec![Rule { index: 3, trigger: "Guest".into() }],
    ];
    let calls = RefCell::new(vec![]);
    let map = build_prefix_bp_map_with(
        &rows,
        &BindingPowerTable::new(),
        |rule| {
            calls.borrow_mut().push(("eligible", rule.index));
            rule.index != 1
        },
        |rule| {
            calls.borrow_mut().push(("metadata", rule.index));
            (rule.trigger.clone(), Some(10 + rule.index as u8))
        },
    );
    assert_eq!(
        calls.into_inner(),
        vec![
            ("eligible", 0),
            ("metadata", 0),
            ("eligible", 1),
            ("eligible", 2),
            ("metadata", 2),
            ("eligible", 3),
            ("metadata", 3),
        ]
    );
    assert_eq!(map, HashMap::from([((1, 0), 10), ((1, 2), 12), ((2, 0), 13)]));
}

#[test]
fn prefix_bp_retains_original_cast_key_overwrite_semantics() {
    let rows = vec![(0..=65536)
        .map(|index| Rule { index, trigger: String::new() })
        .collect::<Vec<_>>()];
    let tested = Cell::new(0usize);
    let accepted = Cell::new(0usize);
    let map = build_prefix_bp_map_with(
        &rows,
        &BindingPowerTable::new(),
        |rule| {
            tested.set(tested.get() + 1);
            rule.index == 0 || rule.index == 65536
        },
        |rule| {
            accepted.set(accepted.get() + 1);
            ("Owner".into(), Some(if rule.index == 0 { 9 } else { 21 }))
        },
    );
    assert_eq!(tested.get(), 65537);
    assert_eq!(accepted.get(), 2);
    assert_eq!(map, HashMap::from([((0, 0), 21)]));
}
