//! Original descriptor-helper baselines before their shared-module relocation.

use super::super::binder::{
    binder_initial_body_cat, lookup_src_idx, BinderShape, CollectionSepInfo,
};
use super::*;
use std::collections::HashMap;

fn param(cat: &str) -> BinderPosition {
    BinderPosition::ParamParse { cat: cat.into(), collection: None }
}

fn optional(positions: Vec<BinderPosition>) -> BinderPosition {
    BinderPosition::OptionalGroup {
        positions,
        group_idx: 0,
        first_token_set: vec![],
    }
}

fn binder_loop(
    collection_cat: Option<&str>,
    inner_positions: Vec<BinderPosition>,
) -> BinderPosition {
    BinderPosition::BinderListLoop {
        separator: ",".into(),
        close: ")".into(),
        inner_positions,
        collection_param_cat: collection_cat.map(str::to_owned),
        allow_empty: true,
        allow_multi: true,
        slot_idx: 0,
    }
}

fn shape(positions: Vec<BinderPosition>) -> BinderShape {
    BinderShape {
        label: "DescriptorBaseline".into(),
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

fn categories() -> Vec<String> {
    ["Owner", "Operand", "Operand", "Later"]
        .map(str::to_owned)
        .to_vec()
}

#[test]
fn descriptor_lookup_keeps_first_duplicate_and_unknown_body_suppresses_nested_fallback() {
    let categories = categories();
    assert_eq!(lookup_src_idx("Operand", &categories), Some(1));
    assert_eq!(lookup_src_idx("Missing", &categories), None);

    let mut descriptor = shape(vec![optional(vec![param("Operand")]), param("Later")]);
    descriptor.body_cat = Some("Missing".into());
    assert_eq!(binder_initial_body_cat(&descriptor), Some("Missing"));
    let explicit_body = binder_initial_body_cat(&descriptor).expect("explicit body category");
    assert!(std::ptr::eq(
        explicit_body,
        descriptor
            .body_cat
            .as_deref()
            .expect("original body category")
    ));
    assert_eq!(lookup_src_idx(explicit_body, &categories), None);
    descriptor.body_cat = None;
    assert_eq!(binder_initial_body_cat(&descriptor), Some("Operand"));
}

#[test]
fn descriptor_nested_body_search_preserves_source_order_and_collection_category_precedence() {
    for (collection_cat, expected) in [(None, "First"), (Some("LoopCollection"), "LoopCollection")]
    {
        let descriptor = shape(vec![
            BinderPosition::Literal("start".into()),
            optional(vec![
                BinderPosition::TokenKindCapture {
                    kind_name: "Word".into(),
                    param_name: "word".into(),
                },
                binder_loop(
                    collection_cat,
                    vec![
                        BinderPosition::IdentTextCapture { param_name: "ident".into() },
                        optional(vec![param("First"), param("Second")]),
                        param("LoopTail"),
                    ],
                ),
                param("OptionalTail"),
            ]),
            param("OuterTail"),
        ]);
        assert_eq!(binder_initial_body_cat(&descriptor), Some(expected));
    }
}

#[test]
fn descriptor_items_use_owner_rule_binding_power_and_only_immediate_literal_guards() {
    let categories = categories();
    let positions = vec![
        BinderPosition::Literal("(".into()),
        param("Operand"),
        BinderPosition::Literal(")".into()),
        BinderPosition::Literal(";".into()),
        param("Later"),
        BinderPosition::Literal("end".into()),
    ];
    let binding_powers = HashMap::from([((0, 7), 31), ((1, 7), 9), ((0, 8), 44)]);
    for (owner, expected_bp) in [(0, 31), (99, 0)] {
        let (items, truncated) = binder_items(&positions, owner, 7, &categories, &binding_powers);
        assert!(!truncated);
        assert_eq!(
            items,
            vec![
                SpineItem::Literal { text: "(".into(), required_top_cat: None },
                SpineItem::ParamParse { cat_src_idx: 1, cur_bp: expected_bp },
                SpineItem::Literal {
                    text: ")".into(),
                    required_top_cat: Some(1)
                },
                SpineItem::Literal { text: ";".into(), required_top_cat: None },
                SpineItem::ParamParse { cat_src_idx: 3, cur_bp: expected_bp },
                SpineItem::Literal {
                    text: "end".into(),
                    required_top_cat: Some(3)
                },
            ]
        );
    }
}

#[test]
fn descriptor_items_retain_prefix_when_unresolved_or_nonmergeable_positions_stop_the_walk() {
    let categories = categories();
    let binding_powers = HashMap::from([((0, 7), 31)]);
    let blockers = vec![
        param("Missing"),
        BinderPosition::GuardSlot,
        optional(vec![param("Operand")]),
        binder_loop(None, vec![param("Operand")]),
        BinderPosition::ParamParse {
            cat: "Operand".into(),
            collection: Some(CollectionSepInfo {
                separator: ",".into(),
                close: "]".into(),
                elem_cat: "Operand".into(),
                key_val_separator: None,
                slot_idx: 0,
            }),
        },
    ];
    for blocker in blockers {
        let positions = vec![
            BinderPosition::Literal("(".into()),
            param("Operand"),
            BinderPosition::Literal(")".into()),
            blocker,
            param("Later"),
            BinderPosition::Literal("unvisited".into()),
        ];
        let (items, truncated) = binder_items(&positions, 0, 7, &categories, &binding_powers);
        assert!(truncated);
        assert_eq!(
            items,
            vec![
                SpineItem::Literal { text: "(".into(), required_top_cat: None },
                SpineItem::ParamParse { cat_src_idx: 1, cur_bp: 31 },
                SpineItem::Literal {
                    text: ")".into(),
                    required_top_cat: Some(1)
                },
            ]
        );
    }
}
