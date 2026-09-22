//! Original mixfix descriptor ordering, source identity, and coordinate baselines.

use super::*;
use mettail_ast::grammar::rule_fixture;
use mettail_prattail::binding_power::{BindingPowerTable, InfixOperator, MixfixPart, MixfixRep};
use proc_macro2::Span;
use syn::Ident;

fn rule(label: &str, category: &str) -> GrammarRule {
    rule_fixture(Ident::new(label, Span::call_site()), Ident::new(category, Span::call_site()))
}

fn operator(label: &str, category: &str, terminal: &str, bp: u8) -> InfixOperator {
    InfixOperator {
        terminal: terminal.into(),
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

fn literal(text: &str) -> SpineItem {
    SpineItem::Literal {
        text: text.into(),
        required_top_cat: None,
    }
}

#[test]
fn original_grouping_preserves_source_borrows_sorted_keys_and_first_category_last_label() {
    let categories = vec!["Z".into(), "A".into(), "Z".into()];
    let per_cat = vec![
        vec![rule("Same", "Z"), rule("Other", "Z")],
        vec![rule("Alpha", "A")],
        vec![rule("Same", "Z"), rule("Same", "Z")],
    ];
    let labels = super::super::infix::build_label_index(&categories, &per_cat);
    assert_eq!(labels.get(&("Z".into(), "Same".into())), Some(&(2, 1)));
    let mut table = BindingPowerTable::new();
    table.operators = vec![
        operator("Same", "Z", "z", 2),
        operator("Alpha", "A", "b", 4),
        operator("Other", "Z", "a", 6),
        operator("Same", "Z", "z", 8),
        operator("Same", "Undeclared", "z", 10),
        operator("Missing", "Z", "z", 12),
        operator("Same", "Z", "z", 14),
    ];
    table.operators[1].is_mixfix = false;
    table.operators[1].is_postfix = true;
    table.operators[2].is_mixfix = false;
    table.operators[3].is_mixfix = false;
    table.operators[3].is_postfix = true;
    // This row has valid result coordinates but an unresolved operand category.
    table.operators[4].result_category = "Z".into();
    table.operators[4].is_cross_category = true;
    let grouped = super::super::infix::group_ops_by_cat_terminal(&table, &categories, &labels);
    assert_eq!(
        grouped.keys().cloned().collect::<Vec<_>>(),
        vec![(0, "a".into()), (0, "z".into()), (1, "b".into())]
    );
    let expected_rows = [vec![(2, 0, 1)], vec![(0, 2, 1), (3, 2, 1), (6, 2, 1)], vec![(1, 1, 0)]];
    for (rows, expected) in grouped.values().zip(expected_rows) {
        assert_eq!(rows.len(), expected.len());
        for (row, (operator_idx, result_src_idx, rule_idx)) in rows.iter().zip(expected) {
            assert!(std::ptr::eq(row.op, &table.operators[operator_idx]));
            assert_eq!((row.result_src_idx, row.rule_idx), (result_src_idx, rule_idx));
        }
    }
}

#[test]
fn original_member_coordinates_preserve_repetition_capture_and_unresolved_stop_order() {
    let categories = vec!["Z".into(), "A".into(), "Z".into(), "Ident".into()];
    let mut op = operator("Coordinates", "Z", "!", 2);
    op.mixfix_parts = vec![part("Z", &["("], &[")"]), part("A", &["[", "{"], &["}"])];
    let items = vec![
        literal("("),
        SpineItem::ParamParse { cat_src_idx: 0, cur_bp: 0 },
        literal(")"),
        literal("["),
        literal("{"),
        SpineItem::ParamParse { cat_src_idx: 1, cur_bp: 0 },
        literal("}"),
    ];
    let coords = vec![
        (2, 0, 0),
        (2, 0, 1),
        (0, 0, 0),
        (0, 0, 1),
        (1, 0, 1),
        (1, 0, 2),
        (0, 1, 0),
        (0, 1, 1),
    ];
    assert_eq!(mixfix_member_items(&op, &categories), (items.clone(), coords.clone(), false));

    let stopped_part = part("Undeclared", &["before-stop"], &["after-stop"]);
    op.mixfix_parts.push(stopped_part);
    op.mixfix_parts.push(part("Z", &["unvisited-part"], &[]));
    let mut after_preceding_items = items.clone();
    after_preceding_items.push(literal("before-stop"));
    let mut after_preceding_coords = coords.clone();
    after_preceding_coords.push((1, 1, 1));
    assert_eq!(
        mixfix_member_items(&op, &categories),
        (after_preceding_items.clone(), after_preceding_coords.clone(), true)
    );
    op.mixfix_parts[2].operand_category = "Ident".into();
    op.mixfix_parts[2].capture_kind = Some("Ident".into());
    assert_eq!(
        mixfix_member_items(&op, &categories),
        (after_preceding_items, after_preceding_coords, true)
    );
    op.mixfix_parts[2].capture_kind = None;
    op.mixfix_parts[2].repetition = Some(MixfixRep {
        separator: ",".into(),
        min: 0,
        close: vec!["rep-close".into()],
    });
    assert_eq!(mixfix_member_items(&op, &categories), (items, coords, true));

    op.mixfix_parts.clear();
    op.nullary_literals = vec!["tail".into(); 256];
    let (items, coords, truncated) = mixfix_member_items(&op, &categories);
    assert_eq!(items, vec![literal("tail"); 256]);
    assert_eq!(coords.len(), 257);
    assert_eq!(coords[0], (2, 0, 0));
    assert_eq!(coords[1], (2, 0, 1));
    assert_eq!(coords[255], (2, 0, 255));
    assert_eq!(coords[256], (2, 0, 0));
    assert!(!truncated);
}
