//! Original atomic prefix rows and same-category led-table lookup snapshots.
//! The expected quotations are literal fixtures, not a second classifier.

use super::*;
use mettail_ast::grammar::rule_fixture;
use mettail_prattail::binding_power::{BindingPowerTable, InfixOperator};
use proc_macro2::Span;
use syn::parse_quote;

fn name(text: &str) -> Ident {
    Ident::new(text, Span::call_site())
}

fn row_text(rows: Vec<PrefixArmDescriptor>) -> Vec<(String, Option<String>, u16, u16)> {
    rows.into_iter()
        .map(|row| {
            (
                row.pattern.to_string(),
                row.extra_guard.map(|guard| guard.to_string()),
                row.rule_idx,
                row.category_src_idx,
            )
        })
        .collect()
}

#[test]
fn atomic_prefix_baseline_six_quotation_sites_preserve_indices() {
    for (shape, pattern, guard) in [
        (
            AtomicShape::LiteralInteger,
            quote! { Some(mettail_prattail::automata::TokenKind::Integer) },
            None,
        ),
        (
            AtomicShape::LiteralBoolean,
            quote! {
                Some(mettail_prattail::automata::TokenKind::True)
                | Some(mettail_prattail::automata::TokenKind::False)
                | Some(mettail_prattail::automata::TokenKind::BooleanLit)
            },
            None,
        ),
        (
            AtomicShape::LiteralString,
            quote! { Some(mettail_prattail::automata::TokenKind::StringLit) },
            None,
        ),
        (
            AtomicShape::LiteralFloat,
            quote! { Some(mettail_prattail::automata::TokenKind::Float) },
            None,
        ),
        (
            AtomicShape::TerminalKeyword {
                terminal_text: "a|b".into(),
                wrapper_variant: name("UnusedWrapper"),
            },
            quote! { Some(mettail_prattail::automata::TokenKind::Fixed(__kw)) },
            Some(quote! { __kw == "a|b" }),
        ),
        (
            AtomicShape::VarRule {
                wrapper_variant: name("UnusedVariableWrapper"),
            },
            quote! { Some(mettail_prattail::automata::TokenKind::Ident) },
            None,
        ),
    ] {
        for (category_idx, rule_idx) in [(0, u16::MAX), (u16::MAX, 7)] {
            assert_eq!(
                row_text(atomic_arm_descriptors(category_idx, rule_idx, &shape)),
                vec![(
                    pattern.to_string(),
                    guard.as_ref().map(ToString::to_string),
                    rule_idx,
                    category_idx,
                )],
                "original branch {shape:?}",
            );
        }
    }
}

#[test]
fn atomic_prefix_baseline_patterned_uses_home_context_and_order() {
    let shape = AtomicShape::LiteralPatterned {
        cat_name: "Value".into(),
        family: LiteralFamily::Integer,
        native_type: parse_quote!(CanonicalBigInt),
        wrapper_variant: name("UnusedNativeWrapper"),
        rust_code: quote! { must_not_be_evaluated(text) },
    };
    let rows = row_text(atomic_arm_descriptors(31, 17, &shape));
    let guard = Some(quote! { __cat == "Value" }.to_string());
    assert_eq!(
        rows,
        vec![
            (
                quote! { Some(mettail_prattail::automata::TokenKind::IntegerLit(__cat)) }
                    .to_string(),
                guard.clone(),
                17,
                31,
            ),
            (
                quote! { Some(mettail_prattail::automata::TokenKind::Custom(__cat)) }.to_string(),
                guard,
                17,
                31,
            ),
            (
                quote! { Some(mettail_prattail::automata::TokenKind::Integer) }.to_string(),
                None,
                17,
                31,
            ),
        ],
        "CanonicalBigInt's bare Integer row exists in HomeCategory, not FirstSet",
    );
}

#[test]
fn atomic_prefix_baseline_all_excluded_shapes_are_empty() {
    for shape in [
        AtomicShape::CrossCatProjection {
            source_cat_name: "Source".into(),
            wrapper_variant: name("Projection"),
        },
        AtomicShape::CrossCatPrefixUnary {
            trigger: "start".into(),
            source_cat_name: "Source".into(),
            wrapper_variant: name("CrossPrefix"),
        },
        AtomicShape::PrefixOperator {
            trigger: "-".into(),
            operand_cat_name: "Value".into(),
        },
        AtomicShape::NullaryLiteralRun {
            trigger: "Map".into(),
            trailing_literals: vec!["(".into(), ")".into()],
            wrapper_variant: name("EmptyMap"),
        },
        AtomicShape::NonAtomic,
    ] {
        assert!(atomic_arm_descriptors(12, 34, &shape).is_empty(), "excluded {shape:?}");
    }
}

fn operator(label: &str, category: &str, result: &str, left_bp: u8) -> InfixOperator {
    InfixOperator {
        terminal: "irrelevant".into(),
        category: category.into(),
        result_category: result.into(),
        left_bp,
        right_bp: 253,
        label: label.into(),
        is_cross_category: true,
        is_postfix: true,
        is_mixfix: true,
        mixfix_parts: Vec::new(),
        nullary_literals: vec!["unused".into()],
    }
}

#[test]
fn atomic_prefix_baseline_led_lookup_first_matching_row_and_exact_fields() {
    let rule = rule_fixture(name("Chosen"), name("RuleCategoryIsNotRead"));
    let mut table = BindingPowerTable {
        operators: vec![
            operator("Other", "Expr", "Expr", 1),
            operator("Chosen", "WrongResult", "WrongResult", 2),
            operator("Chosen", "DifferentSource", "Expr", 3),
            operator("Chosen", "Expr", "Expr", 0),
            operator("Chosen", "Expr", "Expr", u8::MAX),
        ],
    };
    assert_eq!(same_category_led_left_bp(&rule, "Expr", &table), Some(0));
    table.operators.swap(3, 4);
    assert_eq!(same_category_led_left_bp(&rule, "Expr", &table), Some(u8::MAX));
    table.operators.truncate(3);
    assert_eq!(same_category_led_left_bp(&rule, "Expr", &table), None);
    assert_eq!(same_category_led_left_bp(&rule, "Undeclared", &table), None);
}
