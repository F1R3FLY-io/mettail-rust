//! Failure-injection correspondence for the original assembly callback loops.
//! PrefixCallbackFailure supplies Result laws; the worker-specific source
//! schedules remain those in GroupingSourceDescriptorProjection,
//! PrefixDiscoveryProjection and ParikhDescriptorProjection.

use super::binder::{build_prefix_bp_map_with, try_build_prefix_bp_map_with};
use super::grouping::{
    grouping_source_categories_for_result, try_grouping_source_categories_for_result,
};
use super::parikh::{build_alphabet, try_build_alphabet};
use crate::binding_power::{Associativity, BindingPowerTable, InfixRuleInfo};
use std::cell::RefCell;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Call {
    Category(usize),
    Infix(usize),
    Projection(usize),
    Unary(usize),
    Metadata(usize),
    Alphabet(usize),
}

struct Probe {
    fail_at: Option<usize>,
    calls: RefCell<Vec<Call>>,
}

impl Probe {
    fn new(fail_at: Option<usize>) -> Self {
        Self { fail_at, calls: RefCell::new(Vec::new()) }
    }

    fn visit(&self, call: Call) -> Result<(), usize> {
        let mut calls = self.calls.borrow_mut();
        let index = calls.len();
        calls.push(call);
        if self.fail_at == Some(index) {
            Err(index)
        } else {
            Ok(())
        }
    }

    fn trace(&self) -> Vec<Call> {
        self.calls.borrow().clone()
    }
}

fn infix(terminal: &str, operand: &str, result: &str, cross: bool) -> InfixRuleInfo {
    InfixRuleInfo {
        label: "Operator".into(),
        terminal: terminal.into(),
        category: operand.into(),
        result_category: result.into(),
        associativity: Associativity::Left,
        shares_level_with_previous: false,
        is_cross_category: cross,
        is_postfix: false,
        is_mixfix: false,
        mixfix_parts: Vec::new(),
        nullary_literals: Vec::new(),
    }
}

fn category(rule: usize) -> String {
    match rule {
        0 | 2 => "Home",
        3 => "Operand",
        _ => "Other",
    }
    .into()
}

fn grouping_infix(rule: usize) -> Option<InfixRuleInfo> {
    match rule {
        0 => Some(infix("to-home", "Operand", "Home", true)),
        3 => Some(infix("to-operand", "Other", "Operand", true)),
        _ => None,
    }
}

fn projection(rule: usize) -> Option<String> {
    (rule == 0).then(|| "Operand".to_string())
}

#[test]
fn checked_grouping_preserves_double_projection_and_every_failure_prefix() {
    let categories = vec!["Home".into(), "Operand".into(), "Other".into()];
    let rules = vec![0, 1, 2, 3, 4];
    let per_cat = vec![vec![0, 2, 0], vec![3], vec![1, 4]];
    let plain = Probe::new(None);
    let expected = grouping_source_categories_for_result(
        &categories,
        &rules,
        &per_cat,
        0,
        |rule| {
            plain
                .visit(Call::Category(*rule))
                .expect("infallible category probe");
            category(*rule)
        },
        |rule| {
            plain
                .visit(Call::Infix(*rule))
                .expect("infallible infix probe");
            grouping_infix(*rule)
        },
        |rule| {
            plain
                .visit(Call::Projection(*rule))
                .expect("infallible projection probe");
            projection(*rule)
        },
    );
    assert_eq!(expected, vec![0, 1, 2]);
    let expected_calls = vec![
        Call::Category(0),
        Call::Infix(0),
        Call::Category(1),
        Call::Category(2),
        Call::Infix(2),
        Call::Category(3),
        Call::Category(4),
        Call::Projection(0),
        Call::Projection(2),
        Call::Projection(0),
        Call::Projection(0),
        Call::Projection(2),
        Call::Projection(0),
        Call::Category(0),
        Call::Category(1),
        Call::Category(2),
        Call::Category(3),
        Call::Infix(3),
        Call::Category(4),
    ];
    assert_eq!(
        plain.trace(),
        expected_calls,
        "original two projection passes must remain observable"
    );
    for fail_at in std::iter::once(None).chain((0..expected_calls.len()).map(Some)) {
        let probe = Probe::new(fail_at);
        let actual = try_grouping_source_categories_for_result(
            &categories,
            &rules,
            &per_cat,
            0,
            |rule| {
                probe.visit(Call::Category(*rule))?;
                Ok(category(*rule))
            },
            |rule| {
                probe.visit(Call::Infix(*rule))?;
                Ok(grouping_infix(*rule))
            },
            |rule| {
                probe.visit(Call::Projection(*rule))?;
                Ok(projection(*rule))
            },
        );
        if let Some(index) = fail_at {
            assert_eq!(actual, Err(index), "callback {index} must not publish a partial roster");
            assert_eq!(probe.trace(), expected_calls[..=index]);
        } else {
            assert_eq!(actual.expect("all-ok grouping must finish"), expected);
            assert_eq!(probe.trace(), expected_calls);
        }
    }
}

fn prefix_metadata(rule: usize) -> (String, Option<u8>) {
    ("Home".into(), (rule == 0).then_some(17))
}

#[test]
fn checked_prefix_map_skips_metadata_and_preserves_every_failure_prefix() {
    let rows = vec![vec![0, 1, 2], Vec::new(), vec![3]];
    let table = BindingPowerTable::new();
    let plain = Probe::new(None);
    let expected = build_prefix_bp_map_with(
        &rows,
        &table,
        |rule| {
            plain
                .visit(Call::Unary(*rule))
                .expect("infallible eligibility probe");
            rule % 2 == 0
        },
        |rule| {
            plain
                .visit(Call::Metadata(*rule))
                .expect("infallible metadata probe");
            prefix_metadata(*rule)
        },
    );
    let expected_calls = vec![
        Call::Unary(0),
        Call::Metadata(0),
        Call::Unary(1),
        Call::Unary(2),
        Call::Metadata(2),
        Call::Unary(3),
    ];
    assert_eq!(plain.trace(), expected_calls);
    assert_eq!(expected.len(), 2);
    assert_eq!(expected.get(&(0, 0)), Some(&17));
    assert!(expected.contains_key(&(0, 2)));
    for fail_at in std::iter::once(None).chain((0..expected_calls.len()).map(Some)) {
        let probe = Probe::new(fail_at);
        let actual = try_build_prefix_bp_map_with(
            &rows,
            &table,
            |rule| {
                probe.visit(Call::Unary(*rule))?;
                Ok(rule % 2 == 0)
            },
            |rule| {
                probe.visit(Call::Metadata(*rule))?;
                Ok(prefix_metadata(*rule))
            },
        );
        if let Some(index) = fail_at {
            assert_eq!(actual, Err(index), "callback {index} must not publish a partial BP map");
            assert_eq!(probe.trace(), expected_calls[..=index]);
        } else {
            assert_eq!(actual.expect("all-ok prefix map must finish"), expected);
            assert_eq!(probe.trace(), expected_calls);
        }
    }
}

fn alphabet_infix(rule: usize) -> Option<InfixRuleInfo> {
    match rule {
        0 | 4 => Some(infix("z", "Operand", "Home", true)),
        1 => None,
        2 => Some(infix("not-cross", "Operand", "Home", false)),
        3 => Some(infix("a", "Other", "Home", true)),
        5 => Some(infix("same-category", "Home", "Home", true)),
        _ => unreachable!("bounded alphabet fixture"),
    }
}

#[test]
fn checked_alphabet_preserves_sorted_assignment_and_every_failure_prefix() {
    let rules = vec![0, 1, 2, 3, 4, 5];
    let plain = Probe::new(None);
    let expected = build_alphabet(&rules, |rule| {
        plain
            .visit(Call::Alphabet(*rule))
            .expect("infallible alphabet probe");
        alphabet_infix(*rule)
    });
    let expected_calls: Vec<_> = rules.iter().copied().map(Call::Alphabet).collect();
    assert_eq!(plain.trace(), expected_calls);
    assert_eq!(expected.coarse_bit, 2);
    assert_eq!(expected.trigger_bit.len(), 2);
    assert_eq!(expected.trigger_bit.get("a"), Some(&0));
    assert_eq!(expected.trigger_bit.get("z"), Some(&1));
    for fail_at in std::iter::once(None).chain((0..expected_calls.len()).map(Some)) {
        let probe = Probe::new(fail_at);
        let actual: Result<_, usize> = try_build_alphabet(&rules, |rule| {
            probe.visit(Call::Alphabet(*rule))?;
            Ok(alphabet_infix(*rule))
        });
        if let Some(index) = fail_at {
            assert!(
                matches!(actual, Err(error) if error == index),
                "callback {index} must not publish a partial alphabet"
            );
            assert_eq!(probe.trace(), expected_calls[..=index]);
        } else {
            let actual = actual.expect("all-ok alphabet must finish");
            assert_eq!(actual.trigger_bit, expected.trigger_bit);
            assert_eq!(actual.coarse_bit, expected.coarse_bit);
            assert_eq!(actual.top(), expected.top());
            assert_eq!(probe.trace(), expected_calls);
        }
    }
}
