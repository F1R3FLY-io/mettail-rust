//! Original atomic prefix rows and unified prefix descriptor payloads.
//!
//! Classification is supplied by the existing `AtomicDescriptor`; this module
//! does not recognize a rule again. Static quotations and native literal
//! payloads stay in the adapter. The original six quotation sites and the
//! patterned HomeCategory call retain their order, rows, guards, and indices.
//! `AtomicPrefixDescriptorProjection.v` verifies this representation boundary,
//! not the bucket driver, transition bodies, or parser completeness.

use super::atomic::AtomicDescriptor;
use super::native_first::EmissionContext;
use super::prefix::FirstPredicate;
use crate::binding_power::BindingPowerTable;

/// Original atomic arm row. Token payloads need not implement Clone or Display.
pub struct PrefixArmDescriptor<P> {
    pub pattern: P,
    pub extra_guard: Option<P>,
    pub rule_idx: u16,
    pub category_src_idx: u16,
}

/// The original unified bucket alternatives, with only token payloads abstracted.
/// This is descriptor data, not a replacement instruction set or new recognizer.
pub enum UnifiedDescriptor<P> {
    /// Cross-category infix LHS delegation and its original structural-literal flag.
    CrossCatLhs {
        source_src_idx: u16,
        sigil_leads_result_rule: bool,
    },
    Atomic(PrefixArmDescriptor<P>),
    /// Literal-leading binder/prefix rule and initial body category.
    BinderPrefix {
        rule_idx: u16,
        body_src_idx: u16,
    },
    /// Category-leading composite; ordinary same-category led rules are excluded
    /// by the existing producer, not by this data type.
    LeadingCategory {
        rule_idx: u16,
        source_src_idx: u16,
    },
    LeadingTokenKindCapture {
        rule_idx: u16,
        body_src_idx: u16,
        kind_name: String,
    },
    /// Nested openers preserve the existing authored order and duplicates.
    LeadingGuestBody {
        rule_idx: u16,
        body_src_idx: u16,
        open_kind: String,
        nested_open_kinds: Vec<String>,
        close_kind: String,
    },
    CrossCatPrefixUnary {
        rule_idx: u16,
        source_src_idx: u16,
        operand_bp: u8,
    },
    CrossCatProjection {
        rule_idx: u16,
        source_src_idx: u16,
    },
    /// Multi-literal nullary prefix; the existing continuation consumes its tail.
    NullaryLiteralRun {
        rule_idx: u16,
    },
}

/// Original atomic descriptor construction. The native callback receives the
/// original HomeCategory mode explicitly. Excluded shapes make no callback;
/// returned patterned rows are neither sorted, filtered, nor deduplicated.
pub fn atomic_arm_descriptors<L, P>(
    category_src_idx: u16,
    rule_idx: u16,
    shape: &AtomicDescriptor<L>,
    mut predicate_parts: impl FnMut(FirstPredicate<'_>) -> (P, Option<P>),
    mut patterned: impl FnMut(&L, EmissionContext) -> Vec<(P, Option<P>)>,
) -> Vec<PrefixArmDescriptor<P>> {
    let pattern_guards: Vec<(P, Option<P>)> = match shape {
        AtomicDescriptor::LiteralInteger => vec![predicate_parts(FirstPredicate::Integer)],
        AtomicDescriptor::LiteralBoolean => vec![predicate_parts(FirstPredicate::Boolean)],
        AtomicDescriptor::LiteralString => vec![predicate_parts(FirstPredicate::String)],
        AtomicDescriptor::LiteralFloat => vec![predicate_parts(FirstPredicate::Float)],
        AtomicDescriptor::LiteralPatterned(literal) => {
            patterned(literal, EmissionContext::HomeCategory)
        },
        AtomicDescriptor::TerminalKeyword { terminal_text, .. } => {
            vec![predicate_parts(FirstPredicate::Fixed(terminal_text))]
        },
        AtomicDescriptor::VarRule { .. } => vec![predicate_parts(FirstPredicate::Ident)],
        AtomicDescriptor::CrossCatProjection { .. }
        | AtomicDescriptor::CrossCatPrefixUnary { .. } => return Vec::new(),
        AtomicDescriptor::PrefixOperator { .. } => return Vec::new(),
        AtomicDescriptor::NullaryLiteralRun { .. } => return Vec::new(),
        AtomicDescriptor::NonAtomic => return Vec::new(),
    };
    pattern_guards
        .into_iter()
        .map(|(pattern, extra_guard)| PrefixArmDescriptor {
            pattern,
            extra_guard,
            rule_idx,
            category_src_idx,
        })
        .collect()
}

/// Original first matching table row, using label spelling and the result
/// category. Operator flags and the rule's own category are not substitutes
/// for the existing source/result string comparison.
pub fn same_category_led_left_bp(
    label: &str,
    result_category: &str,
    bp_table: &BindingPowerTable,
) -> Option<u8> {
    bp_table
        .operators
        .iter()
        .find(|operator| {
            operator.label == label
                && operator.result_category == result_category
                && operator.category == operator.result_category
        })
        .map(|operator| operator.left_bp)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::cell::RefCell;

    // Deliberately neither Clone nor Display: row construction owns opaque
    // payloads and must not derive recognition or identity by rendering them.
    struct Payload(u8);

    #[test]
    fn atomic_prefix_owned_payloads_keep_home_mode_order_guards_and_indices() {
        let events = RefCell::new(Vec::new());
        let rows = atomic_arm_descriptors(
            u16::MAX,
            17,
            &AtomicDescriptor::LiteralPatterned(41),
            |_| panic!("patterned branch must not quote a singleton"),
            |literal, context| {
                events.borrow_mut().push((*literal, context));
                vec![(Payload(1), None), (Payload(2), Some(Payload(3))), (Payload(1), None)]
            },
        );
        assert_eq!(*events.borrow(), [(41, EmissionContext::HomeCategory)]);
        assert_eq!(
            rows.into_iter()
                .map(|row| (
                    row.pattern.0,
                    row.extra_guard.map(|guard| guard.0),
                    row.rule_idx,
                    row.category_src_idx,
                ))
                .collect::<Vec<_>>(),
            [(1, None, 17, u16::MAX), (2, Some(3), 17, u16::MAX), (1, None, 17, u16::MAX)]
        );
    }

    #[test]
    fn atomic_prefix_excluded_payloads_never_invoke_constructors() {
        for shape in [
            AtomicDescriptor::CrossCatProjection {
                source_cat_name: "Source".into(),
                wrapper_variant: "Wrapper".into(),
            },
            AtomicDescriptor::CrossCatPrefixUnary {
                trigger: "start".into(),
                source_cat_name: "Source".into(),
                wrapper_variant: "Wrapper".into(),
            },
            AtomicDescriptor::PrefixOperator {
                trigger: "-".into(),
                operand_cat_name: "Value".into(),
            },
            AtomicDescriptor::NullaryLiteralRun {
                trigger: "Map".into(),
                trailing_literals: vec!["(".into(), ")".into()],
                wrapper_variant: "Empty".into(),
            },
            AtomicDescriptor::NonAtomic,
        ] {
            let rows: Vec<PrefixArmDescriptor<Payload>> = atomic_arm_descriptors(
                0,
                0,
                &shape,
                |_| panic!("excluded shape must not quote"),
                |_: &(), _| panic!("excluded shape must not expand a literal"),
            );
            assert!(rows.is_empty());
        }
    }
}
