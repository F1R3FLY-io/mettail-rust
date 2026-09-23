//! The original prefix driver's ordered descriptor passes.
//!
//! This is the existing macro driver with borrowed source observations and
//! quotation callbacks. Classification, FIRST, binding powers, binder-body
//! discovery and identifier summaries call their existing shared workers.
//! Global authored rules and indexed category rules are distinct inputs.
//! `OriginalPrefixBucketDriverProjection.v` verifies finite source-observation
//! correspondence, not semantic pruning or emitted transition correctness.

use super::atomic::AtomicDescriptor;
use super::atomic_prefix::{same_category_led_left_bp, PrefixArmDescriptor, UnifiedDescriptor};
use super::binder::optional::BinderSyntaxObservation;
use super::binder::rule::BinderRuleReader;
use super::binder::{binder_initial_body_cat, BinderShape};
use super::prefix::{
    category_leading_literals, first_set_of_category, insert_unified_descriptor,
    result_has_home_var_reading, source_ident_first_is_var_only, FirstPredicate,
    IdentSummaryContext, UnifiedBucket,
};
use crate::binding_power::{compute_prefix_bp, BindingPowerTable, InfixRuleInfo};
use std::collections::{BTreeMap, HashSet};

/// The existing helper boundaries needed by the original bucket driver.
///
/// These callbacks describe the same immutable source as the inherited reader
/// and global rule roster. They retain the original classifiers and census,
/// rather than reconstructing source from normalized grammar data. `atomic_rows`
/// delegates `atomic_prefix::atomic_arm_descriptors`, including HomeCategory
/// native quotation. Callback order is significant; no classification is cached
/// between the first and second local passes.
pub trait PrefixBucketContext<'source, R: BinderRuleReader<'source>>:
    IdentSummaryContext<'source, R>
{
    fn infix(&mut self, rule: R::Rule) -> Option<InfixRuleInfo>;
    fn category_names(&mut self) -> Vec<String>;
    fn binding_power_table(&mut self) -> BindingPowerTable;
    fn explicit_prefix_bp(&self, rule: R::Rule) -> Option<u8>;
    fn binder_shape(&mut self, rule: R::Rule) -> Option<BinderShape>;
    fn atomic_rows(
        &mut self,
        category_src_idx: u16,
        rule_idx: u16,
        shape: &AtomicDescriptor<Self::Literal>,
    ) -> Vec<PrefixArmDescriptor<Self::Pattern>>;
    fn nested_guest_openers(&mut self, open: &str) -> Vec<String>;
}

/// Existing ordered map plus its separate first-insertion-order roster.
pub type PrefixBuckets<P> = (
    BTreeMap<(String, String), UnifiedBucket<P, UnifiedDescriptor<P>>>,
    Vec<(String, String)>,
);

/// Derive the original buckets; the backend still owns transition emission.
///
/// The explicit indexed roster may contain synthetic rules absent from the
/// context's global authored roster. Missing category indices keep the original
/// site-specific fallback or skip behavior. The existing compatibility gate is
/// supplied explicitly, without changing its policy or claiming its soundness.
pub fn derive_prefix_buckets<'source, R, C>(
    reader: &R,
    context: &mut C,
    category_src_idx: u16,
    category_name: &str,
    rules_in_category: &[(u16, R::Rule)],
    crosscat_lex_compat_gate: bool,
) -> PrefixBuckets<C::Pattern>
where
    R: BinderRuleReader<'source>,
    C: PrefixBucketContext<'source, R>,
    C::Pattern: Clone,
{
    let mut cross_cat_infix_sources: HashSet<String> = HashSet::new();
    for index in 0..context.rules_len() {
        let rule = context.rule_at(index);
        if reader.category(rule).to_string() != category_name {
            continue;
        }
        if let Some(info) = context.infix(rule) {
            if info.is_cross_category && info.category != info.result_category {
                cross_cat_infix_sources.insert(info.category.clone());
            }
        }
    }
    let categories = context.category_names();
    let bp_table = context.binding_power_table();
    let mut sorted_sources: Vec<&String> = cross_cat_infix_sources.iter().collect();
    sorted_sources.sort();
    let mut unified_buckets = BTreeMap::new();
    let mut unified_order = Vec::new();
    let result_leading_literals = category_leading_literals(category_name, reader, context);
    for source_cat_name in &sorted_sources {
        let source_src_idx = categories
            .iter()
            .position(|c| c == *source_cat_name)
            .map(|i| i as u16)
            .unwrap_or(0);
        let first_set = first_set_of_category(source_cat_name, reader, context);
        for ft in first_set {
            let sigil_leads_result_rule = ft
                .leading_literal
                .as_ref()
                .map(|lit| result_leading_literals.contains(lit))
                .unwrap_or(false);
            let pat_str = ft.pattern.to_string();
            let guard_str = ft
                .extra_guard
                .as_ref()
                .map(|g| g.to_string())
                .unwrap_or_default();
            let key = (pat_str, guard_str);
            if !unified_buckets.contains_key(&key) {
                unified_order.push(key.clone());
            }
            // Preserve the original clone-on-new-entry behavior here. The
            // other passes use the existing by-value insertion helper.
            let entry = unified_buckets.entry(key).or_insert_with(|| UnifiedBucket {
                pat: ft.pattern.clone(),
                extra_guard: ft.extra_guard.clone(),
                descs: Vec::new(),
            });
            entry
                .descs
                .push(UnifiedDescriptor::CrossCatLhs { source_src_idx, sigil_leads_result_rule });
        }
    }

    // Literal/binder branches are inserted during pass one. Atomic rows are
    // collected immediately, but flushed only after that complete pass.
    let mut atomic_descriptors = Vec::new();
    for &(rule_idx, rule) in rules_in_category {
        let shape = context.atomic(rule);
        atomic_descriptors.extend(context.atomic_rows(category_src_idx, rule_idx, &shape));
        if let AtomicDescriptor::CrossCatPrefixUnary {
            trigger,
            source_cat_name,
            wrapper_variant: _,
        } = &shape
        {
            let source_src_idx = categories
                .iter()
                .position(|c| c == source_cat_name)
                .map(|i| i as u16)
                .unwrap_or(category_src_idx);
            let operand_bp =
                compute_prefix_bp(source_cat_name, context.explicit_prefix_bp(rule), &bp_table);
            let (pattern, guard) = context.predicate_parts(FirstPredicate::Fixed(trigger));
            insert_unified_descriptor(
                &mut unified_buckets,
                &mut unified_order,
                pattern,
                guard,
                UnifiedDescriptor::CrossCatPrefixUnary { rule_idx, source_src_idx, operand_bp },
            );
            continue;
        }
        if let AtomicDescriptor::NullaryLiteralRun { trigger, .. } = &shape {
            let (pattern, guard) = context.predicate_parts(FirstPredicate::Fixed(trigger));
            insert_unified_descriptor(
                &mut unified_buckets,
                &mut unified_order,
                pattern,
                guard,
                UnifiedDescriptor::NullaryLiteralRun { rule_idx },
            );
            continue;
        }
        if matches!(shape, AtomicDescriptor::CrossCatProjection { .. }) {
            continue;
        }
        if let Some(shape) = context.binder_shape(rule) {
            let body_src_idx = binder_initial_body_cat(&shape)
                .and_then(|name| categories.iter().position(|c| c == name).map(|i| i as u16))
                .unwrap_or(category_src_idx);
            match reader.syntax_pattern(rule).and_then(|sp| reader.at(sp, 0)) {
                Some(BinderSyntaxObservation::Literal(trigger)) => {
                    if trigger == "(" {
                        continue;
                    }
                    let (pattern, guard) = context.predicate_parts(FirstPredicate::Fixed(trigger));
                    insert_unified_descriptor(
                        &mut unified_buckets,
                        &mut unified_order,
                        pattern,
                        guard,
                        UnifiedDescriptor::BinderPrefix { rule_idx, body_src_idx },
                    );
                },
                Some(BinderSyntaxObservation::TokenKind { name, .. }) => {
                    let kind_name = name.to_string();
                    let (pattern, guard) =
                        context.predicate_parts(FirstPredicate::CaptureName(&kind_name));
                    insert_unified_descriptor(
                        &mut unified_buckets,
                        &mut unified_order,
                        pattern,
                        guard,
                        UnifiedDescriptor::LeadingTokenKindCapture {
                            rule_idx,
                            body_src_idx,
                            kind_name,
                        },
                    );
                },
                Some(BinderSyntaxObservation::GuestBody { open, close, .. }) => {
                    let open_kind = open.to_string();
                    let nested_open_kinds = context.nested_guest_openers(&open_kind);
                    let close_kind = close.to_string();
                    let (pattern, guard) =
                        context.predicate_parts(FirstPredicate::GuestOpen(&open_kind));
                    insert_unified_descriptor(
                        &mut unified_buckets,
                        &mut unified_order,
                        pattern,
                        guard,
                        UnifiedDescriptor::LeadingGuestBody {
                            rule_idx,
                            body_src_idx,
                            open_kind,
                            nested_open_kinds,
                            close_kind,
                        },
                    );
                },
                Some(BinderSyntaxObservation::Param(_)) => {
                    if shape.leading_ident_capture.is_some() {
                        let (pattern, guard) = context.predicate_parts(FirstPredicate::Ident);
                        insert_unified_descriptor(
                            &mut unified_buckets,
                            &mut unified_order,
                            pattern,
                            guard,
                            UnifiedDescriptor::LeadingTokenKindCapture {
                                rule_idx,
                                body_src_idx,
                                kind_name: "Ident".to_string(),
                            },
                        );
                        continue;
                    }
                    let Some(source_cat_name) = shape.leading_category.as_deref() else {
                        continue;
                    };
                    let Some(source_src_idx) = categories
                        .iter()
                        .position(|category| category == source_cat_name)
                        .map(|index| index as u16)
                    else {
                        continue;
                    };
                    if same_category_led_left_bp(
                        &reader.label(rule).to_string(),
                        category_name,
                        &bp_table,
                    )
                    .is_some()
                    {
                        continue;
                    }
                    for first in first_set_of_category(source_cat_name, reader, context) {
                        insert_unified_descriptor(
                            &mut unified_buckets,
                            &mut unified_order,
                            first.pattern,
                            first.extra_guard,
                            UnifiedDescriptor::LeadingCategory { rule_idx, source_src_idx },
                        );
                    }
                },
                _ => continue,
            }
        }
    }
    for desc in atomic_descriptors {
        insert_unified_descriptor(
            &mut unified_buckets,
            &mut unified_order,
            desc.pattern.clone(),
            desc.extra_guard.clone(),
            UnifiedDescriptor::Atomic(desc),
        );
    }

    // Classify again in the original second pass. Never reuse a first-pass
    // result, move the lexical checks outside this row loop, or cache them.
    for &(rule_idx, rule) in rules_in_category {
        if let AtomicDescriptor::CrossCatProjection { source_cat_name, .. } = context.atomic(rule) {
            let source_src_idx = categories
                .iter()
                .position(|c| c == &source_cat_name)
                .map(|i| i as u16)
                .unwrap_or(0);
            for ft in first_set_of_category(&source_cat_name, reader, context) {
                if crosscat_lex_compat_gate
                    && ft.is_var_contribution
                    && source_ident_first_is_var_only(&source_cat_name, reader, context)
                    && result_has_home_var_reading(category_name, reader, context)
                {
                    continue;
                }
                insert_unified_descriptor(
                    &mut unified_buckets,
                    &mut unified_order,
                    ft.pattern.clone(),
                    ft.extra_guard.clone(),
                    UnifiedDescriptor::CrossCatProjection { rule_idx, source_src_idx },
                );
            }
        }
    }
    (unified_buckets, unified_order)
}
