//! Original bounded grouping-source descriptor derivation.
//!
//! The two original hop loops and their scheduling remain unchanged. This is
//! not a transitive closure: direct sources are followed by one infix hop from
//! each projection source only when there are fewer than four such sources.
//! Classifier callbacks retain the existing infix normalization and atomic
//! classification, including their original lazy call sites.
//!
//! `GroupingSourceDescriptorProjection.v` verifies finite accessor substitution,
//! callback order, sorted-set behavior, faults, and the original u16 casts.
//! Runtime checked-width admission and allocation remain caller obligations.

use crate::binding_power::InfixRuleInfo;
use std::collections::BTreeSet;

/// Extend the set with original cross-category infix operand sources.
/// Category filtering precedes classification; name lookup uses first position.
pub fn grouping_source_infix_hop<R>(
    categories: &[String],
    rules: &[R],
    result_idx: usize,
    out: &mut BTreeSet<u16>,
    rule_category: &mut impl FnMut(&R) -> String,
    classify_infix: &mut impl FnMut(&R) -> Option<InfixRuleInfo>,
) {
    let result = try_grouping_source_infix_hop(
        categories,
        rules,
        result_idx,
        out,
        &mut |rule| Ok::<_, std::convert::Infallible>(rule_category(rule)),
        &mut |rule| Ok(classify_infix(rule)),
    );
    match result {
        Ok(()) => (),
        Err(error) => match error {},
    }
}

/// Same source loop with first-error propagation at the original callback sites.
pub fn try_grouping_source_infix_hop<R, E>(
    categories: &[String],
    rules: &[R],
    result_idx: usize,
    out: &mut BTreeSet<u16>,
    rule_category: &mut impl FnMut(&R) -> Result<String, E>,
    classify_infix: &mut impl FnMut(&R) -> Result<Option<InfixRuleInfo>, E>,
) -> Result<(), E> {
    let result_cat_name = &categories[result_idx];
    for rule in rules {
        if rule_category(rule)? != *result_cat_name {
            continue;
        }
        if let Some(info) = classify_infix(rule)? {
            if info.is_cross_category && info.category != info.result_category {
                if let Some(source_idx) = categories.iter().position(|c| c == &info.category) {
                    if source_idx != result_idx {
                        out.insert(source_idx as u16);
                    }
                }
            }
        }
    }
    Ok(())
}

/// Extend the set with projection sources in the original category row.
/// A missing row is a no-op; no category equality filter is added to that row.
pub fn grouping_source_projection_hop<R>(
    per_cat: &[Vec<R>],
    categories: &[String],
    result_idx: usize,
    out: &mut BTreeSet<u16>,
    projection_source: &mut impl FnMut(&R) -> Option<String>,
) {
    let result =
        try_grouping_source_projection_hop(per_cat, categories, result_idx, out, &mut |rule| {
            Ok::<_, std::convert::Infallible>(projection_source(rule))
        });
    match result {
        Ok(()) => (),
        Err(error) => match error {},
    }
}

/// A callback error is distinct from an absent projection source.
pub fn try_grouping_source_projection_hop<R, E>(
    per_cat: &[Vec<R>],
    categories: &[String],
    result_idx: usize,
    out: &mut BTreeSet<u16>,
    projection_source: &mut impl FnMut(&R) -> Result<Option<String>, E>,
) -> Result<(), E> {
    if let Some(rules) = per_cat.get(result_idx) {
        for rule in rules {
            if let Some(source_cat_name) = projection_source(rule)? {
                if let Some(source_idx) = categories.iter().position(|c| c == &source_cat_name) {
                    if source_idx != result_idx {
                        out.insert(source_idx as u16);
                    }
                }
            }
        }
    }
    Ok(())
}

/// Derive the exact original ordered grouping targets, with the result first.
/// The projection callback is deliberately run twice. `visited` retains the
/// original write-only updates; it does not suppress a repeated result in the
/// sorted tail. Narrowing to u16 occurs before the second-hop category lookup.
pub fn grouping_source_categories_for_result<R>(
    categories: &[String],
    rules: &[R],
    per_cat: &[Vec<R>],
    result_idx: usize,
    mut rule_category: impl FnMut(&R) -> String,
    mut classify_infix: impl FnMut(&R) -> Option<InfixRuleInfo>,
    mut projection_source: impl FnMut(&R) -> Option<String>,
) -> Vec<u16> {
    let result = try_grouping_source_categories_for_result(
        categories,
        rules,
        per_cat,
        result_idx,
        |rule| Ok::<_, std::convert::Infallible>(rule_category(rule)),
        |rule| Ok(classify_infix(rule)),
        |rule| Ok(projection_source(rule)),
    );
    match result {
        Ok(sources) => sources,
        Err(error) => match error {},
    }
}

/// Checked callback interface to the original bounded grouping schedule.
/// Input coordinate admission is the caller's responsibility. No partial
/// source roster is returned if any original callback fails.
pub fn try_grouping_source_categories_for_result<R, E>(
    categories: &[String],
    rules: &[R],
    per_cat: &[Vec<R>],
    result_idx: usize,
    mut rule_category: impl FnMut(&R) -> Result<String, E>,
    mut classify_infix: impl FnMut(&R) -> Result<Option<InfixRuleInfo>, E>,
    mut projection_source: impl FnMut(&R) -> Result<Option<String>, E>,
) -> Result<Vec<u16>, E> {
    let result_src_idx = result_idx as u16;
    let mut closure: BTreeSet<u16> = BTreeSet::new();
    let mut visited: BTreeSet<u16> = BTreeSet::new();
    visited.insert(result_src_idx);
    let mut seed: BTreeSet<u16> = BTreeSet::new();
    try_grouping_source_infix_hop(
        categories,
        rules,
        result_idx,
        &mut seed,
        &mut rule_category,
        &mut classify_infix,
    )?;
    try_grouping_source_projection_hop(
        per_cat,
        categories,
        result_idx,
        &mut seed,
        &mut projection_source,
    )?;
    const HUB_PROJECTION_THRESHOLD: usize = 4;
    let projection_sources: Vec<usize> = {
        let mut pv: BTreeSet<u16> = BTreeSet::new();
        try_grouping_source_projection_hop(
            per_cat,
            categories,
            result_idx,
            &mut pv,
            &mut projection_source,
        )?;
        pv.into_iter().map(|c| c as usize).collect()
    };
    for src in seed {
        closure.insert(src);
        visited.insert(src);
    }
    if projection_sources.len() < HUB_PROJECTION_THRESHOLD {
        for p in projection_sources {
            let mut hop: BTreeSet<u16> = BTreeSet::new();
            try_grouping_source_infix_hop(
                categories,
                rules,
                p,
                &mut hop,
                &mut rule_category,
                &mut classify_infix,
            )?;
            for src in hop {
                closure.insert(src);
                visited.insert(src);
            }
        }
    }
    let mut sources = Vec::with_capacity(closure.len() + 1);
    sources.push(result_src_idx);
    sources.extend(closure);
    Ok(sources)
}
