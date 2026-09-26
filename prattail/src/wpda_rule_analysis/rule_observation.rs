//! Original finite rule observations used by generated and owned engines.
//!
//! These bodies are relocated from `wpda_codegen/semantic_actions.rs` and
//! `collection.rs`; the existing binder reader supplies the same shallow fields.
//! In particular, a missing syntax sequence, any operation, or any non-simple
//! parameter retains the original zero minimum-span observation.

use super::binder::optional::{BinderSyntaxObservation, BinderSyntaxReader};
use super::binder::rule::{BinderRuleReader, BinderTypeObservation};
use super::binder::term_param::TermParamObservation;
use std::collections::{BTreeMap, BTreeSet};

/// Original single-hop table census, including builtin exclusion and collecting
/// every unresolved-source refusal without publishing a partial table.
pub fn single_hop_coercions<'source, R, E>(
    reader: &R,
    per_cat: &[Vec<(u16, R::Rule)>],
    mut resolve: impl FnMut(&str, R::Rule) -> Result<u16, E>,
) -> (BTreeMap<(u16, u16), Vec<u16>>, Vec<E>)
where
    R: BinderRuleReader<'source>,
    <R as BinderSyntaxReader<'source>>::Name: std::fmt::Display,
{
    let mut table: BTreeMap<(u16, u16), Vec<u16>> = BTreeMap::new();
    let mut refusals = Vec::new();
    for (cat_i, rules) in per_cat.iter().enumerate() {
        let to_cat = cat_i as u16;
        for (rule_idx, rule) in rules {
            let Some(tc) = reader.term_context(*rule) else {
                continue;
            };
            if reader.params_len(tc) != 1 {
                continue;
            }
            let TermParamObservation::Simple { name: param_name, ty } = reader.param(
                reader
                    .param_at(tc, 0)
                    .expect("one-element parameter context"),
            ) else {
                continue;
            };
            let BinderTypeObservation::Base(source_ident) = reader.ty(ty) else {
                continue;
            };
            let source_cat_name = source_ident.to_string();
            if source_cat_name == reader.category(*rule).to_string() {
                continue;
            }
            let Some(sp) = reader.syntax_pattern(*rule) else {
                continue;
            };
            let is_pass2a = reader.sequence_len(sp) == 1
                && matches!(
                    reader.at(sp, 0), Some(BinderSyntaxObservation::Param(syn_name))
                        if reader.names_equal(syn_name, param_name)
                );
            if !is_pass2a {
                continue;
            }
            if mettail_ast::grammar::NonTerminalKind::classify(&source_cat_name).is_builtin() {
                continue;
            }
            let from_cat = match resolve(&source_cat_name, *rule) {
                Ok(idx) => idx,
                Err(unresolved) => {
                    refusals.push(unresolved);
                    continue;
                },
            };
            table.entry((from_cat, to_cat)).or_default().push(*rule_idx);
        }
    }
    (table, refusals)
}

/// Original transparent-projection census from `kind_dispatch.rs`.
pub fn transparent_projection_rules<'source, R>(
    reader: &R,
    per_cat: &[Vec<R::Rule>],
    categories: &[String],
) -> Vec<(u16, u16, u16)>
where
    R: BinderRuleReader<'source>,
    <R as BinderSyntaxReader<'source>>::Name: std::fmt::Display,
{
    let mut out = Vec::new();
    for (to_cat_idx, rules) in per_cat.iter().enumerate() {
        let to_cat = to_cat_idx as u16;
        for (rule_idx, rule) in rules.iter().enumerate() {
            let Some(term_context) = reader.term_context(*rule) else {
                continue;
            };
            if reader.params_len(term_context) != 1 {
                continue;
            }
            let TermParamObservation::Simple { name: param_name, ty } = reader.param(
                reader
                    .param_at(term_context, 0)
                    .expect("one-element parameter context"),
            ) else {
                continue;
            };
            let BinderTypeObservation::Base(source_ident) = reader.ty(ty) else {
                continue;
            };
            let source_cat_name = source_ident.to_string();
            if source_cat_name == reader.category(*rule).to_string() {
                continue;
            }
            let Some(syntax_pattern) = reader.syntax_pattern(*rule) else {
                continue;
            };
            let is_transparent = reader.sequence_len(syntax_pattern) == 1
                && matches!(reader.at(syntax_pattern, 0),
                    Some(BinderSyntaxObservation::Param(syn_name))
                        if reader.names_equal(syn_name, param_name));
            if !is_transparent {
                continue;
            }
            let Some(from_cat) = categories
                .iter()
                .position(|category| category == &source_cat_name)
                .map(|idx| idx as u16)
            else {
                continue;
            };
            out.push((from_cat, to_cat, rule_idx as u16));
        }
    }
    out
}

/// Original finite closure body from `emit_cat_can_reach`. The caller supplies
/// exactly the original union of cross-category operator and projection edges.
pub fn non_reflexive_category_reachability(direct: BTreeSet<(u16, u16)>) -> Vec<(u16, u16)> {
    let mut reach: BTreeSet<(u16, u16)> = direct.clone();
    loop {
        let mut added = false;
        let snapshot: Vec<(u16, u16)> = reach.iter().copied().collect();
        for &(a, b) in &snapshot {
            for &(c, d) in &snapshot {
                if b == c && a != d && reach.insert((a, d)) {
                    added = true;
                }
            }
        }
        if !added {
            break;
        }
    }
    debug_assert!(
        direct.iter().all(|edge| reach.contains(edge)),
        "cat_can_reach RTC must contain every direct cross-cat edge (conservative over-approximation)"
    );
    reach.into_iter().filter(|(a, b)| a != b).collect()
}

/// The original first-syntax-node literal observation, including absence.
pub fn leading_literal<'source, R: BinderRuleReader<'source>>(
    reader: &R,
    rule: R::Rule,
) -> Option<&'source str> {
    let syntax = reader.syntax_pattern(rule)?;
    match reader.at(syntax, 0) {
        Some(BinderSyntaxObservation::Literal(text)) => Some(text),
        _ => None,
    }
}

/// Count literals after the first parameter, with the original exclusions.
pub fn min_terminal_span<'source, R: BinderRuleReader<'source>>(reader: &R, rule: R::Rule) -> u32 {
    let Some(sp) = reader.syntax_pattern(rule) else {
        return 0;
    };
    if (0..reader.sequence_len(sp))
        .any(|index| matches!(reader.at(sp, index), Some(BinderSyntaxObservation::Op(_))))
    {
        return 0;
    }
    let all_simple_params = reader
        .term_context(rule)
        .map(|tc| {
            (0..reader.params_len(tc)).all(|index| {
                matches!(
                    reader.param(
                        reader
                            .param_at(tc, index)
                            .expect("parameter index is in bounds")
                    ),
                    TermParamObservation::Simple { .. }
                )
            })
        })
        .unwrap_or(true);
    if !all_simple_params {
        return 0;
    }
    let mut seen_param = false;
    let mut post_param_literals: u32 = 0;
    for index in 0..reader.sequence_len(sp) {
        match reader.at(sp, index) {
            Some(BinderSyntaxObservation::Param(_)) => seen_param = true,
            Some(BinderSyntaxObservation::Literal(_)) if seen_param => post_param_literals += 1,
            _ => {},
        }
    }
    post_param_literals
}
