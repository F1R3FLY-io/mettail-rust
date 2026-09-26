//! Original macro absorption-table query, shared without a second eligibility
//! policy. `IterAbsorptionObservation.v` covers the lazy lookup and first-match
//! receipt boundary. Terminal strings remain borrowed from the original table.

use crate::binding_power::{BindingPowerTable, InfixOperator};
use std::collections::HashMap;

/// The original `cat_lit_rule_idx` filter-map. Category spelling is observed
/// before native presence; missing native types skip label generation entirely.
pub fn try_literal_rule_indices<'a, T: 'a, N, E>(
    categories: &'a [T],
    label_index: &HashMap<(String, String), (u16, u16)>,
    mut category_name: impl FnMut(&'a T) -> String,
    mut native_type: impl FnMut(&'a T) -> Option<N>,
    mut literal_label: impl FnMut(N) -> Result<String, E>,
) -> Result<HashMap<String, u16>, E> {
    categories
        .iter()
        .filter_map(|td| {
            let cat_name = category_name(td);
            let nt = native_type(td)?;
            let lit_label = match literal_label(nt) {
                Ok(label) => label,
                Err(error) => return Some(Err(error)),
            };
            let (_, ri) = label_index.get(&(cat_name.clone(), lit_label))?;
            Some(Ok((cat_name, *ri)))
        })
        .collect()
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BorrowedIterAbsorbSpec<'a> {
    pub left_bp: u8,
    pub right_bp: u8,
    pub assoc_right: bool,
    pub is_mixfix: bool,
    pub op_cat_src_idx: u16,
    pub op_rule_idx: u16,
    pub atom_cat_src_idx: u16,
    pub atom_lit_rule_idx: u16,
    pub trigger: &'a str,
    pub sep: &'a str,
}

pub struct IterAbsorptionQuery<'a> {
    /// Original diagnostic order, including each eligible operator's first
    /// terminal clash. Diagnostics do not suppress the separate arm scan.
    pub disjointness: Vec<(&'a InfixOperator, &'a InfixOperator)>,
    /// Source-ordered generated match arms, not a map that changes precedence.
    pub arms: Vec<BorrowedIterAbsorbSpec<'a>>,
}

impl<'a> IterAbsorptionQuery<'a> {
    pub fn lookup(&self, rs: u16, ri: u16) -> Option<BorrowedIterAbsorbSpec<'a>> {
        self.arms
            .iter()
            .find(|arm| (arm.op_cat_src_idx, arm.op_rule_idx) == (rs, ri))
            .copied()
    }
}

/// Literal relocation of `emit_iter_eligible_fn`'s query. The original emitter
/// does not call canonical-op ranking; category/value-home inputs were unused.
pub fn query<'a>(
    bp_table: &'a BindingPowerTable,
    category: &str,
    label_index: &HashMap<(String, String), (u16, u16)>,
    cat_lit_rule_idx: &HashMap<String, u16>,
) -> IterAbsorptionQuery<'a> {
    let cat_ops: Vec<&InfixOperator> = bp_table
        .operators
        .iter()
        .filter(|op| op.category == category)
        .collect();
    let disjointness = cat_ops
        .iter()
        .enumerate()
        .filter(|(_, op)| op.is_iterative_candidate())
        .filter_map(|(i, op)| {
            let clash = cat_ops
                .iter()
                .enumerate()
                .find(|(j, other)| *j != i && other.terminal == op.terminal)
                .map(|(_, other)| other)?;
            Some((*op, *clash))
        })
        .collect();
    let arms = cat_ops
        .iter()
        .filter(|op| op.is_iterative_candidate())
        .filter_map(|op| {
            let conflict = cat_ops.iter().any(|other| {
                !std::ptr::eq(*other as *const _, *op as *const _)
                    && other.terminal == op.terminal
                    && other.left_bp == op.left_bp
            });
            if conflict {
                return None;
            }
            let (rs, ri) = *label_index.get(&(op.result_category.clone(), op.label.clone()))?;
            let l = op.left_bp;
            let r = op.right_bp;
            let assoc_right = op.left_bp > op.right_bp;
            let is_mixfix = op.is_mixfix;
            let atom_cat_src_idx = rs;
            let atom_lit_rule_idx = *cat_lit_rule_idx.get(&op.result_category)?;
            let (trigger, sep): (&str, &str) = if op.is_mixfix {
                let sep = op
                    .mixfix_parts
                    .first()
                    .and_then(|p| p.following_terminals.first().map(String::as_str))
                    .unwrap_or_default();
                (op.terminal.as_str(), sep)
            } else {
                ("", "")
            };
            Some(BorrowedIterAbsorbSpec {
                left_bp: l,
                right_bp: r,
                assoc_right,
                is_mixfix,
                op_cat_src_idx: rs,
                op_rule_idx: ri,
                atom_cat_src_idx,
                atom_lit_rule_idx,
                trigger,
                sep,
            })
        })
        .collect();
    IterAbsorptionQuery { disjointness, arms }
}

#[cfg(test)]
mod tests;
