//! Canonical, fallible ordering of complete private semantic replies.
//!
//! Refines SemanticReceiptOrder, SemanticChunkComparison, SemanticResultMerge
//! and SemanticResultPermutation. The two-index-buffer merge and inverse
//! permutation reuse the design in vinary-math-ir/src/canonical.rs. No Par
//! ordering, receipt encoding, proof deduplication or candidate pruning occurs.

use super::receipt::{effect_tag, opcode_tag, premise_tag};
use super::SemanticWireError;
use crate::semantic_service::SemanticServiceResult;
use mettail_dovetail_runtime::{
    SemanticNormalizationHopReceiptV1, SemanticNormalizationStepReceiptV1, SemanticPremiseReceipt,
    SemanticResourceReceipt, SemanticTransitionReceipt,
};
use mettail_rholang_codegen::{DynamicReflectionError, ReflectedCodecBudget};
use std::cmp::Ordering;

type Result<T> = std::result::Result<T, SemanticWireError>;
const ACCOUNTING_CHUNK_BYTES: usize = 64 * 1024;

// Evaluate only as far as the first unequal field, retaining every error.
macro_rules! fields {
    ($($comparison:expr),+ $(,)?) => {{
        $(let order = $comparison?;
        if order != Ordering::Equal { return Ok(order); })+
        Ok(Ordering::Equal)
    }};
}

struct Comparator<'a, 'b, C> {
    budget: &'a mut ReflectedCodecBudget<'b, C>,
}

impl<C: FnMut() -> bool> Comparator<'_, '_, C> {
    fn scalar<T: Ord>(&mut self, a: T, b: T) -> Result<Ordering> {
        self.budget.charge(1, 0)?;
        Ok(a.cmp(&b))
    }

    fn bytes(&mut self, a: &[u8], b: &[u8]) -> Result<Ordering> {
        self.budget.charge(1, 0)?;
        let common = a.len().min(b.len());
        let mut start = 0;
        while start < common {
            let end = start.saturating_add(ACCOUNTING_CHUNK_BYTES).min(common);
            // One logical visit to each byte of the compared pair, prepaid.
            self.budget.charge(2 * (end - start), 0)?;
            let order = a[start..end].cmp(&b[start..end]);
            if order != Ordering::Equal {
                return Ok(order);
            }
            start = end;
        }
        Ok(a.len().cmp(&b.len()))
    }

    fn roster<T>(
        &mut self,
        a: &[T],
        b: &[T],
        mut compare: impl FnMut(&mut Self, &T, &T) -> Result<Ordering>,
    ) -> Result<Ordering> {
        self.budget.charge(1, 0)?;
        for (a, b) in a.iter().zip(b) {
            let order = compare(self, a, b)?;
            if order != Ordering::Equal {
                return Ok(order);
            }
        }
        Ok(a.len().cmp(&b.len()))
    }

    fn premise(
        &mut self,
        a: &SemanticPremiseReceipt,
        b: &SemanticPremiseReceipt,
    ) -> Result<Ordering> {
        let tag_order = self.scalar(premise_tag(a), premise_tag(b))?;
        if tag_order != Ordering::Equal {
            return Ok(tag_order);
        }
        use SemanticPremiseReceipt::*;
        match (a, b) {
            (Freshness { rule: ar, premise: ap }, Freshness { rule: br, premise: bp }) => {
                fields!(self.scalar(ar.0, br.0), self.scalar(ap, bp))
            },
            (
                Transition { rule: ar, premise: ap, child_rule: ac },
                Transition { rule: br, premise: bp, child_rule: bc },
            ) => fields!(self.scalar(ar.0, br.0), self.scalar(ap, bp), self.scalar(ac.0, bc.0)),
            (
                Judgment {
                    rule: ar,
                    premise: ap,
                    judgment: aj,
                    proofs: an,
                    proof_steps: ast,
                },
                Judgment {
                    rule: br,
                    premise: bp,
                    judgment: bj,
                    proofs: bn,
                    proof_steps: bst,
                },
            ) => fields!(
                self.scalar(ar.0, br.0),
                self.scalar(ap, bp),
                self.scalar(aj.0, bj.0),
                self.scalar(an, bn),
                self.scalar(ast, bst)
            ),
            (
                ForAll { rule: ar, premise: ap, elements: ae },
                ForAll { rule: br, premise: bp, elements: be },
            ) => fields!(self.scalar(ar.0, br.0), self.scalar(ap, bp), self.scalar(ae, be)),
            (
                Intrinsic { rule: ar, premise: ap, receipt: ai },
                Intrinsic { rule: br, premise: bp, receipt: bi },
            ) => fields!(
                self.scalar(ar.0, br.0),
                self.scalar(ap, bp),
                self.scalar(opcode_tag(ai.opcode), opcode_tag(bi.opcode)),
                self.roster(&ai.inputs, &bi.inputs, |c, a, b| c.bytes(a, b)),
                self.roster(&ai.outputs, &bi.outputs, |c, a, b| c.bytes(a, b)),
                self.scalar(ai.work, bi.work)
            ),
            (
                Guard {
                    rule: ar,
                    premise: ap,
                    guard_commitment: ag,
                    evidence_commitment: ae,
                },
                Guard {
                    rule: br,
                    premise: bp,
                    guard_commitment: bg,
                    evidence_commitment: be,
                },
            ) => fields!(
                self.scalar(ar.0, br.0),
                self.scalar(ap, bp),
                self.bytes(ag, bg),
                self.bytes(ae, be)
            ),
            // Tags are exhaustive and injective. Fail closed if their shared
            // codec mapping is ever incorrectly changed, rather than equating evidence.
            _ => Err(SemanticWireError::Shape("noninjective premise tags")),
        }
    }

    fn resource(
        &mut self,
        a: &SemanticResourceReceipt,
        b: &SemanticResourceReceipt,
    ) -> Result<Ordering> {
        use SemanticResourceReceipt::*;
        self.budget.charge(1, 0)?;
        match (a, b) {
            (NoSemanticGrade, NoSemanticGrade) => Ok(Ordering::Equal),
            (NoSemanticGrade, Checked { .. }) => Ok(Ordering::Less),
            (Checked { .. }, NoSemanticGrade) => Ok(Ordering::Greater),
            (
                Checked {
                    grade_sort: asort,
                    grade: ag,
                    cost_image_fingerprint: ai,
                },
                Checked {
                    grade_sort: bsort,
                    grade: bg,
                    cost_image_fingerprint: bi,
                },
            ) => fields!(self.scalar(asort.0, bsort.0), self.bytes(ag, bg), self.bytes(ai, bi)),
        }
    }

    fn step(
        &mut self,
        a: &SemanticNormalizationStepReceiptV1,
        b: &SemanticNormalizationStepReceiptV1,
    ) -> Result<Ordering> {
        fields!(
            self.scalar(a.rule.0, b.rule.0),
            self.bytes(&a.before, &b.before),
            self.bytes(&a.after, &b.after),
            self.roster(&a.premises, &b.premises, Self::premise)
        )
    }

    fn hop(
        &mut self,
        a: &SemanticNormalizationHopReceiptV1,
        b: &SemanticNormalizationHopReceiptV1,
    ) -> Result<Ordering> {
        fields!(
            self.bytes(&a.before, &b.before),
            self.bytes(&a.after, &b.after),
            self.roster(&a.exhaustive_proofs, &b.exhaustive_proofs, Self::step),
            self.scalar(a.charged_work, b.charged_work)
        )
    }

    fn receipt(
        &mut self,
        a: &SemanticTransitionReceipt,
        b: &SemanticTransitionReceipt,
    ) -> Result<Ordering> {
        fields!(
            self.bytes(&a.language_fingerprint, &b.language_fingerprint),
            self.bytes(&a.theory_fingerprint, &b.theory_fingerprint),
            self.bytes(&a.image_fingerprint, &b.image_fingerprint),
            self.scalar(a.action.0, b.action.0),
            self.scalar(a.rule.0, b.rule.0),
            self.bytes(&a.input, &b.input),
            self.bytes(&a.output, &b.output),
            self.scalar(a.effect.0, b.effect.0),
            self.scalar(effect_tag(a.effect_class), effect_tag(b.effect_class)),
            self.resource(&a.resource, &b.resource),
            self.roster(&a.premises, &b.premises, Self::premise),
            self.roster(&a.normalization_hops, &b.normalization_hops, Self::hop),
            self.scalar(a.work, b.work),
        )
    }

    fn result_key(
        &mut self,
        a: &SemanticTransitionReceipt,
        b: &SemanticTransitionReceipt,
    ) -> Result<Ordering> {
        fields!(self.bytes(&a.output, &b.output), self.receipt(a, b))
    }
}

fn stable_order<C: FnMut() -> bool>(
    values: &[SemanticServiceResult],
    budget: &mut ReflectedCodecBudget<'_, C>,
) -> Result<(Vec<usize>, Vec<usize>)> {
    let count = values.len();
    let bytes = count
        .checked_mul(16)
        .and_then(|n| n.checked_add(32))
        .ok_or(DynamicReflectionError::PayloadByteLimit)?;
    // Two logical descriptors and two eight-byte index slots per record;
    // independent of architecture and allocator layout. No third scratch vector.
    budget.charge(count, bytes)?;
    let mut current = Vec::new();
    current
        .try_reserve_exact(count)
        .map_err(|_| DynamicReflectionError::AllocationFailed)?;
    current.extend(0..count);
    let mut scratch = Vec::new();
    scratch
        .try_reserve_exact(count)
        .map_err(|_| DynamicReflectionError::AllocationFailed)?;
    let mut compare = Comparator { budget };
    let mut width = 1;
    while width < count {
        compare.budget.charge(count, 0)?;
        scratch.clear();
        let mut start: usize = 0;
        while start < count {
            let middle = start.saturating_add(width).min(count);
            let end = middle.saturating_add(width).min(count);
            let mut left = start;
            let mut right = middle;
            while left < middle && right < end {
                let order = compare
                    .result_key(&values[current[left]].receipt, &values[current[right]].receipt)?;
                if order == Ordering::Greater {
                    scratch.push(current[right]);
                    right += 1;
                } else {
                    scratch.push(current[left]);
                    left += 1;
                }
            }
            scratch.extend_from_slice(&current[left..middle]);
            scratch.extend_from_slice(&current[right..end]);
            start = end;
        }
        std::mem::swap(&mut current, &mut scratch);
        width = width.checked_mul(2).unwrap_or(count);
    }
    Ok((current, scratch))
}

fn reorder<T, C: FnMut() -> bool>(
    values: &mut [T],
    order: &[usize],
    inverse: &mut Vec<usize>,
    budget: &mut ReflectedCodecBudget<'_, C>,
) -> Result<()> {
    let count = values.len();
    if order.len() != count || inverse.capacity() < count {
        return Err(SemanticWireError::Shape("invalid semantic permutation extent"));
    }
    budget.charge(count, 0)?;
    inverse.clear();
    inverse.resize(count, count);
    budget.charge(count, 0)?;
    for (destination, &source) in order.iter().enumerate() {
        if source >= count || inverse[source] != count {
            return Err(SemanticWireError::Shape("invalid semantic permutation"));
        }
        inverse[source] = destination;
    }
    // At most n swaps and n cursor advances: at most 2n loop tests plus
    // two logical whole-record/index swaps per iteration. Prepay before any
    // movement, then check cancellation per cursor without resetting balances.
    let movement = count
        .checked_mul(4)
        .ok_or(DynamicReflectionError::WorkLimit)?;
    budget.charge(movement, 0)?;
    for source in 0..count {
        budget.charge(0, 0)?;
        while inverse[source] != source {
            budget.charge(0, 0)?;
            let destination = inverse[source];
            values.swap(source, destination);
            inverse.swap(source, destination);
        }
    }
    budget.charge(0, 0)?;
    Ok(())
}

/// Sort an owned/private reply before its final publication guard. Failure
/// during comparison leaves its order unchanged; cancellation during movement
/// may leave a permutation, never a missing or unpaired record. The caller must
/// discard the entire private reply on any error, not publish a partial prefix.
pub(crate) fn sort_results<C: FnMut() -> bool>(
    values: &mut [SemanticServiceResult],
    budget: &mut ReflectedCodecBudget<'_, C>,
) -> Result<()> {
    budget.charge(0, 0)?;
    if values.len() < 2 {
        return Ok(());
    }
    let (order, mut inverse) = stable_order(values, budget)?;
    reorder(values, &order, &mut inverse, budget)
}

#[cfg(test)]
mod tests;
