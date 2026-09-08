//! The exact finite-depth schema checked by SemanticReceiptWire.v.
//!
//! Tuple materialization reserves one logical value descriptor and eight bytes
//! per child slot before allocation. Owned byte vectors move into the wire;
//! copying a fingerprint or decoding a borrowed byte vector separately charges
//! its bytes. Every variable roster is iterative. Receipt work fields are data,
//! never recharged as execution. This is transport, not proof verification.

use super::{decode_u32, decode_u64, encode_u64, SemanticWireError, VALUE_DESCRIPTOR_BYTES};
use crate::language_install::{exact_expr, exact_list, wire_list};
use mettail_dovetail_runtime::{
    SemanticIntrinsicOpcodeV1, SemanticIntrinsicReceiptV1, SemanticNormalizationHopReceiptV1,
    SemanticNormalizationStepReceiptV1, SemanticPremiseReceipt, SemanticResourceReceipt,
    SemanticTransitionReceipt,
};
use mettail_grammar_core::{
    SemanticEffectClassV1, TheoryActionId, TheoryEffectId, TheoryJudgmentId, TheoryRuleProgramId,
    TheorySortId,
};
use mettail_rholang_codegen::{DynamicReflectionError, ReflectedCodecBudget};
use models::rhoapi::{expr::ExprInstance, Par};
use models::rust::utils::new_gbytearray_par;

type Result<T> = std::result::Result<T, SemanticWireError>;

fn slots<T, C: FnMut() -> bool>(
    length: usize,
    visit: usize,
    budget: &mut ReflectedCodecBudget<'_, C>,
) -> Result<Vec<T>> {
    let bytes = length
        .checked_mul(8)
        .and_then(|n| n.checked_add(VALUE_DESCRIPTOR_BYTES))
        .ok_or(DynamicReflectionError::PayloadByteLimit)?;
    budget.charge(visit, bytes)?;
    let mut out = Vec::new();
    out.try_reserve_exact(length)
        .map_err(|_| DynamicReflectionError::AllocationFailed)?;
    Ok(out)
}

pub(super) struct Encoder<'a, 'b, C> {
    pub(super) budget: &'a mut ReflectedCodecBudget<'b, C>,
}

impl<C: FnMut() -> bool> Encoder<'_, '_, C> {
    pub(super) fn uint(&mut self, n: impl Into<u64>) -> Result<Par> {
        encode_u64(n.into(), self.budget)
    }

    pub(super) fn tuple<const N: usize>(
        &mut self,
        fields: impl FnOnce(&mut Self) -> Result<[Par; N]>,
    ) -> Result<Par> {
        let mut out = slots(N, 1, self.budget)?;
        out.extend(fields(self)?);
        Ok(wire_list(out))
    }

    fn roster<T>(
        &mut self,
        items: Vec<T>,
        mut encode: impl FnMut(&mut Self, T) -> Result<Par>,
    ) -> Result<Par> {
        let mut out = slots(items.len(), 1, self.budget)?;
        for item in items {
            out.push(encode(self, item)?);
        }
        Ok(wire_list(out))
    }

    fn bytes(&mut self, bytes: Vec<u8>) -> Result<Par> {
        self.budget.charge(1, VALUE_DESCRIPTOR_BYTES)?;
        Ok(new_gbytearray_par(bytes, Vec::new(), false))
    }

    fn fingerprint(&mut self, bytes: [u8; 32]) -> Result<Par> {
        self.budget.charge(33, VALUE_DESCRIPTOR_BYTES + 32)?;
        let mut out = Vec::new();
        out.try_reserve_exact(32)
            .map_err(|_| DynamicReflectionError::AllocationFailed)?;
        out.extend_from_slice(&bytes);
        Ok(new_gbytearray_par(out, Vec::new(), false))
    }

    fn premise(&mut self, p: SemanticPremiseReceipt) -> Result<Par> {
        let tag = premise_tag(&p);
        match p {
            SemanticPremiseReceipt::Freshness { rule, premise } => {
                self.tuple(|e| Ok([e.uint(tag)?, e.uint(rule.0)?, e.uint(premise)?]))
            },
            SemanticPremiseReceipt::Transition { rule, premise, child_rule } => self.tuple(|e| {
                Ok([e.uint(tag)?, e.uint(rule.0)?, e.uint(premise)?, e.uint(child_rule.0)?])
            }),
            SemanticPremiseReceipt::Judgment {
                rule,
                premise,
                judgment,
                proofs,
                proof_steps,
            } => self.tuple(|e| {
                Ok([
                    e.uint(tag)?,
                    e.uint(rule.0)?,
                    e.uint(premise)?,
                    e.uint(judgment.0)?,
                    e.uint(proofs)?,
                    e.uint(proof_steps)?,
                ])
            }),
            SemanticPremiseReceipt::ForAll { rule, premise, elements } => self.tuple(|e| {
                Ok([e.uint(tag)?, e.uint(rule.0)?, e.uint(premise)?, e.uint(elements)?])
            }),
            SemanticPremiseReceipt::Intrinsic { rule, premise, receipt } => self.tuple(|e| {
                Ok([
                    e.uint(tag)?,
                    e.uint(rule.0)?,
                    e.uint(premise)?,
                    e.uint(opcode_tag(receipt.opcode))?,
                    e.roster(receipt.inputs, Self::bytes)?,
                    e.roster(receipt.outputs, Self::bytes)?,
                    e.uint(receipt.work)?,
                ])
            }),
            SemanticPremiseReceipt::Guard {
                rule,
                premise,
                guard_commitment,
                evidence_commitment,
            } => self.tuple(|e| {
                Ok([
                    e.uint(tag)?,
                    e.uint(rule.0)?,
                    e.uint(premise)?,
                    e.fingerprint(guard_commitment)?,
                    e.fingerprint(evidence_commitment)?,
                ])
            }),
        }
    }

    fn step(&mut self, s: SemanticNormalizationStepReceiptV1) -> Result<Par> {
        self.tuple(|e| {
            Ok([
                e.uint(s.rule.0)?,
                e.bytes(s.before)?,
                e.bytes(s.after)?,
                e.roster(s.premises, Self::premise)?,
            ])
        })
    }

    fn hop(&mut self, h: SemanticNormalizationHopReceiptV1) -> Result<Par> {
        self.tuple(|e| {
            Ok([
                e.bytes(h.before)?,
                e.bytes(h.after)?,
                e.roster(h.exhaustive_proofs, Self::step)?,
                e.uint(h.charged_work)?,
            ])
        })
    }

    fn resource(&mut self, r: SemanticResourceReceipt) -> Result<Par> {
        match r {
            SemanticResourceReceipt::NoSemanticGrade => self.tuple(|e| Ok([e.uint(0_u32)?])),
            SemanticResourceReceipt::Checked {
                grade_sort,
                grade,
                cost_image_fingerprint,
            } => self.tuple(|e| {
                Ok([
                    e.uint(1_u32)?,
                    e.uint(grade_sort.0)?,
                    e.bytes(grade)?,
                    e.fingerprint(cost_image_fingerprint)?,
                ])
            }),
        }
    }

    fn receipt(&mut self, r: SemanticTransitionReceipt) -> Result<Par> {
        self.tuple(|e| {
            Ok([
                e.fingerprint(r.language_fingerprint)?,
                e.fingerprint(r.theory_fingerprint)?,
                e.fingerprint(r.image_fingerprint)?,
                e.uint(r.action.0)?,
                e.uint(r.rule.0)?,
                e.bytes(r.input)?,
                e.bytes(r.output)?,
                e.uint(r.effect.0)?,
                e.uint(effect_tag(r.effect_class))?,
                e.resource(r.resource)?,
                e.roster(r.premises, Self::premise)?,
                e.roster(r.normalization_hops, Self::hop)?,
                e.uint(r.work)?,
            ])
        })
    }
}

pub(super) fn premise_tag(premise: &SemanticPremiseReceipt) -> u32 {
    match premise {
        SemanticPremiseReceipt::Freshness { .. } => 0,
        SemanticPremiseReceipt::Transition { .. } => 1,
        SemanticPremiseReceipt::Judgment { .. } => 2,
        SemanticPremiseReceipt::ForAll { .. } => 3,
        SemanticPremiseReceipt::Intrinsic { .. } => 4,
        SemanticPremiseReceipt::Guard { .. } => 5,
    }
}

pub(super) fn opcode_tag(opcode: SemanticIntrinsicOpcodeV1) -> u32 {
    match opcode {
        SemanticIntrinsicOpcodeV1::ExactTermEq => 0,
        SemanticIntrinsicOpcodeV1::Utf8AtEnd => 1,
        SemanticIntrinsicOpcodeV1::Utf8ScalarAt => 2,
        SemanticIntrinsicOpcodeV1::Utf8Slice => 3,
        SemanticIntrinsicOpcodeV1::CheckedNatAdd => 4,
        SemanticIntrinsicOpcodeV1::Utf8ConcatMany => 5,
    }
}

pub(super) fn effect_tag(effect: SemanticEffectClassV1) -> u32 {
    match effect {
        SemanticEffectClassV1::Pure => 0,
        SemanticEffectClassV1::Structural => 1,
        SemanticEffectClassV1::Behavioral => 2,
        SemanticEffectClassV1::Resource => 3,
        SemanticEffectClassV1::External => 4,
    }
}

pub(super) struct Decoder<'a, 'b, C> {
    pub(super) budget: &'a mut ReflectedCodecBudget<'b, C>,
}

impl<C: FnMut() -> bool> Decoder<'_, '_, C> {
    pub(super) fn uint(&mut self, value: &Par) -> Result<u64> {
        decode_u64(value, self.budget)
    }
    fn coordinate(&mut self, value: &Par) -> Result<u32> {
        decode_u32(value, self.budget)
    }

    fn literal(&mut self, value: &Par) -> Result<()> {
        self.budget.charge(1, 0)?;
        if !value.locally_free.is_empty() || value.connective_used {
            return Err(SemanticWireError::Shape("receipt has nonliteral metadata"));
        }
        Ok(())
    }

    pub(super) fn list<'v>(&mut self, value: &'v Par) -> Result<&'v [Par]> {
        self.literal(value)?;
        match exact_expr(value) {
            Some(ExprInstance::EListBody(list))
                if list.locally_free.is_empty() && !list.connective_used =>
            {
                exact_list(value).ok_or(SemanticWireError::Shape("expected an exact receipt list"))
            },
            _ => Err(SemanticWireError::Shape("expected a closed receipt list")),
        }
    }

    pub(super) fn tuple<'v, const N: usize>(&mut self, value: &'v Par) -> Result<&'v [Par; N]> {
        self.list(value)?
            .try_into()
            .map_err(|_| SemanticWireError::Shape("receipt tuple arity"))
    }

    fn roster<T>(
        &mut self,
        value: &Par,
        mut decode: impl FnMut(&mut Self, &Par) -> Result<T>,
    ) -> Result<Vec<T>> {
        let values = self.list(value)?;
        let mut out = slots(values.len(), 0, self.budget)?;
        for value in values {
            out.push(decode(self, value)?);
        }
        Ok(out)
    }

    fn borrowed_bytes<'v>(&mut self, value: &'v Par) -> Result<&'v [u8]> {
        self.literal(value)?;
        match exact_expr(value) {
            Some(ExprInstance::GByteArray(bytes)) => Ok(bytes),
            _ => Err(SemanticWireError::Shape("expected receipt bytes")),
        }
    }

    fn bytes(&mut self, value: &Par) -> Result<Vec<u8>> {
        let bytes = self.borrowed_bytes(value)?;
        let reservation = bytes
            .len()
            .checked_add(VALUE_DESCRIPTOR_BYTES)
            .ok_or(DynamicReflectionError::PayloadByteLimit)?;
        self.budget.charge(bytes.len(), reservation)?;
        let mut out = Vec::new();
        out.try_reserve_exact(bytes.len())
            .map_err(|_| DynamicReflectionError::AllocationFailed)?;
        out.extend_from_slice(bytes);
        Ok(out)
    }

    fn fingerprint(&mut self, value: &Par) -> Result<[u8; 32]> {
        let bytes = self.borrowed_bytes(value)?;
        let bytes: &[u8; 32] = bytes
            .try_into()
            .map_err(|_| SemanticWireError::Shape("expected 32-byte commitment"))?;
        self.budget.charge(32, 32)?;
        Ok(*bytes)
    }

    fn premise(&mut self, value: &Par) -> Result<SemanticPremiseReceipt> {
        let (tag, payload) = self
            .list(value)?
            .split_first()
            .ok_or(SemanticWireError::Shape("empty premise"))?;
        Ok(match (self.coordinate(tag)?, payload) {
            (0, [rule, premise]) => SemanticPremiseReceipt::Freshness {
                rule: TheoryRuleProgramId(self.coordinate(rule)?),
                premise: self.coordinate(premise)?,
            },
            (1, [rule, premise, child]) => SemanticPremiseReceipt::Transition {
                rule: TheoryRuleProgramId(self.coordinate(rule)?),
                premise: self.coordinate(premise)?,
                child_rule: TheoryRuleProgramId(self.coordinate(child)?),
            },
            (2, [rule, premise, judgment, proofs, steps]) => SemanticPremiseReceipt::Judgment {
                rule: TheoryRuleProgramId(self.coordinate(rule)?),
                premise: self.coordinate(premise)?,
                judgment: TheoryJudgmentId(self.coordinate(judgment)?),
                proofs: self.coordinate(proofs)?,
                proof_steps: self.coordinate(steps)?,
            },
            (3, [rule, premise, elements]) => SemanticPremiseReceipt::ForAll {
                rule: TheoryRuleProgramId(self.coordinate(rule)?),
                premise: self.coordinate(premise)?,
                elements: self.coordinate(elements)?,
            },
            (4, [rule, premise, opcode, inputs, outputs, work]) => {
                SemanticPremiseReceipt::Intrinsic {
                    rule: TheoryRuleProgramId(self.coordinate(rule)?),
                    premise: self.coordinate(premise)?,
                    receipt: SemanticIntrinsicReceiptV1 {
                        opcode: match self.coordinate(opcode)? {
                            0 => SemanticIntrinsicOpcodeV1::ExactTermEq,
                            1 => SemanticIntrinsicOpcodeV1::Utf8AtEnd,
                            2 => SemanticIntrinsicOpcodeV1::Utf8ScalarAt,
                            3 => SemanticIntrinsicOpcodeV1::Utf8Slice,
                            4 => SemanticIntrinsicOpcodeV1::CheckedNatAdd,
                            5 => SemanticIntrinsicOpcodeV1::Utf8ConcatMany,
                            _ => return Err(SemanticWireError::Shape("unknown intrinsic opcode")),
                        },
                        inputs: self.roster(inputs, Self::bytes)?,
                        outputs: self.roster(outputs, Self::bytes)?,
                        work: self.uint(work)?,
                    },
                }
            },
            (5, [rule, premise, guard, evidence]) => SemanticPremiseReceipt::Guard {
                rule: TheoryRuleProgramId(self.coordinate(rule)?),
                premise: self.coordinate(premise)?,
                guard_commitment: self.fingerprint(guard)?,
                evidence_commitment: self.fingerprint(evidence)?,
            },
            _ => return Err(SemanticWireError::Shape("unknown premise tag or arity")),
        })
    }

    fn step(&mut self, value: &Par) -> Result<SemanticNormalizationStepReceiptV1> {
        let [rule, before, after, premises] = self.tuple(value)?;
        Ok(SemanticNormalizationStepReceiptV1 {
            rule: TheoryRuleProgramId(self.coordinate(rule)?),
            before: self.bytes(before)?,
            after: self.bytes(after)?,
            premises: self.roster(premises, Self::premise)?,
        })
    }

    fn hop(&mut self, value: &Par) -> Result<SemanticNormalizationHopReceiptV1> {
        let [before, after, proofs, work] = self.tuple(value)?;
        Ok(SemanticNormalizationHopReceiptV1 {
            before: self.bytes(before)?,
            after: self.bytes(after)?,
            exhaustive_proofs: self.roster(proofs, Self::step)?,
            charged_work: self.uint(work)?,
        })
    }

    fn resource(&mut self, value: &Par) -> Result<SemanticResourceReceipt> {
        let (tag, payload) = self
            .list(value)?
            .split_first()
            .ok_or(SemanticWireError::Shape("empty resource"))?;
        Ok(match (self.coordinate(tag)?, payload) {
            (0, []) => SemanticResourceReceipt::NoSemanticGrade,
            (1, [sort, grade, image]) => SemanticResourceReceipt::Checked {
                grade_sort: TheorySortId(self.coordinate(sort)?),
                grade: self.bytes(grade)?,
                cost_image_fingerprint: self.fingerprint(image)?,
            },
            _ => return Err(SemanticWireError::Shape("unknown resource tag or arity")),
        })
    }

    fn receipt(&mut self, value: &Par) -> Result<SemanticTransitionReceipt> {
        let [language, theory, image, action, rule, input, output, effect, class, resource, premises, hops, work] =
            self.tuple(value)?;
        self.budget.charge(0, VALUE_DESCRIPTOR_BYTES)?;
        Ok(SemanticTransitionReceipt {
            language_fingerprint: self.fingerprint(language)?,
            theory_fingerprint: self.fingerprint(theory)?,
            image_fingerprint: self.fingerprint(image)?,
            action: TheoryActionId(self.coordinate(action)?),
            rule: TheoryRuleProgramId(self.coordinate(rule)?),
            input: self.bytes(input)?,
            output: self.bytes(output)?,
            effect: TheoryEffectId(self.coordinate(effect)?),
            effect_class: match self.coordinate(class)? {
                0 => SemanticEffectClassV1::Pure,
                1 => SemanticEffectClassV1::Structural,
                2 => SemanticEffectClassV1::Behavioral,
                3 => SemanticEffectClassV1::Resource,
                4 => SemanticEffectClassV1::External,
                _ => return Err(SemanticWireError::Shape("unknown effect class")),
            },
            resource: self.resource(resource)?,
            premises: self.roster(premises, Self::premise)?,
            normalization_hops: self.roster(hops, Self::hop)?,
            work: self.uint(work)?,
        })
    }
}

/// Move a complete neutral receipt into its version-one structural wire form.
/// No result ordering, semantic verification or publication is performed here.
pub fn encode_receipt_v1<C: FnMut() -> bool>(
    receipt: SemanticTransitionReceipt,
    budget: &mut ReflectedCodecBudget<'_, C>,
) -> Result<Par> {
    let encoded = Encoder { budget }.receipt(receipt)?;
    budget.charge(0, 0)?;
    Ok(encoded)
}

/// Decode every field with bounded allocations. A decoded receipt is data,
/// never evidence that a semantic transition occurred or authority to execute it.
pub fn decode_receipt_v1<C: FnMut() -> bool>(
    value: &Par,
    budget: &mut ReflectedCodecBudget<'_, C>,
) -> Result<SemanticTransitionReceipt> {
    let receipt = Decoder { budget }.receipt(value)?;
    budget.charge(0, 0)?;
    Ok(receipt)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::semantic_service::tests::transport_receipt;
    use models::rhoapi::EList;
    use models::rust::utils::new_gint_par;

    fn encode(
        r: SemanticTransitionReceipt,
        wl: u64,
        bl: usize,
        stop: usize,
    ) -> (Result<Par>, u64, usize, usize) {
        let mut work = 7;
        let mut calls = 0;
        let mut cancel = || {
            calls += 1;
            calls == stop
        };
        let mut budget = ReflectedCodecBudget::new(&mut work, wl, bl, &mut cancel);
        let result = encode_receipt_v1(r, &mut budget);
        let remaining = budget.finish();
        (result, work, bl - remaining, calls)
    }

    fn decode(
        p: &Par,
        wl: u64,
        bl: usize,
        stop: usize,
    ) -> (Result<SemanticTransitionReceipt>, u64, usize, usize) {
        let mut work = 7;
        let mut calls = 0;
        let mut cancel = || {
            calls += 1;
            calls == stop
        };
        let mut budget = ReflectedCodecBudget::new(&mut work, wl, bl, &mut cancel);
        let result = decode_receipt_v1(p, &mut budget);
        let remaining = budget.finish();
        (result, work, bl - remaining, calls)
    }

    fn list_mut(value: &mut Par) -> &mut EList {
        match value.exprs[0]
            .expr_instance
            .as_mut()
            .expect("fixture expression")
        {
            ExprInstance::EListBody(list) => list,
            _ => panic!("fixture list"),
        }
    }

    #[test]
    fn semantic_wire_receipt_preserves_every_variant_field_and_duplicate() {
        for effect in [
            SemanticEffectClassV1::Pure,
            SemanticEffectClassV1::Structural,
            SemanticEffectClassV1::Behavioral,
            SemanticEffectClassV1::Resource,
            SemanticEffectClassV1::External,
        ] {
            for opcode in [
                SemanticIntrinsicOpcodeV1::ExactTermEq,
                SemanticIntrinsicOpcodeV1::Utf8AtEnd,
                SemanticIntrinsicOpcodeV1::Utf8ScalarAt,
                SemanticIntrinsicOpcodeV1::Utf8Slice,
                SemanticIntrinsicOpcodeV1::CheckedNatAdd,
                SemanticIntrinsicOpcodeV1::Utf8ConcatMany,
            ] {
                for checked in [false, true] {
                    let mut original = transport_receipt();
                    original.effect_class = effect;
                    original.action = TheoryActionId(u32::MAX);
                    original.rule = TheoryRuleProgramId(u32::MAX);
                    original.effect = TheoryEffectId(u32::MAX);
                    if checked {
                        original.resource = SemanticResourceReceipt::Checked {
                            grade_sort: TheorySortId(u32::MAX),
                            grade: vec![0, 255],
                            cost_image_fingerprint: [255; 32],
                        };
                    }
                    if let SemanticPremiseReceipt::Intrinsic { receipt, .. } =
                        &mut original.premises[4]
                    {
                        receipt.opcode = opcode;
                    } else {
                        panic!("intrinsic fixture");
                    }
                    original.premises.push(original.premises[0].clone());
                    let (encoded, ew, eb, _) = encode(original.clone(), 1_000_000, 1_000_000, 0);
                    let encoded = encoded.expect("complete receipt");
                    assert_eq!(exact_list(&encoded).expect("root tuple").len(), 13);
                    assert!(ew < 10_000 && eb < 100_000, "u64::MAX work is data, not a charge");
                    let (decoded, _, _, _) = decode(&encoded, 1_000_000, 1_000_000, 0);
                    let decoded = decoded.expect("all fields");
                    assert_eq!(decoded, original);
                    assert_eq!(encode(decoded, 1_000_000, 1_000_000, 0).0, Ok(encoded));
                }
            }
        }
    }

    #[test]
    fn semantic_wire_receipt_enforces_exact_budgets_and_every_cancellation_boundary() {
        let original = transport_receipt();
        let (wire, ew, eb, ec) = encode(original.clone(), 1_000_000, 1_000_000, 0);
        let wire = wire.expect("baseline encode");
        assert_eq!(encode(original.clone(), ew, eb, 0).0, Ok(wire.clone()));
        for (wl, bl, reason) in [
            (ew - 1, eb, DynamicReflectionError::WorkLimit),
            (ew, eb - 1, DynamicReflectionError::PayloadByteLimit),
        ] {
            let (result, used, bytes, _) = encode(original.clone(), wl, bl, 0);
            assert_eq!(result, Err(SemanticWireError::Resource(reason)));
            assert!(used >= 7 && used <= wl && bytes <= bl);
        }
        for stop in 1..=ec {
            let (result, used, bytes, _) = encode(original.clone(), ew, eb, stop);
            assert_eq!(result, Err(SemanticWireError::Resource(DynamicReflectionError::Cancelled)));
            assert!(used >= 7 && used <= ew && bytes <= eb);
        }
        let (decoded, dw, db, dc) = decode(&wire, 1_000_000, 1_000_000, 0);
        assert_eq!(decoded, Ok(original.clone()));
        assert_eq!(decode(&wire, dw, db, 0).0, Ok(original));
        for (wl, bl, reason) in [
            (dw - 1, db, DynamicReflectionError::WorkLimit),
            (dw, db - 1, DynamicReflectionError::PayloadByteLimit),
        ] {
            let (result, used, bytes, _) = decode(&wire, wl, bl, 0);
            assert_eq!(result, Err(SemanticWireError::Resource(reason)));
            assert!(used >= 7 && used <= wl && bytes <= bl);
        }
        for stop in 1..=dc {
            let (result, used, bytes, _) = decode(&wire, dw, db, stop);
            assert_eq!(result, Err(SemanticWireError::Resource(DynamicReflectionError::Cancelled)));
            assert!(used >= 7 && used <= dw && bytes <= db);
        }
    }

    #[test]
    fn semantic_wire_receipt_rejects_wrong_shape_tags_metadata_and_commitments() {
        let wire = encode(transport_receipt(), 1_000_000, 1_000_000, 0)
            .0
            .expect("fixture");
        let mut malformed = Vec::new();
        let mut value = wire.clone();
        list_mut(&mut value).ps.pop();
        malformed.push(value);
        let mut value = wire.clone();
        list_mut(&mut value).ps.push(Par::default());
        malformed.push(value);
        let mut value = wire.clone();
        list_mut(&mut value).locally_free.push(1);
        malformed.push(value);
        let mut value = wire.clone();
        list_mut(&mut value).connective_used = true;
        malformed.push(value);
        let mut value = wire.clone();
        list_mut(&mut value).remainder = Some(Default::default());
        malformed.push(value);
        for index in [0, 1, 2] {
            let mut value = wire.clone();
            list_mut(&mut value).ps[index] = new_gbytearray_par(vec![0; 31], Vec::new(), false);
            malformed.push(value);
        }
        let mut value = wire.clone();
        list_mut(&mut value).ps[8] = new_gint_par(5, Vec::new(), false);
        malformed.push(value);
        let mut value = wire.clone();
        list_mut(&mut list_mut(&mut value).ps[9])
            .ps
            .push(Par::default());
        malformed.push(value);
        let mut value = wire.clone();
        let premises = list_mut(&mut list_mut(&mut value).ps[10]);
        list_mut(&mut premises.ps[0]).ps[0] = new_gint_par(6, Vec::new(), false);
        malformed.push(value);
        let mut value = wire.clone();
        let premises = list_mut(&mut list_mut(&mut value).ps[10]);
        list_mut(&mut premises.ps[4]).ps[3] = new_gint_par(6, Vec::new(), false);
        malformed.push(value);
        let mut value = wire.clone();
        list_mut(&mut value).ps[10]
            .conditionals
            .push(Default::default());
        malformed.push(value);
        let mut value = wire;
        value.sends.push(Default::default());
        malformed.push(value);
        for value in malformed {
            assert!(decode(&value, 1_000_000, 1_000_000, 0).0.is_err());
        }
    }

    #[test]
    fn semantic_wire_receipt_large_rosters_are_stack_safe() {
        std::thread::Builder::new()
            .stack_size(128 * 1024)
            .spawn(|| {
                let mut receipt = transport_receipt();
                receipt.premises = vec![
                    SemanticPremiseReceipt::Freshness {
                        rule: TheoryRuleProgramId(7),
                        premise: 9,
                    };
                    10_000
                ];
                let encoded = encode(receipt.clone(), 10_000_000, 10_000_000, 0)
                    .0
                    .expect("encode roster");
                assert_eq!(decode(&encoded, 10_000_000, 10_000_000, 0).0, Ok(receipt));
            })
            .expect("small stack thread")
            .join()
            .expect("stack-safe receipt transport");
    }
}
