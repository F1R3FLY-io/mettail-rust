//! Version-two structural transport for actionless relation observations.
//! The installed service validates fresh evidence before encoding; decoding a
//! receipt is never authority or a semantic proof.

use super::receipt::{slots, Decoder, Encoder};
use super::{decode_u32, SemanticWireError};
use crate::semantic_service::RelationObservationResult;
use mettail_dovetail_runtime::{SemanticProjectionReceipt, SemanticRelationNormalFormReceipt};
use mettail_grammar_core::{ProjectionDirectionV1, TheoryRuleProgramId, TheorySortId};
use mettail_rholang_codegen::ReflectedCodecBudget;
use models::rhoapi::Par;

type Result<T> = std::result::Result<T, SemanticWireError>;

impl<C: FnMut() -> bool> Encoder<'_, '_, C> {
    fn relation_receipt(&mut self, r: SemanticRelationNormalFormReceipt) -> Result<Par> {
        self.tuple(|e| {
            Ok([
                e.fingerprint(r.language_fingerprint)?,
                e.fingerprint(r.theory_fingerprint)?,
                e.fingerprint(r.image_fingerprint)?,
                e.uint(r.relation_sort.0)?,
                e.bytes(r.input)?,
                e.bytes(r.output)?,
                e.roster(r.normalization_hops, Self::hop)?,
                e.uint(r.work)?,
            ])
        })
    }

    fn projection_receipt(&mut self, r: SemanticProjectionReceipt) -> Result<Par> {
        self.tuple(|e| {
            Ok([
                e.fingerprint(r.projected_language_fingerprint)?,
                e.fingerprint(r.base_image_fingerprint)?,
                e.fingerprint(r.image_fingerprint)?,
                e.fingerprint(r.host_signature_fingerprint)?,
                e.fingerprint(r.host_codec_profile_fingerprint)?,
                e.uint(r.projection)?,
                e.uint(match r.direction {
                    ProjectionDirectionV1::GuestToHost => 0u8,
                    ProjectionDirectionV1::HostToGuest => 1u8,
                })?,
                e.uint(r.input_sort.0)?,
                e.uint(r.output_sort.0)?,
                e.uint(r.source_occurrence)?,
                e.uint(r.rule.0)?,
                e.bytes(r.input)?,
                e.bytes(r.output)?,
                e.resource(r.resource)?,
                e.roster(r.premises, Self::premise)?,
                e.uint(r.work)?,
            ])
        })
    }
}

impl<C: FnMut() -> bool> Decoder<'_, '_, C> {
    fn relation_receipt(&mut self, value: &Par) -> Result<SemanticRelationNormalFormReceipt> {
        let [language, theory, image, sort, input, output, hops, work] = self.tuple(value)?;
        Ok(SemanticRelationNormalFormReceipt {
            language_fingerprint: self.fingerprint(language)?,
            theory_fingerprint: self.fingerprint(theory)?,
            image_fingerprint: self.fingerprint(image)?,
            relation_sort: TheorySortId(decode_u32(sort, self.budget)?),
            input: self.bytes(input)?,
            output: self.bytes(output)?,
            normalization_hops: self.roster(hops, Self::hop)?,
            work: self.uint(work)?,
        })
    }

    fn projection_receipt(&mut self, value: &Par) -> Result<SemanticProjectionReceipt> {
        let [language, base, image, host, codec, projection, direction, input_sort, output_sort, occurrence, rule, input, output, resource, premises, work] =
            self.tuple(value)?;
        Ok(SemanticProjectionReceipt {
            projected_language_fingerprint: self.fingerprint(language)?,
            base_image_fingerprint: self.fingerprint(base)?,
            image_fingerprint: self.fingerprint(image)?,
            host_signature_fingerprint: self.fingerprint(host)?,
            host_codec_profile_fingerprint: self.fingerprint(codec)?,
            projection: decode_u32(projection, self.budget)?,
            direction: match decode_u32(direction, self.budget)? {
                0 => ProjectionDirectionV1::GuestToHost,
                1 => ProjectionDirectionV1::HostToGuest,
                _ => return Err(SemanticWireError::Shape("unknown projection direction")),
            },
            input_sort: TheorySortId(decode_u32(input_sort, self.budget)?),
            output_sort: TheorySortId(decode_u32(output_sort, self.budget)?),
            source_occurrence: decode_u32(occurrence, self.budget)?,
            rule: TheoryRuleProgramId(decode_u32(rule, self.budget)?),
            input: self.bytes(input)?,
            output: self.bytes(output)?,
            resource: self.resource(resource)?,
            premises: self.roster(premises, Self::premise)?,
            work: self.uint(work)?,
        })
    }
}

/// Encode every result in the kernel's original order, retaining duplicate
/// normal forms and every supporting terminal/projection proof occurrence.
pub(crate) fn encode_relation_results_v2<C: FnMut() -> bool>(
    results: Vec<RelationObservationResult>,
    budget: &mut ReflectedCodecBudget<'_, C>,
) -> Result<Par> {
    let encoded = Encoder { budget }.roster(results, |e, result| {
        e.budget.charge(1, 0)?;
        if !result.term.locally_free.is_empty() || result.term.connective_used {
            return Err(SemanticWireError::Shape("relation result term is not closed"));
        }
        e.tuple(|e| {
            Ok([
                result.term,
                e.relation_receipt(result.relation_receipt)?,
                e.roster(result.terminal_receipts, |e, receipt| e.relation_receipt(receipt))?,
                e.roster(result.projection_receipts, |e, receipt| e.projection_receipt(receipt))?,
            ])
        })
    })?;
    budget.charge(0, 0)?;
    Ok(encoded)
}

/// Borrow the structural term, while decoding the complete proof rosters.
/// This avoids recursively cloning deeply nested Rholang terms.
pub struct DecodedRelationResult<'a> {
    pub term: &'a Par,
    pub relation_receipt: SemanticRelationNormalFormReceipt,
    pub terminal_receipts: Vec<SemanticRelationNormalFormReceipt>,
    pub projection_receipts: Vec<SemanticProjectionReceipt>,
}

pub fn decode_relation_results_v2<'a, C: FnMut() -> bool>(
    value: &'a Par,
    budget: &mut ReflectedCodecBudget<'_, C>,
) -> Result<Vec<DecodedRelationResult<'a>>> {
    let mut decoder = Decoder { budget };
    let values = decoder.list(value)?;
    let mut decoded = slots(values.len(), 0, decoder.budget)?;
    for value in values {
        let [term, relation, terminal, projections] = decoder.tuple(value)?;
        decoder.budget.charge(1, 0)?;
        if !term.locally_free.is_empty() || term.connective_used {
            return Err(SemanticWireError::Shape("relation result term is not closed"));
        }
        decoded.push(DecodedRelationResult {
            term,
            relation_receipt: decoder.relation_receipt(relation)?,
            terminal_receipts: decoder
                .roster(terminal, |d, receipt| d.relation_receipt(receipt))?,
            projection_receipts: decoder
                .roster(projections, |d, receipt| d.projection_receipt(receipt))?,
        });
    }
    budget.charge(0, 0)?;
    Ok(decoded)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::language_install::exact_list;
    use mettail_dovetail_runtime::{SemanticPremiseReceipt, SemanticResourceReceipt};
    use models::rhoapi::expr::ExprInstance;
    use models::rust::utils::new_gint_par;

    fn relation(output: u8) -> SemanticRelationNormalFormReceipt {
        SemanticRelationNormalFormReceipt {
            language_fingerprint: [1; 32],
            theory_fingerprint: [2; 32],
            image_fingerprint: [3; 32],
            relation_sort: TheorySortId(4),
            input: vec![5],
            output: vec![output],
            normalization_hops: Vec::new(),
            work: 7,
        }
    }

    fn projection() -> SemanticProjectionReceipt {
        SemanticProjectionReceipt {
            projected_language_fingerprint: [8; 32],
            base_image_fingerprint: [9; 32],
            image_fingerprint: [10; 32],
            host_signature_fingerprint: [11; 32],
            host_codec_profile_fingerprint: [12; 32],
            projection: 13,
            direction: ProjectionDirectionV1::GuestToHost,
            input_sort: TheorySortId(14),
            output_sort: TheorySortId(15),
            source_occurrence: 16,
            rule: TheoryRuleProgramId(17),
            input: vec![18],
            output: vec![19],
            resource: SemanticResourceReceipt::NoSemanticGrade,
            premises: vec![
                SemanticPremiseReceipt::Freshness {
                    rule: TheoryRuleProgramId(17),
                    premise: 0,
                },
                SemanticPremiseReceipt::Freshness {
                    rule: TheoryRuleProgramId(17),
                    premise: 0,
                },
            ],
            work: 20,
        }
    }

    #[test]
    fn relation_codec_round_trips_every_result_and_duplicate_proof_occurrence() {
        let results = vec![
            RelationObservationResult {
                term: new_gint_par(21, Vec::new(), false),
                relation_receipt: relation(22),
                terminal_receipts: vec![relation(23), relation(23)],
                projection_receipts: vec![projection(), projection()],
            },
            RelationObservationResult {
                term: new_gint_par(24, Vec::new(), false),
                relation_receipt: relation(25),
                terminal_receipts: vec![relation(26)],
                projection_receipts: vec![projection()],
            },
        ];
        let mut work = 0;
        let mut cancel = || false;
        let mut budget = ReflectedCodecBudget::new(&mut work, 1_000_000, 1_000_000, &mut cancel);
        let encoded = encode_relation_results_v2(results, &mut budget).unwrap();
        let decoded = decode_relation_results_v2(&encoded, &mut budget).unwrap();
        assert_eq!(decoded.len(), 2);
        assert_eq!(decoded[0].term, &new_gint_par(21, Vec::new(), false));
        assert_eq!(decoded[1].term, &new_gint_par(24, Vec::new(), false));
        assert_eq!(decoded[0].relation_receipt, relation(22));
        assert_eq!(decoded[1].relation_receipt, relation(25));
        assert_eq!(decoded[0].terminal_receipts, vec![relation(23), relation(23)]);
        assert_eq!(decoded[0].projection_receipts, vec![projection(), projection()]);
        assert_eq!(decoded[1].terminal_receipts, vec![relation(26)]);
    }

    #[test]
    fn relation_codec_rejects_unknown_projection_direction_and_small_allowance() {
        let result = RelationObservationResult {
            term: new_gint_par(1, Vec::new(), false),
            relation_receipt: relation(2),
            terminal_receipts: vec![relation(3)],
            projection_receipts: vec![projection()],
        };
        let mut work = 0;
        let mut cancel = || false;
        let mut budget = ReflectedCodecBudget::new(&mut work, 1_000_000, 1_000_000, &mut cancel);
        let mut encoded = encode_relation_results_v2(vec![result], &mut budget).unwrap();
        let Some(ExprInstance::EListBody(results)) = encoded.exprs[0].expr_instance.as_mut() else {
            panic!("result roster");
        };
        let Some(ExprInstance::EListBody(fields)) = results.ps[0].exprs[0].expr_instance.as_mut()
        else {
            panic!("result tuple");
        };
        let Some(ExprInstance::EListBody(projections)) =
            fields.ps[3].exprs[0].expr_instance.as_mut()
        else {
            panic!("projection roster");
        };
        let Some(ExprInstance::EListBody(projection)) =
            projections.ps[0].exprs[0].expr_instance.as_mut()
        else {
            panic!("projection tuple");
        };
        projection.ps[6] = new_gint_par(2, Vec::new(), false);
        assert_eq!(exact_list(&encoded).unwrap().len(), 1);
        assert!(matches!(
            decode_relation_results_v2(&encoded, &mut budget),
            Err(SemanticWireError::Shape("unknown projection direction"))
        ));
        let mut work = 0;
        let mut budget = ReflectedCodecBudget::new(&mut work, 0, 0, &mut cancel);
        assert!(matches!(
            decode_relation_results_v2(&encoded, &mut budget),
            Err(SemanticWireError::Resource(_))
        ));
    }
}
