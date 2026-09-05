//! Bounded canonical wire codec for executable theory images.
//!
//! The wire format is deliberately flat and count-prefixed. Decoding is bound
//! to the authoritative [`LanguageCoreV1`]: source-derived constructor, rule,
//! arena, and action counts are checked before their corresponding vectors are
//! allocated. Configured aggregate limits and the encoded-byte ceiling cover
//! automaton data that is derived rather than present in the source.

use crate::{
    CollectionKind, JudgmentDecisionV1, JudgmentRuleV1, LanguageCoreV1, LanguageRight,
    LanguageRights, PathMapModeV1, SemanticEffectClassV1, TheoryActionId, TheoryActionImageV1,
    TheoryConstructorId, TheoryConstructorImageV1, TheoryEffectId, TheoryGrammarConstructorV1,
    TheoryImageAdmissionLimits, TheoryImageError, TheoryImageJudgmentAtomV1, TheoryImageOperatorV1,
    TheoryImagePremiseFormV1, TheoryImagePremiseNodeV1, TheoryImageTermFormV1,
    TheoryImageTermNodeV1, TheoryImageVariableV1, TheoryJudgmentId, TheoryJudgmentImageV1,
    TheoryJudgmentPatternAutomatonV1, TheoryJudgmentPatternEntryV1, TheoryJudgmentRuleProgramId,
    TheoryJudgmentRuleProgramV1, TheoryLiteralCarrierV1, TheoryLiteralV1, TheoryPatternAutomatonV1,
    TheoryPatternEntryId, TheoryPatternEntryV1, TheoryPatternInvocationV1,
    TheoryPatternStateFormV1, TheoryPatternStateId, TheoryPatternStateV1, TheoryResourceProfileV1,
    TheoryRuleArenaV1, TheoryRuleDirectionV1, TheoryRuleDispositionV1, TheoryRuleOriginV1,
    TheoryRuleProgramId, TheoryRuleProgramV1, TheoryRuleSuppressionV1, TheorySemanticImageV1,
    TheorySortId, TheorySortImageV1, TheorySortKindImageV1, TheoryTermId, TheoryVariableId,
    TheoryVariableRoleV1, TheoryWorkChargeV1, THEORY_SEMANTIC_IMAGE_ABI_CURRENT,
};

const THEORY_IMAGE_MAGIC: &[u8; 8] = b"MTTHIMG1";
const RIGHT_COUNT: u16 = 12;

trait ImageSink {
    fn write(&mut self, bytes: &[u8]) -> Result<(), TheoryImageError>;
}

struct CountSink(usize);

impl ImageSink for CountSink {
    fn write(&mut self, bytes: &[u8]) -> Result<(), TheoryImageError> {
        self.0 = self
            .0
            .checked_add(bytes.len())
            .ok_or(TheoryImageError::LengthOverflow)?;
        Ok(())
    }
}

struct VecSink<'a>(&'a mut Vec<u8>);

impl ImageSink for VecSink<'_> {
    fn write(&mut self, bytes: &[u8]) -> Result<(), TheoryImageError> {
        self.0.extend_from_slice(bytes);
        Ok(())
    }
}

struct HashSink<'a>(&'a mut blake3::Hasher);

impl ImageSink for HashSink<'_> {
    fn write(&mut self, bytes: &[u8]) -> Result<(), TheoryImageError> {
        self.0.update(bytes);
        Ok(())
    }
}

impl TheorySemanticImageV1 {
    /// Return a domain-separated commitment without materializing a serialized
    /// copy of the image.
    pub fn fingerprint(&self) -> Result<[u8; 32], TheoryImageError> {
        let mut hasher = blake3::Hasher::new();
        hasher.update(b"mettail-theory-semantic-image/1\0");
        encode_image(self, &mut HashSink(&mut hasher))?;
        Ok(*hasher.finalize().as_bytes())
    }

    /// Validate and encode the image in the canonical flat wire format.
    pub fn encode(
        &self,
        language: &LanguageCoreV1,
        limits: TheoryImageAdmissionLimits,
    ) -> Result<Vec<u8>, TheoryImageError> {
        self.validate(language, limits)?;
        let length = encoded_theory_image_len(self)?;
        enforce(length, limits.max_encoded_bytes, "encoded bytes")?;
        let mut bytes = empty_vec(length)?;
        encode_image(self, &mut VecSink(&mut bytes))?;
        debug_assert_eq!(bytes.len(), length);
        Ok(bytes)
    }

    /// Decode untrusted bytes under source-exact and configured allocation
    /// bounds, then rerun complete fingerprint and structural validation.
    pub fn decode(
        bytes: &[u8],
        language: &LanguageCoreV1,
        limits: TheoryImageAdmissionLimits,
    ) -> Result<Self, TheoryImageError> {
        limits.validate_source(language)?;
        enforce(bytes.len(), limits.max_encoded_bytes, "encoded bytes")?;
        let mut reader = ImageReader::new(bytes);
        if reader.read_exact(THEORY_IMAGE_MAGIC.len())? != THEORY_IMAGE_MAGIC {
            return Err(TheoryImageError::InvalidMagic);
        }
        let abi = reader.read_u16()?;
        if abi != THEORY_SEMANTIC_IMAGE_ABI_CURRENT {
            return Err(TheoryImageError::UnsupportedAbi(abi));
        }
        let compiler_abi = reader.read_u16()?;
        let language_fingerprint = reader.read_array()?;
        let grammar_fingerprint = reader.read_array()?;
        let theory_fingerprint = reader.read_array()?;
        let resource_profile = decode_resource_profile(&mut reader)?;

        let sort_count = reader.read_exact_count(language.theory.sorts.len(), "sort count")?;
        let mut sorts = empty_vec(sort_count)?;
        let mut totals = DecodeTotals::default();
        for (index, source) in language.theory.sorts.iter().enumerate() {
            sorts.push(decode_sort(
                &mut reader,
                TheorySortId(u32::try_from(index).map_err(|_| TheoryImageError::LengthOverflow)?),
                source,
                limits,
                &mut totals,
            )?);
        }

        let constructor_count =
            reader.read_exact_count(language.theory.constructors.len(), "constructor count")?;
        let mut constructors = empty_vec(constructor_count)?;
        for source in &language.theory.constructors {
            constructors.push(decode_constructor(&mut reader, source.domain.len())?);
        }

        let expected_rules = language
            .theory
            .equations
            .len()
            .checked_mul(2)
            .and_then(|count| count.checked_add(language.theory.rewrites.len()))
            .ok_or(TheoryImageError::LengthOverflow)?;
        let rule_count = reader.read_exact_count(expected_rules, "rule count")?;
        let mut rules = empty_vec(rule_count)?;
        for _ in 0..rule_count {
            let id = TheoryRuleProgramId(reader.read_u32()?);
            let origin = decode_origin(&mut reader)?;
            let source = source_arena(language, origin)?;
            rules.push(decode_rule(&mut reader, id, origin, source, limits, &mut totals)?);
        }

        let patterns = decode_patterns(&mut reader, limits, &mut totals)?;

        let judgment_count =
            reader.read_exact_count(language.theory.judgments.len(), "judgment count")?;
        let mut judgments = empty_vec(judgment_count)?;
        for source in &language.theory.judgments {
            judgments.push(decode_judgment(
                &mut reader,
                source.arguments.len(),
                source.rules.len(),
            )?);
        }

        let expected_judgment_rules =
            language
                .theory
                .judgments
                .iter()
                .try_fold(0usize, |count, judgment| {
                    count
                        .checked_add(judgment.rules.len())
                        .ok_or(TheoryImageError::LengthOverflow)
                })?;
        let judgment_rule_count =
            reader.read_exact_count(expected_judgment_rules, "judgment rule count")?;
        let mut judgment_rules = empty_vec(judgment_rule_count)?;
        for judgment in &language.theory.judgments {
            for source in &judgment.rules {
                judgment_rules.push(decode_judgment_rule(
                    &mut reader,
                    source,
                    limits,
                    &mut totals,
                )?);
            }
        }

        let judgment_patterns = decode_judgment_patterns(&mut reader, limits, &mut totals)?;

        let action_count =
            reader.read_exact_count(language.theory.actions.len(), "action count")?;
        let mut actions = empty_vec(action_count)?;
        for source in &language.theory.actions {
            actions.push(decode_action(&mut reader, source.domain.len(), limits, &mut totals)?);
        }
        if !reader.is_empty() {
            return Err(TheoryImageError::TrailingBytes);
        }
        let image = Self {
            abi,
            compiler_abi,
            language_fingerprint,
            grammar_fingerprint,
            theory_fingerprint,
            resource_profile,
            sorts,
            constructors,
            rules,
            patterns,
            judgments,
            judgment_rules,
            judgment_patterns,
            actions,
        };
        image.validate(language, limits)?;
        Ok(image)
    }
}

pub(crate) fn encoded_theory_image_len(
    image: &TheorySemanticImageV1,
) -> Result<usize, TheoryImageError> {
    let mut sink = CountSink(0);
    encode_image(image, &mut sink)?;
    Ok(sink.0)
}

fn encode_image<S: ImageSink>(
    image: &TheorySemanticImageV1,
    sink: &mut S,
) -> Result<(), TheoryImageError> {
    sink.write(THEORY_IMAGE_MAGIC)?;
    write_u16(sink, image.abi)?;
    write_u16(sink, image.compiler_abi)?;
    sink.write(&image.language_fingerprint)?;
    sink.write(&image.grammar_fingerprint)?;
    sink.write(&image.theory_fingerprint)?;
    encode_resource_profile(sink, image.resource_profile)?;

    write_count(sink, image.sorts.len())?;
    for sort in &image.sorts {
        encode_sort(sink, sort)?;
    }

    write_count(sink, image.constructors.len())?;
    for constructor in &image.constructors {
        write_u32(sink, constructor.id.0)?;
        write_ids(sink, &constructor.domain, |id| id.0)?;
        write_u32(sink, constructor.codomain.0)?;
        match constructor.grammar {
            None => write_u8(sink, 0)?,
            Some(grammar) => {
                write_u8(sink, 1)?;
                write_u32(sink, grammar.category.0)?;
                write_u32(sink, grammar.constructor.0)?;
            },
        }
    }

    write_count(sink, image.rules.len())?;
    for rule in &image.rules {
        write_u32(sink, rule.id.0)?;
        encode_origin(sink, rule.origin)?;
        encode_disposition(sink, rule.disposition)?;
        write_string(sink, &rule.name)?;
        write_count(sink, rule.variables.len())?;
        for variable in &rule.variables {
            write_u32(sink, variable.id.0)?;
            write_u32(sink, variable.sort.0)?;
            write_u8(sink, encode_variable_role(variable.role))?;
        }
        write_count(sink, rule.terms.len())?;
        for term in &rule.terms {
            write_u32(sink, term.sort.0)?;
            encode_term_form(sink, &term.form)?;
        }
        write_count(sink, rule.premises.len())?;
        for premise in &rule.premises {
            encode_premise(sink, &premise.form)?;
        }
        write_u32_values(sink, &rule.premise_roots)?;
        write_u32(sink, rule.left.0)?;
        write_u32(sink, rule.right.0)?;
        encode_work_charge(sink, rule.charge)?;
    }

    write_count(sink, image.patterns.states.len())?;
    for state in &image.patterns.states {
        encode_pattern_state(sink, state)?;
    }
    write_count(sink, image.patterns.entries.len())?;
    for entry in &image.patterns.entries {
        write_u32(sink, entry.id.0)?;
        write_u32(sink, entry.rule.0)?;
        write_u32(sink, entry.root.0)?;
        write_ids(sink, &entry.slot_variables, |id| id.0)?;
    }

    write_count(sink, image.judgments.len())?;
    for judgment in &image.judgments {
        write_u32(sink, judgment.id.0)?;
        write_ids(sink, &judgment.arguments, |id| id.0)?;
        write_u8(sink, encode_judgment_decision(judgment.decision))?;
        write_ids(sink, &judgment.rules, |id| id.0)?;
    }

    write_count(sink, image.judgment_rules.len())?;
    for rule in &image.judgment_rules {
        write_u32(sink, rule.id.0)?;
        write_u32(sink, rule.owner.0)?;
        write_string(sink, &rule.name)?;
        write_count(sink, rule.variables.len())?;
        for variable in &rule.variables {
            write_u32(sink, variable.id.0)?;
            write_u32(sink, variable.sort.0)?;
            write_u8(sink, encode_variable_role(variable.role))?;
        }
        write_count(sink, rule.terms.len())?;
        for term in &rule.terms {
            write_u32(sink, term.sort.0)?;
            encode_term_form(sink, &term.form)?;
        }
        write_count(sink, rule.premises.len())?;
        for premise in &rule.premises {
            encode_judgment_atom(sink, premise)?;
        }
        encode_judgment_atom(sink, &rule.conclusion)?;
        encode_work_charge(sink, rule.charge)?;
    }

    write_count(sink, image.judgment_patterns.states.len())?;
    for state in &image.judgment_patterns.states {
        encode_pattern_state(sink, state)?;
    }
    write_count(sink, image.judgment_patterns.entries.len())?;
    for entry in &image.judgment_patterns.entries {
        write_u32(sink, entry.id.0)?;
        write_u32(sink, entry.rule.0)?;
        write_u32(sink, entry.root.0)?;
        write_ids(sink, &entry.slot_variables, |id| id.0)?;
    }

    write_count(sink, image.actions.len())?;
    for action in &image.actions {
        write_u32(sink, action.id.0)?;
        write_ids(sink, &action.domain, |id| id.0)?;
        write_u32(sink, action.codomain.0)?;
        write_ids(sink, &action.transitions, |id| id.0)?;
        write_u32(sink, action.effect.0)?;
        write_u8(sink, encode_effect_class(action.effect_class))?;
        write_u16(sink, encode_rights(&action.required_rights))?;
        write_u32(sink, action.grade.0)?;
    }
    Ok(())
}

fn encode_resource_profile<S: ImageSink>(
    sink: &mut S,
    profile: TheoryResourceProfileV1,
) -> Result<(), TheoryImageError> {
    match profile {
        TheoryResourceProfileV1::Uncosted => write_u8(sink, 0),
        TheoryResourceProfileV1::Costed { grade_sort } => {
            write_u8(sink, 1)?;
            write_u32(sink, grade_sort.0)
        },
    }
}

fn decode_resource_profile(
    reader: &mut ImageReader<'_>,
) -> Result<TheoryResourceProfileV1, TheoryImageError> {
    match reader.read_u8()? {
        0 => Ok(TheoryResourceProfileV1::Uncosted),
        1 => Ok(TheoryResourceProfileV1::Costed {
            grade_sort: TheorySortId(reader.read_u32()?),
        }),
        tag => Err(TheoryImageError::InvalidTag(tag)),
    }
}

fn encode_sort<S: ImageSink>(
    sink: &mut S,
    sort: &TheorySortImageV1,
) -> Result<(), TheoryImageError> {
    write_u32(sink, sort.id.0)?;
    match &sort.kind {
        TheorySortKindImageV1::Syntax { literal } => {
            write_u8(sink, 0)?;
            encode_optional_literal_carrier(sink, literal.as_ref())
        },
        TheorySortKindImageV1::Collection { kind, key, element } => {
            write_u8(sink, 1)?;
            write_u8(sink, encode_collection_kind(*kind))?;
            write_optional_u32(sink, key.map(|id| id.0))?;
            write_u32(sink, element.0)
        },
        TheorySortKindImageV1::Function { domain, codomain, multiple } => {
            write_u8(sink, 2)?;
            write_u32(sink, domain.0)?;
            write_u32(sink, codomain.0)?;
            write_u8(sink, u8::from(*multiple))
        },
        TheorySortKindImageV1::Product { factors } => {
            write_u8(sink, 3)?;
            write_ids(sink, factors, |id| id.0)
        },
        TheorySortKindImageV1::Opaque { abi } => {
            write_u8(sink, 4)?;
            write_string(sink, abi)
        },
    }
}

fn encode_optional_literal_carrier<S: ImageSink>(
    sink: &mut S,
    carrier: Option<&TheoryLiteralCarrierV1>,
) -> Result<(), TheoryImageError> {
    match carrier {
        None => write_u8(sink, 0),
        Some(carrier) => {
            write_u8(sink, 1)?;
            encode_literal_carrier(sink, carrier)
        },
    }
}

fn encode_literal_carrier<S: ImageSink>(
    sink: &mut S,
    carrier: &TheoryLiteralCarrierV1,
) -> Result<(), TheoryImageError> {
    match carrier {
        TheoryLiteralCarrierV1::Boolean => write_u8(sink, 0),
        TheoryLiteralCarrierV1::Integer => write_u8(sink, 1),
        TheoryLiteralCarrierV1::Rational => write_u8(sink, 2),
        TheoryLiteralCarrierV1::FixedPoint => write_u8(sink, 3),
        TheoryLiteralCarrierV1::Float => write_u8(sink, 4),
        TheoryLiteralCarrierV1::String => write_u8(sink, 5),
        TheoryLiteralCarrierV1::Bytes => write_u8(sink, 6),
        TheoryLiteralCarrierV1::Unit => write_u8(sink, 7),
        TheoryLiteralCarrierV1::External(abi) => {
            write_u8(sink, 8)?;
            write_string(sink, abi)
        },
        TheoryLiteralCarrierV1::HostOpaque(abi) => {
            write_u8(sink, 9)?;
            write_string(sink, abi)
        },
    }
}

fn decode_sort(
    reader: &mut ImageReader<'_>,
    expected_id: TheorySortId,
    source: &crate::TheorySortV1,
    limits: TheoryImageAdmissionLimits,
    totals: &mut DecodeTotals,
) -> Result<TheorySortImageV1, TheoryImageError> {
    let id = TheorySortId(reader.read_u32()?);
    if id != expected_id {
        return Err(TheoryImageError::SourceMismatch { kind: "sort id", index: expected_id.0 });
    }
    let tag = reader.read_u8()?;
    let kind = match (&source.kind, tag) {
        (crate::TheorySortKindV1::Syntax { .. }, 0) => TheorySortKindImageV1::Syntax {
            literal: decode_optional_literal_carrier(reader, limits, totals)?,
        },
        (crate::TheorySortKindV1::Collection { .. }, 1) => {
            charge_sort_references(totals, limits, 1)?;
            let kind = decode_collection_kind(reader.read_u8()?)?;
            let key = read_optional_u32(reader)?.map(TheorySortId);
            charge_sort_references(totals, limits, usize::from(key.is_some()))?;
            TheorySortKindImageV1::Collection {
                kind,
                key,
                element: TheorySortId(reader.read_u32()?),
            }
        },
        (crate::TheorySortKindV1::Function { .. }, 2) => {
            charge_sort_references(totals, limits, 2)?;
            TheorySortKindImageV1::Function {
                domain: TheorySortId(reader.read_u32()?),
                codomain: TheorySortId(reader.read_u32()?),
                multiple: reader.read_bool()?,
            }
        },
        (crate::TheorySortKindV1::Product { factors }, 3) => {
            charge_sort_references(totals, limits, factors.len())?;
            TheorySortKindImageV1::Product {
                factors: read_ids_exact(reader, factors.len(), TheorySortId, "product factors")?,
            }
        },
        (crate::TheorySortKindV1::Opaque { .. }, 4) => TheorySortKindImageV1::Opaque {
            abi: decode_sort_metadata(reader, limits, totals)?,
        },
        (_, 0..=4) => {
            return Err(TheoryImageError::SourceMismatch {
                kind: "sort kind",
                index: expected_id.0,
            });
        },
        (_, tag) => return Err(TheoryImageError::InvalidTag(tag)),
    };
    Ok(TheorySortImageV1 { id, kind })
}

fn decode_optional_literal_carrier(
    reader: &mut ImageReader<'_>,
    limits: TheoryImageAdmissionLimits,
    totals: &mut DecodeTotals,
) -> Result<Option<TheoryLiteralCarrierV1>, TheoryImageError> {
    match reader.read_u8()? {
        0 => Ok(None),
        1 => decode_literal_carrier(reader, limits, totals).map(Some),
        tag => Err(TheoryImageError::InvalidTag(tag)),
    }
}

fn decode_literal_carrier(
    reader: &mut ImageReader<'_>,
    limits: TheoryImageAdmissionLimits,
    totals: &mut DecodeTotals,
) -> Result<TheoryLiteralCarrierV1, TheoryImageError> {
    Ok(match reader.read_u8()? {
        0 => TheoryLiteralCarrierV1::Boolean,
        1 => TheoryLiteralCarrierV1::Integer,
        2 => TheoryLiteralCarrierV1::Rational,
        3 => TheoryLiteralCarrierV1::FixedPoint,
        4 => TheoryLiteralCarrierV1::Float,
        5 => TheoryLiteralCarrierV1::String,
        6 => TheoryLiteralCarrierV1::Bytes,
        7 => TheoryLiteralCarrierV1::Unit,
        8 => TheoryLiteralCarrierV1::External(decode_sort_metadata(reader, limits, totals)?),
        9 => TheoryLiteralCarrierV1::HostOpaque(decode_sort_metadata(reader, limits, totals)?),
        tag => return Err(TheoryImageError::InvalidTag(tag)),
    })
}

fn decode_sort_metadata(
    reader: &mut ImageReader<'_>,
    limits: TheoryImageAdmissionLimits,
    totals: &mut DecodeTotals,
) -> Result<String, TheoryImageError> {
    let remaining = limits
        .max_total_sort_metadata_bytes
        .checked_sub(totals.sort_metadata_bytes)
        .ok_or(TheoryImageError::LimitExceeded("sort metadata bytes"))?;
    let value = reader.read_string(remaining, "sort metadata bytes")?;
    add_limit(
        &mut totals.sort_metadata_bytes,
        value.len(),
        limits.max_total_sort_metadata_bytes,
        "sort metadata bytes",
    )?;
    Ok(value)
}

fn charge_sort_references(
    totals: &mut DecodeTotals,
    limits: TheoryImageAdmissionLimits,
    count: usize,
) -> Result<(), TheoryImageError> {
    add_limit(
        &mut totals.sort_references,
        count,
        limits.max_total_sort_references,
        "sort references",
    )
}

fn encode_pattern_state<S: ImageSink>(
    sink: &mut S,
    state: &TheoryPatternStateV1,
) -> Result<(), TheoryImageError> {
    write_u32(sink, state.id.0)?;
    write_u32(sink, state.slot_count)?;
    match &state.form {
        TheoryPatternStateFormV1::Bind => write_u8(sink, 0),
        TheoryPatternStateFormV1::Apply { operator, arguments } => {
            write_u8(sink, 1)?;
            encode_operator(sink, operator)?;
            write_count(sink, arguments.len())?;
            for invocation in arguments {
                write_u32(sink, invocation.state.0)?;
                write_u32_values(sink, &invocation.parent_slots)?;
            }
            Ok(())
        },
    }
}

fn encode_judgment_atom<S: ImageSink>(
    sink: &mut S,
    atom: &TheoryImageJudgmentAtomV1,
) -> Result<(), TheoryImageError> {
    write_u32(sink, atom.judgment.0)?;
    write_ids(sink, &atom.terms, |id| id.0)
}

fn encode_work_charge<S: ImageSink>(
    sink: &mut S,
    charge: TheoryWorkChargeV1,
) -> Result<(), TheoryImageError> {
    write_u32(sink, charge.pattern_nodes)?;
    write_u32(sink, charge.template_nodes)?;
    write_u32(sink, charge.premise_nodes)?;
    write_u32(sink, charge.variable_slots)
}

fn encode_judgment_decision(decision: JudgmentDecisionV1) -> u8 {
    match decision {
        JudgmentDecisionV1::Exact => 0,
        JudgmentDecisionV1::Bounded => 1,
    }
}

fn decode_judgment_decision(tag: u8) -> Result<JudgmentDecisionV1, TheoryImageError> {
    match tag {
        0 => Ok(JudgmentDecisionV1::Exact),
        1 => Ok(JudgmentDecisionV1::Bounded),
        _ => Err(TheoryImageError::InvalidTag(tag)),
    }
}

fn encode_origin<S: ImageSink>(
    sink: &mut S,
    origin: TheoryRuleOriginV1,
) -> Result<(), TheoryImageError> {
    match origin {
        TheoryRuleOriginV1::Equation {
            source,
            direction: TheoryRuleDirectionV1::Forward,
        } => {
            write_u8(sink, 0)?;
            write_u32(sink, source)
        },
        TheoryRuleOriginV1::Equation {
            source,
            direction: TheoryRuleDirectionV1::Reverse,
        } => {
            write_u8(sink, 1)?;
            write_u32(sink, source)
        },
        TheoryRuleOriginV1::Rewrite { source } => {
            write_u8(sink, 2)?;
            write_u32(sink, source)
        },
    }
}

fn encode_disposition<S: ImageSink>(
    sink: &mut S,
    disposition: TheoryRuleDispositionV1,
) -> Result<(), TheoryImageError> {
    match disposition {
        TheoryRuleDispositionV1::Executable => write_u8(sink, 0),
        TheoryRuleDispositionV1::Suppressed(TheoryRuleSuppressionV1::MatchAllRoot) => {
            write_u8(sink, 1)
        },
        TheoryRuleDispositionV1::Suppressed(TheoryRuleSuppressionV1::PremiseDependency {
            variable,
        }) => {
            write_u8(sink, 2)?;
            write_u32(sink, variable.0)
        },
        TheoryRuleDispositionV1::Suppressed(TheoryRuleSuppressionV1::UnboundTemplate {
            variable,
        }) => {
            write_u8(sink, 3)?;
            write_u32(sink, variable.0)
        },
    }
}

fn encode_term_form<S: ImageSink>(
    sink: &mut S,
    form: &TheoryImageTermFormV1,
) -> Result<(), TheoryImageError> {
    match form {
        TheoryImageTermFormV1::Slot(variable) => {
            write_u8(sink, 0)?;
            write_u32(sink, variable.0)
        },
        TheoryImageTermFormV1::Apply {
            operator,
            arguments,
            slots,
            remainder,
            pathmap_mode,
        } => {
            write_u8(sink, 1)?;
            encode_operator(sink, operator)?;
            write_ids(sink, arguments, |id| id.0)?;
            write_ids(sink, slots, |id| id.0)?;
            write_optional_u32(sink, remainder.map(|id| id.0))?;
            write_pathmap_mode(sink, *pathmap_mode)
        },
        TheoryImageTermFormV1::Map { sources, parameters, body } => {
            write_u8(sink, 2)?;
            write_ids(sink, sources, |id| id.0)?;
            write_ids(sink, parameters, |id| id.0)?;
            write_u32(sink, body.0)
        },
    }
}

fn encode_operator<S: ImageSink>(
    sink: &mut S,
    operator: &TheoryImageOperatorV1,
) -> Result<(), TheoryImageError> {
    match operator {
        TheoryImageOperatorV1::Constructor(id) => {
            write_u8(sink, 0)?;
            write_u32(sink, id.0)
        },
        TheoryImageOperatorV1::Abstraction { sort } => {
            write_u8(sink, 1)?;
            write_u32(sink, sort.0)
        },
        TheoryImageOperatorV1::Substitution { sort, function } => {
            write_u8(sink, 2)?;
            write_u32(sink, sort.0)?;
            write_u32(sink, function.0)
        },
        TheoryImageOperatorV1::Collection { sort, element, kind } => {
            write_u8(sink, 3)?;
            write_u32(sink, sort.0)?;
            write_u32(sink, element.0)?;
            write_u8(sink, encode_collection_kind(*kind))
        },
        TheoryImageOperatorV1::Product { sort } => {
            write_u8(sink, 4)?;
            write_u32(sink, sort.0)
        },
        TheoryImageOperatorV1::Literal { sort, value } => {
            write_u8(sink, 5)?;
            write_u32(sink, sort.0)?;
            encode_literal(sink, value)
        },
        TheoryImageOperatorV1::Judgment { judgment } => {
            write_u8(sink, 6)?;
            write_u32(sink, judgment.0)
        },
        TheoryImageOperatorV1::PathMapMode { sort, mode } => {
            write_u8(sink, 7)?;
            write_u32(sink, sort.0)?;
            write_u8(
                sink,
                match mode {
                    PathMapModeV1::NeutralEmpty => 0,
                    PathMapModeV1::Set => 1,
                    PathMapModeV1::Map => 2,
                },
            )
        },
    }
}

fn encode_literal<S: ImageSink>(
    sink: &mut S,
    literal: &TheoryLiteralV1,
) -> Result<(), TheoryImageError> {
    match literal {
        TheoryLiteralV1::String(value) => {
            write_u8(sink, 0)?;
            write_string(sink, value)
        },
        TheoryLiteralV1::Bytes(value) => {
            write_u8(sink, 1)?;
            write_bytes(sink, value)
        },
        TheoryLiteralV1::Integer(value) => {
            write_u8(sink, 2)?;
            sink.write(&value.to_le_bytes())
        },
        TheoryLiteralV1::FloatBits(value) => {
            write_u8(sink, 3)?;
            sink.write(&value.to_le_bytes())
        },
        TheoryLiteralV1::Boolean(value) => {
            write_u8(sink, 4)?;
            write_bool(sink, *value)
        },
        TheoryLiteralV1::Unit => write_u8(sink, 5),
    }
}

fn encode_premise<S: ImageSink>(
    sink: &mut S,
    premise: &TheoryImagePremiseFormV1,
) -> Result<(), TheoryImageError> {
    match premise {
        TheoryImagePremiseFormV1::Freshness { variable, target, remainder } => {
            write_u8(sink, 0)?;
            write_u32(sink, variable.0)?;
            write_u32(sink, target.0)?;
            write_bool(sink, *remainder)
        },
        TheoryImagePremiseFormV1::Transition { source, target } => {
            write_u8(sink, 1)?;
            write_u32(sink, source.0)?;
            write_u32(sink, target.0)
        },
        TheoryImagePremiseFormV1::Judgment { judgment, terms } => {
            write_u8(sink, 2)?;
            write_u32(sink, judgment.0)?;
            write_ids(sink, terms, |id| id.0)
        },
        TheoryImagePremiseFormV1::ForAll { collection, parameter, body } => {
            write_u8(sink, 3)?;
            write_u32(sink, collection.0)?;
            write_u32(sink, parameter.0)?;
            write_u32(sink, *body)
        },
        TheoryImagePremiseFormV1::Guard { commitment } => {
            write_u8(sink, 4)?;
            sink.write(commitment)
        },
    }
}

fn source_arena(
    language: &LanguageCoreV1,
    origin: TheoryRuleOriginV1,
) -> Result<&TheoryRuleArenaV1, TheoryImageError> {
    match origin {
        TheoryRuleOriginV1::Equation { source, .. } => language
            .theory
            .equations
            .get(source as usize)
            .map(|rule| &rule.arena)
            .ok_or(TheoryImageError::UnknownReference {
                kind: "equation",
                owner: source,
                target: source,
            }),
        TheoryRuleOriginV1::Rewrite { source } => language
            .theory
            .rewrites
            .get(source as usize)
            .map(|rule| &rule.arena)
            .ok_or(TheoryImageError::UnknownReference {
                kind: "rewrite",
                owner: source,
                target: source,
            }),
    }
}

#[derive(Default)]
struct DecodeTotals {
    sort_references: usize,
    sort_metadata_bytes: usize,
    variables: usize,
    terms: usize,
    term_references: usize,
    premises: usize,
    names: usize,
    literals: usize,
    transitions: usize,
    automaton_states: usize,
    automaton_entries: usize,
    automaton_edges: usize,
    automaton_slot_references: usize,
}

fn decode_constructor(
    reader: &mut ImageReader<'_>,
    source_domain: usize,
) -> Result<TheoryConstructorImageV1, TheoryImageError> {
    let id = TheoryConstructorId(reader.read_u32()?);
    let domain = read_ids_exact(reader, source_domain, TheorySortId, "constructor domain")?;
    let codomain = TheorySortId(reader.read_u32()?);
    let grammar = match reader.read_u8()? {
        0 => None,
        1 => Some(TheoryGrammarConstructorV1 {
            category: crate::CategoryId(reader.read_u32()?),
            constructor: crate::ConstructorId(reader.read_u32()?),
        }),
        tag => return Err(TheoryImageError::InvalidTag(tag)),
    };
    Ok(TheoryConstructorImageV1 { id, domain, codomain, grammar })
}

fn decode_origin(reader: &mut ImageReader<'_>) -> Result<TheoryRuleOriginV1, TheoryImageError> {
    let tag = reader.read_u8()?;
    let source = reader.read_u32()?;
    match tag {
        0 => Ok(TheoryRuleOriginV1::Equation {
            source,
            direction: TheoryRuleDirectionV1::Forward,
        }),
        1 => Ok(TheoryRuleOriginV1::Equation {
            source,
            direction: TheoryRuleDirectionV1::Reverse,
        }),
        2 => Ok(TheoryRuleOriginV1::Rewrite { source }),
        _ => Err(TheoryImageError::InvalidTag(tag)),
    }
}

fn decode_disposition(
    reader: &mut ImageReader<'_>,
) -> Result<TheoryRuleDispositionV1, TheoryImageError> {
    Ok(match reader.read_u8()? {
        0 => TheoryRuleDispositionV1::Executable,
        1 => TheoryRuleDispositionV1::Suppressed(TheoryRuleSuppressionV1::MatchAllRoot),
        2 => TheoryRuleDispositionV1::Suppressed(TheoryRuleSuppressionV1::PremiseDependency {
            variable: TheoryVariableId(reader.read_u32()?),
        }),
        3 => TheoryRuleDispositionV1::Suppressed(TheoryRuleSuppressionV1::UnboundTemplate {
            variable: TheoryVariableId(reader.read_u32()?),
        }),
        tag => return Err(TheoryImageError::InvalidTag(tag)),
    })
}

fn decode_rule(
    reader: &mut ImageReader<'_>,
    id: TheoryRuleProgramId,
    origin: TheoryRuleOriginV1,
    source: &TheoryRuleArenaV1,
    limits: TheoryImageAdmissionLimits,
    totals: &mut DecodeTotals,
) -> Result<TheoryRuleProgramV1, TheoryImageError> {
    let disposition = decode_disposition(reader)?;
    let name = reader.read_string(limits.max_total_name_bytes, "name bytes")?;
    add_limit(&mut totals.names, name.len(), limits.max_total_name_bytes, "name bytes")?;

    let variable_count = reader.read_exact_count(source.variables.len(), "rule variables")?;
    add_limit(
        &mut totals.variables,
        variable_count,
        limits.max_total_rule_variables,
        "rule variables",
    )?;
    let mut variables = empty_vec(variable_count)?;
    for _ in 0..variable_count {
        variables.push(TheoryImageVariableV1 {
            id: TheoryVariableId(reader.read_u32()?),
            sort: TheorySortId(reader.read_u32()?),
            role: decode_variable_role(reader.read_u8()?)?,
        });
    }

    let term_count = reader.read_exact_count(source.terms.len(), "term nodes")?;
    add_limit(&mut totals.terms, term_count, limits.max_total_term_nodes, "term nodes")?;
    let mut terms = empty_vec(term_count)?;
    for _ in 0..term_count {
        terms.push(TheoryImageTermNodeV1 {
            sort: TheorySortId(reader.read_u32()?),
            form: decode_term_form(reader, limits, totals)?,
        });
    }

    let premise_count = reader.read_exact_count(source.premises.len(), "premise nodes")?;
    add_limit(
        &mut totals.premises,
        premise_count,
        limits.max_total_premise_nodes,
        "premise nodes",
    )?;
    let mut premises = empty_vec(premise_count)?;
    for _ in 0..premise_count {
        premises.push(TheoryImagePremiseNodeV1 {
            form: decode_premise(reader, limits, totals)?,
        });
    }
    let premise_roots =
        reader.read_u32_values_exact(source.premise_roots.len(), "premise roots")?;
    let left = TheoryTermId(reader.read_u32()?);
    let right = TheoryTermId(reader.read_u32()?);
    let charge = TheoryWorkChargeV1 {
        pattern_nodes: reader.read_u32()?,
        template_nodes: reader.read_u32()?,
        premise_nodes: reader.read_u32()?,
        variable_slots: reader.read_u32()?,
    };
    Ok(TheoryRuleProgramV1 {
        id,
        origin,
        disposition,
        name,
        variables,
        terms,
        premises,
        premise_roots,
        left,
        right,
        charge,
    })
}

fn decode_term_form(
    reader: &mut ImageReader<'_>,
    limits: TheoryImageAdmissionLimits,
    totals: &mut DecodeTotals,
) -> Result<TheoryImageTermFormV1, TheoryImageError> {
    match reader.read_u8()? {
        0 => Ok(TheoryImageTermFormV1::Slot(TheoryVariableId(reader.read_u32()?))),
        1 => {
            let operator = decode_operator(reader, limits, totals)?;
            let arguments = read_ids_charged(
                reader,
                &mut totals.term_references,
                limits.max_total_term_references,
                TheoryTermId,
                "term references",
            )?;
            let slots = read_ids_charged(
                reader,
                &mut totals.term_references,
                limits.max_total_term_references,
                TheoryVariableId,
                "term references",
            )?;
            let remainder = read_optional_u32(reader)?.map(TheoryVariableId);
            let pathmap_mode = read_pathmap_mode(reader)?;
            Ok(TheoryImageTermFormV1::Apply {
                operator,
                arguments,
                slots,
                remainder,
                pathmap_mode,
            })
        },
        2 => {
            let sources = read_ids_charged(
                reader,
                &mut totals.term_references,
                limits.max_total_term_references,
                TheoryTermId,
                "term references",
            )?;
            let parameters = read_ids_charged(
                reader,
                &mut totals.term_references,
                limits.max_total_term_references,
                TheoryVariableId,
                "term references",
            )?;
            add_limit(
                &mut totals.term_references,
                1,
                limits.max_total_term_references,
                "term references",
            )?;
            let body = TheoryTermId(reader.read_u32()?);
            Ok(TheoryImageTermFormV1::Map { sources, parameters, body })
        },
        tag => Err(TheoryImageError::InvalidTag(tag)),
    }
}

fn decode_operator(
    reader: &mut ImageReader<'_>,
    limits: TheoryImageAdmissionLimits,
    totals: &mut DecodeTotals,
) -> Result<TheoryImageOperatorV1, TheoryImageError> {
    Ok(match reader.read_u8()? {
        0 => TheoryImageOperatorV1::Constructor(TheoryConstructorId(reader.read_u32()?)),
        1 => {
            charge_sort_references(totals, limits, 1)?;
            TheoryImageOperatorV1::Abstraction { sort: TheorySortId(reader.read_u32()?) }
        },
        2 => {
            charge_sort_references(totals, limits, 2)?;
            TheoryImageOperatorV1::Substitution {
                sort: TheorySortId(reader.read_u32()?),
                function: TheorySortId(reader.read_u32()?),
            }
        },
        3 => {
            charge_sort_references(totals, limits, 2)?;
            TheoryImageOperatorV1::Collection {
                sort: TheorySortId(reader.read_u32()?),
                element: TheorySortId(reader.read_u32()?),
                kind: decode_collection_kind(reader.read_u8()?)?,
            }
        },
        4 => {
            charge_sort_references(totals, limits, 1)?;
            TheoryImageOperatorV1::Product { sort: TheorySortId(reader.read_u32()?) }
        },
        5 => {
            charge_sort_references(totals, limits, 1)?;
            TheoryImageOperatorV1::Literal {
                sort: TheorySortId(reader.read_u32()?),
                value: decode_literal(reader, limits, totals)?,
            }
        },
        6 => TheoryImageOperatorV1::Judgment {
            judgment: TheoryJudgmentId(reader.read_u32()?),
        },
        7 => {
            charge_sort_references(totals, limits, 1)?;
            let sort = TheorySortId(reader.read_u32()?);
            let mode = match reader.read_u8()? {
                0 => PathMapModeV1::NeutralEmpty,
                1 => PathMapModeV1::Set,
                2 => PathMapModeV1::Map,
                tag => return Err(TheoryImageError::InvalidTag(tag)),
            };
            TheoryImageOperatorV1::PathMapMode { sort, mode }
        },
        tag => return Err(TheoryImageError::InvalidTag(tag)),
    })
}

fn decode_literal(
    reader: &mut ImageReader<'_>,
    limits: TheoryImageAdmissionLimits,
    totals: &mut DecodeTotals,
) -> Result<TheoryLiteralV1, TheoryImageError> {
    Ok(match reader.read_u8()? {
        0 => {
            let value = reader.read_string(limits.max_total_literal_bytes, "literal bytes")?;
            add_limit(
                &mut totals.literals,
                value.len(),
                limits.max_total_literal_bytes,
                "literal bytes",
            )?;
            TheoryLiteralV1::String(value)
        },
        1 => {
            let value = reader.read_bytes(limits.max_total_literal_bytes, "literal bytes")?;
            add_limit(
                &mut totals.literals,
                value.len(),
                limits.max_total_literal_bytes,
                "literal bytes",
            )?;
            TheoryLiteralV1::Bytes(value)
        },
        2 => TheoryLiteralV1::Integer(i128::from_le_bytes(reader.read_array()?)),
        3 => TheoryLiteralV1::FloatBits(u64::from_le_bytes(reader.read_array()?)),
        4 => TheoryLiteralV1::Boolean(reader.read_bool()?),
        5 => TheoryLiteralV1::Unit,
        tag => return Err(TheoryImageError::InvalidTag(tag)),
    })
}

fn decode_premise(
    reader: &mut ImageReader<'_>,
    limits: TheoryImageAdmissionLimits,
    totals: &mut DecodeTotals,
) -> Result<TheoryImagePremiseFormV1, TheoryImageError> {
    Ok(match reader.read_u8()? {
        0 => TheoryImagePremiseFormV1::Freshness {
            variable: TheoryVariableId(reader.read_u32()?),
            target: TheoryVariableId(reader.read_u32()?),
            remainder: reader.read_bool()?,
        },
        1 => TheoryImagePremiseFormV1::Transition {
            source: TheoryVariableId(reader.read_u32()?),
            target: TheoryVariableId(reader.read_u32()?),
        },
        2 => TheoryImagePremiseFormV1::Judgment {
            judgment: TheoryJudgmentId(reader.read_u32()?),
            terms: read_ids_charged(
                reader,
                &mut totals.term_references,
                limits.max_total_term_references,
                TheoryTermId,
                "term references",
            )?,
        },
        3 => TheoryImagePremiseFormV1::ForAll {
            collection: TheoryVariableId(reader.read_u32()?),
            parameter: TheoryVariableId(reader.read_u32()?),
            body: reader.read_u32()?,
        },
        4 => TheoryImagePremiseFormV1::Guard { commitment: reader.read_array()? },
        tag => return Err(TheoryImageError::InvalidTag(tag)),
    })
}

fn decode_patterns(
    reader: &mut ImageReader<'_>,
    limits: TheoryImageAdmissionLimits,
    totals: &mut DecodeTotals,
) -> Result<TheoryPatternAutomatonV1, TheoryImageError> {
    let states = decode_pattern_states(reader, limits, totals)?;
    let entry_count = reader.read_count(limits.max_automaton_entries, 16, "automaton entries")?;
    add_limit(
        &mut totals.automaton_entries,
        entry_count,
        limits.max_automaton_entries,
        "automaton entries",
    )?;
    let mut entries = empty_vec(entry_count)?;
    for _ in 0..entry_count {
        let id = TheoryPatternEntryId(reader.read_u32()?);
        let rule = TheoryRuleProgramId(reader.read_u32()?);
        let root = TheoryPatternStateId(reader.read_u32()?);
        let slot_variables = read_ids_charged(
            reader,
            &mut totals.automaton_slot_references,
            limits.max_automaton_slot_references,
            TheoryVariableId,
            "entry variables",
        )?;
        entries.push(TheoryPatternEntryV1 { id, rule, root, slot_variables });
    }
    Ok(TheoryPatternAutomatonV1 { states, entries })
}

fn decode_pattern_states(
    reader: &mut ImageReader<'_>,
    limits: TheoryImageAdmissionLimits,
    totals: &mut DecodeTotals,
) -> Result<Vec<TheoryPatternStateV1>, TheoryImageError> {
    let state_count = reader.read_count(limits.max_automaton_states, 10, "automaton states")?;
    add_limit(
        &mut totals.automaton_states,
        state_count,
        limits.max_automaton_states,
        "automaton states",
    )?;
    let mut states = empty_vec(state_count)?;
    for _ in 0..state_count {
        let id = TheoryPatternStateId(reader.read_u32()?);
        let slot_count = reader.read_u32()?;
        let form = match reader.read_u8()? {
            0 => TheoryPatternStateFormV1::Bind,
            1 => {
                let operator = decode_operator(reader, limits, totals)?;
                let count = reader.read_count(limits.max_automaton_edges, 8, "automaton edges")?;
                add_limit(
                    &mut totals.automaton_edges,
                    count,
                    limits.max_automaton_edges,
                    "automaton edges",
                )?;
                let mut arguments = empty_vec(count)?;
                for _ in 0..count {
                    let state = TheoryPatternStateId(reader.read_u32()?);
                    let parent_slots = read_ids_charged(
                        reader,
                        &mut totals.automaton_slot_references,
                        limits.max_automaton_slot_references,
                        |value| value,
                        "parent slots",
                    )?;
                    arguments.push(TheoryPatternInvocationV1 { state, parent_slots });
                }
                TheoryPatternStateFormV1::Apply { operator, arguments }
            },
            tag => return Err(TheoryImageError::InvalidTag(tag)),
        };
        states.push(TheoryPatternStateV1 { id, slot_count, form });
    }
    Ok(states)
}

fn decode_judgment(
    reader: &mut ImageReader<'_>,
    source_arguments: usize,
    source_rules: usize,
) -> Result<TheoryJudgmentImageV1, TheoryImageError> {
    Ok(TheoryJudgmentImageV1 {
        id: TheoryJudgmentId(reader.read_u32()?),
        arguments: read_ids_exact(reader, source_arguments, TheorySortId, "judgment arguments")?,
        decision: decode_judgment_decision(reader.read_u8()?)?,
        rules: read_ids_exact(reader, source_rules, TheoryJudgmentRuleProgramId, "judgment rules")?,
    })
}

fn decode_judgment_rule(
    reader: &mut ImageReader<'_>,
    source: &JudgmentRuleV1,
    limits: TheoryImageAdmissionLimits,
    totals: &mut DecodeTotals,
) -> Result<TheoryJudgmentRuleProgramV1, TheoryImageError> {
    let id = TheoryJudgmentRuleProgramId(reader.read_u32()?);
    let owner = TheoryJudgmentId(reader.read_u32()?);
    let name = reader.read_string(limits.max_total_name_bytes, "name bytes")?;
    add_limit(&mut totals.names, name.len(), limits.max_total_name_bytes, "name bytes")?;

    let variable_count =
        reader.read_exact_count(source.variables.len(), "judgment rule variables")?;
    add_limit(
        &mut totals.variables,
        variable_count,
        limits.max_total_rule_variables,
        "rule variables",
    )?;
    let mut variables = empty_vec(variable_count)?;
    for _ in 0..variable_count {
        variables.push(TheoryImageVariableV1 {
            id: TheoryVariableId(reader.read_u32()?),
            sort: TheorySortId(reader.read_u32()?),
            role: decode_variable_role(reader.read_u8()?)?,
        });
    }

    let term_count = reader.read_exact_count(source.terms.len(), "judgment rule terms")?;
    add_limit(&mut totals.terms, term_count, limits.max_total_term_nodes, "term nodes")?;
    let mut terms = empty_vec(term_count)?;
    for _ in 0..term_count {
        terms.push(TheoryImageTermNodeV1 {
            sort: TheorySortId(reader.read_u32()?),
            form: decode_term_form(reader, limits, totals)?,
        });
    }

    let premise_count = reader.read_exact_count(source.premises.len(), "judgment rule premises")?;
    add_limit(
        &mut totals.premises,
        premise_count,
        limits.max_total_premise_nodes,
        "premise nodes",
    )?;
    let mut premises = empty_vec(premise_count)?;
    for source_atom in &source.premises {
        premises.push(decode_judgment_atom(reader, source_atom.terms.len(), limits, totals)?);
    }
    let conclusion = decode_judgment_atom(reader, source.conclusion.terms.len(), limits, totals)?;
    let charge = decode_work_charge(reader)?;
    Ok(TheoryJudgmentRuleProgramV1 {
        id,
        owner,
        name,
        variables,
        terms,
        premises,
        conclusion,
        charge,
    })
}

fn decode_judgment_atom(
    reader: &mut ImageReader<'_>,
    source_terms: usize,
    limits: TheoryImageAdmissionLimits,
    totals: &mut DecodeTotals,
) -> Result<TheoryImageJudgmentAtomV1, TheoryImageError> {
    let judgment = TheoryJudgmentId(reader.read_u32()?);
    let term_count = reader.read_exact_count(source_terms, "judgment atom terms")?;
    add_limit(
        &mut totals.term_references,
        term_count,
        limits.max_total_term_references,
        "term references",
    )?;
    Ok(TheoryImageJudgmentAtomV1 {
        judgment,
        terms: read_ids_without_count(reader, term_count, TheoryTermId)?,
    })
}

fn decode_work_charge(
    reader: &mut ImageReader<'_>,
) -> Result<TheoryWorkChargeV1, TheoryImageError> {
    Ok(TheoryWorkChargeV1 {
        pattern_nodes: reader.read_u32()?,
        template_nodes: reader.read_u32()?,
        premise_nodes: reader.read_u32()?,
        variable_slots: reader.read_u32()?,
    })
}

fn decode_judgment_patterns(
    reader: &mut ImageReader<'_>,
    limits: TheoryImageAdmissionLimits,
    totals: &mut DecodeTotals,
) -> Result<TheoryJudgmentPatternAutomatonV1, TheoryImageError> {
    let states = decode_pattern_states(reader, limits, totals)?;
    let entry_count =
        reader.read_count(limits.max_automaton_entries, 16, "judgment automaton entries")?;
    add_limit(
        &mut totals.automaton_entries,
        entry_count,
        limits.max_automaton_entries,
        "automaton entries",
    )?;
    let mut entries = empty_vec(entry_count)?;
    for _ in 0..entry_count {
        let id = TheoryPatternEntryId(reader.read_u32()?);
        let rule = TheoryJudgmentRuleProgramId(reader.read_u32()?);
        let root = TheoryPatternStateId(reader.read_u32()?);
        let slot_variables = read_ids_charged(
            reader,
            &mut totals.automaton_slot_references,
            limits.max_automaton_slot_references,
            TheoryVariableId,
            "judgment entry variables",
        )?;
        entries.push(TheoryJudgmentPatternEntryV1 { id, rule, root, slot_variables });
    }
    Ok(TheoryJudgmentPatternAutomatonV1 { states, entries })
}

fn decode_action(
    reader: &mut ImageReader<'_>,
    source_domain: usize,
    limits: TheoryImageAdmissionLimits,
    totals: &mut DecodeTotals,
) -> Result<TheoryActionImageV1, TheoryImageError> {
    let id = TheoryActionId(reader.read_u32()?);
    let domain = read_ids_exact(reader, source_domain, TheorySortId, "action domain")?;
    let codomain = TheorySortId(reader.read_u32()?);
    let transitions = read_ids_charged(
        reader,
        &mut totals.transitions,
        limits.max_total_action_transitions,
        TheoryRuleProgramId,
        "action transitions",
    )?;
    Ok(TheoryActionImageV1 {
        id,
        domain,
        codomain,
        transitions,
        effect: TheoryEffectId(reader.read_u32()?),
        effect_class: decode_effect_class(reader.read_u8()?)?,
        required_rights: decode_rights(reader.read_u16()?)?,
        grade: TheorySortId(reader.read_u32()?),
    })
}

fn encode_variable_role(role: TheoryVariableRoleV1) -> u8 {
    match role {
        TheoryVariableRoleV1::Input => 0,
        TheoryVariableRoleV1::Derived => 1,
        TheoryVariableRoleV1::Binder => 2,
        TheoryVariableRoleV1::Remainder => 3,
        TheoryVariableRoleV1::Quantified => 4,
    }
}

fn decode_variable_role(tag: u8) -> Result<TheoryVariableRoleV1, TheoryImageError> {
    Ok(match tag {
        0 => TheoryVariableRoleV1::Input,
        1 => TheoryVariableRoleV1::Derived,
        2 => TheoryVariableRoleV1::Binder,
        3 => TheoryVariableRoleV1::Remainder,
        4 => TheoryVariableRoleV1::Quantified,
        _ => return Err(TheoryImageError::InvalidTag(tag)),
    })
}

fn encode_collection_kind(kind: CollectionKind) -> u8 {
    match kind {
        CollectionKind::Bag => 0,
        CollectionKind::Set => 1,
        CollectionKind::List => 2,
        CollectionKind::Map => 3,
        CollectionKind::PathMap => 4,
    }
}

fn decode_collection_kind(tag: u8) -> Result<CollectionKind, TheoryImageError> {
    Ok(match tag {
        0 => CollectionKind::Bag,
        1 => CollectionKind::Set,
        2 => CollectionKind::List,
        3 => CollectionKind::Map,
        4 => CollectionKind::PathMap,
        _ => return Err(TheoryImageError::InvalidTag(tag)),
    })
}

fn write_pathmap_mode<S: ImageSink>(
    sink: &mut S,
    mode: Option<PathMapModeV1>,
) -> Result<(), TheoryImageError> {
    write_u8(
        sink,
        match mode {
            None => 0,
            Some(PathMapModeV1::NeutralEmpty) => 1,
            Some(PathMapModeV1::Set) => 2,
            Some(PathMapModeV1::Map) => 3,
        },
    )
}

fn read_pathmap_mode(
    reader: &mut ImageReader<'_>,
) -> Result<Option<PathMapModeV1>, TheoryImageError> {
    Ok(match reader.read_u8()? {
        0 => None,
        1 => Some(PathMapModeV1::NeutralEmpty),
        2 => Some(PathMapModeV1::Set),
        3 => Some(PathMapModeV1::Map),
        tag => return Err(TheoryImageError::InvalidTag(tag)),
    })
}

fn encode_effect_class(effect: SemanticEffectClassV1) -> u8 {
    match effect {
        SemanticEffectClassV1::Pure => 0,
        SemanticEffectClassV1::Structural => 1,
        SemanticEffectClassV1::Behavioral => 2,
        SemanticEffectClassV1::Resource => 3,
        SemanticEffectClassV1::External => 4,
    }
}

fn decode_effect_class(tag: u8) -> Result<SemanticEffectClassV1, TheoryImageError> {
    Ok(match tag {
        0 => SemanticEffectClassV1::Pure,
        1 => SemanticEffectClassV1::Structural,
        2 => SemanticEffectClassV1::Behavioral,
        3 => SemanticEffectClassV1::Resource,
        4 => SemanticEffectClassV1::External,
        _ => return Err(TheoryImageError::InvalidTag(tag)),
    })
}

fn right_index(right: LanguageRight) -> u16 {
    match right {
        LanguageRight::Parse => 0,
        LanguageRight::Construct => 1,
        LanguageRight::Match => 2,
        LanguageRight::Observe => 3,
        LanguageRight::ReflectAst => 4,
        LanguageRight::Reduce => 5,
        LanguageRight::Bridge => 6,
        LanguageRight::Publish => 7,
        LanguageRight::Introspect => 8,
        LanguageRight::Check => 9,
        LanguageRight::SearchProof => 10,
        LanguageRight::Spend => 11,
    }
}

fn right_from_index(index: u16) -> Option<LanguageRight> {
    Some(match index {
        0 => LanguageRight::Parse,
        1 => LanguageRight::Construct,
        2 => LanguageRight::Match,
        3 => LanguageRight::Observe,
        4 => LanguageRight::ReflectAst,
        5 => LanguageRight::Reduce,
        6 => LanguageRight::Bridge,
        7 => LanguageRight::Publish,
        8 => LanguageRight::Introspect,
        9 => LanguageRight::Check,
        10 => LanguageRight::SearchProof,
        11 => LanguageRight::Spend,
        _ => return None,
    })
}

fn encode_rights(rights: &LanguageRights) -> u16 {
    rights
        .iter()
        .fold(0u16, |mask, right| mask | (1u16 << right_index(right)))
}

fn decode_rights(mask: u16) -> Result<LanguageRights, TheoryImageError> {
    if mask >> RIGHT_COUNT != 0 {
        return Err(TheoryImageError::InvalidTag(u8::MAX));
    }
    Ok(LanguageRights::from_rights((0..RIGHT_COUNT).filter_map(|index| {
        (mask & (1u16 << index) != 0)
            .then(|| right_from_index(index))
            .flatten()
    })))
}

fn write_u8<S: ImageSink>(sink: &mut S, value: u8) -> Result<(), TheoryImageError> {
    sink.write(&[value])
}

fn write_bool<S: ImageSink>(sink: &mut S, value: bool) -> Result<(), TheoryImageError> {
    write_u8(sink, u8::from(value))
}

fn write_u16<S: ImageSink>(sink: &mut S, value: u16) -> Result<(), TheoryImageError> {
    sink.write(&value.to_le_bytes())
}

fn write_u32<S: ImageSink>(sink: &mut S, value: u32) -> Result<(), TheoryImageError> {
    sink.write(&value.to_le_bytes())
}

fn write_count<S: ImageSink>(sink: &mut S, value: usize) -> Result<(), TheoryImageError> {
    write_u32(sink, u32::try_from(value).map_err(|_| TheoryImageError::LengthOverflow)?)
}

fn write_string<S: ImageSink>(sink: &mut S, value: &str) -> Result<(), TheoryImageError> {
    write_bytes(sink, value.as_bytes())
}

fn write_bytes<S: ImageSink>(sink: &mut S, value: &[u8]) -> Result<(), TheoryImageError> {
    write_count(sink, value.len())?;
    sink.write(value)
}

fn write_optional_u32<S: ImageSink>(
    sink: &mut S,
    value: Option<u32>,
) -> Result<(), TheoryImageError> {
    match value {
        None => write_u8(sink, 0),
        Some(value) => {
            write_u8(sink, 1)?;
            write_u32(sink, value)
        },
    }
}

fn write_ids<S: ImageSink, T>(
    sink: &mut S,
    values: &[T],
    id: impl Fn(&T) -> u32,
) -> Result<(), TheoryImageError> {
    write_count(sink, values.len())?;
    for value in values {
        write_u32(sink, id(value))?;
    }
    Ok(())
}

fn write_u32_values<S: ImageSink>(sink: &mut S, values: &[u32]) -> Result<(), TheoryImageError> {
    write_ids(sink, values, |value| *value)
}

fn add_limit(
    total: &mut usize,
    additional: usize,
    limit: usize,
    kind: &'static str,
) -> Result<(), TheoryImageError> {
    *total = total
        .checked_add(additional)
        .ok_or(TheoryImageError::LengthOverflow)?;
    enforce(*total, limit, kind)
}

fn enforce(actual: usize, limit: usize, kind: &'static str) -> Result<(), TheoryImageError> {
    if actual > limit {
        return Err(TheoryImageError::LimitExceeded(kind));
    }
    Ok(())
}

fn empty_vec<T>(capacity: usize) -> Result<Vec<T>, TheoryImageError> {
    let mut values = Vec::new();
    values
        .try_reserve_exact(capacity)
        .map_err(|_| TheoryImageError::Allocation)?;
    Ok(values)
}

fn read_ids_charged<T>(
    reader: &mut ImageReader<'_>,
    total: &mut usize,
    limit: usize,
    wrap: fn(u32) -> T,
    kind: &'static str,
) -> Result<Vec<T>, TheoryImageError> {
    let count = reader.read_count(limit, 4, kind)?;
    add_limit(total, count, limit, kind)?;
    let mut values = empty_vec(count)?;
    for _ in 0..count {
        values.push(wrap(reader.read_u32()?));
    }
    Ok(values)
}

fn read_ids_exact<T>(
    reader: &mut ImageReader<'_>,
    expected: usize,
    wrap: fn(u32) -> T,
    kind: &'static str,
) -> Result<Vec<T>, TheoryImageError> {
    let count = reader.read_exact_count(expected, kind)?;
    reader.require_width(count, 4)?;
    let mut values = empty_vec(count)?;
    for _ in 0..count {
        values.push(wrap(reader.read_u32()?));
    }
    Ok(values)
}

fn read_ids_without_count<T>(
    reader: &mut ImageReader<'_>,
    count: usize,
    wrap: fn(u32) -> T,
) -> Result<Vec<T>, TheoryImageError> {
    reader.require_width(count, 4)?;
    let mut values = empty_vec(count)?;
    for _ in 0..count {
        values.push(wrap(reader.read_u32()?));
    }
    Ok(values)
}

fn read_optional_u32(reader: &mut ImageReader<'_>) -> Result<Option<u32>, TheoryImageError> {
    match reader.read_u8()? {
        0 => Ok(None),
        1 => Ok(Some(reader.read_u32()?)),
        tag => Err(TheoryImageError::InvalidTag(tag)),
    }
}

struct ImageReader<'a> {
    bytes: &'a [u8],
    cursor: usize,
}

impl<'a> ImageReader<'a> {
    fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, cursor: 0 }
    }

    fn is_empty(&self) -> bool {
        self.cursor == self.bytes.len()
    }

    fn remaining(&self) -> usize {
        self.bytes.len().saturating_sub(self.cursor)
    }

    fn require_width(&self, count: usize, width: usize) -> Result<(), TheoryImageError> {
        let required = count
            .checked_mul(width)
            .ok_or(TheoryImageError::LengthOverflow)?;
        if required > self.remaining() {
            return Err(TheoryImageError::Truncated);
        }
        Ok(())
    }

    fn read_exact(&mut self, length: usize) -> Result<&'a [u8], TheoryImageError> {
        let end = self
            .cursor
            .checked_add(length)
            .ok_or(TheoryImageError::LengthOverflow)?;
        let value = self
            .bytes
            .get(self.cursor..end)
            .ok_or(TheoryImageError::Truncated)?;
        self.cursor = end;
        Ok(value)
    }

    fn read_array<const N: usize>(&mut self) -> Result<[u8; N], TheoryImageError> {
        self.read_exact(N)?
            .try_into()
            .map_err(|_| TheoryImageError::Truncated)
    }

    fn read_u8(&mut self) -> Result<u8, TheoryImageError> {
        Ok(self.read_exact(1)?[0])
    }

    fn read_bool(&mut self) -> Result<bool, TheoryImageError> {
        match self.read_u8()? {
            0 => Ok(false),
            1 => Ok(true),
            tag => Err(TheoryImageError::InvalidTag(tag)),
        }
    }

    fn read_u16(&mut self) -> Result<u16, TheoryImageError> {
        Ok(u16::from_le_bytes(self.read_array()?))
    }

    fn read_u32(&mut self) -> Result<u32, TheoryImageError> {
        Ok(u32::from_le_bytes(self.read_array()?))
    }

    fn read_count(
        &mut self,
        limit: usize,
        minimum_width: usize,
        kind: &'static str,
    ) -> Result<usize, TheoryImageError> {
        let count =
            usize::try_from(self.read_u32()?).map_err(|_| TheoryImageError::LengthOverflow)?;
        enforce(count, limit, kind)?;
        self.require_width(count, minimum_width)?;
        Ok(count)
    }

    fn read_exact_count(
        &mut self,
        expected: usize,
        kind: &'static str,
    ) -> Result<usize, TheoryImageError> {
        let count =
            usize::try_from(self.read_u32()?).map_err(|_| TheoryImageError::LengthOverflow)?;
        if count != expected {
            return Err(TheoryImageError::SourceMismatch { kind, index: u32::MAX });
        }
        Ok(count)
    }

    fn read_bytes(
        &mut self,
        limit: usize,
        kind: &'static str,
    ) -> Result<Vec<u8>, TheoryImageError> {
        let count = self.read_count(limit, 1, kind)?;
        let source = self.read_exact(count)?;
        let mut value = empty_vec(count)?;
        value.extend_from_slice(source);
        Ok(value)
    }

    fn read_string(
        &mut self,
        limit: usize,
        kind: &'static str,
    ) -> Result<String, TheoryImageError> {
        let bytes = self.read_bytes(limit, kind)?;
        String::from_utf8(bytes).map_err(|_| TheoryImageError::InvalidUtf8)
    }

    fn read_u32_values_exact(
        &mut self,
        expected: usize,
        kind: &'static str,
    ) -> Result<Vec<u32>, TheoryImageError> {
        read_ids_exact(self, expected, |value| value, kind)
    }
}
