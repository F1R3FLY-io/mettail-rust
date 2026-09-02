//! Lossless structural `LanguageCoreV1` values for the canonical `language/3`
//! schema.
//!
//! This is the exact, programmatic normal form used by migration and bootstrap
//! tooling. It is ordinary map/list/scalar Rholang data: no source text is
//! rendered or parsed, and no binary blob hides the grammar from analysis.
//! `language/2` remains the backward-compatible authoring presentation.

use crate::canonical::{RhoValue, ValueDecodeError};
use mettail_grammar_core as core;
use serde_json::{Map as JsonMap, Number as JsonNumber, Value as JsonValue};
use std::collections::BTreeMap;

/// ABI of the structural payload stored under `language/3`'s `core` key.
pub const LANGUAGE_CORE_VALUE_SCHEMA_V1: &str = "mettail-language-core-value/1";

/// Serde's tagged structural encoding introduces a small fixed amount of
/// framing around each semantic node. Four times the admitted DDL depth is a
/// closed upper bound for all GrammarCore and CanonicalValue variants.
const MAX_LANGUAGE_CORE_VALUE_DEPTH: usize = crate::parse::MAX_DDL_STRUCTURAL_DEPTH * 4;

const ENVELOPE_KEYS: &[&str] = &["core", "core_schema", "mettail", "name"];
const DATA_FRAGMENT_KEYS: &[&str] = &["core", "core_schema"];

/// Encode a validated complete language artifact as closed ordinary-Rholang
/// data. The duplicate envelope name is a checked commitment, not an alias.
pub fn language_core_to_value(
    language: &core::LanguageCoreV1,
) -> Result<RhoValue, ValueDecodeError> {
    let encoded = encode_core(language)?;
    let value = RhoValue::Map(BTreeMap::from([
        ("core".into(), encoded),
        ("core_schema".into(), RhoValue::String(LANGUAGE_CORE_VALUE_SCHEMA_V1.into())),
        ("mettail".into(), RhoValue::String("language/3".into())),
        ("name".into(), RhoValue::String(language.grammar.name.clone())),
    ]));
    admit_language_core_value(&value)?;
    Ok(value)
}

/// Encode a completed language as the closed, headerless payload accepted by
/// Greg/Mike `Data(v)`.  The surrounding `Theory` supplies and checks the
/// language name; no identity field is duplicated inside the fragment.
pub fn language_core_to_data_fragment(
    language: &core::LanguageCoreV1,
) -> Result<RhoValue, ValueDecodeError> {
    let fragment = RhoValue::Map(BTreeMap::from([
        ("core".into(), encode_core(language)?),
        ("core_schema".into(), RhoValue::String(LANGUAGE_CORE_VALUE_SCHEMA_V1.into())),
    ]));
    let decoded = decode_language_core_data_fragment(&fragment)?.ok_or_else(|| {
        ValueDecodeError::new("Data", "exact LanguageCore fragment was not recognized")
    })?;
    if &decoded != language {
        return Err(ValueDecodeError::new(
            "Data.core",
            "exact LanguageCore fragment changed during canonical validation",
        ));
    }
    Ok(fragment)
}

fn encode_core(language: &core::LanguageCoreV1) -> Result<RhoValue, ValueDecodeError> {
    language.validate().map_err(|errors| {
        ValueDecodeError::new("$.core", format!("invalid LanguageCore: {errors:?}"))
    })?;
    let json = serde_json::to_value(language).map_err(|error| {
        ValueDecodeError::new("$.core", format!("cannot encode LanguageCore: {error}"))
    })?;
    json_to_rho(json)
}

pub(crate) fn is_language_core_value(value: &RhoValue) -> bool {
    matches!(value, RhoValue::Map(envelope) if envelope.contains_key("core"))
}

/// Decode the exact structural arm when the `core` key is present. `None`
/// means that the caller should use the presentation decoder. A structural arm
/// is closed and cannot be mixed with presentation or composition keys.
pub(crate) fn decode_language_core_value(
    value: &RhoValue,
) -> Result<Option<core::LanguageCoreV1>, ValueDecodeError> {
    let RhoValue::Map(envelope) = value else {
        return Ok(None);
    };
    if !envelope.contains_key("core") {
        return Ok(None);
    }
    admit_language_core_value(value)?;
    if let Some(key) = envelope
        .keys()
        .find(|key| !ENVELOPE_KEYS.contains(&key.as_str()))
    {
        return Err(ValueDecodeError::new(
            format!("$.{key}"),
            "the structural language/3 core arm is closed and cannot be mixed with presentation fields",
        ));
    }
    for key in ENVELOPE_KEYS {
        if !envelope.contains_key(*key) {
            return Err(ValueDecodeError::new(format!("$.{key}"), "missing required key"));
        }
    }
    require_string(envelope, "mettail", "language/3")?;
    require_string(envelope, "core_schema", LANGUAGE_CORE_VALUE_SCHEMA_V1)?;
    let name = match &envelope["name"] {
        RhoValue::String(name) if !name.is_empty() => name,
        _ => return Err(ValueDecodeError::new("$.name", "expected a non-empty string")),
    };
    let core_value = &envelope["core"];
    let json = rho_to_json(core_value)?;
    let language: core::LanguageCoreV1 = serde_json::from_value(json).map_err(|error| {
        ValueDecodeError::new("$.core", format!("invalid structural LanguageCore: {error}"))
    })?;
    language.validate().map_err(|errors| {
        ValueDecodeError::new("$.core", format!("invalid LanguageCore: {errors:?}"))
    })?;
    if name != &language.grammar.name {
        return Err(ValueDecodeError::new(
            "$.name",
            format!(
                "envelope name `{name}` does not match GrammarCore name `{}`",
                language.grammar.name
            ),
        ));
    }

    // Re-encoding is the closed-schema gate for the derived Serde record. It
    // rejects unknown members, alternate byte spellings, and other values that
    // a permissive typed decoder might otherwise ignore.
    let canonical_json = serde_json::to_value(&language).map_err(|error| {
        ValueDecodeError::new("$.core", format!("cannot re-encode LanguageCore: {error}"))
    })?;
    let canonical = json_to_rho(canonical_json)?;
    if &canonical != core_value {
        return Err(ValueDecodeError::new(
            "$.core",
            "structural LanguageCore is not in its closed canonical form",
        ));
    }
    Ok(Some(language))
}

/// Decode the exact-core arm of a `Data(v)` builder. `None` means the value is
/// an ordinary partial presentation. Once `core` appears, the fragment is
/// closed: it contains exactly `core_schema` and `core`.
pub fn decode_language_core_data_fragment(
    value: &RhoValue,
) -> Result<Option<core::LanguageCoreV1>, ValueDecodeError> {
    let RhoValue::Map(fragment) = value else {
        return Ok(None);
    };
    if !fragment.contains_key("core") {
        return Ok(None);
    }
    if let Some(key) = fragment
        .keys()
        .find(|key| !DATA_FRAGMENT_KEYS.contains(&key.as_str()))
    {
        return Err(ValueDecodeError::new(
            format!("Data.{key}"),
            "the exact LanguageCore Data fragment is closed and cannot be mixed with presentation fields",
        ));
    }
    for key in DATA_FRAGMENT_KEYS {
        if !fragment.contains_key(*key) {
            return Err(ValueDecodeError::new(format!("Data.{key}"), "missing required key"));
        }
    }
    require_string(fragment, "core_schema", LANGUAGE_CORE_VALUE_SCHEMA_V1)?;
    let json = rho_to_json(&fragment["core"])?;
    let language: core::LanguageCoreV1 = serde_json::from_value(json).map_err(|error| {
        ValueDecodeError::new("Data.core", format!("invalid structural LanguageCore: {error}"))
    })?;
    language.validate().map_err(|errors| {
        ValueDecodeError::new("Data.core", format!("invalid LanguageCore: {errors:?}"))
    })?;
    let canonical = encode_core(&language)?;
    if canonical != fragment["core"] {
        return Err(ValueDecodeError::new(
            "Data.core",
            "structural LanguageCore is not in its closed canonical form",
        ));
    }
    Ok(Some(language))
}

fn admit_language_core_value(value: &RhoValue) -> Result<(), ValueDecodeError> {
    crate::canonical::admit_canonical_value_resources(value)?;
    let mut work = vec![(value, 1usize)];
    while let Some((value, depth)) = work.pop() {
        if depth > MAX_LANGUAGE_CORE_VALUE_DEPTH {
            return Err(ValueDecodeError::new(
                "$.core",
                format!("structural LanguageCore nesting exceeds {MAX_LANGUAGE_CORE_VALUE_DEPTH}"),
            ));
        }
        let child_depth = depth.checked_add(1).ok_or_else(|| {
            ValueDecodeError::new("$.core", "structural LanguageCore depth overflowed")
        })?;
        match value {
            RhoValue::Map(values) => {
                work.extend(values.values().rev().map(|value| (value, child_depth)));
            },
            RhoValue::List(values) => {
                work.extend(values.iter().rev().map(|value| (value, child_depth)));
            },
            RhoValue::String(_)
            | RhoValue::Bytes(_)
            | RhoValue::Integer(_)
            | RhoValue::FloatBits(_)
            | RhoValue::Boolean(_)
            | RhoValue::Nil => {},
        }
    }
    Ok(())
}

fn require_string(
    envelope: &BTreeMap<String, RhoValue>,
    key: &str,
    expected: &str,
) -> Result<(), ValueDecodeError> {
    match &envelope[key] {
        RhoValue::String(actual) if actual == expected => Ok(()),
        RhoValue::String(actual) => Err(ValueDecodeError::new(
            format!("$.{key}"),
            format!("expected `{expected}`, found `{actual}`"),
        )),
        _ => Err(ValueDecodeError::new(format!("$.{key}"), "expected a string")),
    }
}

/// Iterative JSON-value to Rholang-value conversion. `serde_json::Value` is
/// only an in-memory typed Serde data model here; no JSON text is produced.
fn json_to_rho(root: JsonValue) -> Result<RhoValue, ValueDecodeError> {
    enum Job {
        Visit(JsonValue),
        FinishList(usize),
        FinishMap(Vec<String>),
    }

    let mut jobs = vec![Job::Visit(root)];
    let mut values = Vec::new();
    while let Some(job) = jobs.pop() {
        match job {
            Job::Visit(JsonValue::Null) => values.push(RhoValue::Nil),
            Job::Visit(JsonValue::Bool(value)) => values.push(RhoValue::Boolean(value)),
            Job::Visit(JsonValue::String(value)) => values.push(RhoValue::String(value)),
            Job::Visit(JsonValue::Number(value)) => {
                if let Some(value) = value.as_i128() {
                    values.push(RhoValue::Integer(value));
                } else if let Some(value) = value.as_u128() {
                    let value = i128::try_from(value).map_err(|_| {
                        ValueDecodeError::new("$.core", "unsigned integer exceeds i128")
                    })?;
                    values.push(RhoValue::Integer(value));
                } else {
                    let value = value
                        .as_f64()
                        .filter(|value| value.is_finite())
                        .ok_or_else(|| {
                            ValueDecodeError::new("$.core", "non-finite or invalid numeric value")
                        })?;
                    values.push(RhoValue::FloatBits(value.to_bits()));
                }
            },
            Job::Visit(JsonValue::Array(items)) => {
                let length = items.len();
                jobs.push(Job::FinishList(length));
                jobs.extend(items.into_iter().rev().map(Job::Visit));
            },
            Job::Visit(JsonValue::Object(entries)) => {
                let entries: Vec<_> = entries.into_iter().collect();
                let keys = entries.iter().map(|(key, _)| key.clone()).collect();
                jobs.push(Job::FinishMap(keys));
                jobs.extend(
                    entries
                        .into_iter()
                        .rev()
                        .map(|(_, value)| Job::Visit(value)),
                );
            },
            Job::FinishList(length) => {
                let start = values.len().checked_sub(length).ok_or_else(|| {
                    ValueDecodeError::new("$.core", "structural codec value-stack underflow")
                })?;
                let children = values.drain(start..).collect();
                values.push(RhoValue::List(children));
            },
            Job::FinishMap(keys) => {
                let start = values.len().checked_sub(keys.len()).ok_or_else(|| {
                    ValueDecodeError::new("$.core", "structural codec map-stack underflow")
                })?;
                let children: Vec<_> = values.drain(start..).collect();
                values.push(RhoValue::Map(keys.into_iter().zip(children).collect()));
            },
        }
    }
    if values.len() != 1 {
        return Err(ValueDecodeError::new(
            "$.core",
            "structural codec did not produce exactly one value",
        ));
    }
    Ok(values.pop().expect("length checked"))
}

/// Iterative Rholang-value to JSON-value conversion. A native byte vector is
/// accepted as a sequence for diagnostics, but the re-encoding equality gate
/// rejects it because the canonical Serde form is an integer list.
fn rho_to_json(root: &RhoValue) -> Result<JsonValue, ValueDecodeError> {
    enum Job<'a> {
        Visit(&'a RhoValue),
        FinishList(usize),
        FinishMap(Vec<&'a str>),
    }

    let mut jobs = vec![Job::Visit(root)];
    let mut values = Vec::new();
    while let Some(job) = jobs.pop() {
        match job {
            Job::Visit(RhoValue::Nil) => values.push(JsonValue::Null),
            Job::Visit(RhoValue::Boolean(value)) => values.push(JsonValue::Bool(*value)),
            Job::Visit(RhoValue::String(value)) => values.push(JsonValue::String(value.clone())),
            Job::Visit(RhoValue::Integer(value)) => {
                let number = JsonNumber::from_i128(*value).ok_or_else(|| {
                    ValueDecodeError::new(
                        "$.core",
                        "integer is not representable by the core codec",
                    )
                })?;
                values.push(JsonValue::Number(number));
            },
            Job::Visit(RhoValue::FloatBits(bits)) => {
                let value = f64::from_bits(*bits);
                let number = JsonNumber::from_f64(value).ok_or_else(|| {
                    ValueDecodeError::new("$.core", "non-finite float is not admitted")
                })?;
                values.push(JsonValue::Number(number));
            },
            Job::Visit(RhoValue::Bytes(bytes)) => {
                values.push(JsonValue::Array(
                    bytes
                        .iter()
                        .map(|value| JsonValue::Number(JsonNumber::from(*value)))
                        .collect(),
                ));
            },
            Job::Visit(RhoValue::List(items)) => {
                jobs.push(Job::FinishList(items.len()));
                jobs.extend(items.iter().rev().map(Job::Visit));
            },
            Job::Visit(RhoValue::Map(entries)) => {
                let keys: Vec<_> = entries.keys().map(String::as_str).collect();
                jobs.push(Job::FinishMap(keys));
                jobs.extend(entries.values().rev().map(Job::Visit));
            },
            Job::FinishList(length) => {
                let start = values.len().checked_sub(length).ok_or_else(|| {
                    ValueDecodeError::new("$.core", "structural decoder value-stack underflow")
                })?;
                let children = values.drain(start..).collect();
                values.push(JsonValue::Array(children));
            },
            Job::FinishMap(keys) => {
                let start = values.len().checked_sub(keys.len()).ok_or_else(|| {
                    ValueDecodeError::new("$.core", "structural decoder map-stack underflow")
                })?;
                let children: Vec<_> = values.drain(start..).collect();
                let mut map = JsonMap::new();
                for (key, value) in keys.into_iter().zip(children) {
                    map.insert(key.to_string(), value);
                }
                values.push(JsonValue::Object(map));
            },
        }
    }
    if values.len() != 1 {
        return Err(ValueDecodeError::new(
            "$.core",
            "structural decoder did not produce exactly one value",
        ));
    }
    Ok(values.pop().expect("length checked"))
}

#[cfg(test)]
mod tests {
    use super::*;
    use mettail_grammar_core::{
        Associativity, BeamWidth, BuiltinToken, Capability, Category, CategoryId, ConstructorId,
        FieldSource, GrammarCoreV1, KeywordReservation, LexerMode, ModeId, ModeTransition,
        ParserConfiguration, Precedence, Production, ProductionClass, ProductionId, Provenance,
        ReductionPlan, Reservation, SourceProvenance, SyncConstraint, TokenDecoder,
        TokenDefinition, TokenId, TokenPattern, TreeInvariant,
    };
    use std::collections::{BTreeMap, BTreeSet};

    fn comprehensive_language() -> core::LanguageCoreV1 {
        let mut grammar = GrammarCoreV1::new("RoundTrip");
        grammar.canonical_specification = Some(core::CanonicalValue::Map(BTreeMap::from([
            ("wide".into(), core::CanonicalValue::Integer(i128::MAX)),
            ("bits".into(), core::CanonicalValue::FloatBits(u64::MAX)),
        ])));
        grammar.backend_context = Some("diagnostic context".into());
        grammar.documentation = Some("documentation".into());
        grammar.categories = vec![Category {
            id: CategoryId(0),
            name: "Term".into(),
            carrier: core::Carrier::Dynamic,
            primary: true,
            admits_variables: false,
        }];
        grammar.tokens = vec![
            TokenDefinition {
                id: TokenId(0),
                name: "Identifier".into(),
                pattern: TokenPattern::Builtin(BuiltinToken::Identifier),
                category: None,
                evaluation: None,
                priority: -2,
                mode: ModeId(0),
                channel: "main".into(),
                transition: ModeTransition::default(),
                decoder: TokenDecoder::Text,
                reservation: Reservation::None,
            },
            TokenDefinition {
                id: TokenId(1),
                name: "open".into(),
                pattern: TokenPattern::Literal("(".into()),
                category: None,
                evaluation: None,
                priority: 3,
                mode: ModeId(0),
                channel: "layout".into(),
                transition: ModeTransition { push: Some(ModeId(1)), pop: false },
                decoder: TokenDecoder::Unit,
                reservation: Reservation::Contextual,
            },
            TokenDefinition {
                id: TokenId(2),
                name: "body".into(),
                pattern: TokenPattern::Regex("[^)]+".into()),
                category: None,
                evaluation: None,
                priority: 1,
                mode: ModeId(1),
                channel: "body".into(),
                transition: ModeTransition { push: None, pop: true },
                decoder: TokenDecoder::Capability("urn:decoder:body/1".into()),
                reservation: Reservation::Reserved,
            },
        ];
        grammar.modes = vec![
            LexerMode {
                id: ModeId(0),
                name: "default".into(),
                token_ids: vec![TokenId(0), TokenId(1)],
                raw: false,
            },
            LexerMode {
                id: ModeId(1),
                name: "body".into(),
                token_ids: vec![TokenId(2)],
                raw: true,
            },
        ];
        grammar.productions = vec![Production {
            id: ProductionId(0),
            constructor: ConstructorId(0),
            label: "PBody".into(),
            result: CategoryId(0),
            syntax: vec![
                core::SyntaxItem::Token(TokenId(1)),
                core::SyntaxItem::CaptureToken { token: TokenId(2), slot: "text".into() },
            ],
            precedence: Precedence {
                binding_power: Some(41),
                associativity: Associativity::Right,
                shares_previous_level: true,
            },
            classification: ProductionClass {
                prefix: true,
                generated: true,
                ..ProductionClass::default()
            },
            reduction: 0,
            provenance: Some(SourceProvenance {
                uri: Some("rho:test".into()),
                line: 7,
                column: 9,
            }),
        }];
        grammar.reductions = vec![ReductionPlan {
            output_category: CategoryId(0),
            constructor: ConstructorId(0),
            input_arity: 1,
            fields: vec![FieldSource::Text(0), FieldSource::Unit, FieldSource::EmptySequence],
            evaluation: Some(core::NativeEvaluation::Handler("urn:handler:test/1".into())),
            evaluation_mode: Some(core::EvaluationMode::Step),
            tier: Some(core::TierDirective {
                tier: core::EvaluationTier::T3,
                bound: Some(17),
                force: true,
            }),
        }];
        grammar.semantic_dependencies = vec![vec![ConstructorId(0)]];
        grammar.semantic_program.target = vec!["Neutral".into(), "V1".into()];
        grammar.semantic_program.equations = vec![core::CanonicalValue::String("eq".into())];
        grammar.parser_configuration = ParserConfiguration {
            beam_width: BeamWidth::Auto,
            log_semiring_model_path: Some("model/commitment".into()),
            recovery: core::RecoveryConfiguration {
                vpa_nesting_ceiling: Some(77),
                ..core::RecoveryConfiguration::default()
            },
            reservation: KeywordReservation::Auto {
                contextual: BTreeSet::from(["local".into()]),
            },
        };
        grammar.synchronization = vec![SyncConstraint::Track {
            auxiliary: "layout".into(),
            primary: "main".into(),
        }];
        grammar.tree_invariants = vec![TreeInvariant {
            name: "balanced".into(),
            formula: core::CanonicalValue::Boolean(true),
        }];
        grammar.capabilities = BTreeSet::from([
            Capability::TokenDecoder("urn:decoder:body/1".into()),
            Capability::NativeEvaluator("urn:handler:test/1".into()),
        ]);
        grammar.requested_rights = core::LanguageRights::all();
        grammar.provenance = Provenance {
            source_uri: Some("rho:test".into()),
            source_hash: Some([0xA5; 32]),
            frontend: "test".into(),
            attributes: BTreeMap::from([("commitment".into(), "exact".into())]),
        };
        grammar.weight_profile = core::WeightProfile::LocalLog {
            beam_width: Some(4.5),
            model_fingerprint: Some([0x5A; 32]),
        };
        grammar
            .capabilities
            .insert(Capability::NativeEvaluator("urn:handler:test/1".into()));
        let language = core::LanguageCoreV1::structural(grammar);
        language.validate().expect("fixture is valid");
        language
    }

    #[test]
    fn structural_language_core_round_trip_preserves_every_field() {
        let expected = comprehensive_language();
        let value = language_core_to_value(&expected).expect("encoding succeeds");
        let actual = crate::canonical::value_to_language_core(&value)
            .expect("public canonical entrypoint decodes the core arm");
        assert_eq!(actual, expected);
        assert_eq!(actual.grammar.fingerprint().unwrap(), expected.grammar.fingerprint().unwrap());
        assert_eq!(actual.fingerprint().unwrap(), expected.fingerprint().unwrap());
    }

    #[test]
    fn exact_data_fragment_round_trip_preserves_every_field_without_identity_headers() {
        let expected = comprehensive_language();
        let fragment = language_core_to_data_fragment(&expected).expect("encoding succeeds");
        let RhoValue::Map(fields) = &fragment else {
            panic!("exact Data fragment is a map")
        };
        assert_eq!(
            fields.keys().map(String::as_str).collect::<Vec<_>>(),
            vec!["core", "core_schema"]
        );
        let actual = decode_language_core_data_fragment(&fragment)
            .expect("fragment is valid")
            .expect("fragment is exact");
        assert_eq!(actual, expected);
    }

    #[test]
    fn exact_data_fragment_is_closed() {
        let mut fragment = language_core_to_data_fragment(&comprehensive_language()).unwrap();
        let RhoValue::Map(fields) = &mut fragment else {
            unreachable!()
        };
        fields.insert("types".into(), RhoValue::List(Vec::new()));
        let error = decode_language_core_data_fragment(&fragment).unwrap_err();
        assert!(error.message.contains("closed"));
    }

    #[test]
    fn structural_arm_rejects_name_mismatch_and_unknown_fields() {
        let value = language_core_to_value(&comprehensive_language()).unwrap();
        let mut mismatch_value = value.clone();
        let RhoValue::Map(mismatch) = &mut mismatch_value else {
            unreachable!()
        };
        mismatch.insert("name".into(), RhoValue::String("Wrong".into()));
        let error = decode_language_core_value(&mismatch_value).unwrap_err();
        assert!(error.message.contains("does not match"));

        let mut open_value = value;
        let RhoValue::Map(open) = &mut open_value else {
            unreachable!()
        };
        open.insert("types".into(), RhoValue::List(Vec::new()));
        let error = decode_language_core_value(&open_value).unwrap_err();
        assert!(error.message.contains("closed"));
    }

    #[test]
    fn structural_arm_rejects_unknown_nested_fields_by_reencoding() {
        let mut value = language_core_to_value(&comprehensive_language()).unwrap();
        let RhoValue::Map(envelope) = &mut value else {
            unreachable!()
        };
        let RhoValue::Map(core) = envelope.get_mut("core").unwrap() else {
            unreachable!()
        };
        core.insert("uncommitted".into(), RhoValue::Boolean(true));
        let error = decode_language_core_value(&value).unwrap_err();
        assert!(error.message.contains("closed canonical form"));
    }
}
