use mettail_grammar_core::*;

fn fixture() -> GrammarCoreV1 {
    let mut store = AuthoredRuleStore::new();
    let label = AuthoredNameId(
        store
            .try_push(AuthoredNode::Name(AuthoredName {
                spelling: "Zero".into(),
                equality_class: 0,
            }))
            .expect("authored fixture node is retained"),
    );
    let category = AuthoredNameId(
        store
            .try_push(AuthoredNode::Name(AuthoredName {
                spelling: "Term".into(),
                equality_class: 1,
            }))
            .expect("authored fixture node is retained"),
    );
    let rule = AuthoredRuleId(
        store
            .try_push(AuthoredNode::Rule(AuthoredRule {
                source_body_present: mettail_grammar_core::SourceObservation::Unavailable,
                explicit_fold: mettail_grammar_core::SourceObservation::Unavailable,
                label,
                category,
                term_context: None,
                syntax_pattern: None,
                items: Vec::new(),
            }))
            .expect("authored fixture node is retained"),
    );
    let mut grammar = GrammarCoreV1::new("AuthoredTransport");
    grammar.categories.push(Category {
        id: CategoryId(0),
        name: "Term".into(),
        carrier: Carrier::Dynamic,
        primary: true,
        admits_variables: false,
    });
    grammar.reductions.push(ReductionPlan {
        output_category: CategoryId(0),
        constructor: ConstructorId(0),
        input_arity: 0,
        fields: Vec::new(),
        evaluation: None,
        evaluation_mode: None,
        tier: None,
    });
    grammar.productions.push(Production {
        id: ProductionId(0),
        constructor: ConstructorId(0),
        label: "Zero".into(),
        result: CategoryId(0),
        authored: Some(rule),
        syntax: Vec::new(),
        precedence: Precedence::default(),
        classification: ProductionClass::default(),
        reduction: 0,
        provenance: None,
    });
    grammar.authored = Some(store);
    grammar
        .validate()
        .expect("authored transport fixture is valid");
    grammar
}

fn assert_association_error(grammar: &GrammarCoreV1, expected: &'static str) {
    assert!(grammar
        .validate()
        .expect_err("invalid authored transport must be refused")
        .iter()
        .any(|error| matches!(
            error, ValidationError::InvalidAuthoredRule { production: 0, field, .. }
                if *field == expected
        )));
}

#[test]
fn authored_transport_checks_store_rule_tag_bounds_and_names() {
    let original = fixture();
    let mut changed = original.clone();
    changed.authored = None;
    assert_association_error(&changed, "store");
    for index in [0, u32::MAX] {
        let mut changed = original.clone();
        changed.productions[0].authored = Some(AuthoredRuleId(index));
        assert_association_error(&changed, "rule");
    }
    let mut changed = original.clone();
    changed.productions[0].label = "Other".into();
    assert_association_error(&changed, "label");
    let mut changed = original.clone();
    changed.categories[0].name = "Other".into();
    assert_association_error(&changed, "category");
    let mut changed = original;
    changed.productions[0].result = CategoryId(17);
    assert_association_error(&changed, "category");
}

#[test]
fn authored_transport_unavailable_and_present_empty_are_distinct() {
    let mut grammar = fixture();
    grammar.productions[0].authored = None;
    grammar.authored = None;
    grammar
        .validate()
        .expect("authored transport fixture is valid");
    let absent = grammar
        .fingerprint()
        .expect("semantic commitment serializes");
    grammar.authored = Some(AuthoredRuleStore::new());
    grammar
        .validate()
        .expect("authored transport fixture is valid");
    assert_ne!(
        absent,
        grammar
            .fingerprint()
            .expect("semantic commitment serializes")
    );
}

#[test]
fn authored_transport_commits_store_and_association_but_not_diagnostics() {
    let original = fixture();
    let mut changed = original.clone();
    changed
        .authored
        .as_mut()
        .expect("authored fixture node is retained")
        .try_push(AuthoredNode::Name(AuthoredName {
            spelling: "unused authored name".into(),
            equality_class: 2,
        }))
        .expect("authored fixture node is retained");
    changed
        .validate()
        .expect("authored transport fixture is valid");
    assert_ne!(
        original
            .fingerprint()
            .expect("semantic commitment serializes"),
        changed
            .fingerprint()
            .expect("semantic commitment serializes")
    );
    let left = LanguageCoreV1::structural(original.clone());
    let right = LanguageCoreV1::structural(changed);
    assert_eq!(
        left.theory_fingerprint()
            .expect("theory commitment serializes"),
        right
            .theory_fingerprint()
            .expect("theory commitment serializes")
    );
    assert_ne!(
        left.fingerprint().expect("semantic commitment serializes"),
        right.fingerprint().expect("semantic commitment serializes")
    );

    let mut changed = original.clone();
    changed.productions[0].authored = None;
    assert_ne!(
        original
            .fingerprint()
            .expect("semantic commitment serializes"),
        changed
            .fingerprint()
            .expect("semantic commitment serializes")
    );
    let mut changed = original.clone();
    changed.backend_context = Some("diagnostic".into());
    changed.documentation = Some("explanation".into());
    changed.provenance.frontend = "another frontend".into();
    changed.productions[0].provenance = Some(SourceProvenance {
        uri: Some("test:source".into()),
        line: 5,
        column: 7,
    });
    assert_eq!(
        original
            .fingerprint()
            .expect("semantic commitment serializes"),
        changed
            .fingerprint()
            .expect("semantic commitment serializes")
    );
}

#[test]
fn authored_transport_binary_roundtrip_retains_store_and_references() {
    let grammar = fixture();
    let bytes = postcard::to_allocvec(&grammar).expect("transport fixture encodes");
    let decoded: GrammarCoreV1 = postcard::from_bytes(&bytes).expect("transport fixture decodes");
    decoded
        .validate()
        .expect("authored transport fixture is valid");
    assert_eq!(grammar, decoded);
    for old_abi in [GRAMMAR_CORE_ABI_V1, GRAMMAR_CORE_ABI_V2, GRAMMAR_CORE_ABI_V3] {
        let mut old = grammar.clone();
        old.abi = old_abi;
        let bytes = postcard::to_allocvec(&old).expect("transport fixture encodes");
        let decoded: GrammarCoreV1 =
            postcard::from_bytes(&bytes).expect("transport fixture decodes");
        assert!(decoded
            .validate()
            .expect_err("invalid authored transport must be refused")
            .contains(&ValidationError::UnsupportedAbi(old_abi)));
    }
}

#[test]
fn original_occurrence_receipt_preserves_order_multiplicity_and_semantic_identity() {
    let mut grammar = fixture();
    let mut second = grammar.productions[0].clone();
    second.id = ProductionId(1);
    grammar.productions.push(second);
    let unavailable = grammar.fingerprint().expect("fingerprint");
    grammar.wpda_original_occurrences = Some(vec![]);
    grammar.validate().expect("explicit empty receipt");
    assert_ne!(unavailable, grammar.fingerprint().expect("fingerprint"));

    let roster = vec![ProductionId(1), ProductionId(0), ProductionId(1)];
    grammar.wpda_original_occurrences = Some(roster.clone());
    grammar
        .validate()
        .expect("duplicate occurrences are original evidence");
    let fingerprint = grammar.fingerprint().expect("fingerprint");
    let bytes = postcard::to_allocvec(&grammar).expect("encode receipt");
    let decoded: GrammarCoreV1 = postcard::from_bytes(&bytes).expect("decode receipt");
    decoded.validate().expect("receipt remains valid");
    assert_eq!(decoded.wpda_original_occurrences, Some(roster));
    assert_eq!(decoded.fingerprint().expect("fingerprint"), fingerprint);
    for changed in [
        vec![ProductionId(1), ProductionId(1), ProductionId(0)],
        vec![ProductionId(1), ProductionId(0)],
    ] {
        grammar.wpda_original_occurrences = Some(changed);
        grammar.validate().expect("ordered receipt");
        assert_ne!(grammar.fingerprint().expect("fingerprint"), fingerprint);
    }
}

#[test]
fn original_occurrence_receipt_checks_bounds_ids_and_retained_authored_references() {
    let original = fixture();
    let mut changed = original.clone();
    changed.wpda_original_occurrences = Some(vec![ProductionId(u32::MAX)]);
    assert!(changed.validate().expect_err("out of range").contains(
        &ValidationError::InvalidWpdaOriginalOccurrence {
            occurrence: 0,
            production: ProductionId(u32::MAX),
            field: "production"
        }
    ));
    let mut changed = original.clone();
    changed.wpda_original_occurrences = Some(vec![ProductionId(0)]);
    changed.productions[0].id = ProductionId(1);
    assert!(changed.validate().expect_err("mismatched index").contains(
        &ValidationError::InvalidWpdaOriginalOccurrence {
            occurrence: 0,
            production: ProductionId(0),
            field: "id"
        }
    ));
    let mut changed = original.clone();
    changed.wpda_original_occurrences = Some(vec![ProductionId(0)]);
    changed.productions[0].authored = None;
    assert!(changed
        .validate()
        .expect_err("missing authored reference")
        .contains(&ValidationError::InvalidWpdaOriginalOccurrence {
            occurrence: 0,
            production: ProductionId(0),
            field: "authored"
        }));
    changed.productions[0].authored = Some(AuthoredRuleId(u32::MAX));
    assert_association_error(&changed, "rule");

    let mut grammar = original;
    let mut helper = grammar.productions[0].clone();
    helper.id = ProductionId(1);
    helper.authored = None;
    grammar.productions.push(helper);
    grammar.wpda_original_occurrences = Some(vec![ProductionId(0)]);
    grammar
        .validate()
        .expect("unlisted helper is not inferred into the receipt");
}

/// Feed named fields through Serde while reusing postcard to deserialize each
/// field value. This tests missing-vs-null without another wire dependency.
struct NamedFields<'a> {
    fields: std::slice::Iter<'a, (&'static str, Vec<u8>)>,
    pending: Option<&'a [u8]>,
}

impl<'de> serde::de::MapAccess<'de> for NamedFields<'de> {
    type Error = serde::de::value::Error;

    fn next_key_seed<K: serde::de::DeserializeSeed<'de>>(
        &mut self,
        seed: K,
    ) -> Result<Option<K::Value>, Self::Error> {
        use serde::de::IntoDeserializer;
        let Some((name, bytes)) = self.fields.next() else {
            return Ok(None);
        };
        self.pending = Some(bytes);
        seed.deserialize((*name).into_deserializer()).map(Some)
    }

    fn next_value_seed<V: serde::de::DeserializeSeed<'de>>(
        &mut self,
        seed: V,
    ) -> Result<V::Value, Self::Error> {
        let bytes = self.pending.take().expect("named key precedes value");
        seed.deserialize(&mut postcard::Deserializer::from_bytes(bytes))
            .map_err(serde::de::Error::custom)
    }
}

#[test]
fn original_occurrence_receipt_missing_named_field_is_not_unavailable() {
    use serde::Deserialize;
    let grammar = fixture();
    macro_rules! fields {
        ($($field:ident),+ $(,)?) => { vec![$(
            (stringify!($field), postcard::to_allocvec(&grammar.$field).expect("field encodes"))
        ),+] };
    }
    let mut fields = fields![
        abi,
        name,
        backend_context,
        documentation,
        categories,
        tokens,
        modes,
        productions,
        authored,
        authored_bindings,
        wpda_token_observations,
        wpda_original_occurrences,
        reductions,
        semantic_dependencies,
        semantic_program,
        parser_configuration,
        synchronization,
        tree_invariants,
        refinement_types,
        guard_configuration,
        capabilities,
        provenance,
        limits,
        weight_profile,
    ];
    let decode = |fields: &[(&'static str, Vec<u8>)]| {
        GrammarCoreV1::deserialize(serde::de::value::MapAccessDeserializer::new(NamedFields {
            fields: fields.iter(),
            pending: None,
        }))
    };
    assert_eq!(decode(&fields).expect("explicit None is supported"), grammar);
    fields.retain(|(name, _)| *name != "wpda_original_occurrences");
    let error = decode(&fields).expect_err("missing receipt field is rejected");
    assert!(error.to_string().contains("wpda_original_occurrences"), "{error}");
}
