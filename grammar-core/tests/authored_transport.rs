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
