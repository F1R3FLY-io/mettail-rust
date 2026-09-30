use super::*;
use crate::{
    CategorySpec, CustomTokenSpec, LanguageSpec, LexerModeSpec, RuleSpecInput, SyntaxItemSpec,
};

// Lexer observation must not invoke semantic callbacks. Supply explicit,
// fingerprint-scoped fixture authority so parser admission remains unchanged;
// every callback panics if this lexical-only test accidentally executes it.
struct ObservationHost([u8; 32]);
impl mettail_grammar_core::RuntimeHost for ObservationHost {
    fn capability_manifest(
        &self,
        key: &mettail_grammar_core::RuntimeCapabilityKey,
    ) -> Option<mettail_grammar_core::RuntimeCapabilityManifest> {
        use mettail_grammar_core as core;
        (key.language_fingerprint == self.0).then(|| core::RuntimeCapabilityManifest {
            key: key.clone(),
            code_commitment: [1; 32],
            abi: "lexical-observation-test/1".into(),
            effects: [core::RuntimeEffect::Reduce].into_iter().collect(),
            cost: core::RuntimeLogicalCost {
                base: 1,
                per_input_byte: 1,
                per_value: 1,
                maximum: 1024,
            },
        })
    }
    fn decode_token(&self, _: &str, _: &str) -> Result<mettail_grammar_core::DynamicValue, String> {
        panic!("lexical observation must not execute token decoders")
    }
    fn evaluate(
        &self,
        _: &mettail_grammar_core::NativeEvaluation,
        _: &[mettail_grammar_core::DynamicValue],
        _: mettail_grammar_core::SourceSpan,
    ) -> Result<mettail_grammar_core::DynamicValue, String> {
        panic!("lexical observation must not execute native evaluation")
    }
}

fn specification(native: Option<&str>) -> LanguageSpec {
    LanguageSpec::new(
        "ObservedTokens".into(),
        vec![CategorySpec {
            name: "Value".into(),
            native_type: native.map(str::to_owned),
            is_primary: true,
            has_var: true,
        }],
        vec![RuleSpecInput {
            authored: None,
            label: "Plus".into(),
            category: "Value".into(),
            syntax: vec![SyntaxItemSpec::Terminal("+".into())],
            associativity: crate::binding_power::Associativity::Left,
            shares_level_with_previous: false,
            prefix_precedence: None,
            has_rust_code: false,
            rust_code: None,
            eval_mode: None,
            source_location: None,
            is_auto_injected: false,
        }],
    )
}

fn custom(name: &str) -> CustomTokenSpec {
    CustomTokenSpec {
        name: name.into(),
        pattern: "word".into(),
        category: None,
        payload_type: Some("str".into()),
        constructor_code: None,
        is_builtin_override: false,
        priority: 2,
        push_mode: None,
        is_pop: false,
        stream: None,
    }
}

#[test]
fn bridge_binding_is_identity_based_not_display_name_based() {
    let mut spec = specification(Some("i64"));
    spec.custom_tokens.push(custom("Word"));
    spec.modes.push(LexerModeSpec {
        name: "body".into(),
        token_specs: vec![custom("Part")],
        raw: false,
    });
    let mut grammar = spec.to_grammar_core().expect("bridge");
    let observations = grammar.wpda_token_observations.as_ref().expect("retained");
    assert_eq!(observations.len(), grammar.tokens.len());
    // These IDs are the actual original append order, not family-name lookup.
    assert_eq!(observations[0], Some(O::Ident));
    assert_eq!(observations[1], Some(O::Integer));
    assert_eq!(observations[2], None); // no Float variant in this emitted grammar
    assert_eq!(observations[5], Some(O::Custom("Word".into())));
    assert_eq!(observations[6], Some(O::Custom("Part".into())));
    // Literal rows follow the existing sorted-set order, including the
    // original lexer's implicit punctuation. Earlier declaration IDs do not move.
    let literals = ["(", ")", "+", ",", "[", "]", "{", "}"];
    assert_eq!(observations.len(), 7 + literals.len());
    for (offset, text) in literals.iter().enumerate() {
        assert_eq!(observations[7 + offset], Some(O::Fixed((*text).into())));
    }
    for token in &mut grammar.tokens {
        token.name = format!("unrelated-display-{}", token.id.0);
    }
    let bindings = OwnedTokenBindings::new(&grammar).expect("view");
    assert_eq!(bindings.resolve(TokenId(1), "41"), Ok(TokenKind::Integer));
    assert_eq!(bindings.resolve(TokenId(5), "word"), Ok(TokenKind::Custom("Word".into())));
    assert_eq!(bindings.resolve(TokenId(6), "word"), Ok(TokenKind::Custom("Part".into())));
    for (offset, text) in literals.iter().enumerate() {
        assert_eq!(
            bindings.resolve(TokenId((7 + offset) as u32), text),
            Ok(TokenKind::Fixed((*text).into()))
        );
    }
    assert_eq!(
        bindings.resolve(TokenId(2), "1.0"),
        Err(TokenBindingError::MissingToken(TokenId(2)))
    );
    assert_eq!(
        bindings.resolve(TokenId(999), ""),
        Err(TokenBindingError::MissingToken(TokenId(999)))
    );
}

#[test]
fn boolean_uses_original_lexer_payload_not_host_decode() {
    let mut spec = specification(Some("bool"));
    spec.literal_patterns.boolean = Some("true|false|YES".into());
    let grammar = spec.to_grammar_core().expect("bridge");
    let bindings = OwnedTokenBindings::new(&grammar).expect("view");
    assert_eq!(
        grammar
            .wpda_token_observations
            .as_ref()
            .expect("bridge retained Boolean observations")[4],
        Some(O::BooleanText)
    );
    for (text, expected) in [
        ("true", TokenKind::True),
        ("false", TokenKind::False),
        ("YES", TokenKind::False),
    ] {
        assert_eq!(bindings.resolve(TokenId(4), text), Ok(expected));
    }
}

#[test]
fn boolean_terminal_collision_retains_original_selected_kind() {
    let mut spec = specification(Some("bool"));
    spec.rules[0].label = "FalseTerm".into();
    spec.rules[0].syntax = vec![SyntaxItemSpec::Terminal("false".into())];
    let grammar = spec.to_grammar_core().expect("bridge");
    let terminal = grammar
        .tokens
        .iter()
        .find(|token| token.name == "literal/false")
        .expect("Core literal append site");
    let observation = grammar
        .wpda_token_observations
        .as_ref()
        .and_then(|rows| rows.get(terminal.id.0 as usize))
        .and_then(Option::as_ref);
    assert_eq!(observation, Some(&O::BooleanText));
    let bindings = OwnedTokenBindings::new(&grammar).expect("view");
    assert_eq!(bindings.resolve(terminal.id, "false"), Ok(TokenKind::False));
}

#[test]
fn typed_auxiliary_and_custom_share_the_actual_first_variant_winner() {
    let mut spec = specification(None);
    spec.custom_tokens.push(custom("Rat"));
    spec.literal_patterns
        .rational_by_category
        .insert("Rat".into(), "[0-9]+r".into());
    let grammar = spec.to_grammar_core().expect("bridge");
    let bindings = OwnedTokenBindings::new(&grammar).expect("view");
    // Active hybrid roster has Custom(Rat), not the nonhybrid RationalLit row.
    assert_eq!(bindings.resolve(TokenId(5), "12r"), Ok(TokenKind::Custom("Rat".into())));
    assert_eq!(bindings.resolve(TokenId(6), "word"), Ok(TokenKind::Custom("Rat".into())));
}

#[test]
fn unavailable_tables_and_invalid_cardinality_fail_closed() {
    let mut grammar = specification(None)
        .to_grammar_core()
        .expect("valid observation fixture");
    grammar.wpda_token_observations = None;
    assert!(matches!(
        OwnedTokenBindings::new(&grammar),
        Err(TokenBindingError::MissingTable)
    ));
    grammar.wpda_token_observations = Some(vec![]);
    assert!(matches!(
        OwnedTokenBindings::new(&grammar),
        Err(TokenBindingError::WrongTableLength)
    ));
    assert!(grammar
        .validate()
        .expect_err("mismatched token observation cardinality must be rejected")
        .contains(&mettail_grammar_core::ValidationError::InvalidWpdaTokenObservationCount));
}

#[test]
fn observation_table_is_committed_and_old_abi_is_rejected() {
    let grammar = specification(Some("bool"))
        .to_grammar_core()
        .expect("valid Boolean observation fixture");
    let encoded = postcard::to_allocvec(&grammar).expect("encode retained table");
    let decoded: GrammarCoreV1 = postcard::from_bytes(&encoded).expect("decode retained table");
    assert_eq!(decoded.wpda_token_observations, grammar.wpda_token_observations);
    let mut changed = grammar.clone();
    changed
        .wpda_token_observations
        .as_mut()
        .expect("bridge retained mutable observation table")[4] = Some(O::BooleanLit);
    assert_ne!(
        grammar
            .fingerprint()
            .expect("original observation fingerprint"),
        changed
            .fingerprint()
            .expect("changed observation fingerprint")
    );
    changed.abi = mettail_grammar_core::GRAMMAR_CORE_ABI_V5;
    assert!(changed
        .validate()
        .expect_err("old grammar ABI must be rejected")
        .contains(&mettail_grammar_core::ValidationError::UnsupportedAbi(5)));
}

#[test]
fn neutral_matcher_retains_guarded_sites_and_boolean_alternatives() {
    use NeutralPattern as P;
    let guest = P::GuestName("Rat".into());
    let category = P::CategoryName("Rat".into());
    let wrong = P::CategoryName("Other".into());
    let custom = TokenKind::Custom("Rat".into());
    assert_ne!(P::GuestCustomRef, P::CustomTyped);
    assert!(matches_prefix(&P::GuestCustomRef, Some(&guest), &custom));
    assert!(matches_prefix(&P::CustomTyped, Some(&category), &custom));
    assert!(!matches_prefix(&P::CustomTyped, Some(&wrong), &custom));
    assert!(!matches_prefix(&P::RationalTyped, Some(&category), &custom));
    assert!(matches_prefix(
        &P::RationalTyped,
        Some(&category),
        &TokenKind::RationalLit("Rat".into())
    ));
    for kind in [TokenKind::True, TokenKind::False, TokenKind::BooleanLit] {
        assert!(matches_prefix(&P::BooleanAlternative, None, &kind));
        assert!(matches_prefix(&P::Capture, Some(&P::CaptureName("Boolean".into())), &kind));
    }
    assert!(!matches_prefix(&P::Integer, None, &TokenKind::IntegerLit("Rat".into())));
}

#[test]
fn actual_bridge_image_session_and_source_chain_uses_retained_bindings() {
    use crate::runtime_backend::{compile_parser_image, RUNTIME_COMPILER_ABI, RUNTIME_UNICODE_ABI};
    use crate::wpda_owned::source::{OwnedTokenSource, SourceAdapterLimits};
    use crate::wpda_runtime::WpdaTokenSource;
    use mettail_grammar_core::RuntimeParser;
    let grammar = specification(Some("bool"))
        .to_grammar_core()
        .expect("producer");
    let image = compile_parser_image(&grammar).expect("image");
    let host = ObservationHost(grammar.fingerprint().expect("fixture fingerprint"));
    let parser =
        RuntimeParser::new(&grammar, &image, RUNTIME_COMPILER_ABI, RUNTIME_UNICODE_ABI, &host)
            .expect("admit");
    let session = parser.lexical_session("true").expect("original lexer");
    let source = OwnedTokenSource::from_admitted_session(
        &session,
        SourceAdapterLimits { nodes: 100, edges: 100, text_bytes: 1000 },
    )
    .expect("retained observer");
    let mut kinds = vec![source.peek_kind(0).expect("primary lexical observation")];
    kinds.extend(
        source
            .peek_alternatives(0)
            .iter()
            .map(|alternative| alternative.kind.clone()),
    );
    assert!(kinds.contains(&TokenKind::True));
    assert!(kinds.contains(&TokenKind::Ident));
}

#[test]
fn native_custom_producer_resolves_actual_edges_without_requiring_unused_rows() {
    use crate::runtime_backend::{compile_parser_image, RUNTIME_COMPILER_ABI, RUNTIME_UNICODE_ABI};
    use crate::wpda_owned::source::{OwnedTokenSource, SourceAdapterLimits};
    use crate::wpda_runtime::WpdaTokenSource;
    use mettail_grammar_core::RuntimeParser;
    let mut spec = specification(Some("i64"));
    spec.custom_tokens.push(custom("Word"));
    let grammar = spec
        .to_grammar_core()
        .expect("native and custom producer fixture");
    let rows = grammar
        .wpda_token_observations
        .as_ref()
        .expect("retained append-site observations");
    assert!(rows.iter().any(Option::is_none), "unused Float/Boolean rows remain unavailable");
    let image = compile_parser_image(&grammar).expect("compile native custom image");
    let host = ObservationHost(grammar.fingerprint().expect("fixture fingerprint"));
    let parser =
        RuntimeParser::new(&grammar, &image, RUNTIME_COMPILER_ABI, RUNTIME_UNICODE_ABI, &host)
            .expect("admit native custom image");
    for (text, expected) in [("word", TokenKind::Custom("Word".into())), ("41", TokenKind::Integer)]
    {
        let session = parser
            .lexical_session(text)
            .expect("existing native custom lexer");
        let source = OwnedTokenSource::from_admitted_session(
            &session,
            SourceAdapterLimits { nodes: 100, edges: 100, text_bytes: 1000 },
        )
        .expect("every actual edge has an original producer observation");
        let mut kinds = vec![source.peek_kind(0).expect("primary accepted edge")];
        kinds.extend(
            source
                .peek_alternatives(0)
                .iter()
                .map(|alternative| alternative.kind.clone()),
        );
        assert!(
            kinds.contains(&expected),
            "missing actual {expected:?} observation for {text:?}"
        );
    }
}
