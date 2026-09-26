use super::*;

fn pattern_grammar(pattern: &str) -> core::GrammarCoreV1 {
    let mut grammar = core::GrammarCoreV1::new("RuntimeUnicodeProfile");
    grammar.categories.push(category(0, "Value", true));
    grammar.tokens.push(token(
        0,
        "input",
        core::TokenPattern::Regex(pattern.into()),
        core::TokenDecoder::Text,
    ));
    grammar.modes[0].token_ids.push(core::TokenId(0));
    grammar.reductions.push(reduction(0, 0, 1));
    grammar.productions.push(core::Production {
        authored: None,
        id: core::ProductionId(0),
        constructor: core::ConstructorId(0),
        label: "Input".into(),
        result: core::CategoryId(0),
        syntax: vec![core::SyntaxItem::CaptureToken {
            token: core::TokenId(0),
            slot: "text".into(),
        }],
        precedence: core::Precedence::default(),
        classification: core::ProductionClass::default(),
        reduction: 0,
        provenance: None,
    });
    grammar
}

#[test]
fn runtime_unicode_profile_passes_independent_image_language_verification() {
    let defaults = crate::LiteralPatterns::default();
    for pattern in [
        ".",
        "[^a]",
        defaults.string.as_str(),
        r"\p{Letter}",
        r"\d",
        r"\D",
        r"\w",
        r"\W",
        r"\s",
        r"\S",
        r"[\D]",
        r"[^\w]",
        r"[a\p{Letter}]",
    ] {
        // compile_parser_image always runs the unchanged independent verifier:
        // this checks complete byte languages, not a sampled set of examples.
        let grammar = pattern_grammar(pattern);
        let image = compile_parser_image(&grammar)
            .unwrap_or_else(|error| panic!("Unicode profile image for {pattern:?}: {error:?}"));
        assert_eq!(image.compiler_abi, RUNTIME_COMPILER_ABI);
    }
}

#[test]
fn runtime_unicode_profile_keeps_unsupported_syntax_explicit() {
    let grammar = pattern_grammar(r"\xFF");
    assert!(
        matches!(compile_parser_image(&grammar), Err(RuntimeCompileError::Regex { .. })),
        "profile selection must not add a second parser for unsupported syntax"
    );
}
