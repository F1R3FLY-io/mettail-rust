use super::*;
use mettail_grammar_core::{DynamicTerm, DynamicValue, GrammarCoreV1, SourceSpan};

const SOURCE: &str = include_str!("../../../tests/fixtures/regex_gslt.rho");

fn term(core: &GrammarCoreV1, label: &str, fields: Vec<DynamicValue>) -> DynamicValue {
    let production = core
        .productions
        .iter()
        .find(|p| p.label == label)
        .expect("declared constructor");
    DynamicValue::Term(Box::new(DynamicTerm {
        category: production.result,
        constructor: production.constructor,
        fields,
        span: SourceSpan::default(),
    }))
}

fn quantifier(core: &GrammarCoreV1, suffix: &str, child: DynamicValue) -> DynamicValue {
    let (label, fields) = match suffix {
        "*" => ("PStar", vec![child]),
        "+" => ("PPlus", vec![child]),
        "?" => ("POptional", vec![child]),
        "{2,3}" => ("PRepeat", vec![child, DynamicValue::Integer(2), DynamicValue::Integer(3)]),
        _ => unreachable!("fixed quantifier matrix"),
    };
    term(core, label, fields)
}

fn assert_structure(actual: &DynamicValue, expected: &DynamicValue, source: &str) {
    // Source spans describe the spelling, not constructor structure. Check every
    // other field with an explicit worklist, including ordered native bounds.
    let mut pending = vec![(actual, expected)];
    while let Some((actual, expected)) = pending.pop() {
        match (actual, expected) {
            (DynamicValue::Term(actual), DynamicValue::Term(expected)) => {
                assert_eq!(actual.category, expected.category, "{source}");
                assert_eq!(actual.constructor, expected.constructor, "{source}");
                assert_eq!(actual.fields.len(), expected.fields.len(), "{source}");
                pending.extend(actual.fields.iter().zip(&expected.fields));
            },
            _ => assert_eq!(actual, expected, "{source}"),
        }
    }
}

#[test]
fn practical_regex_quantifiers_reject_adjacent_pairs_and_admit_grouping() {
    let runtime = RholangLanguageRuntime::new(Arc::new(LanguageInstallService::new(
        Arc::new(MemoryRegistry::default()),
        LanguageInstallPolicy::default(),
    )));
    let batch = runtime
        .install_all(rholang_ddl_candidate(SOURCE))
        .expect("actual inline Regex declaration installs");
    let token = &batch.exports[0].handle;
    let handle = runtime
        .resolve(token, LanguageRight::Parse)
        .expect("parse capability");
    let installed = runtime
        .service
        .table()
        .authorize(&handle, LanguageRight::Parse)
        .expect("installed language");
    let core = installed.core();
    let category = resolve_required_category(core, "Pattern").expect("Pattern category");
    let parse = |source: &str| {
        runtime
            .service
            .parse(&handle, source, Some(category), runtime.host.as_ref())
    };
    let literal = |text: &str| term(core, "PLiteral", vec![DynamicValue::Text(text.into())]);
    for inner in ["*", "+", "?", "{2,3}"] {
        for outer in ["*", "+", "?", "{2,3}"] {
            let adjacent = format!("a{inner}{outer}");
            assert!(
                matches!(parse(&adjacent), Err(InstalledParseError::Parse(RuntimeError::NoParse))),
                "{adjacent}: adjacent quantifiers must be rejected"
            );
            let grouped = format!("(a{inner}){outer}");
            let parses = parse(&grouped).unwrap_or_else(|error| panic!("{grouped}: {error:?}"));
            assert_eq!(parses.len(), 1, "{grouped}");
            let expected = quantifier(
                core,
                outer,
                term(core, "PGroup", vec![quantifier(core, inner, literal("a"))]),
            );
            assert_structure(&parses[0].syntax, &expected, &grouped);
            eprintln!("{adjacent}: rejected; {grouped}: exact constructor structure verified");
        }
    }
    for (source, expected) in [
        (
            "ab*|c",
            term(
                core,
                "PAlt",
                vec![
                    term(core, "PConcat", vec![literal("a"), quantifier(core, "*", literal("b"))]),
                    literal("c"),
                ],
            ),
        ),
        (
            "abc",
            term(
                core,
                "PConcat",
                vec![term(core, "PConcat", vec![literal("a"), literal("b")]), literal("c")],
            ),
        ),
        (
            "a|b|c",
            term(
                core,
                "PAlt",
                vec![term(core, "PAlt", vec![literal("a"), literal("b")]), literal("c")],
            ),
        ),
    ] {
        let parses = parse(source).unwrap_or_else(|error| panic!("{source}: {error:?}"));
        assert_eq!(parses.len(), 1, "{source}");
        assert_structure(&parses[0].syntax, &expected, source);
    }
    assert_eq!(
        runtime
            .parse_source(token, "a*?", "Pattern")
            .expect("parse-only boundary"),
        LanguageParseOutcome::Rejected(LanguageParseRejection::NoParse)
    );
    assert_eq!(
        runtime
            .parse_source(token, "(a*)?", "Pattern")
            .expect("parse-only boundary"),
        LanguageParseOutcome::Accepted
    );
}
