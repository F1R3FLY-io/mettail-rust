//! Test exec [] and exec {} - minimal repro for TrailingTokens/LParen bug
//! Also tests non-empty collections: [1,2,3], ["a"], {1,1,2}
use mettail_languages::calculator::{self as calc};
use mettail_runtime::Language;

#[test]
fn test_parse_non_empty_list() {
    mettail_runtime::clear_var_cache();
    let lang = calc::CalculatorLanguage;
    let result = lang.parse_term("[1,2,3]");
    assert!(result.is_ok(), "parse [1,2,3] should succeed: {:?}", result.err());
    let result = lang.parse_term(r#"["a"]"#);
    assert!(result.is_ok(), r#"parse ["a"] should succeed: {:?}"#, result.err());
}

#[test]
fn test_parse_non_empty_bag() {
    mettail_runtime::clear_var_cache();
    let lang = calc::CalculatorLanguage;
    let result = lang.parse_term("{1,1,2}");
    assert!(result.is_ok(), "parse {{1,1,2}} should succeed: {:?}", result.err());
}

#[test]
fn test_parse_empty_list() {
    mettail_runtime::clear_var_cache();
    let lang = calc::CalculatorLanguage;
    let result = lang.parse_term("[]");
    assert!(result.is_ok(), "parse [] should succeed: {:?}", result.err());
    let term = result.unwrap();
    let display = format!("{}", term);
    assert_eq!(display, "[]", "display of [] should be []");
    // Round-trip: parse the display
    let roundtrip = lang.parse_term(&display);
    assert!(roundtrip.is_ok(), "roundtrip parse of '{}' should succeed: {:?}", display, roundtrip.err());
}

#[test]
fn test_exec_flow_empty_list() {
    // Simulate REPL exec flow: parse -> ascent -> parse_term(display) for some reachable term
    mettail_runtime::clear_var_cache();
    let lang = calc::CalculatorLanguage;
    let term = lang.parse_term("[]").expect("parse");
    let results = lang.run_ascent(term.as_ref()).expect("run_ascent");
    let display = format!("{}", term);
    // Prefer normal form reachable from initial term (REPL exec behavior); else any term with same display
    let to_parse = results
        .normal_form_reachable_from(term.term_id())
        .map(|nf| nf.display.clone())
        .or_else(|| {
            results
                .all_terms
                .iter()
                .find(|t| t.display == display)
                .map(|t| t.display.clone())
        })
        .unwrap_or(display);
    let result_term = lang.parse_term(&to_parse);
    assert!(
        result_term.is_ok(),
        "parse_term({:?}) should succeed for exec flow: {:?}",
        to_parse,
        result_term.err()
    );
}

#[test]
fn test_parse_empty_bag() {
    mettail_runtime::clear_var_cache();
    let lang = calc::CalculatorLanguage;
    let result = lang.parse_term("{}");
    assert!(result.is_ok(), "parse {{}} should succeed: {:?}", result.err());
    let term = result.unwrap();
    let display = format!("{}", term);
    assert_eq!(display, "{}", "display of {{}} should be {{}}");
    // Round-trip: parse the display
    let roundtrip = lang.parse_term(&display);
    assert!(roundtrip.is_ok(), "roundtrip parse of '{}' should succeed: {:?}", display, roundtrip.err());
}
