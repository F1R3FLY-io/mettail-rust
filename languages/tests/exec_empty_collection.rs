//! Test exec [] and exec {} - minimal repro for TrailingTokens/LParen bug
use mettail_languages::calculator::{self as calc};
use mettail_runtime::Language;

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
    // Simulate exact REPL exec flow: parse -> ascent -> parse_term(nf.display)
    mettail_runtime::clear_var_cache();
    let lang = calc::CalculatorLanguage;
    let term = lang.parse_term("[]").expect("parse");
    let results = lang.run_ascent(term.as_ref()).expect("run_ascent");
    let initial_id = term.term_id();
    let nf = results.normal_form_reachable_from(initial_id).expect("normal form");
    let result_term = lang.parse_term(&nf.display);
    assert!(result_term.is_ok(), "parse_term(nf.display) should succeed for exec flow: {:?}", result_term.err());
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
