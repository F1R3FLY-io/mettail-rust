//! Regression coverage for empty and non-empty collection parsing.
use mettail_languages::calculator::{self as calc};
use mettail_runtime::Language;
use mettail_testkit::runtime_report::{report_semantic_outputs, run_default_backend_report};

#[test]
fn test_parse_non_empty_list() {
    mettail_runtime::clear_var_cache();
    let lang = calc::CalculatorLanguage;
    let result = lang.parse_term("list(1,2,3)");
    assert!(result.is_ok(), "parse list(1,2,3) should succeed: {:?}", result.err());
    let result = lang.parse_term(r#"list("a")"#);
    assert!(result.is_ok(), r#"parse list("a") should succeed: {:?}"#, result.err());
}

#[test]
fn test_parse_non_empty_bag() {
    mettail_runtime::clear_var_cache();
    let lang = calc::CalculatorLanguage;
    let result = lang.parse_term("bag(1,1,2)");
    assert!(result.is_ok(), "parse bag(1,1,2) should succeed: {:?}", result.err());
}

#[test]
fn test_parse_empty_list() {
    mettail_runtime::clear_var_cache();
    let lang = calc::CalculatorLanguage;
    let result = lang.parse_term("list()");
    assert!(result.is_ok(), "parse list() should succeed: {:?}", result.err());
    let term = result.unwrap();
    let display = format!("{}", term);
    assert_eq!(display, "list()", "display of list() should be list()");
    // Round-trip: parse the display
    let roundtrip = lang.parse_term(&display);
    assert!(
        roundtrip.is_ok(),
        "roundtrip parse of '{}' should succeed: {:?}",
        display,
        roundtrip.err()
    );
}

#[test]
fn test_exec_flow_empty_list() {
    // Simulate REPL exec flow: parse -> selected backend -> parse_term(display)
    // for some backend-produced semantic output.
    mettail_runtime::clear_var_cache();
    let lang = calc::CalculatorLanguage;
    let term = lang.parse_term("list()").expect("parse");
    let report = run_default_backend_report(&lang, term.as_ref(), "empty collection exec flow")
        .expect("run");
    let display = format!("{}", term);
    let outputs = report_semantic_outputs(&report);
    let to_parse = outputs
        .iter()
        .find(|candidate| lang.parse_term(candidate).is_ok())
        .cloned()
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
    let result = lang.parse_term("bag()");
    assert!(result.is_ok(), "parse bag() should succeed: {:?}", result.err());
    let term = result.unwrap();
    let display = format!("{}", term);
    assert_eq!(display, "bag()", "display of bag() should be bag()");
    // Round-trip: parse the display
    let roundtrip = lang.parse_term(&display);
    assert!(
        roundtrip.is_ok(),
        "roundtrip parse of '{}' should succeed: {:?}",
        display,
        roundtrip.err()
    );
}
