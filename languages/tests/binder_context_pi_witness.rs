#![cfg(all(feature = "pi", feature = "dovetail-codegen"))]

use mettail_languages::pi::{PiLanguage, PiTerm, PiTermInner};
use mettail_runtime::{BoundTerm, Language};
use proptest::prelude::*;

fn assert_reduces_to(source: &str, expected: &str) {
    let source = PiLanguage.parse_term(source).expect("source parses");
    let expected = PiLanguage
        .parse_term(expected)
        .expect("expected term parses");
    let actual = PiLanguage::dovetail_normal_term(source.as_ref(), 24, 200_000)
        .expect("communication reduces");
    let PiTermInner::Proc(actual) = &actual.as_any().downcast_ref::<PiTerm>().unwrap().0 else {
        panic!("Proc expected")
    };
    let PiTermInner::Proc(expected) = &expected.as_any().downcast_ref::<PiTerm>().unwrap().0 else {
        panic!("Proc expected")
    };
    assert!(
        BoundTerm::term_eq(&actual.unify_freevars_impl(), &expected.unify_freevars_impl()),
        "actual: {actual:?}\nexpected: {expected:?}"
    );
}

#[test]
fn communication_accepts_an_input_prefix_continuation() {
    assert_reduces_to("new(y, { in(c,x).in(d,z).e!x | c!y })", "new(y, { in(d,z).e!y })");
}

#[test]
fn communication_accepts_a_variable_continuation() {
    assert_reduces_to("{ in(c,x).p | c!m }", "{ p }");
}

fn continuation(leaf: u8, prefixes: &[bool], sent: &str) -> String {
    let mut body = match leaf {
        0 => format!("e!{sent}"),
        1 => "e!y".to_owned(),
        2 => "p".to_owned(),
        3 => "0".to_owned(),
        4 => format!("{{ e!{sent} | e!{sent} }}"),
        _ => format!("in(d,z).z!{sent}"),
    };
    for (index, input) in prefixes.iter().enumerate() {
        body = if *input {
            format!("in(d{index},z{index}).{body}")
        } else {
            format!("d{index}!y.{body}")
        };
    }
    body
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(128))]

    #[test]
    fn communication_depends_on_channels_and_preserves_the_continuation(
        leaf in 0u8..6,
        prefixes in proptest::collection::vec(any::<bool>(), 0..6),
        synchronous in any::<bool>(),
        matching in any::<bool>(),
        remainder_count in 0usize..4,
    ) {
        let channel = if matching { "c" } else { "other" };
        let output_continuation = if synchronous { ".k!y" } else { "" };
        let remainder = " | rest!y".repeat(remainder_count);
        let source = format!(
            "new(y, {{ in(c,x).{} | {channel}!y{output_continuation}{remainder} }})",
            continuation(leaf, &prefixes, "x"),
        );
        let expected = if matching {
            let output = if synchronous { " | k!y" } else { "" };
            let body = if leaf == 4 && prefixes.is_empty() {
                "e!y | e!y".to_owned()
            } else {
                continuation(leaf, &prefixes, "y")
            };
            format!(
                "new(y, {{ {body}{output}{remainder} }})",
            )
        } else {
            source.clone()
        };
        assert_reduces_to(&source, &expected);
        let source_term = PiLanguage.parse_term(&source).expect("source parses");
        let report = PiLanguage::dovetail_report_for(source_term.as_ref(), 24, 200_000)
            .expect("communication report succeeds");
        let fired = report.rule_firings.iter().any(|firing| {
            firing.label.as_deref().is_some_and(|label| {
                matches!(label.rsplit("::").next(), Some("Comm" | "CommAsync"))
            })
        });
        prop_assert_eq!(fired, matching);
    }
}

#[test]
fn communication_argument_keeps_its_restriction_binder() {
    let language = PiLanguage;
    let source = language
        .parse_term("new(y, { in(c,x).{ in(d,z).e!x } | c!y })")
        .expect("source parses");
    let expected = language
        .parse_term("new(y, { in(d,z).e!y })")
        .expect("expected term parses");
    let captured = language
        .parse_term("new(y, { in(d,z).e!z })")
        .expect("capture control parses");
    let actual = PiLanguage::dovetail_normal_term(source.as_ref(), 24, 200_000)
        .expect("communication reduces");
    let PiTermInner::Proc(actual) = &actual.as_any().downcast_ref::<PiTerm>().unwrap().0 else {
        panic!("Proc expected")
    };
    let PiTermInner::Proc(expected) = &expected.as_any().downcast_ref::<PiTerm>().unwrap().0 else {
        panic!("Proc expected")
    };
    let PiTermInner::Proc(captured) = &captured.as_any().downcast_ref::<PiTerm>().unwrap().0 else {
        panic!("Proc expected")
    };
    let actual = actual.unify_freevars_impl();
    let expected = expected.unify_freevars_impl();
    let captured = captured.unify_freevars_impl();
    assert!(!BoundTerm::term_eq(&expected, &captured));
    assert!(
        !BoundTerm::term_eq(&actual, &captured),
        "communication captured the sent name: {actual:?}"
    );
    assert!(
        BoundTerm::term_eq(&actual, &expected),
        "actual: {actual:?}\nexpected: {expected:?}"
    );
}
