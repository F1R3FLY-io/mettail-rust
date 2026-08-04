//! Structural contract for Rholang's generic receiver-first method surface.
//!
//! Method names and arities belong to f1r3node's reducer.  The grammar's job is
//! deliberately smaller: retain the receiver, the identifier text, and the ordered
//! positional arguments without installing one production (and one lexer terminal)
//! per reducer method.

#![cfg(feature = "rholang")]

use mettail_ast::auto_inject::reconstruct_language_def;
use mettail_languages::rholang::{Proc, RholangLanguage};
use mettail_runtime::Language;

fn parse(source: &str) -> Proc {
    Proc::parse(source).unwrap_or_else(|err| panic!("failed to parse {source:?}: {err:?}"))
}

fn rholang_definition() -> mettail_ast::language::LanguageDef {
    let source = RholangLanguage
        .metadata()
        .definition_source()
        .expect("Rholang metadata carries its definition source");
    reconstruct_language_def(source).expect("Rholang definition source reconstructs")
}

fn assert_method(
    source: &str,
    expected_receiver: &str,
    expected_name: &str,
    expected_args: &[&str],
) {
    let parsed = parse(source);
    let Proc::MethodCall(receiver, name, arguments) = &parsed else {
        panic!("{source:?} parsed as {parsed}, not MethodCall");
    };

    assert_eq!(receiver.to_string(), expected_receiver, "receiver drift");
    assert_eq!(name, expected_name, "method-name text drift");
    assert_eq!(
        arguments
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>(),
        expected_args,
        "ordered positional arguments drifted",
    );

    let displayed = parsed.to_string();
    assert!(
        !displayed.contains(" . ") && !displayed.contains(" , "),
        "member-call punctuation must remain compact: {displayed:?}",
    );
    let reparsed = parse(&displayed);
    assert_eq!(
        reparsed.to_string(),
        displayed,
        "MethodCall display is not parse-stable: {source:?} -> {displayed:?}",
    );
}

#[test]
fn arbitrary_identifier_names_are_preserved_for_the_reducer() {
    assert_method("Nil.notamethod()", "Nil", "notamethod", &[]);
    assert_method("Nil.length()", "Nil", "length", &[]);
    assert_method("Nil.toNextLeaf()", "Nil", "toNextLeaf", &[]);
}

#[test]
fn argument_vector_preserves_arity_and_source_order() {
    assert_method("Nil.f()", "Nil", "f", &[]);
    assert_method("Nil.f(1)", "Nil", "f", &["1"]);
    assert_method("Nil.f(1, true, \"three\")", "Nil", "f", &["1", "true", "\"three\""]);
}

#[test]
fn chained_calls_retain_the_previous_call_as_the_receiver() {
    let parsed = parse("Nil.first(1).second(2, 3)");
    let Proc::MethodCall(receiver, name, arguments) = &parsed else {
        panic!("method chain did not end in MethodCall: {parsed}");
    };
    assert_eq!(name, "second");
    assert_eq!(
        arguments
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>(),
        ["2", "3"]
    );

    let Proc::MethodCall(inner_receiver, inner_name, inner_arguments) = receiver.as_ref() else {
        panic!("method chain lost its inner MethodCall receiver: {receiver}");
    };
    assert_eq!(inner_receiver.to_string(), "Nil");
    assert_eq!(inner_name, "first");
    assert_eq!(
        inner_arguments
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>(),
        ["1"]
    );
}

#[test]
fn definition_has_one_generic_constructor_and_one_receiver_withholding_rule() {
    let definition = rholang_definition();

    let method_terms = definition
        .terms
        .iter()
        .filter(|rule| rule.label.to_string() == "MethodCall")
        .collect::<Vec<_>>();
    assert_eq!(
        method_terms.len(),
        1,
        "Rholang must expose exactly one generic MethodCall constructor",
    );
    let method_term = method_terms[0];
    assert_eq!(
        method_term
            .term_context
            .as_ref()
            .expect("MethodCall uses judgement syntax")
            .len(),
        3,
        "MethodCall must carry receiver, identifier text, and one ordered argument vector",
    );
    assert!(
        method_term.rust_code.is_none() && method_term.eval_mode.is_none(),
        "MethodCall must remain a constructor; method semantics belong to the reducer",
    );

    let withholding = definition
        .rewrites
        .iter()
        .filter(|rule| rule.withholds_congruence())
        .map(|rule| rule.name.to_string())
        .filter(|name| name.starts_with("MethodCall"))
        .collect::<Vec<_>>();
    assert_eq!(
        withholding,
        ["MethodCallReceiverWithheld"],
        "the generic method surface needs exactly one explicit receiver-withholding rule",
    );
    assert!(
        definition
            .rewrites
            .iter()
            .filter(|rule| rule.is_congruence_rule())
            .all(|rule| !rule.name.to_string().starts_with("MethodCall")),
        "method-specific positive congruences reappeared",
    );
}
