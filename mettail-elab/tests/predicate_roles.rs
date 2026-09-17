use mettail_elab::canonical::{value_to_language_core, RhoValue};
use mettail_elab::core_value::language_core_to_value;
use mettail_elab::module::{CanonicalModuleExport, CanonicalModuleValue};
use std::collections::BTreeMap;

fn s(value: &str) -> RhoValue {
    RhoValue::String(value.into())
}
fn l(values: impl IntoIterator<Item = RhoValue>) -> RhoValue {
    RhoValue::List(values.into_iter().collect())
}
fn m(values: impl IntoIterator<Item = (&'static str, RhoValue)>) -> RhoValue {
    RhoValue::Map(
        values
            .into_iter()
            .map(|(key, value)| (key.into(), value))
            .collect(),
    )
}
fn ctor(name: &str) -> RhoValue {
    l([s(name)])
}

fn language(role: Option<RhoValue>) -> RhoValue {
    let mut observation = BTreeMap::from([
        ("name".into(), s("matches")),
        ("action".into(), s("match")),
        ("result".into(), s("Expr")),
    ]);
    if let Some(role) = role {
        observation.insert("predicate_role".into(), role);
    }
    m([
        ("mettail", s("language/3")),
        ("name", s("Predicate")),
        ("types", l([s("Expr")])),
        (
            "terms",
            l([("Call", "call"), ("Yes", "yes"), ("No", "no")].map(|(label, text)| {
                m([
                    ("label", s(label)),
                    ("category", s("Expr")),
                    ("syntax", l([l([s("lit"), s(text)])])),
                ])
            })),
        ),
        (
            "rewrites",
            l([m([("name", s("Match")), ("left", ctor("Call")), ("right", ctor("Yes"))])]),
        ),
        (
            "oslf",
            m([
                ("effects", l([m([("name", s("pure"))])])),
                (
                    "actions",
                    l([m([
                        ("id", s("match")),
                        ("domain", l([s("Expr")])),
                        ("codomain", s("Expr")),
                        ("transition", l([s("rewrite"), s("Match")])),
                        ("effect", s("pure")),
                        ("grade", s("Expr")),
                        ("execution", s("one_step")),
                    ])]),
                ),
                ("observations", l([RhoValue::Map(observation)])),
            ]),
        ),
    ])
}

fn role() -> RhoValue {
    m([
        ("input_constructor", s("Call")),
        ("accepting", ctor("Yes")),
        ("rejecting", ctor("No")),
    ])
}

#[test]
fn predicate_roles_lower_through_existing_terms_and_exact_core_values() {
    let core = value_to_language_core(&language(Some(role()))).expect("canonical role lowers");
    let predicate = core.theory.observations[0]
        .predicate_role
        .as_ref()
        .expect("explicit role");
    assert_eq!(predicate.input_constructor, "Call");
    assert!(predicate.accepting.variables.is_empty());
    assert_eq!(predicate.accepting.terms[0].sort, "Expr");
    let value = language_core_to_value(&core).expect("exact value encoding");
    assert_eq!(value_to_language_core(&value).expect("exact decoding"), core);
    let omitted = value_to_language_core(&language(None)).expect("omission stays supported");
    assert!(omitted.theory.observations[0].predicate_role.is_none());
    assert_eq!(core.grammar_fingerprint(), omitted.grammar_fingerprint());
    assert_ne!(core.theory_fingerprint(), omitted.theory_fingerprint());
}

#[test]
fn predicate_roles_survive_module_transport_and_bind_module_identity() {
    let module = CanonicalModuleValue {
        name: "Predicates".into(),
        dependencies: Vec::new(),
        exports: vec![CanonicalModuleExport {
            name: "Predicate".into(),
            spec: language(Some(role())),
        }],
    };
    let decoded =
        CanonicalModuleValue::from_rho_value(&module.to_rho_value()).expect("module round trip");
    assert_eq!(decoded, module);
    let core = value_to_language_core(&decoded.exports[0].spec).expect("export role lowers");
    assert!(core.theory.observations[0].predicate_role.is_some());
    let mut omitted = module.clone();
    omitted.exports[0].spec = language(None);
    assert_ne!(module.fingerprint(), omitted.fingerprint());
}

#[test]
fn predicate_roles_reject_missing_fields_unknown_fields_and_free_variables() {
    for malformed in [
        m([("input_constructor", s("Call")), ("accepting", ctor("Yes"))]),
        m([
            ("input_constructor", s("Call")),
            ("accepting", ctor("Yes")),
            ("rejecting", ctor("No")),
            ("truthy", RhoValue::Boolean(true)),
        ]),
        m([
            ("input_constructor", s("Call")),
            ("accepting", s("external")),
            ("rejecting", ctor("No")),
        ]),
        m([
            ("input_constructor", s("Missing")),
            ("accepting", ctor("Yes")),
            ("rejecting", ctor("No")),
        ]),
    ] {
        assert!(value_to_language_core(&language(Some(malformed))).is_err());
    }
}
