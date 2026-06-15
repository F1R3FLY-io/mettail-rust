#![cfg(feature = "calculator")]

use mettail_languages::calculator::CalculatorLanguage;
#[cfg(not(feature = "oracle-ascent"))]
use mettail_runtime::SeedFacts;
use mettail_runtime::{Language, RuntimeBackend};

#[test]
fn generated_language_runtime_backends_are_substrate_neutral() {
    let language = CalculatorLanguage;
    let capabilities = language.metadata().runtime_backends();

    assert!(
        capabilities.is_empty(),
        "raw generated languages must not advertise a production runtime backend"
    );
    let runtime_capabilities = language.runtime_backend_capabilities();

    assert_eq!(language.default_runtime_backend(), None);
    assert!(runtime_capabilities.is_empty());
    assert!(!language.supports_runtime_backend(RuntimeBackend::Ascent));
    assert!(!language.supports_runtime_backend(RuntimeBackend::Dovetail));
    assert!(!language.supports_runtime_backend(RuntimeBackend::RhoMachine));
}

#[cfg(not(feature = "oracle-ascent"))]
#[test]
fn generated_language_ascent_oracle_fails_closed_without_oracle_feature() {
    let language = CalculatorLanguage;
    let term = language
        .parse_term("42")
        .expect("calculator literal should parse without the Ascent oracle");

    let ascent_err = language
        .run_ascent(term.as_ref())
        .expect_err("no-oracle generated languages must not run Ascent");
    assert!(ascent_err.contains("Ascent oracle is disabled for Calculator"), "{ascent_err}");

    let seeded_err = language
        .run_ascent_with_facts(term.as_ref(), &SeedFacts::new())
        .expect_err("seeded no-oracle generated languages must not run Ascent");
    assert!(
        seeded_err.contains("Ascent oracle with seeded facts is disabled for Calculator"),
        "{seeded_err}"
    );

    let report_err = language
        .run_backend_report(RuntimeBackend::Ascent, term.as_ref())
        .expect_err("production report dispatch must never route to Ascent");
    assert!(
        report_err.contains("Ascent report execution for language Calculator is oracle-only"),
        "{report_err}"
    );

    let seeded_report_err = language
        .run_backend_report_with_facts(RuntimeBackend::Ascent, term.as_ref(), &SeedFacts::new())
        .expect_err("seeded production report dispatch must never route to Ascent");
    assert!(
        seeded_report_err
            .contains("seeded Ascent report execution for language Calculator is oracle-only"),
        "{seeded_report_err}"
    );

    let default_err = language
        .run_default_backend_report(term.as_ref())
        .expect_err("raw generated languages must not fabricate a default backend");
    assert!(
        default_err.contains("language Calculator does not advertise a default runtime backend"),
        "{default_err}"
    );
}
