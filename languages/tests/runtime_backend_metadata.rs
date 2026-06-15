#![cfg(feature = "calculator")]

use mettail_languages::calculator::CalculatorLanguage;
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
