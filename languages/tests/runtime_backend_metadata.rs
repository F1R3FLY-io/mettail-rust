#![cfg(feature = "calculator")]

use mettail_languages::calculator::CalculatorLanguage;
use mettail_runtime::{Language, RuntimeBackend};

#[test]
fn generated_language_runtime_backends_are_metadata_driven() {
    let language = CalculatorLanguage;
    let capabilities = language.metadata().runtime_backends();

    assert_eq!(capabilities.len(), 1);
    assert_eq!(capabilities[0].backend, RuntimeBackend::Ascent);
    assert!(capabilities[0].is_default);
    assert_eq!(capabilities[0].evidence_refs, &["mettail-macros:generated-ascent-runner"]);

    let metadata_default = capabilities
        .iter()
        .find(|capability| capability.is_default)
        .map(|capability| capability.backend)
        .expect("generated languages must advertise a default backend");
    let runtime_capabilities = language.runtime_backend_capabilities();

    assert_eq!(language.default_runtime_backend(), metadata_default);
    assert_eq!(runtime_capabilities.len(), 1);
    assert_eq!(runtime_capabilities[0].backend, RuntimeBackend::Ascent);
    assert!(runtime_capabilities[0].is_default);
    assert_eq!(
        runtime_capabilities[0].evidence_refs,
        vec!["mettail-macros:generated-ascent-runner".to_string()]
    );
    assert!(language.supports_runtime_backend(RuntimeBackend::Ascent));
    assert!(!language.supports_runtime_backend(RuntimeBackend::Dovetail));
    assert!(!language.supports_runtime_backend(RuntimeBackend::RhoMachine));
}
