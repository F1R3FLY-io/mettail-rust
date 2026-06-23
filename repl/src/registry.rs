use anyhow::Result;
use mettail_runtime::{Language, RuntimeBackend, RuntimeBackendCapability};
use std::collections::HashMap;

// Raw generated language implementations are registered only on the Dovetail-only fallback build
// (no f1r3node) — there RhoCalc/Calculator, whose production default is the Rho machine, register
// raw. On the default `rho-languages` build every language is wrapped via `crate::rho_backends`.
#[cfg(all(feature = "bundled-languages", not(feature = "rho-languages")))]
use mettail_languages::calculator::CalculatorLanguage;
#[cfg(all(feature = "bundled-languages", not(feature = "rho-languages")))]
use mettail_languages::rhocalc::RhoCalcLanguage;

/// Registry of available languages
pub struct LanguageRegistry {
    languages: HashMap<String, Box<dyn Language>>,
}

/// Runtime-facing summary for one registered language value.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RegisteredLanguageInfo {
    pub name: String,
    pub default_backend: Option<RuntimeBackend>,
    pub runtime_backends: Vec<RuntimeBackendCapability>,
}

impl LanguageRegistry {
    /// Create a new registry
    pub fn new() -> Self {
        Self { languages: HashMap::new() }
    }

    /// Register a language
    pub fn register(&mut self, language: Box<dyn Language>) {
        let name = language.name().to_lowercase();
        self.languages.insert(name, language);
    }

    /// Get a language by name (case-insensitive)
    pub fn get(&self, name: &str) -> Result<&dyn Language> {
        self.languages
            .get(&name.to_lowercase())
            .map(|b| b.as_ref())
            .ok_or_else(|| anyhow::anyhow!("Language '{}' not found", name))
    }

    /// List all available languages
    pub fn list(&self) -> Vec<&str> {
        self.languages.values().map(|l| l.name()).collect()
    }

    /// List all available languages with the runtime backend view exposed by
    /// the concrete registered value.
    pub fn list_with_runtime(&self) -> Vec<RegisteredLanguageInfo> {
        let mut info = self
            .languages
            .values()
            .map(|language| RegisteredLanguageInfo {
                name: language.name().to_string(),
                default_backend: language.selected_default_runtime_backend(),
                runtime_backends: language.runtime_backend_capabilities(),
            })
            .collect::<Vec<_>>();
        info.sort_by(|left, right| left.name.cmp(&right.name));
        info
    }

    /// Check if a language exists (case-insensitive)
    pub fn contains(&self, name: &str) -> bool {
        self.languages.contains_key(&name.to_lowercase())
    }
}

impl Default for LanguageRegistry {
    fn default() -> Self {
        Self::new()
    }
}

/// Build the default registry with all available languages, each wrapped in its checked production
/// runtime backend so `exec` works (a raw `language!` value advertises no default backend).
pub fn build_registry() -> Result<LanguageRegistry> {
    // Default build: every bundled language wrapped in its production backend (Dovetail for
    // Lambda/Ambient; two-stage Dovetail+Rholang for RhoCalc/Calculator).
    #[cfg(feature = "rho-languages")]
    {
        let mut registry = LanguageRegistry::new();
        registry.register(crate::rho_backends::lambda_backed()?);
        registry.register(crate::rho_backends::ambient_backed()?);
        registry.register(crate::rho_backends::rhocalc_backed()?);
        registry.register(crate::rho_backends::calculator_backed()?);
        Ok(registry)
    }

    // Dovetail-only build (no f1r3node): Lambda/Ambient still get the generic Dovetail backend;
    // RhoCalc/Calculator (whose production default is the Rho machine) register raw.
    #[cfg(all(feature = "bundled-languages", not(feature = "rho-languages")))]
    {
        let mut registry = LanguageRegistry::new();
        registry.register(crate::rho_backends::lambda_backed()?);
        registry.register(crate::rho_backends::ambient_backed()?);
        registry.register(Box::new(CalculatorLanguage));
        registry.register(Box::new(RhoCalcLanguage));
        Ok(registry)
    }

    #[cfg(not(feature = "bundled-languages"))]
    {
        Ok(LanguageRegistry::new())
    }
}
