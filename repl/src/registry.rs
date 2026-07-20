use anyhow::Result;
use mettail_runtime::{Language, RuntimeBackend, RuntimeBackendCapability};
use std::collections::HashMap;

// Raw generated language implementations are registered only on the Dovetail-only non-Rho build
// (no f1r3node). There RhoCalc/Calculator, whose production default is the Rho machine, register
// raw because no Rho runtime is linked. On the default `rho-languages` build every language is
// wrapped via `crate::rho_backends`.
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
    // Default build: every bundled language wrapped in its production two-stage
    // Dovetail+Rholang backend (A-S5.6: Lambda/Ambient exec on the in-Rho quiescence driver;
    // RhoCalc/Calculator on COMM / scalar dataflow; A-S6: SwapDemo AND every rho_net demo on
    // the in-Rho locate-all set-automaton match — the runtime mandate is registry-wide, so at
    // runtime Dovetail handles only semantic predicates, labeled step introspection, and lazy
    // deferral reports).
    #[cfg(feature = "rho-languages")]
    {
        let mut registry = LanguageRegistry::new();
        registry.register(crate::rho_backends::lambda_backed()?);
        registry.register(crate::rho_backends::ambient_backed()?);
        registry.register(crate::rho_backends::rhocalc_backed()?);
        registry.register(crate::rho_backends::calculator_backed()?);
        registry.register(crate::rho_backends::swapdemo_backed()?);
        // A-S6 (USER decision 2026-07-20): the demo languages flip to the machine too.
        registry.register(crate::rho_backends::acdemo_backed()?);
        registry.register(crate::rho_backends::acbagdemo_backed()?);
        registry.register(crate::rho_backends::nlacdemo_backed()?);
        registry.register(crate::rho_backends::ambdemo_backed()?);
        registry.register(crate::rho_backends::ambnewdemo_backed()?);
        registry.register(crate::rho_backends::inoutdemo_backed()?);
        registry.register(crate::rho_backends::commdemo_backed()?);
        registry.register(crate::rho_backends::ctxdemo_backed()?);
        registry.register(crate::rho_backends::bicongdemo_backed()?);
        registry.register(crate::rho_backends::lambdademo_backed()?);
        registry.register(crate::rho_backends::nativedemo_backed()?);
        registry.register(crate::rho_backends::nativefolddemo_backed()?);
        Ok(registry)
    }

    // Dovetail-only build (no f1r3node): Lambda/Ambient (A-S5.6) and SwapDemo + the 12 rho_net
    // demos (A-S6) register through the decision-(4) fail-closed wrapper (parse/introspection
    // work; exec errors pointing at the rho build — their production semantics run ONLY on the
    // Rho machine, no dual runtime path remains); RhoCalc/Calculator (whose production default
    // is the Rho machine but which keep a raw parse/introspection surface here) register raw.
    #[cfg(all(feature = "bundled-languages", not(feature = "rho-languages")))]
    {
        let mut registry = LanguageRegistry::new();
        registry.register(crate::rho_backends::lambda_backed()?);
        registry.register(crate::rho_backends::ambient_backed()?);
        registry.register(Box::new(CalculatorLanguage));
        registry.register(Box::new(RhoCalcLanguage));
        registry.register(crate::rho_backends::swapdemo_backed()?);
        registry.register(crate::rho_backends::acdemo_backed()?);
        registry.register(crate::rho_backends::acbagdemo_backed()?);
        registry.register(crate::rho_backends::nlacdemo_backed()?);
        registry.register(crate::rho_backends::ambdemo_backed()?);
        registry.register(crate::rho_backends::ambnewdemo_backed()?);
        registry.register(crate::rho_backends::inoutdemo_backed()?);
        registry.register(crate::rho_backends::commdemo_backed()?);
        registry.register(crate::rho_backends::ctxdemo_backed()?);
        registry.register(crate::rho_backends::bicongdemo_backed()?);
        registry.register(crate::rho_backends::lambdademo_backed()?);
        registry.register(crate::rho_backends::nativedemo_backed()?);
        registry.register(crate::rho_backends::nativefolddemo_backed()?);
        Ok(registry)
    }

    #[cfg(not(feature = "bundled-languages"))]
    {
        Ok(LanguageRegistry::new())
    }
}
