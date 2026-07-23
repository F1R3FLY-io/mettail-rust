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

/// FLT (Foreign Language Term) Phase 2 — the tag-keyed resolver over a [`LanguageRegistry`].
///
/// An FLT surface `` L`…` `` names its guest language by a REQUIRED reserved tag `L` (e.g. `lam`);
/// this resolver maps that tag to the guest [`Language`] value and its stable
/// `definition_fingerprint()` — the `fp` every public FLT reflector
/// ([`mettail_rholang_codegen::reflect_flt_pattern`] et al.) keys its unforgeable reflected tags on.
/// Because the tag is REQUIRED, exactly one grammar parses an FLT body, so the registry's
/// first-match composition is moot (design §Registry).
///
/// The reserved tag need not equal the language NAME (the registry key). A tag alias
/// ([`register_tag`](Self::register_tag)) maps a surface tag (e.g. `lam`) to a guest language name
/// (e.g. `Lambda`); [`resolve`](Self::resolve) falls back to treating the tag AS a language name
/// when no alias is registered.
pub struct FltResolver<'a> {
    registry: &'a LanguageRegistry,
    tag_aliases: HashMap<String, String>,
}

impl<'a> FltResolver<'a> {
    /// A resolver over `registry` with no tag aliases (every tag resolves as a language name).
    pub fn new(registry: &'a LanguageRegistry) -> Self {
        Self { registry, tag_aliases: HashMap::new() }
    }

    /// A resolver pre-seeded with the bundled FLT surface-tag aliases (the demo's `lam` → `Lambda`).
    pub fn with_default_aliases(registry: &'a LanguageRegistry) -> Self {
        let mut resolver = Self::new(registry);
        resolver.register_tag("lam", "Lambda");
        resolver
    }

    /// Register an FLT surface `tag` as an alias for a guest `language_name` (both case-insensitive).
    pub fn register_tag(&mut self, tag: impl Into<String>, language_name: impl Into<String>) {
        self.tag_aliases
            .insert(tag.into().to_lowercase(), language_name.into().to_lowercase());
    }

    /// Resolve an FLT surface `tag` to its guest language and definition fingerprint.
    ///
    /// Tries the registered alias first, then the tag AS a (case-insensitive) language name. Fails
    /// closed when no language matches or the resolved language advertises no fingerprint (a
    /// fingerprint is mandatory — the reflected-tag ABI cannot be keyed without it).
    pub fn resolve(&self, tag: &str) -> Result<(&dyn Language, &'static str)> {
        let key = self
            .tag_aliases
            .get(&tag.to_lowercase())
            .cloned()
            .unwrap_or_else(|| tag.to_lowercase());
        let language = self.registry.get(&key).map_err(|_| {
            anyhow::anyhow!("no guest language registered for FLT tag '{tag}' (resolved name '{key}')")
        })?;
        let fingerprint = language.metadata().definition_fingerprint().ok_or_else(|| {
            anyhow::anyhow!(
                "guest language '{key}' (FLT tag '{tag}') advertises no definition fingerprint"
            )
        })?;
        Ok((language, fingerprint))
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

#[cfg(all(test, feature = "rho-languages"))]
mod flt_resolver_tests {
    use super::*;

    /// GATE (Phase 2 Stage 4): the FLT tag `lam` resolves to the Lambda language and its Phase-1
    /// definition fingerprint; the tag is also resolvable AS the language name, and an unknown tag
    /// fails closed.
    #[test]
    fn flt_resolver_resolves_the_lambda_tag_to_its_fingerprint() {
        let registry = build_registry().expect("the production registry builds");
        let resolver = FltResolver::with_default_aliases(&registry);

        let (language, fingerprint) = resolver.resolve("lam").expect("the `lam` tag resolves");
        assert_eq!(language.name(), "Lambda", "the `lam` tag resolves to the Lambda language");
        assert_eq!(
            fingerprint, "mettail-langdef-v1:6ef0c40636bb0bca",
            "the resolved fingerprint is the Phase-1 Lambda definition fingerprint"
        );

        // The tag is also resolvable directly as the (case-insensitive) language name.
        let (_, by_name) = resolver.resolve("Lambda").expect("`Lambda` resolves as a name");
        assert_eq!(by_name, fingerprint, "resolving by name yields the same fingerprint");

        // An unknown tag fails closed.
        assert!(resolver.resolve("not-a-language").is_err(), "an unknown FLT tag fails closed");
    }
}
