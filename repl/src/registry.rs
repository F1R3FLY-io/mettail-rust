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
/// An FLT surface `` L`…` `` names its guest language by a REQUIRED reserved tag `L` (e.g. `lambda`);
/// this resolver maps that tag to the guest [`Language`] value and its stable
/// `definition_fingerprint()` — the `fp` every public FLT reflector
/// ([`mettail_rholang_codegen::reflect_flt_pattern`] et al.) keys its unforgeable reflected tags on.
/// Because the tag is REQUIRED, exactly one grammar parses an FLT body, so the registry's
/// first-match composition is moot (design §Registry).
///
/// The reserved tag need not equal the language NAME (the registry key). A tag alias
/// ([`register_tag`](Self::register_tag)) maps a surface tag (e.g. `lambda`) to a guest language name
/// (e.g. `Lambda`); [`resolve`](Self::resolve) falls back to treating the tag AS a language name
/// when no alias is registered.
pub struct FltResolver<'a> {
    registry: &'a LanguageRegistry,
    tag_aliases: HashMap<String, String>,
    /// Tag → the guest FLT reflector (`Box<dyn FltReflect>`, a raw `language!` value that reflects a
    /// guest FLT template body into a [`GroundTerm`](mettail_rholang_codegen::GroundTerm) with
    /// stable `^free(name)` holes). Because `FltReflect: Language`, this SAME value also yields the
    /// guest's `name()`/fingerprint, so the reflection and the reflected-tag fingerprint stay
    /// coherent (design §Stage-4). Present only when the codegen reflector surface is linked.
    #[cfg(feature = "rho-languages")]
    guests: HashMap<String, Box<dyn mettail_rholang_codegen::FltReflect>>,
}

impl<'a> FltResolver<'a> {
    /// A resolver over `registry` with no tag aliases (every tag resolves as a language name).
    pub fn new(registry: &'a LanguageRegistry) -> Self {
        Self {
            registry,
            tag_aliases: HashMap::new(),
            #[cfg(feature = "rho-languages")]
            guests: HashMap::new(),
        }
    }

    /// A resolver pre-seeded with the bundled FLT surface-tag aliases (the demo's `lambda` → `Lambda`)
    /// and — where the codegen reflector surface is linked — the matching guest reflectors.
    pub fn with_default_aliases(registry: &'a LanguageRegistry) -> Self {
        let mut resolver = Self::new(registry);
        resolver.register_tag("lambda", "Lambda");
        #[cfg(feature = "rho-languages")]
        resolver.register_guest("lambda", Box::new(mettail_languages::lambda::LambdaLanguage));
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
            anyhow::anyhow!(
                "no guest language registered for FLT tag '{tag}' (resolved name '{key}')"
            )
        })?;
        let fingerprint = language
            .metadata()
            .definition_fingerprint()
            .ok_or_else(|| {
                anyhow::anyhow!(
                    "guest language '{key}' (FLT tag '{tag}') advertises no definition fingerprint"
                )
            })?;
        Ok((language, fingerprint))
    }
}

/// The FLT guest-reflection surface — present only when the codegen reflector
/// ([`mettail_rholang_codegen::FltReflect`]) is linked (`rho-languages`).
#[cfg(feature = "rho-languages")]
impl<'a> FltResolver<'a> {
    /// Register a guest FLT `reflector` (a raw `language!` value) under a surface `tag`
    /// (case-insensitive). The reflector reflects a guest FLT template body into a
    /// [`GroundTerm`](mettail_rholang_codegen::GroundTerm) and — via its
    /// [`Language`](mettail_runtime::Language) supertrait — advertises the guest fingerprint the
    /// reflection is keyed on.
    pub fn register_guest(
        &mut self,
        tag: impl Into<String>,
        reflector: Box<dyn mettail_rholang_codegen::FltReflect>,
    ) {
        self.guests.insert(tag.into().to_lowercase(), reflector);
    }

    /// Parse `body` in the guest surface named by FLT `tag` and reflect it into the guest
    /// [`GroundTerm`](mettail_rholang_codegen::GroundTerm) (holes as stable `^free(name)` leaves),
    /// returning it paired with the guest's definition fingerprint — the `fp` the public FLT
    /// reflectors ([`reflect_flt_pattern`](mettail_rholang_codegen::reflect_flt_pattern) /
    /// [`reflect_flt_construction`](mettail_rholang_codegen::reflect_flt_construction)) key their
    /// unforgeable reflected tags on.
    ///
    /// Dispatches through the registered `&dyn FltReflect` guest; fails closed when no guest is
    /// registered for the tag, the guest advertises no fingerprint, or the body does not reflect.
    pub fn parse_and_reflect_flt(
        &self,
        tag: &str,
        body: &str,
    ) -> Result<(mettail_rholang_codegen::GroundTerm, &'static str)> {
        let guest = self
            .guests
            .get(&tag.to_lowercase())
            .ok_or_else(|| anyhow::anyhow!("no FLT guest reflector registered for tag '{tag}'"))?;
        // `FltReflect: Language`, so the reflector value also carries the guest fingerprint.
        let fingerprint = guest.metadata().definition_fingerprint().ok_or_else(|| {
            anyhow::anyhow!("FLT guest for tag '{tag}' advertises no definition fingerprint")
        })?;
        let ground = guest
            .parse_and_reflect_flt(body)
            .map_err(|err| anyhow::anyhow!("FLT reflection for tag '{tag}' failed: {err}"))?;
        Ok((ground, fingerprint))
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
        // Task #11 (extended 2026-07-26) — DE-PRODUCTIONIZED, per USER decision: "I don't
        // want REPL integration for the non-production grammars!" SwapDemo and the eleven
        // rho_net demonstration grammars are NOT production languages, so they are no longer
        // registry members and are no longer reachable from the REPL at all. That
        // unreachability is the DESIRED OUTCOME, not a cost: the A-S6 in-Rho firing each
        // wrapper exposed interactively stays covered end-to-end by the corresponding
        // `rholang-runtime/tests/rho_net_*_firing.rs`, which drives the same machine path
        // directly. Commented out, not deleted, so the A-S6 registry shape stays legible.
        // registry.register(crate::rho_backends::swapdemo_backed()?);
        // // A-S6 (USER decision 2026-07-20): the demo languages flip to the machine too.
        // registry.register(crate::rho_backends::acdemo_backed()?);
        // registry.register(crate::rho_backends::acbagdemo_backed()?);
        // registry.register(crate::rho_backends::nlacdemo_backed()?);
        // registry.register(crate::rho_backends::ambdemo_backed()?);
        // registry.register(crate::rho_backends::ambnewdemo_backed()?);
        // registry.register(crate::rho_backends::inoutdemo_backed()?);
        // registry.register(crate::rho_backends::commdemo_backed()?);
        // registry.register(crate::rho_backends::ctxdemo_backed()?);
        // registry.register(crate::rho_backends::bicongdemo_backed()?);
        // registry.register(crate::rho_backends::lambdademo_backed()?);
        // registry.register(crate::rho_backends::nativedemo_backed()?);
        // Task #11 (extended 2026-07-26) — DE-PRODUCTIONIZED, per USER decision: "I don't
        // want REPL integration for the non-production grammars!" NativeFoldDemo is a
        // DEMONSTRATION grammar whose definition moved to
        // `languages/tests/definitions/nativefolddemo.rs`; it is no longer a library module,
        // so there is nothing to register. Commented out, not deleted.
        // registry.register(crate::rho_backends::nativefolddemo_backed()?);
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
        // Task #11 (extended 2026-07-26) — DE-PRODUCTIONIZED, per USER decision: "I don't
        // want REPL integration for the non-production grammars!" SwapDemo and the eleven
        // rho_net demonstration grammars are NOT production languages, so they are no longer
        // registry members and are no longer reachable from the REPL at all. That
        // unreachability is the DESIRED OUTCOME, not a cost: the A-S6 in-Rho firing each
        // wrapper exposed interactively stays covered end-to-end by the corresponding
        // `rholang-runtime/tests/rho_net_*_firing.rs`, which drives the same machine path
        // directly. Commented out, not deleted, so the A-S6 registry shape stays legible.
        // registry.register(crate::rho_backends::swapdemo_backed()?);
        // registry.register(crate::rho_backends::acdemo_backed()?);
        // registry.register(crate::rho_backends::acbagdemo_backed()?);
        // registry.register(crate::rho_backends::nlacdemo_backed()?);
        // registry.register(crate::rho_backends::ambdemo_backed()?);
        // registry.register(crate::rho_backends::ambnewdemo_backed()?);
        // registry.register(crate::rho_backends::inoutdemo_backed()?);
        // registry.register(crate::rho_backends::commdemo_backed()?);
        // registry.register(crate::rho_backends::ctxdemo_backed()?);
        // registry.register(crate::rho_backends::bicongdemo_backed()?);
        // registry.register(crate::rho_backends::lambdademo_backed()?);
        // registry.register(crate::rho_backends::nativedemo_backed()?);
        // Task #11 (extended 2026-07-26) — DE-PRODUCTIONIZED, per USER decision: "I don't
        // want REPL integration for the non-production grammars!" NativeFoldDemo is a
        // DEMONSTRATION grammar whose definition moved to
        // `languages/tests/definitions/nativefolddemo.rs`; it is no longer a library module,
        // so there is nothing to register. Commented out, not deleted.
        // registry.register(crate::rho_backends::nativefolddemo_backed()?);
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

    /// GATE (Phase 2 Stage 4): the FLT tag `lambda` resolves to the Lambda language and its Phase-1
    /// definition fingerprint; the tag is also resolvable AS the language name, and an unknown tag
    /// fails closed.
    #[test]
    fn flt_resolver_resolves_the_lambda_tag_to_its_fingerprint() {
        let registry = build_registry().expect("the production registry builds");
        let resolver = FltResolver::with_default_aliases(&registry);

        let (language, fingerprint) = resolver
            .resolve("lambda")
            .expect("the `lambda` tag resolves");
        assert_eq!(language.name(), "Lambda", "the `lambda` tag resolves to the Lambda language");
        assert_eq!(
            fingerprint, "mettail-langdef-v1:6ef0c40636bb0bca",
            "the resolved fingerprint is the Phase-1 Lambda definition fingerprint"
        );

        // The tag is also resolvable directly as the (case-insensitive) language name.
        let (_, by_name) = resolver
            .resolve("Lambda")
            .expect("`Lambda` resolves as a name");
        assert_eq!(by_name, fingerprint, "resolving by name yields the same fingerprint");

        // An unknown tag fails closed.
        assert!(resolver.resolve("not-a-language").is_err(), "an unknown FLT tag fails closed");
    }

    /// THE Stage-4 gate: `parse_and_reflect_flt("lambda", "(f, lam a. lam b. a)")` — the guest surface
    /// of `App($f, K)` — reflects to `App(^free(f), K)` with a STABLE `^free(f)` hole leaf (the
    /// moniker `pretty_name` "f", NOT the reflector's `format!("{:?}", fv)` debug string), paired
    /// with the Lambda definition fingerprint.
    #[test]
    fn flt_resolver_parses_and_reflects_the_lambda_app_template() {
        use mettail_rholang_codegen::{
            GroundTerm, BOUND_VAR_REFLECT_LABEL, FREE_VAR_REFLECT_LABEL, LAMBDA_REFLECT_LABEL,
            PEANO_SUCC_REFLECT_LABEL, PEANO_ZERO_REFLECT_LABEL,
        };
        mettail_runtime::clear_var_cache();
        let registry = build_registry().expect("the production registry builds");
        let resolver = FltResolver::with_default_aliases(&registry);

        let (ground, fingerprint) = resolver
            .parse_and_reflect_flt("lambda", "(f, lam a. lam b. a)")
            .expect("the `lambda` FLT template `App($f, K)` reflects");
        assert_eq!(
            fingerprint, "mettail-langdef-v1:6ef0c40636bb0bca",
            "the reflection is paired with the Lambda definition fingerprint"
        );

        // Expected `App(^free(f), K)` with `K = lam a. lam b. a = Lam(Lam(^bound(1)))`.
        let n = GroundTerm::nullary;
        let node = GroundTerm::new;
        let g_free_f = node(FREE_VAR_REFLECT_LABEL, vec![n("f")]);
        let peano1 = node(PEANO_SUCC_REFLECT_LABEL, vec![n(PEANO_ZERO_REFLECT_LABEL)]);
        let g_bound1 = node(BOUND_VAR_REFLECT_LABEL, vec![peano1]);
        let g_k = node(LAMBDA_REFLECT_LABEL, vec![node(LAMBDA_REFLECT_LABEL, vec![g_bound1])]);
        let expected = node("App", vec![g_free_f, g_k]);
        assert_eq!(
            ground, expected,
            "App($f, K) reflects to App(^free(f), K) with a stable ^free(f) hole leaf"
        );

        // The hole leaf name is the STABLE pretty_name "f", never a `FreeVar { … }` debug string.
        assert_eq!(
            ground.children[0].children[0].constructor, "f",
            "the ^free hole leaf carries the stable pretty_name, not a Debug string"
        );
    }
}
