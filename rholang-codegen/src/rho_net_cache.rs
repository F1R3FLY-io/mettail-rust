//! A-S2 (D-stage demotion) — per-process memoization of the in-Rho compilation artifacts.
//!
//! Before this stage, EVERY generated Rho-net invocation body re-derived the whole in-Rho
//! compilation pipeline per exec: `reconstruct_language_def(source)` (a full `syn` parse +
//! composition + auto-injection augmentation) followed by `compile_in_rho_matching_ruleset`
//! (pattern conversion + set-automaton compilation). Those artifacts are a pure function of the
//! generated `definition_source`, so [`cached_in_rho_artifacts`] computes them ONCE per source
//! and hands out shared [`Arc`] handles — the generated bodies (report-free AND report-carrying
//! fallback) swap their reconstruct+compile preamble for this getter.
//!
//! ## Cache shape (and the one deviation from the design sketch)
//!
//! The design sketch called for a single process-global
//! `LazyLock<Mutex<HashMap<u64, Arc<CompiledInRhoArtifacts>>>>`. That shape is UNSOUND here:
//! [`LanguageDef`] (and [`InRhoMatchingRuleset`] via its nested-structural-AC shapes, which
//! store an AST `Pattern`) hold `syn`/`proc-macro2` values, and every `proc-macro2` type is
//! deliberately `!Send + !Sync` (`ProcMacroAutoTraits = PhantomData<Rc<()>>`). The marker is not
//! a formality: `proc-macro2` token streams are `Rc`-backed (`RcVec`), so a `LanguageDef`
//! carrying any raw token payload (a `syn::Expr::Macro`/`Verbatim` inside a guard, a `logic`
//! block, …) shares NON-ATOMIC refcounts — cloning or dropping such a value from two threads is
//! a data race, so an `unsafe impl Send/Sync` wrapper would be undefined behavior, not a
//! workaround. The cache is therefore a **thread-local** map with the SAME key scheme (the
//! `u64` hash of the source, collision-verified against the stored source) and the same
//! `Arc<CompiledInRhoArtifacts>` value shape. Every observable property the process-global
//! sketch wanted is preserved:
//!
//! - **memoization**: an invocation compiler runs on the caller's thread (the REPL / test
//!   thread), so repeated execs hit the same thread's cache — the per-exec reconstruct+compile
//!   is gone where it mattered;
//! - **thread-safety**: by construction — no shared mutable state crosses threads at all;
//! - **determinism**: the derivation is a pure function of the source, so every thread's
//!   artifacts agree (asserted by the unit tests below on the `Send`-safe derived data).

use std::cell::RefCell;
use std::collections::HashMap;
use std::hash::{DefaultHasher, Hash, Hasher};
use std::sync::Arc;

use mettail_ast::language::LanguageDef;
use models::rhoapi::Par;

use crate::lower::{lower_language_def, RhoLowering};
use crate::reconstruct_language_def;
use crate::rho_net::RhoNetProgram;
use crate::rho_net_ruleset::{compile_in_rho_matching_ruleset, InRhoMatchingRuleset};

/// The in-Rho compilation artifacts of one generated `definition_source`, derived once and
/// shared by every generated Rho-net invocation body on the same thread.
///
/// All four artifact fields are pure functions of [`definition_source`](Self::definition_source)
/// (the collision-verification key): re-deriving them yields equal data, which is what makes the
/// memoization observationally transparent.
pub struct CompiledInRhoArtifacts {
    /// The EXACT source the artifacts were derived from — the collision-verification key for
    /// the hashed cache slot (a verified mismatch recomputes without caching, so a `u64` hash
    /// collision can never alias two languages' artifacts).
    pub definition_source: String,
    /// The reconstructed augmented [`LanguageDef`] — the same value
    /// `reconstruct_language_def(source)` returns (composition applied + auto-injection rules
    /// appended), i.e. the def the `definition_fingerprint` is computed over.
    pub def: LanguageDef,
    /// The scalar/contract lowering of [`def`](Self::def) (`lower_language_def`).
    pub lowered: RhoLowering,
    /// The in-Rho matching ruleset of [`def`](Self::def) (`compile_in_rho_matching_ruleset`) —
    /// the positional automaton + dispatch families + deferrals the match drivers and the
    /// A-S2 static gate consume.
    pub ruleset: InRhoMatchingRuleset,
    /// The installable Rho-net σ-receiver program `Par` (every materialized contract
    /// parallel-composed), or the FAIL-CLOSED install diagnostic. Carried as a `Result` because
    /// the install surface is fail-closed per language (a language with unlowered/flagged rule
    /// families has no complete installed program) while the match/ruleset artifacts above
    /// remain valid — a consumer that needs the installed program unwraps this field and
    /// inherits exactly the install-time error it would have produced itself.
    pub installed_par: Result<Par, String>,
}

impl CompiledInRhoArtifacts {
    /// Derive the artifacts from `definition_source` (the uncached pure derivation the cache
    /// memoizes).
    fn derive(definition_source: &str) -> Result<Self, String> {
        let def = reconstruct_language_def(definition_source).map_err(|err| {
            format!("definition source did not reconstruct for in-Rho artifacts: {err}")
        })?;
        let lowered = lower_language_def(&def);
        let ruleset = compile_in_rho_matching_ruleset(&def);
        let installed_par = RhoNetProgram::from_language_def(&def, &lowered)
            .lower_to_par(&def, &lowered)
            .installed_program_par()
            .map_err(|err| format!("in-Rho installed program is fail-closed: {err:?}"));
        Ok(Self {
            definition_source: definition_source.to_string(),
            def,
            lowered,
            ruleset,
            installed_par,
        })
    }
}

thread_local! {
    /// The per-thread artifact cache: `u64` source hash → shared artifacts. See the module
    /// docs for why this is `thread_local!` rather than a process-global
    /// `LazyLock<Mutex<…>>` (soundness: `proc-macro2` data is genuinely not thread-safe).
    static IN_RHO_ARTIFACTS: RefCell<HashMap<u64, Arc<CompiledInRhoArtifacts>>> =
        RefCell::new(HashMap::new());
}

/// Hash a definition source to its cache key.
fn source_hash(definition_source: &str) -> u64 {
    let mut hasher = DefaultHasher::new();
    definition_source.hash(&mut hasher);
    hasher.finish()
}

/// The memoized in-Rho compilation artifacts for `definition_source`: on the first call per
/// thread this reconstructs the [`LanguageDef`], lowers it, compiles the in-Rho matching
/// ruleset, and materializes the installable σ-receiver program; every subsequent call returns
/// the same [`Arc`] handle. A reconstruction failure is NOT cached (each call retries), so a
/// transiently observed error cannot poison the slot.
///
/// The generated Rho-net invocation bodies (`rho_net_match_invocation_to`, the report-carrying
/// `_from_dovetail_to*` fallbacks, and the contextual driver) call this instead of re-running
/// `reconstruct_language_def` + `compile_in_rho_matching_ruleset` per invocation.
pub fn cached_in_rho_artifacts(
    definition_source: &str,
) -> Result<Arc<CompiledInRhoArtifacts>, String> {
    let key = source_hash(definition_source);
    // Fast path: a cached slot whose stored source VERIFIES equal (collision guard).
    let hit = IN_RHO_ARTIFACTS.with(|cache| {
        cache.borrow().get(&key).and_then(|artifacts| {
            if artifacts.definition_source == definition_source {
                Some(Arc::clone(artifacts))
            } else {
                None
            }
        })
    });
    if let Some(artifacts) = hit {
        return Ok(artifacts);
    }

    let artifacts = Arc::new(CompiledInRhoArtifacts::derive(definition_source)?);
    IN_RHO_ARTIFACTS.with(|cache| {
        let mut cache = cache.borrow_mut();
        match cache.get(&key) {
            // A verified `u64` collision (astronomically unlikely): keep the existing slot and
            // hand back the freshly derived artifacts uncached — correct, never aliased.
            Some(existing) if existing.definition_source != definition_source => {},
            _ => {
                cache.insert(key, Arc::clone(&artifacts));
            },
        }
    });
    Ok(artifacts)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The SwapDemo fragment (mirrors `rho_net_ruleset::tests::swap_demo_def`) as a SOURCE
    /// string — the cache is keyed by source text, exactly as the generated bodies call it
    /// (with `metadata().definition_source()`).
    const SWAP_SOURCE: &str = r#"
        name: SwapCacheGen,
        types { Proc }
        terms {
            A . |- "A" : Proc ;
            B . |- "B" : Proc ;
            Pair . x:Proc, y:Proc |- "pair" "(" x "," y ")" : Proc ;
            Swap . x:Proc, y:Proc |- "swap" "(" x "," y ")" : Proc ;
        }
        equations {}
        rewrites { SwapStep . |- (Swap x y) ~> (Pair y x) ; }
    "#;

    /// A second, distinct source (different name + rewrite direction) — must occupy its own
    /// cache slot.
    const OTHER_SOURCE: &str = r#"
        name: OtherCacheGen,
        types { Proc }
        terms {
            A . |- "A" : Proc ;
            B . |- "B" : Proc ;
            Pair . x:Proc, y:Proc |- "pair" "(" x "," y ")" : Proc ;
            Swap . x:Proc, y:Proc |- "swap" "(" x "," y ")" : Proc ;
        }
        equations {}
        rewrites { PairStep . |- (Pair x y) ~> (Swap y x) ; }
    "#;

    #[test]
    fn same_source_returns_the_same_arc() {
        // Determinism + memoization on one thread: the second call is the SAME allocation
        // (pointer-equal), not merely an equal value — the reconstruct+compile ran once.
        let first = cached_in_rho_artifacts(SWAP_SOURCE).expect("SwapDemo artifacts derive");
        let second = cached_in_rho_artifacts(SWAP_SOURCE).expect("cached artifacts return");
        assert!(Arc::ptr_eq(&first, &second), "the cache must return the memoized Arc");
        assert_eq!(first.definition_source, SWAP_SOURCE);
        assert_eq!(first.def.name.to_string(), "SwapCacheGen");
        assert_eq!(first.lowered.language_name(), "SwapCacheGen");
        assert!(first.ruleset.deferred.is_empty(), "SwapDemo defers nothing");
        assert!(
            first.installed_par.is_ok(),
            "the SwapDemo σ-receiver program installs: {:?}",
            first.installed_par.as_ref().err()
        );
    }

    #[test]
    fn distinct_sources_get_distinct_artifacts() {
        let swap = cached_in_rho_artifacts(SWAP_SOURCE).expect("SwapDemo artifacts derive");
        let other = cached_in_rho_artifacts(OTHER_SOURCE).expect("other artifacts derive");
        assert!(!Arc::ptr_eq(&swap, &other), "distinct sources must not alias a slot");
        assert_ne!(
            swap.ruleset.language_fingerprint, other.ruleset.language_fingerprint,
            "distinct definitions have distinct fingerprints"
        );
    }

    #[test]
    fn a_broken_source_errors_and_is_not_cached() {
        let err = match cached_in_rho_artifacts("not a language definition") {
            Err(err) => err,
            Ok(_) => panic!("garbage must not derive artifacts"),
        };
        assert!(
            err.contains("did not reconstruct"),
            "the error names the reconstruction failure: {err}"
        );
        // The failure did not poison a slot: a valid source still derives.
        cached_in_rho_artifacts(SWAP_SOURCE).expect("valid source still derives after a failure");
    }

    #[test]
    fn concurrent_threads_agree_on_the_derived_artifacts() {
        // Thread-safety + cross-thread determinism: N threads derive the same source
        // concurrently; every thread succeeds (no shared mutable state — the cache is
        // per-thread by construction) and the `Send`-safe DERIVED data (fingerprint, deferral
        // labels, installed-program bytes) is identical everywhere. The `Arc` itself is
        // deliberately NOT sent across threads: `LanguageDef` is `!Send` (proc-macro2), which
        // is exactly why the cache is thread-local — see the module docs.
        let handles: Vec<_> = (0..4)
            .map(|_| {
                std::thread::spawn(|| {
                    let artifacts = cached_in_rho_artifacts(SWAP_SOURCE)
                        .expect("every thread derives the artifacts");
                    let again = cached_in_rho_artifacts(SWAP_SOURCE)
                        .expect("every thread memoizes its own slot");
                    assert!(Arc::ptr_eq(&artifacts, &again));
                    let deferred: Vec<String> = artifacts
                        .ruleset
                        .deferred
                        .iter()
                        .map(|entry| entry.rule_label.clone())
                        .collect();
                    let installed = artifacts
                        .installed_par
                        .as_ref()
                        .map(|par| format!("{par:?}"))
                        .map_err(Clone::clone);
                    (artifacts.ruleset.language_fingerprint.clone(), deferred, installed)
                })
            })
            .collect();

        let results: Vec<_> = handles
            .into_iter()
            .map(|handle| handle.join().expect("no derivation thread panics"))
            .collect();
        let baseline = &results[0];
        for result in &results[1..] {
            assert_eq!(result, baseline, "every thread derives identical artifacts");
        }
    }
}
