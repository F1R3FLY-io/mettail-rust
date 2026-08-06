//! A-S2 (D-stage demotion) — per-process memoization of the in-Rho compilation artifacts,
//! with E-3 T-LAZY demand-driven artifact derivation.
//!
//! Before A-S2, EVERY generated Rho-net invocation body re-derived the whole in-Rho
//! compilation pipeline per exec: `reconstruct_language_def(source)` (a full `syn` parse +
//! composition + auto-injection augmentation) followed by `compile_in_rho_matching_ruleset`
//! (pattern conversion + set-automaton compilation). Those artifacts are a pure function of the
//! generated `definition_source`, so [`cached_in_rho_artifacts`] computes them ONCE per source
//! and hands out shared [`Arc`] handles — the generated bodies (report-free AND report-carrying
//! fallback) swap their reconstruct+compile preamble for this getter.
//!
//! ## E-3 T-LAZY: demand-driven artifact derivation (dead-weight elimination)
//!
//! The A-S2 cache derived all four artifacts EAGERLY on first touch. The E-3 red-team
//! (amendment EM-1) established that the eager [`installed_par`](Self::installed_par)
//! emission is UNCONSUMED dead weight: the generated invocation bodies read only
//! [`ruleset`](Self::ruleset) and [`def`](Self::def) (`rho_invocation.rs`), the observe
//! seam unwraps the PLAN-derived program (`backend.rs` →
//! `RhoDefaultBackendPlan::installed_rho_net_program_par`), and no other consumer of this
//! struct's installed-program field exists anywhere — every first touch paid the full
//! `from_language_def → lower_to_par → installed_program_par` emission (the fingerprint-heavy
//! σ-receiver network + subst-TRS + drive + float appends) for an artifact nobody read, while
//! exec paths re-derived the same emission through the plan.
//!
//! T-LAZY therefore keeps `definition_source` + `def` EAGER (reconstruction is the one
//! fallible phase, and `def` anchors every downstream derivation) and makes the other three
//! artifacts independently-forced thunks:
//!
//! * [`ruleset()`](Self::ruleset) — forced by every exec path (the A-S2 static gate + the
//!   match/drive drivers);
//! * [`lowered()`](Self::lowered) — forced only by [`installed_par()`](Self::installed_par)
//!   today (no generated body reads it);
//! * [`installed_par()`](Self::installed_par) — forced by NO production path today (the EM-1
//!   finding); the E-3 bench harness carries the one named forcing consumer so both cell
//!   states stay measured. Whether a production consumer should ever adopt this accessor is
//!   a D3 sign-off question, deliberately not decided here.
//!
//! The cells are `std::cell::OnceCell` (unsync): the cache is `thread_local!` (see below), so
//! the artifacts never cross threads and unsync interior mutability is sound by construction.
//!
//! **INVARIANT (EM-10, tested below):** cell init closures call PURE pipeline functions only,
//! never accessors; the pipeline functions never consult this cache. Forcing order is
//! therefore free (any accessor order derives identical values — `force_order_is_invariant`),
//! re-entrant initialization is impossible by construction (an init closure cannot reach
//! `get_or_init` on any cell), and a panicking derivation leaves its cell UNSET (the
//! `OnceCell` stores only after the closure returns), so a later call retries — consistent
//! with the reconstruction-failure no-poison contract of [`cached_in_rho_artifacts`].
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

use std::cell::{OnceCell, RefCell};
use std::collections::HashMap;
use std::hash::{DefaultHasher, Hash, Hasher};
use std::sync::Arc;

use mettail_ast::language::LanguageDef;
use models::rhoapi::Par;

use crate::lower::{lower_language_def, RhoLowering};
use crate::reconstruct_language_def;
use crate::rho_net::RhoNetProgram;
use crate::rho_net_ruleset::{compile_in_rho_matching_ruleset, InRhoMatchingRuleset};

/// The in-Rho compilation artifacts of one generated `definition_source`, derived on demand
/// and shared by every generated Rho-net invocation body on the same thread.
///
/// All derived artifacts are pure functions of [`definition_source`](Self::definition_source)
/// (the collision-verification key): re-deriving them yields equal data, which is what makes
/// the memoization observationally transparent — and what makes DEMAND-driven derivation
/// (E-3 T-LAZY, module docs) indistinguishable from the old eager derivation on every path
/// that eventually forces the same artifacts.
pub struct CompiledInRhoArtifacts {
    /// The EXACT source the artifacts were derived from — the collision-verification key for
    /// the hashed cache slot (a verified mismatch recomputes without caching, so a `u64` hash
    /// collision can never alias two languages' artifacts).
    pub definition_source: String,
    /// The reconstructed augmented [`LanguageDef`] — the same value
    /// `reconstruct_language_def(source)` returns (composition applied + auto-injection rules
    /// appended), i.e. the def the `definition_fingerprint` is computed over. EAGER: the one
    /// fallible derivation, and the anchor of every lazy cell below.
    pub def: LanguageDef,
    /// LAZY: the scalar/contract lowering of [`def`](Self::def) (`lower_language_def`),
    /// forced by [`lowered()`](Self::lowered).
    lowered: OnceCell<RhoLowering>,
    /// LAZY: the in-Rho matching ruleset of [`def`](Self::def)
    /// (`compile_in_rho_matching_ruleset`) — the positional automaton + dispatch families +
    /// deferrals the match drivers and the A-S2 static gate consume. Forced by
    /// [`ruleset()`](Self::ruleset) on every exec path.
    ruleset: OnceCell<InRhoMatchingRuleset>,
    /// LAZY: the installable Rho-net σ-receiver program `Par` (every materialized contract
    /// parallel-composed), or the FAIL-CLOSED install diagnostic. Stored as a `Result`
    /// because the install surface is fail-closed per language (a language with
    /// unlowered/flagged rule families has no complete installed program) while the
    /// match/ruleset artifacts above remain valid — a consumer that forces
    /// [`installed_par()`](Self::installed_par) inherits exactly the install-time error it
    /// would have produced itself. The stored `Err` is a DETERMINISTIC derivation outcome (a
    /// pure function of the def), so caching it is sound; only panics leave the cell unset.
    installed_par: OnceCell<Result<Par, String>>,
}

impl CompiledInRhoArtifacts {
    /// Derive the EAGER core from `definition_source` (the uncached fallible reconstruction
    /// the cache memoizes); every other artifact is forced on demand through the accessors.
    fn derive(definition_source: &str) -> Result<Self, String> {
        let def = reconstruct_language_def(definition_source).map_err(|err| {
            format!("definition source did not reconstruct for in-Rho artifacts: {err}")
        })?;
        Ok(Self {
            definition_source: definition_source.to_string(),
            def,
            lowered: OnceCell::new(),
            ruleset: OnceCell::new(),
            installed_par: OnceCell::new(),
        })
    }

    /// E-3 T-INCR: assemble artifacts from an INCREMENTAL rule-append derivation
    /// (`crate::rho_net_incremental::extend_in_rho_artifacts`) — the extended
    /// source, the EM-2-repaired extended [`LanguageDef`], and the bypass-derived
    /// [`InRhoMatchingRuleset`], which SEEDS the `ruleset` cell.
    ///
    /// The seeded value is REQUIRED to equal what the cell's own init closure
    /// would derive (`compile_in_rho_matching_ruleset(&def)`) — that is exactly
    /// the T-INCR equivalence obligation, enforced by the fail-closed admission
    /// checks + the debug-build batch cross-check in `rho_net_incremental` and by
    /// the standing E-3 equivalence-gate tests — so memoization transparency (the
    /// EM-10 payoff) is preserved: no observer can distinguish a seeded cell from
    /// a demand-derived one. The `lowered`/`installed_par` cells start UNSET and
    /// derive on demand from `def` through the SAME pure pipeline functions as any
    /// batch-derived artifacts (which is what reduces the incremental installed-Par
    /// byte-equality to LanguageDef identity).
    pub(crate) fn from_incremental_parts(
        definition_source: String,
        def: LanguageDef,
        ruleset: InRhoMatchingRuleset,
    ) -> Self {
        let seeded = OnceCell::new();
        seeded
            .set(ruleset)
            .unwrap_or_else(|_| unreachable!("a freshly created OnceCell accepts one set"));
        Self {
            definition_source,
            def,
            lowered: OnceCell::new(),
            ruleset: seeded,
            installed_par: OnceCell::new(),
        }
    }

    /// The scalar/contract lowering of [`def`](Self::def), derived on first call
    /// (`lower_language_def` — a pure pipeline function, per the EM-10 invariant).
    pub fn lowered(&self) -> &RhoLowering {
        self.lowered.get_or_init(|| lower_language_def(&self.def))
    }

    /// The in-Rho matching ruleset of [`def`](Self::def), derived on first call
    /// (`compile_in_rho_matching_ruleset` — a pure pipeline function, per the EM-10
    /// invariant; it re-runs the lowering pipeline INTERNALLY through
    /// `rho_net_injection_sites` and never consults this cache, so forcing it does NOT
    /// force [`lowered()`](Self::lowered)).
    pub fn ruleset(&self) -> &InRhoMatchingRuleset {
        self.ruleset
            .get_or_init(|| compile_in_rho_matching_ruleset(&self.def))
    }

    /// The installable σ-receiver program of [`def`](Self::def) (or its fail-closed install
    /// diagnostic), derived on first call. Forces [`lowered()`](Self::lowered) FIRST — in
    /// the accessor, OUTSIDE the cell's init closure, so the closure itself calls only the
    /// pure `from_language_def → lower_to_par → installed_program_par` chain (the EM-10
    /// invariant; this also mirrors the old eager derivation order exactly).
    pub fn installed_par(&self) -> &Result<Par, String> {
        let lowered = self.lowered();
        self.installed_par.get_or_init(|| {
            RhoNetProgram::from_language_def(&self.def, lowered)
                .lower_to_par(&self.def, lowered)
                .installed_program_par()
                .map_err(|err| format!("in-Rho installed program is fail-closed: {err:?}"))
        })
    }

    /// Whether the [`lowered()`](Self::lowered) cell has been forced (E-3 cell-state
    /// introspection: the bench harness asserts which arms force which cells, and tests pin
    /// the deferral structure).
    pub fn lowered_forced(&self) -> bool {
        self.lowered.get().is_some()
    }

    /// Whether the [`ruleset()`](Self::ruleset) cell has been forced.
    pub fn ruleset_forced(&self) -> bool {
        self.ruleset.get().is_some()
    }

    /// Whether the [`installed_par()`](Self::installed_par) cell has been forced.
    pub fn installed_par_forced(&self) -> bool {
        self.installed_par.get().is_some()
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
/// thread this reconstructs the [`LanguageDef`] (the eager, fallible core); the lowering,
/// the in-Rho matching ruleset, and the installable σ-receiver program are derived on
/// demand through the [`CompiledInRhoArtifacts`] accessors (E-3 T-LAZY — the eager
/// installed-program emission was unconsumed dead weight, module docs). Every subsequent
/// call returns the same [`Arc`] handle. A reconstruction failure is NOT cached (each call
/// retries), so a transiently observed error cannot poison the slot.
///
/// The generated Rho-net invocation bodies (`rho_net_match_invocation_to`, the
/// report-carrying `_from_dovetail_to*` fallbacks, and the contextual driver) call this
/// instead of re-running `reconstruct_language_def` + `compile_in_rho_matching_ruleset` per
/// invocation, then force exactly the artifacts their path consumes.
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
    insert_in_rho_artifacts(&artifacts);
    Ok(artifacts)
}

/// Insert already-derived artifacts into the calling thread's cache under their own
/// source's hash — the ONE key scheme (`memo stays one-key-per-source`, E-3 design
/// §4.3). Shared by [`cached_in_rho_artifacts`] (batch derivation) and the E-3
/// T-INCR incremental append path (`crate::rho_net_incremental`), which derives the
/// EXTENDED source's artifacts without re-parsing it and then memoizes them exactly
/// where a batch derivation of that source would land. The same collision guard
/// applies: a verified `u64` collision keeps the existing slot (the fresh artifacts
/// stay correct, merely uncached).
pub(crate) fn insert_in_rho_artifacts(artifacts: &Arc<CompiledInRhoArtifacts>) {
    let key = source_hash(&artifacts.definition_source);
    IN_RHO_ARTIFACTS.with(|cache| {
        let mut cache = cache.borrow_mut();
        match cache.get(&key) {
            // A verified `u64` collision (astronomically unlikely): keep the existing slot and
            // hand back the freshly derived artifacts uncached — correct, never aliased.
            Some(existing) if existing.definition_source != artifacts.definition_source => {},
            _ => {
                cache.insert(key, Arc::clone(artifacts));
            },
        }
    });
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
        // (pointer-equal), not merely an equal value — the reconstruct ran once.
        let first = cached_in_rho_artifacts(SWAP_SOURCE).expect("SwapDemo artifacts derive");
        let second = cached_in_rho_artifacts(SWAP_SOURCE).expect("cached artifacts return");
        assert!(Arc::ptr_eq(&first, &second), "the cache must return the memoized Arc");
        assert_eq!(first.definition_source, SWAP_SOURCE);
        assert_eq!(first.def.name.to_string(), "SwapCacheGen");
        assert_eq!(first.lowered().language_name(), "SwapCacheGen");
        assert!(first.ruleset().deferred.is_empty(), "SwapDemo defers nothing");
        assert!(
            first.installed_par().is_ok(),
            "the SwapDemo σ-receiver program installs: {:?}",
            first.installed_par().as_ref().err()
        );
    }

    #[test]
    fn distinct_sources_get_distinct_artifacts() {
        let swap = cached_in_rho_artifacts(SWAP_SOURCE).expect("SwapDemo artifacts derive");
        let other = cached_in_rho_artifacts(OTHER_SOURCE).expect("other artifacts derive");
        assert!(!Arc::ptr_eq(&swap, &other), "distinct sources must not alias a slot");
        assert_ne!(
            swap.ruleset().language_fingerprint,
            other.ruleset().language_fingerprint,
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
    fn fresh_artifacts_defer_every_lazy_cell() {
        // E-3 T-LAZY: first touch derives ONLY the eager core (source + def) — no lowering,
        // no ruleset compile, no emission. Run on a fresh thread so this test's slot cannot
        // have been forced by a sibling test on a shared runner thread.
        std::thread::spawn(|| {
            let artifacts =
                cached_in_rho_artifacts(SWAP_SOURCE).expect("SwapDemo artifacts derive");
            assert!(!artifacts.lowered_forced(), "first touch must not lower");
            assert!(!artifacts.ruleset_forced(), "first touch must not compile the ruleset");
            assert!(!artifacts.installed_par_forced(), "first touch must not emit");
        })
        .join()
        .expect("the fresh-thread probe completes");
    }

    #[test]
    fn forcing_the_ruleset_leaves_the_other_cells_unforced() {
        // The EM-10 invariant made observable: `compile_in_rho_matching_ruleset` re-runs the
        // lowering pipeline INTERNALLY (pure functions), never through this cache's
        // accessors — so the gate/exec path's ruleset force must NOT force `lowered` or
        // `installed_par`.
        std::thread::spawn(|| {
            let artifacts =
                cached_in_rho_artifacts(SWAP_SOURCE).expect("SwapDemo artifacts derive");
            let _ruleset = artifacts.ruleset();
            assert!(artifacts.ruleset_forced());
            assert!(
                !artifacts.lowered_forced(),
                "the ruleset init closure calls pure pipeline fns only (EM-10)"
            );
            assert!(!artifacts.installed_par_forced());
        })
        .join()
        .expect("the fresh-thread probe completes");
    }

    #[test]
    fn forcing_the_installed_par_forces_the_lowering_first() {
        // `installed_par()` mirrors the old eager derivation order: lowering first (through
        // the ACCESSOR, outside the cell's init closure), then the pure emission chain.
        std::thread::spawn(|| {
            let artifacts =
                cached_in_rho_artifacts(SWAP_SOURCE).expect("SwapDemo artifacts derive");
            assert!(artifacts.installed_par().is_ok(), "the SwapDemo program installs");
            assert!(artifacts.lowered_forced(), "the emission consumes the lowering");
            assert!(artifacts.installed_par_forced());
        })
        .join()
        .expect("the fresh-thread probe completes");
    }

    /// What one force-order thread reports back: the lowered language name, the ruleset's
    /// fingerprint, the deferred rule labels, and the installed program's debug rendering
    /// (or the derivation error). Deliberately a POSITIONAL tuple — the whole point is to
    /// compare every observable at once with a single `assert_eq!` across the six orders,
    /// which named fields would turn into four assertions that can drift apart.
    type ForceOrderObservation = (String, String, Vec<String>, Result<String, String>);

    #[test]
    fn force_order_is_invariant() {
        // EM-10's payoff: any accessor order derives identical values (pure pipeline fns,
        // no cache consultation, no cross-cell init coupling). Each order runs on a FRESH
        // thread (fresh cache ⇒ fresh unforced cells); the `Send`-safe observables must
        // agree across all six orders.
        let orders: [[u8; 3]; 6] =
            [[0, 1, 2], [0, 2, 1], [1, 0, 2], [1, 2, 0], [2, 0, 1], [2, 1, 0]];
        let observations: Vec<ForceOrderObservation> = orders
            .into_iter()
            .map(|order| {
                std::thread::spawn(move || {
                    let artifacts = cached_in_rho_artifacts(SWAP_SOURCE)
                        .expect("SwapDemo artifacts derive on every order thread");
                    let mut lowered_name = String::new();
                    let mut fingerprint = String::new();
                    let mut deferred: Vec<String> = Vec::new();
                    let mut installed: Result<String, String> = Err(String::new());
                    for step in order {
                        match step {
                            0 => lowered_name = artifacts.lowered().language_name().to_string(),
                            1 => {
                                let ruleset = artifacts.ruleset();
                                fingerprint = ruleset.language_fingerprint.clone();
                                deferred = ruleset
                                    .deferred
                                    .iter()
                                    .map(|entry| entry.rule_label.clone())
                                    .collect();
                            },
                            _ => {
                                installed = artifacts
                                    .installed_par()
                                    .as_ref()
                                    .map(|par| format!("{par:?}"))
                                    .map_err(Clone::clone);
                            },
                        }
                    }
                    (lowered_name, fingerprint, deferred, installed)
                })
                .join()
                .expect("no order thread panics")
            })
            .collect();
        let baseline = &observations[0];
        for observation in &observations[1..] {
            assert_eq!(observation, baseline, "every force order derives identical artifacts");
        }
    }

    /// Extract the verbatim `language! { … }` body from a production language
    /// source file — the same extraction `tests/a_s5c_production_language_gates.rs`
    /// uses: everything between the macro invocation's opening `{` and the LAST
    /// `}` in the file (the macro's own closing brace).
    fn extract_language_body(source: &str) -> &str {
        let macro_at = source
            .find("language!")
            .expect("the production language file must invoke language!");
        let open = source[macro_at..]
            .find('{')
            .map(|offset| macro_at + offset)
            .expect("the language! invocation must open a brace");
        let close = source
            .rfind('}')
            .expect("the language! invocation must close its brace");
        &source[open + 1..close]
    }

    #[test]
    fn lambda_source_now_derives_an_installed_par() {
        // A-S5.1 (leg i): the REAL production Lambda body — through the SAME
        // source-keyed artifact surface the generated invocation bodies consume —
        // derives `installed_par(): Ok(_)` when FORCED (E-3: the emission is
        // demand-driven now; the bench harness is the named forcing consumer, and
        // this pin forces it the same way): the three congruence-only lowering
        // failures (AppCongL/AppCongR/LamCong) are the recorded install-EXEMPT
        // disposition instead of fail-closed install errors. (The exemption
        // record itself is pinned by `tests/a_s5c_production_language_gates.rs`;
        // this pin covers the cache's drive-through-transparent install surface.)
        let body = extract_language_body(include_str!("../../languages/src/lambda.rs"));
        let artifacts =
            cached_in_rho_artifacts(body).expect("the production Lambda body derives artifacts");
        assert_eq!(artifacts.def.name.to_string(), "Lambda");
        assert!(
            artifacts.installed_par().is_ok(),
            "A-S5.1: Lambda's σ-receiver program installs through the cache surface: {:?}",
            artifacts.installed_par().as_ref().err()
        );
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
                        .ruleset()
                        .deferred
                        .iter()
                        .map(|entry| entry.rule_label.clone())
                        .collect();
                    let installed = artifacts
                        .installed_par()
                        .as_ref()
                        .map(|par| format!("{par:?}"))
                        .map_err(Clone::clone);
                    (artifacts.ruleset().language_fingerprint.clone(), deferred, installed)
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
