//! Production runtime-backend wrappers for the bundled REPL languages.
//!
//! A raw generated `language!` value is a parse/introspection substrate — it advertises NO default
//! runtime backend, so `exec` fails with "language X does not advertise a default runtime backend".
//! This module installs the checked production backends so `exec` works, capability-based:
//!
//! | Language   | Backend                         | `exec` behavior |
//! |------------|---------------------------------|-----------------|
//! | Lambda     | Dovetail + Rholang (two-stage)  | A-S5.6: the in-Rho QUIESCENCE DRIVER (`^drive` seed) β-reduces the whole subject to NF on the Rho machine |
//! | Ambient    | Dovetail + Rholang (two-stage)  | A-S5.6: the in-Rho QUIESCENCE DRIVER fires the guarded AC mobility trio (In/Out/Open) to quiescence on the Rho machine |
//! | RhoCalc    | Dovetail + Rholang (two-stage)  | COMM / observed pure values → Rho machine; mixed → pre-fold then Rho |
//! | Calculator | Dovetail + Rholang (two-stage)  | scalar expr tree → Rho dataflow (E3); non-scalar → rejected at Rho-default boundary; partial arithmetic → semantic predicate |
//! | SwapDemo + the 12 rho_net demos | Dovetail + Rholang (two-stage) | A-S6: the in-Rho set-automaton MATCH (single-shot locate-and-fire) is the default exec path; the D-stage runs only on typed deferrals |
//!
//! A-S2 (D-stage demotion): the two-stage languages install the LAZY wrapper
//! (`install_dovetail_rho_runtime_backend_lazy`) — the report-free F2 compile is the default exec
//! path (ZERO Dovetail work when admitted); the checked Dovetail report is built LAZILY only on a
//! typed deferral (semantic predicate → report payload; gate reject → the report-carrying
//! fallback), so at runtime Dovetail handles only semantic predicates and the fail-closed
//! fallback.
//!
//! A-S5.6 (THE PRODUCTION FLIP — plan v2 §6, F5/F6/F16): Lambda and Ambient move from the
//! generic Dovetail backend onto the same two-stage lazy shape, with `invocation_free` = the
//! generated `rho_net_drive_invocation_to` (both languages are drive-admitted since
//! A-S5.2/A-S5.5). An admitted exec seeds `⌜^drive⌝!(⟦subject⟧, fuel, @OUT)` and the installed
//! `^drive` receiver family matches, fires (through the σ ABI / AC carrier ABI), re-drives every
//! contractum, and rests the quiescent term on OUT — with the four-channel readback and the
//! ALWAYS-ON §4.7 cross-check (err/fuel channels, NF-scan, ledger consistency) surfacing
//! violations as typed exec errors naming the channel. The report-carrying fallbacks differ by
//! design (F16): Lambda tries the report-driven match and otherwise returns a TYPED error — it
//! must NOT σ-replay Beta (the replay driver has no Beta arm; the retired arms + `__other =>`
//! error live at `macros/src/gen/runtime/rho_invocation.rs:1350-1364` — replaying would
//! double-substitute); Ambient keeps the SwapDemo-shaped match-then-σ-replay fallback (its
//! report-path arms exist).
//!
//! A-S6 (THE DEMO FLIP — USER decision 2026-07-20): the runtime mandate is UNIVERSAL — every
//! demo language with an admitted rho_net path joins the default registry on the same two-stage
//! lazy shape, with `invocation_free` = the generated `rho_net_match_invocation_to` (single-shot
//! locate-and-fire; demos are NOT drive-opted — `DRIVE_OPT_IN` stays exactly {Lambda, Ambient}).
//! At runtime Dovetail's roles registry-wide are exactly: semantic predicates, labeled host
//! introspection (the REPL `step` Layer-1 rewrite-graph evidence — display-only, no exec result
//! flows from it), and lazy deferral reports.
//!
//! A Dovetail-only build (`--no-default-features --features bundled-languages`, no f1r3node)
//! FAILS CLOSED for the exec of every machine-defaulted wrapped language (campaign decision (4),
//! universal since A-S6): parse/introspection still work, but `exec` returns a typed error
//! pointing at the rho build. See `docs/design/dovetail-rho-macro-extensions/` (E1–E3) and
//! `docs/architecture/rho-native-integration/09-term-level-reduction-split.md`.
#![cfg(feature = "bundled-languages")]

#[cfg(not(feature = "rho-languages"))]
mod dovetail_only {
    //! Decision (4) — the Dovetail-only (no f1r3node) profile: Lambda/Ambient (A-S5.6) and
    //! every rho_net demo language (A-S6) still REGISTER (parse/introspection/env work
    //! through delegation), but their production reduction semantics live on the Rho machine,
    //! so `exec` FAILS CLOSED with a typed error pointing at the rho build instead of
    //! silently running a divergent host path.

    use anyhow::Result;
    use std::any::Any;

    use mettail_languages::acbagdemo::AcBagDemoLanguage;
    use mettail_languages::acdemo::AcDemoLanguage;
    use mettail_languages::ambdemo::AmbDemoLanguage;
    use mettail_languages::ambient::AmbientLanguage;
    use mettail_languages::ambnewdemo::AmbNewDemoLanguage;
    use mettail_languages::bicongdemo::BiCongDemoLanguage;
    use mettail_languages::commdemo::CommDemoLanguage;
    use mettail_languages::ctxdemo::CtxDemoLanguage;
    use mettail_languages::inoutdemo::InOutDemoLanguage;
    use mettail_languages::lambda::LambdaLanguage;
    use mettail_languages::lambdademo::LambdaDemoLanguage;
    use mettail_languages::nativedemo::NativeDemoLanguage;
    use mettail_languages::nativefolddemo::NativeFoldDemoLanguage;
    use mettail_languages::nlacdemo::NlAcDemoLanguage;
    use mettail_languages::swapdemo::SwapDemoLanguage;
    use mettail_runtime::{
        AscentResults, Language, LanguageMetadata, RuntimeBackend, RuntimeBackendCapability,
        RuntimeBackendReport, Term, TermType, VarTypeInfo,
    };

    /// The production in-Rho execution mechanism of the two drive-opted languages
    /// (Lambda/Ambient — A-S5.6).
    const QUIESCENCE_DRIVER: &str = "the in-Rho quiescence driver";
    /// The production in-Rho execution mechanism of every non-drive-opted wrapped
    /// language (SwapDemo + the 12 rho_net demos — A-S6).
    const SET_AUTOMATON_MATCH: &str = "the in-Rho set-automaton match";

    /// The typed decision-(4) exec error for one language, naming its production in-Rho
    /// mechanism.
    fn rho_build_required(language: &str, mechanism: &str) -> String {
        format!(
            "{language} executes on {mechanism} (A-S5.6/A-S6); this Dovetail-only build has \
             no Rho machine. Rebuild with `--features rho-languages` (the default) to exec \
             {language} terms — parse and introspection remain available here."
        )
    }

    /// A fail-closed production wrapper: every parse/introspection/env surface delegates to
    /// the raw generated language; every EXECUTION surface returns the typed decision-(4)
    /// error. The advertised default backend stays `RhoMachine` — the language's production
    /// semantics — so the failure names the missing build instead of pretending no backend
    /// exists.
    struct RhoBuildRequiredLanguage<L: Language> {
        inner: L,
        mechanism: &'static str,
    }

    impl<L: Language> Language for RhoBuildRequiredLanguage<L> {
        fn name(&self) -> &'static str {
            self.inner.name()
        }

        fn metadata(&self) -> &'static dyn LanguageMetadata {
            self.inner.metadata()
        }

        fn parse_term(&self, input: &str) -> Result<Box<dyn Term>, String> {
            self.inner.parse_term(input)
        }

        fn parse_term_for_env(&self, input: &str) -> Result<Box<dyn Term>, String> {
            self.inner.parse_term_for_env(input)
        }

        fn run_ascent(&self, _term: &dyn Term) -> Result<AscentResults, String> {
            Err(rho_build_required(self.name(), self.mechanism))
        }

        fn default_runtime_backend(&self) -> Option<RuntimeBackend> {
            Some(RuntimeBackend::RhoMachine)
        }

        fn runtime_backend_capabilities(&self) -> Vec<RuntimeBackendCapability> {
            vec![RuntimeBackendCapability {
                backend: RuntimeBackend::RhoMachine,
                is_default: true,
            }]
        }

        fn supports_runtime_backend(&self, backend: RuntimeBackend) -> bool {
            backend == RuntimeBackend::RhoMachine
        }

        fn run_backend_report(
            &self,
            _backend: RuntimeBackend,
            _term: &dyn Term,
        ) -> Result<RuntimeBackendReport, String> {
            Err(rho_build_required(self.name(), self.mechanism))
        }

        fn create_env(&self) -> Box<dyn Any + Send + Sync> {
            self.inner.create_env()
        }

        fn add_to_env(&self, env: &mut dyn Any, name: &str, term: &dyn Term) -> Result<(), String> {
            self.inner.add_to_env(env, name, term)
        }

        fn remove_from_env(&self, env: &mut dyn Any, name: &str) -> Result<bool, String> {
            self.inner.remove_from_env(env, name)
        }

        fn clear_env(&self, env: &mut dyn Any) {
            self.inner.clear_env(env)
        }

        fn substitute_env(&self, term: &dyn Term, env: &dyn Any) -> Result<Box<dyn Term>, String> {
            self.inner.substitute_env(term, env)
        }

        fn substitute_env_preserve_structure(
            &self,
            term: &dyn Term,
            env: &dyn Any,
        ) -> Result<Box<dyn Term>, String> {
            self.inner.substitute_env_preserve_structure(term, env)
        }

        fn list_env(&self, env: &dyn Any) -> Vec<(String, String, Option<String>)> {
            self.inner.list_env(env)
        }

        fn set_env_comment(
            &self,
            env: &mut dyn Any,
            name: &str,
            comment: String,
        ) -> Result<(), String> {
            self.inner.set_env_comment(env, name, comment)
        }

        fn is_env_empty(&self, env: &dyn Any) -> bool {
            self.inner.is_env_empty(env)
        }

        fn infer_term_type(&self, term: &dyn Term) -> TermType {
            self.inner.infer_term_type(term)
        }

        fn infer_var_types(&self, term: &dyn Term) -> Vec<VarTypeInfo> {
            self.inner.infer_var_types(term)
        }

        fn infer_var_type(&self, term: &dyn Term, var_name: &str) -> Option<TermType> {
            self.inner.infer_var_type(term, var_name)
        }
    }

    /// Lambda in the Dovetail-only profile: parse/introspection delegate; exec fails closed
    /// pointing at the rho build (decision (4)).
    pub fn lambda_backed() -> Result<Box<dyn Language>> {
        Ok(Box::new(RhoBuildRequiredLanguage {
            inner: LambdaLanguage,
            mechanism: QUIESCENCE_DRIVER,
        }))
    }

    /// Ambient in the Dovetail-only profile: parse/introspection delegate; exec fails closed
    /// pointing at the rho build (decision (4)).
    pub fn ambient_backed() -> Result<Box<dyn Language>> {
        Ok(Box::new(RhoBuildRequiredLanguage {
            inner: AmbientLanguage,
            mechanism: QUIESCENCE_DRIVER,
        }))
    }

    /// Expands one A-S6 fail-closed demo wrapper for the Dovetail-only profile:
    /// parse/introspection delegate; exec fails closed pointing at the rho build
    /// (decision (4), universal since the demo flip).
    macro_rules! demo_fail_closed {
        ($(#[$doc:meta])* $fn_name:ident, $lang:path) => {
            $(#[$doc])*
            pub fn $fn_name() -> Result<Box<dyn Language>> {
                Ok(Box::new(RhoBuildRequiredLanguage {
                    inner: $lang,
                    mechanism: SET_AUTOMATON_MATCH,
                }))
            }
        };
    }

    demo_fail_closed!(
        /// SwapDemo in the Dovetail-only profile (fail-closed, A-S6).
        swapdemo_backed, SwapDemoLanguage
    );
    demo_fail_closed!(
        /// AcDemo in the Dovetail-only profile (fail-closed, A-S6).
        acdemo_backed, AcDemoLanguage
    );
    demo_fail_closed!(
        /// AcBagDemo in the Dovetail-only profile (fail-closed, A-S6).
        acbagdemo_backed, AcBagDemoLanguage
    );
    demo_fail_closed!(
        /// NlAcDemo in the Dovetail-only profile (fail-closed, A-S6).
        nlacdemo_backed, NlAcDemoLanguage
    );
    demo_fail_closed!(
        /// AmbDemo in the Dovetail-only profile (fail-closed, A-S6).
        ambdemo_backed, AmbDemoLanguage
    );
    demo_fail_closed!(
        /// AmbNewDemo in the Dovetail-only profile (fail-closed, A-S6).
        ambnewdemo_backed, AmbNewDemoLanguage
    );
    demo_fail_closed!(
        /// InOutDemo in the Dovetail-only profile (fail-closed, A-S6).
        inoutdemo_backed, InOutDemoLanguage
    );
    demo_fail_closed!(
        /// CommDemo in the Dovetail-only profile (fail-closed, A-S6).
        commdemo_backed, CommDemoLanguage
    );
    demo_fail_closed!(
        /// CtxDemo in the Dovetail-only profile (fail-closed, A-S6).
        ctxdemo_backed, CtxDemoLanguage
    );
    demo_fail_closed!(
        /// BiCongDemo in the Dovetail-only profile (fail-closed, A-S6).
        bicongdemo_backed, BiCongDemoLanguage
    );
    demo_fail_closed!(
        /// LambdaDemo in the Dovetail-only profile (fail-closed, A-S6).
        lambdademo_backed, LambdaDemoLanguage
    );
    demo_fail_closed!(
        /// NativeDemo in the Dovetail-only profile (fail-closed, A-S6).
        nativedemo_backed, NativeDemoLanguage
    );
    demo_fail_closed!(
        /// NativeFoldDemo in the Dovetail-only profile (fail-closed, A-S6).
        nativefolddemo_backed, NativeFoldDemoLanguage
    );
}

#[cfg(not(feature = "rho-languages"))]
pub use dovetail_only::{
    acbagdemo_backed, acdemo_backed, ambdemo_backed, ambient_backed, ambnewdemo_backed,
    bicongdemo_backed, commdemo_backed, ctxdemo_backed, inoutdemo_backed, lambda_backed,
    lambdademo_backed, nativedemo_backed, nativefolddemo_backed, nlacdemo_backed, swapdemo_backed,
};

#[cfg(feature = "rho-languages")]
mod rho {
    use anyhow::{anyhow, Result};

    use mettail_languages::acbagdemo::AcBagDemoLanguage;
    use mettail_languages::acdemo::AcDemoLanguage;
    use mettail_languages::ambdemo::AmbDemoLanguage;
    use mettail_languages::ambient::AmbientLanguage;
    use mettail_languages::ambnewdemo::AmbNewDemoLanguage;
    use mettail_languages::bicongdemo::BiCongDemoLanguage;
    use mettail_languages::calculator::CalculatorLanguage;
    use mettail_languages::commdemo::CommDemoLanguage;
    use mettail_languages::ctxdemo::CtxDemoLanguage;
    use mettail_languages::inoutdemo::InOutDemoLanguage;
    use mettail_languages::lambda::LambdaLanguage;
    use mettail_languages::lambdademo::LambdaDemoLanguage;
    use mettail_languages::nativedemo::NativeDemoLanguage;
    use mettail_languages::nativefolddemo::NativeFoldDemoLanguage;
    use mettail_languages::nlacdemo::NlAcDemoLanguage;
    use mettail_languages::swapdemo::SwapDemoLanguage;
    use mettail_runtime::{Language, RuntimeDovetailRunReport, Term};

    use mettail_rholang_codegen::{
        lower_language_def, plan_rho_default_backend, reconstruct_language_def,
        suggest_rejected_rule_dispositions, RhoCoverageEvidence, RhoDefaultBackendRequirements,
        RhoFoldDataflowDisposition, RhoGuardCoverageEvidence,
    };
    use mettail_rholang_runtime::{
        build_fold_dataflow_invocation_from_contract, build_rho_net_drive_invocation_from_contract,
        build_rho_net_injection_invocation_from_contract,
        build_rho_net_replay_invocation_from_contracts, dovetail_rho_backed_rhocalc,
        install_dovetail_rho_runtime_backend_lazy, DriveNfScan, PlannedRhoBackend,
        RhoBackendInvocation, RhoInvocationDeferral,
    };

    /// Dovetail saturation bounds (match the generated `dovetail_compiler_stage`).
    const MAX_ITERS: usize = 64;
    const MAX_NODES: usize = 1_000_000;
    /// The observation channel the wrappers run scalar/COMM results on.
    const OUT: &str = "OUT";

    /// Build one production language's [`PlannedRhoBackend`] from its REAL reconstructed
    /// augmented `LanguageDef` (so the plan's fingerprint matches the generated language
    /// value and the wrapper installs on it). Rejected rules are dispositioned by the shared
    /// language-aware classifier. Shared by every two-stage wrapper below.
    fn planned_rho_backend_for(
        language_name: &str,
        source: Option<&'static str>,
    ) -> Result<PlannedRhoBackend> {
        let source = source
            .ok_or_else(|| anyhow!("{language_name}Language must expose its definition_source"))?;
        let def = reconstruct_language_def(source)
            .map_err(|err| anyhow!("reconstruct {language_name} LanguageDef: {err:?}"))?;
        let lowering = lower_language_def(&def);
        let dispositions = suggest_rejected_rule_dispositions(&def, &lowering);
        let requirements = RhoDefaultBackendRequirements {
            coverage: RhoCoverageEvidence::CoveredRejectedRules(dispositions),
            // DERIVED, not asserted. `NoGuardObligations` is a claim about the language that
            // silently becomes false the moment it declares a guard slot — and then the plan
            // fails coverage here, at a call site with no idea why. The substrate's own default
            // disposition per obligation kind is gate-compatible by construction, and a language
            // with no obligations yields an empty vector, i.e. exactly the old behaviour.
            guard_coverage: RhoGuardCoverageEvidence::CoveredGuardObligations(
                mettail_rholang_codegen::guard_quality::substrate_guard_coverage(&def),
            ),
        };
        let plan = plan_rho_default_backend(&def, requirements).map_err(|err| {
            anyhow!("{language_name} Rho-default backend planning failed: {err:?}")
        })?;
        Ok(PlannedRhoBackend::from_plan(plan))
    }

    /// RhoCalc → two-stage Dovetail+Rholang backend (re-exported from rholang-runtime, beside the
    /// AST-first lowering it depends on).
    pub fn rhocalc_backed() -> Result<Box<dyn Language>> {
        dovetail_rho_backed_rhocalc(OUT).map_err(|err| anyhow!("{err}"))
    }

    /// The Calculator Dovetail D-stage report producer (the bare fn `install_dovetail_…` wraps).
    fn calculator_dovetail_report(term: &dyn Term) -> Result<RuntimeDovetailRunReport, String> {
        CalculatorLanguage::dovetail_report_for(term, MAX_ITERS, MAX_NODES)
    }

    /// The Calculator step-only Dovetail producer — the REPL `step` navigable one-step REWRITE-step
    /// graph (Increment 4): each node is a whole program state in source syntax, each edge a
    /// one-step rewrite successor, and a node with no successor is a normal form. Reached only via
    /// `Language::run_step_backend_report`; production `exec` uses `calculator_dovetail_report`.
    fn calculator_dovetail_step_graph(term: &dyn Term) -> Result<RuntimeDovetailRunReport, String> {
        CalculatorLanguage::dovetail_step_graph(term, MAX_ITERS, MAX_NODES)
    }

    /// The Calculator F-stage: lower the term's scalar expression tree to a Rholang dataflow (E3)
    /// and run it on the Rho machine. Non-scalar/free-var terms are rejected at the Rho-default
    /// boundary; partial arithmetic such as `÷0`/overflow is surfaced as a
    /// semantic-predicate block so the runtime audit does not confuse it with
    /// ordinary Rho-machine work.
    ///
    /// A-S2 note: this is now the report-CARRYING fallback compiler, reached only on deferral
    /// (its report parameter feeds `rho_fold_dataflow_invocation_from_dovetail_to`'s
    /// completeness assertion; the lowering itself never reads the report). The default exec
    /// path is [`calculator_invocation_free`].
    fn calculator_invocation(
        term: &dyn Term,
        report: &RuntimeDovetailRunReport,
    ) -> Result<RhoBackendInvocation, String> {
        match CalculatorLanguage::rho_fold_dataflow_invocation_from_dovetail_to(term, report, OUT)?
        {
            RhoFoldDataflowDisposition::Run(invocation) => Ok(RhoBackendInvocation::from(
                build_fold_dataflow_invocation_from_contract(invocation),
            )),
            RhoFoldDataflowDisposition::Defer => Err(
                "Calculator term is not lowerable to Rho scalar dataflow; Rho-default execution \
                 admits only Rho-machine work or semantic-predicate blocks"
                    .to_string(),
            ),
            RhoFoldDataflowDisposition::BlockedBySemanticPredicate(reason) => {
                Ok(RhoBackendInvocation::DeferToDovetailSemanticPredicate {
                    predicate: reason.to_string(),
                })
            },
        }
    }

    /// A-S2 (D-stage demotion): the Calculator REPORT-FREE F2 compile — the generated
    /// `rho_fold_dataflow_invocation_to` seam (the report-carrying
    /// `_from_dovetail_to` variant only ADDS a completeness assertion over it, so this is the
    /// same lowering with zero Dovetail work):
    /// - `Run` → the Rho dataflow invocation executes with NO D-stage;
    /// - `BlockedBySemanticPredicate` (÷0/overflow) → typed
    ///   [`RhoInvocationDeferral::SemanticPredicate`]: the wrapper LAZILY builds the checked
    ///   Dovetail report and returns it as the predicate payload (today's outcome);
    /// - `Defer` / a lowering error → [`RhoInvocationDeferral::GateReject`]: the wrapper
    ///   LAZILY builds the checked report and re-runs [`calculator_invocation`], reproducing
    ///   the eager pipeline's exact error text (D-stage error first if the report fails, else
    ///   the F-stage "not lowerable" rejection).
    fn calculator_invocation_free(
        term: &dyn Term,
    ) -> Result<RhoBackendInvocation, RhoInvocationDeferral> {
        match CalculatorLanguage::rho_fold_dataflow_invocation_to(term, OUT) {
            Ok(RhoFoldDataflowDisposition::Run(invocation)) => Ok(RhoBackendInvocation::from(
                build_fold_dataflow_invocation_from_contract(invocation),
            )),
            Ok(RhoFoldDataflowDisposition::BlockedBySemanticPredicate(reason)) => {
                Err(RhoInvocationDeferral::SemanticPredicate { predicate: reason.to_string() })
            },
            Ok(RhoFoldDataflowDisposition::Defer) => Err(RhoInvocationDeferral::GateReject {
                detail: "Calculator term is not lowerable to Rho scalar dataflow".to_string(),
            }),
            Err(detail) => Err(RhoInvocationDeferral::GateReject { detail }),
        }
    }

    /// Calculator → two-stage Dovetail+Rholang backend (E3 fold-dataflow). A-S2: the LAZY
    /// wrapper — the report-free F2 ([`calculator_invocation_free`]) is the default exec path;
    /// the D-stage runs only on deferral (semantic predicates and non-lowerable terms).
    pub fn calculator_backed() -> Result<Box<dyn Language>> {
        let backend = planned_rho_backend_for(
            "Calculator",
            CalculatorLanguage.metadata().definition_source(),
        )?;
        let language = install_dovetail_rho_runtime_backend_lazy(
            CalculatorLanguage,
            backend,
            calculator_dovetail_report,
            calculator_dovetail_step_graph,
            calculator_invocation_free,
            calculator_invocation,
        )
        .map_err(|err| anyhow!("Calculator Dovetail+Rho backend install failed: {err:?}"))?;
        Ok(Box::new(language))
    }

    /// The SwapDemo Dovetail D-stage report producer. SwapDemo is NOT fold-bearing, so it has
    /// no `dovetail_step_graph`; this producer serves both the D-stage and the (REPL-`step`-only)
    /// step slot — `exec`/`run_backend_report` never reaches the step slot.
    fn swapdemo_dovetail_report(term: &dyn Term) -> Result<RuntimeDovetailRunReport, String> {
        SwapDemoLanguage::dovetail_report_for(term, MAX_ITERS, MAX_NODES)
    }

    /// The SwapDemo F-stage: capability-gated in-Rho set-automaton MATCHING (Stage 3 piece 5).
    /// The automaton MATCHES the redex on the interpreter (the `sa:` τ COMMs) and fires the
    /// σ-receiver. On a gate/scope rejection (a fired rule not matchable in Rho, or a
    /// multi/nested redex), fall CLOSED to the proven Stage-0 host-matched σ-replay driver —
    /// "the language stays on its existing path" — so every input stays correct.
    ///
    /// A-S2 note: this is now the report-CARRYING fallback compiler, reached only on deferral.
    /// The default exec path is [`swapdemo_invocation_free`].
    fn swapdemo_invocation(
        term: &dyn Term,
        report: &RuntimeDovetailRunReport,
    ) -> Result<RhoBackendInvocation, String> {
        match SwapDemoLanguage::rho_net_match_invocation_from_dovetail_to(term, report, OUT) {
            Ok(invocation) => Ok(RhoBackendInvocation::from(
                build_rho_net_injection_invocation_from_contract(invocation),
            )),
            Err(_gate_or_scope_reject) => {
                let injections =
                    SwapDemoLanguage::rho_net_replay_invocation_from_dovetail_to(term, report, OUT)?;
                Ok(RhoBackendInvocation::from(
                    build_rho_net_replay_invocation_from_contracts(injections),
                ))
            },
        }
    }

    /// A-S2 (D-stage demotion): the SwapDemo REPORT-FREE F2 compile — the generated
    /// `rho_net_match_invocation_to` (the match body with the STATIC gate instead of the
    /// report's fired-rule gate, and located-site native counting instead of report firings;
    /// A-S3 admits located native sites via registered machine-side handlers — vacuous for
    /// SwapDemo, which has no native rules). On success the automaton locates + matches every
    /// redex in Rho with ZERO Dovetail work. Any rejection (static gate, an unregistrable
    /// located native rule, nested-multi-site scope, serialization) is a
    /// [`RhoInvocationDeferral::GateReject`]: the wrapper LAZILY builds the checked
    /// Dovetail report and re-runs [`swapdemo_invocation`] — today's match-then-σ-replay
    /// fallback, byte-identical outcomes.
    fn swapdemo_invocation_free(
        term: &dyn Term,
    ) -> Result<RhoBackendInvocation, RhoInvocationDeferral> {
        match SwapDemoLanguage::rho_net_match_invocation_to(term, OUT) {
            Ok(invocation) => Ok(RhoBackendInvocation::from(
                build_rho_net_injection_invocation_from_contract(invocation),
            )),
            Err(detail) => Err(RhoInvocationDeferral::GateReject { detail }),
        }
    }

    /// SwapDemo → two-stage Dovetail+Rholang backend: base rewrites MATCH in Rho (the campaign
    /// endpoint), with the host-matched σ-replay as the fail-closed fallback. A-S2: the LAZY
    /// wrapper — the report-free F2 ([`swapdemo_invocation_free`]) is the default exec path;
    /// the D-stage runs only on deferral.
    pub fn swapdemo_backed() -> Result<Box<dyn Language>> {
        let backend =
            planned_rho_backend_for("SwapDemo", SwapDemoLanguage.metadata().definition_source())?;
        let language = install_dovetail_rho_runtime_backend_lazy(
            SwapDemoLanguage,
            backend,
            swapdemo_dovetail_report,
            swapdemo_dovetail_report,
            swapdemo_invocation_free,
            swapdemo_invocation,
        )
        .map_err(|err| anyhow!("SwapDemo Dovetail+Rho backend install failed: {err:?}"))?;
        Ok(Box::new(language))
    }

    // ── A-S5.6: the PRODUCTION FLIP — Lambda + Ambient on the in-Rho quiescence driver ──

    /// The Lambda Dovetail D-stage report producer (deferral-only since the flip).
    fn lambda_dovetail_report(term: &dyn Term) -> Result<RuntimeDovetailRunReport, String> {
        LambdaLanguage::dovetail_report_for(term, MAX_ITERS, MAX_NODES)
    }

    /// The Lambda step-only Dovetail producer — Lambda is TYPED-path
    /// (`has_substitution_rewrite`), so the generated `dovetail_step_graph` exists and yields
    /// the navigable one-step REWRITE graph (β edges). REPL `step` routing prefers this
    /// Layer-1 graph whenever it has rewrite edges (F5: Lambda step = Layer-1 typed rewrite
    /// graph); production `exec` never reaches this slot.
    fn lambda_dovetail_step_graph(term: &dyn Term) -> Result<RuntimeDovetailRunReport, String> {
        LambdaLanguage::dovetail_step_graph(term, MAX_ITERS, MAX_NODES)
    }

    /// Lambda's static NF-scan mirror for the always-on §4.7 exec cross-check: a β redex is
    /// `App(^lambda(_), _)` anywhere (the `binder_apply_redex_present` family, exactly the
    /// A-S5.2 runtime-suite scan).
    fn lambda_nf_scan() -> DriveNfScan {
        DriveNfScan::BinderApply { apply_label: "App".to_string() }
    }

    /// A-S5.6: the Lambda REPORT-FREE F2 compile — the generated
    /// `rho_net_drive_invocation_to` QUIESCENCE-DRIVER seed (A-S5.2). On success the whole
    /// subject drives to NF in-Rho with ZERO Dovetail work (matching, β through the σ ABI +
    /// installed subst TRS, contractum re-drive, congruence/binder descent — all COMMs), and
    /// the execute arm runs the four-channel readback + the always-on cross-check. Any
    /// rejection (static gate, admission, reflection) is a typed
    /// [`RhoInvocationDeferral::GateReject`] routing to the LAZY D-stage +
    /// [`lambda_invocation`].
    fn lambda_invocation_free(
        term: &dyn Term,
    ) -> Result<RhoBackendInvocation, RhoInvocationDeferral> {
        match LambdaLanguage::rho_net_drive_invocation_to(term, OUT) {
            Ok(invocation) => Ok(RhoBackendInvocation::from(
                build_rho_net_drive_invocation_from_contract(invocation, lambda_nf_scan()),
            )),
            Err(detail) => Err(RhoInvocationDeferral::GateReject { detail }),
        }
    }

    /// The Lambda report-CARRYING fallback compiler (deferral-only). F16 (plan v2 §6.1): it
    /// must NOT σ-replay Beta — the σ-replay driver has NO Beta arm (the retired Stage-3c
    /// subst arms + the `__other =>` error live at
    /// `macros/src/gen/runtime/rho_invocation.rs:1350-1364`; a σ-replayed β would
    /// double-substitute). Body: try the report-driven in-Rho match; otherwise return a
    /// TYPED error naming the deferral.
    fn lambda_invocation(
        term: &dyn Term,
        report: &RuntimeDovetailRunReport,
    ) -> Result<RhoBackendInvocation, String> {
        match LambdaLanguage::rho_net_match_invocation_from_dovetail_to(term, report, OUT) {
            Ok(invocation) => Ok(RhoBackendInvocation::from(
                build_rho_net_injection_invocation_from_contract(invocation),
            )),
            Err(match_reject) => Err(format!(
                "Lambda in-Rho exec deferred: the quiescence-driver seed was rejected and the \
                 report-driven match also rejects ({match_reject}). Lambda has NO σ-replay \
                 fallback by design (F16): the replay driver carries no Beta arm — σ-replaying \
                 a β firing would double-substitute."
            )),
        }
    }

    /// Lambda → two-stage Dovetail+Rholang backend (A-S5.6): the in-Rho quiescence driver is
    /// the default exec path ([`lambda_invocation_free`], zero Dovetail work when admitted);
    /// the D-stage runs only on deferral, and the fallback never σ-replays Beta (F16).
    pub fn lambda_backed() -> Result<Box<dyn Language>> {
        let backend =
            planned_rho_backend_for("Lambda", LambdaLanguage.metadata().definition_source())?;
        let language = install_dovetail_rho_runtime_backend_lazy(
            LambdaLanguage,
            backend,
            lambda_dovetail_report,
            lambda_dovetail_step_graph,
            lambda_invocation_free,
            lambda_invocation,
        )
        .map_err(|err| anyhow!("Lambda Dovetail+Rho backend install failed: {err:?}"))?;
        Ok(Box::new(language))
    }

    /// The Ambient Dovetail D-stage report producer. Ambient is UNTYPED-path (its binder +
    /// `new`-float equations keep `should_emit_binder_congruence` true, so both structural-AC
    /// typed gates are off — F5), hence NO generated `dovetail_step_graph` exists; this
    /// producer serves both the D-stage and the (REPL-`step`-only) step slot, exactly the
    /// SwapDemo pattern. The step slot's report is a DERIVATION graph (no rewrite edges), so
    /// REPL `step` routing falls through to the Layer-2 live COMM trace (F5 pin, probe P4).
    fn ambient_dovetail_report(term: &dyn Term) -> Result<RuntimeDovetailRunReport, String> {
        AmbientLanguage::dovetail_report_for(term, MAX_ITERS, MAX_NODES)
    }

    /// Ambient's static NF-scan mirror for the always-on §4.7 exec cross-check: the guarded
    /// AC mobility trio (C-G Red In / Red Out / Red Open with cross-level name-equality
    /// guards) over the FLATTENED term — the same mirror family the A-S5.5 runtime suite
    /// checks against.
    fn ambient_nf_scan() -> DriveNfScan {
        DriveNfScan::GuardedAcMobilityTrio {
            amb_label: "PAmb".to_string(),
            in_label: "PIn".to_string(),
            out_label: "POut".to_string(),
            open_label: "POpen".to_string(),
        }
    }

    /// A-S5.6: the Ambient REPORT-FREE F2 compile — the generated
    /// `rho_net_drive_invocation_to` QUIESCENCE-DRIVER seed (A-S5.5: the AC carrier arms +
    /// F4 flattening at both seams; the generated invocation boundary runs the A-S5.4a
    /// unconditional unbind-first float, so extrusion-split redexes drive under the binder
    /// arm). Any rejection is a typed [`RhoInvocationDeferral::GateReject`] routing to the
    /// LAZY D-stage + [`ambient_invocation`].
    fn ambient_invocation_free(
        term: &dyn Term,
    ) -> Result<RhoBackendInvocation, RhoInvocationDeferral> {
        match AmbientLanguage::rho_net_drive_invocation_to(term, OUT) {
            Ok(invocation) => Ok(RhoBackendInvocation::from(
                build_rho_net_drive_invocation_from_contract(invocation, ambient_nf_scan()),
            )),
            Err(detail) => Err(RhoInvocationDeferral::GateReject { detail }),
        }
    }

    /// The Ambient report-CARRYING fallback compiler (deferral-only): the SwapDemo shape —
    /// try the report-driven in-Rho match, else fall CLOSED to the host-matched σ-replay
    /// driver (Ambient's report-path arms exist — plan v2 §6.1 keeps the replay arm here,
    /// unlike Lambda/F16).
    fn ambient_invocation(
        term: &dyn Term,
        report: &RuntimeDovetailRunReport,
    ) -> Result<RhoBackendInvocation, String> {
        match AmbientLanguage::rho_net_match_invocation_from_dovetail_to(term, report, OUT) {
            Ok(invocation) => Ok(RhoBackendInvocation::from(
                build_rho_net_injection_invocation_from_contract(invocation),
            )),
            Err(_gate_or_scope_reject) => {
                let injections =
                    AmbientLanguage::rho_net_replay_invocation_from_dovetail_to(term, report, OUT)?;
                Ok(RhoBackendInvocation::from(
                    build_rho_net_replay_invocation_from_contracts(injections),
                ))
            },
        }
    }

    /// Ambient → two-stage Dovetail+Rholang backend (A-S5.6): the in-Rho quiescence driver
    /// is the default exec path ([`ambient_invocation_free`], zero Dovetail work when
    /// admitted); the D-stage runs only on deferral, falling closed to match-then-σ-replay.
    pub fn ambient_backed() -> Result<Box<dyn Language>> {
        let backend =
            planned_rho_backend_for("Ambient", AmbientLanguage.metadata().definition_source())?;
        let language = install_dovetail_rho_runtime_backend_lazy(
            AmbientLanguage,
            backend,
            ambient_dovetail_report,
            ambient_dovetail_report,
            ambient_invocation_free,
            ambient_invocation,
        )
        .map_err(|err| anyhow!("Ambient Dovetail+Rho backend install failed: {err:?}"))?;
        Ok(Box::new(language))
    }

    // ── A-S6: the DEMO-LANGUAGE registry flip — every admitted rho_net demo on the machine ──
    //
    // USER decision (2026-07-20): the runtime mandate — "Dovetail handles only semantic
    // predicates at runtime" — is UNIVERSAL. Every bundled demo language with an admitted
    // rho_net path joins the default registry on the SAME two-stage lazy wrapper as
    // SwapDemo/Lambda/Ambient:
    //
    // * `invocation_free` = the generated report-free `rho_net_match_invocation_to`
    //   (single-shot locate-and-fire; demos are NOT drive-opted — `DRIVE_OPT_IN` stays
    //   exactly {Lambda, Ambient});
    // * the report-carrying fallback is per-language: match-then-σ-replay (the SwapDemo
    //   shape) where the σ-replay driver has arms for the language's families, and
    //   match-then-TYPED-ERROR where it does not (LambdaDemo — the F16 discipline: the
    //   replay driver has NO Beta arm, so a σ-replayed β would double-substitute);
    // * the step slot is the generated `dovetail_step_graph` for TYPED-path demos
    //   (AmbDemo/AmbNewDemo/InOutDemo/CommDemo/LambdaDemo/NativeDemo/NativeFoldDemo) and
    //   `dovetail_report_for` for UNTYPED demos (AcDemo/AcBagDemo/NlAcDemo/CtxDemo/
    //   BiCongDemo — the SwapDemo pattern; its derivation graph fails the REPL Layer-1
    //   keep condition, so `step` falls through to the Layer-2 live COMM trace).
    //
    // Probed reality (2026-07-20, `scratchpad/as6_probe2.log`): every demo below plans,
    // installs, and — except CommDemo — ADMITS its representative redex subjects on the
    // report-free match path with ZERO D-stage work. CommDemo's `PFor` carries a
    // pre-scope Name field the match-path reflection does not support ("binder node with
    // pre-scope fields — no single-child ^lambda ground image in this slice"), so its
    // exec rides the BY-DESIGN deferral: lazy D-stage → report-match rejects for the
    // same reason → the σ-replay driver fires the Comm through its comm arm.

    /// Expands one demo wrapper's STEP slot: the generated navigable one-step rewrite
    /// graph for typed-path demos, the D-stage report (derivation graph — the SwapDemo
    /// pattern) for untyped demos. Reached only via REPL `step` routing
    /// (`Language::run_step_backend_report`); production `exec` never calls it.
    macro_rules! demo_step_slot {
        ($lang:path, typed_step_graph) => {
            |term: &dyn Term| <$lang>::dovetail_step_graph(term, MAX_ITERS, MAX_NODES)
        };
        ($lang:path, report_as_step) => {
            |term: &dyn Term| <$lang>::dovetail_report_for(term, MAX_ITERS, MAX_NODES)
        };
    }

    /// Expands one demo wrapper's report-CARRYING fallback compiler (deferral-only):
    /// `match_then_replay` = the SwapDemo shape (report-driven match, else fall closed to
    /// the host-matched σ-replay driver); `match_then_typed_error` = the Lambda/F16 shape
    /// (report-driven match, else a TYPED error — the σ-replay driver has no substitution
    /// arm for the language's firing family, so replaying would double-substitute).
    macro_rules! demo_fallback_slot {
        ($lang:path, $name:literal, match_then_replay) => {
            |term: &dyn Term, report: &RuntimeDovetailRunReport| {
                match <$lang>::rho_net_match_invocation_from_dovetail_to(term, report, OUT) {
                    Ok(invocation) => Ok(RhoBackendInvocation::from(
                        build_rho_net_injection_invocation_from_contract(invocation),
                    )),
                    Err(_gate_or_scope_reject) => {
                        let injections =
                            <$lang>::rho_net_replay_invocation_from_dovetail_to(term, report, OUT)?;
                        Ok(RhoBackendInvocation::from(
                            build_rho_net_replay_invocation_from_contracts(injections),
                        ))
                    },
                }
            }
        };
        ($lang:path, $name:literal, match_then_typed_error) => {
            |term: &dyn Term, report: &RuntimeDovetailRunReport| {
                match <$lang>::rho_net_match_invocation_from_dovetail_to(term, report, OUT) {
                    Ok(invocation) => Ok(RhoBackendInvocation::from(
                        build_rho_net_injection_invocation_from_contract(invocation),
                    )),
                    Err(match_reject) => Err(format!(
                        "{} in-Rho exec deferred: the report-free match was rejected and the \
                         report-driven match also rejects ({match_reject}). {} has NO σ-replay \
                         fallback by design (F16): the replay driver carries no substitution \
                         arm — σ-replaying a substitution firing would double-substitute.",
                        $name, $name,
                    )),
                }
            }
        };
    }

    /// Expands one A-S6 demo-language production wrapper: the two-stage LAZY
    /// Dovetail+Rholang backend on the `swapdemo_backed` shape — the report-free
    /// `rho_net_match_invocation_to` is the default exec path (in-Rho locate-all match,
    /// ZERO Dovetail work when admitted); the D-stage runs only on a typed deferral,
    /// resolved by the selected fallback shape.
    macro_rules! demo_rho_backed {
        (
            $(#[$doc:meta])*
            $fn_name:ident, $lang:path, $name:literal,
            step: $step_kind:ident, fallback: $fallback_kind:ident
        ) => {
            $(#[$doc])*
            pub fn $fn_name() -> Result<Box<dyn Language>> {
                let backend = planned_rho_backend_for(
                    $name,
                    <$lang as Language>::metadata(&$lang).definition_source(),
                )?;
                let language = install_dovetail_rho_runtime_backend_lazy(
                    $lang,
                    backend,
                    |term: &dyn Term| <$lang>::dovetail_report_for(term, MAX_ITERS, MAX_NODES),
                    demo_step_slot!($lang, $step_kind),
                    |term: &dyn Term| match <$lang>::rho_net_match_invocation_to(term, OUT) {
                        Ok(invocation) => Ok(RhoBackendInvocation::from(
                            build_rho_net_injection_invocation_from_contract(invocation),
                        )),
                        Err(detail) => Err(RhoInvocationDeferral::GateReject { detail }),
                    },
                    demo_fallback_slot!($lang, $name, $fallback_kind),
                )
                .map_err(|err| {
                    anyhow!("{} Dovetail+Rho backend install failed: {err:?}", $name)
                })?;
                Ok(Box::new(language))
            }
        };
    }

    demo_rho_backed!(
        /// AcDemo (flat HashBag AC rewrite `{x, ...rest} ~> wrap(x)`) → two-stage lazy
        /// Dovetail+Rholang backend (A-S6). Untyped path: the step slot serves the
        /// D-stage derivation report (Layer-2 fall-through in REPL `step`).
        acdemo_backed, AcDemoLanguage, "AcDemo",
        step: report_as_step, fallback: match_then_replay
    );

    demo_rho_backed!(
        /// AcBagDemo (bag-TRANSFORMING AC rewrite `{x, ...rest} ~> {mark(x), ...rest}` +
        /// the `MarkIdem` equation) → two-stage lazy Dovetail+Rholang backend (A-S6).
        /// Probed: the equation does NOT gate the match path — the bag-valued RHS
        /// re-sources from the subject spread and admits with zero D-stage.
        acbagdemo_backed, AcBagDemoLanguage, "AcBagDemo",
        step: report_as_step, fallback: match_then_replay
    );

    demo_rho_backed!(
        /// NlAcDemo (non-linear `{x, x, ...rest}` bare-var AC rewrite) → two-stage lazy
        /// Dovetail+Rholang backend (A-S6). The reducer enforces the non-linear
        /// consistency guard over the subject spread.
        nlacdemo_backed, NlAcDemoLanguage, "NlAcDemo",
        step: report_as_step, fallback: match_then_replay
    );

    demo_rho_backed!(
        /// AmbDemo (the Ambient-calculus `OpenRule` STRUCTURAL non-linear AC family) →
        /// two-stage lazy Dovetail+Rholang backend (A-S6). Typed path (structural-AC,
        /// binder-free): the step slot is the generated `dovetail_step_graph`.
        ambdemo_backed, AmbDemoLanguage, "AmbDemo",
        step: typed_step_graph, fallback: match_then_replay
    );

    demo_rho_backed!(
        /// AmbNewDemo (`OpenRule` + the `PNew` binder CONSTRUCTOR, no binder rewrites) →
        /// two-stage lazy Dovetail+Rholang backend (A-S6). Probed: redexes under
        /// `new(x, …)` locate and fire in Rho too.
        ambnewdemo_backed, AmbNewDemoLanguage, "AmbNewDemo",
        step: typed_step_graph, fallback: match_then_replay
    );

    demo_rho_backed!(
        /// InOutDemo (the DEPTH-2 NESTED structural non-linear AC family — Ambient
        /// `InRule`/`OutRule`) → two-stage lazy Dovetail+Rholang backend (A-S6).
        inoutdemo_backed, InOutDemoLanguage, "InOutDemo",
        step: typed_step_graph, fallback: match_then_replay
    );

    demo_rho_backed!(
        /// CommDemo (the canonical single-receive communication rewrite with an `eval`
        /// substitution RHS) → two-stage lazy Dovetail+Rholang backend (A-S6). Probed
        /// reality: the report-free match DEFERS — `PFor` is a binder node with a
        /// PRE-SCOPE Name field, which the match-path reflection does not support — so
        /// an exec rides the BY-DESIGN lazy deferral: the D-stage report is built, the
        /// report-driven match rejects for the same reason, and the σ-replay driver
        /// fires the Comm through its comm arm (per-firing channels `OUT0`, `OUT1`, …).
        commdemo_backed, CommDemoLanguage, "CommDemo",
        step: typed_step_graph, fallback: match_then_replay
    );

    demo_rho_backed!(
        /// CtxDemo (the unary-congruence contextual family: `Flip` under `WrapCong`) →
        /// two-stage lazy Dovetail+Rholang backend (A-S6). The congruence-only
        /// `WrapCong` is statically exempt (A-S5.1); `Flip` locates and fires in Rho at
        /// the root AND under `wrap(…)` contexts.
        ctxdemo_backed, CtxDemoLanguage, "CtxDemo",
        step: report_as_step, fallback: match_then_replay
    );

    demo_rho_backed!(
        /// BiCongDemo (the 2-ary-congruence n-hole contextual family: `Flip` under
        /// `NodeCong`) → two-stage lazy Dovetail+Rholang backend (A-S6). Both holes'
        /// redexes locate and fire in Rho. Untyped path (like CtxDemo): the step slot
        /// serves the D-stage derivation report.
        bicongdemo_backed, BiCongDemoLanguage, "BiCongDemo",
        step: report_as_step, fallback: match_then_replay
    );

    demo_rho_backed!(
        /// LambdaDemo (the untyped λ-calculus binder/β-substitution demonstration) →
        /// two-stage lazy Dovetail+Rholang backend (A-S6). β fires in-Rho through the
        /// TRS seed on the match path. The fallback is the Lambda/F16 shape: the
        /// σ-replay driver has NO Beta arm, so the deferral fallback returns a TYPED
        /// error instead of replaying (a σ-replayed β would double-substitute).
        lambdademo_backed, LambdaDemoLanguage, "LambdaDemo",
        step: typed_step_graph, fallback: match_then_typed_error
    );

    demo_rho_backed!(
        /// NativeDemo (the native-system-process `PowInt` `![…] fold` demonstration) →
        /// two-stage lazy Dovetail+Rholang backend (A-S6). A located native site ADMITS
        /// (A-S3): the wrapper's clear/drain bracket registers the rule's machine-side
        /// handler contract and the machine's dispatch COMM computes the value at COMM
        /// time — no host-pre-computed contractum rides the call.
        nativedemo_backed, NativeDemoLanguage, "NativeDemo",
        step: typed_step_graph, fallback: match_then_replay
    );

    demo_rho_backed!(
        /// NativeFoldDemo (the native scalar-fold `AddInt` demonstration) → two-stage
        /// lazy Dovetail+Rholang backend (A-S6). Multi-site subjects admit — each
        /// located site drives its own machine-side handler invocation.
        nativefolddemo_backed, NativeFoldDemoLanguage, "NativeFoldDemo",
        step: typed_step_graph, fallback: match_then_replay
    );
}

#[cfg(feature = "rho-languages")]
pub use rho::{
    acbagdemo_backed, acdemo_backed, ambdemo_backed, ambient_backed, ambnewdemo_backed,
    bicongdemo_backed, calculator_backed, commdemo_backed, ctxdemo_backed, inoutdemo_backed,
    lambda_backed, lambdademo_backed, nativedemo_backed, nativefolddemo_backed, nlacdemo_backed,
    rhocalc_backed, swapdemo_backed,
};
