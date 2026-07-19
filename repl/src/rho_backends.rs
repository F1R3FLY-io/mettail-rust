//! Production runtime-backend wrappers for the bundled REPL languages.
//!
//! A raw generated `language!` value is a parse/introspection substrate — it advertises NO default
//! runtime backend, so `exec` fails with "language X does not advertise a default runtime backend".
//! This module installs the checked production backends so `exec` works, capability-based:
//!
//! | Language   | Backend                         | `exec` behavior |
//! |------------|---------------------------------|-----------------|
//! | Lambda     | Dovetail (generic)              | β-redex reduces (E1); normal form displays itself |
//! | Ambient    | Dovetail (generic)              | AC redex (open/in/extrusion) reduces |
//! | RhoCalc    | Dovetail + Rholang (two-stage)  | COMM / observed pure values → Rho machine; mixed → pre-fold then Rho |
//! | Calculator | Dovetail + Rholang (two-stage)  | scalar expr tree → Rho dataflow (E3); non-scalar → rejected at Rho-default boundary; partial arithmetic → semantic predicate |
//!
//! A-S2 (D-stage demotion): the two-stage languages (RhoCalc/Calculator/SwapDemo) install the
//! LAZY wrapper (`install_dovetail_rho_runtime_backend_lazy`) — the report-free F2 compile is
//! the default exec path (ZERO Dovetail work when admitted); the checked Dovetail report is
//! built LAZILY only on a typed deferral (semantic predicate → report payload; gate reject →
//! today's report-carrying fallback), so at runtime Dovetail handles only semantic predicates
//! and the fail-closed fallback.
//!
//! Lambda/Ambient need only `bundled-languages` (the generic
//! [`mettail_dovetail_runtime::dovetail_backed`], no f1r3node); RhoCalc/Calculator need
//! `rho-languages` (the Rho machine). A Dovetail-only build (`--no-default-features --features
//! bundled-languages`) therefore still gets Lambda/Ambient backends. See
//! `docs/design/dovetail-rho-macro-extensions/` (E1–E3) and
//! `docs/architecture/rho-native-integration/09-term-level-reduction-split.md`.
#![cfg(feature = "bundled-languages")]

use anyhow::{anyhow, Result};

use mettail_dovetail_runtime::dovetail_backed;
use mettail_languages::ambient::AmbientLanguage;
use mettail_languages::lambda::LambdaLanguage;
use mettail_runtime::Language;

/// Lambda → generic Dovetail backend. β-reduction works because of extension E1 (generalized
/// substitution lowering); a normal form has no redex and reconstructs to itself.
pub fn lambda_backed() -> Result<Box<dyn Language>> {
    dovetail_backed(LambdaLanguage, LambdaLanguage::dovetail_compiler_stage())
        .map_err(|err| anyhow!("Lambda Dovetail backend install failed: {err:?}"))
}

/// Ambient → generic Dovetail backend (associative-commutative redex reduction).
pub fn ambient_backed() -> Result<Box<dyn Language>> {
    dovetail_backed(AmbientLanguage, AmbientLanguage::dovetail_compiler_stage())
        .map_err(|err| anyhow!("Ambient Dovetail backend install failed: {err:?}"))
}

#[cfg(feature = "rho-languages")]
mod rho {
    use anyhow::{anyhow, Result};

    use mettail_languages::calculator::CalculatorLanguage;
    use mettail_languages::swapdemo::SwapDemoLanguage;
    use mettail_runtime::{Language, RuntimeDovetailRunReport, Term};

    use mettail_rholang_codegen::{
        lower_language_def, plan_rho_default_backend, reconstruct_language_def,
        suggest_rejected_rule_dispositions, RhoCoverageEvidence, RhoDefaultBackendRequirements,
        RhoFoldDataflowDisposition, RhoGuardCoverageEvidence,
    };
    use mettail_rholang_runtime::{
        build_fold_dataflow_invocation_from_contract,
        build_rho_net_injection_invocation_from_contract,
        build_rho_net_replay_invocation_from_contracts, dovetail_rho_backed_rhocalc,
        install_dovetail_rho_runtime_backend_lazy, PlannedRhoBackend, RhoBackendInvocation,
        RhoInvocationDeferral,
    };

    /// Dovetail saturation bounds (match the generated `dovetail_compiler_stage`).
    const MAX_ITERS: usize = 64;
    const MAX_NODES: usize = 1_000_000;
    /// The observation channel the wrappers run scalar/COMM results on.
    const OUT: &str = "OUT";

    /// RhoCalc → two-stage Dovetail+Rholang backend (re-exported from rholang-runtime, beside the
    /// AST-first lowering it depends on).
    pub fn rhocalc_backed() -> Result<Box<dyn Language>> {
        dovetail_rho_backed_rhocalc(OUT).map_err(|err| anyhow!("{err}"))
    }

    /// Build the Calculator [`PlannedRhoBackend`] from its REAL reconstructed augmented
    /// `LanguageDef` (so the plan's fingerprint matches `CalculatorLanguage` and the wrapper
    /// installs on it). Rejected rules are dispositioned by the shared language-aware classifier:
    /// structural constructors use generated Rho AST contracts, while native/eval and unsupported
    /// scalar operators use Rho-native system processes.
    fn calculator_planned_rho_backend() -> Result<PlannedRhoBackend> {
        let source = CalculatorLanguage
            .metadata()
            .definition_source()
            .ok_or_else(|| anyhow!("CalculatorLanguage must expose its definition_source"))?;
        let def = reconstruct_language_def(&source)
            .map_err(|err| anyhow!("reconstruct Calculator LanguageDef: {err:?}"))?;
        let lowering = lower_language_def(&def);
        let dispositions = suggest_rejected_rule_dispositions(&def, &lowering);
        let requirements = RhoDefaultBackendRequirements {
            coverage: RhoCoverageEvidence::CoveredRejectedRules(dispositions),
            guard_coverage: RhoGuardCoverageEvidence::NoGuardObligations,
        };
        let plan = plan_rho_default_backend(&def, requirements)
            .map_err(|err| anyhow!("Calculator Rho-default backend planning failed: {err:?}"))?;
        Ok(PlannedRhoBackend::from_plan(plan))
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
        let backend = calculator_planned_rho_backend()?;
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

    /// Build the SwapDemo [`PlannedRhoBackend`] from its REAL reconstructed augmented
    /// `LanguageDef` (so the plan's fingerprint matches `SwapDemoLanguage` and the wrapper
    /// installs on it) — byte-identical to [`calculator_planned_rho_backend`] with SwapDemo.
    fn swapdemo_planned_rho_backend() -> Result<PlannedRhoBackend> {
        let source = SwapDemoLanguage
            .metadata()
            .definition_source()
            .ok_or_else(|| anyhow!("SwapDemoLanguage must expose its definition_source"))?;
        let def = reconstruct_language_def(&source)
            .map_err(|err| anyhow!("reconstruct SwapDemo LanguageDef: {err:?}"))?;
        let lowering = lower_language_def(&def);
        let dispositions = suggest_rejected_rule_dispositions(&def, &lowering);
        let requirements = RhoDefaultBackendRequirements {
            coverage: RhoCoverageEvidence::CoveredRejectedRules(dispositions),
            guard_coverage: RhoGuardCoverageEvidence::NoGuardObligations,
        };
        let plan = plan_rho_default_backend(&def, requirements)
            .map_err(|err| anyhow!("SwapDemo Rho-default backend planning failed: {err:?}"))?;
        Ok(PlannedRhoBackend::from_plan(plan))
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
        let backend = swapdemo_planned_rho_backend()?;
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
}

#[cfg(feature = "rho-languages")]
pub use rho::{calculator_backed, rhocalc_backed, swapdemo_backed};
