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
//! | RhoCalc    | Dovetail + Rholang (two-stage)  | COMM → Rho machine; folds → Dovetail; mixed → pre-fold then Rho |
//! | Calculator | Dovetail + Rholang (two-stage)  | scalar expr tree → Rho dataflow (E3); non-scalar/÷0/overflow → Dovetail |
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
    use std::collections::BTreeSet;

    use mettail_languages::calculator::CalculatorLanguage;
    use mettail_runtime::{Language, RuntimeDovetailRunReport, Term};

    use mettail_rholang_codegen::{
        lower_language_def, plan_rho_default_backend, reconstruct_language_def,
        RhoCoverageEvidence, RhoDefaultBackendRequirements, RhoFoldDataflowDisposition,
        RhoGuardCoverageEvidence, RhoRejectedRuleDisposition, RhoRejectedRuleDispositionKind,
    };
    use mettail_rholang_runtime::{
        build_fold_dataflow_invocation_from_contract, dovetail_rho_backed_rhocalc,
        install_dovetail_rho_runtime_backend, PlannedRhoBackend, RhoBackendInvocation,
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
    /// installs on it). Every rule the scalar lowering rejects (BigInt / collections / casts / …)
    /// is dispositioned through the verified native-handler boundary — those terms run on Dovetail.
    fn calculator_planned_rho_backend() -> Result<PlannedRhoBackend> {
        let source = CalculatorLanguage
            .metadata()
            .definition_source()
            .ok_or_else(|| anyhow!("CalculatorLanguage must expose its definition_source"))?;
        let def = reconstruct_language_def(&source)
            .map_err(|err| anyhow!("reconstruct Calculator LanguageDef: {err:?}"))?;
        let lowering = lower_language_def(&def);
        let dispositions: Vec<RhoRejectedRuleDisposition> = lowering
            .rejected
            .iter()
            .cloned()
            .collect::<BTreeSet<String>>()
            .into_iter()
            .map(|label| {
                RhoRejectedRuleDisposition::new(
                    label,
                    RhoRejectedRuleDispositionKind::NativeHandler,
                )
            })
            .collect();
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

    /// The Calculator F-stage: lower the term's scalar expression tree to a Rholang dataflow (E3)
    /// and run it on the Rho machine, or defer to Dovetail for a non-scalar / free-var / `÷0` /
    /// overflow term. The Dovetail report is the completeness gate + the Defer-fallback payload.
    fn calculator_invocation(
        term: &dyn Term,
        report: &RuntimeDovetailRunReport,
    ) -> Result<RhoBackendInvocation, String> {
        match CalculatorLanguage::rho_fold_dataflow_invocation_from_dovetail_to(term, report, OUT)?
        {
            RhoFoldDataflowDisposition::Run(invocation) => {
                Ok(build_fold_dataflow_invocation_from_contract(invocation))
            },
            RhoFoldDataflowDisposition::Defer => Ok(RhoBackendInvocation::DeferToDovetailReport),
        }
    }

    /// Calculator → two-stage Dovetail+Rholang backend (E3 fold-dataflow).
    pub fn calculator_backed() -> Result<Box<dyn Language>> {
        let backend = calculator_planned_rho_backend()?;
        let language = install_dovetail_rho_runtime_backend(
            CalculatorLanguage,
            backend,
            calculator_dovetail_report,
            calculator_invocation,
        )
        .map_err(|err| anyhow!("Calculator Dovetail+Rho backend install failed: {err:?}"))?;
        Ok(Box::new(language))
    }
}

#[cfg(feature = "rho-languages")]
pub use rho::{calculator_backed, rhocalc_backed};
