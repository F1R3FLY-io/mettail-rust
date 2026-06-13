//! Rho-default backend planning.
//!
//! `RhoBackendFlipGate.v` proves the Boolean gate. This module is the Rust-side
//! artifact that a runtime selector can consume: it lowers a `LanguageDef`,
//! checks proof/oracle/coverage/deadlock evidence, and either returns a concrete
//! Rho-default backend plan or all blockers.

use std::collections::BTreeSet;

use mettail_ast::language::LanguageDef;
use models::rhoapi::Par;

use crate::flip::{decide_rho_flip, RhoFlipDecision, RhoFlipGates};
use crate::lower::{lower_language_def, RhoLowering};
use crate::validate::{RhoValidationError, ValidatedRhoProgram};

/// Coverage evidence for rules not lowered by the scalar Rho AST generator.
///
/// A default Rho backend may not ignore `RhoLowering::rejected`. Either every
/// rule lowered to Rholang AST, or every rejected rule is covered by an
/// explicit external/native/Rho handler contract that passed the separate
/// coverage audit.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RhoCoverageEvidence {
    /// The backend is acceptable only when `RhoLowering::rejected` is empty.
    AllRulesLowered,
    /// Rejected rules are acceptable only when this exact set names them all.
    DelegatedRejectedRules(Vec<String>),
}

impl RhoCoverageEvidence {
    fn delegated_set(&self) -> BTreeSet<&str> {
        match self {
            Self::AllRulesLowered => BTreeSet::new(),
            Self::DelegatedRejectedRules(rules) => rules.iter().map(String::as_str).collect(),
        }
    }

    fn uncovered_rejections(&self, lowering: &RhoLowering) -> Vec<String> {
        let delegated = self.delegated_set();
        lowering
            .rejected
            .iter()
            .filter(|rule| !delegated.contains(rule.as_str()))
            .cloned()
            .collect()
    }

    fn extraneous_delegations(&self, lowering: &RhoLowering) -> Vec<String> {
        let rejected: BTreeSet<&str> = lowering.rejected.iter().map(String::as_str).collect();
        self.delegated_set()
            .into_iter()
            .filter(|rule| !rejected.contains(rule))
            .map(ToOwned::to_owned)
            .collect()
    }

    fn exactly_covers(&self, lowering: &RhoLowering) -> bool {
        self.uncovered_rejections(lowering).is_empty()
            && self.extraneous_delegations(lowering).is_empty()
    }
}

/// Evidence inputs for selecting Rho as a language's default runtime backend.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RhoDefaultBackendEvidence {
    pub proofs_passed: bool,
    pub oracle_parity_passed: bool,
    pub coverage_audit_passed: bool,
    pub coverage: RhoCoverageEvidence,
}

/// Concrete plan for a language that passed the Rho-default flip gate.
#[derive(Debug, Clone, PartialEq)]
pub struct RhoDefaultBackendPlan {
    pub lowering: RhoLowering,
    pub validated_program: ValidatedRhoProgram,
    pub delegated_rejections: Vec<String>,
}

impl RhoDefaultBackendPlan {
    /// Executable Rho backend artifact selected and validated by the flip gate.
    pub fn program(&self) -> &ValidatedRhoProgram {
        &self.validated_program
    }

    /// Normalized AST to inject into the host Rho runtime, when available.
    pub fn ast_par(&self) -> Option<&Par> {
        self.program().ast_par()
    }

    /// Reader/debug annotation. This text is not parsed as the execution path.
    pub fn text_annotation(&self) -> &str {
        self.program().text_annotation()
    }
}

/// Rejected Rho-default plan with complete diagnostic state for callers.
#[derive(Debug, Clone, PartialEq)]
pub struct RhoDefaultBackendPlanError {
    pub lowering: RhoLowering,
    pub decision: RhoFlipDecision,
    pub uncovered_rejections: Vec<String>,
    pub extraneous_delegations: Vec<String>,
    pub validation_errors: Vec<RhoValidationError>,
}

/// Lower `def` and build the Rho-default backend plan if every flip gate passes.
pub fn plan_rho_default_backend(
    def: &LanguageDef,
    evidence: RhoDefaultBackendEvidence,
) -> Result<RhoDefaultBackendPlan, RhoDefaultBackendPlanError> {
    let lowering = lower_language_def(def);
    let validated_program = ValidatedRhoProgram::try_from(lowering.program.clone());
    let validation_errors = validated_program.clone().err().unwrap_or_default();
    let uncovered_rejections = evidence.coverage.uncovered_rejections(&lowering);
    let extraneous_delegations = evidence.coverage.extraneous_delegations(&lowering);
    let coverage_passed =
        evidence.coverage_audit_passed && evidence.coverage.exactly_covers(&lowering);
    let decision = decide_rho_flip(
        RhoFlipGates {
            proofs_passed: evidence.proofs_passed,
            oracle_parity_passed: evidence.oracle_parity_passed,
            coverage_passed,
            artifact_validated: validation_errors.is_empty(),
        },
        &lowering.deadlock_report,
    );

    if decision.can_flip_to_rho() {
        Ok(RhoDefaultBackendPlan {
            delegated_rejections: match evidence.coverage {
                RhoCoverageEvidence::AllRulesLowered => Vec::new(),
                RhoCoverageEvidence::DelegatedRejectedRules(rules) => rules,
            },
            validated_program: validated_program
                .expect("flip decision requires successful artifact validation"),
            lowering,
        })
    } else {
        Err(RhoDefaultBackendPlanError {
            lowering,
            decision,
            uncovered_rejections,
            extraneous_delegations,
            validation_errors,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::flip::RhoFlipBlocker;

    const ALL_LOWERED_FRAGMENT: &str = r#"
        name: CalcAllLowered,
        types { Proc }
        terms {
            AddInt . a:Int, b:Int |- a "+" b : Int ;
            SubInt . a:Int, b:Int |- a "-" b : Int ;
            Neg . a:Int |- "-" a : Int ;
        }
    "#;

    const PARTIAL_FRAGMENT: &str = r#"
        name: CalcPartial,
        types { Proc }
        terms {
            AddInt . a:Int, b:Int |- a "+" b : Int ;
            PowInt . a:Int, b:Int |- a "^" b : Int ;
            AddBigInt . a:BigInt, b:BigInt |- a "+" b : BigInt ;
        }
    "#;

    fn parse(src: &str) -> LanguageDef {
        syn::parse_str::<LanguageDef>(src).expect("test fragment must parse")
    }

    fn passing_evidence(coverage: RhoCoverageEvidence) -> RhoDefaultBackendEvidence {
        RhoDefaultBackendEvidence {
            proofs_passed: true,
            oracle_parity_passed: true,
            coverage_audit_passed: true,
            coverage,
        }
    }

    #[test]
    fn default_backend_plan_succeeds_when_all_rules_lower() {
        let plan = plan_rho_default_backend(
            &parse(ALL_LOWERED_FRAGMENT),
            passing_evidence(RhoCoverageEvidence::AllRulesLowered),
        )
        .expect("all-lowered fragment should pass the default-backend gate");

        assert_eq!(plan.lowering.lowered, vec!["AddInt", "SubInt", "Neg"]);
        assert_eq!(plan.lowering.rejected, Vec::<String>::new());
        assert_eq!(plan.delegated_rejections, Vec::<String>::new());
        assert_eq!(plan.ast_par().expect("plan must carry AST").receives.len(), 3);
        assert!(plan.text_annotation().contains("contract @\"AddInt\""));
    }

    #[test]
    fn default_backend_plan_blocks_uncovered_rejections() {
        let err = plan_rho_default_backend(
            &parse(PARTIAL_FRAGMENT),
            passing_evidence(RhoCoverageEvidence::AllRulesLowered),
        )
        .expect_err("uncovered rejected rules must block Rho default");

        assert_eq!(err.uncovered_rejections, vec!["PowInt", "AddBigInt"]);
        assert_eq!(err.extraneous_delegations, Vec::<String>::new());
        assert_eq!(err.decision.blockers, vec![RhoFlipBlocker::Coverage]);
    }

    #[test]
    fn default_backend_plan_accepts_exact_delegated_rejections() {
        let plan = plan_rho_default_backend(
            &parse(PARTIAL_FRAGMENT),
            passing_evidence(RhoCoverageEvidence::DelegatedRejectedRules(vec![
                "PowInt".to_string(),
                "AddBigInt".to_string(),
            ])),
        )
        .expect("explicitly covered rejected rules may be delegated");

        assert_eq!(plan.lowering.lowered, vec!["AddInt"]);
        assert_eq!(plan.lowering.rejected, vec!["PowInt", "AddBigInt"]);
        assert_eq!(plan.delegated_rejections, vec!["PowInt", "AddBigInt"]);
    }

    #[test]
    fn default_backend_plan_rejects_stale_delegation_claims() {
        let err = plan_rho_default_backend(
            &parse(PARTIAL_FRAGMENT),
            passing_evidence(RhoCoverageEvidence::DelegatedRejectedRules(vec![
                "PowInt".to_string(),
                "AddBigInt".to_string(),
                "MissingRule".to_string(),
            ])),
        )
        .expect_err("delegation evidence must exactly match rejected rules");

        assert_eq!(err.uncovered_rejections, Vec::<String>::new());
        assert_eq!(err.extraneous_delegations, vec!["MissingRule"]);
        assert_eq!(err.decision.blockers, vec![RhoFlipBlocker::Coverage]);
    }

    #[test]
    fn default_backend_plan_reports_all_non_coverage_gate_failures() {
        let err = plan_rho_default_backend(
            &parse(ALL_LOWERED_FRAGMENT),
            RhoDefaultBackendEvidence {
                proofs_passed: false,
                oracle_parity_passed: false,
                coverage_audit_passed: true,
                coverage: RhoCoverageEvidence::AllRulesLowered,
            },
        )
        .expect_err("missing proof and oracle gates must block Rho default");

        assert_eq!(err.uncovered_rejections, Vec::<String>::new());
        assert_eq!(
            err.decision.blockers,
            vec![RhoFlipBlocker::Proofs, RhoFlipBlocker::OracleParity]
        );
    }
}
