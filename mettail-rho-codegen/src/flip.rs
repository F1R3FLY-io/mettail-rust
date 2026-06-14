//! Per-language Rho-default flip gate.
//!
//! This is the Rust-side image of `RhoBackendFlipGate.v`: a language can use
//! the Rho backend by default exactly when the planner can validate exact
//! coverage, generated artifact shape, and static channel-deadlock gates.

use crate::deadlock::{ChannelDeadlockDiagnostic, ChannelDeadlockReport};

/// Gate inputs other than the generated channel-deadlock report.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RhoFlipGates {
    pub coverage_passed: bool,
    pub artifact_validated: bool,
}

/// A reason the Rho backend must not become default for a language.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RhoFlipBlocker {
    Coverage,
    ArtifactValidation,
    ChannelDeadlocks(Vec<ChannelDeadlockDiagnostic>),
}

/// Flip decision with all blockers surfaced at once.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RhoFlipDecision {
    pub blockers: Vec<RhoFlipBlocker>,
}

impl RhoFlipDecision {
    pub fn can_flip_to_rho(&self) -> bool {
        self.blockers.is_empty()
    }
}

/// Decide whether a language may use Rho as its default runtime backend.
pub fn decide_rho_flip(
    gates: RhoFlipGates,
    deadlock_report: &ChannelDeadlockReport,
) -> RhoFlipDecision {
    let mut blockers = Vec::new();

    if !gates.coverage_passed {
        blockers.push(RhoFlipBlocker::Coverage);
    }
    if !gates.artifact_validated {
        blockers.push(RhoFlipBlocker::ArtifactValidation);
    }
    if !deadlock_report.no_new_deadlocks() {
        blockers.push(RhoFlipBlocker::ChannelDeadlocks(deadlock_report.diagnostics.clone()));
    }

    RhoFlipDecision { blockers }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::deadlock::{analyze_channel_deadlocks, ChannelNetwork, ContractFlow};

    fn clean_report() -> ChannelDeadlockReport {
        analyze_channel_deadlocks(
            &ChannelNetwork::new()
                .with_external("entry")
                .with_contract(ContractFlow::exported_service("entry", std::iter::empty::<&str>())),
        )
    }

    fn passing_gates() -> RhoFlipGates {
        RhoFlipGates {
            coverage_passed: true,
            artifact_validated: true,
        }
    }

    #[test]
    fn all_gates_and_clean_deadlock_report_allow_flip() {
        let decision = decide_rho_flip(passing_gates(), &clean_report());
        assert!(decision.can_flip_to_rho());
        assert_eq!(decision.blockers, Vec::new());
    }

    #[test]
    fn missing_coverage_blocks_flip() {
        let report = clean_report();
        let decision = decide_rho_flip(
            RhoFlipGates {
                coverage_passed: false,
                artifact_validated: true,
            },
            &report,
        );

        assert!(!decision.can_flip_to_rho());
        assert_eq!(decision.blockers, vec![RhoFlipBlocker::Coverage]);
    }

    #[test]
    fn channel_deadlock_diagnostics_block_flip() {
        let report = analyze_channel_deadlocks(
            &ChannelNetwork::new().with_contract(ContractFlow::new("needs_b", ["b"], ["out"])),
        );
        let decision = decide_rho_flip(passing_gates(), &report);

        assert!(!decision.can_flip_to_rho());
        assert_eq!(
            decision.blockers,
            vec![RhoFlipBlocker::ChannelDeadlocks(vec![
                ChannelDeadlockDiagnostic::MissingProducer {
                    contract: "needs_b".to_string(),
                    channel: "b".to_string(),
                }
            ])]
        );
    }

    #[test]
    fn decision_reports_all_blockers_together() {
        let report = analyze_channel_deadlocks(
            &ChannelNetwork::new().with_contract(ContractFlow::new("needs_b", ["b"], ["out"])),
        );
        let decision = decide_rho_flip(
            RhoFlipGates {
                coverage_passed: false,
                artifact_validated: false,
            },
            &report,
        );

        assert_eq!(
            decision.blockers,
            vec![
                RhoFlipBlocker::Coverage,
                RhoFlipBlocker::ArtifactValidation,
                RhoFlipBlocker::ChannelDeadlocks(report.diagnostics.clone()),
            ]
        );
    }

    #[test]
    fn artifact_validation_blocks_flip() {
        let decision = decide_rho_flip(
            RhoFlipGates {
                coverage_passed: true,
                artifact_validated: false,
            },
            &clean_report(),
        );

        assert!(!decision.can_flip_to_rho());
        assert_eq!(decision.blockers, vec![RhoFlipBlocker::ArtifactValidation]);
    }
}
