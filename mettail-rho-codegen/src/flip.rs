//! Per-language Rho-default flip gate.
//!
//! This is the Rust-side image of `RhoBackendFlipGate.v`: a language can use
//! the Rho backend by default exactly when the planner can validate exact
//! coverage, generated artifact shape, and static channel-deadlock gates.

use crate::deadlock::{ChannelDeadlockDiagnostic, ChannelDeadlockReport};
use crate::guard_quality::RhoGuardQuality;

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
    /// A covered guard obligation carries an evidence quality that refuses
    /// production-default lowering (`RhoGuardQuality::refuses_production_default`,
    /// i.e. `Unknown`). The predicate substrate could not derive usable evidence
    /// for the obligation, so the fail-closed gate refuses the flip. This mirrors
    /// the doc-08 rule "`Unknown` quality ⇒ production-default refused" and the
    /// Rocq model `RhoBackendFlipGate.unknown_guard_quality_blocks_default_backend`.
    GuardQuality {
        obligation: String,
        quality: RhoGuardQuality,
    },
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
///
/// `guard_quality_blockers` carries any [`RhoFlipBlocker::GuardQuality`] the
/// planner derived from the predicate substrate (a covered guard obligation
/// whose [`RhoGuardQuality`] refuses production-default lowering). They are
/// pre-computed by the caller — the planner owns disposition→quality derivation
/// via [`crate::guard_quality::derive_guard_qualities`] — and folded in here so
/// this Boolean gate remains the single place blockers are assembled. Callers
/// with no guard-quality findings pass an empty vector.
pub fn decide_rho_flip(
    gates: RhoFlipGates,
    deadlock_report: &ChannelDeadlockReport,
    guard_quality_blockers: Vec<RhoFlipBlocker>,
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
    blockers.extend(guard_quality_blockers);

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
        let decision = decide_rho_flip(passing_gates(), &clean_report(), Vec::new());
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
            Vec::new(),
        );

        assert!(!decision.can_flip_to_rho());
        assert_eq!(decision.blockers, vec![RhoFlipBlocker::Coverage]);
    }

    #[test]
    fn channel_deadlock_diagnostics_block_flip() {
        let report = analyze_channel_deadlocks(
            &ChannelNetwork::new().with_contract(ContractFlow::new("needs_b", ["b"], ["out"])),
        );
        let decision = decide_rho_flip(passing_gates(), &report, Vec::new());

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
            Vec::new(),
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
            Vec::new(),
        );

        assert!(!decision.can_flip_to_rho());
        assert_eq!(decision.blockers, vec![RhoFlipBlocker::ArtifactValidation]);
    }

    #[test]
    fn unknown_guard_quality_blocks_flip() {
        // A covered obligation whose substrate quality is `Unknown` is the new
        // fail-closed blocker: even with every Boolean gate passing and a clean
        // deadlock report, an `Unknown`-quality guard refuses the flip.
        let guard_blocker = RhoFlipBlocker::GuardQuality {
            obligation: "predicate:mystery".to_string(),
            quality: RhoGuardQuality::Unknown,
        };
        let decision =
            decide_rho_flip(passing_gates(), &clean_report(), vec![guard_blocker.clone()]);

        assert!(!decision.can_flip_to_rho());
        assert_eq!(decision.blockers, vec![guard_blocker]);
    }

    #[test]
    fn guard_quality_blocker_joins_other_blockers() {
        // The guard-quality blocker is appended after the Boolean/deadlock
        // blockers, so a fully-failing gate surfaces all four at once.
        let report = analyze_channel_deadlocks(
            &ChannelNetwork::new().with_contract(ContractFlow::new("needs_b", ["b"], ["out"])),
        );
        let guard_blocker = RhoFlipBlocker::GuardQuality {
            obligation: "term:Guarded:guard:0".to_string(),
            quality: RhoGuardQuality::Unknown,
        };
        let decision = decide_rho_flip(
            RhoFlipGates {
                coverage_passed: false,
                artifact_validated: false,
            },
            &report,
            vec![guard_blocker.clone()],
        );

        assert_eq!(
            decision.blockers,
            vec![
                RhoFlipBlocker::Coverage,
                RhoFlipBlocker::ArtifactValidation,
                RhoFlipBlocker::ChannelDeadlocks(report.diagnostics.clone()),
                guard_blocker,
            ]
        );
    }
}
