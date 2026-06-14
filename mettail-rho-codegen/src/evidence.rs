//! Shared Rho evidence-reference audit helpers.
//!
//! Production Rho execution boundaries use these checks to make evidence refs
//! reviewable artifacts rather than free-form labels.

use std::collections::BTreeSet;
use std::path::{Component, Path, PathBuf};

/// Evidence-reference audit policy for production Rho plans.
///
/// Repository-relative references must resolve to existing local artifacts, and
/// logical evidence identifiers must use an explicitly allowed prefix.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RhoEvidenceRefAuditPolicy {
    repo_root: PathBuf,
    allowed_logical_prefixes: BTreeSet<String>,
}

impl RhoEvidenceRefAuditPolicy {
    /// Build a strict local-artifact audit rooted at the repository. Logical
    /// evidence identifiers are rejected unless their prefix is explicitly
    /// allowed with [`Self::with_allowed_logical_prefix`].
    pub fn new(repo_root: impl Into<PathBuf>) -> Self {
        Self {
            repo_root: repo_root.into(),
            allowed_logical_prefixes: BTreeSet::new(),
        }
    }

    /// Permit a non-file evidence namespace such as
    /// `mettail-rho-codegen:artifact-validation` or `native-handler:Rule`.
    pub fn with_allowed_logical_prefix(mut self, prefix: impl Into<String>) -> Self {
        self.allowed_logical_prefixes.insert(prefix.into());
        self
    }

    pub fn repo_root(&self) -> &Path {
        &self.repo_root
    }

    pub fn allowed_logical_prefixes(&self) -> &BTreeSet<String> {
        &self.allowed_logical_prefixes
    }
}

/// Evidence-reference audit diagnostics surfaced by strict production
/// planners.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RhoEvidenceRefAuditDiagnostic {
    AbsoluteLocalPath {
        evidence_ref: String,
    },
    ParentComponent {
        evidence_ref: String,
    },
    MissingLocalPath {
        evidence_ref: String,
        resolved_path: String,
    },
    DisallowedLogicalRef {
        evidence_ref: String,
        prefix: String,
    },
    MissingLogicalPrefix {
        evidence_ref: String,
    },
}

/// Whether a successful Rho plan was built with evidence-reference auditing
/// enabled.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RhoEvidenceAuditStatus {
    /// The planner checked Boolean gates and nonblank evidence refs, but did
    /// not verify that repository-local evidence paths exist or that logical
    /// evidence namespaces were explicitly allowed.
    NotAudited,
    /// The planner verified repository-local evidence paths and logical
    /// evidence namespaces under a caller-supplied audit policy.
    Audited,
}

fn evidence_ref_logical_prefix(evidence_ref: &str) -> Option<&str> {
    let colon = evidence_ref.find(':')?;
    let slash = evidence_ref.find(['/', '\\']).unwrap_or(usize::MAX);
    (colon < slash).then_some(&evidence_ref[..colon])
}

pub(crate) fn audit_one_evidence_ref(
    policy: &RhoEvidenceRefAuditPolicy,
    evidence_ref: &str,
) -> Vec<RhoEvidenceRefAuditDiagnostic> {
    let trimmed = evidence_ref.trim();
    let mut diagnostics = Vec::new();

    if let Some(prefix) = evidence_ref_logical_prefix(trimmed) {
        if prefix.is_empty() {
            diagnostics.push(RhoEvidenceRefAuditDiagnostic::MissingLogicalPrefix {
                evidence_ref: trimmed.to_string(),
            });
        } else if !policy.allowed_logical_prefixes.contains(prefix) {
            diagnostics.push(RhoEvidenceRefAuditDiagnostic::DisallowedLogicalRef {
                evidence_ref: trimmed.to_string(),
                prefix: prefix.to_string(),
            });
        }
        return diagnostics;
    }

    let path = Path::new(trimmed);
    if path.is_absolute() {
        diagnostics.push(RhoEvidenceRefAuditDiagnostic::AbsoluteLocalPath {
            evidence_ref: trimmed.to_string(),
        });
        return diagnostics;
    }
    if path
        .components()
        .any(|component| component == Component::ParentDir)
    {
        diagnostics.push(RhoEvidenceRefAuditDiagnostic::ParentComponent {
            evidence_ref: trimmed.to_string(),
        });
        return diagnostics;
    }

    let resolved = policy.repo_root.join(path);
    if !resolved.exists() {
        diagnostics.push(RhoEvidenceRefAuditDiagnostic::MissingLocalPath {
            evidence_ref: trimmed.to_string(),
            resolved_path: resolved.display().to_string(),
        });
    }

    diagnostics
}

pub(crate) fn audit_evidence_refs<'a>(
    evidence_refs: impl IntoIterator<Item = &'a String>,
    policy: Option<&RhoEvidenceRefAuditPolicy>,
) -> Vec<RhoEvidenceRefAuditDiagnostic> {
    let Some(policy) = policy else {
        return Vec::new();
    };

    evidence_refs
        .into_iter()
        .flat_map(|evidence_ref| audit_one_evidence_ref(policy, evidence_ref))
        .collect()
}
