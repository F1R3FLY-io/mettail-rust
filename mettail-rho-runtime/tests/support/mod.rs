use std::path::{Path, PathBuf};

use mettail_rho_codegen::RhoEvidenceRefAuditPolicy;

pub fn workspace_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("mettail-rho-runtime must be a workspace member")
        .to_path_buf()
}

pub fn strict_evidence_audit_policy() -> RhoEvidenceRefAuditPolicy {
    RhoEvidenceRefAuditPolicy::new(workspace_root())
}
