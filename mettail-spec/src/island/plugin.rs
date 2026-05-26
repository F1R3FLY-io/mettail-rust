//! Island language plugins.

use crate::error::Result;
use crate::island::template::IslandTemplate;
use crate::surface::IslandToken;

/// Result of processing an island through a plugin.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IslandArtifact {
    /// Rust items / expressions validated for host context.
    RustContext { snippet: String },
    /// Rholang process fragment (GST snapshot).
    RholangProc { gst: ProcGst },
}

/// Minimal GST for Rholang process islands (Phase 3 MVP).
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize)]
pub enum ProcGst {
    Empty,
    Stmt(ProcStmt),
    Seq(Vec<ProcGst>),
}

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize)]
pub enum ProcStmt {
    Let {
        name: String,
        body: String,
    },
    For {
        bind: String,
        source: String,
        body: String,
    },
    Send {
        channel: String,
        payload: String,
    },
    Raw(String),
}

/// Plugin for a single island language label.
pub trait IslandPlugin: Send + Sync {
    fn lang_names(&self) -> &[&str];
    fn process(&self, token: &IslandToken) -> Result<IslandArtifact>;
}

/// Build template from token body (already escape-decoded by lexer).
pub fn template_from_token(token: &IslandToken) -> IslandTemplate {
    crate::island::template::split_template(&token.body)
}
