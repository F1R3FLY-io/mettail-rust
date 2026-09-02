//! Diagnostics.
//!
//! Plan §7 requires three checks to be reported as *named, located*
//! diagnostics rather than as parse failures:
//!
//!   * `RepeatLabel`         - duplicate label within one theory
//!   * `ReplacementShadows`  - a replacement target colliding with an existing label
//!   * `ForwardReference`    - an `Equations`/`Rewrites` block mentioning a
//!     label introduced by a later `Terms` block
//!
//! The remaining kinds arise from the §3.4 additions.

use crate::lex::Span;
use std::fmt;

/// Structured source identity retained independently of diagnostic wording.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SourceProvenance {
    pub reference: String,
    pub content_commitment: Option<[u8; 32]>,
    pub import_chain: Vec<String>,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum DiagKind {
    Parse,
    /// Plan §7, from `bad/RepeatLabel.module`.
    RepeatLabel,
    /// Plan §7, from `bad/ReplacementShadows.module`.
    ReplacementShadows,
    /// Plan §7, new: the builder chain is ordered (plan §3.2).
    ForwardReference,
    /// G1: a term rule whose result or argument sort was never declared.
    UndeclaredCategory,
    /// G2: an unknown collection sort.
    UnknownCollection,
    /// G6: an argument not referenced exactly once in the concrete syntax.
    ArgumentUse,
    /// A replacement naming a label the theory does not have.
    UnknownReplacementTarget,
    /// Two declarations in one module use the same theory name.
    DuplicateTheory,
    /// Two imports, or an import and a local theory, bind the same module-scope name.
    DuplicateImport,
    /// Two `theory ...` entries export the same language name.
    DuplicateExport,
    /// A compound `theory ...` entry has no stable declared language name.
    UnnamedExport,
    /// `\/` joining two theories that introduce the same label independently.
    JoinCollision,
    /// Import or name resolution.
    Resolution,
    /// Signed Registry source and its canonical `module/1` projection differ.
    RegistryProjection,
    /// A malformed or unsupported canonical `Data(v)` fragment.
    Value,
    /// A deterministic resource-admission bound was exceeded.
    ResourceLimit,
}

impl DiagKind {
    pub fn name(&self) -> &'static str {
        match self {
            DiagKind::Parse => "parse",
            DiagKind::RepeatLabel => "repeat-label",
            DiagKind::ReplacementShadows => "replacement-shadows",
            DiagKind::ForwardReference => "forward-reference",
            DiagKind::UndeclaredCategory => "undeclared-category",
            DiagKind::UnknownCollection => "unknown-collection",
            DiagKind::ArgumentUse => "argument-use",
            DiagKind::UnknownReplacementTarget => "unknown-replacement-target",
            DiagKind::DuplicateTheory => "duplicate-theory",
            DiagKind::DuplicateImport => "duplicate-import",
            DiagKind::DuplicateExport => "duplicate-export",
            DiagKind::UnnamedExport => "unnamed-export",
            DiagKind::JoinCollision => "join-collision",
            DiagKind::Resolution => "resolution",
            DiagKind::RegistryProjection => "registry-projection",
            DiagKind::Value => "value",
            DiagKind::ResourceLimit => "resource-limit",
        }
    }
}

#[derive(Clone, Debug)]
pub struct Diag {
    pub kind: DiagKind,
    pub msg: String,
    pub span: Span,
    pub provenance: Option<SourceProvenance>,
}

impl Diag {
    pub fn new(kind: DiagKind, msg: impl Into<String>, span: Span) -> Diag {
        Diag {
            kind,
            msg: msg.into(),
            span,
            provenance: None,
        }
    }

    pub fn with_provenance(mut self, provenance: SourceProvenance) -> Self {
        self.provenance = Some(provenance);
        self
    }

    pub fn attach_provenance(&mut self, provenance: SourceProvenance) {
        if self.provenance.is_none() {
            self.provenance = Some(provenance);
        }
    }
}

impl fmt::Display for Diag {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: [{}] {}", self.span, self.kind.name(), self.msg)?;
        if let Some(provenance) = &self.provenance {
            write!(f, " [source: {}", provenance.reference)?;
            if let Some(commitment) = provenance.content_commitment {
                write!(f, ", blake3:")?;
                for byte in commitment {
                    write!(f, "{byte:02x}")?;
                }
            }
            write!(f, "]")?;
        }
        Ok(())
    }
}

impl std::error::Error for Diag {}
