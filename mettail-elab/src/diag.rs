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
    /// `\/` joining two theories that introduce the same label independently.
    JoinCollision,
    /// Import or name resolution.
    Resolution,
    /// A malformed or unsupported canonical `Data(v)` fragment.
    Value,
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
            DiagKind::JoinCollision => "join-collision",
            DiagKind::Resolution => "resolution",
            DiagKind::Value => "value",
        }
    }
}

#[derive(Clone, Debug)]
pub struct Diag {
    pub kind: DiagKind,
    pub msg: String,
    pub span: Span,
}

impl Diag {
    pub fn new(kind: DiagKind, msg: impl Into<String>, span: Span) -> Diag {
        Diag { kind, msg: msg.into(), span }
    }
}

impl fmt::Display for Diag {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: [{}] {}", self.span, self.kind.name(), self.msg)
    }
}

impl std::error::Error for Diag {}
