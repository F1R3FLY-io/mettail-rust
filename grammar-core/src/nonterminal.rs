//! Original nonterminal classification, shared by authored and surface inputs.
//!
//! `NonTerminalKindProjection.v` proves the exact method/variant relocation.
//! The Serde enum name retains the pre-existing authored-store wire metadata;
//! `ast::grammar` and `AuthoredNonTerminalKind` re-export this same definition.

use serde::{Deserialize, Serialize};

/// Classification of a nonterminal reference in a grammar rule.
///
/// Determined once at construction time based on the nonterminal name.
/// Replaces scattered string comparisons throughout code generation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename = "AuthoredNonTerminalKind")]
pub enum NonTerminalKind {
    /// Variable reference (`Var`) — stored as `OrdVar`, not boxed
    Var,
    /// Integer literal (`Integer`) — stored as native int type, not boxed
    Integer,
    /// Boolean literal (`Boolean`) — stored as `bool`, not boxed
    Boolean,
    /// String literal (`StringLiteral`) — stored as `String`, not boxed
    StringLiteral,
    /// Float literal (`FloatLiteral`) — stored as canonical float, not boxed
    FloatLiteral,
    /// Identifier TEXT (`Ident`) — stored as a bare `std::string::String`, not boxed.
    ///
    /// The builtin `Ident` token class given a first-class mid-rule surface: a position
    /// that consumes ONE `Token::Ident` and carries its text INERTLY, with none of
    /// [`Self::Var`]'s binder semantics. The distinction is the whole point — `Var`
    /// lowers to `mettail_runtime::OrdVar`, which `subst` canonicalises under unify, so a
    /// `Var`-typed method name inside `new nth in { … }` would be CAPTURED by the binder.
    /// An `Ident`-typed field is a `String` and no substitution can see it.
    ///
    /// Both Rholang oracles spell the method name with their `var` TOKEN
    /// (BNFC `rholang_mercury.cf:41` `PMethod. Proc11 ::= Proc11 "." Var "(" [Proc] ")"`,
    /// tree-sitter `grammar.js:293-298` `field('name', $.var)`) — a lexical class, not a
    /// binding construct, which is exactly what this kind models.
    ///
    /// ⚠ MEASURED ALTERNATIVE, REJECTED. The other way to reach a mid-rule String is a
    /// declared `tokens { }` kind consumed by a `m@Kind` capture. For a kind co-extensive
    /// with `Ident` that is not free: measured on Rholang, declaring it alone moved the
    /// lexer's multi-accept DFA states from 4/474 (0.8 %) to 379/475 (79.8 %) and
    /// alt-accept edges from 482 to 1234 (×2.56), because `subset.rs`'s reservation
    /// `retain` deletes only `TokenKind::Ident` and cannot delete a `Custom` co-accept.
    /// Parse time over the shipped 11-input corpus regressed geomean ×2.49, worst ×8.59
    /// (`{p | q}`), with inputs containing no identifier flat at ×1.03 as the control.
    /// It is also LESS conformant: a `Custom` kind co-accepts at reserved-keyword states
    /// too, so `x.new()` would parse, where both oracles reject it.
    Ident,
    /// A reference to a user-defined category (e.g., `Proc`, `Name`, `Expr`)
    Category,
}

impl NonTerminalKind {
    /// Classify a nonterminal by its name string.
    #[inline]
    pub fn classify(name: &str) -> Self {
        match name {
            "Var" => Self::Var,
            "Integer" => Self::Integer,
            "Boolean" => Self::Boolean,
            "StringLiteral" => Self::StringLiteral,
            "FloatLiteral" => Self::FloatLiteral,
            "Ident" => Self::Ident,
            _ => Self::Category,
        }
    }

    /// Returns true if this is any literal kind (Integer, Boolean, StringLiteral, FloatLiteral).
    #[inline]
    pub fn is_literal(self) -> bool {
        matches!(self, Self::Integer | Self::Boolean | Self::StringLiteral | Self::FloatLiteral)
    }

    /// Returns true if this is a built-in type (Var or any literal) — not a user-defined category.
    #[inline]
    pub fn is_builtin(self) -> bool {
        self != Self::Category
    }
}
