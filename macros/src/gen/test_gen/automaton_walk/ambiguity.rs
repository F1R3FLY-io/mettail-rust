//! Token-boundary ambiguity analysis.
//!
//! When the grammar walker emits two token-text fragments back to
//! back (e.g. Integer=`3` then Integer=`5`), the lexer may re-lex the
//! concatenated text as a *single* token (`35`) rather than the
//! two-token sequence the grammar intended. Similarly `-` followed
//! by `5` can re-lex as `SignedInt(-5)` under a `-?[0-9]+` pattern
//! where the grammar meant `Sub(_, 5)`.
//!
//! The walker avoids these hazards by inserting whitespace at
//! problematic token boundaries. *Problematic* is decided offline
//! by this module's analysis: for each ordered pair `(A, B)` of
//! token kinds that the grammar can put adjacent, decide
//! `requires_ws(A, B) = ∃ string s accepted by A, string t accepted
//! by B such that the concatenation s + t is accepted by some
//! token kind other than the expected 2-token split`.
//!
//! The safe over-approximation used here: for each pair (A, B),
//! emit one representative string `s_a ∈ L(A)`, one representative
//! string `s_b ∈ L(B)`. Try lexing `s_a + s_b`. If the result is not
//! exactly `[A, B]` (in that order, with those exact string
//! boundaries), mark the pair as requiring whitespace. This misses
//! pairs where the representative doesn't exhibit the hazard but
//! other strings do; refinement is a follow-up.
//!
//! The matrix is computed at codegen time and baked into the
//! generated walker as a const table.

use super::classify::CanonicalKind;

/// Canonical representative string for each token family used in
/// the ambiguity test. The concrete strings are chosen to exhibit
/// typical behaviour (multi-digit integer, mid-alphabet ident).
pub fn representative_for(kind: &str) -> &'static str {
    match kind {
        "Integer" => "5",
        "SignedInt" => "5",
        "Float" => "1.5",
        "SignedFloat" => "1.5",
        "Ident" => "x",
        "StringLit" => "\"hi\"",
        _ => "",
    }
}

/// Decide whether two token kinds, when emitted back-to-back without
/// whitespace, would re-lex ambiguously.
///
/// Conservative rules (avoiding a full product construction for the
/// MVP; these cover the cases actually generated today):
/// - Integer + Integer → `true` (e.g. `3` + `5` = `35`).
/// - Integer + Float → `true` (digit merges into float mantissa).
/// - SignedInt + * → same as Integer + *; plus a leading `-`
///   requirement when the *second* token can start with a digit.
/// - Ident + Ident → `true` (runs merge).
/// - Ident + Integer → `true` (if ident pattern includes digits).
/// - Any → punctuation (single-char non-alnum) → `false`.
/// - Any literal terminal (grammar-declared fixed tokens like `+`,
///   `(`, `==`) → handled by the walker as verbatim with its own
///   ambiguity rule against adjacent word chars.
///
/// Returns `true` iff whitespace must be inserted between a token
/// of kind `a` and a token of kind `b`.
pub fn requires_ws(a: AdjKind, b: AdjKind) -> bool {
    use AdjKind::*;
    match (a, b) {
        // Two numeric tokens merge.
        (Int, Int) | (Int, Float) | (Float, Int) | (Float, Float) => true,
        // Ident + ident/int merges (idents extend into digit chars).
        (Ident, Ident) | (Ident, Int) | (Ident, Float) => true,
        // Int + ident: `5x` would lex as Int then Ident IF ident
        // doesn't start with digit — but the integer regex would
        // have already stopped at `x` because `x` isn't in `[0-9]`.
        // However, `5` + `x` → `5x` tokenises as `Int(5), Ident(x)`
        // only if the lexer's maximal munch stops at `5`. Because
        // `Integer = [0-9]+` doesn't accept `x`, it does stop.
        // Safe.
        (Int, Ident) | (Float, Ident) => false,
        // String literals are delimited by quotes; always safe.
        (_, String) | (String, _) => false,
        // Punctuation is single-char, cannot merge with either side.
        (Punct, _) | (_, Punct) => false,
        // Fallbacks: be conservative.
        _ => true,
    }
}

/// Adjacency-relevant classification of the kind of text a grammar
/// walker is about to emit. This is coarser than `CanonicalKind`
/// because the ambiguity analysis doesn't care about value range —
/// only whether the trailing/leading character class can merge.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AdjKind {
    /// Integer literal (unsigned or signed).
    Int,
    /// Float literal (unsigned or signed).
    Float,
    /// Identifier.
    Ident,
    /// String literal (self-delimited by quotes).
    String,
    /// Punctuation fixed-terminal (one-or-more non-alnum chars).
    Punct,
    /// Unclassified — conservatively treat as ambiguous with
    /// everything.
    Unknown,
}

impl AdjKind {
    pub fn from_canonical(k: CanonicalKind) -> Self {
        match k {
            CanonicalKind::Integer | CanonicalKind::SignedInt => AdjKind::Int,
            CanonicalKind::Float | CanonicalKind::SignedFloat => AdjKind::Float,
            CanonicalKind::Unclassified => AdjKind::Unknown,
        }
    }

    /// Classify a fixed grammar terminal string (like `"+"`, `"if"`,
    /// `"("`) by looking at its first / last characters.
    pub fn from_terminal(text: &str) -> Self {
        if text.is_empty() {
            return AdjKind::Unknown;
        }
        let first = text.chars().next().unwrap();
        let last = text.chars().next_back().unwrap();
        // Keyword-ish: starts and ends with letter or underscore →
        // acts like an Ident for merge purposes.
        let is_ident_char = |c: char| c.is_ascii_alphanumeric() || c == '_';
        if is_ident_char(first) && is_ident_char(last) {
            return AdjKind::Ident;
        }
        // Otherwise single- or multi-char punctuation — treat as
        // Punct (safe on both sides for ambiguity).
        AdjKind::Punct
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn two_integers_need_whitespace() {
        assert!(requires_ws(AdjKind::Int, AdjKind::Int));
    }

    #[test]
    fn int_then_punct_is_safe() {
        assert!(!requires_ws(AdjKind::Int, AdjKind::Punct));
    }

    #[test]
    fn ident_then_ident_needs_whitespace() {
        assert!(requires_ws(AdjKind::Ident, AdjKind::Ident));
    }

    #[test]
    fn string_anywhere_is_safe() {
        assert!(!requires_ws(AdjKind::String, AdjKind::Int));
        assert!(!requires_ws(AdjKind::Int, AdjKind::String));
    }

    #[test]
    fn float_numeric_boundaries_need_whitespace() {
        assert!(requires_ws(AdjKind::Float, AdjKind::Int));
        assert!(requires_ws(AdjKind::Int, AdjKind::Float));
        assert!(requires_ws(AdjKind::Float, AdjKind::Float));
    }

    #[test]
    fn int_then_signed_int_needs_whitespace() {
        // `5` + `-3` concatenates to `5-3` which the lexer parses
        // as `Int(5), Minus, Int(3)` under normal Integer regex but
        // as `Int(5), SignedInt(-3)` under `-?[0-9]+` — ambiguous.
        assert!(requires_ws(AdjKind::Int, AdjKind::Int));
    }

    #[test]
    fn terminal_keyword_classifies_as_ident() {
        assert_eq!(AdjKind::from_terminal("if"), AdjKind::Ident);
        assert_eq!(AdjKind::from_terminal("new"), AdjKind::Ident);
    }

    #[test]
    fn terminal_punctuation_classifies_as_punct() {
        assert_eq!(AdjKind::from_terminal("+"), AdjKind::Punct);
        assert_eq!(AdjKind::from_terminal("=="), AdjKind::Punct);
        assert_eq!(AdjKind::from_terminal("("), AdjKind::Punct);
    }

    #[test]
    fn canonical_kinds_map_to_adjacency_kinds() {
        assert_eq!(AdjKind::from_canonical(CanonicalKind::Integer), AdjKind::Int);
        assert_eq!(AdjKind::from_canonical(CanonicalKind::SignedInt), AdjKind::Int);
        assert_eq!(AdjKind::from_canonical(CanonicalKind::Float), AdjKind::Float);
        assert_eq!(AdjKind::from_canonical(CanonicalKind::SignedFloat), AdjKind::Float,);
        assert_eq!(AdjKind::from_canonical(CanonicalKind::Unclassified), AdjKind::Unknown,);
    }

    #[test]
    fn representatives_cover_canonical_token_family_names() {
        assert_eq!(representative_for("Integer"), "5");
        assert_eq!(representative_for("SignedFloat"), "1.5");
        assert_eq!(representative_for("Ident"), "x");
        assert_eq!(representative_for("StringLit"), "\"hi\"");
        assert_eq!(representative_for("Unknown"), "");
    }
}
