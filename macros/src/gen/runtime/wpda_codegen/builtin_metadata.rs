//! Built-in type metadata — shape recognizers and lattice queries.
//!
//! **Stage 3.27d-pre + 3.13 + 3.27d + 3.27f shared infrastructure (2026-04-30).**
//!
//! This module is the single source of truth for:
//!
//! 1. **Shape recognizers** — pure structural predicates over `GrammarRule`.
//!    Used by both Stage 3.27d (G-PREFIX-BP) and Stage 3.27f
//!    (G-INTEGER-OVERFLOW-FORK) plus Stage 3.13 (auto-injection codegen).
//!    No dependency on `BuiltinTypeLattice`.
//!
//! ## Why a shared module?
//!
//! The shape recognizer for unary-prefix rules and the shape recognizer
//! for simple cross-cat projection rules share the same `tc.len() == 1`
//! single-Simple-param invariant — they branch on one extra check
//! (whether `T == rule.category` or not). Putting them in one module
//! consolidates the underlying invariant test and makes future
//! built-in-aware features have a single place to look.
//!
//! ## Future-proof contract
//!
//! Adding a new built-in type (e.g., `Decimal128`):
//! 1. Add `NativeKind::Decimal128` variant to `ast/src/language.rs`.
//! 2. Update `from_syn_type` arm.
//! 3. Add lossless edges to `BuiltinTypeLattice` impl
//!    (`Decimal128 -> [CanonicalBigRat]` etc.).
//! 4. Update `standard_token_variant`.
//!
//! No code change in `binder.rs`, `prefix.rs`, `infix.rs`, or
//! `semantic_actions.rs` is needed for the shared shape recognizers.

use mettail_ast::grammar::{GrammarRule, SyntaxExpr, TermParam};
use mettail_ast::types::TypeExpr;

/// Recognized shape of a unary-prefix rule.
///
/// Returned by `classify_unary_prefix_shape` when the rule matches
/// the pattern `Label . a:T |- "literal" a : T;` with a single Simple
/// parameter, no binder/guard/opt-group, and `T == rule.category`.
#[derive(Debug, Clone)]
pub struct UnaryPrefixShape {
    /// The trigger literal (e.g., `"-"`, `"bitnot"`, `"not"`).
    pub trigger: String,
    /// The operand category (== `rule.category`).
    pub operand_category: String,
}

/// Recognized shape of a simple single-param cross-cat projection rule.
///
/// Returned by `classify_simple_projection_shape` when the rule matches
/// the pattern `Label . v:Source |- v : Target;` with a single Simple
/// parameter, no syntax literals, and `Source != Target`.
///
/// Examples: `IntToBigInt . i:Int |- i : BigInt`,
/// `ProcInt . i:Int |- i : Proc`.
///
/// **Used by:** Stage 3.13 auto-injection, which detects user-defined
/// projections and skips synthesizing duplicates.
#[derive(Debug, Clone)]
pub struct SimpleProjectionShape {
    /// The source category (the operand's type).
    pub source_category: String,
    /// The target category (== `rule.category`).
    pub target_category: String,
}

/// Classify a `GrammarRule` as a unary-prefix rule, if it matches.
///
/// **Predicate (all must hold):**
/// - `term_context.len() == 1`
/// - `syntax_pattern.len() == 2`
/// - `tc[0] = TermParam::Simple { name, ty: TypeExpr::Base(T) }`
/// - `sp[0] = SyntaxExpr::Literal(trigger)`
/// - `sp[1] = SyntaxExpr::Param(name)` with `name == param_name from tc[0]`
/// - `T == rule.category`
///
/// **Excluded by construction:**
/// - Binder rules (would require `Abstraction` / `MultiAbstraction` / `GuardBody`)
/// - Opt-group rules (`Optional` term param)
/// - Mixfix rules (sp.len() != 2)
/// - Cross-cat projections (handled by `classify_simple_projection_shape`)
/// - Function-call-form prefixes (e.g., `negate(x)` — different sp shape)
///
/// **Returns** `None` for non-unary-prefix shapes (the common case).
pub fn classify_unary_prefix_shape(rule: &GrammarRule) -> Option<UnaryPrefixShape> {
    let tc = rule.term_context.as_ref()?;
    let sp = rule.syntax_pattern.as_ref()?;

    if tc.len() != 1 || sp.len() != 2 {
        return None;
    }

    let (param_name, ty) = match &tc[0] {
        TermParam::Simple { name, ty } => (name.to_string(), ty),
        _ => return None,
    };

    let operand_category = match ty {
        TypeExpr::Base(t) => t.to_string(),
        _ => return None,
    };

    if operand_category != rule.category.to_string() {
        return None;
    }

    let trigger = match &sp[0] {
        SyntaxExpr::Literal(lit) => lit.clone(),
        _ => return None,
    };

    match &sp[1] {
        SyntaxExpr::Param(p) if p.to_string() == param_name => {},
        _ => return None,
    }

    Some(UnaryPrefixShape { trigger, operand_category })
}

/// Classify a `GrammarRule` as a simple cross-cat projection rule, if
/// it matches.
///
/// **Predicate (all must hold):**
/// - `term_context.len() == 1`
/// - `syntax_pattern.len() == 1`
/// - `tc[0] = TermParam::Simple { name, ty: TypeExpr::Base(T) }`
/// - `sp[0] = SyntaxExpr::Param(name)` with same name as tc[0]
/// - `T != rule.category` (cross-cat — same-cat would be a no-op rule)
///
/// **Used by:** Stage 3.13 detects user-supplied injections; Stage 3.27f
/// finds projection rules through which to emit promotion-Fork branches.
pub fn classify_simple_projection_shape(rule: &GrammarRule) -> Option<SimpleProjectionShape> {
    let tc = rule.term_context.as_ref()?;
    let sp = rule.syntax_pattern.as_ref()?;

    if tc.len() != 1 || sp.len() != 1 {
        return None;
    }

    let (param_name, ty) = match &tc[0] {
        TermParam::Simple { name, ty } => (name.to_string(), ty),
        _ => return None,
    };

    let source_category = match ty {
        TypeExpr::Base(t) => t.to_string(),
        _ => return None,
    };

    let target_category = rule.category.to_string();

    if source_category == target_category {
        return None;
    }

    match &sp[0] {
        SyntaxExpr::Param(p) if p.to_string() == param_name => {},
        _ => return None,
    }

    Some(SimpleProjectionShape { source_category, target_category })
}

#[cfg(test)]
mod tests {
    use super::*;
    use mettail_ast::grammar::{GrammarRule, SyntaxExpr, TermParam};
    use mettail_ast::types::TypeExpr;
    use proc_macro2::Span;
    use syn::Ident;

    fn ident(s: &str) -> Ident {
        Ident::new(s, Span::call_site())
    }

    /// Build a minimal GrammarRule with judgement-style fields populated.
    fn make_rule(
        label: &str,
        category: &str,
        term_context: Vec<TermParam>,
        syntax_pattern: Vec<SyntaxExpr>,
    ) -> GrammarRule {
        GrammarRule {
            label: ident(label),
            category: ident(category),
            items: Vec::new(),
            bindings: Vec::new(),
            term_context: Some(term_context),
            syntax_pattern: Some(syntax_pattern),
            rust_code: None,
            eval_mode: None,
            is_right_assoc: false,
            prefix_bp: None,
            tier_directive: None,
            is_auto_injected: false,
            doc_comment: None,
        }
    }

    fn simple_param(name: &str, ty: &str) -> TermParam {
        TermParam::Simple {
            name: ident(name),
            ty: TypeExpr::Base(ident(ty)),
        }
    }

    #[test]
    fn detects_canonical_neg_int_prefix() {
        // Neg . a:Int |- "-" a : Int
        let rule = make_rule(
            "Neg",
            "Int",
            vec![simple_param("a", "Int")],
            vec![SyntaxExpr::Literal("-".to_string()), SyntaxExpr::Param(ident("a"))],
        );
        let shape = classify_unary_prefix_shape(&rule).expect("should classify");
        assert_eq!(shape.trigger, "-");
        assert_eq!(shape.operand_category, "Int");
    }

    #[test]
    fn detects_bitnot_int_prefix() {
        // BitNotInt . a:Int |- "bitnot" a : Int
        let rule = make_rule(
            "BitNotInt",
            "Int",
            vec![simple_param("a", "Int")],
            vec![SyntaxExpr::Literal("bitnot".to_string()), SyntaxExpr::Param(ident("a"))],
        );
        let shape = classify_unary_prefix_shape(&rule).expect("should classify");
        assert_eq!(shape.trigger, "bitnot");
    }

    #[test]
    fn rejects_cross_cat_projection_as_prefix() {
        // ProcInt . i:Int |- i : Proc — single-param projection, NOT prefix
        let rule = make_rule(
            "ProcInt",
            "Proc",
            vec![simple_param("i", "Int")],
            vec![SyntaxExpr::Param(ident("i"))],
        );
        assert!(classify_unary_prefix_shape(&rule).is_none());
        let proj = classify_simple_projection_shape(&rule).expect("should classify");
        assert_eq!(proj.source_category, "Int");
        assert_eq!(proj.target_category, "Proc");
    }

    #[test]
    fn rejects_binary_infix_as_prefix() {
        // Add . l:Int, r:Int |- l "+" r : Int
        let rule = make_rule(
            "Add",
            "Int",
            vec![simple_param("l", "Int"), simple_param("r", "Int")],
            vec![
                SyntaxExpr::Param(ident("l")),
                SyntaxExpr::Literal("+".to_string()),
                SyntaxExpr::Param(ident("r")),
            ],
        );
        assert!(classify_unary_prefix_shape(&rule).is_none());
        assert!(classify_simple_projection_shape(&rule).is_none());
    }

    #[test]
    fn rejects_same_cat_simple_param_as_projection() {
        // A no-op `Identity . v:Int |- v : Int` (hypothetical) — not a
        // valid cross-cat projection.
        let rule = make_rule(
            "Identity",
            "Int",
            vec![simple_param("v", "Int")],
            vec![SyntaxExpr::Param(ident("v"))],
        );
        assert!(classify_simple_projection_shape(&rule).is_none());
    }

    #[test]
    fn rejects_legacy_old_style_rule() {
        // Old-style BNF rule has `term_context: None` — recognizer must
        // return None even if the pattern superficially matches.
        let rule = GrammarRule {
            label: ident("PAmb"),
            category: ident("Proc"),
            items: Vec::new(),
            bindings: Vec::new(),
            term_context: None,
            syntax_pattern: None,
            rust_code: None,
            eval_mode: None,
            is_right_assoc: false,
            prefix_bp: None,
            tier_directive: None,
            is_auto_injected: false,
            doc_comment: None,
        };
        assert!(classify_unary_prefix_shape(&rule).is_none());
        assert!(classify_simple_projection_shape(&rule).is_none());
    }

    #[test]
    fn rejects_param_name_mismatch_in_prefix() {
        // sp[1] = Param("b") but tc[0].name = "a" — invalid pattern.
        let rule = make_rule(
            "BadNeg",
            "Int",
            vec![simple_param("a", "Int")],
            vec![SyntaxExpr::Literal("-".to_string()), SyntaxExpr::Param(ident("b"))],
        );
        assert!(classify_unary_prefix_shape(&rule).is_none());
    }
}
