//! Phase 7: mixfix + optional-group codegen for the WPDS engine.
//!
//! Note: classic Pratt-style mixfix operators (e.g., `a ? b : c`) are
//! handled by the existing `infix.rs` classifier — `is_mixfix` rules are
//! recognized as part of the binding-power analysis. This module is the
//! Phase 7 home for newer compound shapes:
//!
//! - **Optional groups**: `SyntaxItemSpec::Optional { inner }` from
//!   prattail_bridge — `?-modifier` syntax wrapping a sub-pattern.
//!   Codegen emits a position-driven check: peek next; if in
//!   `FIRST(inner)` parse the inner sub-pattern; else jump past.
//!
//! No shipped grammar exercises Optional groups. The infrastructure is
//! in place for future use; classification returns None for shipped
//! grammars so this module is exercised via synthetic unit tests.

use mettail_ast::grammar::GrammarRule;
use proc_macro2::TokenStream;
use quote::quote;

/// Phase 7: classify whether a rule contains an Optional group in its
/// syntax pattern. Returns true if any item is `Op(Opt { ... })`.
pub(crate) fn rule_has_optional(rule: &GrammarRule) -> bool {
    let Some(sp) = rule.syntax_pattern.as_ref() else {
        return false;
    };
    sp.iter().any(|item| {
        matches!(
            item,
            mettail_ast::grammar::SyntaxExpr::Op(mettail_ast::grammar::PatternOp::Opt { .. })
        )
    })
}

/// Phase 7: emit a per-rule lookup table mapping
/// `(result_src_idx, rule_idx) → (optional_position, first_set)` so the
/// engine arm can decide whether to enter the optional sub-parse.
/// Currently a stub — when shipped grammars use Optional groups, this
/// emits the per-rule dispatch.
#[allow(dead_code)]
pub(crate) fn emit_optional_dispatch(_per_cat: &[Vec<GrammarRule>]) -> TokenStream {
    quote! {
        // Phase 7: optional-group dispatch table (placeholder).
        // Filled in when a grammar first uses Optional syntax.
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use mettail_ast::grammar::GrammarRule;
    use proc_macro2::Span;
    use syn::Ident;

    #[test]
    fn rule_without_optional_returns_false() {
        let rule = GrammarRule {
            label: Ident::new("Test", Span::call_site()),
            category: Ident::new("Cat", Span::call_site()),
            items: Vec::new(),
            bindings: Vec::new(),
            term_context: None,
            syntax_pattern: Some(vec![mettail_ast::grammar::SyntaxExpr::Literal(
                "x".into(),
            )]),
            rust_code: None,
            eval_mode: None,
            is_right_assoc: false,
            prefix_bp: None,
            tier_directive: None,
        };
        assert!(!rule_has_optional(&rule));
    }

    #[test]
    fn rule_with_optional_returns_true() {
        let rule = GrammarRule {
            label: Ident::new("Test", Span::call_site()),
            category: Ident::new("Cat", Span::call_site()),
            items: Vec::new(),
            bindings: Vec::new(),
            term_context: None,
            syntax_pattern: Some(vec![mettail_ast::grammar::SyntaxExpr::Op(
                mettail_ast::grammar::PatternOp::Opt {
                    inner: vec![mettail_ast::grammar::SyntaxExpr::Literal("y".into())],
                },
            )]),
            rust_code: None,
            eval_mode: None,
            is_right_assoc: false,
            prefix_bp: None,
            tier_directive: None,
        };
        assert!(rule_has_optional(&rule));
    }
}
