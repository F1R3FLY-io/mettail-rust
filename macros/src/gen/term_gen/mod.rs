//! Term generation for languages
//!
//! Provides both exhaustive enumeration and random sampling of terms.

mod exhaustive;
mod random;

pub use exhaustive::*;
pub use random::*;

use mettail_ast::grammar::{SyntaxExpr, TermParam};
use mettail_ast::language::LanguageDef;
use proc_macro2::TokenStream;
use quote::quote;
use syn::Ident;

pub fn is_lang_type(cat: &Ident, language: &LanguageDef) -> bool {
    language.types.iter().any(|t| &t.name == cat)
}

/// L9-3: build a constructor literal for a CAPTURES-ONLY rule (`Cat::Label(
/// "<sample>".to_string(), ...)`), synthesizing each `v@Tok` capture's text via
/// a deterministic, regex-valid DFA sample of the token kind's effective
/// pattern (decision F.2 — the sampled text re-lexes to the same token, so
/// `parse(display(t)) == t` holds). Returns `None` unless the rule is
/// captures-only: no interleaved `Param`/`Op` fields, no binder `Scope`, and an
/// empty term context. Such rules (the FLT surface, the L9-3 toy) are the only
/// capture rules the term generators need to synthesize; a capture interleaved
/// with terms/binders is not produced (its structural fields have their own
/// generators, and no grammar mixes them).
pub fn capture_only_construction(
    rule: &mettail_ast::grammar::GrammarRule,
    language: &LanguageDef,
    cat_name: &Ident,
    label: &Ident,
) -> Option<TokenStream> {
    use crate::gen::test_gen::automaton_walk::classify::effective_pattern_for;
    use crate::gen::test_gen::automaton_walk::nfa_walk::deterministic_sample;

    let sp = rule.syntax_pattern.as_deref()?;
    // A captures-only rule carries at least one opaque-leaf capture: a
    // `v@Tok` TokenKind (→ token-text `String`) or a `*flt(v, open, close)`
    // GuestBody (→ `Arc<FltNode>`, L9-4).
    if !sp
        .iter()
        .any(|e| matches!(e, SyntaxExpr::TokenKind { .. } | SyntaxExpr::GuestBody { .. }))
    {
        return None;
    }
    // Captures-only: reject interleaved params / meta-ops / a non-empty context.
    if sp
        .iter()
        .any(|e| matches!(e, SyntaxExpr::Param(_) | SyntaxExpr::Op(_)))
    {
        return None;
    }
    if rule
        .term_context
        .as_deref()
        .is_some_and(|c| !c.is_empty())
    {
        return None;
    }

    let mut args: Vec<TokenStream> = Vec::new();
    for e in sp {
        match e {
            SyntaxExpr::TokenKind { name, .. } => {
                let pattern = effective_pattern_for(language, &name.to_string());
                let sample = deterministic_sample(&pattern).unwrap_or_default();
                args.push(quote! { #sample.to_string() });
            },
            SyntaxExpr::GuestBody { open, close, .. } => {
                // L9-4: synthesize a minimal, roundtrip-valid `Arc<FltNode>`.
                // Display renders `<tag><open_delim><body_src><close_delim>`
                // (see `generate_capture_display_arm`); with an EMPTY body and
                // no holes the printed form is `<tag><open_delim><close_delim>`,
                // which re-lexes to the same opener/closer kinds and re-parses
                // to this exact node (position 0 at the top level). The `tag` is
                // the deterministic opener sample minus its delimiter suffix, so
                // it satisfies the opener token's pattern (e.g. `[a-z]+` for the
                // backtick form, the literal `box` for the reserved-tag brace).
                let open_pattern = effective_pattern_for(language, &open.to_string());
                let opener_sample = deterministic_sample(&open_pattern).unwrap_or_default();
                let (open_delim, _close_delim) = crate::gen::syntax::display::flt_delimiters_for(
                    &open.to_string(),
                    &close.to_string(),
                );
                let tag = opener_sample
                    .strip_suffix(open_delim)
                    .unwrap_or(&opener_sample)
                    .to_string();
                args.push(quote! {
                    std::sync::Arc::new(mettail_runtime::FltNode::new(
                        #tag.to_string(),
                        String::new(),
                        Vec::new(),
                        0,
                    ))
                });
            },
            _ => {},
        }
    }
    Some(quote! { #cat_name::#label(#(#args),*) })
}

/// Task #14 (Option<Guard>): count a term context's Optional positions,
/// SPLIT into `(term_count, total_count)`.
///
/// * `term_count` — Optional-inner Simple/Abstraction/MultiAbstraction
///   positions. These are lowered by `convert_term_context_to_items` into
///   `rule.items` NonTerminals, so they occupy `arg_cats` slots and must be
///   subtracted from the positional prefix.
/// * `total_count` — ALL Optional positions (terms + `?g:Guard` slots).
///   Guards NEVER appear in `rule.items`, but every Optional position
///   (term or guard) still occupies one constructor field, so the
///   `None`-suffix must cover them all.
///
/// Splitting the two is what fixes the term-generation arity bug for
/// guard-in-`#opt(...)` rules: subtracting the guard from `arg_cats.len()`
/// dropped a REAL positional param (E0061) while the `None`-suffix stayed
/// one short of the variant's arity.
pub(crate) fn count_optional_positions(term_context: &[TermParam]) -> (usize, usize) {
    fn count_inner(p: &TermParam) -> (usize, usize) {
        match p {
            TermParam::Simple { .. }
            | TermParam::Abstraction { .. }
            | TermParam::MultiAbstraction { .. } => (1, 1),
            TermParam::GuardBody { .. } => (0, 1),
            TermParam::Optional { params: inner } => sum_pairs(inner.iter().map(count_inner)),
        }
    }
    fn count_top(p: &TermParam) -> (usize, usize) {
        match p {
            TermParam::Optional { params: inner } => sum_pairs(inner.iter().map(count_inner)),
            _ => (0, 0),
        }
    }
    fn sum_pairs(pairs: impl Iterator<Item = (usize, usize)>) -> (usize, usize) {
        pairs.fold((0, 0), |(at, bt), (a, b)| (at + a, bt + b))
    }
    sum_pairs(term_context.iter().map(count_top))
}

#[cfg(test)]
mod tests {
    use super::*;
    use mettail_ast::types::TypeExpr;
    use quote::format_ident;

    fn simple(name: &str, cat: &str) -> TermParam {
        TermParam::Simple {
            name: format_ident!("{}", name),
            ty: TypeExpr::Base(format_ident!("{}", cat)),
        }
    }

    fn guard(name: &str) -> TermParam {
        TermParam::GuardBody { name: format_ident!("{}", name) }
    }

    #[test]
    fn count_split_guard_only_optional() {
        // `k:Int, *opt(?g:Guard)` — the guardoptsmoke PCheck shape: the
        // guard contributes to the None-suffix but NOT to the positional
        // subtraction.
        let ctx = vec![
            simple("k", "Int"),
            TermParam::Optional { params: vec![guard("g")] },
        ];
        assert_eq!(count_optional_positions(&ctx), (0, 1));
    }

    #[test]
    fn count_split_mixed_optional() {
        // `*opt(t:Int ?g:Guard)` — one arg_cats-occupying term + one guard.
        let ctx = vec![TermParam::Optional {
            params: vec![simple("t", "Int"), guard("g")],
        }];
        assert_eq!(count_optional_positions(&ctx), (1, 2));
    }

    #[test]
    fn count_split_terms_only_matches_legacy() {
        // Pre-#14 behavior for term-only optionals: both counts agree, so
        // `take(arg_cats.len() - term_count)` and the None-suffix emit the
        // exact tokens the single-count code emitted (byte-identity for
        // every shipped Optional grammar).
        let ctx = vec![
            simple("a", "Proc"),
            TermParam::Optional { params: vec![simple("e", "Proc")] },
        ];
        assert_eq!(count_optional_positions(&ctx), (1, 1));
    }

    #[test]
    fn count_split_no_optionals_is_zero() {
        let ctx = vec![simple("a", "Proc"), simple("b", "Proc")];
        assert_eq!(count_optional_positions(&ctx), (0, 0));
    }

    #[test]
    fn count_split_top_level_guard_not_counted() {
        // A top-level (mandatory) guard is NOT an Optional position — it is
        // handled by the mandatory-guard skips (random.rs caller loop,
        // exhaustive.rs simple/binder cases), never by the None-suffix.
        let ctx = vec![simple("k", "Int"), guard("g")];
        assert_eq!(count_optional_positions(&ctx), (0, 0));
    }
}
