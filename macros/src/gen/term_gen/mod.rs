//! Term generation for languages
//!
//! Provides both exhaustive enumeration and random sampling of terms.

mod exhaustive;
mod random;

pub use exhaustive::*;
pub use random::*;

use mettail_ast::grammar::TermParam;
use mettail_ast::language::LanguageDef;
use syn::Ident;

pub fn is_lang_type(cat: &Ident, language: &LanguageDef) -> bool {
    language.types.iter().any(|t| &t.name == cat)
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
