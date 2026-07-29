//! Term generation for languages
//!
//! Provides both exhaustive enumeration and random sampling of terms.

mod exhaustive;
mod random;

pub use exhaustive::*;
pub use random::*;

use mettail_ast::grammar::{NonTerminalKind, SyntaxExpr, TermParam};
use mettail_ast::language::LanguageDef;
use proc_macro2::TokenStream;
use quote::quote;
use syn::Ident;

pub fn is_lang_type(cat: &Ident, language: &LanguageDef) -> bool {
    language.types.iter().any(|t| &t.name == cat)
}

/// (A4) Whether an argument position is the builtin `Ident` token class — an `m:Ident`
/// mid-rule parameter, whose AST field is a bare `std::string::String`.
///
/// ★ WHY EVERY ARGUMENT-EMITTING SITE IN THIS MODULE MUST ASK. The generators reach a field's
/// type through its CATEGORY name and gate on [`is_lang_type`], which is false for `Ident`
/// (it is not a declared category). Every such site answered that with `quote! {}` or a
/// `panic!("Non-exported category")` — i.e. it dropped the WHOLE constructor from generation,
/// silently. That is invisible while `Ident` params are rare; a language that collapses a
/// large method surface onto one `recv . name ( args )` constructor would trade its entire
/// generated property-test coverage of that surface for zero, with no diagnostic anywhere.
pub(crate) fn is_ident_position(cat: &Ident) -> bool {
    NonTerminalKind::classify(&cat.to_string()) == NonTerminalKind::Ident
}

/// (A4) The identifier samples a generated term may put in an `Ident` position, SPEC-DERIVED
/// and VALIDATED against the language's own effective `Ident` lexer pattern.
///
/// The base is [`deterministic_sample`](crate::gen::test_gen::automaton_walk::nfa_walk::
/// deterministic_sample) of `effective_pattern_for(language, "Ident")` — the SAME mechanism
/// `capture_only_construction` already uses for a `v@Tok` capture, and the reason that path's
/// terms satisfy `parse(display(t)) == t`. Longer candidates are formed by repeating the base
/// and are KEPT ONLY IF the pattern still accepts them, so an override such as
/// `Ident = "[a-z]"` yields a one-element pool rather than an unparseable term.
///
/// ⚠ THE OBVIOUS ALTERNATIVE IS WRONG, so it is named here rather than rediscovered: reusing
/// the `StringLiteral` sampler (`random.rs`'s `rng.gen_range(0..20)` lowercase bytes) would
/// emit the EMPTY string one time in twenty, and the empty string is not an identifier under
/// any pattern — the resulting term would fail to round-trip in the generated property suite
/// with a message pointing at the parser rather than at the sampler. It is also unvalidated
/// against a spec override, and it can collide with a reserved keyword.
///
/// Reserved-keyword collision is excluded by construction here: every candidate is a
/// repetition of the shortest string the `Ident` DFA accepts (`"a"`, `"aa"`, `"aaa"` for the
/// default pattern), and a grammar terminal is a written literal, so a collision would require
/// the language to declare `a` / `aa` / `aaa` as syntax. The [`terminal_literals`] filter
/// removes such a candidate if it ever happens.
///
/// Panics (as a proc-macro build error naming the cause) if the language's effective `Ident`
/// pattern admits NO string at all: that is an ill-formed override, and a silent fallback to
/// some other name would put an unparseable identifier into every generated term.
pub(crate) fn ident_samples(language: &LanguageDef) -> Vec<String> {
    use crate::gen::test_gen::automaton_walk::classify::effective_pattern_for;
    use crate::gen::test_gen::automaton_walk::nfa_walk::{deterministic_sample, pattern_admits};

    let pattern = effective_pattern_for(language, "Ident");
    let base = deterministic_sample(&pattern).unwrap_or_else(|| {
        panic!(
            "the language's effective `Ident` pattern ({pattern:?}) admits no string, so no \
             identifier can be generated for an `m:Ident` position",
        )
    });
    let reserved = terminal_literals(language);
    let mut out = Vec::with_capacity(3);
    for repeat in 1..=3usize {
        let candidate = base.repeat(repeat);
        if pattern_admits(&pattern, &candidate)
            && !reserved.contains(&candidate)
            && !out.contains(&candidate)
        {
            out.push(candidate);
        }
    }
    if out.is_empty() {
        panic!(
            "the language's effective `Ident` pattern ({pattern:?}) admits {base:?}, but every \
             generated candidate collided with a grammar terminal — no identifier can be \
             generated for an `m:Ident` position",
        );
    }
    out
}

/// (A4) How many of `rule`'s term-context parameters are builtin `Ident` params (`m:Ident`).
///
/// ★ THIS IS POSITIVE EVIDENCE, and it has to be. `OpaqueLeafKind::TokenText` is shared by TWO
/// provenances — a builtin `m:Ident` param and a DECLARED `v@Tok` token-kind capture — and
/// they are governed by DIFFERENT lexer patterns. [`ident_samples`] samples the language's
/// effective `Ident` pattern, which is correct for the first and WRONG for the second: `L9Modal
/// Toy` declares `Word = "<[a-z]+>"`, so an `Ident` sample such as `"a"` placed in a `w@Word`
/// field produces a term whose `Display` does not re-lex — a generated term that silently fails
/// `parse ∘ display` for a reason pointing at the parser.
///
/// A generator therefore may not infer "this text field is an identifier" from the leaf KIND.
/// It must see the `m:Ident` PARAMETER. (`term_gen`'s own random/exhaustive walkers get this
/// for free: they key on the argument CATEGORY being literally `Ident`, which only an
/// `m:Ident` param produces — a `v@Tok` field's placeholder category is `String`. The
/// proptest tape builder reads `FieldInfo::opaque_leaf` instead, so it needs this.)
///
/// A `v@Tok` capture is served correctly elsewhere, by [`capture_only_construction`], which
/// samples each capture's OWN declared kind.
pub(crate) fn ident_param_count(rule: &mettail_ast::grammar::GrammarRule) -> usize {
    rule.term_context.as_deref().map_or(0, |ctx| {
        ctx.iter()
            .filter(|p| matches!(p, TermParam::Simple { ty, .. } if ty.is_ident_text()))
            .count()
    })
}

/// Every terminal literal written in the language's grammar, so [`ident_samples`] can refuse a
/// candidate that would lex as a keyword rather than as an identifier.
fn terminal_literals(language: &LanguageDef) -> std::collections::HashSet<String> {
    use mettail_ast::grammar::GrammarItem;
    let mut out = std::collections::HashSet::with_capacity(language.terms.len() * 2);
    for rule in &language.terms {
        for item in &rule.items {
            if let GrammarItem::Terminal(text) = item {
                out.insert(text.clone());
            }
        }
        if let Some(sp) = rule.syntax_pattern.as_deref() {
            for expr in sp {
                if let SyntaxExpr::Literal(text) = expr {
                    out.insert(text.clone());
                }
            }
        }
    }
    out
}

/// (A4) A runtime expression selecting one of [`ident_samples`] uniformly at random — the
/// value a RANDOM generator puts in an `Ident` position. Evaluates to a `String`.
///
/// A single-element pool degenerates to a constant with no `rng` call, which keeps the
/// generated code free of a `gen_range(0..1)` the compiler would warn about and keeps a
/// one-identifier spec deterministic.
pub(crate) fn random_ident_expr(language: &LanguageDef) -> TokenStream {
    let samples = ident_samples(language);
    if samples.len() == 1 {
        let only = &samples[0];
        return quote! { #only.to_string() };
    }
    let n = samples.len();
    quote! {
        {
            let __idx = rng.gen_range(0..#n);
            [#(#samples),*][__idx].to_string()
        }
    }
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
    if rule.term_context.as_deref().is_some_and(|c| !c.is_empty()) {
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
        let ctx = vec![simple("k", "Int"), TermParam::Optional { params: vec![guard("g")] }];
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
        let ctx =
            vec![simple("a", "Proc"), TermParam::Optional { params: vec![simple("e", "Proc")] }];
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
