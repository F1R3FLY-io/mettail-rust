//! Checked capture samples from the parser's resolved lexical definitions.
//!
//! One context belongs to one generation pass. Resolution is lazy, occurs at
//! most once, and shares the existing parser bridge; samples (including errors)
//! are cached by capture name. This module does not implement another DFA or
//! infer token kinds from field names. It validates the existing DFA walk's
//! candidate before allowing constructor emission.

use super::ident_samples_from_pattern;
use crate::gen::syntax::parser::prattail_bridge::language_def_to_spec;
use crate::gen::test_gen::automaton_walk::nfa_walk::{deterministic_sample, pattern_admits};
use mettail_ast::language::LanguageDef;
use mettail_prattail::automata::{token_kind_matches_capture_name, TokenKind};
use mettail_prattail::LanguageSpec;
use std::cell::{OnceCell, RefCell};
use std::collections::HashMap;

pub(crate) struct CaptureSamplingContext<'a> {
    language: &'a LanguageDef,
    resolved: OnceCell<Result<LanguageSpec, String>>,
    samples: RefCell<HashMap<String, Result<String, String>>>,
}

impl<'a> CaptureSamplingContext<'a> {
    pub(crate) fn new(language: &'a LanguageDef) -> Self {
        Self {
            language,
            resolved: OnceCell::new(),
            samples: RefCell::new(HashMap::new()),
        }
    }

    /// Return accepted, nonempty raw token spelling, or an explicit diagnostic.
    /// Whole-lexer priority and contextual alternatives remain lexer concerns;
    /// pattern acceptance alone is not a proof of an entire parse roundtrip.
    pub(crate) fn sample(&self, capture: &str) -> Result<String, String> {
        if let Some(result) = self.samples.borrow().get(capture) {
            return result.clone();
        }
        let result = self.sample_uncached(capture).map_err(|reason| {
            format!("mettail: language `{}` capture `{capture}`: {reason}", self.language.name)
        });
        self.samples
            .borrow_mut()
            .insert(capture.to_owned(), result.clone());
        result
    }

    fn sample_uncached(&self, capture: &str) -> Result<String, String> {
        let spec = self
            .resolved
            .get_or_init(|| language_def_to_spec(self.language));
        let spec = spec.as_ref().map_err(Clone::clone)?;
        let pattern = resolved_pattern(spec, capture)?;
        let candidate = if token_kind_matches_capture_name(capture, &TokenKind::Ident) {
            ident_samples_from_pattern(self.language, pattern)?
                .into_iter()
                .next()
                .ok_or_else(|| "identifier sample pool is empty".to_owned())?
        } else {
            deterministic_sample(pattern)
                .ok_or_else(|| format!("no DFA sample for resolved pattern {pattern:?}"))?
        };
        if candidate.is_empty() {
            return Err(format!("resolved pattern {pattern:?} produced an empty token sample"));
        }
        if !pattern_admits(pattern, &candidate) {
            return Err(format!("DFA candidate {candidate:?} is not accepted by {pattern:?}"));
        }
        Ok(candidate)
    }
}

fn resolved_pattern<'a>(spec: &'a LanguageSpec, capture: &str) -> Result<&'a str, String> {
    // Match capture aliases with the SAME predicate the WPDA token-capture
    // branch uses. Patterns are the bridge's resolved values, not copies of
    // built-in regular expressions maintained by this sampler.
    let patterns = &spec.literal_patterns;
    for (kind, pattern) in [
        (TokenKind::Ident, patterns.ident.as_str()),
        (TokenKind::Integer, patterns.integer.as_str()),
        (TokenKind::Float, patterns.float.as_str()),
        (TokenKind::StringLit, patterns.string.as_str()),
    ] {
        if token_kind_matches_capture_name(capture, &kind) {
            return Ok(pattern);
        }
    }
    if let Some(pattern) = patterns.boolean.as_deref() {
        if token_kind_matches_capture_name(capture, &TokenKind::BooleanLit) {
            return Ok(pattern);
        }
    }
    for token in &spec.custom_tokens {
        if token_kind_matches_capture_name(capture, &TokenKind::Custom(token.name.clone())) {
            return Ok(&token.pattern);
        }
    }
    Err("no resolved lexical pattern for this capture kind".to_owned())
}

#[cfg(test)]
mod tests {
    use super::*;
    use mettail_ast::language::TokenDef;
    use quote::{format_ident, quote};

    fn declared_token(name: &str, pattern: &str, from_literals: bool) -> TokenDef {
        TokenDef {
            name: format_ident!("{name}"),
            pattern: pattern.to_owned(),
            category: None,
            rust_code: None,
            priority: None,
            push_mode: None,
            is_pop: false,
            stream: None,
            from_literals,
        }
    }

    #[test]
    fn capture_sampling_builtin_aliases_use_the_resolved_parser_patterns() {
        let language = crate::gen::empty_language_for_tests();
        let sampling = CaptureSamplingContext::new(&language);
        assert!(sampling.resolved.get().is_none());
        for aliases in [
            &["String", "StringLit", "StringLiteral"][..],
            &["Ident", "Identifier"][..],
            &["Float", "FloatLiteral"][..],
            &["Integer"][..],
        ] {
            let expected = sampling.sample(aliases[0]).expect("built-in token sample");
            assert!(!expected.is_empty());
            let spec = sampling
                .resolved
                .get()
                .expect("resolved once")
                .as_ref()
                .expect("valid spec");
            for alias in aliases {
                assert_eq!(sampling.sample(alias).expect("alias sample"), expected);
                assert!(pattern_admits(resolved_pattern(spec, alias).expect("pattern"), &expected));
            }
        }
    }

    #[test]
    fn capture_sampling_preserves_declared_tokens_and_caches_results() {
        let mut language = crate::gen::empty_language_for_tests();
        language
            .token_defs
            .push(declared_token("Word", "<[a-z]{2}>", false));
        let sampling = CaptureSamplingContext::new(&language);
        let first = sampling.sample("Word").expect("declared sample");
        assert!(pattern_admits("<[a-z]{2}>", &first));
        assert_eq!(sampling.sample("Word").expect("cached sample"), first);
        assert_eq!(sampling.samples.borrow().len(), 1);
        let spec = sampling
            .resolved
            .get()
            .expect("resolved spec")
            .as_ref()
            .expect("valid spec");
        assert!(std::ptr::eq(
            resolved_pattern(spec, "Word")
                .expect("declared pattern")
                .as_ptr(),
            spec.custom_tokens[0].pattern.as_ptr(),
        ));
    }

    #[test]
    fn capture_sampling_identifier_override_retains_keyword_filtering() {
        let mut language = crate::gen::empty_language_for_tests();
        language
            .token_defs
            .push(declared_token("Ident", "[a-z]+", true));
        language.terms.push(mettail_ast::grammar::GrammarRule {
            items: vec![mettail_ast::grammar::GrammarItem::Terminal("a".into())],
            ..mettail_ast::grammar::rule_fixture(format_ident!("Reserved"), format_ident!("Term"))
        });
        let sampling = CaptureSamplingContext::new(&language);
        let sample = sampling
            .sample("Identifier")
            .expect("unreserved identifier");
        assert_ne!(sample, "a");
        assert!(pattern_admits("[a-z]+", &sample));
    }

    #[test]
    fn capture_sampling_failures_never_become_empty_successes() {
        for pattern in ["[", ""] {
            let mut language = crate::gen::empty_language_for_tests();
            language
                .token_defs
                .push(declared_token("Broken", pattern, false));
            let sampling = CaptureSamplingContext::new(&language);
            let error = sampling
                .sample("Broken")
                .expect_err("invalid pattern must refuse");
            assert!(error.contains("TestLang") && error.contains("Broken"));
            assert_eq!(sampling.sample("Broken").expect_err("cached refusal"), error);
        }
        let language = crate::gen::empty_language_for_tests();
        let sampling = CaptureSamplingContext::new(&language);
        assert!(sampling
            .sample("Undeclared")
            .expect_err("unknown token")
            .contains("no resolved"));
    }

    #[test]
    fn capture_sampling_leaf_emitter_keeps_each_token_kind_and_order() {
        let language: LanguageDef = syn::parse2(quote! {
            name: CaptureOrder,
            types { Term },
            terms { Captured . |- name@Ident raw@StringLiteral : Term; },
            equations {},
            rewrites {},
        })
        .expect("capture fixture");
        let sampling = CaptureSamplingContext::new(&language);
        let rule = &language.terms[0];
        let emitted =
            super::super::capture_only_construction(rule, &rule.category, &rule.label, &sampling)
                .expect("capture-only constructor");
        let ident = sampling.sample("Ident").expect("identifier");
        let string = sampling.sample("StringLiteral").expect("string token");
        assert_eq!(
            emitted.to_string(),
            quote! { Term::Captured(#ident.to_string(), #string.to_string()) }.to_string()
        );
        syn::parse2::<syn::Expr>(emitted).expect("valid constructor expression");
        for generator in [
            super::super::generate_random_generation(&language),
            super::super::generate_term_generation(&language),
        ] {
            let source = generator.to_string();
            assert!(!source.contains("compile_error"), "{source}");
            assert!(source.contains(
                &quote! { Term::Captured(#ident.to_string(), #string.to_string()) }.to_string()
            ));
            syn::parse2::<syn::File>(generator).expect("valid generated items");
        }
    }

    #[test]
    fn capture_sampling_leaf_emitter_reports_missing_kind_without_fabrication() {
        let language: LanguageDef = syn::parse2(quote! {
            name: InvalidCapture,
            types { Term },
            terms { Captured . |- raw@MissingToken : Term; },
            equations {},
            rewrites {},
        })
        .expect("syntactic fixture");
        let sampling = CaptureSamplingContext::new(&language);
        let rule = &language.terms[0];
        let emitted =
            super::super::capture_only_construction(rule, &rule.category, &rule.label, &sampling)
                .expect("capture-only rule must report its failure")
                .to_string();
        assert!(emitted.contains("compile_error"));
        assert!(emitted.contains("MissingToken") && emitted.contains("Term::Captured"));
        assert!(!emitted.contains("to_string"));
    }
}
