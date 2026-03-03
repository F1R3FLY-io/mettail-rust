//! Integration tests for all four DSL composition mechanisms:
//!
//! 1. `extends:` — ExtMath inherits BaseMath types+terms+rewrites
//! 2. `mixins:` — MixedMath pulls in IntArithFragment + BoolOpsFragment
//! 3. `includes:` — ImportedMath imports BaseMath types+terms (not rewrites)
//! 4. `compose_languages!` — CalcLambda delegates to Calculator + Lambda

use mettail_runtime::Language;

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Parse, run Ascent, assert `expected` is among the normal-form displays.
fn assert_normal_form(lang: &dyn Language, input: &str, expected: &str) {
    mettail_runtime::clear_var_cache();
    let term = lang.parse_term(input).unwrap_or_else(|e| {
        panic!("parse({:?}) failed: {}", input, e);
    });
    let results = lang.run_ascent(term.as_ref()).unwrap_or_else(|e| {
        panic!("run_ascent({:?}) failed: {}", input, e);
    });
    let displays: Vec<String> = results
        .normal_forms()
        .iter()
        .map(|nf| nf.display.clone())
        .collect();
    assert!(
        displays.contains(&expected.to_string()),
        "expected normal form {:?} for {:?}, got: {:?}",
        expected,
        input,
        displays,
    );
}

/// Parse succeeds (no Ascent — just verify the parser accepts the input).
fn assert_parses(lang: &dyn Language, input: &str) {
    mettail_runtime::clear_var_cache();
    lang.parse_term(input).unwrap_or_else(|e| {
        panic!("parse({:?}) failed: {}", input, e);
    });
}

// ===========================================================================
// 1. ExtMath  (extends: [BaseMath])
// ===========================================================================

mod ext_math {
    use super::*;
    use mettail_languages::composition::extended_lang::ExtMathLanguage;

    #[test]
    fn add_literal() {
        assert_normal_form(&ExtMathLanguage, "1 + 2", "3");
    }

    #[test]
    fn sub_literal() {
        assert_normal_form(&ExtMathLanguage, "10 - 3", "7");
    }

    #[test]
    fn nested_expr() {
        assert_normal_form(&ExtMathLanguage, "(1 + 2) + 3", "6");
    }

    #[test]
    fn variable_parses() {
        assert_parses(&ExtMathLanguage, "x + y");
    }

    #[test]
    fn metadata_name() {
        assert_eq!(ExtMathLanguage.name(), "ExtMath");
    }

    #[test]
    fn env_round_trip() {
        mettail_runtime::clear_var_cache();
        let lang = ExtMathLanguage;
        let mut env = lang.create_env();
        let term = lang.parse_term_for_env("5").expect("parse 5");
        lang.add_to_env(env.as_mut(), "x", term.as_ref())
            .expect("add x");
        let bindings = lang.list_env(env.as_ref());
        assert_eq!(bindings.len(), 1);
        assert_eq!(bindings[0].0, "x");
    }
}

// ===========================================================================
// 2. MixedMath  (mixins: [IntArithFragment, BoolOpsFragment])
// ===========================================================================

mod mixed_math {
    use super::*;
    use mettail_languages::composition::mixed_lang::MixedMathLanguage;

    #[test]
    fn add_int() {
        assert_normal_form(&MixedMathLanguage, "2 + 3", "5");
    }

    #[test]
    fn sub_int() {
        assert_normal_form(&MixedMathLanguage, "7 - 4", "3");
    }

    #[test]
    fn mul_int() {
        assert_normal_form(&MixedMathLanguage, "3 * 4", "12");
    }

    #[test]
    fn negation() {
        assert_normal_form(&MixedMathLanguage, "-5", "-5");
    }

    #[test]
    fn bool_and() {
        assert_normal_form(&MixedMathLanguage, "true and false", "false");
    }

    #[test]
    fn bool_or() {
        assert_normal_form(&MixedMathLanguage, "false or true", "true");
    }

    #[test]
    fn bool_not() {
        assert_normal_form(&MixedMathLanguage, "not false", "true");
    }

    #[test]
    fn metadata_name() {
        assert_eq!(MixedMathLanguage.name(), "MixedMath");
    }
}

// ===========================================================================
// 3. ImportedMath  (includes: [BaseMath])
// ===========================================================================

mod imported_math {
    use super::*;
    use mettail_languages::composition::grammar_import_lang::ImportedMathLanguage;

    #[test]
    fn add_from_base() {
        assert_normal_form(&ImportedMathLanguage, "1 + 2", "3");
    }

    #[test]
    fn sub_from_base() {
        assert_normal_form(&ImportedMathLanguage, "10 - 4", "6");
    }

    #[test]
    fn div_local() {
        assert_normal_form(&ImportedMathLanguage, "10 / 2", "5");
    }

    #[test]
    fn mixed_ops() {
        // Division is locally defined, addition is imported from BaseMath.
        assert_normal_form(&ImportedMathLanguage, "(10 / 2) + 1", "6");
    }

    #[test]
    fn metadata_name() {
        assert_eq!(ImportedMathLanguage.name(), "ImportedMath");
    }
}

// ===========================================================================
// 4. CalcLambda  (compose_languages! { Calculator + Lambda })
// ===========================================================================

mod calc_lambda {
    use super::*;
    use mettail_languages::composition::composed_lang::{CalcLambdaLanguage, CalcLambdaTerm};

    #[test]
    fn parse_calculator_expr() {
        // Calculator sub-language should handle arithmetic.
        assert_normal_form(&CalcLambdaLanguage, "1 + 2", "3");
    }

    #[test]
    fn parse_lambda_expr() {
        // Lambda sub-language should handle lambda abstractions.
        // Lambda syntax: `lam x.body`, application: `(fun, arg)`
        assert_parses(&CalcLambdaLanguage, "lam x.x");
    }

    #[test]
    fn metadata_name() {
        assert_eq!(CalcLambdaLanguage.name(), "CalcLambda");
    }

    #[test]
    fn metadata_has_terms() {
        let meta = CalcLambdaLanguage.metadata();
        // Should aggregate terms from both Calculator and Lambda.
        assert!(
            !mettail_runtime::LanguageMetadata::terms(meta).is_empty(),
            "composed metadata should have terms from sub-languages"
        );
    }

    #[test]
    fn env_create_and_empty() {
        mettail_runtime::clear_var_cache();
        let lang = CalcLambdaLanguage;
        let env = lang.create_env();
        assert!(lang.is_env_empty(env.as_ref()));
    }

    #[test]
    fn env_add_calc_binding() {
        mettail_runtime::clear_var_cache();
        let lang = CalcLambdaLanguage;
        let mut env = lang.create_env();
        let term = lang.parse_term_for_env("42").expect("parse 42");
        lang.add_to_env(env.as_mut(), "x", term.as_ref())
            .expect("add x");
        assert!(!lang.is_env_empty(env.as_ref()));
        let bindings = lang.list_env(env.as_ref());
        assert!(
            bindings.iter().any(|(name, _, _)| name == "x"),
            "expected binding 'x', got: {:?}",
            bindings,
        );
    }

    #[test]
    fn downcast_calculator_term() {
        mettail_runtime::clear_var_cache();
        let lang = CalcLambdaLanguage;
        let term = lang.parse_term("42").expect("parse 42");
        let typed = term
            .as_any()
            .downcast_ref::<CalcLambdaTerm>()
            .expect("should be CalcLambdaTerm");
        // The Calculator sub-language should have parsed this.
        assert!(
            typed.as_calculator().is_some(),
            "42 should be parsed by Calculator sub-language"
        );
    }

    #[test]
    fn format_term() {
        mettail_runtime::clear_var_cache();
        let lang = CalcLambdaLanguage;
        let term = lang.parse_term("1 + 2").expect("parse");
        let formatted = lang.format_term(term.as_ref());
        assert!(
            !formatted.is_empty(),
            "formatted term should be non-empty"
        );
    }

    #[test]
    fn clear_env() {
        mettail_runtime::clear_var_cache();
        let lang = CalcLambdaLanguage;
        let mut env = lang.create_env();
        let term = lang.parse_term_for_env("7").expect("parse");
        lang.add_to_env(env.as_mut(), "y", term.as_ref())
            .expect("add y");
        assert!(!lang.is_env_empty(env.as_ref()));
        lang.clear_env(env.as_mut());
        assert!(lang.is_env_empty(env.as_ref()));
    }
}
