#![allow(dead_code, unused_imports)]
#![cfg(feature = "dovetail-codegen")]

use mettail_runtime::{BoundTerm, LanguageMetadata};
use proptest::prelude::*;

mettail_macros::language! {
    name: RewriteFamilyGenerated,
    options { emit_tests: false, emit_simulator: false, emit_blockly: false },
    types { Term },
    terms {
        Tick . |- "tick" : Term;
        Done . |- "done" : Term;
        Abs . ^x.body:[Term -> Term] |- "lam" x "." body : Term;
    },
    rewrites {
        Advance . |- Tick ~> Done;
        Under . family:[Term -> Rewrite(Term)] |-
            (Abs ^x.(s (family x))) ~> (Abs ^x.(t (family x)));
    },
}

#[test]
fn generated_metadata_and_reconstruction_have_the_same_normalized_identity() {
    let language = RewriteFamilyGeneratedMetadata;
    let source = language.definition_source().unwrap();
    let reconstructed = mettail_ast::auto_inject::reconstruct_language_def(source).unwrap();
    assert_eq!(
        mettail_ast::identity::language_definition_fingerprint(&reconstructed),
        language.definition_fingerprint().unwrap(),
    );
    assert!(reconstructed
        .rewrites
        .iter()
        .flat_map(|rule| &rule.type_context)
        .all(|parameter| matches!(
            parameter.ty,
            mettail_ast::language::RuleContextType::Ordinary(_)
        )));
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(32))]

    #[test]
    fn generated_dovetail_executes_the_existing_transition_under_binders(depth in 1usize..10) {
        let mut source = "tick".to_owned();
        let mut expected = "done".to_owned();
        for index in 0..depth {
            source = format!("lam x{index}. {source}");
            expected = format!("lam x{index}. {expected}");
        }
        let source = Term::parse(&source).unwrap();
        let expected = Term::parse(&expected).unwrap();
        prop_assert!(!BoundTerm::term_eq(&source, &expected));
        prop_assert!(BoundTerm::term_eq(&source.normalize(), &source));
        let actual = RewriteFamilyGeneratedLanguage::dovetail_report_for(
            &RewriteFamilyGeneratedTerm(source), 64, 1_000_000,
        ).unwrap();
        let expected = RewriteFamilyGeneratedLanguage::dovetail_report_for(
            &RewriteFamilyGeneratedTerm(expected), 64, 1_000_000,
        ).unwrap();
        prop_assert!(actual.is_complete());
        prop_assert!(expected.is_complete());
        prop_assert!(actual.validate_shape().is_ok());
        prop_assert!(expected.validate_shape().is_ok());
        prop_assert!(actual.rule_firings.iter().any(|firing| firing.count > 0 && firing.label.as_ref().is_some_and(|label| label.ends_with("::rewrite::Advance"))));
        prop_assert!(!expected.rule_firings.iter().any(|firing| firing.count > 0 && firing.label.as_ref().is_some_and(|label| label.ends_with("::rewrite::Advance"))));
        prop_assert_eq!(actual.roots, expected.roots);
    }
}
