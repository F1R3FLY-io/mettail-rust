#![cfg(all(feature = "lambda", feature = "dovetail-codegen"))]

use mettail_languages::lambda::{LambdaLanguage, LambdaTerm};
use mettail_runtime::{BoundTerm, Language};

fn assert_capture_safe(source: &str, expected: &str, captured: &str) {
    let language = LambdaLanguage;
    let source_term = language.parse_term(source).expect("source parses");
    let expected_term = language.parse_term(expected).expect("expected term parses");
    let captured_term = language
        .parse_term(captured)
        .expect("capture control parses");
    let reduced = LambdaLanguage::dovetail_normal_term(source_term.as_ref(), 64, 1_000_000)
        .expect("bounded Dovetail reduction succeeds");
    let actual = &reduced.as_any().downcast_ref::<LambdaTerm>().unwrap().0;
    let expected = &expected_term
        .as_any()
        .downcast_ref::<LambdaTerm>()
        .unwrap()
        .0;
    let captured = &captured_term
        .as_any()
        .downcast_ref::<LambdaTerm>()
        .unwrap()
        .0;
    eprintln!("source: {source}\nactual: {actual:?}\nexpected: {expected:?}\ncapture control: {captured:?}");
    assert!(
        !BoundTerm::term_eq(expected, captured),
        "the control must differ from the expected binding"
    );
    assert!(
        !BoundTerm::term_eq(actual, captured),
        "reduction captured a bound variable: {source}"
    );
    assert!(
        BoundTerm::term_eq(actual, expected),
        "reduction changed a variable binding: {source}"
    );
}

#[test]
fn w1_argument_keeps_its_outer_binder() {
    assert_capture_safe("lam y. (lam x. lam z. x, y)", "lam y. lam z. y", "lam y. lam z. z");
}

#[test]
fn w2_body_keeps_its_outer_binder() {
    assert_capture_safe("lam a. lam y. (lam x. y, w)", "lam a. lam y. y", "lam a. lam y. a");
}

mod properties {
    use mettail_languages::lambda::Term;
    use mettail_runtime::{Binder, BoundTerm, BoundVar, FreeVar, OrdVar, Scope, Var};
    use proptest::prelude::*;
    use std::sync::Arc;

    #[derive(Clone, Debug)]
    enum Model {
        Bound(u32, u32),
        Free(usize),
        Scope(usize, Box<Self>),
        App(Box<Self>, Box<Self>),
    }

    fn models() -> impl Strategy<Value = Model> {
        prop_oneof![
            (0u32..8, 0u32..4).prop_map(|(scope, index)| Model::Bound(scope, index)),
            (0usize..4).prop_map(Model::Free),
        ]
        .prop_recursive(5, 64, 2, |inner| {
            prop_oneof![
                (1usize..4, inner.clone())
                    .prop_map(|(arity, body)| Model::Scope(arity, Box::new(body))),
                (inner.clone(), inner).prop_map(|(a, b)| Model::App(Box::new(a), Box::new(b))),
            ]
        })
    }

    fn shift(term: &Model, cutoff: u32, amount: u32) -> Option<Model> {
        Some(match term {
            Model::Bound(scope, index) => Model::Bound(
                if *scope < cutoff {
                    *scope
                } else {
                    scope.checked_add(amount)?
                },
                *index,
            ),
            Model::Free(index) => Model::Free(*index),
            Model::Scope(arity, body) => {
                Model::Scope(*arity, Box::new(shift(body, cutoff + 1, amount)?))
            },
            Model::App(a, b) => {
                Model::App(Box::new(shift(a, cutoff, amount)?), Box::new(shift(b, cutoff, amount)?))
            },
        })
    }

    fn instantiate(term: &Model, depth: u32, replacements: &[Model]) -> Option<Model> {
        Some(match term {
            Model::Bound(scope, index) if *scope == depth => {
                shift(replacements.get(*index as usize)?, 0, depth)?
            },
            Model::Bound(scope, index) => {
                Model::Bound(if *scope > depth { scope - 1 } else { *scope }, *index)
            },
            Model::Free(index) => Model::Free(*index),
            Model::Scope(arity, body) => {
                Model::Scope(*arity, Box::new(instantiate(body, depth + 1, replacements)?))
            },
            Model::App(a, b) => Model::App(
                Box::new(instantiate(a, depth, replacements)?),
                Box::new(instantiate(b, depth, replacements)?),
            ),
        })
    }

    fn bound(scope: u32, index: u32) -> Term {
        Term::TVar(OrdVar(Var::Bound(BoundVar {
            scope: moniker::ScopeOffset(scope),
            binder: moniker::BinderIndex(index),
            pretty_name: None,
        })))
    }

    fn lambda(body: Term) -> Term {
        Term::LamTerm(Scope::from_parts_unsafe(Binder(FreeVar::fresh(None)), Arc::new(body)))
    }

    #[test]
    fn normalizer_w1_preserves_argument_binding() {
        let source =
            lambda(Term::ApplyTerm(Arc::new(lambda(lambda(bound(1, 0)))), Arc::new(bound(0, 0))));
        let actual = source.normalize();
        let expected = lambda(lambda(bound(1, 0)));
        assert!(BoundTerm::term_eq(&actual, &expected), "actual: {actual:?}");
    }

    #[test]
    fn normalizer_w2_preserves_body_binding() {
        let argument = Term::TVar(OrdVar(Var::Free(FreeVar::fresh(None))));
        let source =
            lambda(lambda(Term::ApplyTerm(Arc::new(lambda(bound(1, 0))), Arc::new(argument))));
        let actual = source.normalize();
        let expected = lambda(lambda(bound(0, 0)));
        assert!(BoundTerm::term_eq(&actual, &expected), "actual: {actual:?}");
    }

    #[test]
    fn normalizer_multiple_binders_keep_the_selected_argument() {
        let body = Term::MLamTerm(Scope::from_parts_unsafe(
            vec![Binder(FreeVar::fresh(None)), Binder(FreeVar::fresh(None))],
            Arc::new(lambda(bound(1, 1))),
        ));
        let source = lambda(Term::MApplyTerm(
            Arc::new(body),
            vec![Term::TVar(OrdVar(Var::Free(FreeVar::fresh(None)))), bound(0, 0)],
        ));
        let actual = source.normalize();
        let expected = lambda(lambda(bound(1, 0)));
        assert!(BoundTerm::term_eq(&actual, &expected), "actual: {actual:?}");
    }

    fn ast(term: &Model, names: &[FreeVar<String>]) -> Term {
        match term {
            Model::Bound(scope, index) => bound(*scope, *index),
            Model::Free(index) => Term::TVar(OrdVar(Var::Free(names[*index].clone()))),
            Model::Scope(1, body) => Term::Lam(Scope::from_parts_unsafe(
                Binder(FreeVar::fresh(None)),
                Arc::new(ast(body, names)),
            )),
            Model::Scope(arity, body) => Term::MLamTerm(Scope::from_parts_unsafe(
                (0..*arity).map(|_| Binder(FreeVar::fresh(None))).collect(),
                Arc::new(ast(body, names)),
            )),
            Model::App(a, b) => Term::App(Arc::new(ast(a, names)), Arc::new(ast(b, names))),
        }
    }

    fn agrees(actual: Option<Term>, expected: Option<Model>, names: &[FreeVar<String>]) -> bool {
        match (actual, expected) {
            (Some(actual), Some(expected)) => BoundTerm::term_eq(&actual, &ast(&expected, names)),
            (None, None) => true,
            _ => false,
        }
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(256))]

        #[test]
        fn generated_instantiation_matches_scope_model(
            body in models(),
            replacements in proptest::collection::vec(models(), 0..4),
        ) {
            let names: Vec<_> = (0..4).map(|_| FreeVar::fresh(None)).collect();
            let source = ast(&body, &names);
            let arguments: Vec<_> = replacements.iter().map(|model| ast(model, &names)).collect();
            let expected = instantiate(&body, 0, &replacements);
            let result = source.instantiate_scope_term(&arguments);
            prop_assert!(agrees(result, expected, &names));
            prop_assert!(BoundTerm::term_eq(&source, &ast(&body, &names)));
            for (argument, model) in arguments.iter().zip(&replacements) {
                prop_assert!(BoundTerm::term_eq(argument, &ast(model, &names)));
            }
        }

        #[test]
        fn generated_shift_preserves_internal_bindings(body in models(), amount in 0u32..12) {
            let names: Vec<_> = (0..4).map(|_| FreeVar::fresh(None)).collect();
            let source = ast(&body, &names);
            prop_assert!(agrees(source.shift_bound_scopes(amount), shift(&body, 0, amount), &names));
            prop_assert!(BoundTerm::term_eq(&source, &ast(&body, &names)));
        }
    }

    #[test]
    fn shift_overflow_is_rejected_without_changing_the_source() {
        let source = bound(u32::MAX, 0);
        assert!(source.shift_bound_scopes(1).is_none());
        assert!(BoundTerm::term_eq(&source, &bound(u32::MAX, 0)));
        let body = Term::Lam(Scope::from_parts_unsafe(
            Binder(FreeVar::fresh(None)),
            Arc::new(bound(1, 0)),
        ));
        assert!(body.instantiate_scope_term(&[source]).is_none());
    }

    #[test]
    fn deep_binding_instantiation_is_stack_safe() {
        let depth = 100_000u32;
        let mut source = bound(depth, 0);
        for _ in 0..depth {
            source =
                Term::Lam(Scope::from_parts_unsafe(Binder(FreeVar::fresh(None)), Arc::new(source)));
        }
        let result = source
            .instantiate_scope_term(&[bound(0, 0)])
            .expect("valid scope instantiates");
        let mut cursor = &result;
        let mut count = 0;
        while let Term::Lam(scope) = cursor {
            count += 1;
            cursor = scope.unsafe_body().as_ref();
        }
        assert_eq!(count, depth);
        let Term::TVar(OrdVar(Var::Bound(variable))) = cursor else {
            panic!("bound variable expected")
        };
        assert_eq!(variable.scope.0, depth);
        assert_eq!(variable.binder.0, 0);
    }
}
