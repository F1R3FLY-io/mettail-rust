use mettail_prattail::letprop::{
    analyze_polarity, collect_relations, has_quantifier, lower_to_mu_calculus, validate_arguments,
    LetPropArg, LetPropError, LetPropExpr, RecursivePredicate,
};

const DEPTH: usize = 20_000;
const SMALL_STACK_BYTES: usize = 256 * 1024;

fn on_small_stack(test: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .name("letprop-small-stack".to_string())
        .stack_size(SMALL_STACK_BYTES)
        .spawn(test)
        .expect("spawn letprop small-stack gate")
        .join()
        .expect("letprop small-stack gate panicked");
}

fn deep_arg(variable: &str) -> LetPropArg {
    let mut arg = LetPropArg::Var(variable.to_string());
    for _ in 0..DEPTH {
        arg = LetPropArg::App {
            func: "child".to_string(),
            args: vec![arg],
        };
    }
    arg
}

#[test]
fn letprop_lifecycle_walkers_and_lowering_are_stack_safe_at_depth_20k() {
    on_small_stack(|| {
        let arg = deep_arg("x");
        let cloned_arg = arg.clone();
        assert_eq!(arg, cloned_arg);
        assert_eq!(arg.free_vars().into_iter().collect::<Vec<_>>(), ["x"]);
        let arg_debug = format!("{arg:?}");
        assert!(arg_debug.starts_with("App { func: \"child\", args: [App"));
        assert!(arg_debug.ends_with(&"] }".repeat(DEPTH)));

        let mut body = LetPropExpr::Recursive { args: vec![arg.clone()] };
        for _ in 0..DEPTH {
            body = LetPropExpr::Not(Box::new(body));
        }

        let cloned_body = body.clone();
        assert_eq!(body, cloned_body);
        assert_eq!(analyze_polarity(&body), (Some(true), false));
        assert!(!has_quantifier(&body));
        assert!(collect_relations(&body).is_empty());
        let body_debug = format!("{body:?}");
        assert!(body_debug.starts_with("Not(Not("));
        assert!(body_debug.ends_with(&")".repeat(DEPTH)));

        let predicate = RecursivePredicate {
            name: "safe".to_string(),
            params: vec!["x".to_string()],
            body: body.clone(),
        };
        let cloned_predicate = predicate.clone();
        assert_eq!(predicate, cloned_predicate);
        validate_arguments(&predicate).expect("deep argument remains in scope");
        let lowered = lower_to_mu_calculus(&predicate).expect("lower deep letprop");

        drop(lowered);
        drop(cloned_predicate);
        drop(predicate);
        drop(cloned_body);
        drop(body);
        drop(cloned_arg);
        drop(arg);
    });
}

#[test]
fn letprop_diagnostic_rendering_and_scope_restoration_are_stack_safe_at_depth_20k() {
    on_small_stack(|| {
        let invalid = RecursivePredicate {
            name: "invalid".to_string(),
            params: Vec::new(),
            body: LetPropExpr::Recursive { args: vec![deep_arg("escaped")] },
        };
        let error = validate_arguments(&invalid).expect_err("escaped variable must be rejected");
        let actual = match error {
            LetPropError::ArgumentMismatch { actual, .. } => actual,
            other => panic!("expected argument mismatch, got {other:?}"),
        };
        assert!(actual.starts_with("child(child("));
        assert!(actual.ends_with(&")".repeat(DEPTH)));
        assert_eq!(actual.matches("child(").count(), DEPTH);

        let mut scoped_body = LetPropExpr::Recursive {
            args: vec![LetPropArg::Var("bound".to_string())],
        };
        for _ in 0..DEPTH {
            scoped_body = LetPropExpr::Forall {
                var: "bound".to_string(),
                body: Box::new(scoped_body),
            };
        }
        let scoped = RecursivePredicate {
            name: "scoped".to_string(),
            params: Vec::new(),
            body: scoped_body,
        };
        validate_arguments(&scoped).expect("quantifier binder must remain in scope");

        drop(scoped);
        drop(invalid);
    });
}

#[test]
fn letprop_debug_preserves_the_compact_derived_contract() {
    let arg = LetPropArg::App {
        func: "pair".to_string(),
        args: vec![
            LetPropArg::Var("x".to_string()),
            LetPropArg::App {
                func: "child".to_string(),
                args: vec![LetPropArg::Var("y".to_string())],
            },
        ],
    };
    assert_eq!(
        format!("{arg:?}"),
        "App { func: \"pair\", args: [Var(\"x\"), App { func: \"child\", args: [Var(\"y\")] }] }"
    );

    let expr = LetPropExpr::Implies(
        Box::new(LetPropExpr::Forall {
            var: "x".to_string(),
            body: Box::new(LetPropExpr::Atom {
                relation: "edge".to_string(),
                args: vec![LetPropArg::Var("x".to_string())],
            }),
        }),
        Box::new(LetPropExpr::Not(Box::new(LetPropExpr::Recursive {
            args: vec![LetPropArg::Var("x".to_string())],
        }))),
    );
    assert_eq!(
        format!("{expr:?}"),
        "Implies(Forall { var: \"x\", body: Atom { relation: \"edge\", args: [Var(\"x\")] } }, Not(Recursive { args: [Var(\"x\")] }))"
    );
}
