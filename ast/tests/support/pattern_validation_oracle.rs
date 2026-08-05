use super::*;
use crate::language::LanguageDef;
use proc_macro2::{Ident, Span};

#[derive(Debug, PartialEq, Eq)]
enum InferOutcome {
    Type(String),
    UnknownConstructor(String),
}

fn ident(name: &str) -> Ident {
    Ident::new(name, Span::call_site())
}

fn var(name: &str) -> Pattern {
    Pattern::Term(PatternTerm::Var(ident(name)))
}

fn mix(seed: u64) -> u64 {
    seed.wrapping_mul(6_364_136_223_846_793_005)
        .wrapping_add(1_442_695_040_888_963_407)
}

#[cfg(test)]
fn patterned(seed: u64, depth: usize) -> Pattern {
    if depth == 0 {
        return match seed % 3 {
            0 => var("x"),
            1 => Pattern::Term(PatternTerm::Apply {
                constructor: ident("Leaf"),
                args: Vec::new(),
            }),
            _ => Pattern::Term(PatternTerm::Apply {
                constructor: ident("Missing"),
                args: Vec::new(),
            }),
        };
    }

    let next = mix(seed);
    match seed % 12 {
        0 => var(if seed & 1 == 0 { "x" } else { "y" }),
        1 => Pattern::Term(PatternTerm::Apply {
            constructor: ident("Node"),
            args: vec![patterned(next, depth - 1)],
        }),
        2 => Pattern::Term(PatternTerm::Apply {
            constructor: ident("Pair"),
            args: vec![patterned(next, depth - 1), patterned(mix(next), depth - 1)],
        }),
        3 => Pattern::Collection {
            coll_type: None,
            elements: vec![patterned(next, depth - 1), patterned(mix(next), depth - 1)],
            rest: Some(ident("rest")),
        },
        4 => Pattern::Map {
            collection: Box::new(patterned(next, depth - 1)),
            params: vec![ident("x")],
            body: Box::new(patterned(mix(next), depth - 1)),
        },
        5 => Pattern::Zip {
            first: Box::new(patterned(next, depth - 1)),
            second: Box::new(patterned(mix(next), depth - 1)),
        },
        6 => Pattern::IndexedVec {
            collection: ident("items"),
            index: ident("index"),
            element: Box::new(patterned(next, depth - 1)),
        },
        7 => Pattern::Term(PatternTerm::Lambda {
            binder: ident("x"),
            body: Box::new(patterned(next, depth - 1)),
        }),
        8 => Pattern::Term(PatternTerm::MultiLambda {
            binders: vec![ident("x"), ident("y")],
            body: Box::new(patterned(next, depth - 1)),
        }),
        9 => Pattern::Term(PatternTerm::Subst {
            term: Box::new(patterned(next, depth - 1)),
            var: ident("x"),
            replacement: Box::new(patterned(mix(next), depth - 1)),
        }),
        10 => Pattern::Term(PatternTerm::MultiSubst {
            scope: Box::new(patterned(next, depth - 1)),
            replacements: vec![patterned(mix(next), depth - 1)],
        }),
        // Leaf has arity zero. The legacy algorithm deliberately never visits
        // surplus arguments, so this shape pins that exact observable behavior.
        _ => Pattern::Term(PatternTerm::Apply {
            constructor: ident("Leaf"),
            args: vec![Pattern::Term(PatternTerm::Apply {
                constructor: ident("Missing"),
                args: Vec::new(),
            })],
        }),
    }
}

#[cfg(test)]
fn recursive_validate_pattern(
    pattern: &Pattern,
    language: &LanguageDef,
) -> Result<(), ValidationError> {
    match pattern {
        Pattern::Term(term) => match term {
            PatternTerm::Var(_) => Ok(()),
            PatternTerm::Apply { constructor, args } => {
                let name = constructor.to_string();
                if !language.terms.iter().any(|rule| rule.label == *constructor) {
                    return Err(ValidationError::UnknownConstructor {
                        name,
                        span: constructor.span(),
                    });
                }
                for argument in args {
                    recursive_validate_pattern(argument, language)?;
                }
                Ok(())
            },
            PatternTerm::Lambda { body, .. } | PatternTerm::MultiLambda { body, .. } => {
                recursive_validate_pattern(body, language)
            },
            PatternTerm::Subst { term, replacement, .. } => {
                recursive_validate_pattern(term, language)?;
                recursive_validate_pattern(replacement, language)
            },
            PatternTerm::MultiSubst { scope, replacements } => {
                recursive_validate_pattern(scope, language)?;
                for replacement in replacements {
                    recursive_validate_pattern(replacement, language)?;
                }
                Ok(())
            },
        },
        Pattern::Collection { elements, .. } => {
            for element in elements {
                recursive_validate_pattern(element, language)?;
            }
            Ok(())
        },
        Pattern::Map { collection, body, .. } => {
            recursive_validate_pattern(collection, language)?;
            recursive_validate_pattern(body, language)
        },
        Pattern::Zip { first, second } => {
            recursive_validate_pattern(first, language)?;
            recursive_validate_pattern(second, language)
        },
        Pattern::IndexedVec { element, .. } => recursive_validate_pattern(element, language),
    }
}

#[cfg(test)]
fn recursive_collect_pattern_vars(pattern: &Pattern, vars: &mut HashSet<String>) {
    match pattern {
        Pattern::Term(term) => match term {
            PatternTerm::Var(ident) => {
                vars.insert(ident.to_string());
            },
            PatternTerm::Apply { args, .. } => {
                for argument in args {
                    recursive_collect_pattern_vars(argument, vars);
                }
            },
            PatternTerm::Lambda { binder, body } => {
                vars.insert(binder.to_string());
                let mut body_vars = HashSet::new();
                recursive_collect_pattern_vars(body, &mut body_vars);
                body_vars.remove(&binder.to_string());
                vars.extend(body_vars);
            },
            PatternTerm::MultiLambda { binders, body } => {
                for binder in binders {
                    vars.insert(binder.to_string());
                }
                let mut body_vars = HashSet::new();
                recursive_collect_pattern_vars(body, &mut body_vars);
                for binder in binders {
                    body_vars.remove(&binder.to_string());
                }
                vars.extend(body_vars);
            },
            PatternTerm::Subst { term, var, replacement } => {
                recursive_collect_pattern_vars(term, vars);
                vars.insert(var.to_string());
                recursive_collect_pattern_vars(replacement, vars);
            },
            PatternTerm::MultiSubst { scope, replacements } => {
                recursive_collect_pattern_vars(scope, vars);
                for replacement in replacements {
                    recursive_collect_pattern_vars(replacement, vars);
                }
            },
        },
        Pattern::Collection { elements, rest, .. } => {
            for element in elements {
                recursive_collect_pattern_vars(element, vars);
            }
            if let Some(rest) = rest {
                vars.insert(rest.to_string());
            }
        },
        Pattern::Map { collection, params, body } => {
            recursive_collect_pattern_vars(collection, vars);
            let mut body_vars = HashSet::new();
            recursive_collect_pattern_vars(body, &mut body_vars);
            for param in params {
                body_vars.remove(&param.to_string());
            }
            vars.extend(body_vars);
        },
        Pattern::Zip { first, second } => {
            recursive_collect_pattern_vars(first, vars);
            recursive_collect_pattern_vars(second, vars);
        },
        Pattern::IndexedVec { collection, index, element } => {
            vars.insert(collection.to_string());
            vars.insert(index.to_string());
            recursive_collect_pattern_vars(element, vars);
        },
    }
}

#[cfg(test)]
fn recursive_infer_type(
    pattern: &Pattern,
    language: &LanguageDef,
    context: &HashMap<String, String>,
) -> InferOutcome {
    match pattern {
        Pattern::Term(term) => match term {
            PatternTerm::Var(name) => InferOutcome::Type(
                context
                    .get(&name.to_string())
                    .cloned()
                    .unwrap_or_else(|| "?".to_string()),
            ),
            PatternTerm::Apply { constructor, args } => {
                let Some(rule) = language
                    .terms
                    .iter()
                    .find(|rule| rule.label == *constructor)
                else {
                    return InferOutcome::UnknownConstructor(constructor.to_string());
                };
                let arity = rule
                    .items
                    .iter()
                    .filter(|item| {
                        matches!(
                            item,
                            GrammarItem::NonTerminal { .. }
                                | GrammarItem::Binder { .. }
                                | GrammarItem::Collection { .. }
                        )
                    })
                    .count();
                for argument in args.iter().take(arity) {
                    if let outcome @ InferOutcome::UnknownConstructor(_) =
                        recursive_infer_type(argument, language, context)
                    {
                        return outcome;
                    }
                }
                InferOutcome::Type(rule.category.to_string())
            },
            PatternTerm::Lambda { body, .. } | PatternTerm::MultiLambda { body, .. } => {
                recursive_infer_type(body, language, context)
            },
            PatternTerm::Subst { term, .. } => recursive_infer_type(term, language, context),
            PatternTerm::MultiSubst { scope, .. } => recursive_infer_type(scope, language, context),
        },
        Pattern::Collection { elements, .. } => {
            for element in elements {
                if let outcome @ InferOutcome::UnknownConstructor(_) =
                    recursive_infer_type(element, language, context)
                {
                    return outcome;
                }
            }
            InferOutcome::Type("Collection".to_string())
        },
        Pattern::Map { collection, body, .. } => {
            if let outcome @ InferOutcome::UnknownConstructor(_) =
                recursive_infer_type(collection, language, context)
            {
                return outcome;
            }
            recursive_infer_type(body, language, context)
        },
        Pattern::Zip { first, second } => {
            for child in [first.as_ref(), second.as_ref()] {
                if let outcome @ InferOutcome::UnknownConstructor(_) =
                    recursive_infer_type(child, language, context)
                {
                    return outcome;
                }
            }
            InferOutcome::Type("?".to_string())
        },
        Pattern::IndexedVec { element, .. } => {
            if let outcome @ InferOutcome::UnknownConstructor(_) =
                recursive_infer_type(element, language, context)
            {
                return outcome;
            }
            InferOutcome::Type("?".to_string())
        },
    }
}

fn validation_error_name(result: Result<(), ValidationError>) -> Option<String> {
    match result {
        Ok(()) => None,
        Err(ValidationError::UnknownConstructor { name, .. }) => Some(name),
        Err(other) => panic!("pattern validation produced an unexpected error: {other:?}"),
    }
}

fn inference_outcome(result: Result<String, ValidationError>) -> InferOutcome {
    match result {
        Ok(category) => InferOutcome::Type(category),
        Err(ValidationError::UnknownConstructor { name, .. }) => {
            InferOutcome::UnknownConstructor(name)
        },
        Err(other) => panic!("pattern inference produced an unexpected error: {other:?}"),
    }
}

#[test]
fn pattern_pdas_match_the_recursive_oracles() {
    let language = syn::parse_str::<LanguageDef>(
        r#"
            name: PatternPda,
            types { Term }
            terms {
                Leaf . |- "leaf" : Term ;
                Node . child:Term |- "node" child : Term ;
                Pair . left:Term, right:Term |- "pair" left right : Term ;
            }
            equations {}
            rewrites {}
        "#,
    )
    .expect("oracle language must parse");
    let checker = TypeChecker::new(&language);
    let context = HashMap::from([
        ("x".to_string(), "Term".to_string()),
        ("y".to_string(), "Term".to_string()),
    ]);

    for seed in 0..256 {
        let pattern = patterned(seed, 5);

        let recursive_validation = recursive_validate_pattern(&pattern, &language);
        let iterative_validation = validate_pattern(&pattern, &language);
        assert_eq!(
            validation_error_name(iterative_validation),
            validation_error_name(recursive_validation),
            "validation diverged for seed {seed}: {pattern:?}",
        );

        let mut recursive_vars = HashSet::new();
        recursive_collect_pattern_vars(&pattern, &mut recursive_vars);
        let mut iterative_vars = HashSet::new();
        collect_pattern_vars(&pattern, &mut iterative_vars);
        assert_eq!(
            iterative_vars, recursive_vars,
            "variable collection diverged for seed {seed}: {pattern:?}",
        );

        let expected_type = recursive_infer_type(&pattern, &language, &context);
        let mut iterative_context = context.clone();
        let actual_type =
            inference_outcome(checker.infer_type_from_pattern(&pattern, &mut iterative_context));
        assert_eq!(
            actual_type, expected_type,
            "type inference diverged for seed {seed}: {pattern:?}",
        );
        assert_eq!(iterative_context, context, "inference mutated the variable context");
    }
}
