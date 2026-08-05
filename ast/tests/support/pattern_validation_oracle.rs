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
fn recursive_free_vars(pattern: &Pattern) -> HashSet<String> {
    match pattern {
        Pattern::Term(term) => recursive_term_free_vars(term),
        Pattern::Collection { elements, rest, .. } => {
            let mut vars = HashSet::new();
            for element in elements {
                vars.extend(recursive_free_vars(element));
            }
            if let Some(rest) = rest {
                vars.insert(rest.to_string());
            }
            vars
        },
        Pattern::Map { collection, params, body } => {
            let mut vars = recursive_free_vars(collection);
            let mut body_vars = recursive_free_vars(body);
            for param in params {
                body_vars.remove(&param.to_string());
            }
            vars.extend(body_vars);
            vars
        },
        Pattern::Zip { first, second } => {
            let mut vars = recursive_free_vars(first);
            vars.extend(recursive_free_vars(second));
            vars
        },
        Pattern::IndexedVec { collection, index, element } => {
            let mut vars = recursive_free_vars(element);
            vars.insert(collection.to_string());
            vars.insert(index.to_string());
            vars
        },
    }
}

#[cfg(test)]
fn recursive_term_free_vars(term: &PatternTerm) -> HashSet<String> {
    match term {
        PatternTerm::Var(ident) => HashSet::from([ident.to_string()]),
        PatternTerm::Apply { args, .. } => {
            let mut vars = HashSet::new();
            for argument in args {
                vars.extend(recursive_free_vars(argument));
            }
            vars
        },
        PatternTerm::Lambda { binder, body } => {
            let mut vars = recursive_free_vars(body);
            vars.remove(&binder.to_string());
            vars
        },
        PatternTerm::MultiLambda { binders, body } => {
            let mut vars = recursive_free_vars(body);
            for binder in binders {
                vars.remove(&binder.to_string());
            }
            vars
        },
        PatternTerm::Subst { term, var, replacement } => {
            let mut vars = recursive_free_vars(term);
            vars.insert(var.to_string());
            vars.extend(recursive_free_vars(replacement));
            vars
        },
        PatternTerm::MultiSubst { scope, replacements } => {
            let mut vars = recursive_free_vars(scope);
            for replacement in replacements {
                vars.extend(recursive_free_vars(replacement));
            }
            vars
        },
    }
}

#[cfg(test)]
fn recursive_var_occurrences(pattern: &Pattern, counts: &mut HashMap<String, usize>) {
    match pattern {
        Pattern::Term(term) => recursive_term_var_occurrences(term, counts),
        Pattern::Collection { elements, rest, .. } => {
            for element in elements {
                recursive_var_occurrences(element, counts);
            }
            if let Some(rest) = rest {
                *counts.entry(rest.to_string()).or_default() += 1;
            }
        },
        Pattern::Map { collection, params, body } => {
            recursive_var_occurrences(collection, counts);
            let mut body_counts = HashMap::new();
            recursive_var_occurrences(body, &mut body_counts);
            for param in params {
                body_counts.remove(&param.to_string());
            }
            for (name, count) in body_counts {
                *counts.entry(name).or_default() += count;
            }
        },
        Pattern::Zip { first, second } => {
            recursive_var_occurrences(first, counts);
            recursive_var_occurrences(second, counts);
        },
        Pattern::IndexedVec { collection, index, element } => {
            *counts.entry(collection.to_string()).or_default() += 1;
            *counts.entry(index.to_string()).or_default() += 1;
            recursive_var_occurrences(element, counts);
        },
    }
}

#[cfg(test)]
fn recursive_term_var_occurrences(term: &PatternTerm, counts: &mut HashMap<String, usize>) {
    match term {
        PatternTerm::Var(ident) => *counts.entry(ident.to_string()).or_default() += 1,
        PatternTerm::Apply { args, .. } => {
            for argument in args {
                recursive_var_occurrences(argument, counts);
            }
        },
        PatternTerm::Lambda { binder, body } => {
            let mut body_counts = HashMap::new();
            recursive_var_occurrences(body, &mut body_counts);
            body_counts.remove(&binder.to_string());
            for (name, count) in body_counts {
                *counts.entry(name).or_default() += count;
            }
        },
        PatternTerm::MultiLambda { binders, body } => {
            let mut body_counts = HashMap::new();
            recursive_var_occurrences(body, &mut body_counts);
            for binder in binders {
                body_counts.remove(&binder.to_string());
            }
            for (name, count) in body_counts {
                *counts.entry(name).or_default() += count;
            }
        },
        PatternTerm::Subst { term, var, replacement } => {
            recursive_var_occurrences(term, counts);
            *counts.entry(var.to_string()).or_default() += 1;
            recursive_var_occurrences(replacement, counts);
        },
        PatternTerm::MultiSubst { scope, replacements } => {
            recursive_var_occurrences(scope, counts);
            for replacement in replacements {
                recursive_var_occurrences(replacement, counts);
            }
        },
    }
}

#[cfg(test)]
fn recursive_constructor_labels(pattern: &Pattern, labels: &mut HashSet<String>) {
    match pattern {
        Pattern::Term(term) => match term {
            PatternTerm::Var(_) => {},
            PatternTerm::Apply { constructor, args } => {
                labels.insert(constructor.to_string());
                for argument in args {
                    recursive_constructor_labels(argument, labels);
                }
            },
            PatternTerm::Lambda { body, .. } | PatternTerm::MultiLambda { body, .. } => {
                recursive_constructor_labels(body, labels);
            },
            PatternTerm::Subst { term, replacement, .. } => {
                recursive_constructor_labels(term, labels);
                recursive_constructor_labels(replacement, labels);
            },
            PatternTerm::MultiSubst { scope, replacements } => {
                recursive_constructor_labels(scope, labels);
                for replacement in replacements {
                    recursive_constructor_labels(replacement, labels);
                }
            },
        },
        Pattern::Collection { elements, .. } => {
            for element in elements {
                recursive_constructor_labels(element, labels);
            }
        },
        Pattern::Map { collection, body, .. } => {
            recursive_constructor_labels(collection, labels);
            recursive_constructor_labels(body, labels);
        },
        Pattern::Zip { first, second } => {
            recursive_constructor_labels(first, labels);
            recursive_constructor_labels(second, labels);
        },
        Pattern::IndexedVec { element, .. } => recursive_constructor_labels(element, labels),
    }
}

#[cfg(test)]
fn recursive_is_ground(pattern: &Pattern, language: &LanguageDef) -> bool {
    match pattern {
        Pattern::Term(term) => match term {
            PatternTerm::Var(ident) => language.get_constructor(ident).is_some(),
            PatternTerm::Apply { args, .. } => args
                .iter()
                .all(|argument| recursive_is_ground(argument, language)),
            PatternTerm::Lambda { .. }
            | PatternTerm::MultiLambda { .. }
            | PatternTerm::Subst { .. }
            | PatternTerm::MultiSubst { .. } => false,
        },
        Pattern::Collection { elements, rest, .. } => {
            rest.is_none()
                && elements
                    .iter()
                    .all(|element| recursive_is_ground(element, language))
        },
        Pattern::Map { .. } | Pattern::Zip { .. } | Pattern::IndexedVec { .. } => false,
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

        assert_eq!(
            pattern.free_vars(),
            recursive_free_vars(&pattern),
            "free-variable analysis diverged for seed {seed}: {pattern:?}",
        );
        let mut expected_occurrences = HashMap::new();
        recursive_var_occurrences(&pattern, &mut expected_occurrences);
        assert_eq!(
            pattern.var_occurrences(),
            expected_occurrences,
            "variable occurrence counts diverged for seed {seed}: {pattern:?}",
        );
        let mut expected_labels = HashSet::new();
        recursive_constructor_labels(&pattern, &mut expected_labels);
        let mut actual_labels = HashSet::new();
        pattern.collect_constructor_labels(&mut actual_labels);
        assert_eq!(
            actual_labels, expected_labels,
            "constructor-label collection diverged for seed {seed}: {pattern:?}",
        );
        assert_eq!(
            pattern.is_ground_pattern(&language),
            recursive_is_ground(&pattern, &language),
            "groundness diverged for seed {seed}: {pattern:?}",
        );
        assert_eq!(
            format!("{:?}", pattern.clone()),
            format!("{pattern:?}"),
            "stack-safe clone changed the structure for seed {seed}",
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
