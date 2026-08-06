//! Test-only recursive equations superseded by the Dovetail metapattern PDAs.
//!
//! These functions are intentionally recursive: they are the independent, bounded oracle for
//! proving that the production worklist machines preserve the former traversal order, failure
//! order, diagnostics, and emitted token stream. They are never called on the 20k-depth witnesses.

use std::collections::{BTreeMap, HashSet};

use quote::quote;

use super::*;

fn recursive_find_binder_scope(
    language: &LanguageDef,
    pattern: &AstPattern,
    scope_var: &Ident,
) -> Option<BinderScope> {
    let AstPattern::Term(PatternTerm::Apply { constructor, args }) = pattern else {
        return None;
    };

    if let [AstPattern::Term(PatternTerm::Var(variable))] = args.as_slice() {
        if variable == scope_var {
            if let Some(category) = language.category_of_constructor(constructor) {
                for variant in collect_category_variants(category, language) {
                    match variant {
                        VariantKind::Binder { label, binder_cat, body_cat, .. }
                            if &label == constructor =>
                        {
                            return Some(BinderScope {
                                binder_label: label,
                                binder_cat: category.clone(),
                                binder_var_cat: binder_cat,
                                body_cat,
                                multi: false,
                            });
                        },
                        VariantKind::MultiBinder { label, binder_cat, body_cat, .. }
                            if &label == constructor =>
                        {
                            return Some(BinderScope {
                                binder_label: label,
                                binder_cat: category.clone(),
                                binder_var_cat: binder_cat,
                                body_cat,
                                multi: true,
                            });
                        },
                        _ => {},
                    }
                }
            }
        }
    }

    for argument in args {
        if let Some(scope) = recursive_find_binder_scope(language, argument, scope_var) {
            return Some(scope);
        }
    }
    None
}

fn recursive_pattern_contains_collection(pattern: &AstPattern) -> bool {
    match pattern {
        AstPattern::Collection { .. }
        | AstPattern::Map { .. }
        | AstPattern::Zip { .. }
        | AstPattern::IndexedVec { .. } => true,
        AstPattern::Term(term) => match term {
            PatternTerm::Apply { args, .. } => {
                args.iter().any(recursive_pattern_contains_collection)
            },
            PatternTerm::Lambda { body, .. } | PatternTerm::MultiLambda { body, .. } => {
                recursive_pattern_contains_collection(body)
            },
            PatternTerm::Subst { term, replacement, .. } => {
                recursive_pattern_contains_collection(term)
                    || recursive_pattern_contains_collection(replacement)
            },
            PatternTerm::MultiSubst { scope, replacements } => {
                recursive_pattern_contains_collection(scope)
                    || replacements
                        .iter()
                        .any(recursive_pattern_contains_collection)
            },
            PatternTerm::Var(_) => false,
        },
    }
}

fn recursive_collect_apply_constructors(pattern: &AstPattern, output: &mut HashSet<String>) {
    match pattern {
        AstPattern::Term(PatternTerm::Apply { constructor, args }) => {
            output.insert(constructor.to_string());
            for argument in args {
                recursive_collect_apply_constructors(argument, output);
            }
        },
        AstPattern::Collection { elements, .. } => {
            for element in elements {
                recursive_collect_apply_constructors(element, output);
            }
        },
        _ => {},
    }
}

fn recursive_pattern_contains_substitution(pattern: &AstPattern) -> bool {
    match pattern {
        AstPattern::Term(term) => recursive_term_contains_substitution(term),
        AstPattern::Collection { elements, .. } => {
            elements.iter().any(recursive_pattern_contains_substitution)
        },
        AstPattern::Map { collection, body, .. } => {
            recursive_pattern_contains_substitution(collection)
                || recursive_pattern_contains_substitution(body)
        },
        AstPattern::Zip { first, second } => {
            recursive_pattern_contains_substitution(first)
                || recursive_pattern_contains_substitution(second)
        },
        AstPattern::IndexedVec { element, .. } => recursive_pattern_contains_substitution(element),
    }
}

fn recursive_term_contains_substitution(term: &PatternTerm) -> bool {
    match term {
        PatternTerm::Subst { .. } | PatternTerm::MultiSubst { .. } => true,
        PatternTerm::Apply { args, .. } => args.iter().any(recursive_pattern_contains_substitution),
        PatternTerm::Lambda { body, .. } | PatternTerm::MultiLambda { body, .. } => {
            recursive_pattern_contains_substitution(body)
        },
        PatternTerm::Var(_) => false,
    }
}

fn recursive_pattern_to_dovetail(
    language: &LanguageDef,
    pattern: &AstPattern,
    enum_id: Option<&Ident>,
) -> Result<TokenStream, String> {
    match pattern {
        AstPattern::Term(term) => recursive_term_to_dovetail(language, term, enum_id),
        AstPattern::Collection { .. } => Err("a collection metapattern must be the argument of a constructor (AC bag); a bare collection has no operator".into()),
        AstPattern::Map { .. } => {
            Err("map metapatterns require collection-comprehension lowering".into())
        },
        AstPattern::Zip { .. } => {
            Err("zip metapatterns require collection-comprehension lowering".into())
        },
        AstPattern::IndexedVec { .. } => {
            Err("indexed-vec metapatterns require collection-comprehension lowering".into())
        },
    }
}

fn recursive_term_to_dovetail(
    language: &LanguageDef,
    term: &PatternTerm,
    enum_id: Option<&Ident>,
) -> Result<TokenStream, String> {
    match term {
        PatternTerm::Var(variable) => {
            if let Some(rule) = language.get_constructor(variable) {
                let op = constructor_op_expr(language, &rule.label, enum_id)?;
                Ok(quote! { ::dovetail::rules::Pattern::leaf(#op) })
            } else {
                let name = lit(&variable.to_string());
                Ok(quote! { ::dovetail::rules::Pattern::var(#name) })
            }
        },
        PatternTerm::Apply { constructor, args } => {
            if let [collection @ AstPattern::Collection { .. }] = args.as_slice() {
                return recursive_lower_ac_collection(language, constructor, collection, enum_id);
            }
            let op = constructor_op_expr(language, constructor, enum_id)?;
            let arguments = args
                .iter()
                .map(|argument| recursive_pattern_to_dovetail(language, argument, enum_id))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(quote! {
                ::dovetail::rules::Pattern::app(#op, vec![#(#arguments),*])
            })
        },
        PatternTerm::Lambda { .. } => Err("lambda patterns require binder lowering".into()),
        PatternTerm::MultiLambda { .. } => {
            Err("multi-lambda patterns require binder lowering".into())
        },
        PatternTerm::Subst { .. } => {
            Err("substitution patterns require generated substitution lowering".into())
        },
        PatternTerm::MultiSubst { .. } => {
            Err("multi-substitution patterns require generated substitution lowering".into())
        },
    }
}

fn recursive_lower_ac_collection(
    language: &LanguageDef,
    constructor: &Ident,
    collection: &AstPattern,
    enum_id: Option<&Ident>,
) -> Result<TokenStream, String> {
    let AstPattern::Collection { coll_type, elements, rest } = collection else {
        return Err("lower_ac_collection requires a Collection pattern".into());
    };
    match coll_type {
        None | Some(CollectionType::HashBag) => {},
        Some(other) => {
            return Err(format!("AC collection lowering supports HashBag only, found {other:?}"));
        },
    }

    let op = constructor_op_expr(language, constructor, enum_id)?;
    let fixed = elements
        .iter()
        .map(|element| recursive_pattern_to_dovetail(language, element, enum_id))
        .collect::<Result<Vec<_>, _>>()?;
    let rest = match rest {
        Some(name) => {
            let name = lit(&name.to_string());
            quote! { Some(#name.to_string()) }
        },
        None => quote! { None },
    };
    Ok(quote! {
        ::dovetail::rules::Pattern::ac(
            #op,
            vec![#(#fixed),*],
            #rest,
        )
    })
}

fn recursive_collapse_binder_scope(
    pattern: &AstPattern,
    binder_label: &Ident,
    scope_var: &Ident,
) -> AstPattern {
    match pattern {
        AstPattern::Term(PatternTerm::Apply { constructor, args }) => {
            if constructor == binder_label {
                if let [AstPattern::Term(PatternTerm::Var(variable))] = args.as_slice() {
                    if variable == scope_var {
                        return AstPattern::Term(PatternTerm::Var(scope_var.clone()));
                    }
                }
            }
            AstPattern::Term(PatternTerm::Apply {
                constructor: constructor.clone(),
                args: args
                    .iter()
                    .map(|argument| {
                        recursive_collapse_binder_scope(argument, binder_label, scope_var)
                    })
                    .collect(),
            })
        },
        other => other.clone(),
    }
}

fn recursive_variables(pattern: &AstPattern, variables: &mut BTreeMap<String, Ident>) {
    match pattern {
        AstPattern::Term(term) => match term {
            PatternTerm::Var(variable) => {
                variables
                    .entry(variable.to_string())
                    .or_insert_with(|| variable.clone());
            },
            PatternTerm::Apply { args, .. } => {
                for argument in args {
                    recursive_variables(argument, variables);
                }
            },
            PatternTerm::Lambda { binder, body } => {
                variables
                    .entry(binder.to_string())
                    .or_insert_with(|| binder.clone());
                recursive_variables(body, variables);
            },
            PatternTerm::MultiLambda { binders, body } => {
                for binder in binders {
                    variables
                        .entry(binder.to_string())
                        .or_insert_with(|| binder.clone());
                }
                recursive_variables(body, variables);
            },
            PatternTerm::Subst { term, var, replacement } => {
                recursive_variables(term, variables);
                variables
                    .entry(var.to_string())
                    .or_insert_with(|| var.clone());
                recursive_variables(replacement, variables);
            },
            PatternTerm::MultiSubst { scope, replacements } => {
                recursive_variables(scope, variables);
                for replacement in replacements {
                    recursive_variables(replacement, variables);
                }
            },
        },
        AstPattern::Collection { elements, rest, .. } => {
            for element in elements {
                recursive_variables(element, variables);
            }
            if let Some(rest) = rest {
                variables
                    .entry(rest.to_string())
                    .or_insert_with(|| rest.clone());
            }
        },
        AstPattern::Map { collection, params, body } => {
            recursive_variables(collection, variables);
            for parameter in params {
                variables
                    .entry(parameter.to_string())
                    .or_insert_with(|| parameter.clone());
            }
            recursive_variables(body, variables);
        },
        AstPattern::Zip { first, second } => {
            recursive_variables(first, variables);
            recursive_variables(second, variables);
        },
        AstPattern::IndexedVec { collection, index, element } => {
            variables
                .entry(collection.to_string())
                .or_insert_with(|| collection.clone());
            variables
                .entry(index.to_string())
                .or_insert_with(|| index.clone());
            recursive_variables(element, variables);
        },
    }
}

fn binder_key(scope: Option<BinderScope>) -> Option<(String, String, String, String, bool)> {
    scope.map(|scope| {
        (
            scope.binder_label.to_string(),
            scope.binder_cat.to_string(),
            scope.binder_var_cat.to_string(),
            scope.body_cat.to_string(),
            scope.multi,
        )
    })
}

fn token_result(result: Result<TokenStream, String>) -> Result<String, String> {
    result.map(|tokens| tokens.to_string())
}

fn variable(name: &str) -> AstPattern {
    AstPattern::Term(PatternTerm::Var(format_ident!("{name}")))
}

fn apply(constructor: &str, args: Vec<AstPattern>) -> AstPattern {
    AstPattern::Term(PatternTerm::Apply {
        constructor: format_ident!("{constructor}"),
        args,
    })
}

#[test]
fn dovetail_pattern_pdas_match_recursive_equations_across_the_bundled_corpus() {
    let typed_enum = format_ident!("OracleLanguageOp");
    let mut pattern_count = 0usize;
    let mut binder_queries = 0usize;
    let mut collapses = 0usize;

    for bundled in crate::gen::capture::bundled_corpus::bundled_languages() {
        let language = &bundled.def;
        for (kind, pattern) in language
            .equations
            .iter()
            .flat_map(|equation| {
                [
                    (format!("equation {} left", equation.name), &equation.left),
                    (format!("equation {} right", equation.name), &equation.right),
                ]
            })
            .chain(language.rewrites.iter().flat_map(|rewrite| {
                [
                    (format!("rewrite {} left", rewrite.name), &rewrite.left),
                    (format!("rewrite {} right", rewrite.name), &rewrite.right),
                ]
            }))
        {
            pattern_count += 1;
            assert_eq!(
                pattern_contains_collection(pattern),
                recursive_pattern_contains_collection(pattern),
                "collection detector diverged for {} {kind}",
                bundled.tag,
            );
            assert_eq!(
                pattern_contains_substitution(pattern),
                recursive_pattern_contains_substitution(pattern),
                "substitution detector diverged for {} {kind}",
                bundled.tag,
            );

            let mut actual_heads = HashSet::new();
            collect_apply_constructors(pattern, &mut actual_heads);
            let mut expected_heads = HashSet::new();
            recursive_collect_apply_constructors(pattern, &mut expected_heads);
            assert_eq!(
                actual_heads, expected_heads,
                "constructor collector diverged for {} {kind}",
                bundled.tag,
            );

            for enum_id in [None, Some(&typed_enum)] {
                assert_eq!(
                    token_result(pattern_to_dovetail(language, pattern, enum_id)),
                    token_result(recursive_pattern_to_dovetail(language, pattern, enum_id)),
                    "Dovetail token lowering diverged for {} {kind} ({})",
                    bundled.tag,
                    if enum_id.is_some() { "typed" } else { "string" },
                );
            }

            let mut variables = BTreeMap::new();
            recursive_variables(pattern, &mut variables);
            for variable in variables.values() {
                binder_queries += 1;
                let expected = recursive_find_binder_scope(language, pattern, variable);
                let expected_key = binder_key(expected);
                let actual_key = binder_key(find_binder_scope(language, pattern, variable));
                assert_eq!(
                    actual_key, expected_key,
                    "binder search diverged for {} {kind} variable {variable}",
                    bundled.tag,
                );

                if let Some((binder_label, ..)) = expected_key {
                    collapses += 1;
                    let binder_label = format_ident!("{binder_label}");
                    assert_eq!(
                        format!("{:?}", collapse_binder_scope(pattern, &binder_label, variable)),
                        format!(
                            "{:?}",
                            recursive_collapse_binder_scope(pattern, &binder_label, variable)
                        ),
                        "binder collapse diverged for {} {kind} variable {variable}",
                        bundled.tag,
                    );
                }
            }
        }
    }

    assert!(pattern_count >= 600, "only {pattern_count} pattern sides reached the oracle");
    assert!(binder_queries >= 600, "only {binder_queries} binder queries reached the oracle");
    assert!(collapses >= 2, "only {collapses} real binder collapses reached the oracle");
}

#[test]
fn dovetail_pattern_pdas_match_recursive_equations_on_bounded_nested_shapes() {
    let language = crate::gen::capture::bundled_corpus::bundled_language("Monoid").def;
    let mut pattern = variable("X");
    for _ in 0..64 {
        pattern = apply("Mul", vec![variable("Y"), pattern]);
    }

    assert_eq!(
        token_result(pattern_to_dovetail(&language, &pattern, None)),
        token_result(recursive_pattern_to_dovetail(&language, &pattern, None)),
    );
    assert_eq!(
        pattern_contains_collection(&pattern),
        recursive_pattern_contains_collection(&pattern),
    );
    assert_eq!(
        pattern_contains_substitution(&pattern),
        recursive_pattern_contains_substitution(&pattern),
    );
    let mut actual_heads = HashSet::new();
    collect_apply_constructors(&pattern, &mut actual_heads);
    let mut expected_heads = HashSet::new();
    recursive_collect_apply_constructors(&pattern, &mut expected_heads);
    assert_eq!(actual_heads, expected_heads);

    let binder = format_ident!("Mul");
    let scope = format_ident!("X");
    assert_eq!(
        format!("{:?}", collapse_binder_scope(&pattern, &binder, &scope)),
        format!("{:?}", recursive_collapse_binder_scope(&pattern, &binder, &scope)),
    );
    assert_eq!(
        binder_key(find_binder_scope(&language, &pattern, &scope)),
        binder_key(recursive_find_binder_scope(&language, &pattern, &scope)),
    );
}

#[test]
fn dovetail_pattern_pdas_traverse_twenty_thousand_levels_on_a_small_stack() {
    const DEPTH: usize = 20_000;
    std::thread::Builder::new()
        .name("dovetail-pattern-pda-small-stack".to_owned())
        .stack_size(256 * 1024)
        .spawn(|| {
            let language = crate::gen::capture::bundled_corpus::bundled_language("Monoid").def;
            let mut deep = variable("X");
            for _ in 0..DEPTH {
                deep = apply("Mul", vec![variable("Y"), deep]);
            }

            assert!(!pattern_contains_collection(&deep));
            assert!(!pattern_contains_substitution(&deep));
            let mut heads = HashSet::new();
            collect_apply_constructors(&deep, &mut heads);
            assert_eq!(heads, HashSet::from(["Mul".to_owned()]));
            assert!(find_binder_scope(&language, &deep, &format_ident!("missing")).is_none());

            let lowered = pattern_to_dovetail(&language, &deep, None)
                .expect("a valid 20k-deep application lowers without native-stack recursion");
            assert!(!lowered.is_empty());
            drop(lowered);

            let collapsed =
                collapse_binder_scope(&deep, &format_ident!("NotMul"), &format_ident!("X"));
            drop(collapsed);
            drop(deep);

            let mut late_substitution = AstPattern::Term(PatternTerm::Subst {
                term: Box::new(variable("X")),
                var: format_ident!("x"),
                replacement: Box::new(variable("Y")),
            });
            for _ in 0..DEPTH {
                late_substitution = apply("Mul", vec![variable("Y"), late_substitution]);
            }
            assert!(pattern_contains_substitution(&late_substitution));
            drop(late_substitution);
        })
        .expect("small-stack Dovetail metapattern thread must spawn")
        .join()
        .expect("Dovetail metapattern PDAs must finish on a 256 KiB stack");
}
