//! Bounded recursive reference equations for `observation_surface`.
//!
//! This module is compiled only by the parent module's unit-test build. Production owns no
//! recursive fallback; these equations preserve the superseded implementation independently so
//! the explicit rendering PDA can be checked for exact output and exact error precedence.

use super::*;
use mettail_runtime::Language;

fn collect_free_names_recursive(
    value: &RuntimeObservationValue,
    table: &mut FreeNameTable,
) -> Result<(), String> {
    match value {
        RuntimeObservationValue::Term { constructor, children }
            if constructor == FREE_VAR_REFLECT_LABEL =>
        {
            let [RuntimeObservationValue::Term { constructor: debug, children: none }] =
                children.as_slice()
            else {
                return Err(format!("^free carries one nullary debug leaf: {children:?}"));
            };
            if !none.is_empty() {
                return Err(format!("^free debug leaf is nullary: {children:?}"));
            }
            table.assign(debug);
            Ok(())
        },
        RuntimeObservationValue::Term { children, .. } => children
            .iter()
            .try_for_each(|child| collect_free_names_recursive(child, table)),
        RuntimeObservationValue::List(items)
        | RuntimeObservationValue::Tuple(items)
        | RuntimeObservationValue::Set(items) => items
            .iter()
            .try_for_each(|item| collect_free_names_recursive(item, table)),
        RuntimeObservationValue::Bag(entries) => entries
            .iter()
            .try_for_each(|(element, _)| collect_free_names_recursive(element, table)),
        RuntimeObservationValue::Map(entries) => entries.iter().try_for_each(|(key, value)| {
            collect_free_names_recursive(key, table)?;
            collect_free_names_recursive(value, table)
        }),
        _ => Ok(()),
    }
}

fn peano_value_recursive(value: &RuntimeObservationValue) -> Result<usize, String> {
    match value {
        RuntimeObservationValue::Term { constructor, children }
            if constructor == PEANO_ZERO_REFLECT_LABEL && children.is_empty() =>
        {
            Ok(0)
        },
        RuntimeObservationValue::Term { constructor, children }
            if constructor == PEANO_SUCC_REFLECT_LABEL && children.len() == 1 =>
        {
            Ok(1 + peano_value_recursive(&children[0])?)
        },
        other => Err(format!("not a reflected Peano numeral: {other:?}")),
    }
}

fn render_recursive(
    renderer: &SurfaceRenderer,
    value: &RuntimeObservationValue,
) -> Result<String, String> {
    let mut free_names = FreeNameTable::default();
    collect_free_names_recursive(value, &mut free_names)?;
    let mut fresh = FreshNames::new(free_names.used.clone());
    render_value_recursive(renderer, value, &mut Vec::new(), &free_names, &mut fresh)
}

fn render_value_recursive(
    renderer: &SurfaceRenderer,
    value: &RuntimeObservationValue,
    binders: &mut Vec<String>,
    free_names: &FreeNameTable,
    fresh: &mut FreshNames,
) -> Result<String, String> {
    match value {
        RuntimeObservationValue::Term { constructor, children } => match constructor.as_str() {
            FREE_VAR_REFLECT_LABEL => {
                let [leaf] = children.as_slice() else {
                    return Err(format!("^free carries one debug leaf: {children:?}"));
                };
                let RuntimeObservationValue::Term { constructor: debug, children: none } = leaf
                else {
                    return Err(format!("^free leaf is a nullary tag: {leaf:?}"));
                };
                if !none.is_empty() {
                    return Err(format!("^free leaf is nullary: {leaf:?}"));
                }
                free_names.by_debug.get(debug).cloned().ok_or_else(|| {
                    format!("^free({debug}) missed the collection pass — renderer defect")
                })
            },
            BOUND_VAR_REFLECT_LABEL => {
                let [peano] = children.as_slice() else {
                    return Err(format!("^bound carries one Peano leaf: {children:?}"));
                };
                let depth = peano_value_recursive(peano)?;
                binders.iter().rev().nth(depth).cloned().ok_or_else(|| {
                    format!(
                        "^bound({depth}) exceeds the {} enclosing binder scope(s) — \
                         a dangling de Bruijn index",
                        binders.len()
                    )
                })
            },
            LAMBDA_REFLECT_LABEL => {
                let [body] = children.as_slice() else {
                    return Err(format!("^lambda carries one body: {children:?}"));
                };
                let rule = renderer.unique_binder_rule()?;
                let Some([TermParam::Abstraction { binder, body: body_ident, .. }]) =
                    rule.term_context.as_deref()
                else {
                    unreachable!("unique_binder_rule guarantees the shape");
                };
                let fresh_name = fresh.generate();
                binders.push(fresh_name.clone());
                let body_text = render_value_recursive(renderer, body, binders, free_names, fresh)?;
                binders.pop();
                let pattern = rule.syntax_pattern.as_deref().ok_or_else(|| {
                    format!("binder production {} has no syntax pattern", rule.label)
                })?;
                let mut tokens = Vec::with_capacity(pattern.len());
                for item in pattern {
                    match item {
                        SyntaxExpr::Literal(text) => tokens.push(text.trim().to_string()),
                        SyntaxExpr::Param(ident) if ident == binder => {
                            tokens.push(fresh_name.clone());
                        },
                        SyntaxExpr::Param(ident) if ident == body_ident => {
                            tokens.push(body_text.clone());
                        },
                        SyntaxExpr::Param(other) => {
                            return Err(format!(
                                "binder production {} references unknown parameter {other}",
                                rule.label
                            ));
                        },
                        SyntaxExpr::Op(_) => {
                            return Err(format!(
                                "binder production {} uses pattern ops — unsupported for \
                                 de-reflection",
                                rule.label
                            ));
                        },
                        SyntaxExpr::TokenKind { .. } | SyntaxExpr::GuestBody { .. } => {
                            return Err(format!(
                                "binder production {} uses a token/guest-body capture — \
                                 unsupported for de-reflection",
                                rule.label
                            ));
                        },
                    }
                }
                Ok(tokens.join(" "))
            },
            MULTILAMBDA_REFLECT_LABEL => {
                Err("^multilambda de-reflection is not supported (no production language reflects \
                 multi-binder scopes yet)"
                    .to_string())
            },
            _ => render_constructor_recursive(
                renderer,
                constructor,
                children,
                binders,
                free_names,
                fresh,
            ),
        },
        RuntimeObservationValue::Bag(entries) => {
            let (_rule, separator, delimiters) = renderer.unique_bag_rule()?;
            let mut rendered = Vec::with_capacity(entries.len());
            for (element, count) in entries {
                let text = render_value_recursive(renderer, element, binders, free_names, fresh)?;
                for _ in 0..*count {
                    rendered.push(text.clone());
                }
            }
            rendered.sort();
            let joined = rendered.join(&format!(" {separator} "));
            match delimiters {
                Some((open, close)) if rendered.is_empty() => Ok(format!("{open}{close}")),
                Some((open, close)) => Ok(format!("{open} {joined} {close}")),
                None => Ok(joined),
            }
        },
        RuntimeObservationValue::Int(value) => Ok(value.to_string()),
        RuntimeObservationValue::Bool(value) => Ok(value.to_string()),
        other => Err(format!("observation shape has no surface de-reflection: {other:?}")),
    }
}

fn render_constructor_recursive(
    renderer: &SurfaceRenderer,
    constructor: &str,
    children: &[RuntimeObservationValue],
    binders: &mut Vec<String>,
    free_names: &FreeNameTable,
    fresh: &mut FreshNames,
) -> Result<String, String> {
    let rule = renderer
        .def
        .terms
        .iter()
        .find(|rule| rule.label == constructor)
        .ok_or_else(|| {
            format!("constructor {constructor} has no production in language {}", renderer.def.name)
        })?;

    if let (Some(context), Some(pattern)) =
        (rule.term_context.as_deref(), rule.syntax_pattern.as_deref())
    {
        let mut slots: BTreeMap<String, String> = BTreeMap::new();
        let mut child_iter = children.iter();
        for param in context {
            match param {
                TermParam::Simple { name, .. } => {
                    let child = child_iter.next().ok_or_else(|| {
                        format!("{constructor} is missing a child for parameter {name}")
                    })?;
                    let text = render_value_recursive(renderer, child, binders, free_names, fresh)?;
                    slots.insert(name.to_string(), text);
                },
                other => {
                    return Err(format!(
                        "{constructor} carries a non-simple parameter {other:?} — such \
                         constructors reflect as ^lambda, never by label"
                    ));
                },
            }
        }
        if child_iter.next().is_some() {
            return Err(format!(
                "{constructor} has more children than production parameters ({})",
                children.len()
            ));
        }
        let mut tokens = Vec::with_capacity(pattern.len());
        for item in pattern {
            match item {
                SyntaxExpr::Literal(text) => tokens.push(text.trim().to_string()),
                SyntaxExpr::Param(ident) => {
                    let text = slots.get(&ident.to_string()).ok_or_else(|| {
                        format!("{constructor} pattern references unknown parameter {ident}")
                    })?;
                    tokens.push(text.clone());
                },
                SyntaxExpr::Op(_) => {
                    return Err(format!(
                        "{constructor} uses pattern ops — unsupported for de-reflection"
                    ));
                },
                SyntaxExpr::TokenKind { .. } | SyntaxExpr::GuestBody { .. } => {
                    return Err(format!(
                        "{constructor} uses a token/guest-body capture — unsupported for \
                         de-reflection"
                    ));
                },
            }
        }
        return Ok(tokens.join(" "));
    }

    let mut tokens = Vec::with_capacity(rule.items.len());
    let mut child_iter = children.iter();
    for item in &rule.items {
        match item {
            GrammarItem::Terminal(text) => tokens.push(text.trim().to_string()),
            GrammarItem::NonTerminal { .. } => {
                let child = child_iter.next().ok_or_else(|| {
                    format!("{constructor} is missing a child for a nonterminal slot")
                })?;
                tokens.push(render_value_recursive(renderer, child, binders, free_names, fresh)?);
            },
            GrammarItem::Binder { .. } => {
                return Err(format!(
                    "{constructor} declares an old-style binder item — such constructors \
                     reflect as ^lambda, never by label"
                ));
            },
            GrammarItem::Collection { .. } => {
                let child = child_iter
                    .next()
                    .ok_or_else(|| format!("{constructor} is missing its collection child"))?;
                tokens.push(render_value_recursive(renderer, child, binders, free_names, fresh)?);
            },
        }
    }
    if child_iter.next().is_some() {
        return Err(format!(
            "{constructor} has more children than production slots ({})",
            children.len()
        ));
    }
    Ok(tokens.join(" "))
}

fn term(constructor: &str, children: Vec<RuntimeObservationValue>) -> RuntimeObservationValue {
    RuntimeObservationValue::Term {
        constructor: constructor.to_string(),
        children,
    }
}

fn nullary(constructor: &str) -> RuntimeObservationValue {
    term(constructor, Vec::new())
}

fn peano(depth: usize) -> RuntimeObservationValue {
    let mut value = nullary(PEANO_ZERO_REFLECT_LABEL);
    for _ in 0..depth {
        value = term(PEANO_SUCC_REFLECT_LABEL, vec![value]);
    }
    value
}

fn bound(depth: usize) -> RuntimeObservationValue {
    term(BOUND_VAR_REFLECT_LABEL, vec![peano(depth)])
}

fn lambda(body: RuntimeObservationValue) -> RuntimeObservationValue {
    term(LAMBDA_REFLECT_LABEL, vec![body])
}

fn free(debug: &str) -> RuntimeObservationValue {
    term(FREE_VAR_REFLECT_LABEL, vec![nullary(debug)])
}

fn definition_source(language: &dyn Language) -> &str {
    language
        .metadata()
        .definition_source()
        .expect("the generated language exposes its definition source")
}

#[test]
fn observation_surface_pda_matches_the_bounded_recursive_equations() {
    let lambda_language = mettail_languages::lambda::LambdaLanguage;
    let lambda_renderer =
        SurfaceRenderer::for_definition_source(definition_source(&lambda_language)).unwrap();

    let debug_x = "FreeVar { unique_id: UniqueId(7), pretty_name: Some(\"x\") }";
    let debug_x_twin = "FreeVar { unique_id: UniqueId(8), pretty_name: Some(\"x\") }";
    let cases = vec![
        term("App", vec![lambda(bound(0)), free(debug_x)]),
        lambda(lambda(term("App", vec![bound(1), free(debug_x_twin)]))),
        term("App", vec![RuntimeObservationValue::Int(1)]),
        term("App", vec![RuntimeObservationValue::Text("bad-first".to_string()), bound(0)]),
        bound(2),
        term(FREE_VAR_REFLECT_LABEL, vec![RuntimeObservationValue::Int(1)]),
        term("Foreign", Vec::new()),
        term(MULTILAMBDA_REFLECT_LABEL, vec![RuntimeObservationValue::Int(0)]),
    ];
    for case in &cases {
        assert_eq!(lambda_renderer.render(case), render_recursive(&lambda_renderer, case));
    }

    let mut spine = RuntimeObservationValue::Int(0);
    for _ in 0..64 {
        spine = term("App", vec![spine, RuntimeObservationValue::Bool(true)]);
    }
    assert_eq!(lambda_renderer.render(&spine), render_recursive(&lambda_renderer, &spine));

    let ambient_language = mettail_languages::ambient::AmbientLanguage;
    let ambient_renderer =
        SurfaceRenderer::for_definition_source(definition_source(&ambient_language)).unwrap();
    let bags = [
        RuntimeObservationValue::Bag(Vec::new()),
        RuntimeObservationValue::Bag(vec![
            (RuntimeObservationValue::Int(2), 2),
            (RuntimeObservationValue::Bool(true), 1),
        ]),
    ];
    for bag in &bags {
        assert_eq!(ambient_renderer.render(bag), render_recursive(&ambient_renderer, bag));
    }
}

#[test]
fn observation_surface_traverses_twenty_thousand_levels_on_a_small_stack() {
    const DEPTH: usize = 20_000;
    std::thread::Builder::new()
        .name("observation-surface-pda-depth".to_string())
        .stack_size(256 * 1024)
        .spawn(|| {
            let language = mettail_languages::lambda::LambdaLanguage;
            let renderer =
                SurfaceRenderer::for_definition_source(definition_source(&language)).unwrap();

            // The leaf's Peano spine independently drives the old `peano_value` recursion;
            // the enclosing lambdas drive renderer depth and establish enough binder frames.
            let mut value = bound(DEPTH - 1);
            for _ in 0..DEPTH {
                value = lambda(value);
            }
            let rendered = renderer
                .render(&value)
                .expect("the deep reflected term renders");
            assert!(rendered.starts_with("lam x0 ."));
            assert!(rendered.ends_with("x0"));
            assert!(rendered.len() > DEPTH * 8);

            // Dropping the recursive carrier is itself iterative in `mettail-runtime`; keeping
            // it inside the small-stack thread gates the entire end-to-end lifetime.
            drop(value);
        })
        .expect("the 256 KiB renderer gate thread spawns")
        .join()
        .expect("the 20,000-level renderer gate does not overflow");
}
