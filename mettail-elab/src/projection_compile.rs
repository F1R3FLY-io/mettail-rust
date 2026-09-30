//! Projection-source adaptation into the existing flat GSLT rule compiler.
//!
//! This module changes only endpoint selection and already-parsed term tags.
//! Type checking and arena construction remain in `theory_compile`.

use crate::ast::{
    ProjectionBinding, ProjectionBody, ProjectionDecl, ProjectionDirection, ProjectionPremise,
};
use crate::canonical::{RhoValue, ValueDecodeError};
use mettail_grammar_core as core;
use std::collections::BTreeSet;

fn string(value: impl Into<String>) -> RhoValue {
    RhoValue::String(value.into())
}

fn error<T>(path: &str, message: impl Into<String>) -> Result<T, ValueDecodeError> {
    Err(ValueDecodeError::new(path, message))
}

fn tagged<'a>(
    value: &'a RhoValue,
    path: &str,
) -> Result<(&'a str, &'a [RhoValue]), ValueDecodeError> {
    let RhoValue::List(parts) = value else {
        return error(path, "expected tagged projection term");
    };
    let Some(RhoValue::String(tag)) = parts.first() else {
        return error(path, "projection term has no tag");
    };
    Ok((tag, &parts[1..]))
}

fn text<'a>(value: &'a RhoValue, path: &str) -> Result<&'a str, ValueDecodeError> {
    let RhoValue::String(value) = value else {
        return error(path, "expected string");
    };
    Ok(value)
}

fn sequence<'a>(value: &'a RhoValue, path: &str) -> Result<&'a [RhoValue], ValueDecodeError> {
    let (tag, fields) = tagged(value, path)?;
    if tag != "sequence" {
        return error(path, "expected structural sequence");
    }
    Ok(fields)
}

/// Bounded explicit-stack conversion from the generated rule AST's tagged
/// values to the already supported canonical rule metasyntax. No source text
/// is parsed, and no recursive traversal consumes the native call stack.
fn canonical_rule_term(value: &RhoValue, path: &str) -> Result<RhoValue, ValueDecodeError> {
    enum Task<'a> {
        Visit(&'a RhoValue, String),
        FinishConstructor(String, usize),
        FinishCollection(usize, Option<String>),
        FinishAbstraction(String),
        FinishSubstitution,
    }
    let mut tasks = vec![Task::Visit(value, path.into())];
    let mut values = Vec::<RhoValue>::new();
    while let Some(task) = tasks.pop() {
        match task {
            Task::Visit(value, path) => {
                let (tag, fields) = tagged(value, &path)?;
                match tag {
                    "ast-var" | "ast-remainder" => {
                        if fields.len() != 1 {
                            return error(&path, "variable has wrong arity");
                        }
                        if tag == "ast-remainder" {
                            return error(
                                &path,
                                "collection remainder is outside final collection position",
                            );
                        }
                        values.push(string(text(&fields[0], &path)?));
                    },
                    "ast-sexp" | "ast-host-sexp" => {
                        if fields.len() != 2 {
                            return error(&path, "constructor has wrong arity");
                        }
                        let label = text(&fields[0], &path)?;
                        let name = if tag == "ast-host-sexp" {
                            format!("host::{label}")
                        } else {
                            label.into()
                        };
                        let arguments = sequence(&fields[1], &format!("{path}.arguments"))?;
                        tasks.push(Task::FinishConstructor(name, arguments.len()));
                        for (index, argument) in arguments.iter().enumerate().rev() {
                            tasks.push(Task::Visit(argument, format!("{path}.arguments[{index}]")));
                        }
                    },
                    "ast-collection" => {
                        if fields.len() != 1 {
                            return error(&path, "collection has wrong arity");
                        }
                        let elements = sequence(&fields[0], &format!("{path}.elements"))?;
                        let mut remainder = None;
                        let mut count = elements.len();
                        if let Some(last) = elements.last() {
                            if let Ok(("ast-remainder", fields)) = tagged(last, &path) {
                                if fields.len() != 1 {
                                    return error(&path, "remainder has wrong arity");
                                }
                                remainder = Some(text(&fields[0], &path)?.to_string());
                                count -= 1;
                            }
                        }
                        tasks.push(Task::FinishCollection(count, remainder));
                        for (index, element) in elements[..count].iter().enumerate().rev() {
                            tasks.push(Task::Visit(element, format!("{path}.elements[{index}]")));
                        }
                    },
                    "ast-abs" => {
                        if fields.len() != 2 {
                            return error(&path, "abstraction has wrong arity");
                        }
                        let binder = text(&fields[0], &path)?.to_string();
                        tasks.push(Task::FinishAbstraction(binder));
                        tasks.push(Task::Visit(&fields[1], format!("{path}.body")));
                    },
                    "ast-subst" => {
                        if fields.len() != 2 {
                            return error(&path, "substitution has wrong arity");
                        }
                        tasks.push(Task::FinishSubstitution);
                        tasks.push(Task::Visit(&fields[1], format!("{path}.argument")));
                        tasks.push(Task::Visit(&fields[0], format!("{path}.abstraction")));
                    },
                    "ast-string" => {
                        if fields.len() != 1 {
                            return error(&path, "string literal has wrong arity");
                        }
                        values.push(RhoValue::List(vec![
                            string("lit"),
                            string("String"),
                            fields[0].clone(),
                        ]));
                    },
                    "ast-integer" => {
                        if fields.len() != 1 {
                            return error(&path, "integer literal has wrong arity");
                        }
                        values.push(RhoValue::List(vec![
                            string("lit"),
                            string("i128"),
                            fields[0].clone(),
                        ]));
                    },
                    "ast-boolean-true" | "ast-boolean-false" => {
                        if !fields.is_empty() {
                            return error(&path, "Boolean literal has wrong arity");
                        }
                        values.push(RhoValue::List(vec![
                            string("lit"),
                            string("bool"),
                            RhoValue::Boolean(tag == "ast-boolean-true"),
                        ]));
                    },
                    _ => return error(&path, format!("unknown projection term tag `{tag}`")),
                }
            },
            Task::FinishConstructor(name, count) => {
                let start = values.len().checked_sub(count).ok_or_else(|| {
                    ValueDecodeError::new(path, "constructor result stack underflow")
                })?;
                let mut result = vec![string(name)];
                result.extend(values.drain(start..));
                values.push(RhoValue::List(result));
            },
            Task::FinishCollection(count, remainder) => {
                let start = values.len().checked_sub(count).ok_or_else(|| {
                    ValueDecodeError::new(path, "collection result stack underflow")
                })?;
                let elements = RhoValue::List(values.drain(start..).collect());
                values.push(RhoValue::List(vec![
                    string("coll"),
                    elements,
                    remainder.map(string).unwrap_or(RhoValue::Nil),
                ]));
            },
            Task::FinishAbstraction(binder) => {
                let body = values.pop().ok_or_else(|| {
                    ValueDecodeError::new(path, "abstraction result stack underflow")
                })?;
                values.push(RhoValue::List(vec![string("^"), string(binder), body]));
            },
            Task::FinishSubstitution => {
                let argument = values.pop().ok_or_else(|| {
                    ValueDecodeError::new(path, "substitution argument stack underflow")
                })?;
                let abstraction = values.pop().ok_or_else(|| {
                    ValueDecodeError::new(path, "substitution abstraction stack underflow")
                })?;
                values.push(RhoValue::List(vec![string("eval"), abstraction, argument]));
            },
        }
    }
    if values.len() != 1 {
        return error(path, "projection conversion did not produce one term");
    }
    Ok(values.pop().expect("checked one term"))
}

fn directions(direction: ProjectionDirection) -> Vec<core::ProjectionDirectionV1> {
    match direction {
        ProjectionDirection::GuestToHost => vec![core::ProjectionDirectionV1::GuestToHost],
        ProjectionDirection::HostToGuest => vec![core::ProjectionDirectionV1::HostToGuest],
        ProjectionDirection::Both => vec![
            core::ProjectionDirectionV1::GuestToHost,
            core::ProjectionDirectionV1::HostToGuest,
        ],
    }
}

pub(crate) fn compile_projections(
    declarations: &[ProjectionDecl],
    theory: &core::TheoryCoreV1,
    host: &core::ProjectionHostSignatureV1,
) -> Result<Vec<core::TheoryProjectionV1>, ValueDecodeError> {
    let mut compiled = Vec::with_capacity(declarations.len());
    let host_sorts: BTreeSet<_> = host.sorts.iter().map(|sort| sort.name.as_str()).collect();
    for (index, declaration) in declarations.iter().enumerate() {
        let path = format!("$.projections[{index}]");
        if !host_sorts.contains(declaration.host.as_str()) {
            return error(
                &format!("{path}.host"),
                format!("host category `{}` is absent from the pinned signature", declaration.host),
            );
        }
        let body = match &declaration.body {
            ProjectionBody::Carrier => core::ProjectionBodyV1::Carrier,
            ProjectionBody::Rules(rows) => {
                let mut directed = Vec::new();
                for (source, row) in rows.iter().enumerate() {
                    let row_path = format!("{path}.rules[{source}]");
                    let guest = canonical_rule_term(&row.guest, &format!("{row_path}.guest"))?;
                    let host_term = canonical_rule_term(&row.host, &format!("{row_path}.host"))?;
                    let context = RhoValue::List(
                        row.bindings
                            .iter()
                            .map(|binding| {
                                let (name, sort) = match binding {
                                    ProjectionBinding::Guest { name, category } => {
                                        (name.clone(), category.clone())
                                    },
                                    ProjectionBinding::Host { name, category } => {
                                        (name.clone(), format!("host::{category}"))
                                    },
                                };
                                RhoValue::List(vec![string("typed"), string(name), string(sort)])
                            })
                            .collect(),
                    );
                    let mut premises = Vec::with_capacity(row.premises.len());
                    for (premise_index, premise) in row.premises.iter().enumerate() {
                        match premise {
                            ProjectionPremise::Transition { left, right } => premises.push(RhoValue::List(vec![string("~>"), string(left), string(right)])),
                            ProjectionPremise::Call { .. } => return error(
                                &format!("{row_path}.premises[{premise_index}]"),
                                "typed subprojection premises require the selected-relation kernel opcode",
                            ),
                        }
                    }
                    let premises = RhoValue::List(premises);
                    for direction in directions(row.direction) {
                        let (left, right, input_sort, output_sort) = match direction {
                            core::ProjectionDirectionV1::GuestToHost => (
                                &guest,
                                &host_term,
                                declaration.guest.clone(),
                                format!("host::{}", declaration.host),
                            ),
                            core::ProjectionDirectionV1::HostToGuest => (
                                &host_term,
                                &guest,
                                format!("host::{}", declaration.host),
                                declaration.guest.clone(),
                            ),
                        };
                        let rule = crate::theory_compile::compile_projection_rule(
                            &row.name,
                            &context,
                            &premises,
                            left,
                            right,
                            &input_sort,
                            &output_sort,
                            theory,
                            host,
                            &row_path,
                        )?;
                        directed.push(core::DirectedProjectionRuleV1 {
                            direction,
                            source_occurrence: u32::try_from(source).map_err(|_| {
                                ValueDecodeError::new(
                                    &row_path,
                                    "projection source occurrence overflow",
                                )
                            })?,
                            rule,
                        });
                    }
                }
                core::ProjectionBodyV1::Rules(directed)
            },
        };
        compiled.push(core::TheoryProjectionV1 {
            name: declaration.name.clone(),
            guest_category: declaration.guest.clone(),
            host: core::ProjectionHostEndpointV1 {
                signature_fingerprint: host.signature_fingerprint,
                category: declaration.host.clone(),
                codec_profile_fingerprint: host.codec_profile_fingerprint,
            },
            directions: directions(declaration.direction),
            body,
        });
    }
    Ok(compiled)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::ProjectionRule;
    use crate::lex::Span;

    fn node(tag: &str, fields: impl IntoIterator<Item = RhoValue>) -> RhoValue {
        RhoValue::List(std::iter::once(string(tag)).chain(fields).collect())
    }

    fn constructor(label: &str, host: bool, arguments: Vec<RhoValue>) -> RhoValue {
        node(
            if host { "ast-host-sexp" } else { "ast-sexp" },
            [string(label), node("sequence", arguments)],
        )
    }

    #[test]
    fn bidirectional_bool_and_structured_proc_use_existing_flat_rule_arenas() {
        let span = Span { line: 1, col: 1 };
        let mut theory = core::TheoryCoreV1::structural();
        for name in ["Bool", "Pair"] {
            theory.sorts.push(core::TheorySortV1 {
                name: name.into(),
                kind: core::TheorySortKindV1::Syntax { literal: None },
            });
        }
        for (name, sort) in [("BTrue", "Bool"), ("GPair", "Pair")] {
            theory.constructors.push(core::TheoryConstructorV1 {
                name: name.into(),
                domain: vec![],
                codomain: sort.into(),
            });
        }
        let host = core::ProjectionHostSignatureV1 {
            signature_fingerprint: [7; 32],
            codec_profile_fingerprint: [9; 32],
            sorts: vec![
                core::TheorySortV1 {
                    name: "Bool".into(),
                    kind: core::TheorySortKindV1::Syntax {
                        literal: Some(core::TheoryLiteralCarrierV1::Boolean),
                    },
                },
                core::TheorySortV1 {
                    name: "Proc".into(),
                    kind: core::TheorySortKindV1::Syntax { literal: None },
                },
            ],
            constructors: vec![
                core::TheoryConstructorV1 {
                    name: "Nil".into(),
                    domain: vec![],
                    codomain: "Proc".into(),
                },
                core::TheoryConstructorV1 {
                    name: "PParInfix".into(),
                    domain: vec!["Proc".into(), "Proc".into()],
                    codomain: "Proc".into(),
                },
            ],
        };
        let declarations = vec![
            ProjectionDecl {
                name: "Boolean".into(),
                guest: "Bool".into(),
                host: "Bool".into(),
                direction: ProjectionDirection::Both,
                body: ProjectionBody::Rules(vec![ProjectionRule {
                    name: "Yes".into(),
                    bindings: vec![],
                    premises: vec![],
                    guest: constructor("BTrue", false, vec![]),
                    host: node("ast-boolean-true", []),
                    direction: ProjectionDirection::Both,
                    span,
                }]),
                span,
            },
            ProjectionDecl {
                name: "Structure".into(),
                guest: "Pair".into(),
                host: "Proc".into(),
                direction: ProjectionDirection::Both,
                body: ProjectionBody::Rules(vec![ProjectionRule {
                    name: "Pair".into(),
                    bindings: vec![],
                    premises: vec![],
                    guest: constructor("GPair", false, vec![]),
                    host: constructor(
                        "PParInfix",
                        true,
                        vec![constructor("Nil", true, vec![]), constructor("Nil", true, vec![])],
                    ),
                    direction: ProjectionDirection::Both,
                    span,
                }]),
                span,
            },
        ];
        let compiled = compile_projections(&declarations, &theory, &host)
            .expect("both endpoint signatures use the existing typed rule compiler");
        for (projection, guest, host_sort) in
            [(&compiled[0], "Bool", "host::Bool"), (&compiled[1], "Pair", "host::Proc")]
        {
            let core::ProjectionBodyV1::Rules(rows) = &projection.body else {
                panic!("expected rules")
            };
            assert_eq!(rows.len(), 2);
            assert_eq!(rows[0].source_occurrence, rows[1].source_occurrence);
            assert_eq!(rows[0].rule.arena.terms[rows[0].rule.left.0 as usize].sort, guest);
            assert_eq!(rows[0].rule.arena.terms[rows[0].rule.right.0 as usize].sort, host_sort);
            assert_eq!(rows[1].rule.arena.terms[rows[1].rule.left.0 as usize].sort, host_sort);
            assert_eq!(rows[1].rule.arena.terms[rows[1].rule.right.0 as usize].sort, guest);
        }
    }
}
