//! Structural compilation of canonical rule data into executable theory arenas.
//!
//! This module consumes the already-parsed `RhoValue` representation. It never
//! renders or reparses source. All recursive surface shapes are traversed with
//! explicit worklists, and every emitted edge points backward in its arena.

use crate::canonical::{RhoValue, ValueDecodeError};
use mettail_grammar_core as core;
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone)]
struct Signature {
    sorts: Vec<core::TheorySortV1>,
    sort_indices: BTreeMap<String, usize>,
    constructors: BTreeMap<String, core::TheoryConstructorV1>,
    judgments: BTreeMap<String, Vec<String>>,
}

impl Signature {
    fn from_theory(theory: &core::TheoryCoreV1) -> Self {
        Self {
            sorts: theory.sorts.clone(),
            sort_indices: theory
                .sorts
                .iter()
                .enumerate()
                .map(|(index, sort)| (sort.name.clone(), index))
                .collect(),
            constructors: theory
                .constructors
                .iter()
                .map(|constructor| (constructor.name.clone(), constructor.clone()))
                .collect(),
            judgments: theory
                .judgments
                .iter()
                .map(|judgment| (judgment.name.clone(), judgment.arguments.clone()))
                .collect(),
        }
    }

    fn sort(&self, name: &str) -> Option<&core::TheorySortV1> {
        self.sort_indices
            .get(name)
            .and_then(|index| self.sorts.get(*index))
    }

    fn unique_literal_sort(
        &self,
        literal: &core::TheoryLiteralV1,
        path: &str,
    ) -> Result<String, ValueDecodeError> {
        let carrier = literal_carrier(literal);
        let mut matches = self.sorts.iter().filter(|sort| {
            matches!(
                &sort.kind,
                core::TheorySortKindV1::Syntax { literal: Some(candidate) }
                    if candidate == carrier
            )
        });
        let Some(first) = matches.next() else {
            return error(path, format!("no theory sort admits the `{carrier:?}` literal carrier"));
        };
        if matches.next().is_some() {
            return error(path, "literal sort is ambiguous; supply a typed pattern context");
        }
        Ok(first.name.clone())
    }

    fn function_sort(
        &self,
        domain: &str,
        codomain: &str,
        multiple: bool,
        path: &str,
    ) -> Result<String, ValueDecodeError> {
        let mut matches = self.sorts.iter().filter(|sort| {
            matches!(
                &sort.kind,
                core::TheorySortKindV1::Function {
                    domain: candidate_domain,
                    codomain: candidate_codomain,
                    multiple: candidate_multiple,
                } if candidate_domain == domain
                    && candidate_codomain == codomain
                    && *candidate_multiple == multiple
            )
        });
        let Some(first) = matches.next() else {
            return error(
                path,
                format!("no declared function sort maps `{domain}` to `{codomain}`"),
            );
        };
        if matches.next().is_some() {
            return error(path, "function sort is ambiguous");
        }
        Ok(first.name.clone())
    }
}

pub(crate) fn compile_surface_rules(
    equations: &[RhoValue],
    rewrites: &[RhoValue],
    theory: &mut core::TheoryCoreV1,
) -> Result<(), ValueDecodeError> {
    let signature = Signature::from_theory(theory);
    let mut equation_names = BTreeSet::new();
    for (index, value) in equations.iter().enumerate() {
        let path = format!("$.equations[{index}]");
        let compiled = compile_equation(value, &path, &signature, theory.limits)?;
        if !equation_names.insert(compiled.name.clone()) {
            return error(path, format!("duplicate equation name `{}`", compiled.name));
        }
        theory.equations.push(compiled);
    }
    let mut rewrite_names = BTreeSet::new();
    for (index, value) in rewrites.iter().enumerate() {
        let path = format!("$.rewrites[{index}]");
        let compiled = compile_rewrite(value, &path, &signature, theory.limits)?;
        if !rewrite_names.insert(compiled.name.clone()) {
            return error(path, format!("duplicate rewrite name `{}`", compiled.name));
        }
        theory.rewrites.push(compiled);
    }
    Ok(())
}

pub(crate) fn infer_judgment_types(
    theory: &mut core::TheoryCoreV1,
) -> Result<(), ValueDecodeError> {
    let signature = Signature::from_theory(theory);
    for judgment in &mut theory.judgments {
        for rule in &mut judgment.rules {
            let path = format!("$.oslf.judgments.{}.rules.{}", judgment.name, rule.name);
            let atoms = rule
                .premises
                .iter()
                .chain(std::iter::once(&rule.conclusion))
                .cloned()
                .collect::<Vec<_>>();
            for atom in atoms {
                let argument_sorts = signature.judgments.get(&atom.judgment).ok_or_else(|| {
                    ValueDecodeError::new(&path, format!("unknown judgment `{}`", atom.judgment))
                })?;
                if atom.terms.len() != argument_sorts.len() {
                    return error(
                        &path,
                        format!(
                            "judgment `{}` expects {} terms, found {}",
                            atom.judgment,
                            argument_sorts.len(),
                            atom.terms.len()
                        ),
                    );
                }
                for (root, expected) in atom.terms.iter().zip(argument_sorts) {
                    constrain_term_arena(
                        *root,
                        expected,
                        &signature,
                        &mut rule.variables,
                        &mut rule.terms,
                        &path,
                    )?;
                }
            }
            if let Some(variable) = rule
                .variables
                .iter()
                .find(|variable| variable.sort.is_empty())
            {
                return error(
                    &path,
                    format!("cannot infer sort of judgment variable `{}`", variable.name),
                );
            }
            if rule.terms.iter().any(|term| term.sort.is_empty()) {
                return error(&path, "cannot infer every judgment term sort");
            }
        }
    }
    Ok(())
}

fn constrain_term_arena(
    root: core::TheoryTermId,
    expected: &str,
    signature: &Signature,
    variables: &mut [core::TheoryVariableV1],
    terms: &mut [core::TheoryTermNodeV1],
    path: &str,
) -> Result<(), ValueDecodeError> {
    let mut work = vec![(root, expected.to_string())];
    while let Some((term, expected)) = work.pop() {
        let node = terms.get_mut(term.0 as usize).ok_or_else(|| {
            ValueDecodeError::new(path, format!("unknown theory term #{}", term.0))
        })?;
        if node.sort.is_empty() {
            node.sort = expected.clone();
        } else if node.sort != expected {
            return error(
                path,
                format!("term #{} has sort `{}`, expected `{expected}`", term.0, node.sort),
            );
        }
        match node.form.clone() {
            core::TheoryTermFormV1::Variable(variable) => {
                let variable = variables.get_mut(variable.0 as usize).ok_or_else(|| {
                    ValueDecodeError::new(path, format!("unknown theory variable #{}", variable.0))
                })?;
                if variable.sort.is_empty() {
                    variable.sort = expected;
                } else if variable.sort != expected {
                    return error(
                        path,
                        format!(
                            "variable `{}` has sort `{}`, expected `{expected}`",
                            variable.name, variable.sort
                        ),
                    );
                }
            },
            core::TheoryTermFormV1::Constructor { constructor, arguments } => {
                let declaration = signature.constructors.get(&constructor).ok_or_else(|| {
                    ValueDecodeError::new(path, format!("unknown constructor `{constructor}`"))
                })?;
                if declaration.codomain != expected {
                    return error(
                        path,
                        format!(
                            "constructor `{constructor}` returns `{}`, expected `{expected}`",
                            declaration.codomain
                        ),
                    );
                }
                if arguments.len() != declaration.domain.len() {
                    return error(
                        path,
                        format!(
                            "constructor `{constructor}` expects {} arguments, found {}",
                            declaration.domain.len(),
                            arguments.len()
                        ),
                    );
                }
                work.extend(
                    arguments
                        .into_iter()
                        .zip(declaration.domain.iter().cloned())
                        .rev(),
                );
            },
            core::TheoryTermFormV1::Literal(_) => {},
            _ => return error(
                path,
                "the OSLF judgment value schema admits only variables, constructors, and literals",
            ),
        }
    }
    Ok(())
}

fn compile_equation(
    value: &RhoValue,
    path: &str,
    signature: &Signature,
    limits: core::TheoryLimitsV1,
) -> Result<core::TheoryEquationV1, ValueDecodeError> {
    let values = expect_map(value, path)?;
    let name = required_string(values, "name", path)?.to_string();
    let mut compiler = RuleCompiler::new(signature, limits, &name);
    compiler.decode_context(values.get("context"), &format!("{path}.context"))?;
    let left = compiler.compile_pattern(
        required(values, "left", path)?,
        None,
        Side::Left,
        &format!("{path}.left"),
    )?;
    compiler.compile_premises(values.get("premises"), false, &format!("{path}.premises"))?;
    let left_sort = compiler.term_sort(left)?.to_string();
    let right = compiler.compile_pattern(
        required(values, "right", path)?,
        Some(left_sort),
        Side::Right,
        &format!("{path}.right"),
    )?;
    Ok(core::TheoryEquationV1 {
        name,
        arena: compiler.finish()?,
        left,
        right,
    })
}

fn compile_rewrite(
    value: &RhoValue,
    path: &str,
    signature: &Signature,
    limits: core::TheoryLimitsV1,
) -> Result<core::TheoryRewriteV1, ValueDecodeError> {
    let values = expect_map(value, path)?;
    let name = required_string(values, "name", path)?.to_string();
    let mut compiler = RuleCompiler::new(signature, limits, &name);
    compiler.decode_context(values.get("context"), &format!("{path}.context"))?;
    let left = compiler.compile_pattern(
        required(values, "left", path)?,
        None,
        Side::Left,
        &format!("{path}.left"),
    )?;
    compiler.compile_premises(values.get("premises"), true, &format!("{path}.premises"))?;
    let left_sort = compiler.term_sort(left)?.to_string();
    let right = compiler.compile_pattern(
        required(values, "right", path)?,
        Some(left_sort),
        Side::Right,
        &format!("{path}.right"),
    )?;
    Ok(core::TheoryRewriteV1 {
        name,
        arena: compiler.finish()?,
        left,
        right,
    })
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Side {
    Left,
    Right,
}

struct RuleCompiler<'a> {
    signature: &'a Signature,
    limits: core::TheoryLimitsV1,
    rule: String,
    variable_ids: BTreeMap<String, core::TheoryVariableId>,
    variable_names: BTreeSet<String>,
    variables: Vec<core::TheoryVariableV1>,
    terms: Vec<core::TheoryTermNodeV1>,
    premises: Vec<core::TheoryPremiseNodeV1>,
    premise_roots: Vec<core::TheoryPremiseId>,
}

impl<'a> RuleCompiler<'a> {
    fn new(signature: &'a Signature, limits: core::TheoryLimitsV1, rule: &str) -> Self {
        Self {
            signature,
            limits,
            rule: rule.to_string(),
            variable_ids: BTreeMap::new(),
            variable_names: BTreeSet::new(),
            variables: Vec::new(),
            terms: Vec::new(),
            premises: Vec::new(),
            premise_roots: Vec::new(),
        }
    }

    fn finish(self) -> Result<core::TheoryRuleArenaV1, ValueDecodeError> {
        if self.variables.len() > self.limits.max_rule_variables as usize {
            return error(
                &self.rule,
                format!(
                    "rule has {} variables, limit is {}",
                    self.variables.len(),
                    self.limits.max_rule_variables
                ),
            );
        }
        Ok(core::TheoryRuleArenaV1 {
            variables: self.variables,
            terms: self.terms,
            premises: self.premises,
            premise_roots: self.premise_roots,
        })
    }

    fn decode_context(
        &mut self,
        value: Option<&RhoValue>,
        path: &str,
    ) -> Result<(), ValueDecodeError> {
        let Some(value) = value else { return Ok(()) };
        for (index, entry) in expect_list(value, path)?.iter().enumerate() {
            let entry_path = format!("{path}[{index}]");
            let entry = expect_list(entry, &entry_path)?;
            if entry.len() != 3 || expect_string(&entry[0], &format!("{entry_path}[0]"))? != "typed"
            {
                return error(&entry_path, "expected [\"typed\", name, sort]");
            }
            let name = expect_nonempty_string(&entry[1], &format!("{entry_path}[1]"))?;
            let sort = decode_context_sort(&entry[2], &format!("{entry_path}[2]"))?;
            if self.signature.sort(&sort).is_none() {
                return error(&entry_path, format!("unknown theory sort `{sort}`"));
            }
            self.add_variable(name, &sort, core::TheoryVariableRoleV1::Input, &entry_path)?;
        }
        Ok(())
    }

    fn compile_pattern(
        &mut self,
        value: &RhoValue,
        expected: Option<String>,
        side: Side,
        path: &str,
    ) -> Result<core::TheoryTermId, ValueDecodeError> {
        enum Task<'a> {
            Visit {
                value: &'a RhoValue,
                expected: Option<String>,
                side: Side,
                path: String,
            },
            FinishConstructor {
                name: String,
                sort: String,
                arity: usize,
            },
            FinishAbstraction {
                binder: core::TheoryVariableId,
                sort: String,
            },
            FinishSubstitution {
                sort: String,
            },
            FinishCollection {
                sort: String,
                count: usize,
                remainder: Option<core::TheoryVariableId>,
            },
        }

        let mut tasks = vec![Task::Visit {
            value,
            expected,
            side,
            path: path.to_string(),
        }];
        let mut values = Vec::<core::TheoryTermId>::new();
        while let Some(task) = tasks.pop() {
            match task {
                Task::Visit {
                    value: RhoValue::String(name),
                    expected,
                    side,
                    path,
                } => {
                    let sort = match expected {
                        Some(sort) => sort,
                        None => self
                            .variable_ids
                            .get(name)
                            .and_then(|id| self.variables.get(id.0 as usize))
                            .map(|variable| variable.sort.clone())
                            .ok_or_else(|| {
                                ValueDecodeError::new(
                                    &path,
                                    format!("cannot infer sort of variable `{name}`"),
                                )
                            })?,
                    };
                    let variable = match side {
                        Side::Left => self.add_or_constrain_input(
                            name,
                            &sort,
                            core::TheoryVariableRoleV1::Input,
                            &path,
                        )?,
                        Side::Right => self.require_variable(name, &sort, &path)?,
                    };
                    values.push(self.push_term(
                        sort,
                        core::TheoryTermFormV1::Variable(variable),
                        &path,
                    )?);
                },
                Task::Visit { value, expected, side, path } => {
                    let tagged = expect_list(value, &path)?;
                    let tag = tagged
                        .first()
                        .ok_or_else(|| ValueDecodeError::new(&path, "empty pattern node"))?;
                    let tag = expect_nonempty_string(tag, &format!("{path}[0]"))?;
                    match tag {
                        "eval" => {
                            if tagged.len() != 3 {
                                return error(
                                    &path,
                                    "canonical executable substitution requires [\"eval\", abstraction, argument]",
                                );
                            }
                            let codomain = expected.ok_or_else(|| {
                                ValueDecodeError::new(
                                    &path,
                                    "substitution result needs an expected sort",
                                )
                            })?;
                            let domain = self.infer_root_sort(&tagged[2], &format!("{path}[2]"))?;
                            let function = self.signature.function_sort(
                                &domain,
                                &codomain,
                                false,
                                &path,
                            )?;
                            tasks.push(Task::FinishSubstitution { sort: codomain });
                            tasks.push(Task::Visit {
                                value: &tagged[2],
                                expected: Some(domain),
                                side,
                                path: format!("{path}[2]"),
                            });
                            tasks.push(Task::Visit {
                                value: &tagged[1],
                                expected: Some(function),
                                side,
                                path: format!("{path}[1]"),
                            });
                        },
                        "^" => {
                            require_len(tagged, 3, &path)?;
                            let function = expected.ok_or_else(|| {
                                ValueDecodeError::new(
                                    &path,
                                    "abstraction needs an expected function sort",
                                )
                            })?;
                            let (domain, codomain) = match self.signature.sort(&function) {
                                Some(core::TheorySortV1 {
                                    kind: core::TheorySortKindV1::Function {
                                        domain,
                                        codomain,
                                        multiple: false,
                                    },
                                    ..
                                }) => (domain.clone(), codomain.clone()),
                                _ => return error(&path, format!("`{function}` is not a unary function sort")),
                            };
                            let name = expect_nonempty_string(&tagged[1], &format!("{path}[1]"))?;
                            let binder = match side {
                                Side::Left => self.add_or_constrain_input(
                                    name,
                                    &domain,
                                    core::TheoryVariableRoleV1::Binder,
                                    &format!("{path}[1]"),
                                )?,
                                Side::Right => self.require_variable(
                                    name,
                                    &domain,
                                    &format!("{path}[1]"),
                                )?,
                            };
                            tasks.push(Task::FinishAbstraction { binder, sort: function });
                            tasks.push(Task::Visit {
                                value: &tagged[2],
                                expected: Some(codomain),
                                side,
                                path: format!("{path}[2]"),
                            });
                        },
                        "coll" | "coll_typed" => {
                            let (elements_index, remainder_index, explicit_element) =
                                if tag == "coll" {
                                    require_len(tagged, 3, &path)?;
                                    (1, 2, None)
                                } else {
                                    require_len(tagged, 4, &path)?;
                                    (
                                        2,
                                        3,
                                        Some(expect_nonempty_string(
                                            &tagged[1],
                                            &format!("{path}[1]"),
                                        )?),
                                    )
                                };
                            let sort = match expected {
                                Some(sort) => sort,
                                None => self.unique_collection_sort(explicit_element, &path)?,
                            };
                            let element_sort = match self.signature.sort(&sort) {
                                Some(core::TheorySortV1 {
                                    kind: core::TheorySortKindV1::Collection { element, .. },
                                    ..
                                }) => element.clone(),
                                _ => return error(&path, format!("`{sort}` is not a collection sort")),
                            };
                            if explicit_element.is_some_and(|explicit| explicit != element_sort) {
                                return error(
                                    &path,
                                    format!("collection element sort is `{element_sort}`"),
                                );
                            }
                            let elements = expect_list(&tagged[elements_index], &format!("{path}[{elements_index}]"))?;
                            let remainder = match &tagged[remainder_index] {
                                RhoValue::Nil => None,
                                RhoValue::String(name) => Some(match side {
                                    Side::Left => self.add_or_constrain_input(
                                        name,
                                        &sort,
                                        core::TheoryVariableRoleV1::Remainder,
                                        &format!("{path}[{remainder_index}]"),
                                    )?,
                                    Side::Right => self.require_variable(
                                        name,
                                        &sort,
                                        &format!("{path}[{remainder_index}]"),
                                    )?,
                                }),
                                _ => return error(
                                    format!("{path}[{remainder_index}]"),
                                    "collection remainder must be a variable or Nil",
                                ),
                            };
                            tasks.push(Task::FinishCollection {
                                sort,
                                count: elements.len(),
                                remainder,
                            });
                            for (index, element) in elements.iter().enumerate().rev() {
                                tasks.push(Task::Visit {
                                    value: element,
                                    expected: Some(element_sort.clone()),
                                    side,
                                    path: format!("{path}[{elements_index}][{index}]"),
                                });
                            }
                        },
                        "lit" => {
                            require_len(tagged, 3, &path)?;
                            let declared = theory_literal_carrier(
                                &crate::schema::decode_carrier(
                                    &tagged[1],
                                    &format!("{path}[1]"),
                                )?,
                            )
                            .ok_or_else(|| {
                                ValueDecodeError::new(
                                    format!("{path}[1]"),
                                    "literal pattern requires a scalar carrier",
                                )
                            })?;
                            let literal = scalar_literal(&tagged[2], &format!("{path}[2]"))?;
                            let actual = literal_carrier(&literal);
                            if &declared != actual {
                                return error(
                                    format!("{path}[2]"),
                                    format!(
                                        "literal value has carrier `{actual:?}`, declared `{declared:?}`"
                                    ),
                                );
                            }
                            let sort = match expected {
                                Some(sort) => {
                                    let accepted = self.signature.sort(&sort).is_some_and(|sort| {
                                        matches!(
                                            &sort.kind,
                                            core::TheorySortKindV1::Syntax { literal: Some(carrier) }
                                                if carrier == &declared
                                        )
                                    });
                                    if !accepted {
                                        return error(
                                            &path,
                                            format!(
                                                "sort `{sort}` does not admit the `{declared:?}` literal carrier"
                                            ),
                                        );
                                    }
                                    sort
                                },
                                None => self.signature.unique_literal_sort(&literal, &path)?,
                            };
                            values.push(self.push_term(
                                sort,
                                core::TheoryTermFormV1::Literal(literal),
                                &path,
                            )?);
                        },
                        "pmap" | "pzip" | "^*" => {
                            return error(
                                &path,
                                format!(
                                    "metasyntax `{tag}` is outside the executable Greg/Mike RuleAstV1 surface"
                                ),
                            )
                        },
                        constructor => {
                            let declaration = self.signature.constructors.get(constructor).ok_or_else(|| {
                                ValueDecodeError::new(
                                    &path,
                                    format!("unknown constructor `{constructor}`"),
                                )
                            })?;
                            if tagged.len() - 1 != declaration.domain.len() {
                                return error(
                                    &path,
                                    format!(
                                        "constructor `{constructor}` expects {} arguments, found {}",
                                        declaration.domain.len(),
                                        tagged.len() - 1
                                    ),
                                );
                            }
                            if expected.as_ref().is_some_and(|sort| sort != &declaration.codomain) {
                                return error(
                                    &path,
                                    format!(
                                        "constructor `{constructor}` returns `{}`, expected `{}`",
                                        declaration.codomain,
                                        expected.as_deref().unwrap_or_default()
                                    ),
                                );
                            }
                            tasks.push(Task::FinishConstructor {
                                name: constructor.to_string(),
                                sort: declaration.codomain.clone(),
                                arity: declaration.domain.len(),
                            });
                            for (index, (argument, sort)) in tagged[1..]
                                .iter()
                                .zip(&declaration.domain)
                                .enumerate()
                                .rev()
                            {
                                tasks.push(Task::Visit {
                                    value: argument,
                                    expected: Some(sort.clone()),
                                    side,
                                    path: format!("{path}[{}]", index + 1),
                                });
                            }
                        },
                    }
                },
                Task::FinishConstructor { name, sort, arity } => {
                    let start = values.len().checked_sub(arity).ok_or_else(|| {
                        ValueDecodeError::new(path, "constructor result stack underflow")
                    })?;
                    let arguments = values.drain(start..).collect();
                    values.push(self.push_term(
                        sort,
                        core::TheoryTermFormV1::Constructor { constructor: name, arguments },
                        path,
                    )?);
                },
                Task::FinishAbstraction { binder, sort } => {
                    let body = values.pop().ok_or_else(|| {
                        ValueDecodeError::new(path, "abstraction result stack underflow")
                    })?;
                    values.push(self.push_term(
                        sort,
                        core::TheoryTermFormV1::Abstraction { binder, body },
                        path,
                    )?);
                },
                Task::FinishSubstitution { sort } => {
                    let argument = values.pop().ok_or_else(|| {
                        ValueDecodeError::new(path, "substitution argument stack underflow")
                    })?;
                    let abstraction = values.pop().ok_or_else(|| {
                        ValueDecodeError::new(path, "substitution abstraction stack underflow")
                    })?;
                    values.push(self.push_term(
                        sort,
                        core::TheoryTermFormV1::Substitution { abstraction, argument },
                        path,
                    )?);
                },
                Task::FinishCollection { sort, count, remainder } => {
                    let start = values.len().checked_sub(count).ok_or_else(|| {
                        ValueDecodeError::new(path, "collection result stack underflow")
                    })?;
                    let elements = values.drain(start..).collect();
                    values.push(self.push_term(
                        sort,
                        core::TheoryTermFormV1::Collection { elements, remainder },
                        path,
                    )?);
                },
            }
        }
        if values.len() != 1 {
            return error(path, "pattern compiler did not produce exactly one root");
        }
        Ok(values.pop().expect("checked one pattern root"))
    }

    fn compile_premises(
        &mut self,
        value: Option<&RhoValue>,
        allow_transition: bool,
        path: &str,
    ) -> Result<(), ValueDecodeError> {
        let Some(value) = value else { return Ok(()) };
        for (index, premise) in expect_list(value, path)?.iter().enumerate() {
            let root =
                self.compile_premise(premise, allow_transition, &format!("{path}[{index}]"))?;
            self.premise_roots.push(root);
        }
        Ok(())
    }

    fn compile_premise(
        &mut self,
        value: &RhoValue,
        allow_transition: bool,
        path: &str,
    ) -> Result<core::TheoryPremiseId, ValueDecodeError> {
        enum Task<'a> {
            Visit(&'a RhoValue, String),
            FinishForAll {
                collection: core::TheoryVariableId,
                parameter: core::TheoryVariableId,
                scope_start: usize,
            },
        }
        let mut tasks = vec![Task::Visit(value, path.to_string())];
        let mut values = Vec::new();
        while let Some(task) = tasks.pop() {
            let form = match task {
                Task::Visit(value, path) => {
                    let tagged = expect_list(value, &path)?;
                    let tag = tagged
                        .first()
                        .ok_or_else(|| ValueDecodeError::new(&path, "empty premise"))?;
                    match expect_nonempty_string(tag, &format!("{path}[0]"))? {
                        tag @ ("fresh" | "fresh_rest") => {
                            require_len(tagged, 3, &path)?;
                            let variable =
                                self.require_named_variable(&tagged[1], &format!("{path}[1]"))?;
                            let target =
                                self.require_named_variable(&tagged[2], &format!("{path}[2]"))?;
                            core::TheoryPremiseFormV1::Freshness {
                                variable,
                                target,
                                remainder: tag == "fresh_rest",
                            }
                        },
                        "~>" => {
                            if !allow_transition {
                                return error(
                                    &path,
                                    "transition premises are not admissible in equations",
                                );
                            }
                            require_len(tagged, 3, &path)?;
                            let source_name =
                                expect_nonempty_string(&tagged[1], &format!("{path}[1]"))?;
                            let target_name =
                                expect_nonempty_string(&tagged[2], &format!("{path}[2]"))?;
                            let source =
                                self.variable_ids.get(source_name).copied().ok_or_else(|| {
                                    ValueDecodeError::new(
                                        format!("{path}[1]"),
                                        format!(
                                            "transition source `{source_name}` is not available"
                                        ),
                                    )
                                })?;
                            if self.variable_ids.contains_key(target_name) {
                                return error(
                                    format!("{path}[2]"),
                                    format!("transition target `{target_name}` is already bound"),
                                );
                            }
                            let sort = self.variables[source.0 as usize].sort.clone();
                            let target = self.add_variable(
                                target_name,
                                &sort,
                                core::TheoryVariableRoleV1::Derived,
                                &format!("{path}[2]"),
                            )?;
                            core::TheoryPremiseFormV1::Transition { source, target }
                        },
                        "rel" => {
                            require_len(tagged, 3, &path)?;
                            let judgment =
                                expect_nonempty_string(&tagged[1], &format!("{path}[1]"))?
                                    .to_string();
                            let arguments = expect_list(&tagged[2], &format!("{path}[2]"))?;
                            let expected =
                                self.signature.judgments.get(&judgment).ok_or_else(|| {
                                    ValueDecodeError::new(
                                        format!("{path}[1]"),
                                        format!("unknown judgment `{judgment}`"),
                                    )
                                })?;
                            if arguments.len() != expected.len() {
                                return error(
                                    &path,
                                    format!(
                                        "judgment `{judgment}` expects {} arguments",
                                        expected.len()
                                    ),
                                );
                            }
                            let mut terms = Vec::new();
                            for (index, (argument, sort)) in
                                arguments.iter().zip(expected).enumerate()
                            {
                                let name = expect_nonempty_string(
                                    argument,
                                    &format!("{path}[2][{index}]"),
                                )?;
                                let variable = self.require_variable(
                                    name,
                                    sort,
                                    &format!("{path}[2][{index}]"),
                                )?;
                                terms.push(self.push_term(
                                    sort.clone(),
                                    core::TheoryTermFormV1::Variable(variable),
                                    &path,
                                )?);
                            }
                            core::TheoryPremiseFormV1::Judgment(core::JudgmentAtomV1 {
                                judgment,
                                terms,
                            })
                        },
                        "forall" => {
                            require_len(tagged, 4, &path)?;
                            let collection_name =
                                expect_nonempty_string(&tagged[1], &format!("{path}[1]"))?;
                            let collection = self
                                .variable_ids
                                .get(collection_name)
                                .copied()
                                .ok_or_else(|| {
                                    ValueDecodeError::new(
                                        format!("{path}[1]"),
                                        format!("unknown collection variable `{collection_name}`"),
                                    )
                                })?;
                            let collection_sort =
                                self.variables[collection.0 as usize].sort.clone();
                            let element_sort = match self.signature.sort(&collection_sort) {
                                Some(core::TheorySortV1 {
                                    kind: core::TheorySortKindV1::Collection { element, .. },
                                    ..
                                }) => element.clone(),
                                _ => {
                                    return error(
                                        format!("{path}[1]"),
                                        format!("`{collection_name}` is not collection-sorted"),
                                    )
                                },
                            };
                            let parameter_name =
                                expect_nonempty_string(&tagged[2], &format!("{path}[2]"))?;
                            if self.variable_ids.contains_key(parameter_name) {
                                return error(
                                    format!("{path}[2]"),
                                    format!("quantified variable `{parameter_name}` shadows an existing variable"),
                                );
                            }
                            let scope_start = self.variables.len();
                            let parameter = self.add_variable(
                                parameter_name,
                                &element_sort,
                                core::TheoryVariableRoleV1::Quantified,
                                &format!("{path}[2]"),
                            )?;
                            tasks.push(Task::FinishForAll { collection, parameter, scope_start });
                            tasks.push(Task::Visit(&tagged[3], format!("{path}[3]")));
                            continue;
                        },
                        "guard" => {
                            require_len(tagged, 2, &path)?;
                            core::TheoryPremiseFormV1::Guard(crate::schema::to_core_value(
                                &tagged[1],
                            ))
                        },
                        tag => return error(&path, format!("unknown premise tag `{tag}`")),
                    }
                },
                Task::FinishForAll { collection, parameter, scope_start } => {
                    let body = values.pop().ok_or_else(|| {
                        ValueDecodeError::new(path, "forall premise result stack underflow")
                    })?;
                    for variable in self.variables.get(scope_start..).unwrap_or_default() {
                        if self.variable_ids.get(&variable.name) == Some(&variable.id) {
                            self.variable_ids.remove(&variable.name);
                        }
                    }
                    if self.variables.get(parameter.0 as usize).is_none() {
                        return error(
                            path,
                            "forall premise parameter was not retained in its arena",
                        );
                    }
                    core::TheoryPremiseFormV1::ForAll { collection, parameter, body }
                },
            };
            if self.premises.len() >= self.limits.max_premise_nodes as usize {
                return error(path, "premise-node limit exceeded");
            }
            let id = core::TheoryPremiseId(self.premises.len() as u32);
            self.premises.push(core::TheoryPremiseNodeV1 { form });
            values.push(id);
        }
        if values.len() != 1 {
            return error(path, "premise compiler did not produce exactly one root");
        }
        Ok(values.pop().expect("checked one premise root"))
    }

    fn infer_root_sort(&self, value: &RhoValue, path: &str) -> Result<String, ValueDecodeError> {
        match value {
            RhoValue::String(name) => self
                .variable_ids
                .get(name)
                .and_then(|id| self.variables.get(id.0 as usize))
                .map(|variable| variable.sort.clone())
                .ok_or_else(|| {
                    ValueDecodeError::new(path, format!("cannot infer sort of `{name}`"))
                }),
            RhoValue::List(values) => {
                let tag = values
                    .first()
                    .ok_or_else(|| ValueDecodeError::new(path, "empty pattern node"))?;
                let tag = expect_nonempty_string(tag, &format!("{path}[0]"))?;
                if tag == "lit" {
                    require_len(values, 3, path)?;
                    return self.signature.unique_literal_sort(
                        &scalar_literal(&values[2], &format!("{path}[2]"))?,
                        path,
                    );
                }
                self.signature
                    .constructors
                    .get(tag)
                    .map(|constructor| constructor.codomain.clone())
                    .ok_or_else(|| {
                        ValueDecodeError::new(path, format!("cannot infer root sort of `{tag}`"))
                    })
            },
            _ => error(path, "pattern must be a variable or tagged list"),
        }
    }

    fn unique_collection_sort(
        &self,
        explicit_element: Option<&str>,
        path: &str,
    ) -> Result<String, ValueDecodeError> {
        let mut matches = self.signature.sorts.iter().filter(|sort| {
            matches!(
                &sort.kind,
                core::TheorySortKindV1::Collection { element, .. }
                    if explicit_element.is_none_or(|expected| expected == element)
            )
        });
        let Some(first) = matches.next() else {
            return error(path, "no matching collection sort is declared");
        };
        if matches.next().is_some() {
            return error(
                path,
                "collection sort is ambiguous; an enclosing constructor must determine it",
            );
        }
        Ok(first.name.clone())
    }

    fn add_or_constrain_input(
        &mut self,
        name: &str,
        sort: &str,
        role: core::TheoryVariableRoleV1,
        path: &str,
    ) -> Result<core::TheoryVariableId, ValueDecodeError> {
        if let Some(id) = self.variable_ids.get(name).copied() {
            let variable = &mut self.variables[id.0 as usize];
            if variable.sort != sort {
                return error(
                    path,
                    format!("variable `{name}` has sort `{}`, expected `{sort}`", variable.sort),
                );
            }
            if variable.role == core::TheoryVariableRoleV1::Input {
                variable.role = role;
            } else if variable.role != role {
                return error(path, format!("variable `{name}` has incompatible rule roles"));
            }
            Ok(id)
        } else {
            self.add_variable(name, sort, role, path)
        }
    }

    fn add_variable(
        &mut self,
        name: &str,
        sort: &str,
        role: core::TheoryVariableRoleV1,
        path: &str,
    ) -> Result<core::TheoryVariableId, ValueDecodeError> {
        if self.variables.len() >= self.limits.max_rule_variables as usize {
            return error(path, "rule-variable limit exceeded");
        }
        if !self.variable_names.insert(name.to_string()) {
            return error(path, format!("duplicate variable `{name}`"));
        }
        if self.signature.sort(sort).is_none() {
            return error(path, format!("unknown theory sort `{sort}`"));
        }
        let id = core::TheoryVariableId(self.variables.len() as u32);
        self.variable_ids.insert(name.to_string(), id);
        self.variables.push(core::TheoryVariableV1 {
            id,
            name: name.to_string(),
            sort: sort.to_string(),
            role,
        });
        Ok(id)
    }

    fn require_variable(
        &self,
        name: &str,
        sort: &str,
        path: &str,
    ) -> Result<core::TheoryVariableId, ValueDecodeError> {
        let id = self.variable_ids.get(name).copied().ok_or_else(|| {
            ValueDecodeError::new(path, format!("unbound right-side variable `{name}`"))
        })?;
        let variable = &self.variables[id.0 as usize];
        if variable.sort != sort {
            return error(
                path,
                format!("variable `{name}` has sort `{}`, expected `{sort}`", variable.sort),
            );
        }
        Ok(id)
    }

    fn require_named_variable(
        &self,
        value: &RhoValue,
        path: &str,
    ) -> Result<core::TheoryVariableId, ValueDecodeError> {
        let name = expect_nonempty_string(value, path)?;
        self.variable_ids
            .get(name)
            .copied()
            .ok_or_else(|| ValueDecodeError::new(path, format!("unknown rule variable `{name}`")))
    }

    fn push_term(
        &mut self,
        sort: String,
        form: core::TheoryTermFormV1,
        path: &str,
    ) -> Result<core::TheoryTermId, ValueDecodeError> {
        if self.terms.len() >= self.limits.max_term_nodes as usize {
            return error(path, "term-node limit exceeded");
        }
        let id = core::TheoryTermId(self.terms.len() as u32);
        self.terms.push(core::TheoryTermNodeV1 { sort, form });
        Ok(id)
    }

    fn term_sort(&self, term: core::TheoryTermId) -> Result<&str, ValueDecodeError> {
        self.terms
            .get(term.0 as usize)
            .map(|term| term.sort.as_str())
            .ok_or_else(|| ValueDecodeError::new(&self.rule, "compiled term root is missing"))
    }
}

fn decode_context_sort(value: &RhoValue, path: &str) -> Result<String, ValueDecodeError> {
    enum Task<'a> {
        Visit(&'a RhoValue, String),
        FinishUnary(&'static str),
        FinishBinary(&'static str),
        FinishArrow,
    }
    let mut tasks = vec![Task::Visit(value, path.to_string())];
    let mut values = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            Task::Visit(RhoValue::String(name), _) => values.push(name.clone()),
            Task::Visit(value, path) => {
                let tagged = expect_list(value, &path)?;
                let tag = tagged
                    .first()
                    .ok_or_else(|| ValueDecodeError::new(&path, "empty sort"))?;
                match expect_nonempty_string(tag, &format!("{path}[0]"))? {
                    "arrow" => {
                        require_len(tagged, 3, &path)?;
                        tasks.push(Task::FinishArrow);
                        tasks.push(Task::Visit(&tagged[2], format!("{path}[2]")));
                        tasks.push(Task::Visit(&tagged[1], format!("{path}[1]")));
                    },
                    tag @ ("bag" | "set" | "vec") => {
                        require_len(tagged, 2, &path)?;
                        let name = match tag {
                            "bag" => "HashBag",
                            "set" => "Set",
                            _ => "List",
                        };
                        tasks.push(Task::FinishUnary(name));
                        tasks.push(Task::Visit(&tagged[1], format!("{path}[1]")));
                    },
                    tag @ ("map" | "pathmap") => {
                        require_len(tagged, 3, &path)?;
                        let name = if tag == "map" { "Map" } else { "PathMap" };
                        tasks.push(Task::FinishBinary(name));
                        tasks.push(Task::Visit(&tagged[2], format!("{path}[2]")));
                        tasks.push(Task::Visit(&tagged[1], format!("{path}[1]")));
                    },
                    tag => return error(&path, format!("unknown type-expression tag `{tag}`")),
                }
            },
            Task::FinishUnary(name) => {
                let value = values.pop().expect("unary sort value is scheduled");
                values.push(format!("{name}({value})"));
            },
            Task::FinishBinary(name) => {
                let right = values.pop().expect("binary sort right value is scheduled");
                let left = values.pop().expect("binary sort left value is scheduled");
                values.push(format!("{name}({left},{right})"));
            },
            Task::FinishArrow => {
                let codomain = values.pop().expect("arrow codomain is scheduled");
                let domain = values.pop().expect("arrow domain is scheduled");
                values.push(format!("[{domain} -> {codomain}]"));
            },
        }
    }
    if values.len() != 1 {
        return error(path, "sort decoder did not produce exactly one value");
    }
    Ok(values.pop().expect("checked one sort value"))
}

fn scalar_literal(value: &RhoValue, path: &str) -> Result<core::TheoryLiteralV1, ValueDecodeError> {
    Ok(match value {
        RhoValue::String(value) => core::TheoryLiteralV1::String(value.clone()),
        RhoValue::Bytes(value) => core::TheoryLiteralV1::Bytes(value.clone()),
        RhoValue::Integer(value) => core::TheoryLiteralV1::Integer(*value),
        RhoValue::FloatBits(value) => core::TheoryLiteralV1::FloatBits(*value),
        RhoValue::Boolean(value) => core::TheoryLiteralV1::Boolean(*value),
        RhoValue::Nil => core::TheoryLiteralV1::Unit,
        _ => return error(path, "theory literal must be scalar"),
    })
}

fn literal_carrier(literal: &core::TheoryLiteralV1) -> &core::TheoryLiteralCarrierV1 {
    static STRING: core::TheoryLiteralCarrierV1 = core::TheoryLiteralCarrierV1::String;
    static BYTES: core::TheoryLiteralCarrierV1 = core::TheoryLiteralCarrierV1::Bytes;
    static INTEGER: core::TheoryLiteralCarrierV1 = core::TheoryLiteralCarrierV1::Integer;
    static FLOAT: core::TheoryLiteralCarrierV1 = core::TheoryLiteralCarrierV1::Float;
    static BOOLEAN: core::TheoryLiteralCarrierV1 = core::TheoryLiteralCarrierV1::Boolean;
    static UNIT: core::TheoryLiteralCarrierV1 = core::TheoryLiteralCarrierV1::Unit;
    match literal {
        core::TheoryLiteralV1::String(_) => &STRING,
        core::TheoryLiteralV1::Bytes(_) => &BYTES,
        core::TheoryLiteralV1::Integer(_) => &INTEGER,
        core::TheoryLiteralV1::FloatBits(_) => &FLOAT,
        core::TheoryLiteralV1::Boolean(_) => &BOOLEAN,
        core::TheoryLiteralV1::Unit => &UNIT,
    }
}

fn theory_literal_carrier(carrier: &core::Carrier) -> Option<core::TheoryLiteralCarrierV1> {
    Some(match carrier {
        core::Carrier::Dynamic | core::Carrier::Collection(_) => return None,
        core::Carrier::Builtin(core::BuiltinCarrier::Boolean) => {
            core::TheoryLiteralCarrierV1::Boolean
        },
        core::Carrier::Builtin(core::BuiltinCarrier::Integer) => {
            core::TheoryLiteralCarrierV1::Integer
        },
        core::Carrier::Builtin(core::BuiltinCarrier::Rational) => {
            core::TheoryLiteralCarrierV1::Rational
        },
        core::Carrier::Builtin(core::BuiltinCarrier::FixedPoint) => {
            core::TheoryLiteralCarrierV1::FixedPoint
        },
        core::Carrier::Builtin(core::BuiltinCarrier::Float) => core::TheoryLiteralCarrierV1::Float,
        core::Carrier::Builtin(core::BuiltinCarrier::String) => {
            core::TheoryLiteralCarrierV1::String
        },
        core::Carrier::Builtin(core::BuiltinCarrier::Bytes) => core::TheoryLiteralCarrierV1::Bytes,
        core::Carrier::Extern { urn } => core::TheoryLiteralCarrierV1::External(urn.clone()),
        core::Carrier::HostOpaque { stable_name } => {
            core::TheoryLiteralCarrierV1::HostOpaque(stable_name.clone())
        },
    })
}

fn expect_map<'a>(
    value: &'a RhoValue,
    path: &str,
) -> Result<&'a BTreeMap<String, RhoValue>, ValueDecodeError> {
    match value {
        RhoValue::Map(values) => Ok(values),
        _ => error(path, "expected map"),
    }
}

fn expect_list<'a>(value: &'a RhoValue, path: &str) -> Result<&'a [RhoValue], ValueDecodeError> {
    match value {
        RhoValue::List(values) => Ok(values),
        _ => error(path, "expected list"),
    }
}

fn expect_string<'a>(value: &'a RhoValue, path: &str) -> Result<&'a str, ValueDecodeError> {
    match value {
        RhoValue::String(value) => Ok(value),
        _ => error(path, "expected string"),
    }
}

fn expect_nonempty_string<'a>(
    value: &'a RhoValue,
    path: &str,
) -> Result<&'a str, ValueDecodeError> {
    let value = expect_string(value, path)?;
    if value.is_empty() {
        error(path, "expected non-empty string")
    } else {
        Ok(value)
    }
}

fn required<'a>(
    values: &'a BTreeMap<String, RhoValue>,
    key: &str,
    path: &str,
) -> Result<&'a RhoValue, ValueDecodeError> {
    values
        .get(key)
        .ok_or_else(|| ValueDecodeError::new(format!("{path}.{key}"), "missing required key"))
}

fn required_string<'a>(
    values: &'a BTreeMap<String, RhoValue>,
    key: &str,
    path: &str,
) -> Result<&'a str, ValueDecodeError> {
    expect_nonempty_string(required(values, key, path)?, &format!("{path}.{key}"))
}

fn require_len(values: &[RhoValue], expected: usize, path: &str) -> Result<(), ValueDecodeError> {
    if values.len() == expected {
        Ok(())
    } else {
        error(path, format!("expected {expected} items, found {}", values.len()))
    }
}

fn error<T>(path: impl Into<String>, message: impl Into<String>) -> Result<T, ValueDecodeError> {
    Err(ValueDecodeError::new(path, message))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn string(value: &str) -> RhoValue {
        RhoValue::String(value.to_string())
    }

    fn list(values: impl IntoIterator<Item = RhoValue>) -> RhoValue {
        RhoValue::List(values.into_iter().collect())
    }

    fn map(values: impl IntoIterator<Item = (&'static str, RhoValue)>) -> RhoValue {
        RhoValue::Map(
            values
                .into_iter()
                .map(|(name, value)| (name.to_string(), value))
                .collect(),
        )
    }

    fn theory() -> core::TheoryCoreV1 {
        let mut theory = core::TheoryCoreV1::structural();
        theory.profile = core::TheoryProfileV1::Oslf;
        theory.sorts = vec![
            core::TheorySortV1 {
                name: "Expr".into(),
                kind: core::TheorySortKindV1::Syntax { literal: None },
            },
            core::TheorySortV1 {
                name: "Int".into(),
                kind: core::TheorySortKindV1::Syntax {
                    literal: Some(core::TheoryLiteralCarrierV1::Integer),
                },
            },
            core::TheorySortV1 {
                name: "List(Expr)".into(),
                kind: core::TheorySortKindV1::Collection {
                    kind: core::CollectionKind::List,
                    key: None,
                    element: "Expr".into(),
                },
            },
        ];
        theory.constructors.push(core::TheoryConstructorV1 {
            name: "Wrap".into(),
            domain: vec!["Expr".into()],
            codomain: "Expr".into(),
        });
        theory.judgments.push(core::JudgmentDeclV1 {
            name: "Holds".into(),
            arguments: vec!["Expr".into()],
            decision: core::JudgmentDecisionV1::Bounded,
            rules: Vec::new(),
        });
        theory
    }

    #[test]
    fn surface_rules_compile_to_dense_typed_arenas_without_source_reparse() {
        let equation = map([
            ("name", string("WrapIdentity")),
            ("left", list([string("Wrap"), string("x")])),
            ("right", list([string("Wrap"), string("x")])),
        ]);
        let rewrite = map([
            ("name", string("Unwrap")),
            ("left", list([string("Wrap"), string("x")])),
            ("right", string("x")),
        ]);
        let mut theory = theory();
        compile_surface_rules(&[equation], &[rewrite], &mut theory).expect("rules compile");

        assert_eq!(theory.equations.len(), 1);
        assert_eq!(theory.rewrites.len(), 1);
        let arena = &theory.rewrites[0].arena;
        assert_eq!(arena.variables[0].id, core::TheoryVariableId(0));
        assert_eq!(arena.variables[0].sort, "Expr");
        assert!(matches!(
            arena.terms[theory.rewrites[0].left.0 as usize].form,
            core::TheoryTermFormV1::Constructor { ref constructor, .. }
                if constructor == "Wrap"
        ));
        assert!(matches!(
            arena.terms[theory.rewrites[0].right.0 as usize].form,
            core::TheoryTermFormV1::Variable(core::TheoryVariableId(0))
        ));
    }

    #[test]
    fn forall_parameters_are_lexical_and_cannot_escape_to_the_rhs() {
        let context =
            list([list([string("typed"), string("xs"), list([string("vec"), string("Expr")])])]);
        let premise = list([
            string("forall"),
            string("xs"),
            string("x"),
            list([string("rel"), string("Holds"), list([string("x")])]),
        ]);
        let good = map([
            ("name", string("EveryElement")),
            ("context", context.clone()),
            ("premises", list([premise.clone()])),
            ("left", string("xs")),
            ("right", string("xs")),
        ]);
        let mut compiled = theory();
        compile_surface_rules(&[], &[good], &mut compiled).expect("scoped premise compiles");
        let arena = &compiled.rewrites[0].arena;
        assert_eq!(arena.premises.len(), 2);
        assert!(matches!(
            arena.premises[1].form,
            core::TheoryPremiseFormV1::ForAll {
                collection: core::TheoryVariableId(0),
                parameter: core::TheoryVariableId(1),
                body: core::TheoryPremiseId(0),
            }
        ));

        let escaping = map([
            ("name", string("EscapingElement")),
            ("context", context),
            ("premises", list([premise])),
            ("left", string("xs")),
            ("right", string("x")),
        ]);
        let error = compile_surface_rules(&[], &[escaping], &mut theory())
            .expect_err("quantified variable cannot escape its premise");
        assert!(error.message.contains("unbound right-side variable `x`"), "{error:?}");

        let local_transition = list([
            string("forall"),
            string("xs"),
            string("x"),
            list([string("~>"), string("x"), string("y")]),
        ]);
        let derived_escape = map([
            ("name", string("EscapingDerivedElement")),
            (
                "context",
                list([list([
                    string("typed"),
                    string("xs"),
                    list([string("vec"), string("Expr")]),
                ])]),
            ),
            ("premises", list([local_transition])),
            ("left", string("xs")),
            ("right", string("y")),
        ]);
        let error = compile_surface_rules(&[], &[derived_escape], &mut theory())
            .expect_err("a transition target inside forall cannot escape its lexical body");
        assert!(error.message.contains("unbound right-side variable `y`"), "{error:?}");
    }

    #[test]
    fn literal_carriers_arity_and_rule_names_fail_closed() {
        let integer = list([string("lit"), string("i64"), RhoValue::Integer(7)]);
        let valid =
            map([("name", string("Seven")), ("left", integer.clone()), ("right", integer.clone())]);
        compile_surface_rules(std::slice::from_ref(&valid), &[], &mut theory())
            .expect("matching scalar carrier compiles");

        let mismatched_literal = map([
            ("name", string("BadCarrier")),
            ("left", list([string("lit"), string("bool"), RhoValue::Integer(7)])),
            ("right", integer),
        ]);
        let error = compile_surface_rules(&[mismatched_literal], &[], &mut theory())
            .expect_err("declared and actual literal carriers must agree");
        assert!(error.message.contains("declared `Boolean`"), "{error:?}");

        let bad_arity = map([
            ("name", string("BadArity")),
            ("left", list([string("Wrap")])),
            ("right", list([string("Wrap")])),
        ]);
        let error = compile_surface_rules(&[bad_arity], &[], &mut theory())
            .expect_err("constructor arity must be exact");
        assert!(error.message.contains("expects 1 arguments"), "{error:?}");

        let error = compile_surface_rules(&[valid.clone(), valid], &[], &mut theory())
            .expect_err("rule names must be unique within their namespace");
        assert!(error.message.contains("duplicate equation name"), "{error:?}");
    }
}
