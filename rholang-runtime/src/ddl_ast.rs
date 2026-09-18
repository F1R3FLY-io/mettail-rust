//! Structural wire lowering for the in-Rholang MeTTaIL DDL.
//!
//! The nouveau Rholang parser has already parsed every declaration into the
//! generated `Ddl*` categories before this module runs.  This module therefore
//! performs only a structural, post-order projection to an ordinary Rholang
//! value.  It never renders source and never invokes a parser.

use crate::rholang_ast::RholangAstLowerError;
use mettail_languages::rholang::{
    DdlBinding, DdlCatDecl, DdlEquation, DdlExport, DdlFreshness, DdlFreshnesses, DdlImport,
    DdlImports, DdlModuleItem, DdlParam, DdlPath, DdlPremise, DdlPremises, DdlReplacement,
    DdlRewrite, DdlRuleAst, DdlRuleAstItems, DdlRuleAstRemainderTail, DdlSort, DdlSyntaxItem,
    DdlTermRule, DdlTheoryExpr, Proc,
};
use models::rhoapi::Par;
use models::rust::utils::{new_elist_par, new_gstring_par};

mod admission;
type Reservation<'a> = dyn FnMut(usize, usize) -> Result<(), RholangAstLowerError> + 'a;

/// Versioned, closed AST envelope emitted by the Rholang lowering.
pub use mettail_elab::wire::DDL_AST_ENVELOPE_V2;

pub(crate) enum DdlRoot<'a> {
    Module {
        name: &'a str,
        imports: Option<&'a DdlImports>,
        items: &'a [DdlModuleItem],
    },
    Theory {
        name: &'a str,
        parameters: &'a [DdlParam],
        body: &'a DdlTheoryExpr,
    },
}

enum WireOp<'a> {
    Text(&'a str),
    QuotedText(&'a str),
    Process(usize),
    Node { tag: &'static str, child_count: usize },
}

/// A post-order DDL encoder plus the Rholang process leaves that the host
/// lowering machine must evaluate structurally before the plan can finish.
/// Keeping those leaves outside the wire walk makes arbitrarily alternating
/// `DDL -> Data(Proc) -> DDL` input use the host machine's heap stack rather
/// than the native call stack.
pub(crate) struct DdlLowerPlan<'a> {
    operations: Vec<WireOp<'a>>,
    processes: Vec<&'a Proc>,
}

impl<'a> DdlLowerPlan<'a> {
    pub(crate) fn build(root: DdlRoot<'a>) -> Self {
        Self::try_build(root, &mut |_, _| Ok(())).expect("unlimited DDL plan construction")
    }

    pub(crate) fn try_build(
        root: DdlRoot<'a>,
        reserve: &mut Reservation<'_>,
    ) -> Result<Self, RholangAstLowerError> {
        admission::rosters(4, 2, reserve)?;
        let root = match root {
            DdlRoot::Module { name, imports, items } => Task::Module { name, imports, items },
            DdlRoot::Theory { name, parameters, body } => Task::Theory { name, parameters, body },
        };
        let mut tasks = vec![Task::Node {
            tag: DDL_AST_ENVELOPE_V2,
            children: vec![root],
        }];
        let mut operations = Vec::new();
        let mut processes = Vec::new();

        loop {
            admission::parts(2, 0, 0, reserve)?;
            let Some(task) = tasks.pop() else {
                break;
            };
            admission::expansion(&task, reserve)?;
            let (pending, emitted, process_count) = match &task {
                Task::Text(_) | Task::QuotedText(_) | Task::FinishNode { .. } => (0, 1, 0),
                Task::Process(_) => (0, 1, 1),
                Task::Node { children, .. } => (
                    children
                        .len()
                        .checked_add(1)
                        .ok_or(RholangAstLowerError::PreparationSizeOverflow)?,
                    0,
                    0,
                ),
                _ => (1, 0, 0),
            };
            tasks
                .len()
                .checked_add(pending)
                .ok_or(RholangAstLowerError::PreparationSizeOverflow)?;
            operations
                .len()
                .checked_add(emitted)
                .ok_or(RholangAstLowerError::PreparationSizeOverflow)?;
            processes
                .len()
                .checked_add(process_count)
                .ok_or(RholangAstLowerError::PreparationSizeOverflow)?;
            match task {
                Task::Text(value) => operations.push(WireOp::Text(value)),
                Task::QuotedText(value) => operations.push(WireOp::QuotedText(value)),
                Task::Process(process) => {
                    let index = processes.len();
                    processes.push(process);
                    operations.push(WireOp::Process(index));
                },
                Task::Node { tag, children } => {
                    let child_count = children.len();
                    tasks.push(Task::FinishNode { tag, child_count });
                    tasks.extend(children.into_iter().rev());
                },
                Task::FinishNode { tag, child_count } => {
                    operations.push(WireOp::Node { tag, child_count });
                },
                Task::Module { name, imports, items } => {
                    let items = items
                        .iter()
                        .map(|item| match item {
                            DdlModuleItem::DdlModuleTheoryItem(expression) => Task::Node {
                                tag: "module-theory-entry",
                                children: vec![Task::TheoryExpr(expression.as_ref())],
                            },
                            DdlModuleItem::DdlModuleProcItem(process) => match process.as_ref() {
                                Proc::DdlTheory(name, parameters, body) => Task::Node {
                                    tag: "module-theory-declaration",
                                    children: vec![Task::Theory {
                                        name,
                                        parameters,
                                        body: body.as_ref(),
                                    }],
                                },
                                process => Task::Node {
                                    tag: "module-program",
                                    children: vec![Task::Process(process)],
                                },
                            },
                        })
                        .collect();
                    let imports = imports.map(import_tasks).unwrap_or_default();
                    tasks.push(Task::Node {
                        tag: "module",
                        children: vec![Task::Text(name), sequence(imports), sequence(items)],
                    });
                },
                Task::Theory { name, parameters, body } => {
                    tasks.push(Task::Node {
                        tag: "theory",
                        children: vec![
                            Task::Text(name),
                            sequence(parameters.iter().map(Task::Param).collect()),
                            Task::TheoryExpr(body),
                        ],
                    });
                },
                Task::Param(parameter) => match parameter {
                    DdlParam::DdlParamDecl(name, path) => tasks.push(Task::Node {
                        tag: "param",
                        children: vec![Task::Text(name), Task::Path(path.as_ref())],
                    }),
                },
                Task::Path(path) => match path {
                    DdlPath::DdlPathQualified(head, tail) => tasks.push(Task::Node {
                        tag: "path-qualified",
                        children: vec![Task::Text(head), Task::Path(tail.as_ref())],
                    }),
                    DdlPath::DdlPathName(name) => tasks.push(Task::Node {
                        tag: "path-name",
                        children: vec![Task::Text(name)],
                    }),
                },
                Task::TheoryExpr(expression) => {
                    let node = theory_expression_task(expression);
                    tasks.push(node);
                },
                Task::CatDecl(declaration) => match declaration {
                    DdlCatDecl::DdlCategory(category) => tasks.push(Task::Node {
                        tag: "category",
                        children: vec![Task::Text(category)],
                    }),
                },
                Task::Export(export) => match export {
                    DdlExport::DdlExportDirect(category) => tasks.push(Task::Node {
                        tag: "export",
                        children: vec![Task::Text(category), none()],
                    }),
                    DdlExport::DdlExportRename(category, replacement) => {
                        tasks.push(Task::Node {
                            tag: "export",
                            children: vec![Task::Text(category), some(Task::Text(replacement))],
                        });
                    },
                },
                Task::Replacement(replacement) => match replacement {
                    DdlReplacement::DdlReplacementRule(target, rule) => tasks.push(Task::Node {
                        tag: "replacement",
                        children: vec![Task::Text(target), Task::TermRule(rule.as_ref())],
                    }),
                },
                Task::TermRule(rule) => match rule {
                    DdlTermRule::DdlTerm(label, bindings, syntax, result) => {
                        tasks.push(Task::Node {
                            tag: "term",
                            children: vec![
                                Task::Text(label),
                                sequence(bindings.iter().map(Task::Binding).collect()),
                                sequence(syntax.iter().map(Task::SyntaxItem).collect()),
                                Task::Text(result),
                            ],
                        });
                    },
                },
                Task::Binding(binding) => match binding {
                    DdlBinding::DdlBindingPlain(name, sort) => tasks.push(Task::Node {
                        tag: "binding",
                        children: vec![Task::Text(name), Task::Sort(sort.as_ref())],
                    }),
                    DdlBinding::DdlBindingBinder(binder, body, from, to) => {
                        tasks.push(Task::Node {
                            tag: "binder",
                            children: vec![
                                Task::Text(binder),
                                Task::Text(body),
                                Task::Text(from),
                                Task::Text(to),
                            ],
                        });
                    },
                },
                Task::Sort(sort) => {
                    let (tag, category) = match sort {
                        DdlSort::DdlSortHashBag(category) => ("sort-bag", category),
                        DdlSort::DdlSortSet(category) => ("sort-set", category),
                        DdlSort::DdlSortList(category) => ("sort-list", category),
                        DdlSort::DdlSortCategory(category) => ("sort-category", category),
                    };
                    tasks.push(Task::Node {
                        tag,
                        children: vec![Task::Text(category)],
                    });
                },
                Task::SyntaxItem(item) => match item {
                    DdlSyntaxItem::DdlSyntaxProjection(argument, separator) => {
                        tasks.push(Task::Node {
                            tag: "syntax-projection",
                            children: vec![Task::Text(argument), Task::QuotedText(separator)],
                        });
                    },
                    DdlSyntaxItem::DdlSyntaxTerminal(terminal) => tasks.push(Task::Node {
                        tag: "syntax-terminal",
                        children: vec![Task::QuotedText(terminal)],
                    }),
                    DdlSyntaxItem::DdlSyntaxArgument(argument) => tasks.push(Task::Node {
                        tag: "syntax-argument",
                        children: vec![Task::Text(argument)],
                    }),
                },
                Task::Equation(equation) => match equation {
                    DdlEquation::DdlEquationDirect(left, right) => tasks.push(Task::Node {
                        tag: "equation",
                        children: vec![
                            sequence(Vec::new()),
                            Task::RuleAst(left.as_ref()),
                            Task::RuleAst(right.as_ref()),
                        ],
                    }),
                    DdlEquation::DdlEquationConditional(freshness, left, right) => {
                        tasks.push(Task::Node {
                            tag: "equation",
                            children: vec![
                                sequence(freshness_tasks(freshness.as_ref())),
                                Task::RuleAst(left.as_ref()),
                                Task::RuleAst(right.as_ref()),
                            ],
                        });
                    },
                },
                Task::Freshness(freshness) => match freshness {
                    DdlFreshness::DdlFreshness(left, right) => tasks.push(Task::Node {
                        tag: "freshness",
                        children: vec![Task::Text(left), Task::Text(right)],
                    }),
                },
                Task::Rewrite(rewrite) => match rewrite {
                    DdlRewrite::DdlRewriteDirect(name, left, right) => tasks.push(Task::Node {
                        tag: "rewrite",
                        children: vec![
                            Task::Text(name),
                            sequence(Vec::new()),
                            Task::RuleAst(left.as_ref()),
                            Task::RuleAst(right.as_ref()),
                        ],
                    }),
                    DdlRewrite::DdlRewriteConditional(name, premises, left, right) => {
                        tasks.push(Task::Node {
                            tag: "rewrite",
                            children: vec![
                                Task::Text(name),
                                sequence(premise_tasks(premises.as_ref())),
                                Task::RuleAst(left.as_ref()),
                                Task::RuleAst(right.as_ref()),
                            ],
                        });
                    },
                },
                Task::Premise(premise) => match premise {
                    DdlPremise::DdlPremise(left, right) => tasks.push(Task::Node {
                        tag: "premise",
                        children: vec![Task::Text(left), Task::Text(right)],
                    }),
                },
                Task::RuleAst(ast) => {
                    let node = rule_ast_task(ast);
                    tasks.push(node);
                },
            }
        }

        Ok(Self { operations, processes })
    }

    pub(crate) fn process_jobs(&self) -> impl ExactSizeIterator<Item = &'a Proc> + '_ {
        self.processes.iter().copied()
    }

    pub(crate) fn finish(self, process_values: Vec<Par>) -> Result<Par, String> {
        self.try_finish(process_values, &mut |_, _| Ok(()))
            .map_err(|error| match error {
                RholangAstLowerError::DdlWire(message) => message,
                other => format!("{other:?}"),
            })
    }

    pub(crate) fn try_finish(
        self,
        process_values: Vec<Par>,
        reserve: &mut Reservation<'_>,
    ) -> Result<Par, RholangAstLowerError> {
        admission::parts(2, 0, 0, reserve)?;
        if process_values.len() != self.processes.len() {
            admission::parts(8, 1, 128, reserve)?;
            return Err(RholangAstLowerError::DdlWire(format!(
                "DDL structural plan received {} process values; expected {}",
                process_values.len(),
                self.processes.len()
            )));
        }
        admission::rosters(2, process_values.len(), reserve)?;
        let mut process_values: Vec<Option<Par>> = process_values.into_iter().map(Some).collect();
        let mut values = Vec::new();
        admission::parts(3, 1, 0, reserve)?;
        for operation in self.operations {
            // Iterator advance, dispatch, one output slot and its normal cleanup.
            admission::parts(5, 1, 0, reserve)?;
            values
                .len()
                .checked_add(1)
                .ok_or(RholangAstLowerError::PreparationSizeOverflow)?;
            match operation {
                WireOp::Text(value) => {
                    admission::text(value.len(), false, reserve)?;
                    values.push(string_par(value.to_string()));
                },
                WireOp::QuotedText(value) => {
                    admission::text(value.len(), true, reserve)?;
                    values.push(string_par(
                        decode_captured_string(value).map_err(RholangAstLowerError::DdlWire)?,
                    ));
                },
                WireOp::Process(index) => {
                    let value = process_values.get_mut(index).and_then(Option::take);
                    match value {
                        Some(value) => values.push(value),
                        None => {
                            let message =
                                "DDL structural plan has an absent or repeated process slot";
                            admission::parts(1, 1, message.len(), reserve)?;
                            return Err(RholangAstLowerError::DdlWire(message.into()));
                        },
                    }
                },
                WireOp::Node { tag, child_count } => {
                    let Some(start) = values.len().checked_sub(child_count) else {
                        admission::parts(8, 1, 128, reserve)?;
                        return Err(RholangAstLowerError::DdlWire(format!(
                            "DDL structural plan underflow while assembling `{tag}`"
                        )));
                    };
                    admission::node(child_count, tag.len(), reserve)?;
                    let mut children = values.split_off(start);
                    children.insert(0, string_par(tag.to_string()));
                    values.push(new_elist_par(
                        children,
                        Vec::new(),
                        false,
                        None,
                        Vec::new(),
                        false,
                    ));
                },
            }
        }
        admission::parts(3, 0, 0, reserve)?;
        let mut unused = process_values.iter();
        loop {
            admission::parts(1, 0, 0, reserve)?;
            let Some(slot) = unused.next() else {
                break;
            };
            if slot.is_some() {
                let message = "DDL structural plan left an embedded process slot unused";
                admission::parts(1, 1, message.len(), reserve)?;
                return Err(RholangAstLowerError::DdlWire(message.into()));
            }
        }
        if values.len() != 1 {
            admission::parts(8, 1, 128, reserve)?;
            return Err(RholangAstLowerError::DdlWire(format!(
                "DDL structural plan produced {} root values; expected one",
                values.len()
            )));
        }
        Ok(values.pop().expect("checked one DDL structural root"))
    }
}

fn string_par(value: String) -> Par {
    new_gstring_par(value, Vec::new(), false)
}

fn decode_captured_string(raw: &str) -> Result<String, String> {
    mettail_elab::lex::decode_rholang_string_literal(raw)
}

fn sequence<'a>(children: Vec<Task<'a>>) -> Task<'a> {
    Task::Node { tag: "sequence", children }
}

fn none<'a>() -> Task<'a> {
    Task::Node { tag: "none", children: Vec::new() }
}

fn some<'a>(value: Task<'a>) -> Task<'a> {
    Task::Node { tag: "some", children: vec![value] }
}

fn import_tasks<'a>(imports: &'a DdlImports) -> Vec<Task<'a>> {
    match imports {
        DdlImports::DdlImportsNonEmpty(head, tail) => std::iter::once(head.as_ref())
            .chain(tail.iter())
            .map(|import| match import {
                DdlImport::DdlImportModuleAs(url, alias) => Task::Node {
                    tag: "import-module-as",
                    children: vec![Task::QuotedText(url), Task::Text(alias)],
                },
                DdlImport::DdlImportFromModule(name, url) => Task::Node {
                    tag: "import-from-module",
                    children: vec![Task::Text(name), Task::QuotedText(url)],
                },
            })
            .collect(),
    }
}

fn theory_expression_task<'a>(expression: &'a DdlTheoryExpr) -> Task<'a> {
    use DdlTheoryExpr::*;
    match expression {
        DdlTheoryDiff(left, right) => binary("difference", left, right),
        DdlTheoryJoin(left, right) => binary("join", left, right),
        DdlTheoryMeet(left, right) => binary("meet", left, right),
        DdlTheoryTypes(base, entries) => {
            build(base, "types", entries.iter().map(Task::CatDecl).collect())
        },
        DdlTheoryExports(base, entries) => {
            build(base, "exports", entries.iter().map(Task::Export).collect())
        },
        DdlTheoryReplacements(base, entries) => {
            build(base, "replacements", entries.iter().map(Task::Replacement).collect())
        },
        DdlTheoryTerms(base, entries) => {
            build(base, "terms", entries.iter().map(Task::TermRule).collect())
        },
        DdlTheoryEquations(base, entries) => {
            build(base, "equations", entries.iter().map(Task::Equation).collect())
        },
        DdlTheoryRewrites(base, entries) => {
            build(base, "rewrites", entries.iter().map(Task::Rewrite).collect())
        },
        DdlTheoryData(base, value) => Task::Node {
            tag: "build",
            children: vec![
                Task::TheoryExpr(base.as_ref()),
                Task::Node {
                    tag: "data",
                    children: vec![Task::Process(value.as_ref())],
                },
            ],
        },
        DdlTheoryEmpty => Task::Node { tag: "empty", children: Vec::new() },
        DdlTheoryFree(path) => Task::Node {
            tag: "free",
            children: vec![Task::Path(path.as_ref())],
        },
        DdlTheoryLet(name, bound, body) => Task::Node {
            tag: "let",
            children: vec![
                Task::Text(name),
                Task::TheoryExpr(bound.as_ref()),
                Task::TheoryExpr(body.as_ref()),
            ],
        },
        DdlTheoryBraceGroup(body) | DdlTheoryParenGroup(body) => Task::TheoryExpr(body.as_ref()),
        DdlTheoryApply(path, arguments) => Task::Node {
            tag: "apply",
            children: vec![
                Task::Path(path.as_ref()),
                sequence(arguments.iter().map(Task::TheoryExpr).collect()),
            ],
        },
        DdlTheoryRef(path) => Task::Node {
            tag: "apply",
            children: vec![Task::Path(path.as_ref()), sequence(Vec::new())],
        },
        DdlTheoryTypesImplicit(entries) => {
            implicit_build("types", entries.iter().map(Task::CatDecl).collect())
        },
        DdlTheoryExportsImplicit(entries) => {
            implicit_build("exports", entries.iter().map(Task::Export).collect())
        },
        DdlTheoryReplacementsImplicit(entries) => {
            implicit_build("replacements", entries.iter().map(Task::Replacement).collect())
        },
        DdlTheoryTermsImplicit(entries) => {
            implicit_build("terms", entries.iter().map(Task::TermRule).collect())
        },
        DdlTheoryEquationsImplicit(entries) => {
            implicit_build("equations", entries.iter().map(Task::Equation).collect())
        },
        DdlTheoryRewritesImplicit(entries) => {
            implicit_build("rewrites", entries.iter().map(Task::Rewrite).collect())
        },
        DdlTheoryDataImplicit(value) => Task::Node {
            tag: "build",
            children: vec![
                Task::Node { tag: "empty", children: Vec::new() },
                Task::Node {
                    tag: "data",
                    children: vec![Task::Process(value.as_ref())],
                },
            ],
        },
    }
}

fn binary<'a>(
    tag: &'static str,
    left: &'a std::sync::Arc<DdlTheoryExpr>,
    right: &'a std::sync::Arc<DdlTheoryExpr>,
) -> Task<'a> {
    Task::Node {
        tag,
        children: vec![Task::TheoryExpr(left.as_ref()), Task::TheoryExpr(right.as_ref())],
    }
}

fn build<'a>(
    base: &'a std::sync::Arc<DdlTheoryExpr>,
    tag: &'static str,
    entries: Vec<Task<'a>>,
) -> Task<'a> {
    Task::Node {
        tag: "build",
        children: vec![
            Task::TheoryExpr(base.as_ref()),
            Task::Node { tag, children: vec![sequence(entries)] },
        ],
    }
}

fn implicit_build<'a>(tag: &'static str, entries: Vec<Task<'a>>) -> Task<'a> {
    Task::Node {
        tag: "build",
        children: vec![
            Task::Node { tag: "empty", children: Vec::new() },
            Task::Node { tag, children: vec![sequence(entries)] },
        ],
    }
}

fn freshness_tasks<'a>(freshnesses: &'a DdlFreshnesses) -> Vec<Task<'a>> {
    let mut values = Vec::new();
    let mut cursor = freshnesses;
    loop {
        match cursor {
            DdlFreshnesses::DdlFreshnessOne(value) => {
                values.push(Task::Freshness(value.as_ref()));
                break;
            },
            DdlFreshnesses::DdlFreshnessMore(value, tail) => {
                values.push(Task::Freshness(value.as_ref()));
                cursor = tail.as_ref();
            },
        }
    }
    values
}

fn premise_tasks<'a>(premises: &'a DdlPremises) -> Vec<Task<'a>> {
    let mut values = Vec::new();
    let mut cursor = premises;
    loop {
        match cursor {
            DdlPremises::DdlPremiseOne(value) => {
                values.push(Task::Premise(value.as_ref()));
                break;
            },
            DdlPremises::DdlPremiseMore(value, tail) => {
                values.push(Task::Premise(value.as_ref()));
                cursor = tail.as_ref();
            },
        }
    }
    values
}

fn rule_ast_items<'a>(items: &'a DdlRuleAstItems) -> Vec<Task<'a>> {
    let mut values = Vec::new();
    let mut cursor = items;
    loop {
        match cursor {
            DdlRuleAstItems::DdlRuleAstItemOne(value) => {
                values.push(Task::RuleAst(value.as_ref()));
                break;
            },
            DdlRuleAstItems::DdlRuleAstItemMore(value, tail) => {
                values.push(Task::RuleAst(value.as_ref()));
                cursor = tail.as_ref();
            },
        }
    }
    values
}

fn rule_ast_remainder_tail<'a>(tail: &'a DdlRuleAstRemainderTail) -> (Vec<Task<'a>>, &'a str) {
    let mut values = Vec::new();
    let mut cursor = tail;
    loop {
        match cursor {
            DdlRuleAstRemainderTail::DdlRuleAstTailRemainder(name) => {
                return (values, name);
            },
            DdlRuleAstRemainderTail::DdlRuleAstTailMore(value, rest) => {
                values.push(Task::RuleAst(value.as_ref()));
                cursor = rest.as_ref();
            },
        }
    }
}

fn rule_ast_task<'a>(ast: &'a DdlRuleAst) -> Task<'a> {
    match ast {
        DdlRuleAst::DdlRuleAstSubst(body, argument) => Task::Node {
            tag: "ast-subst",
            children: vec![Task::RuleAst(body.as_ref()), Task::RuleAst(argument.as_ref())],
        },
        DdlRuleAst::DdlRuleAstSExp(label, arguments) => Task::Node {
            tag: "ast-sexp",
            children: vec![
                Task::Text(label),
                sequence(arguments.iter().map(Task::RuleAst).collect()),
            ],
        },
        DdlRuleAst::DdlRuleAstAbs(binder, body) => Task::Node {
            tag: "ast-abs",
            children: vec![Task::Text(binder), Task::RuleAst(body.as_ref())],
        },
        DdlRuleAst::DdlRuleAstCollectionEmpty => Task::Node {
            tag: "ast-collection",
            children: vec![sequence(Vec::new())],
        },
        DdlRuleAst::DdlRuleAstCollection(items) => Task::Node {
            tag: "ast-collection",
            children: vec![sequence(rule_ast_items(items.as_ref()))],
        },
        DdlRuleAst::DdlRuleAstRemainderOnly(name) => Task::Node {
            tag: "ast-remainder",
            children: vec![Task::Text(name)],
        },
        DdlRuleAst::DdlRuleAstCollectionRemainder(first, tail) => {
            let (rest, name) = rule_ast_remainder_tail(tail.as_ref());
            let mut children = Vec::with_capacity(
                rest.len()
                    .checked_add(2)
                    .expect("DDL roster width was checked before helper construction"),
            );
            children.push(Task::RuleAst(first.as_ref()));
            children.extend(rest);
            children.push(Task::Node {
                tag: "ast-remainder",
                children: vec![Task::Text(name)],
            });
            Task::Node {
                tag: "ast-collection",
                children: vec![sequence(children)],
            }
        },
        DdlRuleAst::DdlRuleAstVar(name) => Task::Node {
            tag: "ast-var",
            children: vec![Task::Text(name)],
        },
    }
}

enum Task<'a> {
    Text(&'a str),
    QuotedText(&'a str),
    Process(&'a Proc),
    Node {
        tag: &'static str,
        children: Vec<Task<'a>>,
    },
    FinishNode {
        tag: &'static str,
        child_count: usize,
    },
    Module {
        name: &'a str,
        imports: Option<&'a DdlImports>,
        items: &'a [DdlModuleItem],
    },
    Theory {
        name: &'a str,
        parameters: &'a [DdlParam],
        body: &'a DdlTheoryExpr,
    },
    Param(&'a DdlParam),
    Path(&'a DdlPath),
    TheoryExpr(&'a DdlTheoryExpr),
    CatDecl(&'a DdlCatDecl),
    Export(&'a DdlExport),
    Replacement(&'a DdlReplacement),
    TermRule(&'a DdlTermRule),
    Binding(&'a DdlBinding),
    Sort(&'a DdlSort),
    SyntaxItem(&'a DdlSyntaxItem),
    Equation(&'a DdlEquation),
    Freshness(&'a DdlFreshness),
    Rewrite(&'a DdlRewrite),
    Premise(&'a DdlPremise),
    RuleAst(&'a DdlRuleAst),
}

#[cfg(test)]
#[path = "ddl_ast/admission_tests.rs"]
mod admission_tests;

#[cfg(test)]
mod tests {
    use super::decode_captured_string;
    use mettail_languages::rholang::Str;

    #[test]
    fn captured_string_decoding_matches_the_generated_rholang_literal_action() {
        assert_eq!(decode_captured_string(r#""rho:registry/a@1""#).unwrap(), "rho:registry/a@1");
        let raw = r#""a\\\"b\\\\c""#;
        let expected = "a\\\"b\\\\c";
        assert_eq!(decode_captured_string(raw).as_deref(), Ok(expected));
        assert_eq!(
            Str::parse_via_wpda(raw).expect("the generated parser accepts the string token"),
            Str::StringLit(expected.to_string())
        );
        let rendered = Str::StringLit(expected.to_string()).to_string();
        assert_eq!(rendered, raw);
        assert_eq!(
            Str::parse_via_wpda(&rendered).expect("the generated display output parses"),
            Str::StringLit(expected.to_string())
        );
        assert_eq!(decode_captured_string(r#""\n\t\x""#).unwrap(), r"\n\t\x");
        assert!(decode_captured_string("not-quoted").is_err());
    }
}
