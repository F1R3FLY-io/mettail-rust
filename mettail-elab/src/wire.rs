//! Closed value ABI for already-parsed in-Rholang MeTTaIL declarations.
//!
//! The producer is the nouveau Rholang AST lowering.  This decoder consumes an
//! ordinary Rholang value and reconstructs the neutral elaborator AST.  It is
//! deliberately not a source parser: no operation in this module accepts text
//! containing DDL syntax.

use crate::ast::{
    Ast, Binding, Builder, CatDecl, CollKind, DottedPath, Equation, Export, Import, Item,
    ModuleFile, ModuleItem, Param, Replacement, RewriteDecl, Sort, TermRule, TheoryDecl,
    TheoryExpr,
};
use crate::canonical::{
    admit_canonical_value, admit_canonical_value_resources, RhoValue, ValueDecodeError,
};
use crate::lex::Span;
use std::fmt;

pub const DDL_AST_ENVELOPE_V2: &str = "mettail-ddl-ast/2";

#[derive(Clone, Debug)]
pub enum ParsedDdl {
    Module(ModuleFile),
    Theory(TheoryDecl),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DdlValueError {
    pub path: String,
    pub message: String,
}

impl DdlValueError {
    fn new(path: impl Into<String>, message: impl Into<String>) -> Self {
        Self {
            path: path.into(),
            message: message.into(),
        }
    }
}

impl fmt::Display for DdlValueError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{}: {}", self.path, self.message)
    }
}

impl std::error::Error for DdlValueError {}

impl From<ValueDecodeError> for DdlValueError {
    fn from(error: ValueDecodeError) -> Self {
        Self { path: error.path, message: error.message }
    }
}

const SYNTHETIC_SPAN: Span = Span { line: 0, col: 0 };

/// Decode one admitted structural DDL value.
///
/// A single iterative resource pass charges the complete ABI envelope. The
/// schema decoder then accounts semantic DDL depth independently from fixed
/// list/tag framing, and every opaque `Data(v)` payload receives its own
/// canonical-depth admission. This matches the source parser's sectioned
/// bounds without weakening whole-envelope resource limits.
pub fn decode_ddl_value(value: RhoValue) -> Result<ParsedDdl, DdlValueError> {
    admit_canonical_value_resources(&value)?;
    let mut envelope = expect_node(value, DDL_AST_ENVELOPE_V2, Some(1), "$".into())?;
    let root = envelope.pop().expect("envelope arity checked");
    match node_tag(&root) {
        Some("module") => decode_module(root, "$[1]"),
        Some("theory") => decode_theory(root, "$[1]").map(ParsedDdl::Theory),
        Some(tag) => Err(DdlValueError::new(
            "$[1][0]",
            format!("DDL envelope root tag `{tag}` is not `module` or `theory`"),
        )),
        None => Err(DdlValueError::new("$[1]", "DDL envelope root is not a tagged list")),
    }
}

fn decode_module(value: RhoValue, path: &str) -> Result<ParsedDdl, DdlValueError> {
    let mut fields = expect_node(value, "module", Some(3), path.into())?.into_iter();
    let name = expect_string(fields.next().expect("arity checked"), format!("{path}.name"))?;
    let imports =
        expect_sequence(fields.next().expect("arity checked"), &format!("{path}.imports"))?
            .into_iter()
            .enumerate()
            .map(|(index, value)| decode_import(value, &format!("{path}.imports[{index}]")))
            .collect::<Result<Vec<_>, _>>()?;
    let items = expect_sequence(fields.next().expect("arity checked"), &format!("{path}.items"))?
        .into_iter()
        .enumerate()
        .map(|(index, value)| decode_module_item(value, &format!("{path}.items[{index}]"), index))
        .collect::<Result<Vec<_>, _>>()?;
    Ok(ParsedDdl::Module(ModuleFile {
        imports,
        name,
        items,
        span: SYNTHETIC_SPAN,
    }))
}

fn decode_module_item(
    value: RhoValue,
    path: &str,
    source_ordinal: usize,
) -> Result<ModuleItem, DdlValueError> {
    match node_tag(&value) {
        Some("module-theory-declaration") => {
            let mut fields = expect_node(value, "module-theory-declaration", Some(1), path.into())?;
            decode_theory(fields.pop().expect("arity checked"), &format!("{path}.declaration"))
                .map(ModuleItem::TheoryDecl)
        },
        Some("module-theory-entry") => {
            let mut fields = expect_node(value, "module-theory-entry", Some(1), path.into())?;
            decode_theory_expression(
                fields.pop().expect("arity checked"),
                &format!("{path}.expression"),
            )
            .map(ModuleItem::TheoryEntry)
        },
        Some("module-program") => {
            let mut fields = expect_node(value, "module-program", Some(1), path.into())?;
            let slot = expect_usize(fields.pop().expect("arity checked"), format!("{path}.slot"))?;
            Ok(ModuleItem::Program(crate::ast::StagedProgramRef { slot, source_ordinal }))
        },
        Some(tag) => Err(wrong_tag(path, tag, "a module item")),
        None => Err(not_node(path, "a module item")),
    }
}

fn decode_import(value: RhoValue, path: &str) -> Result<Import, DdlValueError> {
    match node_tag(&value) {
        Some("import-module-as") => {
            let mut fields =
                expect_node(value, "import-module-as", Some(2), path.into())?.into_iter();
            Ok(Import::ModuleAs {
                url: expect_string(fields.next().expect("arity checked"), format!("{path}.url"))?,
                alias: expect_string(
                    fields.next().expect("arity checked"),
                    format!("{path}.alias"),
                )?,
                span: SYNTHETIC_SPAN,
            })
        },
        Some("import-from-module") => {
            let mut fields =
                expect_node(value, "import-from-module", Some(2), path.into())?.into_iter();
            Ok(Import::FromModule {
                name: expect_string(fields.next().expect("arity checked"), format!("{path}.name"))?,
                url: expect_string(fields.next().expect("arity checked"), format!("{path}.url"))?,
                span: SYNTHETIC_SPAN,
            })
        },
        Some(tag) => Err(wrong_tag(path, tag, "an import")),
        None => Err(not_node(path, "an import")),
    }
}

fn decode_theory(value: RhoValue, path: &str) -> Result<TheoryDecl, DdlValueError> {
    let mut fields = expect_node(value, "theory", Some(3), path.into())?.into_iter();
    let name = expect_string(fields.next().expect("arity checked"), format!("{path}.name"))?;
    let params = expect_sequence(fields.next().expect("arity checked"), &format!("{path}.params"))?
        .into_iter()
        .enumerate()
        .map(|(index, value)| decode_param(value, &format!("{path}.params[{index}]")))
        .collect::<Result<Vec<_>, _>>()?;
    let body =
        decode_theory_expression(fields.next().expect("arity checked"), &format!("{path}.body"))?;
    Ok(TheoryDecl { name, params, body, span: SYNTHETIC_SPAN })
}

fn decode_param(value: RhoValue, path: &str) -> Result<Param, DdlValueError> {
    let mut fields = expect_node(value, "param", Some(2), path.into())?.into_iter();
    Ok(Param {
        name: expect_string(fields.next().expect("arity checked"), format!("{path}.name"))?,
        ty: decode_path(fields.next().expect("arity checked"), &format!("{path}.type"))?,
        span: SYNTHETIC_SPAN,
    })
}

fn decode_path(value: RhoValue, path: &str) -> Result<DottedPath, DdlValueError> {
    let mut components = Vec::new();
    let mut value = value;
    let mut cursor = path.to_string();
    loop {
        match node_tag(&value) {
            Some("path-name") => {
                let mut fields = expect_node(value, "path-name", Some(1), cursor.clone())?;
                components.push(expect_string(
                    fields.pop().expect("arity checked"),
                    format!("{cursor}.name"),
                )?);
                break;
            },
            Some("path-qualified") => {
                let mut fields =
                    expect_node(value, "path-qualified", Some(2), cursor.clone())?.into_iter();
                components.push(expect_string(
                    fields.next().expect("arity checked"),
                    format!("{cursor}.head"),
                )?);
                value = fields.next().expect("arity checked");
                cursor.push_str(".tail");
            },
            Some(tag) => return Err(wrong_tag(&cursor, tag, "a dotted path")),
            None => return Err(not_node(&cursor, "a dotted path")),
        }
    }
    Ok(DottedPath(components))
}

fn decode_theory_expression(value: RhoValue, path: &str) -> Result<TheoryExpr, DdlValueError> {
    enum Job {
        Decode {
            value: RhoValue,
            path: String,
            depth: usize,
        },
        FinishApply {
            head: DottedPath,
            argument_count: usize,
        },
        FinishLet {
            name: String,
        },
        FinishBuild {
            builder: Builder,
        },
        FinishBinary {
            tag: String,
        },
    }

    let mut jobs = vec![Job::Decode { value, path: path.into(), depth: 1 }];
    let mut values = Vec::new();
    while let Some(job) = jobs.pop() {
        match job {
            Job::Decode { value, path, depth } => {
                require_structural_depth(depth, &path, "theory expression")?;
                match node_tag(&value) {
                    Some("empty") => {
                        expect_node(value, "empty", Some(0), path)?;
                        values.push(TheoryExpr::Empty(SYNTHETIC_SPAN));
                    },
                    Some("free") => {
                        let mut fields = expect_node(value, "free", Some(1), path.clone())?;
                        values.push(TheoryExpr::Free(
                            decode_path(
                                fields.pop().expect("arity checked"),
                                &format!("{path}.path"),
                            )?,
                            SYNTHETIC_SPAN,
                        ));
                    },
                    Some("apply") => {
                        let mut fields =
                            expect_node(value, "apply", Some(2), path.clone())?.into_iter();
                        let head = decode_path(
                            fields.next().expect("arity checked"),
                            &format!("{path}.head"),
                        )?;
                        let arguments = expect_sequence(
                            fields.next().expect("arity checked"),
                            &format!("{path}.args"),
                        )?;
                        let argument_count = arguments.len();
                        jobs.push(Job::FinishApply { head, argument_count });
                        let child_depth = structural_child_depth(depth, &path)?;
                        jobs.extend(arguments.into_iter().enumerate().rev().map(
                            |(index, argument)| Job::Decode {
                                value: argument,
                                path: format!("{path}.args[{index}]"),
                                depth: child_depth,
                            },
                        ));
                    },
                    Some("let") => {
                        let mut fields =
                            expect_node(value, "let", Some(3), path.clone())?.into_iter();
                        let name = expect_string(
                            fields.next().expect("arity checked"),
                            format!("{path}.name"),
                        )?;
                        let bound = fields.next().expect("arity checked");
                        let body = fields.next().expect("arity checked");
                        jobs.push(Job::FinishLet { name });
                        let child_depth = structural_child_depth(depth, &path)?;
                        jobs.push(Job::Decode {
                            value: body,
                            path: format!("{path}.body"),
                            depth: child_depth,
                        });
                        jobs.push(Job::Decode {
                            value: bound,
                            path: format!("{path}.bound"),
                            depth: child_depth,
                        });
                    },
                    Some("build") => {
                        let mut fields =
                            expect_node(value, "build", Some(2), path.clone())?.into_iter();
                        let base = fields.next().expect("arity checked");
                        let builder = decode_builder(
                            fields.next().expect("arity checked"),
                            &format!("{path}.builder"),
                        )?;
                        jobs.push(Job::FinishBuild { builder });
                        jobs.push(Job::Decode {
                            value: base,
                            path: format!("{path}.base"),
                            depth: structural_child_depth(depth, &path)?,
                        });
                    },
                    Some("meet") | Some("join") | Some("difference") => {
                        let tag = node_tag(&value).expect("matched a node tag").to_string();
                        let mut fields =
                            expect_node(value, &tag, Some(2), path.clone())?.into_iter();
                        let left = fields.next().expect("arity checked");
                        let right = fields.next().expect("arity checked");
                        jobs.push(Job::FinishBinary { tag });
                        let child_depth = structural_child_depth(depth, &path)?;
                        jobs.push(Job::Decode {
                            value: right,
                            path: format!("{path}.right"),
                            depth: child_depth,
                        });
                        jobs.push(Job::Decode {
                            value: left,
                            path: format!("{path}.left"),
                            depth: child_depth,
                        });
                    },
                    Some(tag) => return Err(wrong_tag(&path, tag, "a theory expression")),
                    None => return Err(not_node(&path, "a theory expression")),
                }
            },
            Job::FinishApply { head, argument_count } => {
                let start = values
                    .len()
                    .checked_sub(argument_count)
                    .expect("theory decoder apply continuation underflow");
                let args = values.split_off(start);
                values.push(TheoryExpr::Apply { head, args, span: SYNTHETIC_SPAN });
            },
            Job::FinishLet { name } => {
                let body = values.pop().expect("theory decoder let body is present");
                let bound = values.pop().expect("theory decoder let bound is present");
                values.push(TheoryExpr::Let {
                    name,
                    bound: Box::new(bound),
                    body: Box::new(body),
                    span: SYNTHETIC_SPAN,
                });
            },
            Job::FinishBuild { builder } => {
                let base = values.pop().expect("theory decoder build base is present");
                values.push(TheoryExpr::Build {
                    base: Box::new(base),
                    builder,
                    span: SYNTHETIC_SPAN,
                });
            },
            Job::FinishBinary { tag } => {
                let right = Box::new(values.pop().expect("theory decoder right value is present"));
                let left = Box::new(values.pop().expect("theory decoder left value is present"));
                values.push(match tag.as_str() {
                    "meet" => TheoryExpr::Meet(left, right, SYNTHETIC_SPAN),
                    "join" => TheoryExpr::Join(left, right, SYNTHETIC_SPAN),
                    "difference" => TheoryExpr::Diff(left, right, SYNTHETIC_SPAN),
                    _ => unreachable!("closed theory binary tag validated before continuation"),
                });
            },
        }
    }
    if values.len() != 1 {
        return Err(DdlValueError::new(
            path,
            format!("theory decoder produced {} values instead of one", values.len()),
        ));
    }
    Ok(values.pop().expect("length checked"))
}

fn decode_builder(value: RhoValue, path: &str) -> Result<Builder, DdlValueError> {
    match node_tag(&value) {
        Some("types") => {
            decode_builder_sequence(value, "types", path, decode_cat_decl).map(Builder::Types)
        },
        Some("exports") => {
            decode_builder_sequence(value, "exports", path, decode_export).map(Builder::Exports)
        },
        Some("replacements") => {
            decode_builder_sequence(value, "replacements", path, decode_replacement)
                .map(Builder::Replacements)
        },
        Some("terms") => {
            decode_builder_sequence(value, "terms", path, decode_term_rule).map(Builder::Terms)
        },
        Some("equations") => decode_builder_sequence(value, "equations", path, decode_equation)
            .map(Builder::Equations),
        Some("rewrites") => {
            decode_builder_sequence(value, "rewrites", path, decode_rewrite).map(Builder::Rewrites)
        },
        Some("data") => {
            let mut fields = expect_node(value, "data", Some(1), path.into())?;
            let payload = fields.pop().expect("arity checked");
            admit_canonical_value(&payload)?;
            Ok(Builder::Data(payload))
        },
        Some(tag) => Err(wrong_tag(path, tag, "a DDL builder")),
        None => Err(not_node(path, "a DDL builder")),
    }
}

fn decode_builder_sequence<T>(
    value: RhoValue,
    tag: &str,
    path: &str,
    decode: fn(RhoValue, &str) -> Result<T, DdlValueError>,
) -> Result<Vec<T>, DdlValueError> {
    let mut fields = expect_node(value, tag, Some(1), path.into())?;
    expect_sequence(fields.pop().expect("arity checked"), &format!("{path}.entries"))?
        .into_iter()
        .enumerate()
        .map(|(index, value)| decode(value, &format!("{path}.entries[{index}]")))
        .collect()
}

fn decode_cat_decl(value: RhoValue, path: &str) -> Result<CatDecl, DdlValueError> {
    let mut fields = expect_node(value, "category", Some(1), path.into())?;
    Ok(CatDecl {
        cat: expect_string(fields.pop().expect("arity checked"), format!("{path}.category"))?,
        span: SYNTHETIC_SPAN,
    })
}

fn decode_export(value: RhoValue, path: &str) -> Result<Export, DdlValueError> {
    let mut fields = expect_node(value, "export", Some(2), path.into())?.into_iter();
    Ok(Export {
        cat: expect_string(fields.next().expect("arity checked"), format!("{path}.category"))?,
        as_name: decode_optional_string(
            fields.next().expect("arity checked"),
            &format!("{path}.rename"),
        )?,
        span: SYNTHETIC_SPAN,
    })
}

fn decode_replacement(value: RhoValue, path: &str) -> Result<Replacement, DdlValueError> {
    let mut fields = expect_node(value, "replacement", Some(2), path.into())?.into_iter();
    Ok(Replacement {
        target: expect_string(fields.next().expect("arity checked"), format!("{path}.target"))?,
        rule: decode_term_rule(fields.next().expect("arity checked"), &format!("{path}.rule"))?,
        span: SYNTHETIC_SPAN,
    })
}

fn decode_term_rule(value: RhoValue, path: &str) -> Result<TermRule, DdlValueError> {
    let mut fields = expect_node(value, "term", Some(4), path.into())?.into_iter();
    let label = expect_string(fields.next().expect("arity checked"), format!("{path}.label"))?;
    let context =
        expect_sequence(fields.next().expect("arity checked"), &format!("{path}.context"))?
            .into_iter()
            .enumerate()
            .map(|(index, value)| decode_binding(value, &format!("{path}.context[{index}]")))
            .collect::<Result<Vec<_>, _>>()?;
    let syntax = expect_sequence(fields.next().expect("arity checked"), &format!("{path}.syntax"))?
        .into_iter()
        .enumerate()
        .map(|(index, value)| decode_item(value, &format!("{path}.syntax[{index}]")))
        .collect::<Result<Vec<_>, _>>()?;
    let result = expect_string(fields.next().expect("arity checked"), format!("{path}.result"))?;
    Ok(TermRule {
        label,
        context,
        syntax,
        result,
        span: SYNTHETIC_SPAN,
    })
}

fn decode_binding(value: RhoValue, path: &str) -> Result<Binding, DdlValueError> {
    match node_tag(&value) {
        Some("binding") => {
            let mut fields = expect_node(value, "binding", Some(2), path.into())?.into_iter();
            Ok(Binding::Plain {
                name: expect_string(fields.next().expect("arity checked"), format!("{path}.name"))?,
                sort: decode_sort(fields.next().expect("arity checked"), &format!("{path}.sort"))?,
                span: SYNTHETIC_SPAN,
            })
        },
        Some("binder") => {
            let mut fields = expect_node(value, "binder", Some(4), path.into())?.into_iter();
            Ok(Binding::Binder {
                binder: expect_string(
                    fields.next().expect("arity checked"),
                    format!("{path}.binder"),
                )?,
                body: expect_string(fields.next().expect("arity checked"), format!("{path}.body"))?,
                from: expect_string(fields.next().expect("arity checked"), format!("{path}.from"))?,
                to: expect_string(fields.next().expect("arity checked"), format!("{path}.to"))?,
                span: SYNTHETIC_SPAN,
            })
        },
        Some(tag) => Err(wrong_tag(path, tag, "a term binding")),
        None => Err(not_node(path, "a term binding")),
    }
}

fn decode_sort(value: RhoValue, path: &str) -> Result<Sort, DdlValueError> {
    let tag = node_tag(&value)
        .ok_or_else(|| not_node(path, "a sort"))?
        .to_string();
    let mut fields = expect_node(value, &tag, Some(1), path.into())?;
    let category = expect_string(fields.pop().expect("arity checked"), format!("{path}.category"))?;
    match tag.as_str() {
        "sort-category" => Ok(Sort::Cat(category)),
        "sort-bag" => Ok(Sort::Coll { kind: CollKind::HashBag, of: category }),
        "sort-set" => Ok(Sort::Coll { kind: CollKind::Set, of: category }),
        "sort-list" => Ok(Sort::Coll { kind: CollKind::List, of: category }),
        _ => Err(wrong_tag(path, &tag, "a sort")),
    }
}

fn decode_item(value: RhoValue, path: &str) -> Result<Item, DdlValueError> {
    match node_tag(&value) {
        Some("syntax-terminal") => {
            let mut fields = expect_node(value, "syntax-terminal", Some(1), path.into())?;
            Ok(Item::Terminal(expect_string(
                fields.pop().expect("arity checked"),
                format!("{path}.terminal"),
            )?))
        },
        Some("syntax-argument") => {
            let mut fields = expect_node(value, "syntax-argument", Some(1), path.into())?;
            Ok(Item::ArgRef(expect_string(
                fields.pop().expect("arity checked"),
                format!("{path}.argument"),
            )?))
        },
        Some("syntax-projection") => {
            let mut fields =
                expect_node(value, "syntax-projection", Some(2), path.into())?.into_iter();
            Ok(Item::Projection {
                arg: expect_string(
                    fields.next().expect("arity checked"),
                    format!("{path}.argument"),
                )?,
                sep: expect_string(
                    fields.next().expect("arity checked"),
                    format!("{path}.separator"),
                )?,
            })
        },
        Some(tag) => Err(wrong_tag(path, tag, "a concrete-syntax item")),
        None => Err(not_node(path, "a concrete-syntax item")),
    }
}

fn decode_equation(value: RhoValue, path: &str) -> Result<Equation, DdlValueError> {
    let mut fields = expect_node(value, "equation", Some(3), path.into())?.into_iter();
    let freshness =
        expect_sequence(fields.next().expect("arity checked"), &format!("{path}.freshness"))?
            .into_iter()
            .enumerate()
            .map(|(index, value)| {
                decode_pair(value, "freshness", &format!("{path}.freshness[{index}]"))
            })
            .collect::<Result<Vec<_>, _>>()?;
    let lhs = decode_ast(fields.next().expect("arity checked"), &format!("{path}.left"))?;
    let rhs = decode_ast(fields.next().expect("arity checked"), &format!("{path}.right"))?;
    Ok(Equation {
        freshness,
        lhs,
        rhs,
        span: SYNTHETIC_SPAN,
    })
}

fn decode_rewrite(value: RhoValue, path: &str) -> Result<RewriteDecl, DdlValueError> {
    let mut fields = expect_node(value, "rewrite", Some(4), path.into())?.into_iter();
    let name = expect_string(fields.next().expect("arity checked"), format!("{path}.name"))?;
    let premises =
        expect_sequence(fields.next().expect("arity checked"), &format!("{path}.premises"))?
            .into_iter()
            .enumerate()
            .map(|(index, value)| {
                decode_pair(value, "premise", &format!("{path}.premises[{index}]"))
            })
            .collect::<Result<Vec<_>, _>>()?;
    let lhs = decode_ast(fields.next().expect("arity checked"), &format!("{path}.left"))?;
    let rhs = decode_ast(fields.next().expect("arity checked"), &format!("{path}.right"))?;
    Ok(RewriteDecl {
        name,
        premises,
        lhs,
        rhs,
        span: SYNTHETIC_SPAN,
    })
}

fn decode_pair(value: RhoValue, tag: &str, path: &str) -> Result<(String, String), DdlValueError> {
    let mut fields = expect_node(value, tag, Some(2), path.into())?.into_iter();
    Ok((
        expect_string(fields.next().expect("arity checked"), format!("{path}.left"))?,
        expect_string(fields.next().expect("arity checked"), format!("{path}.right"))?,
    ))
}

fn decode_ast(value: RhoValue, path: &str) -> Result<Ast, DdlValueError> {
    enum Job {
        Decode {
            value: RhoValue,
            path: String,
            depth: usize,
        },
        FinishSExp {
            label: String,
            argument_count: usize,
        },
        FinishSubst,
        FinishAbs {
            binder: String,
        },
        FinishCollection {
            element_count: usize,
        },
    }

    let mut jobs = vec![Job::Decode { value, path: path.into(), depth: 1 }];
    let mut values = Vec::new();
    while let Some(job) = jobs.pop() {
        match job {
            Job::Decode { value, path, depth } => {
                require_structural_depth(depth, &path, "rule AST")?;
                match node_tag(&value) {
                    Some("ast-var") | Some("ast-remainder") => {
                        let tag = node_tag(&value).expect("matched a node tag").to_string();
                        let mut fields = expect_node(value, &tag, Some(1), path.clone())?;
                        let name = expect_string(
                            fields.pop().expect("arity checked"),
                            format!("{path}.name"),
                        )?;
                        values.push(if tag == "ast-var" {
                            Ast::Var(name, SYNTHETIC_SPAN)
                        } else {
                            Ast::Remainder(name, SYNTHETIC_SPAN)
                        });
                    },
                    Some("ast-sexp") => {
                        let mut fields =
                            expect_node(value, "ast-sexp", Some(2), path.clone())?.into_iter();
                        let label = expect_string(
                            fields.next().expect("arity checked"),
                            format!("{path}.label"),
                        )?;
                        let arguments = expect_sequence(
                            fields.next().expect("arity checked"),
                            &format!("{path}.arguments"),
                        )?;
                        let argument_count = arguments.len();
                        jobs.push(Job::FinishSExp { label, argument_count });
                        let child_depth = structural_child_depth(depth, &path)?;
                        jobs.extend(arguments.into_iter().enumerate().rev().map(
                            |(index, argument)| Job::Decode {
                                value: argument,
                                path: format!("{path}.arguments[{index}]"),
                                depth: child_depth,
                            },
                        ));
                    },
                    Some("ast-subst") => {
                        let mut fields =
                            expect_node(value, "ast-subst", Some(2), path.clone())?.into_iter();
                        let body = fields.next().expect("arity checked");
                        let argument = fields.next().expect("arity checked");
                        jobs.push(Job::FinishSubst);
                        let child_depth = structural_child_depth(depth, &path)?;
                        jobs.push(Job::Decode {
                            value: argument,
                            path: format!("{path}.argument"),
                            depth: child_depth,
                        });
                        jobs.push(Job::Decode {
                            value: body,
                            path: format!("{path}.body"),
                            depth: child_depth,
                        });
                    },
                    Some("ast-abs") => {
                        let mut fields =
                            expect_node(value, "ast-abs", Some(2), path.clone())?.into_iter();
                        let binder = expect_string(
                            fields.next().expect("arity checked"),
                            format!("{path}.binder"),
                        )?;
                        let body = fields.next().expect("arity checked");
                        jobs.push(Job::FinishAbs { binder });
                        jobs.push(Job::Decode {
                            value: body,
                            path: format!("{path}.body"),
                            depth: structural_child_depth(depth, &path)?,
                        });
                    },
                    Some("ast-collection") => {
                        let mut fields =
                            expect_node(value, "ast-collection", Some(1), path.clone())?;
                        let elements = expect_sequence(
                            fields.pop().expect("arity checked"),
                            &format!("{path}.elements"),
                        )?;
                        let element_count = elements.len();
                        jobs.push(Job::FinishCollection { element_count });
                        let child_depth = structural_child_depth(depth, &path)?;
                        jobs.extend(elements.into_iter().enumerate().rev().map(
                            |(index, element)| Job::Decode {
                                value: element,
                                path: format!("{path}.elements[{index}]"),
                                depth: child_depth,
                            },
                        ));
                    },
                    Some(tag) => return Err(wrong_tag(&path, tag, "a rule AST")),
                    None => return Err(not_node(&path, "a rule AST")),
                }
            },
            Job::FinishSExp { label, argument_count } => {
                let start = values
                    .len()
                    .checked_sub(argument_count)
                    .expect("rule AST S-expression continuation underflow");
                let arguments = values.split_off(start);
                values.push(Ast::SExp(label, arguments, SYNTHETIC_SPAN));
            },
            Job::FinishSubst => {
                let argument = Box::new(values.pop().expect("rule AST argument is present"));
                let body = Box::new(values.pop().expect("rule AST body is present"));
                values.push(Ast::Subst(body, argument, SYNTHETIC_SPAN));
            },
            Job::FinishAbs { binder } => {
                let body = Box::new(values.pop().expect("rule AST abstraction body is present"));
                values.push(Ast::Abs(binder, body, SYNTHETIC_SPAN));
            },
            Job::FinishCollection { element_count } => {
                let start = values
                    .len()
                    .checked_sub(element_count)
                    .expect("rule AST collection continuation underflow");
                let elements = values.split_off(start);
                values.push(Ast::Coll(elements, SYNTHETIC_SPAN));
            },
        }
    }
    if values.len() != 1 {
        return Err(DdlValueError::new(
            path,
            format!("rule AST decoder produced {} values instead of one", values.len()),
        ));
    }
    Ok(values.pop().expect("length checked"))
}

fn decode_optional_string(value: RhoValue, path: &str) -> Result<Option<String>, DdlValueError> {
    match node_tag(&value) {
        Some("none") => {
            expect_node(value, "none", Some(0), path.into())?;
            Ok(None)
        },
        Some("some") => {
            let mut fields = expect_node(value, "some", Some(1), path.into())?;
            expect_string(fields.pop().expect("arity checked"), format!("{path}.value")).map(Some)
        },
        Some(tag) => Err(wrong_tag(path, tag, "an option")),
        None => Err(not_node(path, "an option")),
    }
}

fn require_structural_depth(depth: usize, path: &str, resource: &str) -> Result<(), DdlValueError> {
    if depth > crate::parse::MAX_DDL_STRUCTURAL_DEPTH {
        Err(DdlValueError::new(
            path,
            format!(
                "{resource} nesting exceeds the maximum of {}",
                crate::parse::MAX_DDL_STRUCTURAL_DEPTH
            ),
        ))
    } else {
        Ok(())
    }
}

fn structural_child_depth(depth: usize, path: &str) -> Result<usize, DdlValueError> {
    depth
        .checked_add(1)
        .ok_or_else(|| DdlValueError::new(path, "structural DDL depth overflowed"))
}

fn expect_sequence(value: RhoValue, path: &str) -> Result<Vec<RhoValue>, DdlValueError> {
    expect_node(value, "sequence", None, path.into())
}

fn expect_node(
    mut value: RhoValue,
    expected: &str,
    arity: Option<usize>,
    path: String,
) -> Result<Vec<RhoValue>, DdlValueError> {
    let RhoValue::List(values) = &mut value else {
        return Err(not_node(&path, expected));
    };
    let mut values = std::mem::take(values);
    if values.is_empty() {
        return Err(DdlValueError::new(path, "tagged list is empty"));
    }
    let tag = expect_string(values.remove(0), format!("{path}[0]"))?;
    if tag != expected {
        return Err(wrong_tag(&path, &tag, expected));
    }
    if let Some(expected_arity) = arity {
        if values.len() != expected_arity {
            return Err(DdlValueError::new(
                path,
                format!("`{expected}` node has arity {}; expected {expected_arity}", values.len()),
            ));
        }
    }
    Ok(values)
}

fn expect_string(mut value: RhoValue, path: String) -> Result<String, DdlValueError> {
    let RhoValue::String(value) = &mut value else {
        return Err(DdlValueError::new(path, "expected a string"));
    };
    Ok(std::mem::take(value))
}

fn expect_usize(value: RhoValue, path: String) -> Result<usize, DdlValueError> {
    let RhoValue::Integer(value) = value else {
        return Err(DdlValueError::new(path, "expected a non-negative integer"));
    };
    usize::try_from(value)
        .map_err(|_| DdlValueError::new(path, "integer is outside the platform index range"))
}

fn node_tag(value: &RhoValue) -> Option<&str> {
    let RhoValue::List(values) = value else {
        return None;
    };
    let Some(RhoValue::String(tag)) = values.first() else {
        return None;
    };
    Some(tag)
}

fn wrong_tag(path: &str, actual: &str, expected: &str) -> DdlValueError {
    DdlValueError::new(path, format!("tag `{actual}` does not denote {expected}"))
}

fn not_node(path: &str, expected: &str) -> DdlValueError {
    DdlValueError::new(path, format!("expected {expected} tagged list"))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn node(tag: &str, fields: Vec<RhoValue>) -> RhoValue {
        RhoValue::List(
            std::iter::once(RhoValue::String(tag.into()))
                .chain(fields)
                .collect(),
        )
    }

    #[test]
    fn decodes_a_structural_standalone_theory_without_source_text() {
        let value = node(
            DDL_AST_ENVELOPE_V2,
            vec![node(
                "theory",
                vec![RhoValue::String("T".into()), node("sequence", vec![]), node("empty", vec![])],
            )],
        );
        let ParsedDdl::Theory(theory) = decode_ddl_value(value).expect("valid theory") else {
            panic!("expected a theory")
        };
        assert_eq!(theory.name, "T");
        assert!(matches!(theory.body, TheoryExpr::Empty(_)));
    }

    #[test]
    fn rejects_unknown_tags_and_decodes_staged_module_program_references() {
        let unknown = node(DDL_AST_ENVELOPE_V2, vec![node("invented", vec![])]);
        assert!(decode_ddl_value(unknown).is_err());

        let module = node(
            DDL_AST_ENVELOPE_V2,
            vec![node(
                "module",
                vec![
                    RhoValue::String("M".into()),
                    node("sequence", vec![]),
                    node("sequence", vec![node("module-program", vec![RhoValue::Integer(0)])]),
                ],
            )],
        );
        let ParsedDdl::Module(module) =
            decode_ddl_value(module).expect("staged program reference decodes structurally")
        else {
            panic!("expected a module")
        };
        assert!(matches!(
            module.items.as_slice(),
            [ModuleItem::Program(crate::ast::StagedProgramRef { slot: 0, source_ordinal: 0 })]
        ));
    }

    #[test]
    fn deeply_nested_theory_and_rule_ast_decode_on_a_small_native_stack() {
        // The public value admission limit is 256. Exercise essentially its
        // full supported depth on a deliberately small stack and also let the
        // decoded values drop there.
        const DEPTH: usize = 240;
        let mut theory = node("empty", vec![]);
        for _ in 0..DEPTH {
            theory = node("join", vec![theory, node("empty", vec![])]);
        }
        let mut rule_ast = node("ast-var", vec![RhoValue::String("x".into())]);
        for _ in 0..DEPTH {
            rule_ast = node("ast-abs", vec![RhoValue::String("x".into()), rule_ast]);
        }

        std::thread::Builder::new()
            .stack_size(64 * 1024)
            .spawn(move || {
                let theory = decode_theory_expression(theory, "$.theory")
                    .expect("theory decoder uses its heap work stack");
                let rule_ast = decode_ast(rule_ast, "$.ast")
                    .expect("rule AST decoder uses its heap work stack");
                drop(theory);
                drop(rule_ast);
            })
            .expect("small-stack decoder thread starts")
            .join()
            .expect("small-stack decoder thread completes");
    }

    fn nested_theory_expression(depth: usize) -> RhoValue {
        assert!(depth >= 1);
        let mut expression = node("empty", vec![]);
        for _ in 1..depth {
            expression = node("join", vec![expression, node("empty", vec![])]);
        }
        expression
    }

    fn nested_canonical_value(depth: usize) -> RhoValue {
        assert!(depth >= 1);
        let mut value = RhoValue::Nil;
        for _ in 1..depth {
            value = RhoValue::List(vec![value]);
        }
        value
    }

    fn theory_envelope(body: RhoValue) -> RhoValue {
        node(
            DDL_AST_ENVELOPE_V2,
            vec![node(
                "theory",
                vec![RhoValue::String("T".into()), node("sequence", vec![]), body],
            )],
        )
    }

    #[test]
    fn wire_framing_does_not_reduce_theory_expression_depth_budget() {
        let exact =
            theory_envelope(nested_theory_expression(crate::parse::MAX_DDL_STRUCTURAL_DEPTH));
        decode_ddl_value(exact).expect("the exact semantic theory bound is admitted");

        let excessive =
            theory_envelope(nested_theory_expression(crate::parse::MAX_DDL_STRUCTURAL_DEPTH + 1));
        let error = decode_ddl_value(excessive).expect_err("one extra theory level is rejected");
        assert!(error.message.contains("theory expression nesting exceeds"));
    }

    #[test]
    fn data_payload_has_an_independent_canonical_depth_budget() {
        let exact = theory_envelope(node(
            "build",
            vec![
                node("empty", vec![]),
                node("data", vec![nested_canonical_value(crate::parse::MAX_DDL_STRUCTURAL_DEPTH)]),
            ],
        ));
        decode_ddl_value(exact).expect("DDL framing does not spend Data(v) depth");

        let excessive = theory_envelope(node(
            "build",
            vec![
                node("empty", vec![]),
                node(
                    "data",
                    vec![nested_canonical_value(crate::parse::MAX_DDL_STRUCTURAL_DEPTH + 1)],
                ),
            ],
        ));
        let error = decode_ddl_value(excessive).expect_err("overdeep Data(v) is rejected");
        assert!(error.message.contains("canonical value nesting exceeds"));
    }
}
