//! Closed value ABI for already-parsed in-Rholang MeTTaIL declarations.
//!
//! The producer is the nouveau Rholang AST lowering.  This decoder consumes an
//! ordinary Rholang value and reconstructs the neutral elaborator AST.  It is
//! deliberately not a source parser: no operation in this module accepts text
//! containing DDL syntax.

use crate::ast::{
    Ast, Binding, Builder, CatDecl, CollKind, DottedPath, Equation, Export, Import, Item,
    LimitAssignment, ModuleFile, ModuleItem, OptionSection, Param, ProjectionBinding,
    ProjectionBody, ProjectionDecl, ProjectionDirection, ProjectionPremise, ProjectionRule,
    Replacement, RewriteDecl, RewriteEntry, Sort, TermAssociativity, TermDecl, TermRule,
    TheoryDecl, TheoryExpr, TokenDecl,
};
use crate::canonical::{
    admit_canonical_value, admit_canonical_value_resources, RhoValue, ValueDecodeError,
};
use crate::lex::Span;
use std::collections::BTreeSet;
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
            decode_builder_sequence(value, "terms", path, decode_term_decl).map(Builder::Terms)
        },
        Some("equations") => decode_builder_sequence(value, "equations", path, decode_equation)
            .map(Builder::Equations),
        Some("rewrites") => decode_builder_sequence(value, "rewrites", path, decode_rewrite_entry)
            .map(Builder::Rewrites),
        Some("options") => decode_options_builder(value, path).map(Builder::Options),
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

fn decode_options_builder(
    value: RhoValue,
    path: &str,
) -> Result<Vec<OptionSection>, DdlValueError> {
    let mut fields = expect_node(value, "options", Some(1), path.into())?;
    let sections =
        expect_sequence(fields.pop().expect("arity checked"), &format!("{path}.sections"))?;
    let mut seen_semantics = false;
    let mut decoded = Vec::with_capacity(sections.len());
    for (index, section) in sections.into_iter().enumerate() {
        let section_path = format!("{path}.sections[{index}]");
        match node_tag(&section) {
            Some("option-semantics-limits") => {
                if seen_semantics {
                    return Err(DdlValueError::new(
                        section_path,
                        "duplicate Semantics.Limits section",
                    ));
                }
                seen_semantics = true;
                let mut fields =
                    expect_node(section, "option-semantics-limits", Some(1), section_path.clone())?;
                let entries = expect_sequence(
                    fields.pop().expect("arity checked"),
                    &format!("{section_path}.entries"),
                )?;
                let mut seen_names = BTreeSet::new();
                let mut limits = Vec::with_capacity(entries.len());
                for (entry_index, entry) in entries.into_iter().enumerate() {
                    let entry_path = format!("{section_path}.entries[{entry_index}]");
                    let mut parts =
                        expect_node(entry, "limit-assignment", Some(2), entry_path.clone())?
                            .into_iter();
                    let name = expect_string(
                        parts.next().expect("arity checked"),
                        format!("{entry_path}.name"),
                    )?;
                    if !matches!(
                        name.as_str(),
                        "max_rule_variables"
                            | "max_term_nodes"
                            | "max_premise_nodes"
                            | "max_proof_nodes"
                            | "max_frontier"
                            | "max_steps"
                            | "max_grade_bits"
                            | "max_output_nodes"
                            | "max_output_bytes"
                    ) {
                        return Err(DdlValueError::new(
                            format!("{entry_path}.name"),
                            format!("unknown Semantics.Limits field `{name}`"),
                        ));
                    }
                    if !seen_names.insert(name.clone()) {
                        return Err(DdlValueError::new(
                            format!("{entry_path}.name"),
                            format!("duplicate Semantics.Limits field `{name}`"),
                        ));
                    }
                    // Generated `Int` captures use decimal text in the
                    // structural DDL wire (as do term binding powers). Do
                    // not silently accept a second representation here.
                    let value_path = format!("{entry_path}.value");
                    let spelling =
                        expect_string(parts.next().expect("arity checked"), value_path.clone())?;
                    let value = spelling.parse::<u32>().map_err(|_| {
                        DdlValueError::new(
                            value_path.clone(),
                            "expected a canonical unsigned 32-bit decimal limit",
                        )
                    })?;
                    if spelling != value.to_string() {
                        return Err(DdlValueError::new(
                            value_path,
                            "expected a canonical unsigned 32-bit decimal limit",
                        ));
                    }
                    limits.push(LimitAssignment { name, value, span: SYNTHETIC_SPAN });
                }
                decoded.push(OptionSection::SemanticsLimits(limits));
            },
            Some(tag) => return Err(wrong_tag(&section_path, tag, "an Options section")),
            None => return Err(not_node(&section_path, "an Options section")),
        }
    }
    Ok(decoded)
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
    let (tag, admits_variables, has_carrier) = match node_tag(&value) {
        Some("category-noadmit") => ("category-noadmit", false, false),
        Some("category-carrier") => ("category-carrier", true, true),
        Some("category-noadmit-carrier") => ("category-noadmit-carrier", false, true),
        _ => ("category", true, false),
    };
    let mut fields =
        expect_node(value, tag, Some(if has_carrier { 2 } else { 1 }), path.into())?.into_iter();
    let cat = expect_string(fields.next().expect("arity checked"), format!("{path}.category"))?;
    let carrier = if has_carrier {
        Some(expect_string(fields.next().expect("arity checked"), format!("{path}.carrier"))?)
    } else {
        None
    };
    Ok(CatDecl {
        cat,
        admits_variables,
        carrier,
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

fn decode_term_decl(value: RhoValue, path: &str) -> Result<TermDecl, DdlValueError> {
    if node_tag(&value) != Some("token") {
        return decode_term_rule(value, path).map(TermDecl::Rule);
    }
    let mut fields = expect_node(value, "token", Some(2), path.into())?.into_iter();
    let name = expect_string(fields.next().expect("arity checked"), format!("{path}.name"))?;
    let pattern =
        decode_reg_pattern(fields.next().expect("arity checked"), &format!("{path}.reg"))?;
    Ok(TermDecl::Token(TokenDecl { name, pattern, span: SYNTHETIC_SPAN }))
}

fn append_reg_spelling(
    pattern: &mut String,
    spelling: &str,
    path: &str,
) -> Result<(), DdlValueError> {
    let bytes = pattern
        .len()
        .checked_add(spelling.len())
        .ok_or_else(|| DdlValueError::new(path, "regex pattern byte count overflowed"))?;
    if bytes > crate::canonical::MAX_CANONICAL_STRING_BYTES {
        return Err(DdlValueError::new(path, "regex pattern exceeds canonical string limit"));
    }
    pattern.push_str(spelling);
    Ok(())
}

/// Reconstitute only the exact lexemes of the generated, typed Reg AST. The
/// existing PraTTaIL regex compiler remains the sole regex-syntax validator
/// and semantic compiler; this function is not a textual DDL parser.
fn decode_reg_pattern(value: RhoValue, path: &str) -> Result<String, DdlValueError> {
    let pieces = expect_sequence(value, path)?;
    let mut pattern = String::new();
    for (index, piece) in pieces.into_iter().enumerate() {
        let piece_path = format!("{path}[{index}]");
        match node_tag(&piece) {
            Some("regex-literal" | "regex-escape" | "regex-operator") => {
                let tag = node_tag(&piece).expect("matched tag").to_owned();
                let mut fields = expect_node(piece, &tag, Some(1), piece_path.clone())?;
                let spelling = expect_string(
                    fields.pop().expect("arity checked"),
                    format!("{piece_path}.spelling"),
                )?;
                append_reg_spelling(&mut pattern, &spelling, &piece_path)?;
            },
            Some("regex-class") => {
                let mut fields = expect_node(piece, "regex-class", Some(1), piece_path.clone())?;
                append_reg_spelling(&mut pattern, "[", &piece_path)?;
                let class_pieces = expect_sequence(
                    fields.pop().expect("arity checked"),
                    &format!("{piece_path}.pieces"),
                )?;
                for (class_index, class_piece) in class_pieces.into_iter().enumerate() {
                    let class_path = format!("{piece_path}.pieces[{class_index}]");
                    let Some(
                        tag @ ("regex-class-literal"
                        | "regex-class-escape"
                        | "regex-class-hyphen"
                        | "regex-class-caret"),
                    ) = node_tag(&class_piece)
                    else {
                        return Err(DdlValueError::new(class_path, "expected a regex class piece"));
                    };
                    let tag = tag.to_owned();
                    let mut fields = expect_node(class_piece, &tag, Some(1), class_path.clone())?;
                    let spelling = expect_string(
                        fields.pop().expect("arity checked"),
                        format!("{class_path}.spelling"),
                    )?;
                    append_reg_spelling(&mut pattern, &spelling, &class_path)?;
                }
                append_reg_spelling(&mut pattern, "]", &piece_path)?;
            },
            Some(tag) => return Err(wrong_tag(&piece_path, tag, "a regex piece")),
            None => return Err(not_node(&piece_path, "a regex piece")),
        }
    }
    if pattern.is_empty() {
        return Err(DdlValueError::new(path, "token regex must not be empty"));
    }
    Ok(pattern)
}

fn decode_term_rule(value: RhoValue, path: &str) -> Result<TermRule, DdlValueError> {
    let attributed = node_tag(&value) == Some("term-attributed");
    let mut fields = expect_node(
        value,
        if attributed {
            "term-attributed"
        } else {
            "term"
        },
        Some(if attributed { 5 } else { 4 }),
        path.into(),
    )?
    .into_iter();
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
    let mut associativity = None;
    let mut prefix_binding_power = None;
    if attributed {
        let attributes =
            expect_sequence(fields.next().expect("arity checked"), &format!("{path}.attributes"))?;
        if attributes.is_empty() {
            return Err(DdlValueError::new(
                format!("{path}.attributes"),
                "attributed term requires at least one attribute",
            ));
        }
        for (index, attribute) in attributes.into_iter().enumerate() {
            let attribute_path = format!("{path}.attributes[{index}]");
            match node_tag(&attribute) {
                Some("term-attr-word") => {
                    let mut values =
                        expect_node(attribute, "term-attr-word", Some(1), attribute_path.clone())?;
                    let spelling = expect_string(
                        values.pop().expect("arity checked"),
                        format!("{attribute_path}.name"),
                    )?;
                    let Some(value) = TermAssociativity::parse(&spelling) else {
                        return Err(DdlValueError::new(
                            attribute_path,
                            "expected left, right, or nonassoc",
                        ));
                    };
                    if associativity.replace(value).is_some() {
                        return Err(DdlValueError::new(attribute_path, "duplicate associativity"));
                    }
                },
                Some("term-attr-call") => {
                    let mut values =
                        expect_node(attribute, "term-attr-call", Some(2), attribute_path.clone())?
                            .into_iter();
                    let name = expect_string(
                        values.next().expect("arity checked"),
                        format!("{attribute_path}.name"),
                    )?;
                    if name != "prefix" {
                        return Err(DdlValueError::new(
                            attribute_path,
                            "expected prefix(binding_power)",
                        ));
                    }
                    let spelling = expect_string(
                        values.next().expect("arity checked"),
                        format!("{attribute_path}.binding_power"),
                    )?;
                    let power = spelling.parse::<u16>().map_err(|_| {
                        DdlValueError::new(
                            format!("{attribute_path}.binding_power"),
                            "expected a u16 binding power",
                        )
                    })?;
                    if prefix_binding_power.replace(power).is_some() {
                        return Err(DdlValueError::new(
                            attribute_path,
                            "duplicate prefix binding power",
                        ));
                    }
                },
                Some(tag) => return Err(wrong_tag(&attribute_path, tag, "a term attribute")),
                None => return Err(not_node(&attribute_path, "a term attribute")),
            }
        }
    }
    Ok(TermRule {
        label,
        context,
        syntax,
        result,
        associativity,
        prefix_binding_power,
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

fn decode_rewrite_entry(value: RhoValue, path: &str) -> Result<RewriteEntry, DdlValueError> {
    match node_tag(&value) {
        Some("rewrite") => decode_rewrite(value, path).map(RewriteEntry::Ordinary),
        Some("projection-group") | Some("projection-carrier") => {
            decode_projection(value, path).map(RewriteEntry::Projection)
        },
        Some(tag) => Err(wrong_tag(path, tag, "a rewrite or projection declaration")),
        None => Err(not_node(path, "a rewrite or projection declaration")),
    }
}

fn decode_projection(value: RhoValue, path: &str) -> Result<ProjectionDecl, DdlValueError> {
    let is_carrier = node_tag(&value) == Some("projection-carrier");
    let tag = if is_carrier {
        "projection-carrier"
    } else {
        "projection-group"
    };
    let fields = expect_node(value, tag, Some(if is_carrier { 4 } else { 5 }), path.into())?;
    let mut fields = fields.into_iter();
    let name = expect_string(fields.next().expect("arity checked"), format!("{path}.name"))?;
    let guest = expect_string(fields.next().expect("arity checked"), format!("{path}.guest"))?;
    let direction = decode_projection_direction(
        fields.next().expect("arity checked"),
        &format!("{path}.direction"),
    )?;
    let host = expect_string(fields.next().expect("arity checked"), format!("{path}.host"))?;
    let body = if is_carrier {
        ProjectionBody::Carrier
    } else {
        let rows = expect_sequence(fields.next().expect("arity checked"), &format!("{path}.rows"))?
            .into_iter()
            .enumerate()
            .map(|(index, row)| decode_projection_rule(row, &format!("{path}.rows[{index}]")))
            .collect::<Result<Vec<_>, _>>()?;
        for (index, row) in rows.iter().enumerate() {
            if row.direction != direction {
                return Err(DdlValueError::new(
                    format!("{path}.rows[{index}].direction"),
                    "projection row direction must match its group declaration",
                ));
            }
        }
        ProjectionBody::Rules(rows)
    };
    Ok(ProjectionDecl {
        name,
        guest,
        host,
        direction,
        body,
        span: SYNTHETIC_SPAN,
    })
}

fn decode_projection_direction(
    value: RhoValue,
    path: &str,
) -> Result<ProjectionDirection, DdlValueError> {
    let direction = match node_tag(&value) {
        Some("guest-to-host") => ProjectionDirection::GuestToHost,
        Some("host-to-guest") => ProjectionDirection::HostToGuest,
        Some("bidirectional") => ProjectionDirection::Both,
        Some(tag) => return Err(wrong_tag(path, tag, "a projection direction")),
        None => return Err(not_node(path, "a projection direction")),
    };
    let tag = match direction {
        ProjectionDirection::GuestToHost => "guest-to-host",
        ProjectionDirection::HostToGuest => "host-to-guest",
        ProjectionDirection::Both => "bidirectional",
    };
    expect_node(value, tag, Some(0), path.into())?;
    Ok(direction)
}

fn decode_projection_rule(value: RhoValue, path: &str) -> Result<ProjectionRule, DdlValueError> {
    let fields = expect_node(value, "projection-rule", Some(5), path.into())?;
    let mut fields = fields.into_iter();
    let mut head = expect_node(
        fields.next().expect("arity checked"),
        "projection-head",
        Some(2),
        format!("{path}.head"),
    )?
    .into_iter();
    let name = expect_string(head.next().expect("arity checked"), format!("{path}.name"))?;
    let bindings =
        expect_sequence(head.next().expect("arity checked"), &format!("{path}.bindings"))?
            .into_iter()
            .enumerate()
            .map(|(index, binding)| {
                decode_projection_binding(binding, &format!("{path}.bindings[{index}]"))
            })
            .collect::<Result<Vec<_>, _>>()?;
    let premises_value = fields.next().expect("arity checked");
    let premises = if node_tag(&premises_value) == Some("projection-premises") {
        let mut fields = expect_node(
            premises_value,
            "projection-premises",
            Some(1),
            format!("{path}.premises"),
        )?;
        expect_sequence(fields.pop().expect("arity checked"), &format!("{path}.premises"))?
    } else {
        expect_sequence(premises_value, &format!("{path}.premises"))?
    }
    .into_iter()
    .enumerate()
    .map(|(index, premise)| {
        decode_projection_premise(premise, &format!("{path}.premises[{index}]"))
    })
    .collect::<Result<Vec<_>, _>>()?;
    let guest = fields.next().expect("arity checked");
    validate_projection_term(&guest, &format!("{path}.guest"))?;
    let direction = decode_projection_direction(
        fields.next().expect("arity checked"),
        &format!("{path}.direction"),
    )?;
    let host = fields.next().expect("arity checked");
    validate_projection_term(&host, &format!("{path}.host"))?;
    Ok(ProjectionRule {
        name,
        bindings,
        premises,
        guest,
        host,
        direction,
        span: SYNTHETIC_SPAN,
    })
}

fn decode_projection_binding(
    value: RhoValue,
    path: &str,
) -> Result<ProjectionBinding, DdlValueError> {
    let is_host = node_tag(&value) == Some("projection-host-binding");
    let tag = if is_host {
        "projection-host-binding"
    } else {
        "projection-guest-binding"
    };
    let fields = expect_node(value, tag, Some(2), path.into())?;
    let mut fields = fields.into_iter();
    let name = expect_string(fields.next().expect("arity checked"), format!("{path}.name"))?;
    let category =
        expect_string(fields.next().expect("arity checked"), format!("{path}.category"))?;
    Ok(if is_host {
        ProjectionBinding::Host { name, category }
    } else {
        ProjectionBinding::Guest { name, category }
    })
}

fn decode_projection_premise(
    value: RhoValue,
    path: &str,
) -> Result<ProjectionPremise, DdlValueError> {
    match node_tag(&value) {
        Some("projection-call") => {
            let fields = expect_node(value, "projection-call", Some(3), path.into())?;
            let mut fields = fields.into_iter();
            Ok(ProjectionPremise::Call {
                name: expect_string(fields.next().expect("arity checked"), format!("{path}.name"))?,
                guest: expect_string(
                    fields.next().expect("arity checked"),
                    format!("{path}.guest"),
                )?,
                host: expect_string(fields.next().expect("arity checked"), format!("{path}.host"))?,
            })
        },
        Some("projection-transition") => {
            let (left, right) = decode_pair(value, "projection-transition", path)?;
            Ok(ProjectionPremise::Transition { left, right })
        },
        Some(tag) => Err(wrong_tag(path, tag, "a projection premise")),
        None => Err(not_node(path, "a projection premise")),
    }
}

pub(crate) fn validate_projection_term(value: &RhoValue, path: &str) -> Result<(), DdlValueError> {
    let mut pending = vec![(value, path.to_string(), 1usize)];
    while let Some((value, path, depth)) = pending.pop() {
        require_structural_depth(depth, &path, "projection term")?;
        let RhoValue::List(items) = value else {
            return Err(not_node(&path, "a projection term"));
        };
        let Some(RhoValue::String(tag)) = items.first() else {
            return Err(not_node(&path, "a projection term"));
        };
        let fields = &items[1..];
        let arity = match tag.as_str() {
            "ast-var" | "ast-remainder" | "ast-string" | "ast-integer" | "ast-collection" => 1,
            "ast-sexp" | "ast-host-sexp" | "ast-subst" | "ast-abs" => 2,
            "ast-boolean-true" | "ast-boolean-false" => 0,
            _ => return Err(wrong_tag(&path, tag, "a projection term")),
        };
        if fields.len() != arity {
            return Err(DdlValueError::new(
                path,
                format!("`{tag}` has arity {}; expected {arity}", fields.len()),
            ));
        }
        let child_depth = structural_child_depth(depth, &path)?;
        match tag.as_str() {
            "ast-var" | "ast-remainder" | "ast-string" => {
                if !matches!(fields[0], RhoValue::String(_)) {
                    return Err(DdlValueError::new(
                        path,
                        "projection term requires string content",
                    ));
                }
            },
            "ast-integer" => {
                if !matches!(fields[0], RhoValue::Integer(_)) {
                    return Err(DdlValueError::new(
                        path,
                        "projection integer requires integer content",
                    ));
                }
            },
            "ast-sexp" | "ast-host-sexp" | "ast-abs" => {
                if !matches!(fields[0], RhoValue::String(_)) {
                    return Err(DdlValueError::new(
                        path,
                        "projection label or binder must be a string",
                    ));
                }
                if tag == "ast-abs" {
                    pending.push((&fields[1], format!("{path}.body"), child_depth));
                } else {
                    let RhoValue::List(children) = &fields[1] else {
                        return Err(not_node(&format!("{path}.arguments"), "a sequence"));
                    };
                    if !matches!(children.first(), Some(RhoValue::String(t)) if t == "sequence") {
                        return Err(not_node(&format!("{path}.arguments"), "a sequence"));
                    }
                    pending.extend(
                        children[1..]
                            .iter()
                            .enumerate()
                            .rev()
                            .map(|(index, child)| {
                                (child, format!("{path}.arguments[{index}]"), child_depth)
                            }),
                    );
                }
            },
            "ast-subst" => {
                pending.push((&fields[1], format!("{path}.argument"), child_depth));
                pending.push((&fields[0], format!("{path}.body"), child_depth));
            },
            "ast-collection" => {
                let RhoValue::List(children) = &fields[0] else {
                    return Err(not_node(&format!("{path}.elements"), "a sequence"));
                };
                if !matches!(children.first(), Some(RhoValue::String(t)) if t == "sequence") {
                    return Err(not_node(&format!("{path}.elements"), "a sequence"));
                }
                pending.extend(
                    children[1..]
                        .iter()
                        .enumerate()
                        .rev()
                        .map(|(index, child)| {
                            (child, format!("{path}.elements[{index}]"), child_depth)
                        }),
                );
            },
            "ast-boolean-true" | "ast-boolean-false" => {},
            _ => unreachable!("closed projection term tags"),
        }
    }
    Ok(())
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

    fn limit_options(entries: &[(&str, i128)]) -> RhoValue {
        node(
            "options",
            vec![node(
                "sequence",
                vec![node(
                    "option-semantics-limits",
                    vec![node(
                        "sequence",
                        entries
                            .iter()
                            .map(|(name, value)| {
                                node(
                                    "limit-assignment",
                                    vec![
                                        RhoValue::String((*name).into()),
                                        RhoValue::String(value.to_string()),
                                    ],
                                )
                            })
                            .collect(),
                    )],
                )],
            )],
        )
    }

    #[test]
    fn authored_semantic_limits_project_to_the_existing_theory_core() {
        let names = [
            "max_rule_variables",
            "max_term_nodes",
            "max_premise_nodes",
            "max_proof_nodes",
            "max_frontier",
            "max_steps",
            "max_grade_bits",
            "max_output_nodes",
            "max_output_bytes",
        ];
        let entries: Vec<_> = names
            .iter()
            .enumerate()
            .map(|(index, name)| (*name, 100 + index as i128))
            .collect();
        let builder = decode_builder(limit_options(&entries), "$.options").unwrap();
        let declaration = TheoryDecl {
            name: "Limited".into(),
            params: Vec::new(),
            body: TheoryExpr::Build {
                base: Box::new(TheoryExpr::Empty(SYNTHETIC_SPAN)),
                builder,
                span: SYNTHETIC_SPAN,
            },
            span: SYNTHETIC_SPAN,
        };
        let language = crate::elaborate_theory_ast(declaration).unwrap();
        let limits = language.language_core.theory.limits;
        assert_eq!(limits.max_rule_variables, 100);
        assert_eq!(limits.max_term_nodes, 101);
        assert_eq!(limits.max_premise_nodes, 102);
        assert_eq!(limits.max_proof_nodes, 103);
        assert_eq!(limits.max_frontier, 104);
        assert_eq!(limits.max_steps, 105);
        assert_eq!(limits.max_grade_bits, 106);
        assert_eq!(limits.max_output_nodes, 107);
        assert_eq!(limits.max_output_bytes, 108);
    }

    #[test]
    fn authored_semantic_limits_reject_unknown_duplicate_and_out_of_range_fields() {
        assert!(decode_builder(limit_options(&[("max_steps", 0)]), "$.options").is_ok());
        assert!(
            decode_builder(limit_options(&[("max_steps", i128::from(u32::MAX))]), "$.options")
                .is_ok()
        );
        for entries in [
            vec![("unknown", 1)],
            vec![("max_steps", 1), ("max_steps", 1)],
            vec![("max_steps", -1)],
            vec![("max_steps", i128::from(u32::MAX) + 1)],
        ] {
            assert!(decode_builder(limit_options(&entries), "$.options").is_err());
        }
        let section = node("option-semantics-limits", vec![node("sequence", vec![])]);
        let duplicate = node("options", vec![node("sequence", vec![section.clone(), section])]);
        assert!(decode_builder(duplicate, "$.options").is_err());

        for malformed in [
            RhoValue::String("+1".into()),
            RhoValue::String("01".into()),
            RhoValue::Integer(1),
        ] {
            let assignment =
                node("limit-assignment", vec![RhoValue::String("max_steps".into()), malformed]);
            let section = node("option-semantics-limits", vec![node("sequence", vec![assignment])]);
            let options = node("options", vec![node("sequence", vec![section])]);
            assert!(decode_builder(options, "$.options").is_err());
        }
    }

    #[test]
    fn category_wire_tags_preserve_variable_admission_and_native_carrier() {
        for (tag, admits_variables, carrier) in [
            ("category", true, None),
            ("category-noadmit", false, None),
            ("category-carrier", true, Some("String")),
            ("category-noadmit-carrier", false, Some("String")),
        ] {
            let mut fields = vec![RhoValue::String("Text".into())];
            if let Some(carrier) = carrier {
                fields.push(RhoValue::String(carrier.into()));
            }
            let declaration = decode_cat_decl(node(tag, fields), "$.type")
                .expect("known structural category tag");
            assert_eq!(declaration.cat, "Text");
            assert_eq!(declaration.admits_variables, admits_variables);
            assert_eq!(declaration.carrier.as_deref(), carrier);
        }
        assert!(decode_cat_decl(
            node("category-carrier", vec![RhoValue::String("Text".into())]),
            "$.type"
        )
        .is_err());
    }

    #[test]
    fn attributed_term_wire_preserves_metadata_and_rejects_duplicate_or_unknown_fields() {
        let term = |attributes| {
            node(
                "term-attributed",
                vec![
                    RhoValue::String("Operator".into()),
                    node("sequence", vec![]),
                    node("sequence", vec![]),
                    RhoValue::String("Expr".into()),
                    node("sequence", attributes),
                ],
            )
        };
        let association = || node("term-attr-word", vec![RhoValue::String("nonassoc".into())]);
        let power = || {
            node(
                "term-attr-call",
                vec![RhoValue::String("prefix".into()), RhoValue::String("30".into())],
            )
        };
        let decoded = decode_term_rule(term(vec![association(), power()]), "$.term")
            .expect("typed term metadata decodes structurally");
        assert_eq!(decoded.associativity, Some(TermAssociativity::NonAssociative));
        assert_eq!(decoded.prefix_binding_power, Some(30));
        assert!(decode_term_rule(term(vec![association(), association()]), "$.term").is_err());
        assert!(decode_term_rule(term(vec![power(), power()]), "$.term").is_err());
        assert!(decode_term_rule(
            term(vec![node("term-attr-word", vec![RhoValue::String("unknown".into())])]),
            "$.term",
        )
        .is_err());
        assert!(decode_term_rule(term(vec![]), "$.term").is_err());
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
    fn projection_wire_preserves_guest_host_endpoints_and_direction() {
        let row = node(
            "projection-rule",
            vec![
                node(
                    "projection-head",
                    vec![RhoValue::String("Yes".into()), node("sequence", vec![])],
                ),
                node("sequence", vec![]),
                node("ast-sexp", vec![RhoValue::String("BTrue".into()), node("sequence", vec![])]),
                node("bidirectional", vec![]),
                node("ast-boolean-true", vec![]),
            ],
        );
        let group = node(
            "projection-group",
            vec![
                RhoValue::String("Boolean".into()),
                RhoValue::String("Bool".into()),
                node("bidirectional", vec![]),
                RhoValue::String("Bool".into()),
                node("sequence", vec![row]),
            ],
        );
        let RewriteEntry::Projection(projection) =
            decode_rewrite_entry(group.clone(), "$.rewrites[0]").expect("closed projection wire")
        else {
            panic!("projection must not become an ordinary guest rewrite")
        };
        assert_eq!(projection.name, "Boolean");
        assert_eq!(projection.guest, "Bool");
        assert_eq!(projection.host, "Bool");
        assert_eq!(projection.direction, ProjectionDirection::Both);
        let ProjectionBody::Rules(rows) = projection.body else {
            panic!("expected authored rows")
        };
        assert_eq!(rows.len(), 1);
        assert_eq!(rows[0].direction, ProjectionDirection::Both);
        assert_eq!(rows[0].host, node("ast-boolean-true", vec![]));

        let mut wrong = group;
        let RhoValue::List(fields) = &mut wrong else {
            unreachable!()
        };
        let RhoValue::List(rows) = &mut fields[5] else {
            unreachable!()
        };
        let RhoValue::List(row) = &mut rows[1] else {
            unreachable!()
        };
        row[4] = node("guest-to-host", vec![]);
        assert!(decode_rewrite_entry(wrong, "$.rewrites[0]").is_err());
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
