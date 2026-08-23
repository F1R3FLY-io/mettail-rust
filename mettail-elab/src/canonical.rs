//! Canonical Rholang-value projection and `GrammarCore` lowering.

use crate::ast::{Ast, Binding, CollKind, Equation, Item, RewriteDecl, Sort, TermRule};
use crate::lex::Span;
use crate::pres::{CatEntry, ElemId, EqEntry, Presentation, RwEntry, TermEntry};
use mettail_grammar_core as core;
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fmt;

/// The subset of ordinary Rholang values used by the `language/2` schema.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum RhoValue {
    Map(BTreeMap<String, RhoValue>),
    List(Vec<RhoValue>),
    String(String),
    Integer(i128),
    Boolean(bool),
    Nil,
}

impl RhoValue {
    pub fn canonical_bytes(&self) -> Vec<u8> {
        let mut output = Vec::new();
        encode_value(self, &mut output);
        output
    }

    pub fn fingerprint(&self) -> [u8; 32] {
        *blake3::hash(&self.canonical_bytes()).as_bytes()
    }
}

fn encode_value(value: &RhoValue, output: &mut Vec<u8>) {
    match value {
        RhoValue::Map(values) => {
            output.push(b'm');
            put_len(values.len(), output);
            for (key, value) in values {
                put_string(key, output);
                encode_value(value, output);
            }
        },
        RhoValue::List(values) => {
            output.push(b'l');
            put_len(values.len(), output);
            for value in values {
                encode_value(value, output);
            }
        },
        RhoValue::String(value) => {
            output.push(b's');
            put_string(value, output);
        },
        RhoValue::Integer(value) => {
            output.push(b'i');
            output.extend_from_slice(&value.to_be_bytes());
        },
        RhoValue::Boolean(value) => output.push(if *value { b't' } else { b'f' }),
        RhoValue::Nil => output.push(b'n'),
    }
}

fn put_len(value: usize, output: &mut Vec<u8>) {
    output.extend_from_slice(&(value as u64).to_be_bytes());
}

fn put_string(value: &str, output: &mut Vec<u8>) {
    put_len(value.len(), output);
    output.extend_from_slice(value.as_bytes());
}

fn map(entries: impl IntoIterator<Item = (&'static str, RhoValue)>) -> RhoValue {
    RhoValue::Map(
        entries
            .into_iter()
            .map(|(key, value)| (key.to_string(), value))
            .collect(),
    )
}

fn list(values: impl IntoIterator<Item = RhoValue>) -> RhoValue {
    RhoValue::List(values.into_iter().collect())
}

fn string(value: impl Into<String>) -> RhoValue {
    RhoValue::String(value.into())
}

/// Normalize an elaborated surface module to the data-structure-faithful
/// `language/2` value. Replacements and theory composition have already been
/// applied by elaboration, so the value contains their semantic result.
pub fn presentation_to_value(name: &str, presentation: &Presentation) -> RhoValue {
    let mut spec = BTreeMap::new();
    spec.insert("mettail".into(), string("language/2"));
    spec.insert("name".into(), string(name));
    spec.insert(
        "types".into(),
        list(
            presentation
                .types
                .iter()
                .map(|entry| string(entry.cat.clone())),
        ),
    );
    spec.insert(
        "exports".into(),
        list(
            presentation
                .exports
                .iter()
                .map(|(from, to)| list([string(from.clone()), string(to.clone())])),
        ),
    );
    spec.insert(
        "terms".into(),
        list(
            presentation
                .terms
                .iter()
                .map(|entry| term_to_value(&entry.rule)),
        ),
    );
    spec.insert(
        "equations".into(),
        list(
            presentation
                .equations
                .iter()
                .enumerate()
                .map(|(ordinal, entry)| {
                    map([
                        ("name", string(format!("equation/{ordinal}"))),
                        (
                            "premises",
                            list(entry.eq.freshness.iter().map(|(left, right)| {
                                list([string("fresh"), string(left.clone()), string(right.clone())])
                            })),
                        ),
                        ("left", ast_to_value(&entry.eq.lhs)),
                        ("right", ast_to_value(&entry.eq.rhs)),
                    ])
                }),
        ),
    );
    spec.insert(
        "rewrites".into(),
        list(presentation.rewrites.iter().map(|entry| {
            map([
                ("name", string(entry.rw.name.clone())),
                (
                    "premises",
                    list(entry.rw.premises.iter().map(|(left, right)| {
                        list([string("~>"), string(left.clone()), string(right.clone())])
                    })),
                ),
                ("left", ast_to_value(&entry.rw.lhs)),
                ("right", ast_to_value(&entry.rw.rhs)),
            ])
        })),
    );
    RhoValue::Map(spec)
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ValueDecodeError {
    pub path: String,
    pub message: String,
}

impl ValueDecodeError {
    fn new(path: impl Into<String>, message: impl Into<String>) -> Self {
        Self {
            path: path.into(),
            message: message.into(),
        }
    }
}

impl fmt::Display for ValueDecodeError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{}: {}", self.path, self.message)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ValueToCoreError {
    Decode(ValueDecodeError),
    Lower(LoweringError),
}

/// Decode the canonical ordinary-Rholang representation back to a
/// presentation. Unknown keys and malformed tagged lists are rejected rather
/// than ignored, so programmatically constructed grammars use the same closed
/// schema as the surface elaborator.
pub fn value_to_presentation(value: &RhoValue) -> Result<(String, Presentation), ValueDecodeError> {
    let spec = expect_map(value, "$".into())?;
    const KEYS: &[&str] =
        &["mettail", "name", "types", "exports", "terms", "equations", "rewrites"];
    if let Some(key) = spec.keys().find(|key| !KEYS.contains(&key.as_str())) {
        return Err(ValueDecodeError::new(format!("$.{key}"), "unknown key"));
    }
    let schema = expect_string(field(spec, "mettail", "$")?, "$.mettail".into())?;
    if schema != "language/2" {
        return Err(ValueDecodeError::new("$.mettail", format!("unsupported schema `{schema}`")));
    }
    let name = expect_string(field(spec, "name", "$")?, "$.name".into())?.to_string();
    let span = Span { line: 0, col: 0 };
    let types = expect_list(field(spec, "types", "$")?, "$.types".into())?
        .iter()
        .enumerate()
        .map(|(index, value)| {
            Ok(CatEntry {
                id: ElemId(index as u64 + 1),
                cat: expect_string(value, format!("$.types[{index}]"))?.to_string(),
                span,
            })
        })
        .collect::<Result<Vec<_>, ValueDecodeError>>()?;
    let exports = expect_list(field(spec, "exports", "$")?, "$.exports".into())?
        .iter()
        .enumerate()
        .map(|(index, value)| {
            let path = format!("$.exports[{index}]");
            let pair = expect_list(value, path.clone())?;
            require_len(pair, 2, &path)?;
            Ok((
                expect_string(&pair[0], format!("{path}[0]"))?.to_string(),
                expect_string(&pair[1], format!("{path}[1]"))?.to_string(),
            ))
        })
        .collect::<Result<Vec<_>, ValueDecodeError>>()?;
    let terms = expect_list(field(spec, "terms", "$")?, "$.terms".into())?
        .iter()
        .enumerate()
        .map(|(index, value)| {
            let path = format!("$.terms[{index}]");
            Ok(TermEntry {
                id: ElemId(types.len() as u64 + index as u64 + 1),
                rule: decode_term(value, &path)?,
                span,
            })
        })
        .collect::<Result<Vec<_>, ValueDecodeError>>()?;
    let equations = expect_list(field(spec, "equations", "$")?, "$.equations".into())?
        .iter()
        .enumerate()
        .map(|(index, value)| {
            let path = format!("$.equations[{index}]");
            let item = expect_map(value, path.clone())?;
            reject_unknown_keys(item, &["name", "premises", "left", "right"], &path)?;
            let _name = expect_string(field(item, "name", &path)?, format!("{path}.name"))?;
            Ok(EqEntry {
                id: ElemId(types.len() as u64 + terms.len() as u64 + index as u64 + 1),
                eq: Equation {
                    freshness: decode_pairs(
                        field(item, "premises", &path)?,
                        "fresh",
                        &format!("{path}.premises"),
                    )?,
                    lhs: decode_ast(field(item, "left", &path)?, &format!("{path}.left"))?,
                    rhs: decode_ast(field(item, "right", &path)?, &format!("{path}.right"))?,
                    span,
                },
            })
        })
        .collect::<Result<Vec<_>, ValueDecodeError>>()?;
    let rewrites = expect_list(field(spec, "rewrites", "$")?, "$.rewrites".into())?
        .iter()
        .enumerate()
        .map(|(index, value)| {
            let path = format!("$.rewrites[{index}]");
            let item = expect_map(value, path.clone())?;
            reject_unknown_keys(item, &["name", "premises", "left", "right"], &path)?;
            Ok(RwEntry {
                id: ElemId(
                    types.len() as u64
                        + terms.len() as u64
                        + equations.len() as u64
                        + index as u64
                        + 1,
                ),
                rw: RewriteDecl {
                    name: expect_string(field(item, "name", &path)?, format!("{path}.name"))?
                        .to_string(),
                    premises: decode_pairs(
                        field(item, "premises", &path)?,
                        "~>",
                        &format!("{path}.premises"),
                    )?,
                    lhs: decode_ast(field(item, "left", &path)?, &format!("{path}.left"))?,
                    rhs: decode_ast(field(item, "right", &path)?, &format!("{path}.right"))?,
                    span,
                },
            })
        })
        .collect::<Result<Vec<_>, ValueDecodeError>>()?;
    Ok((
        name,
        Presentation {
            types,
            exports,
            terms,
            equations,
            rewrites,
        },
    ))
}

pub fn value_to_core(value: &RhoValue) -> Result<core::GrammarCoreV1, ValueToCoreError> {
    let (name, presentation) = value_to_presentation(value).map_err(ValueToCoreError::Decode)?;
    let mut core = presentation_to_core(&name, &presentation).map_err(ValueToCoreError::Lower)?;
    core.provenance.frontend = "rholang-language/2".into();
    Ok(core)
}

/// Decode a `Data(v)` fragment through the canonical schema. The two
/// whole-language identity keys are forbidden; all other supported fields are
/// decoded exactly as they are on the direct registry-value path.
pub fn partial_value_to_presentation(value: &RhoValue) -> Result<Presentation, ValueDecodeError> {
    let fragment = expect_map(value, "Data".into())?;
    if let Some(key) = fragment
        .keys()
        .find(|key| matches!(key.as_str(), "mettail" | "name"))
    {
        return Err(ValueDecodeError::new(
            format!("Data.{key}"),
            "whole-language identity keys are not permitted in Data(v)",
        ));
    }
    let mut complete = BTreeMap::from([
        ("mettail".into(), string("language/2")),
        ("name".into(), string("DataFragment")),
        ("types".into(), list([])),
        ("exports".into(), list([])),
        ("terms".into(), list([])),
        ("equations".into(), list([])),
        ("rewrites".into(), list([])),
    ]);
    for (key, value) in fragment {
        if !complete.contains_key(key) {
            return Err(ValueDecodeError::new(format!("Data.{key}"), "unknown key"));
        }
        complete.insert(key.clone(), value.clone());
    }
    value_to_presentation(&RhoValue::Map(complete)).map(|(_, presentation)| presentation)
}

fn decode_term(value: &RhoValue, path: &str) -> Result<TermRule, ValueDecodeError> {
    let item = expect_map(value, path.into())?;
    reject_unknown_keys(item, &["label", "category", "context", "syntax"], path)?;
    Ok(TermRule {
        label: expect_string(field(item, "label", path)?, format!("{path}.label"))?.to_string(),
        result: expect_string(field(item, "category", path)?, format!("{path}.category"))?
            .to_string(),
        context: expect_list(field(item, "context", path)?, format!("{path}.context"))?
            .iter()
            .enumerate()
            .map(|(index, value)| decode_binding(value, &format!("{path}.context[{index}]")))
            .collect::<Result<Vec<_>, _>>()?,
        syntax: expect_list(field(item, "syntax", path)?, format!("{path}.syntax"))?
            .iter()
            .enumerate()
            .map(|(index, value)| decode_item(value, &format!("{path}.syntax[{index}]")))
            .collect::<Result<Vec<_>, _>>()?,
        span: Span { line: 0, col: 0 },
    })
}

fn decode_binding(value: &RhoValue, path: &str) -> Result<Binding, ValueDecodeError> {
    let values = expect_list(value, path.into())?;
    let tag = values
        .first()
        .ok_or_else(|| ValueDecodeError::new(path, "empty binding"))?;
    match expect_string(tag, format!("{path}[0]"))? {
        "param" => {
            require_len(values, 3, path)?;
            Ok(Binding::Plain {
                name: expect_string(&values[1], format!("{path}[1]"))?.to_string(),
                sort: decode_sort(&values[2], &format!("{path}[2]"))?,
                span: Span { line: 0, col: 0 },
            })
        },
        "binder" => {
            require_len(values, 4, path)?;
            let arrow = expect_list(&values[3], format!("{path}[3]"))?;
            require_len(arrow, 3, &format!("{path}[3]"))?;
            if expect_string(&arrow[0], format!("{path}[3][0]"))? != "arrow" {
                return Err(ValueDecodeError::new(format!("{path}[3][0]"), "expected `arrow`"));
            }
            Ok(Binding::Binder {
                binder: expect_string(&values[1], format!("{path}[1]"))?.to_string(),
                body: expect_string(&values[2], format!("{path}[2]"))?.to_string(),
                from: expect_string(&arrow[1], format!("{path}[3][1]"))?.to_string(),
                to: expect_string(&arrow[2], format!("{path}[3][2]"))?.to_string(),
                span: Span { line: 0, col: 0 },
            })
        },
        other => Err(ValueDecodeError::new(path, format!("unknown binding tag `{other}`"))),
    }
}

fn decode_sort(value: &RhoValue, path: &str) -> Result<Sort, ValueDecodeError> {
    if let RhoValue::String(category) = value {
        return Ok(Sort::Cat(category.clone()));
    }
    let values = expect_list(value, path.into())?;
    require_len(values, 2, path)?;
    let kind = match expect_string(&values[0], format!("{path}[0]"))? {
        "bag" => CollKind::HashBag,
        "set" => CollKind::Set,
        "vec" => CollKind::List,
        other => return Err(ValueDecodeError::new(path, format!("unknown sort tag `{other}`"))),
    };
    Ok(Sort::Coll {
        kind,
        of: expect_string(&values[1], format!("{path}[1]"))?.to_string(),
    })
}

fn decode_item(value: &RhoValue, path: &str) -> Result<Item, ValueDecodeError> {
    if let RhoValue::String(argument) = value {
        return Ok(Item::ArgRef(argument.clone()));
    }
    let values = expect_list(value, path.into())?;
    let tag = expect_string(
        values
            .first()
            .ok_or_else(|| ValueDecodeError::new(path, "empty syntax item"))?,
        format!("{path}[0]"),
    )?;
    match tag {
        "lit" => {
            require_len(values, 2, path)?;
            Ok(Item::Terminal(expect_string(&values[1], format!("{path}[1]"))?.to_string()))
        },
        "sep" => {
            require_len(values, 3, path)?;
            Ok(Item::Projection {
                arg: expect_string(&values[1], format!("{path}[1]"))?.to_string(),
                sep: expect_string(&values[2], format!("{path}[2]"))?.to_string(),
            })
        },
        other => Err(ValueDecodeError::new(path, format!("unknown syntax tag `{other}`"))),
    }
}

fn decode_pairs(
    value: &RhoValue,
    expected_tag: &str,
    path: &str,
) -> Result<Vec<(String, String)>, ValueDecodeError> {
    expect_list(value, path.into())?
        .iter()
        .enumerate()
        .map(|(index, value)| {
            let item_path = format!("{path}[{index}]");
            let values = expect_list(value, item_path.clone())?;
            require_len(values, 3, &item_path)?;
            if expect_string(&values[0], format!("{item_path}[0]"))? != expected_tag {
                return Err(ValueDecodeError::new(
                    format!("{item_path}[0]"),
                    format!("expected `{expected_tag}`"),
                ));
            }
            Ok((
                expect_string(&values[1], format!("{item_path}[1]"))?.to_string(),
                expect_string(&values[2], format!("{item_path}[2]"))?.to_string(),
            ))
        })
        .collect()
}

fn decode_ast(value: &RhoValue, path: &str) -> Result<Ast, ValueDecodeError> {
    let span = Span { line: 0, col: 0 };
    if let RhoValue::String(name) = value {
        return Ok(Ast::Var(name.clone(), span));
    }
    let values = expect_list(value, path.into())?;
    let tag = expect_string(
        values
            .first()
            .ok_or_else(|| ValueDecodeError::new(path, "empty AST node"))?,
        format!("{path}[0]"),
    )?;
    match tag {
        "eval" => {
            require_len(values, 3, path)?;
            Ok(Ast::Subst(
                Box::new(decode_ast(&values[1], &format!("{path}[1]"))?),
                Box::new(decode_ast(&values[2], &format!("{path}[2]"))?),
                span,
            ))
        },
        "^" => {
            require_len(values, 3, path)?;
            Ok(Ast::Abs(
                expect_string(&values[1], format!("{path}[1]"))?.to_string(),
                Box::new(decode_ast(&values[2], &format!("{path}[2]"))?),
                span,
            ))
        },
        "coll" => {
            require_len(values, 3, path)?;
            let mut elements = expect_list(&values[1], format!("{path}[1]"))?
                .iter()
                .enumerate()
                .map(|(index, value)| decode_ast(value, &format!("{path}[1][{index}]")))
                .collect::<Result<Vec<_>, _>>()?;
            match &values[2] {
                RhoValue::Nil => {},
                RhoValue::String(name) => elements.push(Ast::Remainder(name.clone(), span)),
                _ => {
                    return Err(ValueDecodeError::new(
                        format!("{path}[2]"),
                        "expected remainder name or Nil",
                    ))
                },
            }
            Ok(Ast::Coll(elements, span))
        },
        label => Ok(Ast::SExp(
            label.to_string(),
            values[1..]
                .iter()
                .enumerate()
                .map(|(index, value)| decode_ast(value, &format!("{path}[{}]", index + 1)))
                .collect::<Result<Vec<_>, _>>()?,
            span,
        )),
    }
}

fn field<'a>(
    map: &'a BTreeMap<String, RhoValue>,
    key: &str,
    path: &str,
) -> Result<&'a RhoValue, ValueDecodeError> {
    map.get(key)
        .ok_or_else(|| ValueDecodeError::new(format!("{path}.{key}"), "missing required field"))
}

fn expect_map(
    value: &RhoValue,
    path: String,
) -> Result<&BTreeMap<String, RhoValue>, ValueDecodeError> {
    match value {
        RhoValue::Map(value) => Ok(value),
        _ => Err(ValueDecodeError::new(path, "expected map")),
    }
}

fn expect_list(value: &RhoValue, path: String) -> Result<&[RhoValue], ValueDecodeError> {
    match value {
        RhoValue::List(value) => Ok(value),
        _ => Err(ValueDecodeError::new(path, "expected list")),
    }
}

fn expect_string(value: &RhoValue, path: String) -> Result<&str, ValueDecodeError> {
    match value {
        RhoValue::String(value) => Ok(value),
        _ => Err(ValueDecodeError::new(path, "expected string")),
    }
}

fn require_len(values: &[RhoValue], expected: usize, path: &str) -> Result<(), ValueDecodeError> {
    if values.len() == expected {
        Ok(())
    } else {
        Err(ValueDecodeError::new(
            path,
            format!("expected {expected} items, found {}", values.len()),
        ))
    }
}

fn reject_unknown_keys(
    map: &BTreeMap<String, RhoValue>,
    allowed: &[&str],
    path: &str,
) -> Result<(), ValueDecodeError> {
    if let Some(key) = map.keys().find(|key| !allowed.contains(&key.as_str())) {
        Err(ValueDecodeError::new(format!("{path}.{key}"), "unknown key"))
    } else {
        Ok(())
    }
}

fn term_to_value(rule: &TermRule) -> RhoValue {
    map([
        ("label", string(rule.label.clone())),
        ("category", string(rule.result.clone())),
        ("context", list(rule.context.iter().map(binding_to_value))),
        ("syntax", list(rule.syntax.iter().map(item_to_value))),
    ])
}

fn binding_to_value(binding: &Binding) -> RhoValue {
    match binding {
        Binding::Plain { name, sort, .. } => {
            list([string("param"), string(name.clone()), sort_to_value(sort)])
        },
        Binding::Binder { binder, body, from, to, .. } => list([
            string("binder"),
            string(binder.clone()),
            string(body.clone()),
            list([string("arrow"), string(from.clone()), string(to.clone())]),
        ]),
    }
}

fn sort_to_value(sort: &Sort) -> RhoValue {
    match sort {
        Sort::Cat(category) => string(category.clone()),
        Sort::Coll { kind, of } => list([
            string(match kind {
                CollKind::HashBag => "bag",
                CollKind::Set => "set",
                CollKind::List => "vec",
            }),
            string(of.clone()),
        ]),
    }
}

fn item_to_value(item: &Item) -> RhoValue {
    match item {
        Item::Terminal(text) => list([string("lit"), string(text.clone())]),
        Item::ArgRef(name) => string(name.clone()),
        Item::Projection { arg, sep } => {
            list([string("sep"), string(arg.clone()), string(sep.clone())])
        },
    }
}

fn ast_to_value(ast: &Ast) -> RhoValue {
    match ast {
        Ast::Var(name, _) => string(name.clone()),
        Ast::SExp(label, arguments, _) => {
            let mut node = Vec::with_capacity(arguments.len() + 1);
            node.push(string(label.clone()));
            node.extend(arguments.iter().map(ast_to_value));
            list(node)
        },
        Ast::Subst(abstraction, argument, _) => {
            list([string("eval"), ast_to_value(abstraction), ast_to_value(argument)])
        },
        Ast::Abs(binder, body, _) => {
            list([string("^"), string(binder.clone()), ast_to_value(body)])
        },
        Ast::Coll(elements, _) => {
            list([string("coll"), list(elements.iter().map(ast_to_value)), RhoValue::Nil])
        },
        Ast::Remainder(name, _) => {
            list([string("coll"), list(std::iter::empty()), string(name.clone())])
        },
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LoweringError {
    UnknownCategory(String),
    UnknownArgument { rule: String, argument: String },
    ProjectionOfNonCollection { rule: String, argument: String },
    DuplicateArgument { rule: String, argument: String },
    InvalidCore(Vec<core::ValidationError>),
}

/// Lower an elaborated presentation into the backend-neutral parser IR.
pub fn presentation_to_core(
    name: &str,
    presentation: &Presentation,
) -> Result<core::GrammarCoreV1, LoweringError> {
    let mut output = core::GrammarCoreV1::new(name);
    output.provenance.frontend = "mettail-module/theory-v1".into();
    output.categories = presentation
        .types
        .iter()
        .enumerate()
        .map(|(index, entry)| core::Category {
            id: core::CategoryId(index as u32),
            name: entry.cat.clone(),
            carrier: core::Carrier::Dynamic,
            primary: index == 0,
            admits_variables: true,
        })
        .collect();
    let category_ids: HashMap<&str, core::CategoryId> = output
        .categories
        .iter()
        .map(|category| (category.name.as_str(), category.id))
        .collect();

    let mut terminals = BTreeSet::new();
    for entry in &presentation.terms {
        for item in &entry.rule.syntax {
            if let Item::Terminal(text) = item {
                terminals.insert(text.clone());
            }
        }
    }
    output.tokens.push(core::TokenDefinition {
        id: core::TokenId(0),
        name: "Identifier".into(),
        pattern: core::TokenPattern::Builtin(core::BuiltinToken::Identifier),
        priority: 0,
        mode: core::ModeId(0),
        channel: "main".into(),
        transition: core::ModeTransition::default(),
        decoder: core::TokenDecoder::Text,
        reservation: core::Reservation::None,
    });
    let mut terminal_ids = HashMap::new();
    for text in terminals {
        let id = core::TokenId(output.tokens.len() as u32);
        terminal_ids.insert(text.clone(), id);
        output.tokens.push(core::TokenDefinition {
            id,
            name: format!("literal/{text}"),
            pattern: core::TokenPattern::Literal(text),
            priority: 1,
            mode: core::ModeId(0),
            channel: "main".into(),
            transition: core::ModeTransition::default(),
            decoder: core::TokenDecoder::Unit,
            reservation: core::Reservation::Contextual,
        });
    }
    output.modes[0].token_ids = output.tokens.iter().map(|token| token.id).collect();

    for (index, entry) in presentation.terms.iter().enumerate() {
        let rule = &entry.rule;
        let result = *category_ids
            .get(rule.result.as_str())
            .ok_or_else(|| LoweringError::UnknownCategory(rule.result.clone()))?;
        let arguments = argument_table(rule, &category_ids)?;
        let mut syntax = Vec::new();
        for item in &rule.syntax {
            match item {
                Item::Terminal(text) => {
                    syntax.push(core::SyntaxItem::Token(terminal_ids[text]));
                },
                Item::ArgRef(argument) => {
                    let descriptor = arguments.get(argument.as_str()).ok_or_else(|| {
                        LoweringError::UnknownArgument {
                            rule: rule.label.clone(),
                            argument: argument.clone(),
                        }
                    })?;
                    syntax.push(match descriptor {
                        Argument::Category(category) => core::SyntaxItem::Category {
                            category: *category,
                            slot: argument.clone(),
                        },
                        Argument::Identifier => {
                            core::SyntaxItem::CaptureIdent { slot: argument.clone() }
                        },
                        Argument::Collection { element, kind } => core::SyntaxItem::Collection {
                            slot: argument.clone(),
                            element: *element,
                            separator: String::new(),
                            kind: *kind,
                            key_value_separator: None,
                        },
                    });
                },
                Item::Projection { arg, sep } => {
                    let descriptor = arguments.get(arg.as_str()).ok_or_else(|| {
                        LoweringError::UnknownArgument {
                            rule: rule.label.clone(),
                            argument: arg.clone(),
                        }
                    })?;
                    let Argument::Collection { element, kind } = descriptor else {
                        return Err(LoweringError::ProjectionOfNonCollection {
                            rule: rule.label.clone(),
                            argument: arg.clone(),
                        });
                    };
                    syntax.push(core::SyntaxItem::Collection {
                        slot: arg.clone(),
                        element: *element,
                        separator: sep.clone(),
                        kind: *kind,
                        key_value_separator: None,
                    });
                },
            }
        }
        let constructor = core::ConstructorId(index as u32);
        let input_arity = rule.context.len() as u16;
        output.reductions.push(core::ReductionPlan {
            output_category: result,
            constructor,
            input_arity,
            fields: (0..input_arity).map(core::FieldSource::Input).collect(),
        });
        output.productions.push(core::Production {
            id: core::ProductionId(index as u32),
            constructor,
            label: rule.label.clone(),
            result,
            syntax,
            precedence: core::Precedence::default(),
            classification: core::ProductionClass {
                binder: rule
                    .context
                    .iter()
                    .any(|binding| matches!(binding, Binding::Binder { .. })),
                collection: rule.context.iter().any(|binding| {
                    matches!(binding, Binding::Plain { sort: Sort::Coll { .. }, .. })
                }),
                ..core::ProductionClass::default()
            },
            reduction: index as u32,
            provenance: Some(core::SourceProvenance {
                uri: None,
                line: rule.span.line,
                column: rule.span.col,
            }),
        });
    }

    let constructors: HashMap<&str, core::ConstructorId> = output
        .productions
        .iter()
        .map(|production| (production.label.as_str(), production.constructor))
        .collect();
    for equation in &presentation.equations {
        let mut labels = Vec::new();
        equation.eq.lhs.labels(&mut labels);
        equation.eq.rhs.labels(&mut labels);
        output.semantic_dependencies.push(
            labels
                .iter()
                .filter_map(|label| constructors.get(label.as_str()).copied())
                .collect(),
        );
    }
    for rewrite in &presentation.rewrites {
        let mut labels = Vec::new();
        rewrite.rw.lhs.labels(&mut labels);
        rewrite.rw.rhs.labels(&mut labels);
        output.semantic_dependencies.push(
            labels
                .iter()
                .filter_map(|label| constructors.get(label.as_str()).copied())
                .collect(),
        );
    }
    output.validate().map_err(LoweringError::InvalidCore)?;
    Ok(output)
}

#[derive(Clone, Copy)]
enum Argument {
    Category(core::CategoryId),
    Identifier,
    Collection {
        element: core::CategoryId,
        kind: core::CollectionKind,
    },
}

fn argument_table<'a>(
    rule: &'a TermRule,
    categories: &HashMap<&str, core::CategoryId>,
) -> Result<HashMap<&'a str, Argument>, LoweringError> {
    let mut output = HashMap::new();
    for binding in &rule.context {
        match binding {
            Binding::Plain { name, sort, .. } => {
                let argument = match sort {
                    Sort::Cat(category) => Argument::Category(
                        *categories
                            .get(category.as_str())
                            .ok_or_else(|| LoweringError::UnknownCategory(category.clone()))?,
                    ),
                    Sort::Coll { kind, of } => Argument::Collection {
                        element: *categories
                            .get(of.as_str())
                            .ok_or_else(|| LoweringError::UnknownCategory(of.clone()))?,
                        kind: match kind {
                            CollKind::HashBag => core::CollectionKind::Bag,
                            CollKind::Set => core::CollectionKind::Set,
                            CollKind::List => core::CollectionKind::List,
                        },
                    },
                };
                if output.insert(name.as_str(), argument).is_some() {
                    return Err(LoweringError::DuplicateArgument {
                        rule: rule.label.clone(),
                        argument: name.clone(),
                    });
                }
            },
            Binding::Binder { binder, body, to, .. } => {
                let category = *categories
                    .get(to.as_str())
                    .ok_or_else(|| LoweringError::UnknownCategory(to.clone()))?;
                for (name, argument) in [
                    (binder.as_str(), Argument::Identifier),
                    (body.as_str(), Argument::Category(category)),
                ] {
                    if output.insert(name, argument).is_some() {
                        return Err(LoweringError::DuplicateArgument {
                            rule: rule.label.clone(),
                            argument: name.to_string(),
                        });
                    }
                }
            },
        }
    }
    Ok(output)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lex::Span;
    use crate::pres::{CatEntry, ElemId, TermEntry};

    #[test]
    fn module_result_has_language_2_value_and_valid_core() {
        let span = Span { line: 1, col: 1 };
        let presentation = Presentation {
            types: vec![CatEntry { id: ElemId(1), cat: "Expr".into(), span }],
            terms: vec![TermEntry {
                id: ElemId(2),
                rule: TermRule {
                    label: "Zero".into(),
                    context: Vec::new(),
                    syntax: vec![Item::Terminal("0".into())],
                    result: "Expr".into(),
                    span,
                },
                span,
            }],
            ..Presentation::default()
        };
        let value = presentation_to_value("Tiny", &presentation);
        let RhoValue::Map(map) = value else {
            panic!("spec must be a map")
        };
        assert_eq!(map.get("mettail"), Some(&string("language/2")));
        let core = presentation_to_core("Tiny", &presentation).expect("valid core");
        let value = presentation_to_value("Tiny", &presentation);
        let decoded = value_to_core(&value).expect("canonical value lowers");
        assert_eq!(
            core.fingerprint().expect("surface fingerprint"),
            decoded.fingerprint().expect("value fingerprint")
        );
        assert_eq!(core.productions.len(), 1);
    }
}
