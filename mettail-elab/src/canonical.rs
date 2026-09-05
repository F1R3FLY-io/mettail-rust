//! Canonical Rholang-value projection and `GrammarCore` lowering.

use crate::ast::{Ast, Binding, CollKind, Equation, Item, RewriteDecl, Sort, TermRule};
use crate::lex::Span;
use crate::pres::{CatEntry, ElemId, EqEntry, Presentation, RwEntry, TermEntry};
use mettail_grammar_core as core;
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fmt;

/// The subset of ordinary Rholang values used by the `language/2` schema.
pub enum RhoValue {
    Map(BTreeMap<String, RhoValue>),
    List(Vec<RhoValue>),
    String(String),
    Bytes(Vec<u8>),
    Integer(i128),
    FloatBits(u64),
    Boolean(bool),
    Nil,
}

impl Clone for RhoValue {
    fn clone(&self) -> Self {
        enum Task<'a> {
            Visit(&'a RhoValue),
            FinishList(usize),
            FinishMap(Vec<&'a str>),
        }

        let mut tasks = vec![Task::Visit(self)];
        let mut values = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                Task::Visit(RhoValue::Map(map)) => {
                    let keys: Vec<_> = map.keys().map(String::as_str).collect();
                    tasks.push(Task::FinishMap(keys));
                    tasks.extend(map.values().rev().map(Task::Visit));
                },
                Task::Visit(RhoValue::List(list)) => {
                    tasks.push(Task::FinishList(list.len()));
                    tasks.extend(list.iter().rev().map(Task::Visit));
                },
                Task::Visit(RhoValue::String(value)) => {
                    values.push(RhoValue::String(value.clone()));
                },
                Task::Visit(RhoValue::Bytes(value)) => values.push(RhoValue::Bytes(value.clone())),
                Task::Visit(RhoValue::Integer(value)) => values.push(RhoValue::Integer(*value)),
                Task::Visit(RhoValue::FloatBits(bits)) => values.push(RhoValue::FloatBits(*bits)),
                Task::Visit(RhoValue::Boolean(value)) => values.push(RhoValue::Boolean(*value)),
                Task::Visit(RhoValue::Nil) => values.push(RhoValue::Nil),
                Task::FinishList(length) => {
                    let start = values.len() - length;
                    let children = values.drain(start..).collect();
                    values.push(RhoValue::List(children));
                },
                Task::FinishMap(keys) => {
                    let start = values.len() - keys.len();
                    let children: Vec<_> = values.drain(start..).collect();
                    values.push(RhoValue::Map(
                        keys.into_iter().map(str::to_string).zip(children).collect(),
                    ));
                },
            }
        }
        values
            .pop()
            .expect("RhoValue clone machine produces one value")
    }
}

impl PartialEq for RhoValue {
    fn eq(&self, other: &Self) -> bool {
        let mut work = vec![(self, other)];
        while let Some((left, right)) = work.pop() {
            match (left, right) {
                (RhoValue::Map(left), RhoValue::Map(right)) => {
                    if left.len() != right.len() {
                        return false;
                    }
                    for ((left_key, left_value), (right_key, right_value)) in
                        left.iter().zip(right.iter()).rev()
                    {
                        if left_key != right_key {
                            return false;
                        }
                        work.push((left_value, right_value));
                    }
                },
                (RhoValue::List(left), RhoValue::List(right)) => {
                    if left.len() != right.len() {
                        return false;
                    }
                    work.extend(left.iter().zip(right.iter()).rev());
                },
                (RhoValue::String(left), RhoValue::String(right)) if left == right => {},
                (RhoValue::Bytes(left), RhoValue::Bytes(right)) if left == right => {},
                (RhoValue::Integer(left), RhoValue::Integer(right)) if left == right => {},
                (RhoValue::FloatBits(left), RhoValue::FloatBits(right)) if left == right => {},
                (RhoValue::Boolean(left), RhoValue::Boolean(right)) if left == right => {},
                (RhoValue::Nil, RhoValue::Nil) => {},
                _ => return false,
            }
        }
        true
    }
}

impl Eq for RhoValue {}

impl Ord for RhoValue {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.canonical_bytes().cmp(&other.canonical_bytes())
    }
}

impl PartialOrd for RhoValue {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl fmt::Debug for RhoValue {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        enum Task<'a> {
            Value(&'a RhoValue),
            Key(&'a str),
            Text(&'static str),
        }

        let mut tasks = vec![Task::Value(self)];
        while let Some(task) = tasks.pop() {
            match task {
                Task::Text(text) => formatter.write_str(text)?,
                Task::Key(key) => write!(formatter, "{key:?}")?,
                Task::Value(RhoValue::Map(values)) => {
                    formatter.write_str("Map({")?;
                    tasks.push(Task::Text("})"));
                    for (index, (key, value)) in values.iter().enumerate().rev() {
                        tasks.push(Task::Value(value));
                        tasks.push(Task::Text(": "));
                        tasks.push(Task::Key(key));
                        if index > 0 {
                            tasks.push(Task::Text(", "));
                        }
                    }
                },
                Task::Value(RhoValue::List(values)) => {
                    formatter.write_str("List([")?;
                    tasks.push(Task::Text("])"));
                    for (index, value) in values.iter().enumerate().rev() {
                        tasks.push(Task::Value(value));
                        if index > 0 {
                            tasks.push(Task::Text(", "));
                        }
                    }
                },
                Task::Value(RhoValue::String(value)) => {
                    write!(formatter, "String({value:?})")?;
                },
                Task::Value(RhoValue::Bytes(value)) => {
                    write!(formatter, "Bytes({value:?})")?;
                },
                Task::Value(RhoValue::Integer(value)) => {
                    write!(formatter, "Integer({value:?})")?;
                },
                Task::Value(RhoValue::FloatBits(value)) => {
                    write!(formatter, "FloatBits({value:?})")?;
                },
                Task::Value(RhoValue::Boolean(value)) => {
                    write!(formatter, "Boolean({value:?})")?;
                },
                Task::Value(RhoValue::Nil) => formatter.write_str("Nil")?,
            }
        }
        Ok(())
    }
}

impl Drop for RhoValue {
    fn drop(&mut self) {
        let mut work = Vec::new();
        detach_rho_children(self, &mut work);
        while let Some(mut value) = work.pop() {
            detach_rho_children(&mut value, &mut work);
        }
    }
}

fn detach_rho_children(value: &mut RhoValue, work: &mut Vec<RhoValue>) {
    match value {
        RhoValue::Map(values) => {
            work.extend(std::mem::take(values).into_values());
        },
        RhoValue::List(values) => work.append(values),
        RhoValue::String(_)
        | RhoValue::Bytes(_)
        | RhoValue::Integer(_)
        | RhoValue::FloatBits(_)
        | RhoValue::Boolean(_)
        | RhoValue::Nil => {},
    }
}

pub const MAX_CANONICAL_VALUE_NODES: usize = 1_000_000;
pub const MAX_CANONICAL_COLLECTION_ITEMS: usize = 1_000_000;
pub const MAX_CANONICAL_STRING_BYTES: usize = 4 * 1024 * 1024;
pub const MAX_CANONICAL_TOTAL_STRING_BYTES: usize = 16 * 1024 * 1024;
pub const MAX_CANONICAL_BYTE_ARRAY_BYTES: usize = 16 * 1024 * 1024;
pub const MAX_CANONICAL_TOTAL_BYTE_ARRAY_BYTES: usize = 64 * 1024 * 1024;

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
    enum Task<'a> {
        Value(&'a RhoValue),
        Key(&'a str),
    }

    let mut tasks = vec![Task::Value(value)];
    while let Some(task) = tasks.pop() {
        match task {
            Task::Key(key) => put_string(key, output),
            Task::Value(RhoValue::Map(values)) => {
                output.push(b'm');
                put_len(values.len(), output);
                for (key, value) in values.iter().rev() {
                    tasks.push(Task::Value(value));
                    tasks.push(Task::Key(key));
                }
            },
            Task::Value(RhoValue::List(values)) => {
                output.push(b'l');
                put_len(values.len(), output);
                tasks.extend(values.iter().rev().map(Task::Value));
            },
            Task::Value(RhoValue::String(value)) => {
                output.push(b's');
                put_string(value, output);
            },
            Task::Value(RhoValue::Bytes(value)) => {
                output.push(b'b');
                put_len(value.len(), output);
                output.extend_from_slice(value);
            },
            Task::Value(RhoValue::Integer(value)) => {
                output.push(b'i');
                output.extend_from_slice(&value.to_be_bytes());
            },
            Task::Value(RhoValue::FloatBits(bits)) => {
                output.push(b'd');
                output.extend_from_slice(&bits.to_be_bytes());
            },
            Task::Value(RhoValue::Boolean(value)) => {
                output.push(if *value { b't' } else { b'f' });
            },
            Task::Value(RhoValue::Nil) => output.push(b'n'),
        }
    }
}

/// Admit an ordinary Rholang value before any schema-specific traversal.
/// This is shared by direct values, `Data(v)`, and Registry-resolved values.
pub fn admit_canonical_value(value: &RhoValue) -> Result<(), ValueDecodeError> {
    admit_canonical_value_impl(value, true)
}

/// Charge every resource in a structural DDL envelope without treating its
/// fixed ABI lists and tags as recursive grammar constructors.
///
/// The wire decoder must subsequently enforce the semantic DDL depth and call
/// [`admit_canonical_value`] for every opaque `Data(v)` payload. Keeping this
/// function crate-private prevents schema decoders from accidentally bypassing
/// canonical-value depth admission.
pub(crate) fn admit_canonical_value_resources(value: &RhoValue) -> Result<(), ValueDecodeError> {
    admit_canonical_value_impl(value, false)
}

fn admit_canonical_value_impl(
    value: &RhoValue,
    enforce_canonical_depth: bool,
) -> Result<(), ValueDecodeError> {
    let mut work = vec![(value, 1usize)];
    let mut nodes = 0usize;
    let mut collection_items = 0usize;
    let mut total_string_bytes = 0usize;
    let mut total_byte_array_bytes = 0usize;
    while let Some((value, depth)) = work.pop() {
        nodes = nodes
            .checked_add(1)
            .ok_or_else(|| ValueDecodeError::new("$", "canonical value node count overflowed"))?;
        if nodes > MAX_CANONICAL_VALUE_NODES {
            return Err(ValueDecodeError::new(
                "$",
                format!("canonical value exceeds {MAX_CANONICAL_VALUE_NODES} nodes"),
            ));
        }
        if enforce_canonical_depth && depth > crate::parse::MAX_DDL_STRUCTURAL_DEPTH {
            return Err(ValueDecodeError::new(
                "$",
                format!(
                    "canonical value nesting exceeds {}",
                    crate::parse::MAX_DDL_STRUCTURAL_DEPTH
                ),
            ));
        }
        match value {
            RhoValue::Map(values) => {
                collection_items = collection_items.checked_add(values.len()).ok_or_else(|| {
                    ValueDecodeError::new("$", "canonical collection item count overflowed")
                })?;
                let child_depth = depth.checked_add(1).ok_or_else(|| {
                    ValueDecodeError::new("$", "canonical value depth overflowed")
                })?;
                for (key, value) in values.iter().rev() {
                    account_canonical_string(key, &mut total_string_bytes)?;
                    work.push((value, child_depth));
                }
            },
            RhoValue::List(values) => {
                collection_items = collection_items.checked_add(values.len()).ok_or_else(|| {
                    ValueDecodeError::new("$", "canonical collection item count overflowed")
                })?;
                let child_depth = depth.checked_add(1).ok_or_else(|| {
                    ValueDecodeError::new("$", "canonical value depth overflowed")
                })?;
                work.extend(values.iter().rev().map(|value| (value, child_depth)));
            },
            RhoValue::String(value) => {
                account_canonical_string(value, &mut total_string_bytes)?;
            },
            RhoValue::Bytes(value) => {
                account_canonical_bytes(value, &mut total_byte_array_bytes)?;
            },
            RhoValue::Integer(_)
            | RhoValue::FloatBits(_)
            | RhoValue::Boolean(_)
            | RhoValue::Nil => {},
        }
        if collection_items > MAX_CANONICAL_COLLECTION_ITEMS {
            return Err(ValueDecodeError::new(
                "$",
                format!(
                    "canonical value exceeds {MAX_CANONICAL_COLLECTION_ITEMS} collection items"
                ),
            ));
        }
    }
    Ok(())
}

fn account_canonical_bytes(
    value: &[u8],
    total_byte_array_bytes: &mut usize,
) -> Result<(), ValueDecodeError> {
    if value.len() > MAX_CANONICAL_BYTE_ARRAY_BYTES {
        return Err(ValueDecodeError::new(
            "$",
            format!("canonical byte array exceeds {MAX_CANONICAL_BYTE_ARRAY_BYTES} bytes"),
        ));
    }
    *total_byte_array_bytes = total_byte_array_bytes
        .checked_add(value.len())
        .ok_or_else(|| {
            ValueDecodeError::new("$", "canonical total byte-array byte count overflowed")
        })?;
    if *total_byte_array_bytes > MAX_CANONICAL_TOTAL_BYTE_ARRAY_BYTES {
        return Err(ValueDecodeError::new(
            "$",
            format!(
                "canonical byte arrays exceed {MAX_CANONICAL_TOTAL_BYTE_ARRAY_BYTES} total bytes"
            ),
        ));
    }
    Ok(())
}

fn account_canonical_string(
    value: &str,
    total_string_bytes: &mut usize,
) -> Result<(), ValueDecodeError> {
    if value.len() > MAX_CANONICAL_STRING_BYTES {
        return Err(ValueDecodeError::new(
            "$",
            format!("canonical string exceeds {MAX_CANONICAL_STRING_BYTES} bytes"),
        ));
    }
    *total_string_bytes = total_string_bytes.checked_add(value.len()).ok_or_else(|| {
        ValueDecodeError::new("$", "canonical total string byte count overflowed")
    })?;
    if *total_string_bytes > MAX_CANONICAL_TOTAL_STRING_BYTES {
        return Err(ValueDecodeError::new(
            "$",
            format!("canonical strings exceed {MAX_CANONICAL_TOTAL_STRING_BYTES} total bytes"),
        ));
    }
    Ok(())
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
/// `language/2` or `language/3` value. Replacements and theory composition have
/// already been applied by elaboration, so the value contains their semantic
/// result. An OSLF `Data(v)` fragment promotes the result to `language/3`.
pub fn presentation_to_value(
    name: &str,
    presentation: &Presentation,
) -> Result<RhoValue, ValueDecodeError> {
    if let Some(core) = presentation.completed_core() {
        if core.grammar.name != name {
            return Err(ValueDecodeError::new(
                "$.name",
                format!(
                    "Theory name `{name}` does not match completed GrammarCore name `{}`",
                    core.grammar.name
                ),
            ));
        }
        return crate::core_value::language_core_to_value(core);
    }
    let mut spec = BTreeMap::new();
    spec.insert("mettail".into(), string("language/2"));
    spec.insert("name".into(), string(name));
    let mut events = Vec::new();
    for entry in &presentation.types {
        if !presentation.data_derived.contains(&entry.id) {
            events.push((entry.id, map([("types", list([string(entry.cat.clone())]))])));
        }
    }
    for (index, (from, to)) in presentation.exports.iter().enumerate() {
        let id = presentation
            .export_origins
            .get(index)
            .copied()
            .unwrap_or(ElemId(u64::MAX - index as u64));
        if !presentation.data_derived_exports.contains(&id) {
            events.push((
                id,
                map([("exports", list([list([string(from.clone()), string(to.clone())])]))]),
            ));
        }
    }
    for entry in &presentation.terms {
        if !presentation.data_derived.contains(&entry.id) {
            events.push((entry.id, map([("terms", list([term_to_value(&entry.rule)]))])));
        }
    }
    for entry in &presentation.equations {
        if !presentation.data_derived.contains(&entry.id) {
            events.push((
                entry.id,
                map([(
                    "equations",
                    list([map([
                        ("name", string(format!("Equation{}", entry.id.0))),
                        (
                            "premises",
                            list(entry.eq.freshness.iter().map(|(left, right)| {
                                list([string("fresh"), string(left.clone()), string(right.clone())])
                            })),
                        ),
                        ("left", ast_to_value(&entry.eq.lhs)),
                        ("right", ast_to_value(&entry.eq.rhs)),
                    ])]),
                )]),
            ));
        }
    }
    for entry in &presentation.rewrites {
        if !presentation.data_derived.contains(&entry.id) {
            events.push((
                entry.id,
                map([(
                    "rewrites",
                    list([map([
                        ("name", string(entry.rw.name.clone())),
                        (
                            "premises",
                            list(entry.rw.premises.iter().map(|(left, right)| {
                                list([string("~>"), string(left.clone()), string(right.clone())])
                            })),
                        ),
                        ("left", ast_to_value(&entry.rw.lhs)),
                        ("right", ast_to_value(&entry.rw.rhs)),
                    ])]),
                )]),
            ));
        }
    }
    events.extend(
        presentation
            .canonical_fragments
            .iter()
            .map(|fragment| (fragment.id, fragment.value.clone())),
    );
    events.sort_by_key(|(id, _)| *id);
    let mut composed = RhoValue::Map(BTreeMap::new());
    for (_, fragment) in events {
        merge_values(&mut composed, fragment, "$")?;
    }
    let RhoValue::Map(composed_values) = &mut composed else {
        unreachable!()
    };
    let composed = std::mem::take(composed_values);
    spec.extend(composed);
    if spec.contains_key("oslf") {
        spec.insert("mettail".into(), string("language/3"));
    }
    Ok(RhoValue::Map(spec))
}

fn merge_values(
    target: &mut RhoValue,
    incoming: RhoValue,
    path: &str,
) -> Result<(), ValueDecodeError> {
    enum Job {
        Merge {
            target: RhoValue,
            incoming: RhoValue,
            path: String,
        },
        ContinueMap {
            target: BTreeMap<String, RhoValue>,
            incoming: std::collections::btree_map::IntoIter<String, RhoValue>,
            path: String,
        },
        InsertMerged {
            target: BTreeMap<String, RhoValue>,
            incoming: std::collections::btree_map::IntoIter<String, RhoValue>,
            path: String,
            key: String,
        },
    }

    let original = std::mem::replace(target, RhoValue::Nil);
    let mut jobs = vec![Job::Merge {
        target: original,
        incoming,
        path: path.to_owned(),
    }];
    let mut values = Vec::new();
    while let Some(job) = jobs.pop() {
        match job {
            Job::Merge { mut target, mut incoming, path } => {
                let both_maps =
                    matches!(&target, RhoValue::Map(_)) && matches!(&incoming, RhoValue::Map(_));
                let both_lists =
                    matches!(&target, RhoValue::List(_)) && matches!(&incoming, RhoValue::List(_));
                if both_maps {
                    let RhoValue::Map(target) = &mut target else {
                        unreachable!()
                    };
                    let RhoValue::Map(incoming) = &mut incoming else {
                        unreachable!()
                    };
                    jobs.push(Job::ContinueMap {
                        target: std::mem::take(target),
                        incoming: std::mem::take(incoming).into_iter(),
                        path,
                    });
                } else if both_lists {
                    let RhoValue::List(target) = &mut target else {
                        unreachable!()
                    };
                    let RhoValue::List(incoming) = &mut incoming else {
                        unreachable!()
                    };
                    target.append(incoming);
                    values.push(RhoValue::List(std::mem::take(target)));
                } else if target == incoming {
                    values.push(target);
                } else {
                    return Err(ValueDecodeError::new(
                        path,
                        "unequal scalar collision during Data(v) composition",
                    ));
                }
            },
            Job::ContinueMap { mut target, mut incoming, path } => {
                let Some((key, value)) = incoming.next() else {
                    values.push(RhoValue::Map(target));
                    continue;
                };
                if let Some(existing) = target.remove(&key) {
                    let child_path = format!("{path}.{key}");
                    jobs.push(Job::InsertMerged { target, incoming, path, key });
                    jobs.push(Job::Merge {
                        target: existing,
                        incoming: value,
                        path: child_path,
                    });
                } else {
                    target.insert(key, value);
                    jobs.push(Job::ContinueMap { target, incoming, path });
                }
            },
            Job::InsertMerged { mut target, incoming, path, key } => {
                let merged = values
                    .pop()
                    .expect("a nested map merge result is scheduled");
                target.insert(key, merged);
                jobs.push(Job::ContinueMap { target, incoming, path });
            },
        }
    }
    if values.len() != 1 {
        return Err(ValueDecodeError::new(path, "Data(v) merge produced an invalid value stack"));
    }
    *target = values.pop().expect("checked one merged value");
    Ok(())
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ValueDecodeError {
    pub path: String,
    pub message: String,
}

impl ValueDecodeError {
    pub(crate) fn new(path: impl Into<String>, message: impl Into<String>) -> Self {
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
    Resolve { language: String, message: String },
    Lower(LoweringError),
}

/// Complete immutable language identity paired with its declarative install
/// request. Requested rights are intentionally outside `GrammarCoreV1` and
/// `LanguageCoreV1`: changing attenuation demand cannot invalidate a parser or
/// semantic artifact, and this value never grants authority by itself.
#[derive(Clone, Debug, PartialEq)]
pub struct InstallableLanguageCore {
    pub language: core::LanguageCoreV1,
    pub requested_rights: core::LanguageRights,
}

pub trait LanguageValueResolver {
    fn resolve_language(&self, name: &str) -> Result<Option<RhoValue>, String>;
}

/// Decode the canonical ordinary-Rholang representation back to a
/// presentation. Unknown keys and malformed tagged lists are rejected rather
/// than ignored, so programmatically constructed grammars use the same closed
/// schema as the surface elaborator.
pub fn value_to_presentation(value: &RhoValue) -> Result<(String, Presentation), ValueDecodeError> {
    admit_canonical_value(value)?;
    let schema = crate::schema::decode(value)?;
    let spec = expect_map(value, "$".into())?;
    let mut legacy = BTreeMap::from([
        ("mettail".into(), string("language/2")),
        ("name".into(), string(schema.name.clone())),
        ("types".into(), list([])),
        ("exports".into(), list([])),
        ("terms".into(), list([])),
        ("equations".into(), list([])),
        ("rewrites".into(), list([])),
    ]);
    for key in ["types", "exports", "terms", "equations", "rewrites"] {
        if let Some(value) = spec.get(key) {
            legacy.insert(key.into(), value.clone());
        }
    }
    legacy_value_to_presentation(&RhoValue::Map(legacy)).or_else(|_| {
        let mut projection = Presentation::default();
        projection
            .opaque_categories
            .extend(schema.category_names().map(str::to_string));
        projection
            .opaque_labels
            .extend(schema.term_labels().map(str::to_string));
        Ok((schema.name, projection))
    })
}

fn legacy_value_to_presentation(
    value: &RhoValue,
) -> Result<(String, Presentation), ValueDecodeError> {
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
            ..Presentation::default()
        },
    ))
}

pub fn value_to_core(value: &RhoValue) -> Result<core::GrammarCoreV1, ValueToCoreError> {
    Ok(value_to_language_core(value)?.grammar)
}

pub fn value_to_language_core(value: &RhoValue) -> Result<core::LanguageCoreV1, ValueToCoreError> {
    Ok(value_to_installable_language_core(value)?.language)
}

pub fn value_to_installable_language_core(
    value: &RhoValue,
) -> Result<InstallableLanguageCore, ValueToCoreError> {
    if crate::core_value::is_language_core_value(value) {
        let language = crate::core_value::decode_language_core_value(value)
            .map_err(ValueToCoreError::Decode)?
            .ok_or_else(|| {
                ValueToCoreError::Decode(ValueDecodeError::new(
                    "$.core",
                    "structural LanguageCore arm disappeared during decoding",
                ))
            })?;
        return Ok(InstallableLanguageCore {
            language,
            requested_rights: core::LanguageRights::native_flt_default(),
        });
    }
    admit_canonical_value(value).map_err(ValueToCoreError::Decode)?;
    let schema = crate::schema::decode_composed(value, None).map_err(ValueToCoreError::Decode)?;
    let requested_rights = schema.requested_rights();
    let language = schema.lower_language().map_err(ValueToCoreError::Decode)?;
    Ok(InstallableLanguageCore { language, requested_rights })
}

pub fn value_to_core_with_resolver(
    value: &RhoValue,
    resolver: &dyn LanguageValueResolver,
) -> Result<core::GrammarCoreV1, ValueToCoreError> {
    Ok(value_to_language_core_with_resolver(value, resolver)?.grammar)
}

pub fn value_to_language_core_with_resolver(
    value: &RhoValue,
    resolver: &dyn LanguageValueResolver,
) -> Result<core::LanguageCoreV1, ValueToCoreError> {
    Ok(value_to_installable_language_core_with_resolver(value, resolver)?.language)
}

pub fn value_to_installable_language_core_with_resolver(
    value: &RhoValue,
    resolver: &dyn LanguageValueResolver,
) -> Result<InstallableLanguageCore, ValueToCoreError> {
    if crate::core_value::is_language_core_value(value) {
        let language = crate::core_value::decode_language_core_value(value)
            .map_err(ValueToCoreError::Decode)?
            .ok_or_else(|| {
                ValueToCoreError::Decode(ValueDecodeError::new(
                    "$.core",
                    "structural LanguageCore arm disappeared during decoding",
                ))
            })?;
        return Ok(InstallableLanguageCore {
            language,
            requested_rights: core::LanguageRights::native_flt_default(),
        });
    }
    admit_canonical_value(value).map_err(ValueToCoreError::Decode)?;
    let schema =
        crate::schema::decode_composed(value, Some(resolver)).map_err(ValueToCoreError::Decode)?;
    let requested_rights = schema.requested_rights();
    let language = schema.lower_language().map_err(ValueToCoreError::Decode)?;
    Ok(InstallableLanguageCore { language, requested_rights })
}

/// Decode a `Data(v)` fragment through the canonical schema. The two
/// whole-language identity keys are forbidden; all other supported fields are
/// decoded exactly as they are on the direct registry-value path.
pub fn partial_value_to_presentation(value: &RhoValue) -> Result<Presentation, ValueDecodeError> {
    admit_canonical_value(value)?;
    let schema = crate::schema::validate_fragment(value)?;
    let fragment = expect_map(value, "Data".into())?;
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
        if complete.contains_key(key) {
            complete.insert(key.clone(), value.clone());
        }
    }
    let mut presentation = legacy_value_to_presentation(&RhoValue::Map(complete))
        .map(|(_, presentation)| presentation)
        .unwrap_or_default();
    presentation
        .opaque_categories
        .extend(schema.category_names().map(str::to_string));
    presentation
        .opaque_labels
        .extend(schema.term_labels().map(str::to_string));
    Ok(presentation)
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
    enum Task<'a> {
        Visit { value: &'a RhoValue, path: String },
        FinishSubst,
        FinishAbs(String),
        FinishColl { count: usize, remainder: Option<String> },
        FinishSExp { label: String, count: usize },
    }

    let span = Span { line: 0, col: 0 };
    let mut tasks = vec![Task::Visit { value, path: path.into() }];
    let mut output = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            Task::Visit { value: RhoValue::String(name), .. } => {
                output.push(Ast::Var(name.clone(), span));
            },
            Task::Visit { value, path } => {
                let values = expect_list(value, path.clone())?;
                let tag = expect_string(
                    values
                        .first()
                        .ok_or_else(|| ValueDecodeError::new(&path, "empty AST node"))?,
                    format!("{path}[0]"),
                )?;
                match tag {
                    "eval" => {
                        require_len(values, 3, &path)?;
                        tasks.push(Task::FinishSubst);
                        tasks.push(Task::Visit {
                            value: &values[2],
                            path: format!("{path}[2]"),
                        });
                        tasks.push(Task::Visit {
                            value: &values[1],
                            path: format!("{path}[1]"),
                        });
                    },
                    "^" => {
                        require_len(values, 3, &path)?;
                        let binder = expect_string(&values[1], format!("{path}[1]"))?.to_string();
                        tasks.push(Task::FinishAbs(binder));
                        tasks.push(Task::Visit {
                            value: &values[2],
                            path: format!("{path}[2]"),
                        });
                    },
                    "coll" => {
                        require_len(values, 3, &path)?;
                        let elements = expect_list(&values[1], format!("{path}[1]"))?;
                        let remainder = match &values[2] {
                            RhoValue::Nil => None,
                            RhoValue::String(name) => Some(name.clone()),
                            _ => {
                                return Err(ValueDecodeError::new(
                                    format!("{path}[2]"),
                                    "expected remainder name or Nil",
                                ))
                            },
                        };
                        tasks.push(Task::FinishColl { count: elements.len(), remainder });
                        for (index, element) in elements.iter().enumerate().rev() {
                            tasks.push(Task::Visit {
                                value: element,
                                path: format!("{path}[1][{index}]"),
                            });
                        }
                    },
                    label => {
                        tasks.push(Task::FinishSExp {
                            label: label.to_string(),
                            count: values.len() - 1,
                        });
                        for (index, argument) in values[1..].iter().enumerate().rev() {
                            tasks.push(Task::Visit {
                                value: argument,
                                path: format!("{path}[{}]", index + 1),
                            });
                        }
                    },
                }
            },
            Task::FinishSubst => {
                let argument = output.pop().expect("substitution argument is scheduled");
                let abstraction = output.pop().expect("substitution abstraction is scheduled");
                output.push(Ast::Subst(Box::new(abstraction), Box::new(argument), span));
            },
            Task::FinishAbs(binder) => {
                let body = output.pop().expect("abstraction body is scheduled");
                output.push(Ast::Abs(binder, Box::new(body), span));
            },
            Task::FinishColl { count, remainder } => {
                let start = output.len() - count;
                let mut elements = output.drain(start..).collect::<Vec<_>>();
                if let Some(name) = remainder {
                    elements.push(Ast::Remainder(name, span));
                }
                output.push(Ast::Coll(elements, span));
            },
            Task::FinishSExp { label, count } => {
                let start = output.len() - count;
                let arguments = output.drain(start..).collect();
                output.push(Ast::SExp(label, arguments, span));
            },
        }
    }
    if output.len() != 1 {
        return Err(ValueDecodeError::new(path, "AST decoder produced an invalid value stack"));
    }
    Ok(output.pop().expect("checked one AST value"))
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
    enum Task<'a> {
        Visit(&'a Ast),
        FinishSExp { label: &'a str, count: usize },
        FinishSubst,
        FinishAbs(&'a str),
        FinishColl { count: usize, remainder: Option<&'a str> },
    }

    let mut tasks = vec![Task::Visit(ast)];
    let mut output = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            Task::Visit(Ast::Var(name, _)) => output.push(string(name.clone())),
            Task::Visit(Ast::Remainder(name, _)) => {
                output.push(list([string("coll"), list(std::iter::empty()), string(name.clone())]))
            },
            Task::Visit(Ast::SExp(label, arguments, _)) => {
                tasks.push(Task::FinishSExp { label, count: arguments.len() });
                tasks.extend(arguments.iter().rev().map(Task::Visit));
            },
            Task::Visit(Ast::Subst(abstraction, argument, _)) => {
                tasks.push(Task::FinishSubst);
                tasks.push(Task::Visit(argument));
                tasks.push(Task::Visit(abstraction));
            },
            Task::Visit(Ast::Abs(binder, body, _)) => {
                tasks.push(Task::FinishAbs(binder));
                tasks.push(Task::Visit(body));
            },
            Task::Visit(Ast::Coll(elements, _)) => {
                let remainder = elements.last().and_then(|element| match element {
                    Ast::Remainder(name, _) => Some(name.as_str()),
                    _ => None,
                });
                let count = elements.len() - usize::from(remainder.is_some());
                tasks.push(Task::FinishColl { count, remainder });
                tasks.extend(elements[..count].iter().rev().map(Task::Visit));
            },
            Task::FinishSExp { label, count } => {
                let start = output.len() - count;
                let mut node = Vec::with_capacity(count + 1);
                node.push(string(label));
                node.extend(output.drain(start..));
                output.push(list(node));
            },
            Task::FinishSubst => {
                let argument = output.pop().expect("substitution argument is scheduled");
                let abstraction = output.pop().expect("substitution abstraction is scheduled");
                output.push(list([string("eval"), abstraction, argument]));
            },
            Task::FinishAbs(binder) => {
                let body = output.pop().expect("abstraction body is scheduled");
                output.push(list([string("^"), string(binder), body]));
            },
            Task::FinishColl { count, remainder } => {
                let start = output.len() - count;
                let elements = list(output.drain(start..));
                let remainder = remainder.map(string).unwrap_or(RhoValue::Nil);
                output.push(list([string("coll"), elements, remainder]));
            },
        }
    }
    output.pop().expect("AST encoder produces one value")
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LoweringError {
    UnknownCategory(String),
    UnknownArgument { rule: String, argument: String },
    ProjectionOfNonCollection { rule: String, argument: String },
    DuplicateArgument { rule: String, argument: String },
    InvalidCanonical(ValueDecodeError),
    InvalidCore(Vec<core::ValidationError>),
}

/// Lower an elaborated presentation into the backend-neutral parser IR.
pub fn presentation_to_core(
    name: &str,
    presentation: &Presentation,
) -> Result<core::GrammarCoreV1, LoweringError> {
    let value =
        presentation_to_value(name, presentation).map_err(LoweringError::InvalidCanonical)?;
    let schema =
        crate::schema::decode_composed(&value, None).map_err(LoweringError::InvalidCanonical)?;
    schema.lower().map_err(LoweringError::InvalidCanonical)
}

#[allow(dead_code)]
fn presentation_to_core_legacy(
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
        category: None,
        evaluation: None,
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
            category: None,
            evaluation: None,
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
                            key: None,
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
                        key: None,
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
            evaluation: None,
            evaluation_mode: None,
            tier: None,
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
        let value = presentation_to_value("Tiny", &presentation).expect("canonical value");
        let RhoValue::Map(map) = &value else {
            panic!("spec must be a map")
        };
        assert_eq!(map.get("mettail"), Some(&string("language/2")));
        let core = presentation_to_core("Tiny", &presentation).expect("valid core");
        let value = presentation_to_value("Tiny", &presentation).expect("canonical value");
        let decoded = value_to_core(&value).expect("canonical value lowers");
        assert_eq!(
            core.fingerprint().expect("surface fingerprint"),
            decoded.fingerprint().expect("value fingerprint")
        );
        assert_eq!(core.productions.len(), 1);
    }

    #[test]
    fn rho_value_lifecycle_is_stack_safe_beyond_the_admission_bound() {
        std::thread::Builder::new()
            .name("rho-value-lifecycle-small-stack".into())
            .stack_size(256 * 1024)
            .spawn(|| {
                let mut value = RhoValue::Nil;
                for _ in 0..20_000 {
                    value = RhoValue::List(vec![value]);
                }
                let cloned = value.clone();
                assert_eq!(value, cloned);
                assert_eq!(value.cmp(&cloned), std::cmp::Ordering::Equal);
                assert_eq!(value.fingerprint(), cloned.fingerprint());
                assert!(format!("{value:?}").starts_with("List([List(["));
                let error = admit_canonical_value(&value).expect_err("depth must be rejected");
                assert!(error.message.contains("nesting exceeds"));
                drop(cloned);
                drop(value);
            })
            .expect("spawn lifecycle worker")
            .join()
            .expect("lifecycle operations must not overflow or panic");
    }

    #[test]
    fn canonical_data_merge_is_stack_safe_beyond_the_admission_bound() {
        std::thread::Builder::new()
            .name("rho-value-merge-small-stack".into())
            .stack_size(256 * 1024)
            .spawn(|| {
                let mut target = RhoValue::String("leaf".into());
                let mut incoming = RhoValue::String("leaf".into());
                for _ in 0..20_000 {
                    target = RhoValue::Map(BTreeMap::from([("next".into(), target)]));
                    incoming = RhoValue::Map(BTreeMap::from([("next".into(), incoming)]));
                }
                merge_values(&mut target, incoming, "$").expect("equal maps merge");
                let error = admit_canonical_value(&target).expect_err("depth must be rejected");
                assert!(error.message.contains("nesting exceeds"));
            })
            .expect("spawn merge worker")
            .join()
            .expect("canonical merge must not overflow or panic");
    }

    #[test]
    fn collection_remainder_uses_the_canonical_remainder_slot() {
        let span = Span { line: 1, col: 1 };
        let ast = Ast::Coll(
            vec![Ast::SExp("PZero".into(), Vec::new(), span), Ast::Remainder("rest".into(), span)],
            span,
        );
        let value = ast_to_value(&ast);
        let RhoValue::List(fields) = &value else {
            panic!("collection is a tagged list")
        };
        assert_eq!(fields.get(2), Some(&RhoValue::String("rest".into())));
        let decoded = decode_ast(&value, "$.ast").expect("canonical collection decodes");
        assert_eq!(crate::pres::render_ast(&decoded), "{(PZero), ...rest}");
    }
}
