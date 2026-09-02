use crate::{
    CategoryId, CollectionKind, ConstructorId, EvaluationMode, NativeEvaluation, TierDirective,
};
use serde::{de::Error as _, Deserialize, Deserializer, Serialize, Serializer};
use std::fmt;
use std::hash::{Hash, Hasher};

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct SourceSpan {
    pub start: u32,
    pub end: u32,
}

pub enum DynamicValue {
    Term(Box<DynamicTerm>),
    /// A structural FLT metavariable admitted directly at a grammar category.
    ///
    /// This value is produced only by template parsing. It is never decoded
    /// from guest text, so rendered hole contents cannot become guest syntax.
    TemplateHole {
        id: u32,
        category: CategoryId,
    },
    Sequence(Vec<DynamicValue>),
    Collection {
        kind: CollectionKind,
        entries: Vec<DynamicValue>,
    },
    Text(String),
    Integer(i128),
    Boolean(bool),
    Bytes(Vec<u8>),
    Unit,
}

#[derive(Debug)]
pub enum DynamicCollectionError {
    Encode(postcard::Error),
    InvalidMapEntry,
    DuplicateMapKey,
    KindMismatch,
}

impl DynamicValue {
    /// Retained heap weight used by bounded symbolic-template memoization.
    /// Traversal is iterative, and every owned buffer is charged by capacity
    /// rather than length so spare allocation cannot evade the cache budget.
    pub(crate) fn retained_heap_weight(&self) -> usize {
        let mut weight = 0usize;
        let mut pending = vec![self];
        while let Some(value) = pending.pop() {
            match value {
                Self::Term(term) => {
                    weight = weight
                        .saturating_add(std::mem::size_of::<DynamicTerm>())
                        .saturating_add(
                            term.fields
                                .capacity()
                                .saturating_mul(std::mem::size_of::<DynamicValue>()),
                        );
                    pending.extend(term.fields.iter());
                },
                Self::Sequence(values) => {
                    weight = weight.saturating_add(
                        values
                            .capacity()
                            .saturating_mul(std::mem::size_of::<DynamicValue>()),
                    );
                    pending.extend(values.iter());
                },
                Self::Collection { entries, .. } => {
                    weight = weight.saturating_add(
                        entries
                            .capacity()
                            .saturating_mul(std::mem::size_of::<DynamicValue>()),
                    );
                    pending.extend(entries.iter());
                },
                Self::Text(text) => weight = weight.saturating_add(text.capacity()),
                Self::Bytes(bytes) => weight = weight.saturating_add(bytes.capacity()),
                Self::TemplateHole { .. } | Self::Integer(_) | Self::Boolean(_) | Self::Unit => {},
            }
        }
        weight
    }

    pub fn semantic_key(&self) -> Result<Vec<u8>, postcard::Error> {
        postcard::to_allocvec(&SemanticFlatValueV1::from_value(self))
    }

    pub fn collection(
        kind: CollectionKind,
        mut entries: Vec<DynamicValue>,
    ) -> Result<Self, DynamicCollectionError> {
        match kind {
            CollectionKind::List => {},
            CollectionKind::Bag | CollectionKind::Set => {
                let mut keyed = entries
                    .into_iter()
                    .map(|value| {
                        value
                            .semantic_key()
                            .map(|key| (key, value))
                            .map_err(DynamicCollectionError::Encode)
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                keyed.sort_by(|left, right| left.0.cmp(&right.0));
                if kind == CollectionKind::Set {
                    keyed.dedup_by(|left, right| left.0 == right.0);
                }
                entries = keyed.into_iter().map(|(_, value)| value).collect();
            },
            CollectionKind::Map | CollectionKind::PathMap => {
                let mut keyed = entries
                    .into_iter()
                    .map(|entry| {
                        let DynamicValue::Sequence(pair) = &entry else {
                            return Err(DynamicCollectionError::InvalidMapEntry);
                        };
                        if pair.len() != 2 {
                            return Err(DynamicCollectionError::InvalidMapEntry);
                        }
                        pair[0]
                            .semantic_key()
                            .map(|key| (key, entry))
                            .map_err(DynamicCollectionError::Encode)
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                keyed.sort_by(|left, right| left.0.cmp(&right.0));
                if keyed.windows(2).any(|pair| pair[0].0 == pair[1].0) {
                    return Err(DynamicCollectionError::DuplicateMapKey);
                }
                entries = keyed.into_iter().map(|(_, value)| value).collect();
            },
        }
        Ok(Self::Collection { kind, entries })
    }

    pub fn append_collection(
        expected_kind: CollectionKind,
        mut prefix: DynamicValue,
        last: DynamicValue,
    ) -> Result<Self, DynamicCollectionError> {
        match &mut prefix {
            DynamicValue::Collection { kind, entries } if *kind == expected_kind => {
                entries.push(last);
            },
            _ => return Err(DynamicCollectionError::KindMismatch),
        }
        Ok(prefix)
    }

    pub(crate) fn into_collection_parts(
        mut self,
    ) -> Result<(CollectionKind, Vec<DynamicValue>), DynamicCollectionError> {
        match &mut self {
            DynamicValue::Collection { kind, entries } => Ok((*kind, std::mem::take(entries))),
            _ => Err(DynamicCollectionError::KindMismatch),
        }
    }

    fn move_children_to(&mut self, pending: &mut Vec<DynamicValue>) {
        match self {
            Self::Term(term) => pending.append(&mut term.fields),
            Self::Sequence(values) => pending.append(values),
            Self::Collection { entries, .. } => pending.append(entries),
            Self::TemplateHole { .. }
            | Self::Text(_)
            | Self::Integer(_)
            | Self::Boolean(_)
            | Self::Bytes(_)
            | Self::Unit => {},
        }
    }
}

/// Dropping a deeply nested run-time term must consume the Rust stack at a
/// constant depth. Children are detached before each node is dropped, leaving
/// the authoritative pushdown traversal in this heap-backed work vector.
impl Drop for DynamicValue {
    fn drop(&mut self) {
        let mut pending = Vec::new();
        self.move_children_to(&mut pending);
        while let Some(mut value) = pending.pop() {
            value.move_children_to(&mut pending);
            // `value` now contains no owned child values. Its nested `drop`
            // invocation therefore has constant depth and an empty work list.
        }
    }
}

impl Clone for DynamicValue {
    fn clone(&self) -> Self {
        enum Task<'a> {
            Visit(&'a DynamicValue),
            Term {
                category: CategoryId,
                constructor: ConstructorId,
                span: SourceSpan,
                children: usize,
            },
            Sequence(usize),
            Collection(CollectionKind, usize),
        }

        let mut tasks = vec![Task::Visit(self)];
        let mut values = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                Task::Visit(value) => match value {
                    Self::Term(term) => {
                        tasks.push(Task::Term {
                            category: term.category,
                            constructor: term.constructor,
                            span: term.span,
                            children: term.fields.len(),
                        });
                        tasks.extend(term.fields.iter().rev().map(Task::Visit));
                    },
                    Self::TemplateHole { id, category } => {
                        values.push(Self::TemplateHole { id: *id, category: *category });
                    },
                    Self::Sequence(children) => {
                        tasks.push(Task::Sequence(children.len()));
                        tasks.extend(children.iter().rev().map(Task::Visit));
                    },
                    Self::Collection { kind, entries } => {
                        tasks.push(Task::Collection(*kind, entries.len()));
                        tasks.extend(entries.iter().rev().map(Task::Visit));
                    },
                    Self::Text(value) => values.push(Self::Text(value.clone())),
                    Self::Integer(value) => values.push(Self::Integer(*value)),
                    Self::Boolean(value) => values.push(Self::Boolean(*value)),
                    Self::Bytes(value) => values.push(Self::Bytes(value.clone())),
                    Self::Unit => values.push(Self::Unit),
                },
                Task::Term { category, constructor, span, children } => {
                    let first = values
                        .len()
                        .checked_sub(children)
                        .expect("dynamic-value clone lost a term child");
                    let fields = values.split_off(first);
                    values.push(Self::Term(Box::new(DynamicTerm {
                        category,
                        constructor,
                        fields,
                        span,
                    })));
                },
                Task::Sequence(children) => {
                    let first = values
                        .len()
                        .checked_sub(children)
                        .expect("dynamic-value clone lost a sequence child");
                    let children = values.split_off(first);
                    values.push(Self::Sequence(children));
                },
                Task::Collection(kind, children) => {
                    let first = values
                        .len()
                        .checked_sub(children)
                        .expect("dynamic-value clone lost a collection child");
                    let entries = values.split_off(first);
                    values.push(Self::Collection { kind, entries });
                },
            }
        }
        debug_assert_eq!(values.len(), 1);
        values
            .pop()
            .expect("a dynamic value always clones to one root")
    }
}

impl PartialEq for DynamicValue {
    fn eq(&self, other: &Self) -> bool {
        let mut pending = vec![(self, other)];
        while let Some((left, right)) = pending.pop() {
            match (left, right) {
                (Self::Term(left), Self::Term(right)) => {
                    if left.category != right.category
                        || left.constructor != right.constructor
                        || left.span != right.span
                        || left.fields.len() != right.fields.len()
                    {
                        return false;
                    }
                    pending.extend(left.fields.iter().zip(&right.fields));
                },
                (
                    Self::TemplateHole { id: left_id, category: left_category },
                    Self::TemplateHole { id: right_id, category: right_category },
                ) if left_id == right_id && left_category == right_category => {},
                (Self::Sequence(left), Self::Sequence(right)) => {
                    if left.len() != right.len() {
                        return false;
                    }
                    pending.extend(left.iter().zip(right));
                },
                (
                    Self::Collection { kind: left_kind, entries: left },
                    Self::Collection { kind: right_kind, entries: right },
                ) => {
                    if left_kind != right_kind || left.len() != right.len() {
                        return false;
                    }
                    pending.extend(left.iter().zip(right));
                },
                (Self::Text(left), Self::Text(right)) if left == right => {},
                (Self::Integer(left), Self::Integer(right)) if left == right => {},
                (Self::Boolean(left), Self::Boolean(right)) if left == right => {},
                (Self::Bytes(left), Self::Bytes(right)) if left == right => {},
                (Self::Unit, Self::Unit) => {},
                _ => return false,
            }
        }
        true
    }
}

impl Eq for DynamicValue {}

impl Hash for DynamicValue {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let mut pending = vec![self];
        while let Some(value) = pending.pop() {
            match value {
                Self::Term(term) => {
                    0u8.hash(state);
                    term.category.hash(state);
                    term.constructor.hash(state);
                    term.span.hash(state);
                    term.fields.len().hash(state);
                    pending.extend(term.fields.iter().rev());
                },
                Self::TemplateHole { id, category } => {
                    1u8.hash(state);
                    id.hash(state);
                    category.hash(state);
                },
                Self::Sequence(values) => {
                    2u8.hash(state);
                    values.len().hash(state);
                    pending.extend(values.iter().rev());
                },
                Self::Collection { kind, entries } => {
                    3u8.hash(state);
                    kind.hash(state);
                    entries.len().hash(state);
                    pending.extend(entries.iter().rev());
                },
                Self::Text(value) => {
                    4u8.hash(state);
                    value.hash(state);
                },
                Self::Integer(value) => {
                    5u8.hash(state);
                    value.hash(state);
                },
                Self::Boolean(value) => {
                    6u8.hash(state);
                    value.hash(state);
                },
                Self::Bytes(value) => {
                    7u8.hash(state);
                    value.hash(state);
                },
                Self::Unit => 8u8.hash(state),
            }
        }
    }
}

impl fmt::Debug for DynamicValue {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        enum Task<'a> {
            Value(&'a DynamicValue),
            Text(&'static str),
        }

        let mut tasks = vec![Task::Value(self)];
        while let Some(task) = tasks.pop() {
            match task {
                Task::Text(text) => formatter.write_str(text)?,
                Task::Value(value) => match value {
                    Self::Term(term) => {
                        write!(
                            formatter,
                            "Term({:?}, {:?}, {:?}, [",
                            term.category, term.constructor, term.span
                        )?;
                        tasks.push(Task::Text("])"));
                        for (index, child) in term.fields.iter().enumerate().rev() {
                            tasks.push(Task::Value(child));
                            if index != 0 {
                                tasks.push(Task::Text(", "));
                            }
                        }
                    },
                    Self::TemplateHole { id, category } => {
                        write!(formatter, "TemplateHole({id}, {category:?})")?;
                    },
                    Self::Sequence(values) => {
                        formatter.write_str("Sequence([")?;
                        tasks.push(Task::Text("])"));
                        for (index, child) in values.iter().enumerate().rev() {
                            tasks.push(Task::Value(child));
                            if index != 0 {
                                tasks.push(Task::Text(", "));
                            }
                        }
                    },
                    Self::Collection { kind, entries } => {
                        write!(formatter, "Collection({kind:?}, [")?;
                        tasks.push(Task::Text("])"));
                        for (index, child) in entries.iter().enumerate().rev() {
                            tasks.push(Task::Value(child));
                            if index != 0 {
                                tasks.push(Task::Text(", "));
                            }
                        }
                    },
                    Self::Text(value) => write!(formatter, "Text({value:?})")?,
                    Self::Integer(value) => write!(formatter, "Integer({value:?})")?,
                    Self::Boolean(value) => write!(formatter, "Boolean({value:?})")?,
                    Self::Bytes(value) => write!(formatter, "Bytes({value:?})")?,
                    Self::Unit => formatter.write_str("Unit")?,
                },
            }
        }
        Ok(())
    }
}

const FLAT_DYNAMIC_VALUE_VERSION: u8 = 1;

#[derive(Serialize, Deserialize)]
struct FlatDynamicValueV1 {
    version: u8,
    nodes: Vec<FlatDynamicNodeV1>,
}

#[derive(Serialize, Deserialize)]
enum FlatDynamicNodeV1 {
    Term {
        category: CategoryId,
        constructor: ConstructorId,
        span: SourceSpan,
        children: u32,
    },
    TemplateHole {
        id: u32,
        category: CategoryId,
    },
    Sequence(u32),
    Collection {
        kind: CollectionKind,
        children: u32,
    },
    Text(String),
    Integer(i128),
    Boolean(bool),
    Bytes(Vec<u8>),
    Unit,
}

impl FlatDynamicValueV1 {
    fn from_value(value: &DynamicValue) -> Self {
        let mut nodes = Vec::new();
        let mut pending = vec![value];
        while let Some(value) = pending.pop() {
            nodes.push(match value {
                DynamicValue::Term(term) => {
                    pending.extend(term.fields.iter().rev());
                    FlatDynamicNodeV1::Term {
                        category: term.category,
                        constructor: term.constructor,
                        span: term.span,
                        children: u32::try_from(term.fields.len()).unwrap_or(u32::MAX),
                    }
                },
                DynamicValue::TemplateHole { id, category } => {
                    FlatDynamicNodeV1::TemplateHole { id: *id, category: *category }
                },
                DynamicValue::Sequence(values) => {
                    pending.extend(values.iter().rev());
                    FlatDynamicNodeV1::Sequence(u32::try_from(values.len()).unwrap_or(u32::MAX))
                },
                DynamicValue::Collection { kind, entries } => {
                    pending.extend(entries.iter().rev());
                    FlatDynamicNodeV1::Collection {
                        kind: *kind,
                        children: u32::try_from(entries.len()).unwrap_or(u32::MAX),
                    }
                },
                DynamicValue::Text(value) => FlatDynamicNodeV1::Text(value.clone()),
                DynamicValue::Integer(value) => FlatDynamicNodeV1::Integer(*value),
                DynamicValue::Boolean(value) => FlatDynamicNodeV1::Boolean(*value),
                DynamicValue::Bytes(value) => FlatDynamicNodeV1::Bytes(value.clone()),
                DynamicValue::Unit => FlatDynamicNodeV1::Unit,
            });
        }
        Self {
            version: FLAT_DYNAMIC_VALUE_VERSION,
            nodes,
        }
    }

    fn into_value(self) -> Result<DynamicValue, &'static str> {
        if self.version != FLAT_DYNAMIC_VALUE_VERSION {
            return Err("unsupported dynamic-value encoding version");
        }
        let mut values = Vec::new();
        for node in self.nodes.into_iter().rev() {
            let value = match node {
                FlatDynamicNodeV1::Term { category, constructor, span, children } => {
                    let mut fields = take_reverse_children(&mut values, children)?;
                    fields.reverse();
                    DynamicValue::Term(Box::new(DynamicTerm {
                        category,
                        constructor,
                        fields,
                        span,
                    }))
                },
                FlatDynamicNodeV1::TemplateHole { id, category } => {
                    DynamicValue::TemplateHole { id, category }
                },
                FlatDynamicNodeV1::Sequence(children) => {
                    let mut children = take_reverse_children(&mut values, children)?;
                    children.reverse();
                    DynamicValue::Sequence(children)
                },
                FlatDynamicNodeV1::Collection { kind, children } => {
                    let mut entries = take_reverse_children(&mut values, children)?;
                    entries.reverse();
                    DynamicValue::Collection { kind, entries }
                },
                FlatDynamicNodeV1::Text(value) => DynamicValue::Text(value),
                FlatDynamicNodeV1::Integer(value) => DynamicValue::Integer(value),
                FlatDynamicNodeV1::Boolean(value) => DynamicValue::Boolean(value),
                FlatDynamicNodeV1::Bytes(value) => DynamicValue::Bytes(value),
                FlatDynamicNodeV1::Unit => DynamicValue::Unit,
            };
            values.push(value);
        }
        if values.len() != 1 {
            return Err("dynamic-value encoding must contain exactly one tree");
        }
        Ok(values.pop().expect("one validated dynamic-value root"))
    }
}

fn take_reverse_children(
    values: &mut Vec<DynamicValue>,
    children: u32,
) -> Result<Vec<DynamicValue>, &'static str> {
    let children = usize::try_from(children).map_err(|_| "dynamic-value child count overflow")?;
    let first = values
        .len()
        .checked_sub(children)
        .ok_or("dynamic-value encoding has a missing child")?;
    Ok(values.split_off(first))
}

impl Serialize for DynamicValue {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        FlatDynamicValueV1::from_value(self).serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for DynamicValue {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        FlatDynamicValueV1::deserialize(deserializer)?
            .into_value()
            .map_err(D::Error::custom)
    }
}

#[derive(Serialize)]
struct SemanticFlatValueV1 {
    version: u8,
    nodes: Vec<SemanticFlatNodeV1>,
}

#[derive(Serialize)]
enum SemanticFlatNodeV1 {
    Term {
        category: CategoryId,
        constructor: ConstructorId,
        children: u32,
    },
    TemplateHole {
        id: u32,
        category: CategoryId,
    },
    Sequence(u32),
    Collection {
        kind: CollectionKind,
        children: u32,
    },
    Text(String),
    Integer(i128),
    Boolean(bool),
    Bytes(Vec<u8>),
    Unit,
}

impl SemanticFlatValueV1 {
    fn from_value(value: &DynamicValue) -> Self {
        let mut nodes = Vec::new();
        let mut pending = vec![value];
        while let Some(value) = pending.pop() {
            nodes.push(match value {
                DynamicValue::Term(term) => {
                    pending.extend(term.fields.iter().rev());
                    SemanticFlatNodeV1::Term {
                        category: term.category,
                        constructor: term.constructor,
                        children: u32::try_from(term.fields.len()).unwrap_or(u32::MAX),
                    }
                },
                DynamicValue::TemplateHole { id, category } => {
                    SemanticFlatNodeV1::TemplateHole { id: *id, category: *category }
                },
                DynamicValue::Sequence(values) => {
                    pending.extend(values.iter().rev());
                    SemanticFlatNodeV1::Sequence(u32::try_from(values.len()).unwrap_or(u32::MAX))
                },
                DynamicValue::Collection { kind, entries } => {
                    pending.extend(entries.iter().rev());
                    SemanticFlatNodeV1::Collection {
                        kind: *kind,
                        children: u32::try_from(entries.len()).unwrap_or(u32::MAX),
                    }
                },
                DynamicValue::Text(value) => SemanticFlatNodeV1::Text(value.clone()),
                DynamicValue::Integer(value) => SemanticFlatNodeV1::Integer(*value),
                DynamicValue::Boolean(value) => SemanticFlatNodeV1::Boolean(*value),
                DynamicValue::Bytes(value) => SemanticFlatNodeV1::Bytes(value.clone()),
                DynamicValue::Unit => SemanticFlatNodeV1::Unit,
            });
        }
        Self {
            version: FLAT_DYNAMIC_VALUE_VERSION,
            nodes,
        }
    }
}

/// Language-independent result of a runtime reduction.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct DynamicTerm {
    pub category: CategoryId,
    pub constructor: ConstructorId,
    pub fields: Vec<DynamicValue>,
    pub span: SourceSpan,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum FieldSource {
    Input(u16),
    Text(u16),
    EmptySequence,
    Unit,
}

/// Declarative semantic action. Runtime grammar values cannot carry Rust code.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReductionPlan {
    pub output_category: CategoryId,
    pub constructor: ConstructorId,
    pub input_arity: u16,
    pub fields: Vec<FieldSource>,
    pub evaluation: Option<NativeEvaluation>,
    pub evaluation_mode: Option<EvaluationMode>,
    pub tier: Option<TierDirective>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ReductionError {
    Arity { expected: usize, actual: usize },
    MissingInput(u16),
    MissingText(u16),
}

impl ReductionPlan {
    pub fn apply(
        &self,
        inputs: &[DynamicValue],
        captures: &[String],
        span: SourceSpan,
    ) -> Result<DynamicTerm, ReductionError> {
        if inputs.len() != usize::from(self.input_arity) {
            return Err(ReductionError::Arity {
                expected: usize::from(self.input_arity),
                actual: inputs.len(),
            });
        }
        let mut fields = Vec::with_capacity(self.fields.len());
        for source in &self.fields {
            fields.push(match *source {
                FieldSource::Input(index) => inputs
                    .get(usize::from(index))
                    .cloned()
                    .ok_or(ReductionError::MissingInput(index))?,
                FieldSource::Text(index) => DynamicValue::Text(
                    captures
                        .get(usize::from(index))
                        .cloned()
                        .ok_or(ReductionError::MissingText(index))?,
                ),
                FieldSource::EmptySequence => DynamicValue::Sequence(Vec::new()),
                FieldSource::Unit => DynamicValue::Unit,
            });
        }
        Ok(DynamicTerm {
            category: self.output_category,
            constructor: self.constructor,
            fields,
            span,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::hash_map::DefaultHasher;

    fn term(value: i128, span: SourceSpan) -> DynamicValue {
        DynamicValue::Term(Box::new(DynamicTerm {
            category: CategoryId(0),
            constructor: ConstructorId(0),
            fields: vec![DynamicValue::Integer(value)],
            span,
        }))
    }

    #[test]
    fn semantic_keys_erase_source_spans_recursively() {
        let left = DynamicValue::Sequence(vec![term(7, SourceSpan { start: 0, end: 1 })]);
        let right = DynamicValue::Sequence(vec![term(7, SourceSpan { start: 40, end: 90 })]);
        assert_ne!(left, right);
        assert_eq!(left.semantic_key().unwrap(), right.semantic_key().unwrap());
    }

    #[test]
    fn map_keys_are_unique_by_semantics_not_provenance() {
        let entries = vec![
            DynamicValue::Sequence(vec![
                term(1, SourceSpan { start: 0, end: 1 }),
                term(2, SourceSpan { start: 2, end: 3 }),
            ]),
            DynamicValue::Sequence(vec![
                term(1, SourceSpan { start: 4, end: 5 }),
                term(3, SourceSpan { start: 6, end: 7 }),
            ]),
        ];
        assert!(matches!(
            DynamicValue::collection(CollectionKind::Map, entries),
            Err(DynamicCollectionError::DuplicateMapKey)
        ));
    }

    #[test]
    fn set_deduplicates_semantically_equal_values_with_distinct_spans() {
        let set = DynamicValue::collection(
            CollectionKind::Set,
            vec![
                term(1, SourceSpan { start: 0, end: 1 }),
                term(1, SourceSpan { start: 2, end: 3 }),
            ],
        )
        .unwrap();
        let DynamicValue::Collection { ref entries, .. } = set else {
            panic!("collection")
        };
        assert_eq!(entries.len(), 1);
    }

    #[test]
    fn every_owned_value_operation_is_stack_safe_at_extreme_depth() {
        std::thread::Builder::new()
            .name("dynamic-value-small-stack".into())
            .stack_size(256 * 1024)
            .spawn(|| {
                let mut value = DynamicValue::Unit;
                for depth in 0..20_000u32 {
                    value = DynamicValue::Term(Box::new(DynamicTerm {
                        category: CategoryId(0),
                        constructor: ConstructorId(0),
                        fields: vec![value],
                        span: SourceSpan { start: depth, end: depth + 1 },
                    }));
                }

                let clone = value.clone();
                assert_eq!(value, clone);

                let mut value_hash = DefaultHasher::new();
                value.hash(&mut value_hash);
                let mut clone_hash = DefaultHasher::new();
                clone.hash(&mut clone_hash);
                assert_eq!(value_hash.finish(), clone_hash.finish());

                let semantic_key = value.semantic_key().expect("flat semantic encoding");
                assert!(!semantic_key.is_empty());

                let encoded = postcard::to_allocvec(&value).expect("flat value encoding");
                let decoded: DynamicValue =
                    postcard::from_bytes(&encoded).expect("flat value decoding");
                assert_eq!(value, decoded);

                let rendered = format!("{value:?}");
                assert!(rendered.starts_with("Term("));
                assert!(rendered.ends_with("])"));

                drop(decoded);
                drop(clone);
                drop(value);
            })
            .expect("spawn small-stack thread")
            .join()
            .expect("all deep value operations must stay within 256 KiB");
    }

    #[test]
    fn flat_decoder_rejects_a_forest_or_missing_children() {
        let forest = FlatDynamicValueV1 {
            version: FLAT_DYNAMIC_VALUE_VERSION,
            nodes: vec![FlatDynamicNodeV1::Unit, FlatDynamicNodeV1::Unit],
        };
        let bytes = postcard::to_allocvec(&forest).expect("encode malformed forest");
        assert!(postcard::from_bytes::<DynamicValue>(&bytes).is_err());

        let missing_child = FlatDynamicValueV1 {
            version: FLAT_DYNAMIC_VALUE_VERSION,
            nodes: vec![FlatDynamicNodeV1::Sequence(1)],
        };
        let bytes = postcard::to_allocvec(&missing_child).expect("encode missing child");
        assert!(postcard::from_bytes::<DynamicValue>(&bytes).is_err());
    }
}
