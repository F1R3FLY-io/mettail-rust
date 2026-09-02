//! Stack-safe reflection of run-time GrammarCore syntax witnesses.
//!
//! Dynamic and compile-time grammars meet at the same `GroundTerm`/Rho image
//! boundary. GrammarCore constructor identifiers are resolved through the
//! installed core, while native leaves use reserved, injective labels. Template
//! holes remain structural `^free(name)` leaves for the existing FLT pattern and
//! construction reflectors; no hole content is ever reparsed as guest text.

use crate::rho_net_lower::{GroundTerm, FREE_VAR_REFLECT_LABEL};
use mettail_ast::types::CollectionType;
use mettail_grammar_core::{CollectionKind, DynamicValue, GrammarCoreV1};
use std::collections::BTreeMap;
use std::fmt::Write as _;

pub(crate) const TEXT_LABEL: &str = "^dynamic-text:";
pub(crate) const INTEGER_LABEL: &str = "^dynamic-integer:";
pub(crate) const BOOLEAN_LABEL: &str = "^dynamic-boolean:";
pub(crate) const UNIT_LABEL: &str = "^dynamic-unit";
pub(crate) const SEQUENCE_LABEL: &str = "^dynamic-sequence";
pub(crate) const LIST_LABEL: &str = "^dynamic-list";
pub(crate) const BAG_LABEL: &str = "^dynamic-bag";
pub(crate) const SET_LABEL: &str = "^dynamic-set";
pub(crate) const MAP_LABEL: &str = "^dynamic-map";
pub(crate) const PATHMAP_LABEL: &str = "^dynamic-pathmap";

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DynamicReflectionError {
    UnknownConstructor(u32),
    ConflictingConstructorLabel {
        constructor: u32,
        first: String,
        second: String,
    },
    UnknownHole(u32),
    InvalidHoleId(u32),
    HoleCategoryConflict(u32),
    MissingHole(u32),
    InvalidMapEntry,
}

impl std::fmt::Display for DynamicReflectionError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::UnknownConstructor(id) => {
                write!(formatter, "recognition witness names unknown constructor {id}")
            },
            Self::ConflictingConstructorLabel { constructor, first, second } => write!(
                formatter,
                "constructor {constructor} has conflicting labels `{first}` and `{second}`",
            ),
            Self::UnknownHole(id) => {
                write!(formatter, "recognition witness names unknown hole {id}")
            },
            Self::InvalidHoleId(id) => {
                write!(formatter, "recognition witness has out-of-range hole id {id}")
            },
            Self::HoleCategoryConflict(id) => {
                write!(formatter, "recognition witness infers conflicting categories for hole {id}")
            },
            Self::MissingHole(id) => {
                write!(formatter, "recognition witness does not contain declared hole {id}")
            },
            Self::InvalidMapEntry => {
                formatter.write_str("dynamic map entry is not a two-element key/value sequence")
            },
        }
    }
}

impl std::error::Error for DynamicReflectionError {}

/// Recover the category inferred for every structural template-hole id.
///
/// The parser checks each recognition alternative independently.  Callers must
/// additionally compare these vectors across alternatives because reflection
/// intentionally erases a hole's category from its `^free(name)` wire image.
/// This explicit walk keeps that cross-alternative check stack-safe.
pub fn dynamic_template_hole_categories(
    value: &DynamicValue,
    hole_count: usize,
) -> Result<Vec<mettail_grammar_core::CategoryId>, DynamicReflectionError> {
    let mut categories = vec![None; hole_count];
    let mut pending = vec![value];
    while let Some(value) = pending.pop() {
        match value {
            DynamicValue::Term(term) => pending.extend(term.fields.iter()),
            DynamicValue::TemplateHole { id, category } => {
                let slot = categories
                    .get_mut(*id as usize)
                    .ok_or(DynamicReflectionError::InvalidHoleId(*id))?;
                match slot {
                    Some(previous) if previous != category => {
                        return Err(DynamicReflectionError::HoleCategoryConflict(*id))
                    },
                    Some(_) => {},
                    None => *slot = Some(*category),
                }
            },
            DynamicValue::Sequence(values) => pending.extend(values.iter()),
            DynamicValue::Collection { entries, .. } => pending.extend(entries.iter()),
            DynamicValue::Text(_)
            | DynamicValue::Integer(_)
            | DynamicValue::Boolean(_)
            | DynamicValue::Bytes(_)
            | DynamicValue::Unit => {},
        }
    }
    categories
        .into_iter()
        .enumerate()
        .map(|(id, category)| {
            category
                .ok_or(DynamicReflectionError::MissingHole(u32::try_from(id).unwrap_or(u32::MAX)))
        })
        .collect()
}

/// Convert one GrammarCore recognition witness into the common structural
/// reflection algebra. The traversal is an explicit post-order PDA: native
/// stack consumption is independent of guest-term depth.
pub fn dynamic_syntax_to_ground_term(
    value: &DynamicValue,
    core: &GrammarCoreV1,
    hole_names: &BTreeMap<u32, String>,
) -> Result<GroundTerm, DynamicReflectionError> {
    let mut constructor_labels: Vec<Option<String>> = vec![None; core.productions.len()];
    for production in &core.productions {
        let index = production.constructor.0 as usize;
        if index >= constructor_labels.len() {
            constructor_labels.resize(index + 1, None);
        }
        match &constructor_labels[index] {
            Some(first) if first != &production.label => {
                return Err(DynamicReflectionError::ConflictingConstructorLabel {
                    constructor: production.constructor.0,
                    first: first.clone(),
                    second: production.label.clone(),
                });
            },
            Some(_) => {},
            None => constructor_labels[index] = Some(production.label.clone()),
        }
    }

    enum Task<'a> {
        Visit(&'a DynamicValue),
        AssembleTerm { constructor: u32, children: usize },
        AssembleSequence { label: &'static str, children: usize },
        AssembleCollection { kind: CollectionKind, children: usize },
    }

    let mut tasks = vec![Task::Visit(value)];
    let mut values = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            Task::Visit(value) => match value {
                DynamicValue::Term(term) => {
                    tasks.push(Task::AssembleTerm {
                        constructor: term.constructor.0,
                        children: term.fields.len(),
                    });
                    tasks.extend(term.fields.iter().rev().map(Task::Visit));
                },
                DynamicValue::TemplateHole { id, .. } => {
                    let name = hole_names
                        .get(id)
                        .ok_or(DynamicReflectionError::UnknownHole(*id))?;
                    values.push(GroundTerm::new(
                        FREE_VAR_REFLECT_LABEL,
                        vec![GroundTerm::nullary(name.clone())],
                    ));
                },
                DynamicValue::Sequence(children) => {
                    tasks.push(Task::AssembleSequence {
                        label: SEQUENCE_LABEL,
                        children: children.len(),
                    });
                    tasks.extend(children.iter().rev().map(Task::Visit));
                },
                DynamicValue::Collection { kind, entries } => {
                    tasks.push(Task::AssembleCollection { kind: *kind, children: entries.len() });
                    tasks.extend(entries.iter().rev().map(Task::Visit));
                },
                DynamicValue::Text(text) => {
                    values.push(GroundTerm::nullary(atom_label(TEXT_LABEL, text.as_bytes())));
                },
                DynamicValue::Integer(integer) => {
                    values.push(GroundTerm::nullary(format!("{INTEGER_LABEL}{integer}")));
                },
                DynamicValue::Boolean(boolean) => {
                    values.push(GroundTerm::nullary(format!("{BOOLEAN_LABEL}{boolean}")));
                },
                DynamicValue::Bytes(bytes) => {
                    values.push(GroundTerm::bytes(bytes));
                },
                DynamicValue::Unit => values.push(GroundTerm::nullary(UNIT_LABEL)),
            },
            Task::AssembleTerm { constructor, children } => {
                let fields = take_children(&mut values, children);
                let label = constructor_labels
                    .get(constructor as usize)
                    .and_then(Option::as_ref)
                    .ok_or(DynamicReflectionError::UnknownConstructor(constructor))?;
                values.push(GroundTerm::new(label.clone(), fields));
            },
            Task::AssembleSequence { label, children } => {
                let fields = take_children(&mut values, children);
                values.push(GroundTerm::new(label, fields));
            },
            Task::AssembleCollection { kind, children } => {
                let entries = take_children(&mut values, children);
                let term = match kind {
                    CollectionKind::List => GroundTerm::new(LIST_LABEL, entries),
                    CollectionKind::Bag => {
                        GroundTerm::collection(CollectionType::HashBag, BAG_LABEL, entries)
                    },
                    CollectionKind::Set => {
                        GroundTerm::collection(CollectionType::HashSet, SET_LABEL, entries)
                    },
                    CollectionKind::Map => GroundTerm::collection(
                        CollectionType::HashMap,
                        MAP_LABEL,
                        map_entries(entries)?,
                    ),
                    CollectionKind::PathMap => GroundTerm::new(PATHMAP_LABEL, entries),
                };
                values.push(term);
            },
        }
    }
    debug_assert_eq!(values.len(), 1);
    values
        .pop()
        .ok_or(DynamicReflectionError::UnknownConstructor(u32::MAX))
}

fn take_children(values: &mut Vec<GroundTerm>, children: usize) -> Vec<GroundTerm> {
    let first = values
        .len()
        .checked_sub(children)
        .expect("dynamic reflection PDA lost a child result");
    values.split_off(first)
}

fn map_entries(entries: Vec<GroundTerm>) -> Result<Vec<GroundTerm>, DynamicReflectionError> {
    entries
        .into_iter()
        .map(|mut entry| {
            if entry.constructor != SEQUENCE_LABEL || entry.children.len() != 2 {
                return Err(DynamicReflectionError::InvalidMapEntry);
            }
            let mut fields = std::mem::take(&mut entry.children).into_iter();
            let key = fields.next().expect("checked pair arity");
            let value = fields.next().expect("checked pair arity");
            Ok(GroundTerm::map_entry(key, value))
        })
        .collect()
}

fn atom_label(prefix: &str, bytes: &[u8]) -> String {
    let mut label = String::with_capacity(prefix.len() + bytes.len() * 2);
    label.push_str(prefix);
    for byte in bytes {
        write!(&mut label, "{byte:02x}").expect("String writes are infallible");
    }
    label
}

#[cfg(test)]
mod tests {
    use super::*;
    use mettail_grammar_core::{
        CategoryId, ConstructorId, DynamicTerm, Production, ProductionId, SourceSpan,
    };

    #[test]
    fn deep_dynamic_syntax_reflects_on_a_small_native_stack() {
        let mut core = GrammarCoreV1::new("Deep");
        core.productions.push(Production {
            id: ProductionId(0),
            constructor: ConstructorId(0),
            label: "Node".into(),
            result: CategoryId(0),
            syntax: Vec::new(),
            precedence: Default::default(),
            classification: Default::default(),
            reduction: 0,
            provenance: None,
        });

        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(move || {
                let mut value = DynamicValue::Unit;
                for _ in 0..20_000 {
                    value = DynamicValue::Term(Box::new(DynamicTerm {
                        category: CategoryId(0),
                        constructor: ConstructorId(0),
                        fields: vec![value],
                        span: SourceSpan::default(),
                    }));
                }
                let reflected = dynamic_syntax_to_ground_term(&value, &core, &BTreeMap::new())
                    .expect("deep syntax reflects");
                assert_eq!(reflected.constructor, "Node");
            })
            .expect("spawn constrained-stack reflection")
            .join()
            .expect("dynamic reflection is stack-safe");
    }

    #[test]
    fn holes_remain_structural_free_leaves() {
        let value = DynamicValue::TemplateHole { id: 0, category: CategoryId(7) };
        let reflected = dynamic_syntax_to_ground_term(
            &value,
            &GrammarCoreV1::new("Hole"),
            &BTreeMap::from([(0, "x".into())]),
        )
        .expect("hole reflects");
        assert_eq!(reflected.constructor, FREE_VAR_REFLECT_LABEL);
        assert_eq!(reflected.children[0].constructor, "x");
    }
}
