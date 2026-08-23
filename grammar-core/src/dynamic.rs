use crate::{CategoryId, ConstructorId};
use serde::{Deserialize, Serialize};

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct SourceSpan {
    pub start: u32,
    pub end: u32,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum DynamicValue {
    Term(Box<DynamicTerm>),
    Sequence(Vec<DynamicValue>),
    Text(String),
    Integer(i128),
    Boolean(bool),
    Bytes(Vec<u8>),
    Unit,
}

/// Language-independent result of a runtime reduction.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
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
