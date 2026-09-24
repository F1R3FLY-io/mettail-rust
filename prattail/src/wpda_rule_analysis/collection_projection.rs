//! The original collection projection through existing shallow rule readers.
//!
//! Every top-level position is retained. Unlike the infix projection, a
//! separator with a source operation remains unsupported here. Collection kinds
//! are borrowed until the existing classifier chooses its original clone site;
//! neither nested types nor unsupported syntax are traversed or reconstructed.
//! `CollectionReaderProjection.v` composes this boundary with the existing
//! `CollectionClassifierProjection.v` classifier laws.

use super::binder::optional::{BinderSyntaxObservation, OptionalOperationObservation};
use super::binder::rule::{BinderRuleReader, BinderTypeObservation};
use super::binder::term_param::TermParamObservation;
use super::collection::{CollectionParamShape, CollectionRuleShape};
use super::InfixSyntaxShape;
use mettail_ast::types::CollectionType;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CollectionProjectionError<E> {
    Admission(E),
    Allocation,
    InvalidParameterIndex(usize),
    InvalidSyntaxIndex(usize),
}

/// Project exactly the original label, ordered parameters, and ordered syntax.
///
/// Admission prepays the entire supplied rule domain before any reader access,
/// copies, or temporary storage. It is not a constant-cost token. Reader handles
/// must already be valid and immutable. Only complete success publishes a view;
/// logical prepayment does not establish physical allocation-failure recovery
/// for arbitrary name-formatting implementations.
pub fn try_project_collection_rule_in<'syntax, R, E>(
    reader: &R,
    rule: R::Rule,
    admit: impl FnOnce(&R, R::Rule) -> Result<(), E>,
) -> Result<CollectionRuleShape<'syntax, CollectionType>, CollectionProjectionError<E>>
where
    R: BinderRuleReader<'syntax>,
{
    admit(reader, rule).map_err(CollectionProjectionError::Admission)?;
    let label = reader.label(rule).to_string();
    let term_context = if let Some(params) = reader.term_context(rule) {
        let count = reader.params_len(params);
        let mut output = Vec::new();
        output
            .try_reserve_exact(count)
            .map_err(|_| CollectionProjectionError::Allocation)?;
        for index in 0..count {
            let param = reader
                .param_at(params, index)
                .ok_or(CollectionProjectionError::InvalidParameterIndex(index))?;
            output.push(match reader.param(param) {
                TermParamObservation::Simple { name, ty } => match reader.ty(ty) {
                    BinderTypeObservation::Collection { coll_type, element } => {
                        CollectionParamShape::SimpleCollection {
                            name: name.to_string(),
                            kind: coll_type,
                            element_base: match reader.ty(element) {
                                BinderTypeObservation::Base(element) => Some(element.to_string()),
                                _ => None,
                            },
                        }
                    },
                    _ => CollectionParamShape::Other,
                },
                _ => CollectionParamShape::Other,
            });
        }
        Some(output)
    } else {
        None
    };
    let syntax_pattern = if let Some(syntax) = reader.syntax_pattern(rule) {
        let count = reader.sequence_len(syntax);
        let mut output = Vec::new();
        output
            .try_reserve_exact(count)
            .map_err(|_| CollectionProjectionError::Allocation)?;
        for index in 0..count {
            let item = reader
                .at(syntax, index)
                .ok_or(CollectionProjectionError::InvalidSyntaxIndex(index))?;
            output.push(match item {
                BinderSyntaxObservation::Literal(text) => {
                    InfixSyntaxShape::Literal(text.to_owned())
                },
                BinderSyntaxObservation::Param(name) => InfixSyntaxShape::Param(name.to_string()),
                BinderSyntaxObservation::Op(operation) => match reader.operation(operation) {
                    OptionalOperationObservation::Sep { collection, separator, source: None } => {
                        InfixSyntaxShape::Sep {
                            collection: collection.to_string(),
                            separator: separator.to_owned(),
                        }
                    },
                    _ => InfixSyntaxShape::Other,
                },
                _ => InfixSyntaxShape::Other,
            });
        }
        Some(output)
    } else {
        None
    };
    Ok(CollectionRuleShape { label, term_context, syntax_pattern })
}
