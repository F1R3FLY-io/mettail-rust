//! The original macro infix projection over existing shallow rule readers.
//!
//! This supplies `InfixRuleShape` to the unchanged classifier; it neither
//! normalizes rules nor traverses nested unsupported syntax. A runtime caller
//! prepays the whole supplied rule domain before reads, copies, and temporary
//! storage. The admission callback is not a constant-cost token. Valid handles
//! and immutable reader observations are the existing reader preconditions.
//! `InfixClassifierProjection.v` and `AuthoredInfixProjection.v` state the
//! observation and source-order laws; they are not extracted Rust proofs.

use super::binder::optional::{
    BinderSyntaxObservation, BinderSyntaxReader, OptionalOperationObservation,
};
use super::binder::rule::{BinderRuleReader, BinderTypeObservation};
use super::binder::term_param::TermParamObservation;
use super::{InfixParamShape, InfixRuleShape, InfixSyntaxShape, InfixTypeShape};
use mettail_grammar_core::Associativity;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum InfixProjectionError<E> {
    Admission(E),
    Allocation,
    InvalidParameterIndex(usize),
    InvalidSyntaxIndex(usize),
    UnsupportedNonAssociativity,
}

/// Project exactly the original shallow observations, retaining every position.
///
/// Nonassociativity has no representation in the original right-associative
/// Boolean and is refused, not silently converted to left associativity.
/// Explicit prefix binding power is deliberately not an input to this worker.
/// Only complete success publishes a shape. Logical prepayment does not claim
/// physical allocator-failure recovery for arbitrary Display implementations.
pub fn try_project_infix_rule_in<'syntax, R, E>(
    reader: &R,
    rule: R::Rule,
    associativity: Associativity,
    shares_level_with_previous: bool,
    admit: impl FnOnce(&R, R::Rule) -> Result<(), E>,
) -> Result<InfixRuleShape, InfixProjectionError<E>>
where
    R: BinderRuleReader<'syntax>,
    <R as BinderSyntaxReader<'syntax>>::Name: std::fmt::Display,
{
    let is_right_assoc = match associativity {
        Associativity::Left => false,
        Associativity::Right => true,
        Associativity::NonAssociative => {
            return Err(InfixProjectionError::UnsupportedNonAssociativity);
        },
    };
    admit(reader, rule).map_err(InfixProjectionError::Admission)?;
    let label = reader.label(rule).to_string();
    let category = reader.category(rule).to_string();
    let term_context = if let Some(params) = reader.term_context(rule) {
        let count = reader.params_len(params);
        let mut output = Vec::new();
        output
            .try_reserve_exact(count)
            .map_err(|_| InfixProjectionError::Allocation)?;
        for index in 0..count {
            let param = reader
                .param_at(params, index)
                .ok_or(InfixProjectionError::InvalidParameterIndex(index))?;
            output.push(match reader.param(param) {
                TermParamObservation::Simple { name, ty } => InfixParamShape::Simple {
                    name: name.to_string(),
                    ty: project_type(reader, ty),
                },
                _ => InfixParamShape::Other,
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
            .map_err(|_| InfixProjectionError::Allocation)?;
        for index in 0..count {
            let item = reader
                .at(syntax, index)
                .ok_or(InfixProjectionError::InvalidSyntaxIndex(index))?;
            output.push(match item {
                BinderSyntaxObservation::Literal(text) => {
                    InfixSyntaxShape::Literal(text.to_owned())
                },
                BinderSyntaxObservation::Param(name) => InfixSyntaxShape::Param(name.to_string()),
                BinderSyntaxObservation::Op(operation) => match reader.operation(operation) {
                    OptionalOperationObservation::Sep { collection, separator, .. } => {
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
    Ok(InfixRuleShape {
        label,
        category,
        is_right_assoc,
        shares_level_with_previous,
        term_context,
        syntax_pattern,
    })
}

fn project_type<'syntax, R>(reader: &R, ty: R::Type) -> InfixTypeShape
where
    R: BinderRuleReader<'syntax>,
    <R as BinderSyntaxReader<'syntax>>::Name: std::fmt::Display,
{
    match reader.ty(ty) {
        BinderTypeObservation::Base(name) => InfixTypeShape::Base(name.to_string()),
        BinderTypeObservation::Collection { element, .. } => InfixTypeShape::Collection {
            element_base: match reader.ty(element) {
                BinderTypeObservation::Base(name) => Some(name.to_string()),
                _ => None,
            },
        },
        _ => InfixTypeShape::Other,
    }
}
