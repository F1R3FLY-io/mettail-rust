//! Dynamic payloads at the existing WPDA semantic-action boundary.
//!
//! Rule routing supplies already ordered arguments, captures, admitted category
//! indices, and the checked source span. These workers do not derive any of
//! those observations or interpret a second parser's rule tables.
//!
//! `OwnedActionAdapter.v` records the original reduction worker sequence;
//! `TermCategoryObservation.v` covers the borrowed category projection.
//! The caller publishes a returned carrier through `SemanticBuilder::push_term`
//! only on success, inside the existing action invocation/error boundary.

use crate::wpda_runtime::ActionInvocationError;
use mettail_grammar_core::{
    CategoryId, DynamicValue, ReductionPlan, RuntimeError, RuntimeLexicalSession, SourceSpan,
    TokenId,
};
use std::any::Any;

mod provider;
pub use provider::{OwnedActionBuildError, OwnedActionProvider};

/// Explicit WPDA category evidence, separate from a value's Rust debug tag.
/// Native evaluation may replace `value` with a scalar without erasing the
/// recognized constructor or structural holes retained in `syntax`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OwnedTerm {
    pub category: u16,
    /// Exact authored production when one fired; tokens/holes and transparent
    /// unranked boundaries carry None, never a fabricated grouping production.
    pub production: Option<mettail_grammar_core::ProductionId>,
    pub syntax: DynamicValue,
    pub value: DynamicValue,
    pub span: SourceSpan,
}

/// Observe only this carrier's category; never infer one from a type name.
pub fn term_category(value: &(dyn Any + Send + Sync)) -> Option<u16> {
    value.downcast_ref::<OwnedTerm>().map(|term| term.category)
}

/// Original VarRule argument extraction and native interning. The provider
/// checks the retained declared category's variable authority before this call.
fn native_variable(
    category: u16,
    core_category: CategoryId,
    args: Vec<crate::wpda_runtime::ActionArg>,
    span: SourceSpan,
) -> OwnedTerm {
    let arg = args.into_iter().next();
    let name = arg
        .as_ref()
        .and_then(|a| a.as_token_text())
        .unwrap_or("")
        .to_string();
    let variable = mettail_grammar_core::native_variable::get_or_create_var(name);
    let value = DynamicValue::NativeVariable { category: core_category, variable };
    OwnedTerm {
        category,
        production: None,
        syntax: value.clone(),
        value,
        span,
    }
}

/// Realize only an already-observed universal grouping boundary. The semantic
/// value, syntax, category and span remain unchanged; no production is made.
pub(super) fn grouping_boundary(
    builder: &mut crate::wpda_runtime::SemanticBuilder,
    args: Vec<crate::wpda_runtime::ActionArg>,
) -> Result<(), ActionInvocationError> {
    if args.len() != 1 {
        return Err(ActionInvocationError::Arity { expected: 1, actual: args.len() });
    }
    let crate::wpda_runtime::ActionArg::Term { value, .. } = &args[0] else {
        return Ok(());
    };
    let Some(term) = value.downcast_ref::<OwnedTerm>() else {
        return Ok(());
    };
    let mut term = term.clone();
    term.production = None;
    builder.push_term(term);
    Ok(())
}

/// Decode exactly once through the parser's original authorized worker.
/// The caller supplies the selected token and its checked source span; this
/// function does not translate token-source node IDs into byte offsets.
pub fn decode_token(
    session: &RuntimeLexicalSession<'_, '_, '_>,
    category: u16,
    token: TokenId,
    text: &str,
    span: SourceSpan,
) -> Result<OwnedTerm, ActionInvocationError> {
    let value = session
        .decode_token(token, text)
        .map_err(ActionInvocationError::RuntimeSemantic)?;
    Ok(OwnedTerm {
        category,
        production: None,
        syntax: value.clone(),
        value,
        span,
    })
}

/// Carry an already admitted structural hole without decoding or rendering it.
/// `category` is the owned engine index; `core_category` is the exact declared
/// or inferred grammar category. Their admission/mapping belongs to routing.
pub fn structural_hole(
    category: u16,
    id: u32,
    core_category: CategoryId,
    span: SourceSpan,
) -> OwnedTerm {
    let value = DynamicValue::TemplateHole { id, category: core_category };
    OwnedTerm {
        category,
        production: None,
        syntax: value.clone(),
        value,
        span,
    }
}

/// Execute the original Reduce composition on the caller's ordered payloads.
///
/// Source correspondence: runtime.rs's original Reduce arm projects values
/// before syntax, applies the same plan to each in that order, then invokes
/// native evaluation on the value inputs only when declared. Errors stop that
/// sequence immediately. Both apply calls receive the same captures and span;
/// the original legacy call's empty capture slice is the `captures = &[]` case.
/// No carrier is returned until every required worker succeeds.
pub fn reduce(
    session: &RuntimeLexicalSession<'_, '_, '_>,
    category: u16,
    plan: &ReductionPlan,
    inputs: &[OwnedTerm],
    captures: &[String],
    span: SourceSpan,
) -> Result<OwnedTerm, ActionInvocationError> {
    let semantic_inputs = inputs
        .iter()
        .map(|value| value.value.clone())
        .collect::<Vec<_>>();
    let syntax_inputs = inputs
        .iter()
        .map(|value| value.syntax.clone())
        .collect::<Vec<_>>();
    let semantic_term = plan
        .apply(&semantic_inputs, captures, span)
        .map_err(|error| {
            ActionInvocationError::RuntimeSemantic(RuntimeError::Reduction(format!("{error:?}")))
        })?;
    let syntax_term = plan
        .apply(&syntax_inputs, captures, span)
        .map_err(|error| {
            ActionInvocationError::RuntimeSemantic(RuntimeError::Reduction(format!("{error:?}")))
        })?;
    let value = if let Some(evaluation) = &plan.evaluation {
        session
            .evaluate_native(evaluation, &semantic_inputs, span)
            .map_err(ActionInvocationError::RuntimeSemantic)?
    } else {
        DynamicValue::Term(Box::new(semantic_term))
    };
    Ok(OwnedTerm {
        category,
        production: None,
        syntax: DynamicValue::Term(Box::new(syntax_term)),
        value,
        span,
    })
}

#[cfg(test)]
mod tests;
