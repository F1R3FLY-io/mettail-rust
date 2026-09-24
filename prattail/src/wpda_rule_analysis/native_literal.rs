//! The original outer patterned-literal eligibility helper.
//!
//! Name identity lookup and spelling-based family lookup remain distinct.
//! Native evaluation is an opaque callback payload, never evaluated here.
//! `NativeLiteralEligibility.v` models this exact observation schedule.

use super::native_first::LiteralFamily;
use mettail_grammar_core::NativeKind;

pub struct LiteralPatternedPayload<N, L, E> {
    pub cat_name: String,
    pub native_type: N,
    pub family: LiteralFamily,
    pub wrapper_variant: L,
    pub evaluation: E,
}

/// Original source observations; native_type performs the original optional
/// read and clone at its call site. A retained owned reader may return a borrow
/// of its complete native declaration instead. A missing label observation is
/// an error; absence of native type or an evaluator remains structural refusal.
pub trait LiteralPatternedReader<'source> {
    type Name: Copy + ToString;
    type Category: 'source;
    type Native;
    type Label;
    type Evaluation;
    type Token: Copy;
    type Error;
    fn categories(&self) -> &'source [Self::Category];
    fn category_name(&self, category: &'source Self::Category) -> Self::Name;
    fn names_equal(&self, left: Self::Name, right: Self::Name) -> bool;
    fn native_type(&self, category: &'source Self::Category) -> Option<Self::Native>;
    fn native_kind(&self, native: &Self::Native) -> NativeKind;
    fn literal_family(&self, category: &str) -> Option<LiteralFamily>;
    fn literal_label(&mut self, native: &Self::Native) -> Result<Self::Label, Self::Error>;
    fn declared_token(&self, category: &str) -> Option<Self::Token>;
    fn evaluation(&self, token: Self::Token) -> Option<Self::Evaluation>;
    fn default_evaluation(&self, kind: &NativeKind) -> Option<Self::Evaluation>;
}

/// Invoke the original helper once, preserving lazy fallback and callback order.
pub fn try_classify_literal_patterned<'source, R: LiteralPatternedReader<'source>>(
    name: R::Name,
    reader: &mut R,
) -> Result<Option<LiteralPatternedPayload<R::Native, R::Label, R::Evaluation>>, R::Error> {
    let cat_name = name.to_string();
    let Some(category) = reader
        .categories()
        .iter()
        .find(|category| reader.names_equal(reader.category_name(category), name))
    else {
        return Ok(None);
    };
    let Some(native_type) = reader.native_type(category) else {
        return Ok(None);
    };
    let kind = reader.native_kind(&native_type);
    let Some(family) = reader.literal_family(&cat_name) else {
        return Ok(None);
    };
    let wrapper_variant = reader.literal_label(&native_type)?;
    if let Some(token) = reader.declared_token(&cat_name) {
        if let Some(evaluation) = reader.evaluation(token) {
            return Ok(Some(LiteralPatternedPayload {
                cat_name,
                native_type,
                family,
                wrapper_variant,
                evaluation,
            }));
        }
    }
    let Some(evaluation) = reader.default_evaluation(&kind) else {
        return Ok(None);
    };
    Ok(Some(LiteralPatternedPayload {
        cat_name,
        native_type,
        family,
        wrapper_variant,
        evaluation,
    }))
}
