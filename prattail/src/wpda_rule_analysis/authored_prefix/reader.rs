//! Occurrence identity around the existing authored reader. Only the Rule
//! handle changes; every syntax/type/name observation is forwarded unchanged.

use super::super::authored::{AuthoredNameRef, AuthoredRuleReader};
use super::super::authored_synthesis::AuthoredRulePayload;
use super::super::binder::optional::{
    BinderSyntaxObservation, BinderSyntaxReader, OptionalOperationObservation,
};
use super::super::binder::rule::{BinderRuleReader, BinderTypeObservation, MapZipObservation};
use super::super::binder::term_param::{TermParamObservation, TermParamReader};
use mettail_grammar_core::{
    AuthoredNamesId, AuthoredOperationId, AuthoredParamId, AuthoredParamsId, AuthoredSyntaxId,
    AuthoredTypeId,
};
use std::borrow::Borrow;
use std::marker::PhantomData;

pub(in crate::wpda_rule_analysis) struct OccurrenceReader<'reader, 'store, H = AuthoredRulePayload>
{
    pub(in crate::wpda_rule_analysis) inner: &'reader AuthoredRuleReader<'store>,
    handle: PhantomData<H>,
}

impl<'reader, 'store, H> OccurrenceReader<'reader, 'store, H> {
    pub(in crate::wpda_rule_analysis) fn new(inner: &'reader AuthoredRuleReader<'store>) -> Self {
        Self { inner, handle: PhantomData }
    }
}

impl<'store, H> TermParamReader<'store> for OccurrenceReader<'_, 'store, H> {
    type Parameters = AuthoredParamsId;
    type Param = AuthoredParamId;
    type Name = AuthoredNameRef<'store>;
    type Type = AuthoredTypeId;
    fn params_len(&self, params: Self::Parameters) -> usize {
        self.inner.params_len(params)
    }
    fn param_at(&self, params: Self::Parameters, index: usize) -> Option<Self::Param> {
        self.inner.param_at(params, index)
    }
    fn param(
        &self,
        param: Self::Param,
    ) -> TermParamObservation<Self::Name, Self::Parameters, Self::Type> {
        self.inner.param(param)
    }
}
impl<'store, H> BinderSyntaxReader<'store> for OccurrenceReader<'_, 'store, H> {
    type Sequence = AuthoredSyntaxId;
    type Name = AuthoredNameRef<'store>;
    type Operation = AuthoredOperationId;
    fn sequence_len(&self, sequence: Self::Sequence) -> usize {
        self.inner.sequence_len(sequence)
    }
    fn at(
        &self,
        sequence: Self::Sequence,
        index: usize,
    ) -> Option<BinderSyntaxObservation<'store, Self::Name, Self::Operation>> {
        self.inner.at(sequence, index)
    }
    fn operation(
        &self,
        operation: Self::Operation,
    ) -> OptionalOperationObservation<'store, Self::Name, Self::Sequence, Self::Operation> {
        self.inner.operation(operation)
    }
}
impl<'store, H: Copy + Borrow<AuthoredRulePayload>> BinderRuleReader<'store>
    for OccurrenceReader<'_, 'store, H>
{
    type Rule = H;
    type Names = AuthoredNamesId;
    fn term_context(&self, rule: Self::Rule) -> Option<Self::Parameters> {
        self.inner.term_context(rule.borrow().rule)
    }
    fn syntax_pattern(&self, rule: Self::Rule) -> Option<Self::Sequence> {
        self.inner.syntax_pattern(rule.borrow().rule)
    }
    fn label(&self, rule: Self::Rule) -> AuthoredNameRef<'store> {
        self.inner.label(rule.borrow().rule)
    }
    fn category(&self, rule: Self::Rule) -> AuthoredNameRef<'store> {
        self.inner.category(rule.borrow().rule)
    }
    fn ty(
        &self,
        ty: Self::Type,
    ) -> BinderTypeObservation<'store, AuthoredNameRef<'store>, Self::Type> {
        self.inner.ty(ty)
    }
    fn names_len(&self, names: Self::Names) -> usize {
        self.inner.names_len(names)
    }
    fn name_at(&self, names: Self::Names, index: usize) -> Option<AuthoredNameRef<'store>> {
        self.inner.name_at(names, index)
    }
    fn names_equal(&self, left: AuthoredNameRef<'store>, right: AuthoredNameRef<'store>) -> bool {
        self.inner.names_equal(left, right)
    }
    fn map_zip_operation(
        &self,
        operation: Self::Operation,
    ) -> MapZipObservation<AuthoredNameRef<'store>, Self::Names, Self::Sequence, Self::Operation>
    {
        self.inner.map_zip_operation(operation)
    }
}
