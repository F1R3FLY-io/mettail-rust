//! Fallible observations for the original FIRST and identifier workers.
//!
//! Each error stops at its observation: no later callback is evaluated and no
//! partial worker result is returned. Existing infallible contexts forward
//! through the same workers with `Infallible`. Source-reader and formatter laws
//! remain those of the original context traits; arbitrary callbacks are not
//! certified by the finite interface model in `PrefixCallbackFailure.v`.

use super::super::atomic::AtomicDescriptor;
use super::super::binder::optional::BinderSyntaxReader;
use super::super::binder::rule::BinderRuleReader;
use super::{FirstLegacyItem, FirstPredicate, FirstSetContext, IdentSummaryContext};
use std::convert::Infallible;

/// Fallible counterpart of every original FIRST source observation.
pub trait TryFirstSetContext<'source, R: BinderRuleReader<'source>> {
    type Error;
    type Category: Copy;
    type Literal;
    type Pattern: ToString;
    fn try_rules_len(&self) -> Result<usize, Self::Error>;
    fn try_rule_at(&self, index: usize) -> Result<R::Rule, Self::Error>;
    fn try_find_category(&mut self, name: &str) -> Result<Option<Self::Category>, Self::Error>;
    fn try_is_data(&self, category: Self::Category) -> Result<bool, Self::Error>;
    fn try_collection_open(
        &self,
        category: Self::Category,
    ) -> Result<Option<&'source str>, Self::Error>;
    fn try_legacy_first(
        &self,
        rule: R::Rule,
    ) -> Result<
        Option<FirstLegacyItem<'source, <R as BinderSyntaxReader<'source>>::Name>>,
        Self::Error,
    >;
    fn try_native_first(
        &mut self,
        category: Self::Category,
        name: &str,
    ) -> Result<Vec<(Self::Pattern, Option<Self::Pattern>)>, Self::Error>;
    fn try_atomic(&mut self, rule: R::Rule)
        -> Result<AtomicDescriptor<Self::Literal>, Self::Error>;
    fn try_patterned_first(
        &mut self,
        literal: Self::Literal,
    ) -> Result<Vec<(Self::Pattern, Option<Self::Pattern>)>, Self::Error>;
    fn try_binder_leading(&mut self, rule: R::Rule) -> Result<Option<String>, Self::Error>;
    fn try_predicate_parts(
        &mut self,
        predicate: FirstPredicate<'_>,
    ) -> Result<(Self::Pattern, Option<Self::Pattern>), Self::Error>;
}

/// Additional fallible observations for the original identifier summaries.
pub trait TryIdentSummaryContext<'source, R: BinderRuleReader<'source>>:
    TryFirstSetContext<'source, R>
{
    fn try_categories_len(&self) -> Result<usize, Self::Error>;
    fn try_category_at(&self, index: usize) -> Result<Self::Category, Self::Error>;
    fn try_category_spelling(&self, category: Self::Category) -> Result<String, Self::Error>;
    fn try_legacy_len(&self, rule: R::Rule) -> Result<usize, Self::Error>;
    fn try_legacy_at(
        &self,
        rule: R::Rule,
        index: usize,
    ) -> Result<
        Option<FirstLegacyItem<'source, <R as BinderSyntaxReader<'source>>::Name>>,
        Self::Error,
    >;
}

impl<'source, R, C> TryFirstSetContext<'source, R> for C
where
    R: BinderRuleReader<'source>,
    C: FirstSetContext<'source, R>,
{
    type Error = Infallible;
    type Category = <C as FirstSetContext<'source, R>>::Category;
    type Literal = <C as FirstSetContext<'source, R>>::Literal;
    type Pattern = <C as FirstSetContext<'source, R>>::Pattern;
    fn try_rules_len(&self) -> Result<usize, Self::Error> {
        Ok(<C as FirstSetContext<'source, R>>::rules_len(self))
    }
    fn try_rule_at(&self, index: usize) -> Result<R::Rule, Self::Error> {
        Ok(<C as FirstSetContext<'source, R>>::rule_at(self, index))
    }
    fn try_find_category(&mut self, name: &str) -> Result<Option<Self::Category>, Self::Error> {
        Ok(<C as FirstSetContext<'source, R>>::find_category(self, name))
    }
    fn try_is_data(&self, category: Self::Category) -> Result<bool, Self::Error> {
        Ok(<C as FirstSetContext<'source, R>>::is_data(self, category))
    }
    fn try_collection_open(
        &self,
        category: Self::Category,
    ) -> Result<Option<&'source str>, Self::Error> {
        Ok(<C as FirstSetContext<'source, R>>::collection_open(self, category))
    }
    fn try_legacy_first(
        &self,
        rule: R::Rule,
    ) -> Result<
        Option<FirstLegacyItem<'source, <R as BinderSyntaxReader<'source>>::Name>>,
        Self::Error,
    > {
        Ok(<C as FirstSetContext<'source, R>>::legacy_first(self, rule))
    }
    fn try_native_first(
        &mut self,
        category: Self::Category,
        name: &str,
    ) -> Result<Vec<(Self::Pattern, Option<Self::Pattern>)>, Self::Error> {
        Ok(<C as FirstSetContext<'source, R>>::native_first(self, category, name))
    }
    fn try_atomic(
        &mut self,
        rule: R::Rule,
    ) -> Result<AtomicDescriptor<Self::Literal>, Self::Error> {
        Ok(<C as FirstSetContext<'source, R>>::atomic(self, rule))
    }
    fn try_patterned_first(
        &mut self,
        literal: Self::Literal,
    ) -> Result<Vec<(Self::Pattern, Option<Self::Pattern>)>, Self::Error> {
        Ok(<C as FirstSetContext<'source, R>>::patterned_first(self, literal))
    }
    fn try_binder_leading(&mut self, rule: R::Rule) -> Result<Option<String>, Self::Error> {
        Ok(<C as FirstSetContext<'source, R>>::binder_leading(self, rule))
    }
    fn try_predicate_parts(
        &mut self,
        predicate: FirstPredicate<'_>,
    ) -> Result<(Self::Pattern, Option<Self::Pattern>), Self::Error> {
        Ok(<C as FirstSetContext<'source, R>>::predicate_parts(self, predicate))
    }
}

impl<'source, R, C> TryIdentSummaryContext<'source, R> for C
where
    R: BinderRuleReader<'source>,
    C: IdentSummaryContext<'source, R>,
{
    fn try_categories_len(&self) -> Result<usize, Self::Error> {
        Ok(<C as IdentSummaryContext<'source, R>>::categories_len(self))
    }
    fn try_category_at(&self, index: usize) -> Result<Self::Category, Self::Error> {
        Ok(<C as IdentSummaryContext<'source, R>>::category_at(self, index))
    }
    fn try_category_spelling(&self, category: Self::Category) -> Result<String, Self::Error> {
        Ok(<C as IdentSummaryContext<'source, R>>::category_spelling(self, category))
    }
    fn try_legacy_len(&self, rule: R::Rule) -> Result<usize, Self::Error> {
        Ok(<C as IdentSummaryContext<'source, R>>::legacy_len(self, rule))
    }
    fn try_legacy_at(
        &self,
        rule: R::Rule,
        index: usize,
    ) -> Result<
        Option<FirstLegacyItem<'source, <R as BinderSyntaxReader<'source>>::Name>>,
        Self::Error,
    > {
        Ok(<C as IdentSummaryContext<'source, R>>::legacy_at(self, rule, index))
    }
}
