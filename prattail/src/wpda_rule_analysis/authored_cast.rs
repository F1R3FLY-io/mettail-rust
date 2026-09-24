//! Source observations for the original numeric-cast participation worker.
//!
//! The rendered-trigger lookup is deliberately supplied by the producer: a
//! retained source name does not prove equality with a newly constructed source
//! identifier. Unknown observations and nonunique object-category elections are
//! errors, never `false`. This adapter neither evaluates casts nor parses source.

use super::authored::{AuthoredNameRef, AuthoredRuleReader};
use super::cast_participation::{try_cast_machinery_participates, CastObservationContext};
use mettail_ast::language::NativeKind;
use mettail_grammar_core::{AuthoredRuleId, SourceObservation};
use std::collections::HashMap;

#[derive(Debug, PartialEq, Eq)]
pub enum AuthoredCastError<E> {
    MissingDeclarations,
    SourceBodyUnavailable(AuthoredRuleId),
    ExplicitFoldUnavailable(AuthoredRuleId),
    RenderedTrigger(E),
    AmbiguousObjectCategory,
}

struct Context<'reader, 'store, F> {
    reader: &'reader AuthoredRuleReader<'store>,
    trigger_native_kind: F,
}

impl<'store, E, F> CastObservationContext<'store, AuthoredRuleReader<'store>>
    for Context<'_, 'store, F>
where
    F: FnMut(&str) -> Result<Option<NativeKind>, E>,
{
    type Error = AuthoredCastError<E>;

    fn try_source_body_present(&mut self, rule: AuthoredRuleId) -> Result<bool, Self::Error> {
        match self.reader.rule(rule).source_body_present {
            SourceObservation::Known(value) => Ok(value),
            SourceObservation::Unavailable => Err(AuthoredCastError::SourceBodyUnavailable(rule)),
        }
    }

    fn try_explicit_fold(&mut self, rule: AuthoredRuleId) -> Result<bool, Self::Error> {
        match self.reader.rule(rule).explicit_fold {
            SourceObservation::Known(value) => Ok(value),
            SourceObservation::Unavailable => Err(AuthoredCastError::ExplicitFoldUnavailable(rule)),
        }
    }

    fn try_native_kind(
        &mut self,
        name: AuthoredNameRef<'store>,
    ) -> Result<Option<NativeKind>, Self::Error> {
        let declarations = self
            .reader
            .declarations()
            .ok_or(AuthoredCastError::MissingDeclarations)?;
        Ok(declarations
            .categories
            .iter()
            .find(|row| {
                self.reader.name(row.name).payload().equality_class == name.payload().equality_class
            })
            .and_then(|row| row.native))
    }

    fn try_trigger_native_kind(&mut self, text: &str) -> Result<Option<NativeKind>, Self::Error> {
        (self.trigger_native_kind)(text).map_err(AuthoredCastError::RenderedTrigger)
    }

    fn try_elect_object_category(
        &mut self,
        counts: &HashMap<String, (AuthoredNameRef<'store>, usize)>,
    ) -> Result<Option<AuthoredNameRef<'store>>, Self::Error> {
        let Some((winner_key, (winner, maximum))) =
            counts.iter().max_by_key(|(_, (_, count))| *count)
        else {
            return Ok(None);
        };
        if counts
            .iter()
            .any(|(key, (_, count))| key != winner_key && count == maximum)
        {
            return Err(AuthoredCastError::AmbiguousObjectCategory);
        }
        Ok(Some(*winner))
    }
}

/// Observe validated rule handles from this reader, preserving the complete
/// original source roster, including order and duplicates. The caller admits
/// the finite work before entering, as for the surrounding descriptor assembly.
/// `CastSourceObservation.v` covers the checked source/election interface;
/// comparison against original macro observations supplies source correspondence.
pub fn try_authored_cast_participates<'store, E>(
    reader: &'store AuthoredRuleReader<'store>,
    rule: AuthoredRuleId,
    original_rules: impl IntoIterator<Item = AuthoredRuleId>,
    trigger_native_kind: impl FnMut(&str) -> Result<Option<NativeKind>, E>,
) -> Result<bool, AuthoredCastError<E>> {
    let mut context = Context { reader, trigger_native_kind };
    try_cast_machinery_participates(reader, rule, original_rules, &mut context)
}
