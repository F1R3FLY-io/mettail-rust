//! Original numeric-cast participation helpers over the existing borrowed reader.
//!
//! This is parser descriptor eligibility, not cast evaluation. Source body/Fold
//! facts and native lookup remain checked caller observations. The original
//! HashMap election is explicit: the static caller preserves its election;
//! owned callers must reject an ambiguous election rather than invent a winner.

use super::binder::optional::{BinderSyntaxObservation, BinderSyntaxReader};
use super::binder::rule::{BinderRuleReader, BinderTypeObservation};
use super::binder::term_param::TermParamObservation;
use mettail_grammar_core::NativeKind;
use std::collections::HashMap;

pub type CastName<'source, R> = <R as BinderSyntaxReader<'source>>::Name;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Arity {
    Int,
    UInt,
    Float,
    Fixed,
    BigInt,
    BigRat,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Flavor {
    Native,
    Object,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CastFold<Name> {
    pub label: Name,
    pub output_cat: Name,
    pub arity: Option<Arity>,
    pub flavor: Flavor,
    pub is_binary: bool,
}

/// The original native-output arity predicate.
pub fn arity_of_kind(kind: NativeKind) -> Option<Arity> {
    Some(match kind {
        NativeKind::Int8
        | NativeKind::Int16
        | NativeKind::Int32
        | NativeKind::Int64
        | NativeKind::Int128
        | NativeKind::Isize => Arity::Int,
        NativeKind::UInt8 | NativeKind::UInt16 | NativeKind::UInt32 => Arity::UInt,
        NativeKind::Float32 | NativeKind::Float64 => Arity::Float,
        NativeKind::CanonicalFixedPoint => Arity::Fixed,
        NativeKind::CanonicalBigInt => Arity::BigInt,
        NativeKind::CanonicalBigRat => Arity::BigRat,
        _ => return None,
    })
}

/// Original adapter carrier eligibility, deliberately including Bool and Str.
pub fn is_numeric_kind(kind: NativeKind) -> bool {
    matches!(
        kind,
        NativeKind::Int8
            | NativeKind::Int16
            | NativeKind::Int32
            | NativeKind::Int64
            | NativeKind::Int128
            | NativeKind::Isize
            | NativeKind::UInt8
            | NativeKind::UInt16
            | NativeKind::UInt32
            | NativeKind::Float32
            | NativeKind::Float64
            | NativeKind::Bool
            | NativeKind::Str
            | NativeKind::CanonicalBigInt
            | NativeKind::CanonicalBigRat
            | NativeKind::CanonicalFixedPoint
    )
}

pub trait CastObservationContext<'source, R: BinderRuleReader<'source>> {
    type Error;
    fn try_source_body_present(&mut self, rule: R::Rule) -> Result<bool, Self::Error>;
    fn try_explicit_fold(&mut self, rule: R::Rule) -> Result<bool, Self::Error>;
    fn try_native_kind(
        &mut self,
        name: CastName<'source, R>,
    ) -> Result<Option<NativeKind>, Self::Error>;
    /// Preserve the original rendered-string -> fresh identifier -> type lookup.
    /// Missing observations or invalid reconstruction are errors, not nonmatches.
    fn try_trigger_native_kind(
        &mut self,
        spelling: &str,
    ) -> Result<Option<NativeKind>, Self::Error>;
    fn try_elect_object_category(
        &mut self,
        counts: &HashMap<String, (CastName<'source, R>, usize)>,
    ) -> Result<Option<CastName<'source, R>>, Self::Error>;
}

pub fn simple_param_cat_in<'source, R: BinderRuleReader<'source>>(
    reader: &'source R,
    param: R::Param,
) -> Option<CastName<'source, R>> {
    match reader.param(param) {
        TermParamObservation::Simple { ty, .. } => match reader.ty(ty) {
            BinderTypeObservation::Base(category) => Some(category),
            _ => None,
        },
        _ => None,
    }
}

/// The exact original leading-literal unary-wrapper shape helper.
pub fn trigger_unary_wrapper_source_cat_in<'source, R: BinderRuleReader<'source>>(
    reader: &'source R,
    rule: R::Rule,
) -> Option<String> {
    let tc = reader.term_context(rule)?;
    if reader.params_len(tc) != 1 {
        return None;
    }
    let TermParamObservation::Simple { name: param_name, ty } =
        reader.param(reader.param_at(tc, 0)?)
    else {
        return None;
    };
    let BinderTypeObservation::Base(source_ident) = reader.ty(ty) else {
        return None;
    };
    let sp = reader.syntax_pattern(rule)?;
    if !matches!(reader.at(sp, 0), Some(BinderSyntaxObservation::Literal(_))) {
        return None;
    }
    let refs_param = (0..reader.sequence_len(sp)).any(|index| {
        matches!(reader.at(sp, index), Some(BinderSyntaxObservation::Param(syn_name))
            if reader.names_equal(syn_name, param_name))
    });
    let is_lone_param = reader.sequence_len(sp) == 1
        && matches!(reader.at(sp, 0), Some(BinderSyntaxObservation::Param(syn_name))
            if reader.names_equal(syn_name, param_name));
    if refs_param && !is_lone_param {
        Some(source_ident.to_string())
    } else {
        None
    }
}

pub fn try_recognize_cast_fold<'source, R, C>(
    reader: &'source R,
    rule: R::Rule,
    proc_cat: CastName<'source, R>,
    context: &mut C,
) -> Result<Option<CastFold<CastName<'source, R>>>, C::Error>
where
    R: BinderRuleReader<'source>,
    C: CastObservationContext<'source, R>,
{
    if !context.try_explicit_fold(rule)? {
        return Ok(None);
    }
    let Some(ps) = reader.term_context(rule) else {
        return Ok(None);
    };
    if reader.params_len(ps) == 0 || reader.params_len(ps) > 2 {
        return Ok(None);
    }
    let Some(first) = reader
        .param_at(ps, 0)
        .and_then(|param| simple_param_cat_in(reader, param))
    else {
        return Ok(None);
    };
    if !reader.names_equal(first, proc_cat) {
        return Ok(None);
    }
    let is_binary = reader.params_len(ps) == 2;
    if is_binary {
        let Some(width) = reader
            .param_at(ps, 1)
            .and_then(|param| simple_param_cat_in(reader, param))
        else {
            return Ok(None);
        };
        let Some(kind) = context.try_native_kind(width)? else {
            return Ok(None);
        };
        if !kind.is_integer() {
            return Ok(None);
        }
    }
    let (flavor, arity) = match context.try_native_kind(reader.category(rule))? {
        Some(kind) => {
            let Some(arity) = arity_of_kind(kind) else {
                return Ok(None);
            };
            (Flavor::Native, Some(arity))
        },
        None if reader.names_equal(reader.category(rule), proc_cat) && is_binary => {
            (Flavor::Object, None)
        },
        _ => return Ok(None),
    };
    Ok(Some(CastFold {
        label: reader.label(rule),
        output_cat: reader.category(rule),
        arity,
        flavor,
        is_binary,
    }))
}

pub fn try_is_wrap_candidate<'source, R, C>(
    reader: &'source R,
    rule: R::Rule,
    context: &mut C,
) -> Result<bool, C::Error>
where
    R: BinderRuleReader<'source>,
    C: CastObservationContext<'source, R>,
{
    if context.try_source_body_present(rule)? {
        return Ok(false);
    }
    let Some(ps) = reader.term_context(rule) else {
        return Ok(false);
    };
    if reader.params_len(ps) != 1 {
        return Ok(false);
    }
    let Some(inner) = reader
        .param_at(ps, 0)
        .and_then(|param| simple_param_cat_in(reader, param))
    else {
        return Ok(false);
    };
    Ok(matches!(context.try_native_kind(inner)?, Some(kind) if is_numeric_kind(kind)))
}

pub fn try_cast_machinery_participates<'source, R, C>(
    reader: &'source R,
    rule: R::Rule,
    original_rules: impl IntoIterator<Item = R::Rule>,
    context: &mut C,
) -> Result<bool, C::Error>
where
    R: BinderRuleReader<'source>,
    C: CastObservationContext<'source, R>,
{
    if let Some(source) = trigger_unary_wrapper_source_cat_in(reader, rule) {
        if matches!(context.try_trigger_native_kind(&source)?, Some(kind) if is_numeric_kind(kind))
        {
            return Ok(true);
        }
    }
    if try_is_wrap_candidate(reader, rule, context)? {
        return Ok(true);
    }
    let mut counts: HashMap<String, (CastName<'source, R>, usize)> = HashMap::new();
    for candidate in original_rules {
        if try_is_wrap_candidate(reader, candidate, context)? {
            let entry = counts
                .entry(reader.category(candidate).to_string())
                .or_insert((reader.category(candidate), 0));
            entry.1 += 1;
        }
    }
    let Some(proc_cat) = context.try_elect_object_category(&counts)? else {
        return Ok(false);
    };
    Ok(try_recognize_cast_fold(reader, rule, proc_cat, context)?.is_some())
}
