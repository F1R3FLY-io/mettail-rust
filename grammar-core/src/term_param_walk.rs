//! Original declaration-preorder worklist and shared binder-presence predicates.
//!
//! Optional groups reverse-push their children onto one explicit stack. Leaves
//! retain source handles and inherited optional flags; no AST is reconstructed.
//! The fallible predicates own the worklist, so refusal cannot publish a partial
//! answer or expose an iterator that can resume after an error.
//!
//! Admission runs inline before each named read, reservation, push and pop.
//! A runtime policy must bound every visited occurrence, including repeated DAG
//! handles; these callbacks are logical work/storage admission, not an allocator
//! or physical-RSS guarantee. The source reader must satisfy its immutable,
//! validated-handle contract. Static wrappers use infallible admission.
//!
//! `TermParamReaderProjection.v` models the original worker. The checked
//! `BinderPresenceProjection.v` composes its finite traces with the original
//! recursive binder equations, rule/item order and first-failure publication.

use crate::{TermParamObservation, TermParamReader};
use std::convert::Infallible;

/// A non-grouping term parameter, with the variant-specific fields exposed by type.
#[derive(Clone, Copy)]
pub enum TermParamLeafKind<P, N, T> {
    Simple { param: P, name: N, ty: T },
    GuardBody { param: P, name: N },
    Abstraction { param: P, binder: N, body: N, ty: T },
    MultiAbstraction { param: P, binder: N, body: N, ty: T },
}

impl<P, N, T> TermParamLeafKind<P, N, T> {
    /// Return the original authored parameter handle, not a reconstructed node.
    pub fn param(self) -> P {
        match self {
            Self::Simple { param, .. }
            | Self::GuardBody { param, .. }
            | Self::Abstraction { param, .. }
            | Self::MultiAbstraction { param, .. } => param,
        }
    }
}

/// One non-grouping term parameter encountered in declaration preorder.
#[derive(Clone, Copy)]
pub struct TermParamLeaf<P, N, T> {
    pub kind: TermParamLeafKind<P, N, T>,
    /// True once the path to this leaf has entered an `Optional` group.
    pub is_optional: bool,
}

/// An actual observation or worklist operation, not an allocated event plan.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TermParamWalkEvent<P, S> {
    ReadLength(S),
    ReserveFrames(usize),
    ReadIndex { params: S, index: usize },
    PushFrame { param: P, optional: bool },
    PopFrame(P),
    ObserveFirst(P),
    ObserveSecond(P),
}

/// No partial predicate answer is returned on any of these failures.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BinderPresenceError<E> {
    Admission(E),
    Allocation,
    InvalidParameterIndex { index: usize },
}

/// Stack-safe declaration-order traversal over the leaves of nested parameters.
/// Optional groups do not yield items themselves.
pub struct TermParamLeaves<'syntax, R: TermParamReader<'syntax>> {
    reader: &'syntax R,
    work: Vec<(R::Param, bool)>,
}

impl<'syntax, R: TermParamReader<'syntax>> TermParamLeaves<'syntax, R> {
    pub fn new(reader: &'syntax R, params: R::Parameters, is_optional: bool) -> Self {
        infallible(Self::try_new(reader, params, is_optional, &mut |_| Ok::<_, Infallible>(())))
    }

    fn try_new<E>(
        reader: &'syntax R,
        params: R::Parameters,
        is_optional: bool,
        admit: &mut impl FnMut(TermParamWalkEvent<R::Param, R::Parameters>) -> Result<(), E>,
    ) -> Result<Self, BinderPresenceError<E>> {
        let mut leaves = Self { reader, work: Vec::new() };
        leaves.push_params(params, is_optional, admit)?;
        Ok(leaves)
    }

    fn push_params<E>(
        &mut self,
        params: R::Parameters,
        optional: bool,
        admit: &mut impl FnMut(TermParamWalkEvent<R::Param, R::Parameters>) -> Result<(), E>,
    ) -> Result<(), BinderPresenceError<E>> {
        admit(TermParamWalkEvent::ReadLength(params)).map_err(BinderPresenceError::Admission)?;
        let count = self.reader.params_len(params);
        admit(TermParamWalkEvent::ReserveFrames(count)).map_err(BinderPresenceError::Admission)?;
        self.work
            .try_reserve(count)
            .map_err(|_| BinderPresenceError::Allocation)?;
        for index in (0..count).rev() {
            admit(TermParamWalkEvent::ReadIndex { params, index })
                .map_err(BinderPresenceError::Admission)?;
            let param = self
                .reader
                .param_at(params, index)
                .ok_or(BinderPresenceError::InvalidParameterIndex { index })?;
            admit(TermParamWalkEvent::PushFrame { param, optional })
                .map_err(BinderPresenceError::Admission)?;
            self.work.push((param, optional));
        }
        Ok(())
    }

    fn try_next<E>(
        &mut self,
        admit: &mut impl FnMut(TermParamWalkEvent<R::Param, R::Parameters>) -> Result<(), E>,
    ) -> Result<Option<TermParamLeaf<R::Param, R::Name, R::Type>>, BinderPresenceError<E>> {
        while let Some(&(param, is_optional)) = self.work.last() {
            admit(TermParamWalkEvent::PopFrame(param)).map_err(BinderPresenceError::Admission)?;
            self.work.pop();
            admit(TermParamWalkEvent::ObserveFirst(param))
                .map_err(BinderPresenceError::Admission)?;
            if let TermParamObservation::Optional { params } = self.reader.param(param) {
                self.push_params(params, true, admit)?;
                continue;
            }
            admit(TermParamWalkEvent::ObserveSecond(param))
                .map_err(BinderPresenceError::Admission)?;
            let kind = match self.reader.param(param) {
                TermParamObservation::Simple { name, ty } => {
                    TermParamLeafKind::Simple { param, name, ty }
                },
                TermParamObservation::GuardBody { name } => {
                    TermParamLeafKind::GuardBody { param, name }
                },
                TermParamObservation::Abstraction { binder, body, ty } => {
                    TermParamLeafKind::Abstraction { param, binder, body, ty }
                },
                TermParamObservation::MultiAbstraction { binder, body, ty } => {
                    TermParamLeafKind::MultiAbstraction { param, binder, body, ty }
                },
                TermParamObservation::Optional { .. } => continue,
            };
            return Ok(Some(TermParamLeaf { kind, is_optional }));
        }
        Ok(None)
    }
}

impl<'syntax, R: TermParamReader<'syntax>> Iterator for TermParamLeaves<'syntax, R> {
    type Item = TermParamLeaf<R::Param, R::Name, R::Type>;

    fn next(&mut self) -> Option<Self::Item> {
        infallible(self.try_next(&mut |_| Ok::<_, Infallible>(())))
    }
}

fn infallible<T>(result: Result<T, BinderPresenceError<Infallible>>) -> T {
    match result {
        Ok(value) => value,
        Err(BinderPresenceError::Admission(never)) => match never {},
        Err(BinderPresenceError::Allocation) => panic!("parameter worklist allocation failed"),
        Err(BinderPresenceError::InvalidParameterIndex { .. }) => {
            panic!("parameter index is in bounds")
        },
    }
}

/// Original rule-context and legacy-item observations, over the same reader.
/// Each item slice and parameter handle must belong to this immutable reader.
pub trait BinderPresenceReader<'syntax>: TermParamReader<'syntax> {
    type Rule: Copy;
    type Item: 'syntax;

    fn context(&self, rule: Self::Rule) -> Option<Self::Parameters>;
    fn items(&self, rule: Self::Rule) -> &'syntax [Self::Item];
    fn item_is_binder(&self, item: &Self::Item) -> bool;
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BinderPresenceEvent<R, P, S> {
    Parameter(TermParamWalkEvent<P, S>),
    ReadContext(R),
    ReadItems(R),
    ReadItem { rule: R, index: usize },
}

pub type BinderPresenceEventFor<'syntax, R> = BinderPresenceEvent<
    <R as BinderPresenceReader<'syntax>>::Rule,
    <R as TermParamReader<'syntax>>::Param,
    <R as TermParamReader<'syntax>>::Parameters,
>;

/// Scan nested parameters through the original worklist, stopping at its first
/// abstraction leaf. The owned local iterator is destroyed on every error.
pub fn try_params_declares_binder<'syntax, R: TermParamReader<'syntax>, E>(
    reader: &'syntax R,
    params: R::Parameters,
    mut admit: impl FnMut(TermParamWalkEvent<R::Param, R::Parameters>) -> Result<(), E>,
) -> Result<bool, BinderPresenceError<E>> {
    let mut leaves = TermParamLeaves::try_new(reader, params, false, &mut admit)?;
    while let Some(leaf) = leaves.try_next(&mut admit)? {
        if matches!(
            leaf.kind,
            TermParamLeafKind::Abstraction { .. } | TermParamLeafKind::MultiAbstraction { .. }
        ) {
            return Ok(true);
        }
    }
    Ok(false)
}

/// Observe context and legacy items in that order, even when the context binds.
/// A failure in either observation returns no boolean.
pub fn try_rule_declares_binder<'syntax, R: BinderPresenceReader<'syntax>, E>(
    reader: &'syntax R,
    rule: R::Rule,
    mut admit: impl FnMut(BinderPresenceEventFor<'syntax, R>) -> Result<(), E>,
) -> Result<bool, BinderPresenceError<E>> {
    admit(BinderPresenceEvent::ReadContext(rule)).map_err(BinderPresenceError::Admission)?;
    let binds_in_context = match reader.context(rule) {
        Some(params) => try_params_declares_binder(reader, params, |event| {
            admit(BinderPresenceEvent::Parameter(event))
        })?,
        None => false,
    };
    admit(BinderPresenceEvent::ReadItems(rule)).map_err(BinderPresenceError::Admission)?;
    let items = reader.items(rule);
    let mut binds_in_items = false;
    for (index, item) in items.iter().enumerate() {
        admit(BinderPresenceEvent::ReadItem { rule, index })
            .map_err(BinderPresenceError::Admission)?;
        if reader.item_is_binder(item) {
            binds_in_items = true;
            break;
        }
    }
    Ok(binds_in_context || binds_in_items)
}

/// Evaluate rules in source occurrence order until the first true rule or error.
pub fn try_declares_binder<'syntax, R: BinderPresenceReader<'syntax>, E>(
    reader: &'syntax R,
    rules: impl IntoIterator<Item = R::Rule>,
    mut admit: impl FnMut(BinderPresenceEventFor<'syntax, R>) -> Result<(), E>,
) -> Result<bool, BinderPresenceError<E>> {
    for rule in rules {
        if try_rule_declares_binder(reader, rule, &mut admit)? {
            return Ok(true);
        }
    }
    Ok(false)
}

pub fn params_declares_binder<'syntax, R: TermParamReader<'syntax>>(
    reader: &'syntax R,
    params: R::Parameters,
) -> bool {
    infallible(try_params_declares_binder(reader, params, |_| Ok::<_, Infallible>(())))
}

pub fn rule_declares_binder<'syntax, R: BinderPresenceReader<'syntax>>(
    reader: &'syntax R,
    rule: R::Rule,
) -> bool {
    infallible(try_rule_declares_binder(reader, rule, |_| Ok::<_, Infallible>(())))
}

pub fn declares_binder<'syntax, R: BinderPresenceReader<'syntax>>(
    reader: &'syntax R,
    rules: impl IntoIterator<Item = R::Rule>,
) -> bool {
    infallible(try_declares_binder(reader, rules, |_| Ok::<_, Infallible>(())))
}

#[cfg(test)]
#[path = "../tests/support/term_param_walk.rs"]
mod tests;
