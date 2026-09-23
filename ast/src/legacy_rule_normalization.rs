//! The original legacy-BNF normalization loop with borrowed observations.
//!
//! This is the implementation used by `grammar::convert_items_to_term_context`,
//! not an additional normalizer. Adapters supply original items and constructors;
//! the loop retains the original preflight, order, names and refusal behavior.
//! `LegacyRuleNormalizationProjection.v` proves constructor substitution and
//! refusal/commit correspondence. `LegacyNormalizationAdmission.v` covers the
//! same-loop admission envelope, not arbitrary adapter allocations or effects.

use crate::grammar::NonTerminalKind;

/// A shallow view of an original BNF item; no source reconstruction is needed.
pub enum LegacyItemView<'input, N, K> {
    Terminal(&'input String),
    NonTerminal {
        ident: &'input N,
        kind: NonTerminalKind,
    },
    Binder {
        category: &'input N,
    },
    Collection {
        kind: &'input K,
        element: &'input N,
        separator: &'input String,
        delimiters: Option<(&'input String, &'input String)>,
    },
}

/// Supplies stable, borrowed input and the original output constructors.
///
/// Readers must observe the same immutable input throughout both scans.
/// Constructors must be total on admitted inputs and must not publish partial
/// output: a later refusal discards the locally constructed prefix. An arena
/// adapter must therefore stage constructor effects privately until success.
/// Original names and generated names may use different owned representations.
pub trait LegacyRuleNormalizationAdapter<'input> {
    type OriginalName: Clone + 'input;
    type GeneratedName: Clone;
    type CollectionKind: Clone + 'input;
    type Param;
    type Syntax;

    fn has_term_context(&self) -> bool;
    fn has_syntax_pattern(&self) -> bool;
    fn items_len(&self) -> usize;
    fn item(
        &self,
        index: usize,
    ) -> LegacyItemView<'input, Self::OriginalName, Self::CollectionKind>;

    fn fresh_name(&mut self, index: usize) -> Self::GeneratedName;
    fn elems_name(&mut self) -> Self::GeneratedName;
    fn make_simple(
        &mut self,
        name: Self::GeneratedName,
        category: Self::OriginalName,
    ) -> Self::Param;
    fn make_abstraction(
        &mut self,
        binder: Self::GeneratedName,
        body: Self::GeneratedName,
        domain: Self::OriginalName,
        codomain: Self::OriginalName,
    ) -> Self::Param;
    fn make_collection(
        &mut self,
        name: Self::GeneratedName,
        kind: Self::CollectionKind,
        element: Self::OriginalName,
    ) -> Self::Param;
    fn make_literal(&mut self, text: String) -> Self::Syntax;
    fn make_param(&mut self, name: Self::GeneratedName) -> Self::Syntax;
    fn make_sep(&mut self, name: Self::GeneratedName, separator: String) -> Self::Syntax;
}

/// Admission at original observation, clone and constructor sites.
/// Payloads are borrowed so a policy can prepay their actual shallow costs.
#[derive(Debug)]
pub enum LegacyNormalizationEvent<'a, N, G, K> {
    PreflightItem(usize),
    BuildItem(usize),
    FreshName(usize),
    ElemsName,
    PendingBinder(&'a N),
    Simple {
        name: &'a G,
        category: &'a N,
    },
    Abstraction {
        binder: &'a G,
        body: &'a G,
        domain: &'a N,
        codomain: &'a N,
    },
    Collection {
        name: &'a G,
        kind: &'a K,
        element: &'a N,
    },
    Literal(&'a str),
    Param(&'a G),
    Sep {
        name: &'a G,
        separator: &'a str,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LegacyNormalizationError<E> {
    Admission(E),
    Allocation,
    CounterOverflow,
}

fn reserve_output<T, E>(output: &mut Vec<T>) -> Result<(), LegacyNormalizationError<E>> {
    output
        .try_reserve(1)
        .map_err(|_| LegacyNormalizationError::Allocation)
}

fn checked_next_parameter<E>(index: usize) -> Result<usize, LegacyNormalizationError<E>> {
    index
        .checked_add(1)
        .ok_or(LegacyNormalizationError::CounterOverflow)
}

/// Relocated original two-scan algorithm. Only successful output may be committed.
///
/// `None` preserves the entire original rule. `Some` replaces only its term
/// context and syntax pattern, in that order. This iterative loop does not walk
/// nested syntax or types. The original static entrypoint admits every event;
/// runtime callers use the fallible entrypoint with an explicit finite policy.
pub fn normalize_legacy_rule_with<'input, A>(
    adapter: &mut A,
) -> Option<(Vec<A::Param>, Vec<A::Syntax>)>
where
    A: LegacyRuleNormalizationAdapter<'input>,
{
    match try_normalize_legacy_rule_with(adapter, |_| Ok::<_, std::convert::Infallible>(())) {
        Ok(output) => output,
        Err(LegacyNormalizationError::Admission(impossible)) => match impossible {},
        Err(LegacyNormalizationError::Allocation) => {
            panic!("legacy normalization output allocation failed")
        },
        Err(LegacyNormalizationError::CounterOverflow) => {
            panic!("legacy normalization parameter counter overflow")
        },
    }
}

/// Run the same two scans with admission before reads, argument copies and
/// output reservation. `Ok(None)` is the original semantic refusal; `Err` is a
/// resource refusal. Neither publishes a partial context/syntax pair.
///
/// Constructors must remain total and private on admitted inputs. Policies must
/// cover adapter-specific cloning and construction, not merely output slots.
/// The worker allocates no event trace and performs no additional input scan.
pub fn try_normalize_legacy_rule_with<'input, A, E>(
    adapter: &mut A,
    mut admit: impl FnMut(
        LegacyNormalizationEvent<'_, A::OriginalName, A::GeneratedName, A::CollectionKind>,
    ) -> Result<(), E>,
) -> Result<Option<(Vec<A::Param>, Vec<A::Syntax>)>, LegacyNormalizationError<E>>
where
    A: LegacyRuleNormalizationAdapter<'input>,
{
    use LegacyNormalizationEvent as Event;
    if adapter.has_term_context() || adapter.has_syntax_pattern() {
        return Ok(None);
    }

    // Original complete preflight, before constructing any output.
    for index in 0..adapter.items_len() {
        admit(Event::PreflightItem(index)).map_err(LegacyNormalizationError::Admission)?;
        if let LegacyItemView::NonTerminal { kind, .. } = adapter.item(index) {
            if kind != NonTerminalKind::Category {
                return Ok(None);
            }
        }
    }

    let mut tc: Vec<A::Param> = Vec::new();
    let mut sp: Vec<A::Syntax> = Vec::new();
    let mut next_param_id: usize = 0;
    let mut pending_binder: Option<A::OriginalName> = None;

    for index in 0..adapter.items_len() {
        admit(Event::BuildItem(index)).map_err(LegacyNormalizationError::Admission)?;
        match adapter.item(index) {
            LegacyItemView::Terminal(text) => {
                admit(Event::Literal(text)).map_err(LegacyNormalizationError::Admission)?;
                reserve_output(&mut sp)?;
                sp.push(adapter.make_literal(text.clone()));
            },
            LegacyItemView::NonTerminal { ident, kind: NonTerminalKind::Category } => {
                admit(Event::FreshName(next_param_id))
                    .map_err(LegacyNormalizationError::Admission)?;
                let next = checked_next_parameter(next_param_id)?;
                let pname = adapter.fresh_name(next_param_id);
                next_param_id = next;

                if let Some(binder_cat) = pending_binder.take() {
                    admit(Event::FreshName(next_param_id))
                        .map_err(LegacyNormalizationError::Admission)?;
                    let next = checked_next_parameter(next_param_id)?;
                    let body_pname = adapter.fresh_name(next_param_id);
                    next_param_id = next;
                    admit(Event::Abstraction {
                        binder: &pname,
                        body: &body_pname,
                        domain: &binder_cat,
                        codomain: ident,
                    })
                    .map_err(LegacyNormalizationError::Admission)?;
                    reserve_output(&mut tc)?;
                    tc.push(adapter.make_abstraction(
                        pname.clone(),
                        body_pname.clone(),
                        binder_cat,
                        ident.clone(),
                    ));
                    admit(Event::Param(&pname)).map_err(LegacyNormalizationError::Admission)?;
                    reserve_output(&mut sp)?;
                    sp.push(adapter.make_param(pname));
                    admit(Event::Param(&body_pname))
                        .map_err(LegacyNormalizationError::Admission)?;
                    reserve_output(&mut sp)?;
                    sp.push(adapter.make_param(body_pname));
                } else {
                    admit(Event::Simple { name: &pname, category: ident })
                        .map_err(LegacyNormalizationError::Admission)?;
                    reserve_output(&mut tc)?;
                    tc.push(adapter.make_simple(pname.clone(), ident.clone()));
                    admit(Event::Param(&pname)).map_err(LegacyNormalizationError::Admission)?;
                    reserve_output(&mut sp)?;
                    sp.push(adapter.make_param(pname));
                }
            },
            // Preserve the original defensive refusal even after preflight.
            LegacyItemView::NonTerminal { .. } => return Ok(None),
            LegacyItemView::Binder { category } => {
                admit(Event::PendingBinder(category))
                    .map_err(LegacyNormalizationError::Admission)?;
                pending_binder = Some(category.clone());
            },
            LegacyItemView::Collection { kind, element, separator, delimiters } => {
                if let Some((open, close)) = delimiters {
                    admit(Event::ElemsName).map_err(LegacyNormalizationError::Admission)?;
                    let elems_name = adapter.elems_name();
                    admit(Event::Collection { name: &elems_name, kind, element })
                        .map_err(LegacyNormalizationError::Admission)?;
                    reserve_output(&mut tc)?;
                    tc.push(adapter.make_collection(
                        elems_name.clone(),
                        kind.clone(),
                        element.clone(),
                    ));
                    admit(Event::Literal(open)).map_err(LegacyNormalizationError::Admission)?;
                    reserve_output(&mut sp)?;
                    sp.push(adapter.make_literal(open.clone()));
                    admit(Event::Sep { name: &elems_name, separator })
                        .map_err(LegacyNormalizationError::Admission)?;
                    reserve_output(&mut sp)?;
                    sp.push(adapter.make_sep(elems_name, separator.clone()));
                    admit(Event::Literal(close)).map_err(LegacyNormalizationError::Admission)?;
                    reserve_output(&mut sp)?;
                    sp.push(adapter.make_literal(close.clone()));
                } else {
                    return Ok(None);
                }
            },
        }
    }

    if pending_binder.is_some() {
        return Ok(None);
    }
    if tc.is_empty() {
        return Ok(None);
    }

    Ok(Some((tc, sp)))
}

#[cfg(test)]
mod admission_tests {
    use super::*;

    #[test]
    fn checked_parameter_increment_preserves_full_usize_domain() {
        assert_eq!(checked_next_parameter::<()>(0), Ok(1));
        assert_eq!(checked_next_parameter::<()>(usize::MAX - 1), Ok(usize::MAX));
        assert_eq!(
            checked_next_parameter::<()>(usize::MAX),
            Err(LegacyNormalizationError::CounterOverflow)
        );
    }
}
