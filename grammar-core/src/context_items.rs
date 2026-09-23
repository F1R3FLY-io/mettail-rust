//! The original term-context-to-legacy-items conversion, with borrowed readers.
//!
//! `TermContextItemsProjection.v` proves finite source/accessor substitution,
//! including constructor order and the original partial binding indices.
//! `ContextItemsAdmission.v` specifies the optional same-loop admission envelope.
//! Neither model certifies arbitrary readers or physical allocator bounds.

use crate::{TermParamObservation, TermParamReader};

/// Original shallow type probes and output constructors used by this converter.
///
/// Probes preserve source constructors without coercion. Names use the original
/// identifier equality, not display spelling. Constructors retain the original
/// name, classify nonterminals through the original classifier, and set collection
/// delimiters to `None`. Handles and observations remain stable during traversal.
pub trait ContextItemsReader<'syntax>: TermParamReader<'syntax> {
    type CollectionKind: Copy;
    type Item;

    fn base_name(&self, ty: Self::Type) -> Option<Self::Name>;
    fn collection(&self, ty: Self::Type) -> Option<(Self::CollectionKind, Self::Type)>;
    fn map(&self, ty: Self::Type) -> Option<(Self::Type, Self::Type)>;
    fn arrow(&self, ty: Self::Type) -> Option<(Self::Type, Self::Type)>;
    fn multi_binder(&self, ty: Self::Type) -> Option<Self::Type>;
    fn names_equal(&self, left: Self::Name, right: Self::Name) -> bool;
    fn hash_map_kind(&self) -> Self::CollectionKind;
    fn make_nonterminal(&self, name: Self::Name) -> Self::Item;
    fn make_binder(&self, name: Self::Name) -> Self::Item;
    fn make_collection(
        &self,
        kind: Self::CollectionKind,
        element: Self::Name,
        separator: &'static str,
    ) -> Self::Item;
}

/// Admission sites in the original traversal. Item names remain borrowed
/// handles: the caller can charge their actual payload before construction.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ContextItemsEvent<N, K> {
    VisitParameter,
    EnterOptional,
    Nonterminal(N),
    Binder(N),
    Collection {
        kind: K,
        element: N,
        separator: &'static str,
    },
    Binding,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ContextItemsError<E> {
    Admission(E),
    Allocation,
}

/// Prepay and reserve before invoking the original item constructor.
fn push_item<T, N, K, E>(
    items: &mut Vec<T>,
    event: ContextItemsEvent<N, K>,
    admit: &mut impl FnMut(ContextItemsEvent<N, K>) -> Result<(), E>,
    make: impl FnOnce() -> T,
) -> Result<(), ContextItemsError<E>> {
    admit(event).map_err(ContextItemsError::Admission)?;
    items
        .try_reserve(1)
        .map_err(|_| ContextItemsError::Allocation)?;
    items.push(make());
    Ok(())
}

fn push_binding<N, K, E>(
    bindings: &mut Vec<(usize, Vec<usize>)>,
    binder: usize,
    body: usize,
    admit: &mut impl FnMut(ContextItemsEvent<N, K>) -> Result<(), E>,
) -> Result<(), ContextItemsError<E>> {
    admit(ContextItemsEvent::Binding).map_err(ContextItemsError::Admission)?;
    bindings
        .try_reserve(1)
        .map_err(|_| ContextItemsError::Allocation)?;
    let mut bodies = Vec::new();
    bodies
        .try_reserve(1)
        .map_err(|_| ContextItemsError::Allocation)?;
    bodies.push(body);
    bindings.push((binder, bodies));
    Ok(())
}

/// Execute the original outer loop and nested Optional iterator-frame loop.
///
/// Each frame contains only an original list handle and its index iterator; no
/// flattened parameter roster is allocated. As in the original implementation,
/// top-level Arrow parameters always append a binding, including partial types.
pub fn convert_term_context_to_items_with<'syntax, R: ContextItemsReader<'syntax>>(
    reader: &R,
    term_context: R::Parameters,
) -> (Vec<R::Item>, Vec<(usize, Vec<usize>)>) {
    match try_convert_term_context_to_items_with(reader, term_context, |_| {
        Ok::<_, std::convert::Infallible>(())
    }) {
        Ok(output) => output,
        Err(ContextItemsError::Admission(impossible)) => match impossible {},
        Err(ContextItemsError::Allocation) => panic!("term context output allocation failed"),
    }
}

/// Same original loops with admission before work or growth, not a preliminary
/// traversal. Every occurrence is charged, including repeated shared handles.
/// On refusal private buffers are dropped and no partial output is returned.
/// Readers must remain shallow and immutable; constructors must not perform
/// external effects. The admission callback supplies policy, not this worker.
pub fn try_convert_term_context_to_items_with<'syntax, R, E>(
    reader: &R,
    term_context: R::Parameters,
    mut admit: impl FnMut(ContextItemsEvent<R::Name, R::CollectionKind>) -> Result<(), E>,
) -> Result<(Vec<R::Item>, Vec<(usize, Vec<usize>)>), ContextItemsError<E>>
where
    R: ContextItemsReader<'syntax>,
{
    let mut items = Vec::new();
    let mut bindings = Vec::new();

    for index in 0..reader.params_len(term_context) {
        admit(ContextItemsEvent::VisitParameter).map_err(ContextItemsError::Admission)?;
        let param = reader
            .param_at(term_context, index)
            .expect("parameter index is in bounds");
        match reader.param(param) {
            TermParamObservation::Simple { ty, .. } => {
                if let Some(type_name) = reader.base_name(ty) {
                    push_item(
                        &mut items,
                        ContextItemsEvent::Nonterminal(type_name),
                        &mut admit,
                        || reader.make_nonterminal(type_name),
                    )?;
                } else if let Some((coll_type, element)) = reader.collection(ty) {
                    if let Some(elem_name) = reader.base_name(element) {
                        push_item(
                            &mut items,
                            ContextItemsEvent::Collection {
                                kind: coll_type,
                                element: elem_name,
                                separator: "|",
                            },
                            &mut admit,
                            || reader.make_collection(coll_type, elem_name, "|"),
                        )?;
                    }
                } else if let Some((key, value)) = reader.map(ty) {
                    if let (Some(k_name), Some(v_name)) =
                        (reader.base_name(key), reader.base_name(value))
                    {
                        if reader.names_equal(k_name, v_name) {
                            let kind = reader.hash_map_kind();
                            push_item(
                                &mut items,
                                ContextItemsEvent::Collection {
                                    kind,
                                    element: v_name,
                                    separator: ",",
                                },
                                &mut admit,
                                || reader.make_collection(kind, v_name, ","),
                            )?;
                        }
                    }
                }
            },
            TermParamObservation::Abstraction { ty, .. } => {
                if let Some((domain, codomain)) = reader.arrow(ty) {
                    let binder_idx = items.len();
                    if let Some(binder_type) = reader.base_name(domain) {
                        push_item(
                            &mut items,
                            ContextItemsEvent::Binder(binder_type),
                            &mut admit,
                            || reader.make_binder(binder_type),
                        )?;
                    }
                    let body_idx = items.len();
                    if let Some(body_type) = reader.base_name(codomain) {
                        push_item(
                            &mut items,
                            ContextItemsEvent::Nonterminal(body_type),
                            &mut admit,
                            || reader.make_nonterminal(body_type),
                        )?;
                    }
                    push_binding(&mut bindings, binder_idx, body_idx, &mut admit)?;
                }
            },
            TermParamObservation::MultiAbstraction { ty, .. } => {
                if let Some((domain, codomain)) = reader.arrow(ty) {
                    let binder_idx = items.len();
                    if let Some(inner) = reader.multi_binder(domain) {
                        if let Some(binder_type) = reader.base_name(inner) {
                            push_item(
                                &mut items,
                                ContextItemsEvent::Binder(binder_type),
                                &mut admit,
                                || reader.make_binder(binder_type),
                            )?;
                        }
                    }
                    let body_idx = items.len();
                    if let Some(body_type) = reader.base_name(codomain) {
                        push_item(
                            &mut items,
                            ContextItemsEvent::Nonterminal(body_type),
                            &mut admit,
                            || reader.make_nonterminal(body_type),
                        )?;
                    }
                    push_binding(&mut bindings, binder_idx, body_idx, &mut admit)?;
                }
            },
            TermParamObservation::GuardBody { .. } => {},
            TermParamObservation::Optional { params: inner } => {
                fn flatten_optional_items<'syntax, R: ContextItemsReader<'syntax>, E>(
                    reader: &R,
                    inner: R::Parameters,
                    items: &mut Vec<R::Item>,
                    admit: &mut impl FnMut(
                        ContextItemsEvent<R::Name, R::CollectionKind>,
                    ) -> Result<(), E>,
                ) -> Result<(), ContextItemsError<E>> {
                    admit(ContextItemsEvent::EnterOptional)
                        .map_err(ContextItemsError::Admission)?;
                    let mut frames = Vec::new();
                    frames
                        .try_reserve(1)
                        .map_err(|_| ContextItemsError::Allocation)?;
                    frames.push((inner, 0..reader.params_len(inner)));
                    while let Some((params, frame)) = frames.last_mut() {
                        let Some(index) = frame.next() else {
                            frames.pop();
                            continue;
                        };
                        admit(ContextItemsEvent::VisitParameter)
                            .map_err(ContextItemsError::Admission)?;
                        let p = reader
                            .param_at(*params, index)
                            .expect("parameter index is in bounds");
                        match reader.param(p) {
                            TermParamObservation::Simple { ty, .. } => {
                                if let Some(type_name) = reader.base_name(ty) {
                                    push_item(
                                        items,
                                        ContextItemsEvent::Nonterminal(type_name),
                                        admit,
                                        || reader.make_nonterminal(type_name),
                                    )?;
                                } else if let Some((coll_type, element)) = reader.collection(ty) {
                                    if let Some(elem_name) = reader.base_name(element) {
                                        push_item(
                                            items,
                                            ContextItemsEvent::Collection {
                                                kind: coll_type,
                                                element: elem_name,
                                                separator: "|",
                                            },
                                            admit,
                                            || reader.make_collection(coll_type, elem_name, "|"),
                                        )?;
                                    }
                                } else if let Some((key, value)) = reader.map(ty) {
                                    if let (Some(k_name), Some(v_name)) =
                                        (reader.base_name(key), reader.base_name(value))
                                    {
                                        if reader.names_equal(k_name, v_name) {
                                            let kind = reader.hash_map_kind();
                                            push_item(
                                                items,
                                                ContextItemsEvent::Collection {
                                                    kind,
                                                    element: v_name,
                                                    separator: ",",
                                                },
                                                admit,
                                                || reader.make_collection(kind, v_name, ","),
                                            )?;
                                        }
                                    }
                                }
                            },
                            TermParamObservation::Abstraction { ty, .. }
                            | TermParamObservation::MultiAbstraction { ty, .. } => {
                                if let Some((_, codomain)) = reader.arrow(ty) {
                                    if let Some(body_type) = reader.base_name(codomain) {
                                        push_item(
                                            items,
                                            ContextItemsEvent::Nonterminal(body_type),
                                            admit,
                                            || reader.make_nonterminal(body_type),
                                        )?;
                                    }
                                }
                            },
                            TermParamObservation::GuardBody { .. } => {},
                            TermParamObservation::Optional { params: nested } => {
                                admit(ContextItemsEvent::EnterOptional)
                                    .map_err(ContextItemsError::Admission)?;
                                frames
                                    .try_reserve(1)
                                    .map_err(|_| ContextItemsError::Allocation)?;
                                frames.push((nested, 0..reader.params_len(nested)));
                            },
                        }
                    }
                    Ok(())
                }
                flatten_optional_items(reader, inner, &mut items, &mut admit)?;
            },
        }
    }
    Ok((items, bindings))
}
