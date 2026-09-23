//! The original term-context-to-legacy-items conversion, with borrowed readers.
//!
//! `TermContextItemsProjection.v` proves finite source/accessor substitution,
//! including constructor order and the original partial binding indices.
//! This does not certify arbitrary cyclic readers or runtime resource admission.

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

/// Execute the original outer loop and nested Optional iterator-frame loop.
///
/// Each frame contains only an original list handle and its index iterator; no
/// flattened parameter roster is allocated. As in the original implementation,
/// top-level Arrow parameters always append a binding, including partial types.
pub fn convert_term_context_to_items_with<'syntax, R: ContextItemsReader<'syntax>>(
    reader: &R,
    term_context: R::Parameters,
) -> (Vec<R::Item>, Vec<(usize, Vec<usize>)>) {
    let mut items = Vec::new();
    let mut bindings = Vec::new();

    for index in 0..reader.params_len(term_context) {
        let param = reader
            .param_at(term_context, index)
            .expect("parameter index is in bounds");
        match reader.param(param) {
            TermParamObservation::Simple { ty, .. } => {
                if let Some(type_name) = reader.base_name(ty) {
                    items.push(reader.make_nonterminal(type_name));
                } else if let Some((coll_type, element)) = reader.collection(ty) {
                    if let Some(elem_name) = reader.base_name(element) {
                        items.push(reader.make_collection(coll_type, elem_name, "|"));
                    }
                } else if let Some((key, value)) = reader.map(ty) {
                    if let (Some(k_name), Some(v_name)) =
                        (reader.base_name(key), reader.base_name(value))
                    {
                        if reader.names_equal(k_name, v_name) {
                            items.push(reader.make_collection(reader.hash_map_kind(), v_name, ","));
                        }
                    }
                }
            },
            TermParamObservation::Abstraction { ty, .. } => {
                if let Some((domain, codomain)) = reader.arrow(ty) {
                    let binder_idx = items.len();
                    if let Some(binder_type) = reader.base_name(domain) {
                        items.push(reader.make_binder(binder_type));
                    }
                    let body_idx = items.len();
                    if let Some(body_type) = reader.base_name(codomain) {
                        items.push(reader.make_nonterminal(body_type));
                    }
                    bindings.push((binder_idx, vec![body_idx]));
                }
            },
            TermParamObservation::MultiAbstraction { ty, .. } => {
                if let Some((domain, codomain)) = reader.arrow(ty) {
                    let binder_idx = items.len();
                    if let Some(inner) = reader.multi_binder(domain) {
                        if let Some(binder_type) = reader.base_name(inner) {
                            items.push(reader.make_binder(binder_type));
                        }
                    }
                    let body_idx = items.len();
                    if let Some(body_type) = reader.base_name(codomain) {
                        items.push(reader.make_nonterminal(body_type));
                    }
                    bindings.push((binder_idx, vec![body_idx]));
                }
            },
            TermParamObservation::GuardBody { .. } => {},
            TermParamObservation::Optional { params: inner } => {
                fn flatten_optional_items<'syntax, R: ContextItemsReader<'syntax>>(
                    reader: &R,
                    inner: R::Parameters,
                    items: &mut Vec<R::Item>,
                ) {
                    let mut frames = vec![(inner, 0..reader.params_len(inner))];
                    while let Some((params, frame)) = frames.last_mut() {
                        let Some(index) = frame.next() else {
                            frames.pop();
                            continue;
                        };
                        let p = reader
                            .param_at(*params, index)
                            .expect("parameter index is in bounds");
                        match reader.param(p) {
                            TermParamObservation::Simple { ty, .. } => {
                                if let Some(type_name) = reader.base_name(ty) {
                                    items.push(reader.make_nonterminal(type_name));
                                } else if let Some((coll_type, element)) = reader.collection(ty) {
                                    if let Some(elem_name) = reader.base_name(element) {
                                        items.push(
                                            reader.make_collection(coll_type, elem_name, "|"),
                                        );
                                    }
                                } else if let Some((key, value)) = reader.map(ty) {
                                    if let (Some(k_name), Some(v_name)) =
                                        (reader.base_name(key), reader.base_name(value))
                                    {
                                        if reader.names_equal(k_name, v_name) {
                                            items.push(reader.make_collection(
                                                reader.hash_map_kind(),
                                                v_name,
                                                ",",
                                            ));
                                        }
                                    }
                                }
                            },
                            TermParamObservation::Abstraction { ty, .. }
                            | TermParamObservation::MultiAbstraction { ty, .. } => {
                                if let Some((_, codomain)) = reader.arrow(ty) {
                                    if let Some(body_type) = reader.base_name(codomain) {
                                        items.push(reader.make_nonterminal(body_type));
                                    }
                                }
                            },
                            TermParamObservation::GuardBody { .. } => {},
                            TermParamObservation::Optional { params: nested } => {
                                frames.push((nested, 0..reader.params_len(nested)));
                            },
                        }
                    }
                }
                flatten_optional_items(reader, inner, &mut items);
            },
        }
    }
    (items, bindings)
}
