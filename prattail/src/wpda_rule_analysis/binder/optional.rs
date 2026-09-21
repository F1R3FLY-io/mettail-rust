//! Original optional binder classifier over shallow borrowed syntax observations.
//!
//! The frame loop is shared without rebuilding syntax or deriving another
//! automaton. Macro syntax uses borrowed AST handles; an owned-image adapter
//! supplies validated immutable handles. Helpers run only at their original
//! field sites, including on paths that later refuse classification.

use super::{ActionArgKind, BinderPosition, CollectionSepInfo, ParamKind};
use mettail_ast::grammar::DelimitedRegionKind;
use mettail_ast::types::CollectionType;
use std::collections::HashMap;

/// One syntax node, preserving borrowed payloads and opaque operation identity.
pub enum BinderSyntaxObservation<'syntax, N, O> {
    Literal(&'syntax str),
    Param(N),
    TokenKind {
        name: N,
        bind: Option<N>,
    },
    GuestBody {
        open: N,
        close: N,
        bind: N,
        kind: DelimitedRegionKind,
    },
    Op(O),
}

/// Only operations understood by the original optional-body classifier.
/// Other operations retain their handles and are rejected without traversal.
pub enum OptionalOperationObservation<'syntax, N, S, O> {
    Opt {
        inner: S,
    },
    Sep {
        collection: N,
        separator: &'syntax str,
        source: Option<O>,
    },
    Other(O),
}

/// Read immutable syntax one node at a time, without eager recursive projection.
///
/// Every sequence and operation handle must belong to the reader. For a sequence,
/// `at` returns a node exactly when its index is below `sequence_len`; observations
/// and lengths remain unchanged throughout classification. Name conversion must
/// yield its exact, stable authored spelling. The macro adapter satisfies these
/// laws with slice indexing and borrowed identifiers; image adapters must validate
/// their handles before entering this classifier.
///
/// These laws and the original frame-loop correspondence are modeled in
/// `BinderOptionalProjection.v`. They do not certify arbitrary reader or helper
/// implementations, allocation failure, or unwinding.
pub trait BinderSyntaxReader<'syntax> {
    type Sequence: Copy;
    type Name: Copy + ToString;
    type Operation: Copy;

    fn sequence_len(&self, sequence: Self::Sequence) -> usize;
    fn at(
        &self,
        sequence: Self::Sequence,
        index: usize,
    ) -> Option<BinderSyntaxObservation<'syntax, Self::Name, Self::Operation>>;
    fn operation(
        &self,
        operation: Self::Operation,
    ) -> OptionalOperationObservation<'syntax, Self::Name, Self::Sequence, Self::Operation>;
}

/// Retain the original first-position dispatch summary without traversing children.
pub fn optional_first_token_set(positions: &[BinderPosition]) -> Vec<String> {
    let Some(first) = positions.first() else {
        return Vec::new();
    };
    match first {
        BinderPosition::Literal(text) => vec![text.clone()],
        BinderPosition::OptionalGroup { first_token_set, .. } => first_token_set.clone(),
        _ => Vec::new(),
    }
}

/// Compile a syntax-pattern optional body into recursive binder/action models
/// without recursing on the native stack.
///
/// Each `Frame` is one suspended sequence. Completing a child optional appends
/// its two model nodes to the parent and resumes the parent's next item. This is
/// the construction-time PDA paired with the runtime optional-group PDA.
pub fn classify_optional_body<'syntax, R: BinderSyntaxReader<'syntax>>(
    reader: &R,
    root: R::Sequence,
    param_map: &HashMap<String, ParamKind>,
    next_group_idx: &mut u32,
    collection_slots_so_far: &mut u8,
    mut guest_nested_open_kinds: impl FnMut(&str) -> Vec<String>,
    mut kv_sep_for: impl FnMut(&CollectionType) -> Option<String>,
) -> Option<(Vec<BinderPosition>, Vec<ActionArgKind>)> {
    struct Frame<S> {
        items: S,
        next: usize,
        positions: Vec<BinderPosition>,
        args: Vec<ActionArgKind>,
        group_idx: Option<u32>,
    }

    let mut frames = vec![Frame {
        items: root,
        next: 0,
        positions: Vec::new(),
        args: Vec::new(),
        group_idx: None,
    }];

    loop {
        let finished = frames
            .last()
            .is_some_and(|frame| frame.next == reader.sequence_len(frame.items));
        if finished {
            let completed = frames.pop()?;
            if let Some(parent) = frames.last_mut() {
                let group_idx = completed.group_idx?;
                if completed.positions.is_empty() {
                    return None;
                }
                let first_token_set = optional_first_token_set(&completed.positions);
                parent.positions.push(BinderPosition::OptionalGroup {
                    positions: completed.positions,
                    group_idx,
                    first_token_set,
                });
                parent.args.push(ActionArgKind::Optional(completed.args));
                continue;
            }
            return Some((completed.positions, completed.args));
        }

        let frame = frames.last_mut()?;
        let item_idx = frame.next;
        frame.next += 1;
        match reader
            .at(frame.items, item_idx)
            .expect("optional frame cursor is in bounds")
        {
            BinderSyntaxObservation::Literal(text) => {
                frame
                    .positions
                    .push(BinderPosition::Literal(text.to_owned()));
            },
            BinderSyntaxObservation::TokenKind { name, bind } => {
                let kind_name = name.to_string();
                let param_name = bind
                    .map(|name| name.to_string())
                    .unwrap_or_else(|| format!("__tok_{kind_name}"));
                frame.positions.push(BinderPosition::TokenKindCapture {
                    kind_name,
                    param_name: param_name.clone(),
                });
                frame.args.push(ActionArgKind::TokenText { param_name });
            },
            BinderSyntaxObservation::GuestBody { open, close, bind, kind } => {
                let param_name = bind.to_string();
                frame.positions.push(BinderPosition::GuestBodyCapture {
                    open_kind: open.to_string(),
                    nested_open_kinds: guest_nested_open_kinds(&open.to_string()),
                    close_kind: close.to_string(),
                    param_name: param_name.clone(),
                });
                frame
                    .args
                    .push(ActionArgKind::GuestBody { param_name, kind });
            },
            BinderSyntaxObservation::Param(name) => {
                let param_name = name.to_string();
                match param_map.get(&param_name)? {
                    ParamKind::Binder => {
                        frame.positions.push(BinderPosition::BinderListLoop {
                            separator: String::new(),
                            close: String::new(),
                            inner_positions: vec![BinderPosition::BinderIdent],
                            collection_param_cat: None,
                            allow_empty: false,
                            allow_multi: false,
                            slot_idx: 0,
                        });
                        frame.args.push(ActionArgKind::BinderName);
                    },
                    ParamKind::Body { cat } | ParamKind::Simple { cat }
                        if mettail_ast::grammar::NonTerminalKind::classify(cat)
                            == mettail_ast::grammar::NonTerminalKind::Ident =>
                    {
                        frame.positions.push(BinderPosition::IdentTextCapture {
                            param_name: param_name.clone(),
                        });
                        frame.args.push(ActionArgKind::IdentText { param_name });
                    },
                    ParamKind::Body { cat } | ParamKind::Simple { cat } => {
                        frame.positions.push(BinderPosition::ParamParse {
                            cat: cat.clone(),
                            collection: None,
                        });
                        frame.args.push(ActionArgKind::Term(cat.clone()));
                    },
                    ParamKind::Guard => {
                        frame.positions.push(BinderPosition::GuardSlot);
                        frame.args.push(ActionArgKind::Predicate);
                    },
                    ParamKind::BinderList | ParamKind::SimpleCollection { .. } => return None,
                }
            },
            BinderSyntaxObservation::Op(operation) => match reader.operation(operation) {
                OptionalOperationObservation::Opt { inner } => {
                    let group_idx = *next_group_idx;
                    *next_group_idx = next_group_idx.checked_add(1)?;
                    frames.push(Frame {
                        items: inner,
                        next: 0,
                        positions: Vec::new(),
                        args: Vec::new(),
                        group_idx: Some(group_idx),
                    });
                },
                OptionalOperationObservation::Sep { collection, separator, source: None } => {
                    let close = match reader.at(frame.items, frame.next) {
                        Some(BinderSyntaxObservation::Literal(text)) => text.to_owned(),
                        _ => return None,
                    };
                    frame.next += 1;
                    match param_map.get(&collection.to_string())? {
                        ParamKind::BinderList => {
                            frame.positions.push(BinderPosition::BinderListLoop {
                                separator: separator.to_owned(),
                                close,
                                inner_positions: vec![BinderPosition::BinderIdent],
                                collection_param_cat: None,
                                allow_empty: true,
                                allow_multi: true,
                                slot_idx: 0,
                            });
                            frame.args.push(ActionArgKind::BinderList);
                        },
                        ParamKind::SimpleCollection { elem_cat, coll_kind } => {
                            let slot_idx = *collection_slots_so_far;
                            *collection_slots_so_far = collection_slots_so_far.checked_add(1)?;
                            frame.positions.push(BinderPosition::ParamParse {
                                cat: elem_cat.clone(),
                                collection: Some(CollectionSepInfo {
                                    separator: separator.to_owned(),
                                    close,
                                    elem_cat: elem_cat.clone(),
                                    key_val_separator: kv_sep_for(coll_kind),
                                    slot_idx,
                                }),
                            });
                            frame.args.push(ActionArgKind::CollectionDrain {
                                elem_cat: elem_cat.clone(),
                                coll_kind: coll_kind.clone(),
                            });
                        },
                        _ => return None,
                    }
                },
                _ => return None,
            },
        }
    }
}
