//! Original iterative binder traversal and dense marker-table construction.
//!
//! Site rosters retain preorder; each rule emits all optional markers before
//! binder-list markers. Pointer keys belong only to the borrowed forest walk,
//! never to serialized descriptors. Callers admit the complete helper domain.
//! TraversalMarkerProjection.v checks the narrow marker/width interface.

use super::{BinderPosition, BinderShape};
use std::borrow::Borrow;
use std::collections::HashMap;

/// Exact original encoded field whose source value is not representable.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum TraversalWidth {
    CategoryIndex,
    RuleIndex,
    RuleResume,
    OptionalResume,
    BinderResume,
    BinderFrame,
    OptionalMarkerCount,
    BinderMarkerCount,
    MarkerId,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct TraversalWidthError {
    pub field: TraversalWidth,
    pub value: usize,
}

#[derive(Debug, Eq, PartialEq)]
pub enum TraversalBuildError<E> {
    Classify(E),
    Width(TraversalWidthError),
}

impl<E> From<TraversalWidthError> for TraversalBuildError<E> {
    fn from(error: TraversalWidthError) -> Self {
        Self::Width(error)
    }
}

fn checked_u16(value: usize, field: TraversalWidth) -> Result<u16, TraversalWidthError> {
    u16::try_from(value).map_err(|_| TraversalWidthError { field, value })
}

fn checked_rule_resume(index: usize) -> Result<u8, TraversalWidthError> {
    u8::try_from(index)
        .ok()
        .and_then(|value| value.checked_add(2))
        .ok_or(TraversalWidthError {
            field: TraversalWidth::RuleResume,
            value: index,
        })
}

fn checked_u32_after(
    value: usize,
    increment: u32,
    field: TraversalWidth,
) -> Result<u32, TraversalWidthError> {
    u32::try_from(value)
        .ok()
        .and_then(|value| value.checked_add(increment))
        .ok_or(TraversalWidthError { field, value })
}

fn checked_marker_successor(value: u32) -> Result<u32, TraversalWidthError> {
    value.checked_add(1).ok_or(TraversalWidthError {
        field: TraversalWidth::MarkerId,
        value: value as usize,
    })
}

/// Caller continuation for a nested optional or binder-list frame.
///
/// The generated PDA stores this continuation in the GSS symbol immediately
/// below the entered frame. Keeping it out of `WpdaState::BinderListLoop`
/// makes the state frame-local and permits arbitrary Optional/BinderList
/// nesting without caller-specific fields or native recursion.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum TraversalResume {
    Rule { next_pos: u8 },
    Optional { group_idx: u32, next_sub_pos: u32 },
    BinderList { frame_idx: u32, next_sub_pos: u32 },
}

pub struct BinderListSite<'position> {
    pub separator: &'position str,
    pub close: &'position str,
    pub inner_positions: &'position [BinderPosition],
    pub collection_param_cat: &'position Option<String>,
    pub slot_idx: u8,
    pub frame_idx: u32,
    pub resume: TraversalResume,
}

pub struct OptionalSite<'position> {
    pub positions: &'position [BinderPosition],
    pub group_idx: u32,
    pub first_token_set: &'position [String],
    pub resume: TraversalResume,
}

pub struct TraversalSites<'position> {
    pub binder_lists: Vec<BinderListSite<'position>>,
    pub optionals: Vec<OptionalSite<'position>>,
    pub binder_frame_indices: HashMap<*const BinderPosition, u32>,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum TraversalMarkerCoordinate {
    Optional { group_idx: u32, sub_pos: u32 },
    BinderList { frame_idx: u32, sub_pos: u32 },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TraversalMarkerTable {
    pub ids: HashMap<(u16, u16, TraversalMarkerCoordinate), u32>,
    pub optional_metadata: Vec<(u32, u16, u16, u32, u32)>,
    pub binder_metadata: Vec<(u32, u16, u16, u32, u32)>,
}

impl TraversalMarkerTable {
    /// Relocated original builder. Admission for the complete helper domain is
    /// supplied by the caller before invocation. A borrowed cached shape is
    /// accepted directly; classification is called exactly once per reached row.
    pub fn try_build_with<R, S: Borrow<BinderShape>, E>(
        per_cat: &[Vec<R>],
        mut classify: impl FnMut(&R) -> Result<Option<S>, E>,
    ) -> Result<Self, TraversalBuildError<E>> {
        let mut ids = HashMap::new();
        let mut optional_metadata = Vec::new();
        let mut binder_metadata = Vec::new();
        let mut next_marker_id = 0u32;

        for (cat_i, rules) in per_cat.iter().enumerate() {
            for (rule_i, rule) in rules.iter().enumerate() {
                let Some(shape) = classify(rule).map_err(TraversalBuildError::Classify)? else {
                    continue;
                };
                let result_src_idx = checked_u16(cat_i, TraversalWidth::CategoryIndex)?;
                let rule_idx = checked_u16(rule_i, TraversalWidth::RuleIndex)?;
                let shape = shape.borrow();
                let sites = try_traversal_sites(&shape.positions)?;
                for OptionalSite { positions, group_idx, .. } in sites.optionals {
                    let final_sub_pos =
                        checked_u32_after(positions.len(), 1, TraversalWidth::OptionalMarkerCount)?;
                    for sub_pos in 0..=final_sub_pos {
                        let marker_id = next_marker_id;
                        next_marker_id = checked_marker_successor(next_marker_id)?;
                        let coordinate = TraversalMarkerCoordinate::Optional { group_idx, sub_pos };
                        ids.insert((result_src_idx, rule_idx, coordinate), marker_id);
                        optional_metadata.push((
                            marker_id,
                            result_src_idx,
                            rule_idx,
                            group_idx,
                            sub_pos,
                        ));
                    }
                }
                for BinderListSite { inner_positions, frame_idx, .. } in sites.binder_lists {
                    let final_sub_pos = checked_u32_after(
                        inner_positions.len(),
                        1,
                        TraversalWidth::BinderMarkerCount,
                    )?;
                    for sub_pos in 0..=final_sub_pos {
                        let marker_id = next_marker_id;
                        next_marker_id = checked_marker_successor(next_marker_id)?;
                        let coordinate =
                            TraversalMarkerCoordinate::BinderList { frame_idx, sub_pos };
                        ids.insert((result_src_idx, rule_idx, coordinate), marker_id);
                        binder_metadata.push((
                            marker_id,
                            result_src_idx,
                            rule_idx,
                            frame_idx,
                            sub_pos,
                        ));
                    }
                }
            }
        }

        Ok(Self { ids, optional_metadata, binder_metadata })
    }

    pub fn id(
        &self,
        result_src_idx: u16,
        rule_idx: u16,
        coordinate: TraversalMarkerCoordinate,
    ) -> u32 {
        self.ids[&(result_src_idx, rule_idx, coordinate)]
    }
}

/// Build the recursive position forest's flat PDA-frame table iteratively.
/// Sites are emitted in deterministic preorder; depth is represented by the
/// heap-backed `pending` worklist rather than the native call stack.
pub fn try_traversal_sites(
    positions: &[BinderPosition],
) -> Result<TraversalSites<'_>, TraversalWidthError> {
    struct Pending<'position> {
        position: &'position BinderPosition,
        resume: TraversalResume,
    }

    let mut pending = Vec::with_capacity(positions.len());
    for (idx, position) in positions.iter().enumerate().rev() {
        pending.push(Pending {
            position,
            resume: TraversalResume::Rule { next_pos: checked_rule_resume(idx)? },
        });
    }

    let mut binder_lists = Vec::new();
    let mut optionals = Vec::new();
    let mut binder_frame_indices = HashMap::new();
    while let Some(Pending { position, resume }) = pending.pop() {
        match position {
            BinderPosition::OptionalGroup { positions, group_idx, first_token_set } => {
                optionals.push(OptionalSite {
                    positions,
                    group_idx: *group_idx,
                    first_token_set,
                    resume,
                });
                for (idx, child) in positions.iter().enumerate().rev() {
                    pending.push(Pending {
                        position: child,
                        resume: TraversalResume::Optional {
                            group_idx: *group_idx,
                            next_sub_pos: checked_u32_after(
                                idx,
                                2,
                                TraversalWidth::OptionalResume,
                            )?,
                        },
                    });
                }
            },
            BinderPosition::BinderListLoop {
                separator,
                close,
                inner_positions,
                collection_param_cat,
                slot_idx,
                ..
            } => {
                let frame_idx =
                    checked_u32_after(binder_lists.len(), 0, TraversalWidth::BinderFrame)?;
                binder_frame_indices.insert(position as *const BinderPosition, frame_idx);
                binder_lists.push(BinderListSite {
                    separator,
                    close,
                    inner_positions,
                    collection_param_cat,
                    slot_idx: *slot_idx,
                    frame_idx,
                    resume,
                });
                let last = inner_positions.len().saturating_sub(1);
                for (idx, child) in inner_positions.iter().enumerate().rev() {
                    pending.push(Pending {
                        position: child,
                        resume: TraversalResume::BinderList {
                            frame_idx,
                            next_sub_pos: if idx == last {
                                0
                            } else {
                                checked_u32_after(idx, 2, TraversalWidth::BinderResume)?
                            },
                        },
                    });
                }
            },
            _ => {},
        }
    }

    Ok(TraversalSites {
        binder_lists,
        optionals,
        binder_frame_indices,
    })
}

/// Static compatibility entrypoint over the same checked worklist.
pub fn traversal_sites(positions: &[BinderPosition]) -> TraversalSites<'_> {
    try_traversal_sites(positions)
        .expect("binder traversal coordinates exceed compact source addressability")
}

pub fn binder_list_frame_indices(
    positions: &[BinderPosition],
) -> HashMap<*const BinderPosition, u32> {
    traversal_sites(positions).binder_frame_indices
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::convert::Infallible;

    fn shape(positions: Vec<BinderPosition>) -> BinderShape {
        BinderShape {
            label: "Test".into(),
            result_cat: "Expr".into(),
            leading_category: None,
            leading_ident_capture: None,
            positions,
            is_multi: false,
            has_binder: false,
            action_arity: 0,
            action_args: Vec::new(),
            body_cat: None,
            param_cats: Vec::new(),
        }
    }

    fn empty_optional() -> BinderPosition {
        BinderPosition::OptionalGroup {
            positions: Vec::new(),
            group_idx: 9,
            first_token_set: Vec::new(),
        }
    }

    #[test]
    fn marker_order_and_duplicate_coordinate_last_write_match_original() {
        let shape = shape(vec![
            BinderPosition::BinderListLoop {
                separator: ",".into(),
                close: ")".into(),
                inner_positions: Vec::new(),
                collection_param_cat: None,
                allow_empty: true,
                allow_multi: true,
                slot_idx: 0,
            },
            empty_optional(),
            empty_optional(),
        ]);
        let borrowed = TraversalMarkerTable::try_build_with(&[vec![&shape]], |row| {
            Ok::<_, Infallible>(Some(*row))
        })
        .expect("small borrowed forest must build");
        let owned = TraversalMarkerTable::try_build_with(&[vec![()]], |_| {
            Ok::<_, Infallible>(Some(shape.clone()))
        })
        .expect("small owned forest must build");
        assert_eq!(borrowed, owned);
        assert_eq!(
            borrowed.optional_metadata,
            vec![(0, 0, 0, 9, 0), (1, 0, 0, 9, 1), (2, 0, 0, 9, 0), (3, 0, 0, 9, 1),]
        );
        assert_eq!(borrowed.binder_metadata, vec![(4, 0, 0, 0, 0), (5, 0, 0, 0, 1)]);
        assert_eq!(
            borrowed.id(0, 0, TraversalMarkerCoordinate::Optional { group_idx: 9, sub_pos: 0 }),
            2
        );
        assert_eq!(borrowed.ids.len(), 4);
    }

    #[test]
    fn classifier_error_returns_only_the_first_failure_prefix() {
        let shape = shape(vec![empty_optional()]);
        let mut seen = Vec::new();
        let result = TraversalMarkerTable::try_build_with(&[vec![0, 1, 2]], |row| {
            seen.push(*row);
            if *row == 1 {
                Err("classifier refused")
            } else {
                Ok(Some(&shape))
            }
        });
        assert_eq!(seen, vec![0, 1]);
        assert_eq!(result, Err(TraversalBuildError::Classify("classifier refused")));
    }

    #[test]
    fn source_width_checks_cover_exact_encoded_boundaries() {
        for field in [TraversalWidth::CategoryIndex, TraversalWidth::RuleIndex] {
            assert_eq!(checked_u16(usize::from(u16::MAX), field), Ok(u16::MAX));
            assert_eq!(
                checked_u16(usize::from(u16::MAX) + 1, field),
                Err(TraversalWidthError { field, value: 65536 })
            );
        }
        assert_eq!(checked_rule_resume(253), Ok(u8::MAX));
        assert_eq!(
            checked_rule_resume(254),
            Err(TraversalWidthError {
                field: TraversalWidth::RuleResume,
                value: 254,
            })
        );
        for field in [TraversalWidth::OptionalResume, TraversalWidth::BinderResume] {
            assert_eq!(checked_u32_after((u32::MAX - 2) as usize, 2, field), Ok(u32::MAX));
            assert!(matches!(checked_u32_after((u32::MAX - 1) as usize, 2, field),
                Err(TraversalWidthError { field: got, .. }) if got == field));
        }
        for field in [TraversalWidth::OptionalMarkerCount, TraversalWidth::BinderMarkerCount] {
            assert_eq!(checked_u32_after((u32::MAX - 1) as usize, 1, field), Ok(u32::MAX));
            assert!(matches!(checked_u32_after(u32::MAX as usize, 1, field),
                Err(TraversalWidthError { field: got, .. }) if got == field));
        }
        assert_eq!(
            checked_u32_after(u32::MAX as usize, 0, TraversalWidth::BinderFrame),
            Ok(u32::MAX)
        );
        assert_eq!(checked_marker_successor(u32::MAX - 1), Ok(u32::MAX));
        assert_eq!(
            checked_marker_successor(u32::MAX),
            Err(TraversalWidthError {
                field: TraversalWidth::MarkerId,
                value: u32::MAX as usize,
            })
        );
    }

    #[test]
    fn original_root_continuation_boundary_is_enforced_by_the_same_worklist() {
        let mut positions: Vec<_> = (0..254).map(|_| BinderPosition::BinderIdent).collect();
        assert!(try_traversal_sites(&positions).is_ok());
        positions.push(BinderPosition::BinderIdent);
        assert!(matches!(
            try_traversal_sites(&positions),
            Err(TraversalWidthError {
                field: TraversalWidth::RuleResume,
                value: 254,
            })
        ));
    }
}
