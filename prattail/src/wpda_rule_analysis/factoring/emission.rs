//! Pure fields of the original spine emission bundle.
//!
//! This is the data-writing portion of `build_spine_emission_from_parts`,
//! shared without regenerating its token quotation or its factoring trees.
//! `FactoringEmissionData.v` models preservation of these writes when quotation
//! is erased. Existing group member helpers retain ordering and identity.

use std::collections::HashMap;

use super::super::mixfix::MixfixFactoring;
use super::CategoryFactoring;

/// A grouped rule's original prefix-emission disposition.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SpineDisposition {
    /// The minimum member carries the group's initiating branch.
    GroupFirst {
        spine_id: u16,
        body_src_idx: u16,
        /// Original member identity for weight accounting, never the spine id.
        weight_rule_idx: u16,
    },
    /// This member is emitted by the group's first member.
    GroupRest,
}

/// Per-category lex-alt adjustments from the same disposition writes.
#[derive(Debug, Default, PartialEq, Eq)]
pub struct SpineLexAlt {
    pub grouped: HashMap<u16, SpineDisposition>,
}

/// Original mixfix cohort coordinates consumed by dispatch and lex-alt emission.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MixfixGroupEmission {
    pub dispatch_cat_src_idx: u16,
    pub trigger: String,
    pub result_src_idx: u16,
    pub spine_id: u16,
    pub min_l_bp: u8,
    pub min_member_rule_idx: u16,
    /// Original slice order, not a sorted member set.
    pub member_rule_idxs: Vec<u16>,
}

/// Shared data fields of the original macro emission bundle.
#[derive(Debug, PartialEq, Eq)]
pub struct FactoringEmissionDescriptors {
    pub dispositions: Vec<HashMap<u16, SpineDisposition>>,
    /// Minimum member to the complete ordered prefix group member roster.
    pub group_members: Vec<HashMap<u16, Vec<u16>>>,
    pub lex_alt: Vec<SpineLexAlt>,
    pub mixfix_groups: Vec<MixfixGroupEmission>,
}

/// Malformed partition data that previously failed an index or group assertion.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FactoringEmissionError {
    InvalidCategoryIndex { category: u16, category_count: usize },
    EmptyPrefixGroup { category: u16, spine_id: u16 },
}

/// Collect the original pure emission fields, retaining last-write map behavior.
///
/// Prefix groups use their unchanged sorted-set member helper; mixfix groups
/// use their unchanged slice-order helper. No tree or partition is rebuilt.
/// Errors discard private output; the caller owns resource admission.
pub fn try_build_factoring_emission_descriptors(
    category_count: usize,
    partition: &[CategoryFactoring],
    mixfix_partition: &[MixfixFactoring],
) -> Result<FactoringEmissionDescriptors, FactoringEmissionError> {
    let mut dispositions: Vec<HashMap<u16, SpineDisposition>> =
        (0..category_count).map(|_| HashMap::new()).collect();
    let mut group_members: Vec<HashMap<u16, Vec<u16>>> =
        (0..category_count).map(|_| HashMap::new()).collect();
    let mut lex_alt: Vec<SpineLexAlt> = (0..category_count)
        .map(|_| SpineLexAlt::default())
        .collect();
    for cat_fact in partition {
        let cat = cat_fact.category_src_idx;
        let cat_usize = cat as usize;
        if cat_usize >= category_count {
            return Err(FactoringEmissionError::InvalidCategoryIndex {
                category: cat,
                category_count,
            });
        }
        for bucket in &cat_fact.buckets {
            for group in &bucket.groups {
                let spine_id = group.spine_id;
                let body_src_idx = group.body_src_idx;
                let members = group.member_rule_idxs();
                let weight_rule_idx = *members
                    .iter()
                    .next()
                    .ok_or(FactoringEmissionError::EmptyPrefixGroup { category: cat, spine_id })?;
                let mut first = true;
                let mut ordered: Vec<u16> = members.iter().copied().collect();
                ordered.sort_unstable();
                if let Some(&first_member) = ordered.first() {
                    group_members[cat_usize].insert(first_member, ordered.clone());
                }
                for m in ordered {
                    let d = if first {
                        first = false;
                        SpineDisposition::GroupFirst { spine_id, body_src_idx, weight_rule_idx }
                    } else {
                        SpineDisposition::GroupRest
                    };
                    dispositions[cat_usize].insert(m, d);
                    lex_alt[cat_usize].grouped.insert(m, d);
                }
            }
        }
    }
    let mut mixfix_groups = Vec::new();
    for fact in mixfix_partition {
        let dispatch_cat = fact.dispatch_cat_src_idx;
        for bucket in &fact.buckets {
            for group in &bucket.groups {
                let result_src = group.result_src_idx;
                if result_src as usize >= category_count {
                    return Err(FactoringEmissionError::InvalidCategoryIndex {
                        category: result_src,
                        category_count,
                    });
                }
                mixfix_groups.push(MixfixGroupEmission {
                    dispatch_cat_src_idx: dispatch_cat,
                    trigger: bucket.trigger.clone(),
                    result_src_idx: result_src,
                    spine_id: group.spine_id,
                    min_l_bp: group.min_l_bp,
                    min_member_rule_idx: group.min_member_rule_idx,
                    member_rule_idxs: group.member_rule_idxs(),
                });
            }
        }
    }
    Ok(FactoringEmissionDescriptors {
        dispositions,
        group_members,
        lex_alt,
        mixfix_groups,
    })
}

#[cfg(test)]
mod tests {
    use super::super::super::mixfix::{MixfixBucket, MixfixGroup};
    use super::super::{
        build_tree, CandidateMember, FactoringBucket, MemberKind, SpineGroup, SpineItem,
    };
    use super::*;

    fn prefix(category: u16, spine_id: u16, roster: &[u16]) -> CategoryFactoring {
        let item = SpineItem::Literal {
            text: "end".into(),
            required_top_cat: None,
        };
        let members = roster
            .iter()
            .map(|&rule_idx| CandidateMember {
                kind: MemberKind::Nullary,
                rule_idx,
                items: vec![
                    item.clone(),
                    SpineItem::Literal {
                        text: rule_idx.to_string(),
                        required_top_cat: None,
                    },
                ],
                truncated: false,
                total_positions: 2,
                body_src_idx: None,
                mixfix_coords: vec![],
            })
            .collect();
        let roots = build_tree(1, item, members, false, &mut vec![], &mut vec![]);
        CategoryFactoring {
            category_src_idx: category,
            refusals: vec![],
            buckets: vec![FactoringBucket {
                leading_literal: "start".into(),
                cohort_size: roster.len(),
                groups: vec![SpineGroup { spine_id, body_src_idx: 1, roots }],
                ineligible: vec![],
                singletons: vec![],
            }],
        }
    }

    #[test]
    fn prefix_roster_sorted_minimum_and_repeated_key_last_write() {
        let partition = [prefix(0, 0xf800, &[9, 2, 7]), prefix(0, 0xf801, &[2, 5])];
        let out = try_build_factoring_emission_descriptors(2, &partition, &[])
            .expect("nonempty prefix groups have valid category indexes");
        assert_eq!(out.group_members[0][&2], vec![2, 5]);
        assert_eq!(
            out.dispositions[0][&2],
            SpineDisposition::GroupFirst {
                spine_id: 0xf801,
                body_src_idx: 1,
                weight_rule_idx: 2,
            }
        );
        for member in [5, 7, 9] {
            assert_eq!(out.dispositions[0][&member], SpineDisposition::GroupRest);
        }
        assert_eq!(out.lex_alt[0].grouped, out.dispositions[0]);
        assert!(out.dispositions[1].is_empty());
        assert!(out.mixfix_groups.is_empty());
        assert!(matches!(
            try_build_factoring_emission_descriptors(0, &partition, &[]),
            Err(FactoringEmissionError::InvalidCategoryIndex { category: 0, category_count: 0 })
        ));
        let empty = prefix(0, 0xf800, &[]);
        assert!(matches!(
            try_build_factoring_emission_descriptors(1, &[empty], &[]),
            Err(FactoringEmissionError::EmptyPrefixGroup { category: 0, spine_id: 0xf800 })
        ));
    }

    #[test]
    fn mixfix_retains_slice_order_and_result_ownership() {
        let partition = [MixfixFactoring {
            dispatch_cat_src_idx: 1,
            refusals: vec![],
            buckets: vec![MixfixBucket {
                trigger: "!".into(),
                slice: vec![],
                ineligible: vec![],
                singletons: vec![],
                groups: vec![MixfixGroup {
                    spine_id: 0xf802,
                    result_src_idx: 0,
                    min_l_bp: 4,
                    min_member_rule_idx: 2,
                    member_l_bps: vec![(9, 7), (4, 2)],
                    expected_cats_union: vec![],
                    fixb_literal: None,
                    roots: vec![],
                }],
            }],
        }];
        let out = try_build_factoring_emission_descriptors(2, &[], &partition)
            .expect("mixfix result category is in bounds");
        assert_eq!(
            out.mixfix_groups,
            vec![MixfixGroupEmission {
                dispatch_cat_src_idx: 1,
                trigger: "!".into(),
                result_src_idx: 0,
                spine_id: 0xf802,
                min_l_bp: 4,
                min_member_rule_idx: 2,
                member_rule_idxs: vec![7, 2],
            }]
        );
        assert!(matches!(
            try_build_factoring_emission_descriptors(0, &[], &partition),
            Err(FactoringEmissionError::InvalidCategoryIndex { category: 0, category_count: 0 })
        ));
    }
}
