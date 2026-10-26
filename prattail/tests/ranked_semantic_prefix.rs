use mettail_prattail::automata::semiring::ExactParseCost;
use mettail_prattail::derivation_rank::{
    ranked_semantic_prefix, CompleteDerivationRank, RankFragment,
};
use proptest::prelude::*;
use std::collections::BTreeSet;

fn rank(position: u32, category: u16, rule: u16) -> CompleteDerivationRank {
    CompleteDerivationRank::from_positioned_fragments([(
        position,
        RankFragment::rule(category, rule),
    )])
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(256))]

    #[test]
    fn ranked_prefix_retains_actual_minima_and_preserves_the_class_set(
        input in prop::collection::vec((0u8..12, 0u64..40, 0u32..8, 0u16..8, 0u16..16), 0..80),
        limit in 0usize..24,
    ) {
        let readings: Vec<_> = input.into_iter().enumerate()
            .map(|(id, (class, cost, pos, cat, rule))|
                ((class, id), ExactParseCost::from_ticks(cost).unwrap(), rank(pos, cat, rule)))
            .collect();
        let all = ranked_semantic_prefix(readings.clone(), usize::MAX, |term| term.0);
        let expected_classes: BTreeSet<_> = readings.iter().map(|r| r.0.0).collect();
        let actual_classes: BTreeSet<_> = all.iter().map(|r| r.0.0).collect();
        prop_assert_eq!(&actual_classes, &expected_classes);
        prop_assert_eq!(all.len(), expected_classes.len());
        for reading in &all {
            prop_assert!(readings.contains(reading));
            let class: Vec<_> = readings.iter().filter(|r| r.0.0 == reading.0.0).collect();
            let min_cost = class.iter().map(|r| r.1).min().unwrap();
            prop_assert_eq!(reading.1, min_cost);
            let min_rank = class.iter().filter(|r| r.1 == min_cost)
                .map(|r| &r.2).min().unwrap();
            prop_assert_eq!(&reading.2, min_rank);
            let first_minimum = class.iter()
                .find(|r| r.1 == min_cost && &r.2 == min_rank).unwrap();
            prop_assert_eq!(&reading.0, &first_minimum.0);
        }
        prop_assert!(all.windows(2).all(|pair|
            (&pair[0].1, &pair[0].2) <= (&pair[1].1, &pair[1].2)));
        let prefix = ranked_semantic_prefix(readings, limit, |term| term.0);
        prop_assert!(prefix.len() <= limit);
        prop_assert_eq!(&prefix, &all[..all.len().min(limit)]);
        if all.len() <= limit { prop_assert_eq!(prefix, all); }
    }

    #[test]
    fn lower_cost_dominates_every_rank(
        low in 0u64..1000,
        delta in 1u64..1000,
        low_rule in any::<u16>(),
        high_rule in any::<u16>(),
    ) {
        let first = ((0u8, 1), ExactParseCost::from_ticks(low + delta).unwrap(), rank(0, 0, high_rule));
        let second = ((0u8, 2), ExactParseCost::from_ticks(low).unwrap(), rank(0, 0, low_rule));
        let result = ranked_semantic_prefix([first, second.clone()], 1, |term| term.0);
        prop_assert_eq!(result, vec![second]);
    }
}

#[test]
fn equal_cost_requires_the_actual_later_rank_witness() {
    let cost = ExactParseCost::from_ticks(1).unwrap();
    let first = ((7, 1), cost, rank(0, 0, 9));
    let second = ((7, 2), cost, rank(0, 0, 2));
    assert_eq!(ranked_semantic_prefix([first, second.clone()], 1, |term| term.0), vec![second],);
}
