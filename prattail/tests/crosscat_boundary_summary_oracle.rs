//! Independent equivalence oracle for the incremental boundary-target lattice.
//!
//! The production summary is only an empty-result filter: a positive answer
//! still executes the exhaustive GSS walk. Therefore its safety obligation is
//! exact existential reachability—`may_recognize` must be false if and only if
//! the verified per-hop walk cannot emit a boundary for the supplied source
//! category and recognized-target set.

use mettail_prattail::crosscat_boundary::{BoundaryTargetSummary, HopFacts};
use mettail_prattail::wpda_runtime::SymbolKind;

fn oracle_is_rescoping(kind: SymbolKind) -> bool {
    matches!(
        kind,
        SymbolKind::MixfixMarker | SymbolKind::CollectionMarker | SymbolKind::GroupingMarker
    ) || matches!(kind, SymbolKind::RuleAt(k) if k > 0)
}

fn oracle_has_explicit_target(hop: &HopFacts) -> bool {
    hop.xcat == 4 || (hop.xcat == 3 && hop.xcat_wrap != u16::MAX)
}

fn oracle_target(hop: &HopFacts) -> Option<u16> {
    match hop.xcat {
        4 => Some(hop.pushed_cat),
        1 | 2 if hop.caller_kind.is_some() => Some(hop.caller_cat),
        3 if hop.xcat_wrap != u16::MAX => Some(hop.xcat_wrap),
        _ => None,
    }
}

fn oracle_linear_may_emit(hops: &[HopFacts], source_cat: u16, recognized: &[u16]) -> bool {
    for hop in hops {
        let caller_stops = hop.caller_kind.map(oracle_is_rescoping).unwrap_or(false);
        let explicit = oracle_has_explicit_target(hop);
        if caller_stops && !explicit {
            return false;
        }
        if let Some(target_cat) = oracle_target(hop) {
            if (explicit || target_cat != source_cat) && recognized.contains(&target_cat) {
                return true;
            }
        }
        if caller_stops {
            return false;
        }
    }
    false
}

fn summarize_linear(hops: &[HopFacts]) -> BoundaryTargetSummary {
    let mut inherited = BoundaryTargetSummary::default();
    for hop in hops.iter().rev() {
        let mut local = BoundaryTargetSummary::from_hop(hop);
        if local.inherits_callers() {
            local.union_targets_from(&inherited);
        }
        inherited = local;
    }
    inherited
}

#[test]
fn lattice_union_is_idempotent_across_inline_and_sparse_overflow_categories() {
    let cats = [0, 63, 64, 255, 256, 4095, u16::MAX];
    let mut union = BoundaryTargetSummary::default();
    for &cat in &cats {
        let hop = HopFacts {
            xcat: 4,
            xcat_bp: 0,
            xcat_wrap: u16::MAX,
            pushed_cat: cat,
            caller_kind: Some(SymbolKind::CategoryEntry),
            caller_cat: 0,
        };
        assert!(union.union_targets_from(&BoundaryTargetSummary::from_hop(&hop)));
    }
    for &cat in &cats {
        assert!(union.may_recognize(cat, |candidate| candidate == cat));
    }
    let snapshot = union.clone();
    assert!(!union.union_targets_from(&snapshot));
    assert_eq!(union, snapshot);
}

proptest::proptest! {
    #![proptest_config(proptest::prelude::ProptestConfig::with_cases(1_000))]
    #[test]
    fn incremental_summary_matches_the_independent_linear_walk_equation(
        raw_hops in proptest::collection::vec(
            (
                0_u8..7,
                proptest::prelude::any::<u16>(),
                proptest::prop_oneof![
                    proptest::prelude::Just(u16::MAX),
                    0_u16..512,
                ],
                0_u16..512,
                0_u8..9,
                0_u16..512,
            ),
            0..80,
        ),
        source_cat in 0_u16..512,
        recognized in proptest::collection::vec(0_u16..512, 0..32),
    ) {
        let hops: Vec<HopFacts> = raw_hops
            .into_iter()
            .map(|(xcat, xcat_bp, xcat_wrap, pushed_cat, caller_code, caller_cat)| {
                let caller_kind = match caller_code {
                    0 => None,
                    1 => Some(SymbolKind::CategoryEntry),
                    2 => Some(SymbolKind::RuleAt(0)),
                    3 => Some(SymbolKind::RuleAt(1)),
                    4 => Some(SymbolKind::InfixContinuation),
                    5 => Some(SymbolKind::Return),
                    6 => Some(SymbolKind::CollectionMarker),
                    7 => Some(SymbolKind::GroupingMarker),
                    _ => Some(SymbolKind::MixfixMarker),
                };
                HopFacts {
                    xcat,
                    xcat_bp,
                    xcat_wrap,
                    pushed_cat,
                    caller_kind,
                    caller_cat,
                }
            })
            .collect();
        let summary = summarize_linear(&hops);
        let summarized = summary.may_recognize(source_cat, |cat| recognized.contains(&cat));
        let exact = oracle_linear_may_emit(&hops, source_cat, &recognized);
        proptest::prop_assert_eq!(summarized, exact, "hops={:?}", hops);
    }
}
