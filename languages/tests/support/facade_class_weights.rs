use mettail_prattail::automata::lex_weight::LexicographicWeight;
use mettail_prattail::wpda_runtime::{CursorBoundingMode, WpdaResolveResult, WpdaTokenSource};
use mettail_prattail::wpda_walker::{RealizeRequestMode, WpdaEngine, WpdaWalker};

pub fn enumerated_weights<E: WpdaEngine<LexicographicWeight> + Clone>(
    engine: E,
    category: u16,
    source: &dyn WpdaTokenSource,
) -> Vec<(Vec<u8>, LexicographicWeight)> {
    let mut walker = WpdaWalker::new_for_category(engine.clone(), category, 0);
    let mut recovery = mettail_prattail::recovery::RecoveryConfig::default();
    recovery.max_recovery_depth = 0;
    walker.set_recovery_config(recovery);
    walker.set_bounding_mode(CursorBoundingMode::Unbounded);
    walker
        .run_to_end_of_input(1_000_000, source)
        .expect("the small forest saturates");
    let roots = match walker.resolve_at_end_of_input(source) {
        WpdaResolveResult::Accepted { roots, .. }
        | WpdaResolveResult::AcceptedWithTrailing { roots, .. } => roots,
        other => panic!("the witness must have an accepting root: {other:?}"),
    };
    let mut weights = Vec::new();
    for root in roots {
        let terms = walker
            .realize_root_to_terms_with_weights(
                root,
                Some(4096),
                RealizeRequestMode::BoundedEnumeration,
            )
            .expect("raw enumeration succeeds");
        assert!(terms.len() < 4096, "the weight oracle must exhaust each root");
        weights.extend(terms.into_iter().map(|(term, weight)| {
            (
                engine
                    .semantic_fingerprint(&term)
                    .expect("the generated engine supplies keys"),
                weight,
            )
        }));
    }
    weights
}
