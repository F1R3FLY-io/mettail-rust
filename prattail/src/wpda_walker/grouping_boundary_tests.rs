use super::*;
use crate::automata::lex_weight::LexicographicWeight;
use crate::wpda_owned::structural::GROUPING_ACTION;

struct Engine(bool);
impl WpdaEngine<LexicographicWeight> for Engine {
    fn step(
        &self,
        _: &WpdaState,
        _: &WpdaGss<LexicographicWeight>,
        _: Option<&WpdaGssNode>,
        _: usize,
        _: &dyn WpdaTokenSource,
        _: crate::wpda_runtime::FrameCtx,
    ) -> WpdaStepAction<LexicographicWeight> {
        WpdaStepAction::Idle
    }
    fn grouping_boundary_rule(&self) -> Option<u32> {
        self.0.then_some(GROUPING_ACTION)
    }
}

#[test]
fn grouping_boundary_retains_exact_frame_and_close_witness_with_unit_packing() {
    for enabled in [false, true] {
        let mut walker = WpdaWalker::new(Engine(enabled), 0);
        let marker = StackSymbolV2::grouping_marker(3, 9);
        let u = walker
            .gss
            .get_or_create_node(WpdaGssNode { pos: 17, symbol: marker });
        let child = walker.sppf.intern_symbol(3 | CGLL_BIN_TAG, 41, 29);
        let mut descriptor = CgllPureDescriptor {
            state: WpdaState::Unwinding,
            cur_sym: marker,
            frame_class: CgllFrameClass::D1,
            ret_slot: WpdaWalker::<LexicographicWeight, Engine>::cgll_pure_seed_slot(&marker),
            u,
            pos: 29,
            w: child,
        };
        let before = walker.sppf.len();
        let grouped = walker.cgll_retain_grouping_boundary(&descriptor, 8);
        if !enabled {
            assert_eq!(grouped, child);
            assert_eq!(walker.sppf.len(), before, "static passthrough allocates nothing");
            continue;
        }
        assert_ne!(grouped, child);
        assert!(matches!(walker.sppf.node(grouped), Some(crate::sppf::SppfNode::Symbol {
            non_terminal_tag, lo_pos: 17, hi_pos: 8, ..
        }) if *non_terminal_tag == 3 | CGLL_BIN_TAG));
        let packings = walker.sppf.packings_of(grouped);
        assert_eq!(packings.len(), 1);
        assert!(matches!(walker.sppf.node(packings[0]), Some(crate::sppf::SppfNode::Packing {
            rule_idx, children, weight
        }) if *rule_idx == GROUPING_ACTION && children == &[child] && *weight == LexicographicWeight::one_ref()));
        descriptor.cur_sym = StackSymbolV2::category_entry(3);
        assert_eq!(
            walker.cgll_retain_grouping_boundary(&descriptor, 8),
            child,
            "non-grouping transitions never manufacture a boundary"
        );
    }
}
