use super::*;
use crate::automata::lex_weight::LexicographicWeight;
use crate::automata::semiring::Semiring;
use crate::wpda_runtime::{SliceTokenSource, ANY_CAT};
use proptest::prelude::*;
use std::cell::Cell;

#[derive(Clone, Debug, PartialEq, Eq)]
struct Value {
    category: u16,
    number: i64,
}

struct Engine {
    signature: Option<(u8, Vec<u16>)>,
    output: u16,
    calls: Cell<usize>,
    fail: bool,
}

impl WpdaEngine<LexicographicWeight> for Engine {
    fn step(
        &self,
        _: &WpdaState,
        _: &WpdaGss<LexicographicWeight>,
        _: Option<&WpdaGssNode>,
        _: usize,
        _: &dyn WpdaTokenSource,
        _: crate::wpda_runtime::FrameCtx<'_>,
    ) -> WpdaStepAction<LexicographicWeight> {
        WpdaStepAction::Idle
    }

    fn action_signature(&self, category: u16, rule: u16) -> Option<ActionSignature<'_>> {
        if rule == 0 || is_spine_rule_id(rule) {
            self.signature
                .as_ref()
                .map(|(arity, inputs)| ActionSignature {
                    arity: *arity,
                    expected_input_cats: inputs,
                    output_cat: self.output,
                })
        } else {
            Some(ActionSignature {
                arity: u8::from(rule < 4),
                expected_input_cats: if rule < 4 { &[ANY_CAT] } else { &[] },
                output_cat: category,
            })
        }
    }

    fn execute_action(
        &self,
        category: u16,
        rule: u16,
        builder: &mut SemanticBuilder,
        args: Vec<ActionArg>,
    ) -> Result<(), ActionInvocationError> {
        self.calls.set(self.calls.get() + 1);
        let number = match rule {
            0 | 1 => {
                let [ActionArg::Term { value, .. }] = args.as_slice() else {
                    return Ok(());
                };
                let Some(value) = value.downcast_ref::<Value>() else {
                    return Ok(());
                };
                if rule == 0 {
                    let Some((_, inputs)) = &self.signature else {
                        return Ok(());
                    };
                    if inputs.as_slice() != [ANY_CAT] && inputs.as_slice() != [value.category] {
                        return Ok(());
                    }
                    if self.fail {
                        return Err(ActionInvocationError::ResultCount { actual: 2 });
                    }
                }
                value.number + 100
            },
            2 => match args.as_slice() {
                [ActionArg::Optional(Some(items))] => {
                    let [ActionArg::Term { value, .. }] = items.as_slice() else {
                        return Ok(());
                    };
                    let Some(value) = value.downcast_ref::<Value>() else {
                        return Ok(());
                    };
                    value.number + 1000
                },
                [ActionArg::Optional(None)] => 999,
                _ => return Ok(()),
            },
            3 => {
                let [ActionArg::CollectionId(id)] = args.as_slice() else {
                    return Ok(());
                };
                let Ok(values) = ActionArg::try_into_terms::<Value>(builder.drain_collection(*id))
                else {
                    return Ok(());
                };
                values.iter().map(|value| value.number).sum()
            },
            _ => i64::from(rule),
        };
        builder.push_term(Value { category, number });
        Ok(())
    }

    fn term_category(&self, value: &(dyn Any + Send + Sync), _: &str) -> Option<u16> {
        value.downcast_ref::<Value>().map(|value| value.category)
    }

    fn semantic_fingerprint(&self, value: &Arc<dyn Any + Send + Sync>) -> Option<Vec<u8>> {
        let value = value.downcast_ref::<Value>()?;
        Some(
            [value.category.to_le_bytes().as_slice(), value.number.to_le_bytes().as_slice()]
                .concat(),
        )
    }
}

type Walker = WpdaWalker<LexicographicWeight, Engine>;

fn walker(expected: u16, output: u16, hi: usize) -> Walker {
    let mut walker = WpdaWalker::new_for_category(
        Engine {
            signature: Some((1, vec![expected])),
            output,
            calls: Cell::new(0),
            fail: false,
        },
        output,
        0,
    );
    walker.cgll_pure_virtual_base = hi + 1;
    walker.sppf = crate::sppf::Sppf::retaining_packing_evidence();
    walker.cgll_pure_pos_key = (0..=hi).map(|pos| pos as u32).collect();
    walker
}

fn descriptor(
    walker: &mut Walker,
    category: u16,
    body: crate::sppf::SppfId,
    lo: usize,
    hi: usize,
) -> CgllPureDescriptor {
    let symbol = StackSymbolV2::return_symbol(category, 0);
    let u = walker.gss.get_or_create_node(WpdaGssNode {
        pos: lo,
        symbol: StackSymbolV2::category_entry(category),
    });
    CgllPureDescriptor {
        state: WpdaState::Unwinding,
        cur_sym: symbol,
        frame_class: CgllFrameClass::D1,
        ret_slot: Walker::cgll_pure_seed_slot(&symbol),
        u,
        pos: hi,
        w: body,
    }
}

fn reduce(
    walker: &mut Walker,
    run: &mut CgllPureRun,
    descriptor: &CgllPureDescriptor,
    weight: &LexicographicWeight,
) -> Result<(), WalkerResourceError> {
    let kinds = vec![crate::automata::TokenKind::Ident; descriptor.pos];
    let texts = vec!["x"; descriptor.pos];
    walker.try_cgll_pure_reduce(
        run,
        descriptor,
        descriptor.pos,
        weight,
        &WpdaState::Unwinding,
        &SliceTokenSource::with_texts(&kinds, &texts),
    )
}

fn snapshot(walker: &Walker, run: &CgllPureRun, u: crate::gss::GssNodeId) -> String {
    let forest: Vec<_> = (0..walker.sppf.len())
        .map(|id| walker.sppf.node(id as u32))
        .collect();
    format!(
        "{forest:?}|{}|{}|{}|{:?}|{:?}|{:?}|{:?}|{}|{}|{}|{:?}|{:?}",
        walker.sppf.link_count(),
        walker.gss.node_count(),
        walker.gss.edge_count(),
        walker.gss.gll_recorded_pops(u),
        run.worklist,
        run.accepting,
        run.prefix_accepting,
        run.stats.seed_pops,
        run.stats.unwind_chain_fired,
        run.stats.gll_pops,
        run.accept_seen,
        run.prefix_seen
    )
}

fn packing(
    walker: &mut Walker,
    category: u16,
    rule: u16,
    children: Vec<u32>,
    lo: u32,
    hi: u32,
) -> u32 {
    let symbol = walker
        .sppf
        .intern_symbol(CGLL_BIN_TAG | u32::from(category), lo, hi);
    let packed = walker.sppf.intern_packing(
        (u32::from(category) << 16) | u32::from(rule),
        children,
        LexicographicWeight::one(),
    );
    walker.sppf.link_packing_to_symbol(symbol, packed);
    symbol
}

proptest! {
    #![proptest_config(proptest::test_runner::Config::with_cases(96))]

    #[test]
    fn typed_unary_publication_classifier_and_reduce_preserve_conservative_cases(
        actual in 0u16..ANY_CAT, expected in 0u16..ANY_CAT, output in 0u16..ANY_CAT,
        metadata in 0u8..8, shape in 0u8..6, kind in 0u8..5,
        d2 in any::<bool>(), spine in any::<bool>(), bin in any::<bool>(),
        lo in 0usize..3, width in 0usize..5, offset in 0u32..65535,
    ) {
        let rename = |category: u16| if category == ANY_CAT { category }
            else { ((u32::from(category) + offset) % 65535) as u16 };
        for (metadata, shape, kind, d2, spine) in [
            (metadata, shape, kind, d2, spine),
            (7, 0, 0, false, false), (7, 0, 1, false, false), (7, 0, 2, false, false),
            (7, 0, 3, false, false), (7, 0, 4, false, false),
            (7, 0, 0, true, false), (7, 0, 0, false, true),
            (0, 0, 0, false, false), (1, 0, 0, false, false), (2, 0, 0, false, false),
            (3, 0, 0, false, false), (4, 0, 0, false, false), (5, 0, 0, false, false),
            (6, 0, 0, false, false),
        ] {
        let mut outcomes = Vec::new();
        for renamed in [false, true] {
            let map = |cat| if renamed { rename(cat) } else { cat };
            let actual = map(actual);
            let expected = map(expected);
            let output = map(output);
            let hi = lo + width;
            let mut walker = walker(expected, output, hi);
            walker.engine.signature = match metadata {
                0 => None, 1 => Some((0, vec![expected])), 2 => Some((2, vec![expected])),
                3 => Some((1, vec![])), 4 => Some((1, vec![expected, actual])),
                5 => Some((1, vec![ANY_CAT])), 6 => Some((1, vec![actual])),
                _ => Some((1, vec![expected])),
            };
            let body = match shape {
                0 => walker.sppf.intern_symbol(u32::from(actual) | if bin { CGLL_BIN_TAG } else { 0 }, lo as u32, hi as u32),
                1 => crate::sppf::SPPF_ID_NONE,
                2 => walker.sppf.intern_intermediate(42, lo as u32, hi as u32),
                3 => walker.sppf.intern_collection_id(0, vec![]),
                4 => walker.sppf.intern_opt_absent(lo as u32),
                _ => walker.sppf.intern_packing(42, vec![], LexicographicWeight::one()),
            };
            let mut descriptor = descriptor(&mut walker, output, body, lo, hi);
            descriptor.frame_class = if d2 { CgllFrameClass::D2 } else { CgllFrameClass::D1 };
            descriptor.cur_sym.kind = match kind { 0 => SymbolKind::Return, 1 => SymbolKind::RuleAt(1),
                2 => SymbolKind::MixfixMarker, 3 => SymbolKind::CategoryEntry, _ => SymbolKind::GroupingMarker };
            if spine { descriptor.cur_sym.rule_index_in_category = crate::wpda_rule_analysis::factoring::SPINE_RULE_BASE; }
            let rejected = !d2 && !spine && kind < 3 && shape == 0 && metadata == 7 && actual != expected;
            prop_assert_eq!(walker.cgll_pure_unary_body_is_incompatible(&descriptor), rejected);
            outcomes.push(rejected);
            if !d2 && !spine && kind < 3 {
                let mut run = CgllPureRun::default();
                run.stats.seed_pops = 7;
                run.stats.unwind_chain_fired = 11;
                let before = snapshot(&walker, &run, descriptor.u);
                let weight = LexicographicWeight::from_cost(0.125, output, 0);
                reduce(&mut walker, &mut run, &descriptor, &weight).unwrap();
                if rejected {
                    prop_assert_eq!(&snapshot(&walker, &run, descriptor.u), &before);
                    reduce(&mut walker, &mut run, &descriptor, &weight).unwrap();
                    prop_assert_eq!(snapshot(&walker, &run, descriptor.u), before);
                } else {
                    prop_assert_eq!(run.stats.seed_pops, 8);
                    prop_assert_eq!(run.stats.unwind_chain_fired, 12);
                    let published = run.accepting.first().expect("admitted seed publishes").0;
                    prop_assert_eq!(walker.sppf_symbol_category(published), Some(output));
                    let expected_children = if body == crate::sppf::SPPF_ID_NONE { vec![] } else { vec![body] };
                    prop_assert!(walker.sppf.packing_exists(u32::from(output) << 16, &expected_children));
                }
                prop_assert_eq!(walker.engine.calls.get(), 0);
            }
        }
        prop_assert_eq!(outcomes[0], outcomes[1]);
        }
    }

    #[test]
    fn typed_unary_publication_retains_exact_payload_and_errors(
        input in 0u16..500, output in 501u16..1000,
        rule in 4u16..32, lo in 0usize..3, width in 0usize..5,
    ) {
        let hi = lo + width;
        let mut walker = walker(input, output, hi);
        let body = packing(&mut walker, input, rule, vec![], lo as u32, hi as u32);
        let descriptor = descriptor(&mut walker, output, body, lo, hi);
        let mut run = CgllPureRun::default();
        let weight = LexicographicWeight::from_cost(0.125, output, 0);
        walker.resource_limits = Some(WalkerResourceLimits { parse_items: usize::MAX, forest_nodes: walker.sppf.len() });
        let limit = walker.sppf.len();
        prop_assert_eq!(reduce(&mut walker, &mut run, &descriptor, &weight),
            Err(WalkerResourceError::ForestNodeLimit { limit, position: walker.resource_position }));
        walker.resource_limits = None;
        reduce(&mut walker, &mut run, &descriptor, &weight).unwrap();
        let root = run.accepting[0].0;
        prop_assert_eq!(walker.sppf.span_lo(root), Some(lo as u32));
        prop_assert_eq!(walker.sppf.span_hi(root), Some(hi as u32));
        let result = walker.realize_root_complete_with_ranks(root, 1).unwrap();
        prop_assert_eq!(result.len(), 1);
        let actual = result[0].0.downcast_ref::<Value>().unwrap();
        prop_assert_eq!(actual, &Value { category: output, number: i64::from(rule) + 100 });
        prop_assert_eq!(result[0].1, mettail_grammar_core::ExactParseCost::try_from_f64(0.125).unwrap());
        walker.engine.fail = true;
        prop_assert_eq!(walker.realize_root_complete_with_ranks(root, 1).err(),
            Some(RealizationError::Action { rule_idx: u32::from(output) << 16,
                cause: ActionInvocationError::ResultCount { actual: 2 } }));
    }

    #[test]
    fn typed_unary_publication_replay_preserves_valid_siblings(
        input in 1u16..500, output in 501u16..1000,
        pop_first in any::<bool>(), duplicates in 1usize..4,
    ) {
        let mut walker = walker(input, output, 1);
        let valid = packing(&mut walker, input, 4, vec![], 0, 1);
        let invalid = packing(&mut walker, input + 1000, 4, vec![], 0, 1);
        let mut caller = descriptor(&mut walker, output, crate::sppf::SPPF_ID_NONE, 0, 0);
        caller.cur_sym = StackSymbolV2::category_entry(output);
        let mut run = CgllPureRun::default();
        let pushed = StackSymbolV2::return_symbol(output, 0);
        let descend = |walker: &mut Walker, run: &mut CgllPureRun, caller: &CgllPureDescriptor| {
            walker.try_cgll_pure_descend(run, caller, caller.cur_sym, pushed,
                WpdaState::Unwinding, 0, CgllFrameClass::D1, crate::sppf::SPPF_ID_NONE,
                0, CgllPrattHandoff::default()).unwrap();
        };
        descend(&mut walker, &mut run, &caller);
        let mut child = run.worklist.pop_front().unwrap();
        child.pos = 1;
        let mut second = caller.clone();
        second.u = walker.gss.get_or_create_node(WpdaGssNode {
            pos: 0, symbol: StackSymbolV2::category_entry(output + 1000),
        });
        run.v_slot.insert(second.u, second.ret_slot);
        if !pop_first { descend(&mut walker, &mut run, &second); run.worklist.clear(); }
        child.w = invalid;
        let before = snapshot(&walker, &run, child.u);
        for _ in 0..duplicates { reduce(&mut walker, &mut run, &child, &LexicographicWeight::one()).unwrap(); }
        prop_assert_eq!(snapshot(&walker, &run, child.u), before);
        child.w = valid;
        for _ in 0..duplicates { reduce(&mut walker, &mut run, &child, &LexicographicWeight::one()).unwrap(); }
        let resumed_before = run.worklist.len();
        prop_assert_eq!(resumed_before, if pop_first { 1 } else { 2 });
        if pop_first {
            descend(&mut walker, &mut run, &second);
            prop_assert_eq!(run.worklist.len(), resumed_before + 2);
            prop_assert_eq!(run.stats.replays, 1);
        }
        let pops = walker.gss.gll_recorded_pops(child.u);
        prop_assert_eq!(pops.len(), 1);
        child.w = invalid;
        let before = snapshot(&walker, &run, child.u);
        reduce(&mut walker, &mut run, &child, &LexicographicWeight::one()).unwrap();
        prop_assert_eq!(snapshot(&walker, &run, child.u), before);
        let replays = run.stats.replays;
        descend(&mut walker, &mut run, &second);
        prop_assert_eq!(run.stats.replays, replays);
    }

    #[test]
    fn typed_unary_publication_election_matches_typed_forest_without_invalid_demand(
        count in 1usize..18, alternatives in 2u16..7, reverse in any::<bool>(),
    ) {
        let mut observations = Vec::new();
        for repaired in [false, true] {
            let mut walker = walker(1, 2, 1);
            let mut leaf = 0;
            for rule in 4..4 + alternatives { leaf = packing(&mut walker, 0, rule, vec![], 0, 1); }
            let take = walker.sppf.intern_packing(Walker::OPTIONAL_PRESENT_RULE_IDX, vec![leaf], LexicographicWeight::one());
            let skip = walker.sppf.intern_opt_absent(0);
            let mut shared = 0;
            for child in if reverse { [skip, take] } else { [take, skip] } {
                shared = packing(&mut walker, 1, 2, vec![child], 0, 1);
            }
            let collection = walker.sppf.intern_collection_id(0, vec![shared; count]);
            let invalid = packing(&mut walker, 3, 3, vec![collection], 0, 1);
            let root = if repaired {
                let invalid_d = descriptor(&mut walker, 2, invalid, 0, 1);
                let mut run = CgllPureRun::default();
                reduce(&mut walker, &mut run, &invalid_d, &LexicographicWeight::one()).unwrap();
                prop_assert!(run.accepting.is_empty());
                prop_assert_eq!(walker.engine.calls.get(), 0);
                let valid_d = descriptor(&mut walker, 2, shared, 0, 1);
                reduce(&mut walker, &mut run, &valid_d, &LexicographicWeight::one()).unwrap();
                run.accepting[0].0
            } else {
                packing(&mut walker, 2, 0, vec![shared], 0, 1)
            };
            let mut state = KbestState::new();
            let mut depths = rustc_hash::FxHashMap::default();
            let outcome = walker.cgll_kbest_next(&mut state, &mut depths, root,
                KbestOrderKey::Election, 1, true, None);
            prop_assert!(!state.nodes.contains_key(&invalid));
            prop_assert!(!state.nodes.contains_key(&collection));
            let entry = &state.sub(root, KbestOrderKey::Election).unwrap().list[0];
            let KbestVal::Realized { arg: ActionArg::Term { value, .. }, w } = &entry.val else { panic!("typed result") };
            observations.push((format!("{outcome:?}"), value.downcast_ref::<Value>().unwrap().clone(),
                *w, entry.kt.as_ref().unwrap().lateness, entry.kt.as_ref().unwrap().weight,
                entry.kt.as_ref().unwrap().sorted_ordinals(), depths,
                (state.stats.pops, state.stats.infeasible_pops, state.stats.truncations, state.stats.root_empty), walker.engine.calls.get()));
        }
        prop_assert_eq!(&observations[0], &observations[1]);
    }
}
