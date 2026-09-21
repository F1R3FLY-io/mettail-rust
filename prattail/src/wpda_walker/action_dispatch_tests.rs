use super::*;
use crate::automata::lex_weight::LexicographicWeight;
use crate::automata::semiring::Semiring;
use crate::wpda_runtime::{
    ActionArg, ActionEntry, ActionInvocationError, ActionSignature, SelectedCollection,
    SemanticBuilder, ANY_CAT,
};
use std::sync::atomic::{AtomicUsize, Ordering};

const INPUT_CATEGORY: u16 = 7;
const OUTPUT_CATEGORY: u16 = 3;
const LOCAL_RULE: u16 = 5;
const RULE: u32 = ((OUTPUT_CATEGORY as u32) << 16) | LOCAL_RULE as u32;

#[derive(Clone, Copy, Debug)]
enum Path {
    Eager,
    Selected,
    Witness,
    Transient,
}

const PATHS: [Path; 4] = [Path::Eager, Path::Selected, Path::Witness, Path::Transient];

#[derive(Clone, Copy)]
enum Behavior {
    Value,
    Reject,
    FailAfterValue,
    Drain,
    Undrained,
    RepeatedDrain,
}

struct OwnedEngine {
    categories: Vec<u16>,
    offset: i64,
    behavior: Behavior,
    calls: AtomicUsize,
}

impl OwnedEngine {
    fn new(offset: i64, behavior: Behavior) -> Self {
        Self {
            categories: vec![INPUT_CATEGORY],
            offset,
            behavior,
            calls: AtomicUsize::new(0),
        }
    }
}

impl WpdaEngine<LexicographicWeight> for OwnedEngine {
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

    fn action_signature(&self, category: u16, rule: u16) -> Option<ActionSignature<'_>> {
        (category == OUTPUT_CATEGORY && rule == LOCAL_RULE).then_some(ActionSignature {
            arity: 1,
            expected_input_cats: &self.categories,
            output_cat: OUTPUT_CATEGORY,
        })
    }

    fn execute_action(
        &self,
        category: u16,
        rule: u16,
        builder: &mut SemanticBuilder,
        args: Vec<ActionArg>,
    ) -> Result<(), ActionInvocationError> {
        if self.action_signature(category, rule).is_none() {
            return Err(ActionInvocationError::MissingAction { category, rule });
        }
        self.calls.fetch_add(1, Ordering::Relaxed);
        match self.behavior {
            Behavior::Reject => {},
            Behavior::FailAfterValue => {
                builder.push_term(self.offset);
                return Err(ActionInvocationError::ResultCount { actual: 2 });
            },
            Behavior::Undrained => builder.push_term(self.offset),
            Behavior::Drain | Behavior::RepeatedDrain => {
                let [ActionArg::CollectionId(id)] = args.as_slice() else {
                    panic!("the existing selected frame must assign a collection ID");
                };
                let items = builder.drain_collection(*id);
                let total = items
                    .into_iter()
                    .map(|item| item.try_into_term::<i64>().expect("selected i64"))
                    .sum::<i64>();
                if matches!(self.behavior, Behavior::RepeatedDrain) {
                    builder.drain_collection(*id);
                }
                builder.push_term(self.offset + total);
            },
            Behavior::Value => {
                let value = args
                    .into_iter()
                    .next()
                    .expect("one argument")
                    .try_into_term::<i64>()
                    .expect("input i64");
                builder.push_term(self.offset + value);
            },
        }
        Ok(())
    }

    fn cat_of_type_name(&self, name: &str) -> Option<u16> {
        (name == std::any::type_name::<i64>()).then_some(OUTPUT_CATEGORY)
    }
}

struct StaticEngine;

fn static_add(builder: &mut SemanticBuilder, args: Vec<ActionArg>) {
    let value = args
        .into_iter()
        .next()
        .expect("one argument")
        .try_into_term::<i64>()
        .expect("input i64");
    builder.push_term(40i64 + value);
}

static STATIC_ADD: ActionEntry = ActionEntry {
    action_fn: static_add,
    arity: 1,
    expected_input_cats: &[INPUT_CATEGORY],
    output_cat: OUTPUT_CATEGORY,
};

impl WpdaEngine<LexicographicWeight> for StaticEngine {
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

    fn action_for(&self, category: u16, rule: u16) -> Option<&ActionEntry> {
        (category == OUTPUT_CATEGORY && rule == LOCAL_RULE).then_some(&STATIC_ADD)
    }

    fn cat_of_type_name(&self, name: &str) -> Option<u16> {
        (name == std::any::type_name::<i64>()).then_some(OUTPUT_CATEGORY)
    }
}

fn term(value: i64) -> ActionArg {
    ActionArg::Term {
        value: Arc::new(value),
        type_name: std::any::type_name::<i64>(),
    }
}

fn run_path<E: WpdaEngine<LexicographicWeight>>(
    walker: &mut WpdaWalker<LexicographicWeight, E>,
    path: Path,
    local_rule: u16,
) -> Option<i64> {
    let rule = ((OUTPUT_CATEGORY as u32) << 16) | u32::from(local_rule);
    let child = walker.sppf.intern_symbol(u32::from(INPUT_CATEGORY), 0, 1);
    let weight = LexicographicWeight::from_cost(0.5, OUTPUT_CATEGORY, local_rule);
    let packing = walker.sppf.intern_packing(rule, vec![child], weight);
    match path {
        Path::Eager => {
            let memo = std::collections::HashMap::from([(
                child,
                vec![(term(2), LexicographicWeight::one())],
            )]);
            let results = walker.realize_packing_call(packing, rule, &[child], weight, &memo, None);
            assert!(results.len() <= 1);
            results.into_iter().next().map(|(arg, actual)| {
                assert_eq!(actual, weight);
                arg.try_into_term::<i64>().expect("eager result")
            })
        },
        Path::Selected => walker
            .cgll_apply_selected_action(packing, rule, vec![term(2)], weight)
            .map(|(arg, actual)| {
                assert_eq!(actual, weight);
                arg.try_into_term::<i64>().expect("selected result")
            }),
        Path::Witness => walker
            .finish_packing_term_witness(
                PackingWitnessContext {
                    cat: OUTPUT_CATEGORY,
                    local_rule_idx: local_rule,
                    arity: 1,
                    action_children: vec![child],
                    args: vec![term(2)],
                },
                Vec::new(),
            )
            .map(|result| {
                assert_eq!(result.output_cat, Some(OUTPUT_CATEGORY));
                *Arc::downcast::<i64>(result.value).expect("witness result")
            }),
        Path::Transient => {
            walker.sppf_symbol_terms.insert(
                child,
                SppfSymbolTerm {
                    value: Arc::new(2i64),
                    output_cat: Some(INPUT_CATEGORY),
                },
            );
            let cursor = BranchCursor::seed_from_live(
                crate::gss::GSS_NODE_NONE,
                0,
                LexicographicWeight::one(),
                WpdaState::Ready { min_bp: 0 },
            );
            walker
                .fire_action_via_transient_prepared(
                    &cursor,
                    StackSymbolV2::return_symbol(OUTPUT_CATEGORY, local_rule),
                    vec![child],
                )
                .map(|(value, category, drains, children)| {
                    assert_eq!(category, Some(OUTPUT_CATEGORY));
                    assert_eq!(drains, 0);
                    assert_eq!(children, vec![child]);
                    *Arc::downcast::<i64>(value).expect("transient result")
                })
        },
    }
}

#[test]
fn action_dispatch_owned_signature_borrows_instance_storage_without_static_entry() {
    let engine = OwnedEngine::new(40, Behavior::Value);
    assert!(engine.action_for(OUTPUT_CATEGORY, LOCAL_RULE).is_none());
    let signature = engine
        .action_signature(OUTPUT_CATEGORY, LOCAL_RULE)
        .expect("owned signature");
    assert_eq!(signature.arity, 1);
    assert_eq!(signature.output_cat, OUTPUT_CATEGORY);
    assert_eq!(signature.expected_input_cats, &[INPUT_CATEGORY]);
    assert_eq!(signature.expected_input_cats.as_ptr(), engine.categories.as_ptr());
}

#[test]
fn action_dispatch_static_default_and_owned_context_agree_on_all_four_paths() {
    for path in PATHS {
        let mut static_walker = WpdaWalker::new(StaticEngine, 0);
        let mut owned = WpdaWalker::new(OwnedEngine::new(40, Behavior::Value), 0);
        assert_eq!(run_path(&mut static_walker, path, LOCAL_RULE), Some(42), "{path:?}");
        assert_eq!(run_path(&mut owned, path, LOCAL_RULE), Some(42), "{path:?}");
        assert_eq!(owned.engine.calls.load(Ordering::Relaxed), 1, "{path:?}");
        assert!(!owned.realization_failed(), "{path:?}");
    }
}

#[test]
fn action_dispatch_distinct_owned_contexts_do_not_share_dispatch_state() {
    for path in PATHS {
        let mut first = WpdaWalker::new(OwnedEngine::new(10, Behavior::Value), 0);
        let mut second = WpdaWalker::new(OwnedEngine::new(90, Behavior::Value), 0);
        assert_eq!(run_path(&mut first, path, LOCAL_RULE), Some(12), "{path:?}");
        assert_eq!(run_path(&mut second, path, LOCAL_RULE), Some(92), "{path:?}");
    }
}

#[test]
fn action_dispatch_callback_error_withholds_already_pushed_value_on_all_paths() {
    for path in PATHS {
        let mut walker = WpdaWalker::new(OwnedEngine::new(99, Behavior::FailAfterValue), 0);
        assert_eq!(run_path(&mut walker, path, LOCAL_RULE), None, "{path:?}");
        assert_eq!(walker.engine.calls.load(Ordering::Relaxed), 1, "{path:?}");
        assert!(walker.realization_failed(), "{path:?}");
    }
}

#[test]
fn action_dispatch_partial_refusal_does_not_become_callback_failure() {
    for path in PATHS {
        let mut walker = WpdaWalker::new(OwnedEngine::new(99, Behavior::Reject), 0);
        assert_eq!(run_path(&mut walker, path, LOCAL_RULE), None, "{path:?}");
        assert_eq!(walker.engine.calls.load(Ordering::Relaxed), 1, "{path:?}");
        assert!(!walker.realization_failed(), "{path:?}");
    }
}

#[test]
fn action_dispatch_missing_action_never_invokes_or_publishes() {
    for path in PATHS {
        let mut walker = WpdaWalker::new(OwnedEngine::new(99, Behavior::Value), 0);
        assert_eq!(run_path(&mut walker, path, LOCAL_RULE + 1), None, "{path:?}");
        assert_eq!(walker.engine.calls.load(Ordering::Relaxed), 0, "{path:?}");
    }
    let mut builder = SemanticBuilder::new();
    assert_eq!(
        StaticEngine.execute_action(OUTPUT_CATEGORY, LOCAL_RULE + 1, &mut builder, vec![term(2)]),
        Err(ActionInvocationError::MissingAction {
            category: OUTPUT_CATEGORY,
            rule: LOCAL_RULE + 1
        }),
    );
    assert_eq!(builder.len(), 0);
}

fn selected_collection() -> ActionArg {
    ActionArg::SelectedCollection(
        SelectedCollection::new(vec![term(1), term(2)]).expect("closed selected collection"),
    )
}

#[test]
fn action_dispatch_owned_callback_retains_selected_collection_frame() {
    let mut engine = OwnedEngine::new(40, Behavior::Drain);
    engine.categories[0] = ANY_CAT;
    let mut walker = WpdaWalker::new(engine, 0);
    let weight = LexicographicWeight::one();
    let packing = walker.sppf.intern_packing(RULE, Vec::new(), weight);
    let result = walker
        .cgll_apply_selected_action(packing, RULE, vec![selected_collection()], weight)
        .expect("owned callback must drain the existing selected frame");
    assert_eq!(result.0.try_into_term::<i64>().expect("collection result"), 43);
    assert_eq!(walker.engine.calls.load(Ordering::Relaxed), 1);
    assert!(!walker.realization_failed());
}

#[test]
fn action_dispatch_selected_collection_refusal_and_protocol_failure_remain_distinct() {
    for (behavior, fails) in [
        (Behavior::Reject, false),
        (Behavior::Undrained, true),
        (Behavior::RepeatedDrain, true),
    ] {
        let mut engine = OwnedEngine::new(40, behavior);
        engine.categories[0] = ANY_CAT;
        let mut walker = WpdaWalker::new(engine, 0);
        let weight = LexicographicWeight::one();
        let packing = walker.sppf.intern_packing(RULE, Vec::new(), weight);
        let result =
            walker.cgll_apply_selected_action(packing, RULE, vec![selected_collection()], weight);
        assert!(result.is_none());
        assert_eq!(walker.realization_failed(), fails);
        assert_eq!(walker.engine.calls.load(Ordering::Relaxed), 1);
    }
}

#[test]
fn action_dispatch_selected_arity_rejection_precedes_owned_callback() {
    let mut walker = WpdaWalker::new(OwnedEngine::new(40, Behavior::Value), 0);
    let weight = LexicographicWeight::one();
    let packing = walker.sppf.intern_packing(RULE, Vec::new(), weight);
    assert!(walker
        .cgll_apply_selected_action(packing, RULE, Vec::new(), weight)
        .is_none());
    assert_eq!(walker.engine.calls.load(Ordering::Relaxed), 0);
    assert!(!walker.realization_failed());
}
