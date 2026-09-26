//! TermCategoryObservation.v source correspondence: default lookup effects,
//! exact borrowed main-stack payload, and carrier category at both walker sites.

use super::*;
use crate::automata::lex_weight::LexicographicWeight;
use crate::automata::semiring::Semiring;
use crate::wpda_runtime::{ActionInvocationError, ActionSignature, FrameCtx};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Mutex;

#[derive(Default)]
struct StaticObserver {
    names: Mutex<Vec<String>>,
}

impl WpdaEngine<LexicographicWeight> for StaticObserver {
    fn step(
        &self,
        _: &WpdaState,
        _: &WpdaGss<LexicographicWeight>,
        _: Option<&WpdaGssNode>,
        _: usize,
        _: &dyn WpdaTokenSource,
        _: FrameCtx<'_>,
    ) -> WpdaStepAction<LexicographicWeight> {
        WpdaStepAction::Idle
    }

    fn cat_of_type_name(&self, name: &str) -> Option<u16> {
        let mut names = self
            .names
            .lock()
            .expect("lookup trace lock is not poisoned");
        names.push(name.to_owned());
        (name == "known").then_some(names.len() as u16)
    }
}

#[derive(Debug)]
struct IndexedTerm {
    category: u16,
}

struct CarrierObserver {
    category: u16,
    tag: &'static str,
    calls: AtomicUsize,
}

impl CarrierObserver {
    fn new(category: u16, tag: &'static str) -> Self {
        Self {
            category,
            tag,
            calls: AtomicUsize::new(0),
        }
    }
}

impl WpdaEngine<LexicographicWeight> for CarrierObserver {
    fn step(
        &self,
        _: &WpdaState,
        _: &WpdaGss<LexicographicWeight>,
        _: Option<&WpdaGssNode>,
        _: usize,
        _: &dyn WpdaTokenSource,
        _: FrameCtx<'_>,
    ) -> WpdaStepAction<LexicographicWeight> {
        WpdaStepAction::Idle
    }

    fn action_signature(&self, category: u16, rule: u16) -> Option<ActionSignature<'_>> {
        (category == 12 && rule == 0).then_some(ActionSignature {
            arity: 0,
            expected_input_cats: &[],
            output_cat: 12,
        })
    }

    fn execute_action(
        &self,
        category: u16,
        rule: u16,
        builder: &mut SemanticBuilder,
        args: Vec<ActionArg>,
    ) -> Result<(), ActionInvocationError> {
        assert!(self.action_signature(category, rule).is_some());
        assert!(args.is_empty());
        builder.push_raw_arg(ActionArg::Term {
            value: Arc::new(IndexedTerm { category: self.category }),
            type_name: self.tag,
        });
        Ok(())
    }

    fn cat_of_type_name(&self, _: &str) -> Option<u16> {
        panic!("explicit carriers must not infer categories from a type-name tag")
    }

    fn term_category(&self, value: &(dyn Any + Send + Sync), _: &str) -> Option<u16> {
        self.calls.fetch_add(1, Ordering::Relaxed);
        value
            .downcast_ref::<IndexedTerm>()
            .map(|term| term.category)
    }
}

fn observe<E: WpdaEngine<LexicographicWeight>>(
    engine: &E,
    builder: &SemanticBuilder,
) -> Option<u16> {
    builder
        .top_term()
        .and_then(|(value, tag)| engine.term_category(value, tag))
}

#[test]
fn term_category_static_default_preserves_lookup_results_and_state() {
    let original = StaticObserver::default();
    let adapted = StaticObserver::default();
    for (tag, expected) in [("known", Some(1)), ("unknown", None), ("known", Some(3))] {
        let mut builder = SemanticBuilder::new();
        builder.push_raw_arg(ActionArg::Term { value: Arc::new(17u32), type_name: tag });
        let old = builder
            .top_term_type_name()
            .and_then(|name| original.cat_of_type_name(name));
        assert_eq!(old, expected);
        assert_eq!(observe(&adapted, &builder), old);
        assert_eq!(
            *adapted.names.lock().expect("adapted lookup trace"),
            *original.names.lock().expect("original lookup trace"),
        );
        assert_eq!(builder.len(), 1);
    }
}

#[test]
fn term_category_borrows_exact_main_stack_top_without_cloning() {
    let mut builder = SemanticBuilder::new();
    builder.push_term(IndexedTerm { category: 1 });
    let payload: Arc<dyn Any + Send + Sync> = Arc::new(IndexedTerm { category: 9 });
    builder.push_raw_arg(ActionArg::Term {
        value: Arc::clone(&payload),
        type_name: "stored-tag",
    });
    let before = Arc::strong_count(&payload);
    let (borrowed, tag) = builder.top_term().expect("last main-stack term");
    assert!(std::ptr::eq(borrowed, payload.as_ref()));
    assert_eq!(tag, "stored-tag");
    assert_eq!(
        borrowed
            .downcast_ref::<IndexedTerm>()
            .expect("borrowed carrier")
            .category,
        9
    );
    assert_eq!(Arc::strong_count(&payload), before);
    assert_eq!(builder.len(), 2);

    builder.start_optional_scope();
    builder.push_term(IndexedTerm { category: 77 });
    let (borrowed, tag) = builder.top_term().expect("main stack, not optional scope");
    assert!(std::ptr::eq(borrowed, payload.as_ref()));
    assert_eq!(tag, "stored-tag");
    assert_eq!(builder.optional_stack_depth(), 1);
    assert_eq!(Arc::strong_count(&payload), before);
}

#[test]
fn term_category_empty_and_nonterm_top_skip_hook() {
    let engine = CarrierObserver::new(9, "ignored");
    let mut builder = SemanticBuilder::new();
    assert_eq!(observe(&engine, &builder), None);
    builder.push_term(IndexedTerm { category: 9 });
    builder.push_ident("top-is-not-a-term".into(), 0);
    assert_eq!(observe(&engine, &builder), None);
    assert_eq!(engine.calls.load(Ordering::Relaxed), 0);
    assert_eq!(builder.len(), 2);
}

#[test]
fn term_category_both_walker_sites_read_carrier_index_not_debug_tag() {
    for category in [7, 9] {
        for tag in ["same-rust-carrier", "misleading-other-category"] {
            let mut walker = WpdaWalker::new(CarrierObserver::new(category, tag), 0);
            let witness = walker
                .finish_packing_term_witness(
                    PackingWitnessContext {
                        action_context: Default::default(),
                        cat: 12,
                        local_rule_idx: 0,
                        arity: 0,
                        action_children: Vec::new(),
                        args: Vec::new(),
                    },
                    Vec::new(),
                )
                .expect("packing witness result");
            assert_eq!(witness.output_cat, Some(category));
            assert_eq!(
                witness
                    .value
                    .downcast_ref::<IndexedTerm>()
                    .expect("packing witness carrier")
                    .category,
                category
            );

            let cursor = BranchCursor::seed_from_live(
                crate::gss::GSS_NODE_NONE,
                0,
                LexicographicWeight::one(),
                WpdaState::Ready { min_bp: 0 },
            );
            let (value, output_cat, drains, children) = walker
                .fire_action_via_transient_prepared(
                    &cursor,
                    StackSymbolV2::return_symbol(12, 0),
                    Vec::new(),
                )
                .expect("transient result");
            assert_eq!(output_cat, Some(category));
            assert_eq!(
                value
                    .downcast_ref::<IndexedTerm>()
                    .expect("transient carrier")
                    .category,
                category,
            );
            assert_eq!(drains, 0);
            assert!(children.is_empty());
            assert_eq!(walker.engine.calls.load(Ordering::Relaxed), 2);
        }
    }
}

#[test]
fn term_category_unknown_payload_does_not_guess_from_known_tag() {
    let engine = CarrierObserver::new(9, "same-rust-carrier");
    let mut builder = SemanticBuilder::new();
    builder.push_raw_arg(ActionArg::Term {
        value: Arc::new(123u32),
        type_name: "same-rust-carrier",
    });
    assert_eq!(observe(&engine, &builder), None);
    assert_eq!(engine.calls.load(Ordering::Relaxed), 1);
    assert_eq!(
        builder
            .top_term()
            .expect("unrecognized term remains on the stack")
            .0
            .downcast_ref::<u32>(),
        Some(&123),
    );
}
