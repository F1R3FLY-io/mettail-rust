//! Exact numeric-boundary witnesses for the original shared binder workers.
//! Fixture constructors and normal-domain goldens remain in the parent module.

use super::super::MacroBinderSyntaxReader;
use super::*;
use mettail_prattail::wpda_rule_analysis::binder::optional::{
    classify_optional_body, try_classify_optional_body,
};
use mettail_prattail::wpda_rule_analysis::binder::rule::try_classify_binder_in;
use mettail_prattail::wpda_rule_analysis::binder::{BinderNumericError, ParamKind};
use std::cell::{Cell, RefCell};
use std::collections::HashMap;

fn checked_rule(
    fixture: &GrammarRule,
    kv_calls: &Cell<usize>,
) -> Result<Option<BinderShape>, BinderNumericError> {
    try_classify_binder_in(
        &MacroBinderSyntaxReader,
        fixture,
        || (),
        |_| Vec::new(),
        |_, ()| {
            kv_calls.set(kv_calls.get() + 1);
            None
        },
    )
}

fn assert_numeric_error<T>(
    result: Result<Option<T>, BinderNumericError>,
    expected: BinderNumericError,
) {
    match result {
        Err(actual) => assert_eq!(actual, expected),
        Ok(_) => panic!("expected numeric refusal {expected:?}"),
    }
}

fn plain_syntax(count: usize) -> Vec<SyntaxExpr> {
    let mut syntax = Vec::with_capacity(1 + 2 * count);
    syntax.push(literal("start"));
    for _ in 0..count {
        syntax.push(sep("names"));
        syntax.push(literal("]"));
    }
    syntax
}

fn collection_rule(syntax: Vec<SyntaxExpr>) -> GrammarRule {
    rule(vec![simple("names", collection(CollectionType::Vec, "Name"))], syntax)
}

#[test]
fn numeric_main_plain_slot_boundary_preserves_callback_before_refusal() {
    for count in [255, 256] {
        let fixture = collection_rule(plain_syntax(count));
        let calls = Cell::new(0);
        let result = checked_rule(&fixture, &calls);
        assert_eq!(calls.get(), count, "main kv callback precedes the increment");
        if count == 255 {
            let actual = result
                .expect("255 slot assignments fit")
                .expect("collection binder");
            assert_eq!(actual.action_arity, 255);
            assert_eq!(actual.action_args.len(), 255);
            assert_eq!(actual.positions.len(), 255);
            for (index, position) in actual.positions.iter().enumerate() {
                let BinderPosition::ParamParse { collection: Some(info), .. } = position else {
                    panic!("each separator creates one collection position")
                };
                assert_eq!(usize::from(info.slot_idx), index);
            }
            let original = classify_binder_in(&fixture, &language()).expect("legacy normal domain");
            assert_eq!(format!("{actual:?}"), format!("{original:?}"));
        } else {
            assert_numeric_error(result, BinderNumericError::MainPlainSlot);
        }
    }
}

#[test]
fn numeric_mapped_slot_checks_only_after_original_body_validation() {
    for (body, accepted_body) in [
        (vec![param("x"), param("n")], true),
        (vec![param("n")], false),
        (vec![param("unknown")], false),
    ] {
        let mut syntax = plain_syntax(255);
        syntax.push(mapped_sep("names", "xs", &["n", "x"], body));
        syntax.push(literal(")"));
        let fixture = rule(
            vec![
                simple("names", collection(CollectionType::Vec, "Name")),
                abstraction(true, "xs", "body", "Expr"),
            ],
            syntax,
        );
        let calls = Cell::new(0);
        let result = checked_rule(&fixture, &calls);
        assert_eq!(calls.get(), 255, "mapped collection makes no extra kv call");
        if accepted_body {
            assert_numeric_error(result, BinderNumericError::MainMappedSlot);
        } else {
            assert!(result
                .expect("invalid body refuses before its numeric checkpoint")
                .is_none());
        }
    }
}

#[test]
fn numeric_final_arity_counts_leading_capture_without_truncation() {
    for leading_capture in [false, true] {
        for count in [255, 256] {
            let terms = count - usize::from(leading_capture);
            let mut syntax = Vec::with_capacity(1 + terms);
            syntax.push(if leading_capture {
                token(Some("leading"))
            } else {
                literal("start")
            });
            syntax.extend((0..terms).map(|_| param("value")));
            let fixture = rule(vec![simple("value", base("Expr"))], syntax);
            let calls = Cell::new(0);
            let result = checked_rule(&fixture, &calls);
            assert_eq!(calls.get(), 0, "no collection counter participates in this boundary");
            if count == 255 {
                let actual = result
                    .expect("inclusive u8 boundary")
                    .expect("parameter binder");
                assert_eq!(actual.action_arity, 255);
                assert_eq!(actual.action_args.len(), count);
                if leading_capture {
                    assert!(matches!(actual.action_args.first(), Some(ActionArgKind::TokenText {
                        param_name,
                    }) if param_name == "leading"));
                }
                let original =
                    classify_binder_in(&fixture, &language()).expect("legacy normal domain");
                assert_eq!(format!("{actual:?}"), format!("{original:?}"));
            } else {
                assert_numeric_error(result, BinderNumericError::FinalActionArity);
            }
        }
    }
}

fn optional_params(kind: ParamKind) -> HashMap<String, ParamKind> {
    HashMap::from([("names".into(), kind)])
}

fn checked_optional(
    syntax: &[SyntaxExpr],
    params: &HashMap<String, ParamKind>,
    group: &mut u32,
    slot: &mut u8,
    trace: &RefCell<Vec<&'static str>>,
) -> Result<Option<(Vec<BinderPosition>, Vec<ActionArgKind>)>, BinderNumericError> {
    try_classify_optional_body(
        &MacroBinderSyntaxReader,
        syntax,
        params,
        group,
        slot,
        |_| {
            trace.borrow_mut().push("guest");
            Vec::new()
        },
        |_| {
            trace.borrow_mut().push("kv");
            None
        },
    )
}

#[test]
fn numeric_optional_slot_refusal_preserves_counter_and_suppresses_callback() {
    let params = optional_params(ParamKind::SimpleCollection {
        elem_cat: "Name".into(),
        coll_kind: CollectionType::Vec,
    });
    let syntax = [sep("names"), literal("]")];
    let trace = RefCell::new(Vec::new());
    let (mut group, mut slot) = (7, u8::MAX);
    assert_numeric_error(
        checked_optional(&syntax, &params, &mut group, &mut slot, &trace),
        BinderNumericError::OptionalSlot,
    );
    assert_eq!((group, slot), (7, u8::MAX));
    assert!(trace.borrow().is_empty());
    assert!(
        classify_optional_body(
            &MacroBinderSyntaxReader,
            &syntax,
            &params,
            &mut group,
            &mut slot,
            |_| panic!("overflow must not reach guest callback"),
            |_| panic!("overflow must not reach kv callback"),
        )
        .is_none(),
        "legacy checked-overflow compatibility"
    );
    assert_eq!((group, slot), (7, u8::MAX));

    slot = 254;
    let two_slots = [sep("names"), literal("]"), sep("names"), literal("]")];
    assert_numeric_error(
        checked_optional(&two_slots, &params, &mut group, &mut slot, &trace),
        BinderNumericError::OptionalSlot,
    );
    assert_eq!((group, slot), (7, 255));
    assert_eq!(*trace.borrow(), ["kv"], "the successful prefix is not rolled back");

    trace.borrow_mut().clear();
    let binder_params = optional_params(ParamKind::BinderList);
    let (positions, args) =
        checked_optional(&syntax, &binder_params, &mut group, &mut slot, &trace)
            .expect("binder list does not allocate a collection slot")
            .expect("binder list separator");
    assert_eq!((group, slot), (7, 255));
    assert!(trace.borrow().is_empty());
    assert!(matches!(
        positions.as_slice(),
        [BinderPosition::BinderListLoop { slot_idx: 0, .. }]
    ));
    assert!(matches!(args.as_slice(), [ActionArgKind::BinderList]));
}

#[test]
fn numeric_optional_group_refusal_retains_prior_guest_and_group_effects() {
    let params = HashMap::new();
    let child = || SyntaxExpr::Op(PatternOp::Opt { inner: vec![guest()] });
    let trace = RefCell::new(Vec::new());
    let (mut group, mut slot) = (u32::MAX, 23);
    assert_numeric_error(
        checked_optional(&[child()], &params, &mut group, &mut slot, &trace),
        BinderNumericError::OptionalGroup,
    );
    assert_eq!((group, slot), (u32::MAX, 23));
    assert!(trace.borrow().is_empty());
    assert!(
        classify_optional_body(
            &MacroBinderSyntaxReader,
            &[child()],
            &params,
            &mut group,
            &mut slot,
            |_| panic!("group overflow must not enter its child"),
            |_| panic!("group overflow must not enter its child"),
        )
        .is_none(),
        "legacy group-overflow compatibility"
    );
    group = u32::MAX - 1;
    assert_numeric_error(
        checked_optional(&[child(), child()], &params, &mut group, &mut slot, &trace),
        BinderNumericError::OptionalGroup,
    );
    assert_eq!((group, slot), (u32::MAX, 23));
    assert_eq!(*trace.borrow(), ["guest"]);
}

#[test]
fn numeric_main_propagates_optional_error_with_shared_slot_counter() {
    let mut syntax = plain_syntax(255);
    syntax.push(SyntaxExpr::Op(PatternOp::Opt { inner: vec![sep("names"), literal("]")] }));
    let fixture = collection_rule(syntax);
    let calls = Cell::new(0);
    assert_numeric_error(checked_rule(&fixture, &calls), BinderNumericError::OptionalSlot);
    assert_eq!(calls.get(), 255, "optional failure suppresses its kv callback");
    assert!(
        classify_binder_in(&fixture, &language()).is_none(),
        "legacy optional compatibility"
    );

    let mut syntax = plain_syntax(254);
    syntax.push(SyntaxExpr::Op(PatternOp::Opt { inner: vec![sep("names"), literal("]")] }));
    syntax.extend([sep("names"), literal("]")]);
    let fixture = collection_rule(syntax);
    calls.set(0);
    assert_numeric_error(checked_rule(&fixture, &calls), BinderNumericError::MainPlainSlot);
    assert_eq!(calls.get(), 256, "main resumes the counter advanced inside optional");
}
