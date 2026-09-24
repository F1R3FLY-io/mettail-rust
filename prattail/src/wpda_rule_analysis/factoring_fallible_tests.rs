use super::*;
use std::cell::RefCell;

fn observe(
    trace: &RefCell<Vec<&'static str>>,
    fail: usize,
    name: &'static str,
) -> Result<(), usize> {
    let mut trace = trace.borrow_mut();
    let ordinal = trace.len();
    trace.push(name);
    if ordinal == fail {
        Err(ordinal)
    } else {
        Ok(())
    }
}

fn binder() -> BinderShape {
    BinderShape {
        label: "Rule".into(),
        result_cat: "Term".into(),
        leading_category: None,
        leading_ident_capture: None,
        positions: vec![BinderPosition::Literal("end".into())],
        is_multi: false,
        has_binder: false,
        action_arity: 0,
        action_args: vec![],
        body_cat: None,
        param_cats: vec![],
    }
}

#[test]
fn discovery_stops_at_each_original_callback() {
    let expected = ["atomic", "binder", "leading", "atomic", "binder", "leading"];
    for fail in 0..=expected.len() {
        let trace = RefCell::new(Vec::new());
        let result: Result<_, usize> = try_discover_prefix_members_with(
            &["Term".into()],
            0,
            &["first", "second"],
            &Default::default(),
            |_| {
                observe(&trace, fail, "atomic")?;
                Ok(PrefixAtomicObservation::Other)
            },
            |_| {
                observe(&trace, fail, "binder")?;
                Ok(Some(binder()))
            },
            |rule| {
                observe(&trace, fail, "leading")?;
                Ok(Some(*rule))
            },
        );
        assert_eq!(*trace.borrow(), expected[..expected.len().min(fail + 1)]);
        if fail < expected.len() {
            assert_eq!(result.expect_err("injected discovery failure must propagate"), fail);
        } else {
            let baseline = discover_prefix_members_with(
                &["Term".into()],
                0,
                &["first", "second"],
                &Default::default(),
                |_| PrefixAtomicObservation::Other,
                |_| Some(binder()),
                |rule| Some(*rule),
            );
            assert_eq!(
                format!("{:?}", result.expect("all discovery callbacks succeeded")),
                format!("{baseline:?}")
            );
        }
    }
    let result = try_discover_prefix_members_with(
        &["Term".into()],
        0,
        &[()],
        &Default::default(),
        |_| {
            Ok::<_, ()>(PrefixAtomicObservation::NullaryLiteralRun {
                trigger: "literal".into(),
                trailing_literals: vec![],
            })
        },
        |_| panic!("nullary must bypass binder"),
        |_| panic!("nullary must bypass leading literal"),
    )
    .expect("nullary discovery needs no later callbacks");
    assert_eq!(result.len(), 1);
}

fn member(rule_idx: u16) -> (String, CandidateMember) {
    (
        "trigger".into(),
        CandidateMember {
            kind: MemberKind::Nullary,
            rule_idx,
            items: vec![],
            truncated: false,
            total_positions: 0,
            body_src_idx: None,
            mixfix_coords: vec![],
        },
    )
}

#[test]
fn enabled_and_disabled_factoring_preserve_callback_prefixes() {
    let per_cat = [vec![0, 1], vec![]];
    let expected = ["discover", "cast", "cast", "discover"];
    for fail in 0..=expected.len() {
        let trace = RefCell::new(Vec::new());
        let result: Result<_, usize> = try_build_prefix_factoring_with(
            &per_cat,
            false,
            0xfe00,
            |_, rules| {
                observe(&trace, fail, "discover")?;
                Ok(rules.iter().map(|r| member(*r)).collect())
            },
            |_| {
                observe(&trace, fail, "cast")?;
                Ok(false)
            },
        );
        assert_eq!(*trace.borrow(), expected[..expected.len().min(fail + 1)]);
        if fail < expected.len() {
            assert_eq!(result.expect_err("injected factoring failure must propagate"), fail);
        } else {
            let baseline = build_prefix_factoring_with(
                &per_cat,
                false,
                0xfe00,
                |_, rules| rules.iter().map(|r| member(*r)).collect(),
                |_| false,
            );
            assert_eq!(
                format!("{:?}", result.expect("all factoring callbacks succeeded")),
                format!("{baseline:?}")
            );
        }
    }
    for fail in 0..=2 {
        let trace = RefCell::new(Vec::new());
        let result: Result<_, usize> = try_prefix_identity_partition(&per_cat, |_, rules| {
            observe(&trace, fail, "discover")?;
            Ok(rules.iter().map(|r| member(*r)).collect())
        });
        assert_eq!(*trace.borrow(), vec!["discover"; 2.min(fail + 1)]);
        if fail < 2 {
            assert_eq!(
                result.expect_err("injected identity discovery failure must propagate"),
                fail
            );
        } else {
            let baseline = prefix_identity_partition(&per_cat, |_, rules| {
                rules.iter().map(|r| member(*r)).collect()
            });
            assert_eq!(
                format!("{:?}", result.expect("all identity discovery callbacks succeeded")),
                format!("{baseline:?}")
            );
        }
    }
}

#[test]
fn mixfix_cast_failure_is_not_a_resolver_refusal() {
    use super::super::mixfix::{
        build_mixfix_factoring_with, try_build_mixfix_factoring_with, GroupedOp,
    };
    use crate::binding_power::{InfixOperator, MixfixPart};
    let op = InfixOperator {
        terminal: "!".into(),
        category: "Term".into(),
        result_category: "Term".into(),
        left_bp: 1,
        right_bp: 2,
        label: "Rule".into(),
        is_cross_category: false,
        is_postfix: false,
        is_mixfix: true,
        mixfix_parts: vec![MixfixPart {
            operand_category: "Term".into(),
            param_name: "x".into(),
            preceding_terminals: vec![],
            following_terminals: vec![],
            repetition: None,
            capture_kind: None,
        }],
        nullary_literals: vec![],
    };
    let categories = ["Term".into()];
    let per_cat = [vec![()]];
    let grouped =
        [((0, "!".into()), vec![GroupedOp { op: &op, result_src_idx: 0, rule_idx: 0 }])].into();
    let trace = RefCell::new(Vec::new());
    let result = try_build_mixfix_factoring_with(
        &categories,
        &per_cat,
        &[],
        &grouped,
        16,
        0xfe00,
        |_, _, _, _| {
            trace.borrow_mut().push("resolve");
            Ok::<_, ()>(0)
        },
        |_| {
            trace.borrow_mut().push("cast");
            Err::<bool, _>("cast unavailable")
        },
    );
    assert_eq!(result.expect_err("cast observation failure must propagate"), "cast unavailable");
    assert_eq!(*trace.borrow(), ["resolve", "resolve", "cast"]);
    let refused: Result<_, ()> = try_build_mixfix_factoring_with(
        &categories,
        &per_cat,
        &[],
        &grouped,
        16,
        0xfe00,
        |_, _, _, _| Err::<u16, _>("unresolved"),
        |_| panic!("unresolved candidate must never consult cast machinery"),
    );
    assert!(refused.is_ok());
    let successful = try_build_mixfix_factoring_with(
        &categories,
        &per_cat,
        &[],
        &grouped,
        16,
        0xfe00,
        |_, _, _, _| Ok::<_, ()>(0),
        |_| Ok::<_, ()>(false),
    )
    .expect("all mixfix callbacks succeeded");
    let baseline = build_mixfix_factoring_with(
        &categories,
        &per_cat,
        &[],
        &grouped,
        16,
        0xfe00,
        |_, _, _, _| Ok::<_, ()>(0),
        |_| false,
    );
    assert_eq!(format!("{successful:?}"), format!("{baseline:?}"));
}
