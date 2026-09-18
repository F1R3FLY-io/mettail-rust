use super::*;
use mettail_rholang_codegen::DynamicReflectionError;
use prost::Message;
use std::sync::Arc;

fn refused() -> RholangAstLowerError {
    RholangAstLowerError::Preparation(DynamicReflectionError::Cancelled)
}

fn two_processes() -> Vec<DdlModuleItem> {
    vec![
        DdlModuleItem::DdlModuleProcItem(Arc::new(Proc::PZero)),
        DdlModuleItem::DdlModuleProcItem(Arc::new(Proc::PZero)),
    ]
}

fn root(items: &[DdlModuleItem]) -> DdlRoot<'_> {
    DdlRoot::Module { name: "Demo", imports: None, items }
}

fn node(tag: &str, mut children: Vec<Par>) -> Par {
    children.insert(0, string_par(tag.to_owned()));
    new_elist_par(children, Vec::new(), false, None, Vec::new(), false)
}

fn process_values() -> Vec<Par> {
    vec![new_gstring_par("first".into(), vec![0, 1], true), string_par("second".into())]
}

#[test]
fn paid_plan_preserves_exact_postorder_process_identity_and_closed_wire_metadata() {
    let items = two_processes();
    let plan = DdlLowerPlan::try_build(root(&items), &mut |_, _| Ok(())).expect("paid plan");
    let signature = plan
        .operations
        .iter()
        .map(|op| match op {
            WireOp::Text(text) => format!("text:{text}"),
            WireOp::QuotedText(text) => format!("quoted:{text}"),
            WireOp::Process(index) => format!("process:{index}"),
            WireOp::Node { tag, child_count } => format!("{tag}:{child_count}"),
        })
        .collect::<Vec<_>>();
    assert_eq!(
        signature,
        [
            "text:Demo",
            "sequence:0",
            "process:0",
            "module-program:1",
            "process:1",
            "module-program:1",
            "sequence:2",
            "module:3",
            "mettail-ddl-ast/2:1"
        ]
    );
    for (index, process) in plan.process_jobs().enumerate() {
        let DdlModuleItem::DdlModuleProcItem(expected) = &items[index] else {
            unreachable!()
        };
        assert!(std::ptr::eq(process, expected.as_ref()));
    }
    let values = process_values();
    let expected = node(
        DDL_AST_ENVELOPE_V2,
        vec![node(
            "module",
            vec![
                string_par("Demo".into()),
                node("sequence", vec![]),
                node(
                    "sequence",
                    vec![
                        node("module-program", vec![values[0].clone()]),
                        node("module-program", vec![values[1].clone()]),
                    ],
                ),
            ],
        )],
    );
    let actual = plan
        .try_finish(values, &mut |_, _| Ok(()))
        .expect("paid wire");
    assert_eq!(actual.encode_to_vec(), expected.encode_to_vec());
    assert!(
        actual.locally_free.is_empty() && !actual.connective_used,
        "DDL envelope stays closed even when an embedded process carries metadata"
    );
}

#[test]
fn every_build_and_finish_cut_refuses_without_a_partial_result_or_budget_reset() {
    let items = two_processes();
    let mut trace = Vec::new();
    let plan = DdlLowerPlan::try_build(root(&items), &mut |w, u| {
        trace.push((w, u));
        Ok(())
    })
    .expect("baseline plan");
    plan.try_finish(process_values(), &mut |w, u| {
        trace.push((w, u));
        Ok(())
    })
    .expect("baseline wire");
    for cut in 0..trace.len() {
        let mut seen = Vec::new();
        let mut reserve = |w, u| {
            let at = seen.len();
            seen.push((w, u));
            if at == cut {
                Err(refused())
            } else {
                Ok(())
            }
        };
        let result = DdlLowerPlan::try_build(root(&items), &mut reserve)
            .and_then(|plan| plan.try_finish(process_values(), &mut reserve));
        assert_eq!(result.err(), Some(refused()));
        assert_eq!(seen, trace[..=cut]);
    }
    let total = trace
        .iter()
        .fold((0usize, 0usize), |(w, u), (x, y)| (w + x, u + y));
    for (work_limit, unit_limit, success) in [
        (total.0, total.1, true),
        (total.0 - 1, total.1, false),
        (total.0, total.1 - 1, false),
        (0, total.1, false),
    ] {
        let mut used = (0, 0);
        let mut reserve = |w, u| {
            if w > work_limit - used.0 || u > unit_limit - used.1 {
                return Err(refused());
            }
            used.0 += w;
            used.1 += u;
            Ok(())
        };
        let result = DdlLowerPlan::try_build(root(&items), &mut reserve)
            .and_then(|plan| plan.try_finish(process_values(), &mut reserve));
        assert_eq!(result.is_ok(), success);
        assert!(used.0 <= work_limit && used.1 <= unit_limit);
    }
}

#[test]
fn finishing_rejects_arity_underflow_repeated_missing_and_unused_process_slots() {
    let zero = Proc::PZero;
    for (operations, processes, values) in [
        (vec![WireOp::Process(0)], vec![&zero], vec![]),
        (vec![WireOp::Node { tag: "broken", child_count: 1 }], vec![], vec![]),
        (vec![WireOp::Process(0), WireOp::Process(0)], vec![&zero], vec![Par::default()]),
        (vec![WireOp::Process(1)], vec![&zero], vec![Par::default()]),
        (vec![WireOp::Text("unused")], vec![&zero], vec![Par::default()]),
        (vec![], vec![], vec![]),
    ] {
        let plan = DdlLowerPlan { operations, processes };
        assert!(matches!(
            plan.try_finish(values, &mut |_, _| Ok(())),
            Err(RholangAstLowerError::DdlWire(_))
        ));
    }
}

#[test]
fn captured_strings_decode_once_and_malformed_projection_stays_an_error() {
    for raw in [r#""a\\\"b\\\\c""#, r#""λ\n\t\x""#] {
        let plan = DdlLowerPlan {
            operations: vec![WireOp::QuotedText(raw)],
            processes: vec![],
        };
        let actual = plan
            .try_finish(vec![], &mut |_, _| Ok(()))
            .expect("quoted text");
        let expected = string_par(decode_captured_string(raw).expect("existing decoder"));
        assert_eq!(actual.encode_to_vec(), expected.encode_to_vec());
    }
    for raw in ["not-quoted", "\"a\"b\"", "\"tail\\\""] {
        let plan = DdlLowerPlan {
            operations: vec![WireOp::QuotedText(raw)],
            processes: vec![],
        };
        assert!(matches!(
            plan.try_finish(vec![], &mut |_, _| Ok(())),
            Err(RholangAstLowerError::DdlWire(_))
        ));
    }
}

#[test]
fn overflow_is_checked_before_a_roster_or_canonical_list_is_allocated() {
    let mut calls = 0;
    let mut reserve = |_, _| {
        calls += 1;
        Ok(())
    };
    assert_eq!(
        admission::rosters(usize::MAX, 1, &mut reserve),
        Err(RholangAstLowerError::PreparationSizeOverflow)
    );
    assert_eq!(
        admission::node(usize::MAX, 1, &mut reserve),
        Err(RholangAstLowerError::PreparationSizeOverflow)
    );
    assert_eq!(
        admission::text(usize::MAX, true, &mut reserve),
        Err(RholangAstLowerError::PreparationSizeOverflow)
    );
    assert_eq!(calls, 0);
}

#[test]
fn deep_ddl_plans_use_the_existing_heap_worklist_and_leave_data_to_the_host() {
    std::thread::Builder::new()
        .stack_size(128 * 1024)
        .spawn(|| {
            let mut body = DdlTheoryExpr::DdlTheoryEmpty;
            for _ in 0..4096 {
                body = DdlTheoryExpr::DdlTheoryJoin(
                    Arc::new(body),
                    Arc::new(DdlTheoryExpr::DdlTheoryEmpty),
                );
            }
            let plan = DdlLowerPlan::try_build(
                DdlRoot::Theory {
                    name: "Deep",
                    parameters: &[],
                    body: &body,
                },
                &mut |_, _| Ok(()),
            )
            .expect("deep plan");
            assert_eq!(plan.process_jobs().len(), 0);
            let value = plan
                .try_finish(vec![], &mut |_, _| Ok(()))
                .expect("deep canonical value");
            assert_eq!(value.exprs.len(), 1);
            drop(value);
            let nested =
                Proc::DdlTheory("Inner".into(), vec![], Arc::new(DdlTheoryExpr::DdlTheoryEmpty));
            let body = DdlTheoryExpr::DdlTheoryDataImplicit(Arc::new(nested));
            let plan = DdlLowerPlan::try_build(
                DdlRoot::Theory {
                    name: "Outer",
                    parameters: &[],
                    body: &body,
                },
                &mut |_, _| Ok(()),
            )
            .expect("outer plan");
            let jobs = plan.process_jobs().collect::<Vec<_>>();
            assert_eq!(jobs.len(), 1);
            assert!(matches!(jobs[0],Proc::DdlTheory(name,..) if name=="Inner"));
        })
        .expect("bounded-stack test thread")
        .join()
        .expect("heap-driven DDL construction and cleanup");
}
