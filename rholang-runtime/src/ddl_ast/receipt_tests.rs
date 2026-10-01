use super::*;
use crate::rholang_ast::constructed_value::ConstructedValue;
use crate::rholang_ast::construction_receipt::{NativeCounts, NativeReceipt};
use mettail_rholang_codegen::DynamicReflectionError;
use proptest::prelude::*;
use prost::Message;

impl DdlWireValue for mettail_elab::canonical::RhoValue {
    fn text(value: String, _: &mut Reservation<'_>) -> Result<Self, RholangAstLowerError> {
        Ok(Self::String(value))
    }

    fn integer(value: i64, _: &mut Reservation<'_>) -> Result<Self, RholangAstLowerError> {
        Ok(Self::Integer(i128::from(value)))
    }

    fn closed_list(
        children: Vec<Self>,
        _: &mut Reservation<'_>,
    ) -> Result<Self, RholangAstLowerError> {
        Ok(Self::List(children))
    }
}

#[test]
fn generated_and_standalone_projection_frontends_agree_on_typed_native_rows() {
    use mettail_elab::ast::{Builder, ProjectionBody, RewriteEntry, TheoryExpr};
    use mettail_elab::wire::{decode_ddl_value, ParsedDdl};
    use mettail_languages::rholang::DdlTheoryExpr;

    let body_source = r#"Rewrites {
        projection Scalar : Number <~> host::Int {
            One(n:Number,h:host::Int): if n ~> h then (Number n) <~> 1;
            Two : (Number 2) <~> (host::CastInt 2);
        }
        projection TextValue : Text <~> host::Str via carrier;
        projection TextLiteral : Text ~> host::Str {
            Hello : (Text) ~> "λ";
        }
        projection Import : Entry <~ host::Proc {
            Take : (Entry) <~ (host::Par);
        }
    }"#;
    let generated = DdlTheoryExpr::parse(body_source).expect("generated DDL syntax");
    let wire = DdlLowerPlan::build(DdlRoot::Theory {
        name: "T",
        parameters: &[],
        body: &generated,
    })
    .try_finish_with::<mettail_elab::canonical::RhoValue>(Vec::new(), &mut |_, _| Ok(()))
    .expect("structural DDL wire");
    let ParsedDdl::Theory(decoded) = decode_ddl_value(wire).expect("typed projection wire") else {
        panic!("theory wire must remain a theory");
    };
    let standalone = mettail_elab::parse::parse_theory(&format!("Theory T() {{ {body_source} }}"))
        .expect("standalone DDL syntax");
    let TheoryExpr::Build {
        builder: Builder::Rewrites(generated_entries),
        ..
    } = decoded.body
    else {
        panic!("generated theory has Rewrites");
    };
    let TheoryExpr::Build {
        builder: Builder::Rewrites(standalone_entries),
        ..
    } = standalone.body
    else {
        panic!("standalone theory has Rewrites");
    };
    assert_eq!(generated_entries.len(), standalone_entries.len());
    for (generated, standalone) in generated_entries.iter().zip(&standalone_entries) {
        let (RewriteEntry::Projection(generated), RewriteEntry::Projection(standalone)) =
            (generated, standalone)
        else {
            panic!("each entry is a projection");
        };
        assert_eq!(generated.name, standalone.name);
        assert_eq!(generated.guest, standalone.guest);
        assert_eq!(generated.host, standalone.host);
        assert_eq!(generated.direction, standalone.direction);
        match (&generated.body, &standalone.body) {
            (ProjectionBody::Carrier, ProjectionBody::Carrier) => {},
            (ProjectionBody::Rules(generated_rows), ProjectionBody::Rules(standalone_rows)) => {
                assert_eq!(generated_rows.len(), standalone_rows.len());
                for (generated_row, standalone_row) in generated_rows.iter().zip(standalone_rows) {
                    assert_eq!(generated_row.name, standalone_row.name);
                    assert_eq!(generated_row.bindings, standalone_row.bindings);
                    assert_eq!(generated_row.premises, standalone_row.premises);
                    assert_eq!(generated_row.guest, standalone_row.guest);
                    assert_eq!(generated_row.host, standalone_row.host);
                    assert_eq!(generated_row.direction, standalone_row.direction);
                }
            },
            _ => panic!("projection body kind differs"),
        }
    }
}

proptest! {
    #[test]
    fn projection_integer_wire_preserves_every_admitted_i64(value in any::<i64>()) {
        let literal = Int::NumLit(value);
        let plan = DdlLowerPlan {
            operations: vec![WireOp::Integer(&literal)],
            processes: Vec::new(),
        };
        let expected = new_gint_par(value, Vec::new(), false);
        prop_assert_eq!(plan.finish(Vec::new()).expect("native integer wire"), expected);
    }
}

fn refused() -> RholangAstLowerError {
    RholangAstLowerError::Preparation(DynamicReflectionError::Cancelled)
}

fn process() -> ConstructedValue {
    ConstructedValue {
        par: new_gstring_par("embedded".into(), vec![1, 0, 1], true),
        receipt: NativeReceipt {
            outer_metadata_bytes: 3,
            owned: NativeCounts {
                heads: 1,
                payload_bytes: 8,
                ..NativeCounts::default()
            },
        },
    }
}

fn plan(source: &Proc) -> DdlLowerPlan<'_> {
    DdlLowerPlan {
        operations: vec![
            WireOp::Text("plain"),
            WireOp::QuotedText("\"λ\""),
            WireOp::Process(0),
            WireOp::Node { tag: "wire", child_count: 3 },
        ],
        processes: vec![source],
    }
}

#[test]
fn measured_finish_preserves_wire_bytes_decoded_lengths_and_embedded_metadata() {
    let source = Proc::PZero;
    let original = plan(&source)
        .finish(vec![process().par])
        .expect("original wire");
    let actual = plan(&source)
        .try_finish_with(vec![process()], &mut |_, _| Ok(()))
        .expect("measured wire");
    assert_eq!(actual.par.encode_to_vec(), original.encode_to_vec());
    assert!(actual.par.locally_free.is_empty());
    assert!(!actual.par.connective_used);
    assert_eq!(
        actual.receipt,
        NativeReceipt {
            outer_metadata_bytes: 0,
            owned: NativeCounts {
                heads: 5,
                payload_bytes: 19,
                metadata_bytes: 3,
                descendant_pars: 4,
                ..NativeCounts::default()
            },
        }
    );
}

#[test]
fn process_only_plan_transfers_the_supplied_annotation_without_reconstruction() {
    let source = Proc::PZero;
    let expected = process();
    let plan = DdlLowerPlan {
        operations: vec![WireOp::Process(0)],
        processes: vec![&source],
    };
    let actual = plan
        .try_finish_with(vec![process()], &mut |_, _| Ok(()))
        .expect("existing process value");
    assert_eq!(actual.par, expected.par);
    assert_eq!(actual.receipt, expected.receipt);
}

#[test]
fn measured_finish_refuses_at_every_paid_prefix_and_exact_resource_boundary() {
    let source = Proc::PZero;
    let mut trace = Vec::new();
    plan(&source)
        .try_finish_with(vec![process()], &mut |w, u| {
            trace.push((w, u));
            Ok(())
        })
        .expect("measured baseline");
    for cut in 0..trace.len() {
        let mut seen = Vec::new();
        let result = plan(&source).try_finish_with(vec![process()], &mut |w, u| {
            seen.push((w, u));
            if seen.len() == cut + 1 {
                Err(refused())
            } else {
                Ok(())
            }
        });
        assert_eq!(result.err(), Some(refused()));
        assert_eq!(seen, trace[..=cut]);
    }
    let total = trace
        .iter()
        .fold((0, 0), |(w, u), (dw, du)| (w + dw, u + du));
    for (work, units, accepted) in [
        (total.0, total.1, true),
        (total.0 - 1, total.1, false),
        (total.0, total.1 - 1, false),
        (0, 0, false),
    ] {
        let mut used = (0, 0);
        let result = plan(&source).try_finish_with(vec![process()], &mut |w, u| {
            if w > work - used.0 || u > units - used.1 {
                return Err(refused());
            }
            used.0 += w;
            used.1 += u;
            Ok(())
        });
        assert_eq!(result.is_ok(), accepted);
        assert!(used.0 <= work && used.1 <= units);
    }
}

#[test]
fn measured_finish_preserves_slot_and_wire_refusals() {
    let source = Proc::PZero;
    for (operations, processes, values) in [
        (vec![WireOp::Process(0)], vec![&source], vec![]),
        (vec![WireOp::Process(0), WireOp::Process(0)], vec![&source], vec![process()]),
        (vec![WireOp::Process(1)], vec![&source], vec![process()]),
        (vec![WireOp::Text("unused")], vec![&source], vec![process()]),
        (vec![WireOp::Node { tag: "broken", child_count: 1 }], vec![], vec![]),
        (vec![WireOp::QuotedText("unquoted")], vec![], vec![]),
        (vec![], vec![], vec![]),
    ] {
        let result =
            DdlLowerPlan { operations, processes }.try_finish_with(values, &mut |_, _| Ok(()));
        assert!(matches!(result, Err(RholangAstLowerError::DdlWire(_))));
    }
}

#[test]
fn deep_measured_finish_and_late_refusal_cleanup_remain_stack_safe() {
    std::thread::Builder::new()
        .stack_size(128 * 1024)
        .spawn(|| {
            let source = Proc::PZero;
            let make_plan = || {
                let mut operations = vec![WireOp::Process(0)];
                operations.extend((0..4096).map(|_| WireOp::Node { tag: "node", child_count: 1 }));
                DdlLowerPlan { operations, processes: vec![&source] }
            };
            let mut calls = 0;
            let actual = make_plan()
                .try_finish_with(vec![process()], &mut |_, _| {
                    calls += 1;
                    Ok(())
                })
                .expect("deep measured finish");
            assert_eq!(actual.receipt.owned.heads, 1 + 2 * 4096);
            assert_eq!(actual.receipt.owned.payload_bytes, 8 + 4 * 4096);
            assert_eq!(actual.receipt.owned.descendant_pars, 2 * 4096);
            assert_eq!(actual.receipt.owned.metadata_bytes, 3);
            assert_eq!(actual.receipt.outer_metadata_bytes, 0);
            drop(actual);
            let mut seen = 0;
            let result = make_plan().try_finish_with(vec![process()], &mut |_, _| {
                seen += 1;
                if seen == calls - 1 {
                    Err(refused())
                } else {
                    Ok(())
                }
            });
            assert_eq!(result.err(), Some(refused()));
            assert_eq!(seen, calls - 1);
        })
        .expect("small-stack thread")
        .join()
        .expect("iterative finish and owned cleanup");
}
