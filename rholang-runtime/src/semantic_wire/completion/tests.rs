use super::*;
use crate::language_install::{exact_expr, exact_list, wire_list};
use models::rhoapi::{expr::ExprInstance, EList};
use models::rust::utils::new_gint_par;

fn int(n: i64) -> Par {
    new_gint_par(n, Vec::new(), false)
}

fn fields(value: &mut Par) -> &mut EList {
    match value.exprs[0].expr_instance.as_mut().expect("expression") {
        ExprInstance::EListBody(list) => list,
        _ => panic!("list"),
    }
}

fn limits(word: usize, work: u64) -> SemanticServiceLimits {
    SemanticServiceLimits {
        execution: SemanticTransitionLimits {
            work,
            normalization_steps: word,
            outputs: word,
            frontier: word,
            proofs: word,
            proof_nodes: word,
            term_nodes: word,
            term_bytes: word,
            output_nodes: word,
            output_bytes: word,
        },
        boundary_payload_bytes: word,
    }
}

fn prepared() -> (CompletionPermit, SemanticWireUsage) {
    let limits = limits(10_000, 10_000);
    let mut work = 7;
    let mut cancel = || false;
    let mut budget = ReflectedCodecBudget::new(&mut work, 10_000, 10_000 - 11, &mut cancel);
    let permit = CompletionPermit::reserve(limits, &mut budget).expect("prepay");
    budget.charge(20, 30).expect("intermediate work");
    let remaining = budget.finish();
    (
        permit,
        SemanticWireUsage {
            work,
            kernel_work: Some(0),
            effective_limits: Some(limits),
            remaining_boundary_payload_bytes: remaining,
        },
    )
}

#[test]
fn semantic_wire_limits_preserve_order_width_and_exact_arity() {
    let mut work = 0;
    let mut cancel = || false;
    let mut budget = ReflectedCodecBudget::new(&mut work, 100_000, 100_000, &mut cancel);
    let wire = wire_list((1..=11).map(int).collect());
    let decoded = decode_limits_v1(&wire, &mut budget).expect("limits");
    assert_eq!(decoded.commitment_words(), [1, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 1]);
    assert_eq!(encode_limits_v1(decoded, &mut budget).expect("encode"), wire);
    for n in [0, 1, i64::MAX as u64, i64::MAX as u64 + 1, u64::MAX] {
        let value = limits(usize::MAX, n);
        let encoded = encode_limits_v1(value, &mut budget).expect("full-width limits");
        assert_eq!(decode_limits_v1(&encoded, &mut budget), Ok(value));
    }
    for length in [0, 10, 12, 10_000] {
        let malformed = wire_list((0..length).map(|_| int(0)).collect());
        assert!(decode_limits_v1(&malformed, &mut budget).is_err());
    }
    for index in 0..11 {
        let mut malformed = wire.clone();
        fields(&mut malformed).ps[index] = int(-1);
        assert!(decode_limits_v1(&malformed, &mut budget).is_err());
    }
    for kind in 0..5 {
        let mut malformed = wire.clone();
        match kind {
            0 => malformed.locally_free.push(1),
            1 => malformed.connective_used = true,
            2 => fields(&mut malformed).locally_free.push(1),
            3 => fields(&mut malformed).connective_used = true,
            _ => malformed.sends.push(Default::default()),
        }
        assert!(decode_limits_v1(&malformed, &mut budget).is_err());
    }
}

#[test]
fn semantic_wire_usage_inverse_and_maximum_quota() {
    for kernel in [None, Some(0), Some(u64::MAX)] {
        for limit in [None, Some(limits(usize::MAX, u64::MAX))] {
            let usage = SemanticWireUsage {
                work: u64::MAX,
                kernel_work: kernel,
                effective_limits: limit,
                remaining_boundary_payload_bytes: usize::MAX,
            };
            let mut work = 0;
            let mut cancel = || false;
            let mut budget = ReflectedCodecBudget::new(&mut work, 146, 598, &mut cancel);
            let encoded = Encoder { budget: &mut budget }
                .usage(usage)
                .expect("bounded usage");
            let remaining = budget.finish();
            let used = work;
            if usize::BITS == 64 && kernel == Some(u64::MAX) && limit.is_some() {
                assert_eq!((used, remaining), (146, 0));
            }
            let mut decode = ReflectedCodecBudget::new(&mut work, 1000, 0, &mut cancel);
            assert_eq!(decode_usage_v1(&encoded, &mut decode), Ok(usage));
            assert_eq!(decode.remaining_bytes(), 0, "borrowed decoding allocates nothing");
            for (wl, bl) in [(used - 1, 598 - remaining), (used, 597 - remaining)] {
                let mut work = 0;
                let mut budget = ReflectedCodecBudget::new(&mut work, wl, bl, &mut cancel);
                assert!(Encoder { budget: &mut budget }.usage(usage).is_err());
                assert!(budget.work_used() <= wl);
            }
        }
    }
}

#[test]
fn semantic_wire_usage_rejects_malformed_options_and_nested_limits() {
    for option in [
        Par::default(),
        wire_list(vec![]),
        wire_list(vec![int(1)]),
        wire_list(vec![int(0), int(9)]),
        wire_list(vec![int(2), int(9)]),
        wire_list(vec![int(1), int(9), int(10)]),
    ] {
        for index in [1, 2] {
            let mut value =
                wire_list(vec![int(0), wire_list(vec![int(0)]), wire_list(vec![int(0)]), int(0)]);
            fields(&mut value).ps[index] = option.clone();
            let mut work = 0;
            let mut cancel = || false;
            let mut budget = ReflectedCodecBudget::new(&mut work, 100, 0, &mut cancel);
            assert!(decode_usage_v1(&value, &mut budget).is_err());
        }
    }
    let value =
        wire_list(vec![int(0), wire_list(vec![int(0)]), wire_list(vec![int(1), int(7)]), int(0)]);
    let mut work = 0;
    let mut cancel = || false;
    let mut budget = ReflectedCodecBudget::new(&mut work, 100, 0, &mut cancel);
    assert!(decode_usage_v1(&value, &mut budget).is_err());
}

#[test]
fn semantic_wire_reservation_is_atomic_and_preserves_prefix() {
    for (wl, bl, succeeds) in [(159, 742, true), (158, 742, false), (159, 741, false)] {
        let mut work = 7;
        let mut cancel = || false;
        let limits = limits(bl + 11, wl);
        let mut budget = ReflectedCodecBudget::new(&mut work, wl, bl, &mut cancel);
        let result = CompletionPermit::reserve(limits, &mut budget);
        assert_eq!(result.is_ok(), succeeds);
        assert_eq!(budget.work_used(), if succeeds { 159 } else { 7 });
        assert_eq!(budget.remaining_bytes(), if succeeds { 0 } else { bl });
    }
    let mut work = 7;
    let mut cancel = || true;
    let mut budget = ReflectedCodecBudget::new(&mut work, 159, 742, &mut cancel);
    assert!(CompletionPermit::reserve(limits(753, 159), &mut budget).is_err());
    assert_eq!((budget.work_used(), budget.remaining_bytes()), (7, 742));
}

#[test]
fn semantic_wire_completion_preserves_final_usage_and_finite_statuses() {
    for domain in [
        DiagnosticDomain::Wire,
        DiagnosticDomain::Access,
        DiagnosticDomain::Service,
        DiagnosticDomain::Kernel,
        DiagnosticDomain::Boundary,
        DiagnosticDomain::Restore,
    ] {
        for status in 0..4 {
            let (permit, usage) = prepared();
            let body = match status {
                0 => ReplyBody::Proven(wire_list(vec![int(7), int(7)])),
                1 => ReplyBody::Refuted(domain, u16::MAX),
                2 => ReplyBody::Undetermined(domain, u16::MAX),
                _ => ReplyBody::Error(domain, u16::MAX),
            };
            let mut cancel = StickyCancellation::new(|| false);
            let reply = permit.finish(body, usage, &mut cancel).expect("complete");
            let [version, actual, body, report] = exact_list(&reply).unwrap() else {
                panic!("four fields")
            };
            assert_eq!(*version, int(1));
            assert_eq!(*actual, int(status));
            let mut work = 0;
            let mut never = || false;
            let mut budget = ReflectedCodecBudget::new(&mut work, 1000, 0, &mut never);
            assert_eq!(decode_usage_v1(report, &mut budget), Ok(usage));
            assert_eq!(usage.work, 7 + 152 + 20, "completion does not recharge or refund");
            assert_eq!(usage.remaining_boundary_payload_bytes, 10_000 - 11 - 742 - 30);
            if status != 0 {
                assert_eq!(
                    *body,
                    wire_list(vec![int(i64::from(domain.tag())), int(i64::from(u16::MAX))])
                );
            } else {
                assert_eq!(*body, wire_list(vec![int(7), int(7)]), "duplicate results retained");
            }
        }
    }
}

#[test]
fn semantic_wire_completion_refuses_amplification_overdraw_and_reset() {
    for case in 0..7 {
        let (permit, mut usage) = prepared();
        match case {
            0 => usage.work = 151,
            1 => usage.work = 10_001,
            2 => usage.remaining_boundary_payload_bytes = 10_001,
            3 => usage.remaining_boundary_payload_bytes = 10_000,
            4 => usage.effective_limits.as_mut().unwrap().execution.outputs += 1,
            5 => usage.kernel_work = Some(usage.work + 1),
            _ => {
                usage
                    .effective_limits
                    .as_mut()
                    .unwrap()
                    .boundary_payload_bytes = 1
            },
        }
        assert!(permit
            .finish(ReplyBody::Proven(int(0)), usage, &mut StickyCancellation::new(|| false))
            .is_err());
    }
}

#[test]
fn semantic_wire_cancellation_is_sticky_at_every_completion_boundary() {
    let (permit, usage) = prepared();
    let mut calls = 0;
    permit
        .finish(
            ReplyBody::Proven(int(7)),
            usage,
            &mut StickyCancellation::new(|| {
                calls += 1;
                false
            }),
        )
        .expect("baseline");
    assert!(calls > 10);
    for stop in 1..=calls {
        let (permit, usage) = prepared();
        let mut count = 0;
        let mut cancellation = StickyCancellation::new(|| {
            count += 1;
            count == stop
        });
        assert_eq!(
            permit.finish(ReplyBody::Proven(int(7)), usage, &mut cancellation),
            Err(SemanticWireError::Resource(DynamicReflectionError::Cancelled))
        );
        assert!(cancellation.poll(), "one-shot cancellation cannot be forgotten");
    }
    let (permit, usage) = prepared();
    let mut cancellation = StickyCancellation::new(|| true);
    assert!(cancellation.poll());
    let reply = permit
        .finish(ReplyBody::Undetermined(DiagnosticDomain::Kernel, 1), usage, &mut cancellation)
        .expect("prepaid negative reply");
    assert_eq!(exact_list(&reply).unwrap()[1], int(2));
}

#[test]
fn semantic_wire_completion_moves_and_drops_deep_closed_bodies_on_small_stack() {
    std::thread::Builder::new()
        .stack_size(128 * 1024)
        .spawn(|| {
            for refused in [false, true] {
                let mut body = int(0);
                for _ in 0..20_000 {
                    body = wire_list(vec![body]);
                }
                let pointer = exact_list(&body).unwrap().as_ptr();
                let (permit, usage) = prepared();
                let result = permit.finish(
                    ReplyBody::Proven(body),
                    usage,
                    &mut StickyCancellation::new(|| refused),
                );
                if refused {
                    assert!(result.is_err());
                } else {
                    let reply = result.expect("closed body");
                    let body = &exact_list(&reply).unwrap()[2];
                    assert_eq!(
                        exact_list(body).unwrap().as_ptr(),
                        pointer,
                        "owned body moved without cloning"
                    );
                    assert!(matches!(exact_expr(body), Some(ExprInstance::EListBody(_))));
                }
            }
        })
        .expect("worker")
        .join()
        .expect("iterative cleanup");
}
