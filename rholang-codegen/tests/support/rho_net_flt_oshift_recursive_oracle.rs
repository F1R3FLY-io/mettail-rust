use super::*;
use crate::rho_net_lower::is_ground_marker_par;
use prost::Message;

const FP: &str = "mettail-langdef-v1:6ef0c40636bb0bca";

fn g_bound(depth: usize) -> GroundTerm {
    GroundTerm::new(BOUND_VAR_REFLECT_LABEL, vec![peano_ground_term(depth)])
}

fn g_lambda(body: GroundTerm) -> GroundTerm {
    GroundTerm::new(LAMBDA_REFLECT_LABEL, vec![body])
}

fn recursive_host_oshift(par: &Par, cutoff: usize, fingerprint: &str) -> Par {
    if par_carries_ground_marker(par, fingerprint) {
        return par.clone();
    }
    let ps = match elist_ps(par) {
        Some(ps) if !ps.is_empty() => ps,
        _ => return par.clone(),
    };
    let head = &ps[0];
    if head == &flt_tag_par(fingerprint, BOUND_VAR_REFLECT_LABEL) {
        match peano_value(ps.get(2), fingerprint) {
            Some(n) if n >= cutoff => bound_var_par(n + 1, fingerprint),
            _ => par.clone(),
        }
    } else if head == &flt_tag_par(fingerprint, LAMBDA_REFLECT_LABEL) {
        let marker = ps.get(1).cloned();
        let body = recursive_host_oshift(&ps[2], cutoff + 1, fingerprint);
        rebuild_object_node(head, marker, vec![body])
    } else {
        let marked = ps.len() >= 2 && is_ground_marker_par(&ps[1], fingerprint);
        let (marker, children_start) = if marked {
            (ps.get(1).cloned(), 2)
        } else {
            (None, 1)
        };
        let children = ps[children_start..]
            .iter()
            .map(|child| recursive_host_oshift(child, cutoff, fingerprint))
            .collect();
        rebuild_object_node(head, marker, children)
    }
}

#[test]
fn host_oshift_pda_is_protobuf_identical_to_recursive_oracle() {
    let subjects = [
        GroundTerm::new("App", vec![g_bound(0), g_bound(2)]),
        g_lambda(GroundTerm::new("App", vec![g_bound(1), g_bound(3)])),
        GroundTerm::new(
            "Root",
            vec![g_lambda(g_lambda(g_bound(2))), GroundTerm::nullary("GroundLeaf"), g_bound(4)],
        ),
    ];
    for subject in &subjects {
        let par = reflect_ground_term_par(subject, FP);
        for cutoff in 0..5 {
            let expected = recursive_host_oshift(&par, cutoff, FP);
            let actual = host_oshift(&par, cutoff, FP);
            assert_eq!(actual.encode_to_vec(), expected.encode_to_vec());
        }
    }

    let scalar = models::rust::utils::new_gstring_par("leaf".to_owned(), Vec::new(), false);
    assert_eq!(
        host_oshift(&scalar, 7, FP).encode_to_vec(),
        recursive_host_oshift(&scalar, 7, FP).encode_to_vec()
    );
}

#[test]
fn host_oshift_handles_twenty_thousand_lambdas_on_a_small_native_stack() {
    const DEPTH: usize = 20_000;
    let handle = std::thread::Builder::new()
        .name("host-oshift-pda-small-stack".into())
        .stack_size(256 * 1024)
        .spawn(|| {
            let mut subject = g_bound(0);
            for _ in 0..DEPTH {
                subject = g_lambda(subject);
            }
            let reflected = reflect_ground_term_par(&subject, FP);
            let shifted = host_oshift(&reflected, 1, FP);

            let lambda_tag = flt_tag_par(FP, LAMBDA_REFLECT_LABEL);
            let bound_tag = flt_tag_par(FP, BOUND_VAR_REFLECT_LABEL);
            let mut cursor = &shifted;
            for _ in 0..DEPTH {
                let ps = elist_ps(cursor).expect("lambda must remain an EList");
                assert_eq!(ps.first(), Some(&lambda_tag));
                cursor = &ps[2];
            }
            assert_eq!(elist_ps(cursor).and_then(|ps| ps.first()), Some(&bound_tag));
            assert_eq!(peano_value(elist_ps(cursor).and_then(|ps| ps.get(2)), FP), Some(0));

            drop(shifted);
            drop(reflected);
            drop(subject);
        })
        .expect("small-stack host oshift thread must spawn");
    handle
        .join()
        .expect("host oshift PDA must not overflow the native stack");
}
