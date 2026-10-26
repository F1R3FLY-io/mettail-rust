use mettail_rholang_adapter::{MettaGslt, MettaProgram, MettaResourceLogic, MettaSig};
use models::rhoapi::{cost_signature::Value, CostSignature, CostSignedTerm, Par};
use proptest::prelude::*;
use rholang::rust::interpreter::accounting::authority::{
    compound_cost_signatures, cost_signature_to_sig, DemandBound, ResourceMultiset,
};
use rholang::rust::interpreter::accounting::resource_logic::{
    DefaultResourceLogic, GsltPresentation, OslfResourceLogic, RhoGslt,
};
use rholang::rust::interpreter::accounting::Sig;

fn unit() -> CostSignature {
    CostSignature { value: Some(Value::Unit(true)) }
}

fn quoted_nil() -> CostSignature {
    CostSignature {
        value: Some(Value::Quote(Par::default())),
    }
}

fn product(left: &CostSignature, right: &CostSignature) -> CostSignature {
    compound_cost_signatures(left, right).expect("finite closed signatures compose")
}

fn repeated_quote(count: usize) -> CostSignature {
    (0..count).fold(unit(), |signature, _| product(&signature, &quoted_nil()))
}

fn finite_forest(instructions: &[u8]) -> (CostSignature, usize) {
    let mut stack = Vec::new();
    let mut occurrences = 0;
    for instruction in instructions {
        match instruction % 3 {
            0 => stack.push(unit()),
            2 if stack.len() >= 2 => {
                let right = stack.pop().unwrap();
                let left = stack.pop().unwrap();
                stack.push(product(&left, &right));
            },
            _ => {
                stack.push(quoted_nil());
                occurrences += 1;
            },
        }
    }
    let mut signature = stack.pop().unwrap_or_else(unit);
    while let Some(left) = stack.pop() {
        signature = product(&left, &signature);
    }
    (signature, occurrences)
}

fn quote_occurrences(signature: &Sig) -> usize {
    let expected = cost_signature_to_sig(&quoted_nil()).unwrap();
    let mut pending = vec![signature];
    let mut count = 0;
    while let Some(current) = pending.pop() {
        match current {
            Sig::Unit => {},
            Sig::And(left, right) => {
                pending.push(left);
                pending.push(right);
            },
            Sig::Quote(_) => {
                assert_eq!(current, &expected, "every generator denotes the actual quoted Nil");
                count += 1;
            },
            other => panic!("finite template introduced a non-quote authority atom: {other:?}"),
        }
    }
    count
}

fn check_template(signature: CostSignature, occurrences: usize) {
    let native_signature = cost_signature_to_sig(&signature).unwrap();
    assert_eq!(quote_occurrences(&native_signature), occurrences);
    assert_eq!(signature, repeated_quote(occurrences), "product shape cannot alter the lane");
    let program = if occurrences == 0 {
        Par::default()
    } else {
        models::par_from_default! {
            cost_signed_terms: vec![CostSignedTerm {
                body: Some(Par::default()),
                signature: Some(signature),
            }],
            ..Par::default()
        }
    };
    let native = RhoGslt.canonicalize_for_funding(&program).unwrap();
    let adapted = MettaGslt
        .canonicalize_for_funding(&MettaProgram(program))
        .unwrap();
    assert_eq!(native, adapted);
    let host = DefaultResourceLogic;
    let adapter = MettaResourceLogic;
    let deploy = Sig::Unit;
    let adapter_deploy = MettaSig(deploy.clone());
    let host_bound = OslfResourceLogic::<RhoGslt>::demand_bound(&host, &native, &deploy);
    let adapter_bound = adapter.demand_bound(&adapted, &adapter_deploy);
    assert_eq!(host_bound, adapter_bound);
    let DemandBound::FiniteUpperBound { bound, proof } = &host_bound else {
        panic!("finite templates retain upper-bound evidence, including the unit");
    };
    let expected = if occurrences == 0 {
        ResourceMultiset::default()
    } else {
        ResourceMultiset::singleton(native_signature.lane_hash(), 1)
    };
    assert_eq!(bound, &expected, "one whole compound lane, not one lane per generator");
    assert_eq!(
        OslfResourceLogic::<RhoGslt>::verify_demand_bound(&host, &native, &deploy, &host_bound),
        Some(expected.clone()),
    );
    assert_eq!(
        adapter.verify_demand_bound(&adapted, &adapter_deploy, &adapter_bound),
        Some(expected.clone()),
    );

    let mut changed_proof = proof.clone();
    changed_proof.push(0);
    let mut forgeries = vec![
        DemandBound::Exact(expected.clone()),
        DemandBound::FiniteUpperBound { bound: expected, proof: changed_proof },
        DemandBound::FiniteUpperBound {
            bound: ResourceMultiset::singleton(native_signature.lane_hash(), 2),
            proof: proof.clone(),
        },
    ];
    if occurrences > 0 {
        forgeries.push(DemandBound::FiniteUpperBound {
            bound: ResourceMultiset::default(),
            proof: proof.clone(),
        });
    }
    if occurrences > 1 {
        let atom = cost_signature_to_sig(&quoted_nil()).unwrap();
        forgeries.push(DemandBound::FiniteUpperBound {
            bound: ResourceMultiset::singleton(atom.lane_hash(), 1),
            proof: proof.clone(),
        });
    }
    for forged in forgeries {
        assert_eq!(
            OslfResourceLogic::<RhoGslt>::verify_demand_bound(&host, &native, &deploy, &forged),
            None,
        );
        assert_eq!(adapter.verify_demand_bound(&adapted, &adapter_deploy, &forged), None);
    }
}

#[test]
fn finite_template_unit_and_repeated_generator_examples() {
    for occurrences in 0..=8 {
        check_template(repeated_quote(occurrences), occurrences);
    }
    for instructions in [vec![], vec![0, 0, 2], vec![1, 1, 2], vec![1, 0, 2, 1, 2]] {
        let (signature, occurrences) = finite_forest(&instructions);
        check_template(signature, occurrences);
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(128))]

    #[test]
    fn generated_finite_product_forests_preserve_template_evidence(
        instructions in prop::collection::vec(any::<u8>(), 0..65),
    ) {
        let (signature, occurrences) = finite_forest(&instructions);
        check_template(signature, occurrences);
    }

    #[test]
    fn canonical_products_preserve_quote_multiplicity_and_unit(
        left in 0usize..17,
        middle in 0usize..17,
        right in 0usize..17,
    ) {
        let a = repeated_quote(left);
        let b = repeated_quote(middle);
        let c = repeated_quote(right);
        prop_assert_eq!(product(&a, &b), product(&b, &a));
        prop_assert_eq!(product(&a, &unit()), a.clone());
        prop_assert_eq!(product(&unit(), &a), a.clone());
        let left_nested = product(&product(&a, &b), &c);
        let right_nested = product(&a, &product(&b, &c));
        prop_assert_eq!(&left_nested, &right_nested);
        check_template(left_nested, left + middle + right);
    }
}
