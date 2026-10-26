use mettail_rholang_adapter::{conformance, MettaGslt, MettaProgram, MettaResourceLogic, MettaSig};
use models::rhoapi::{
    cost_signature::Value as SignatureValue, expr::ExprInstance, var::VarInstance, CostSignature,
    CostSignedTerm, CostStack, EVar, Expr, Par, Receive, Send, Var,
};
use rholang::rust::interpreter::accounting::authority::{
    compound_cost_signatures, cost_signature_to_sig, DemandBound, ResourceMultiset,
    UnprovableDemand,
};
use rholang::rust::interpreter::accounting::delta_sigma::{DemandEntry, SigKey};
use rholang::rust::interpreter::accounting::oslf::{self, CheckError, DemandKnowledge, Formula};
use rholang::rust::interpreter::accounting::resource_logic::{
    DefaultResourceLogic, GsltPresentation, OslfResourceLogic, ResourceSignature, RhoGslt,
};
use rholang::rust::interpreter::accounting::Sig;

fn ground(tag: u8) -> CostSignature {
    CostSignature {
        value: Some(SignatureValue::Ground(vec![tag])),
    }
}

fn sends(count: usize) -> Par {
    let mut par = Par::default();
    par.sends = (0..count)
        .map(|_| Send {
            chan: Some(Par::default()),
            data: vec![],
            persistent: false,
            locally_free: vec![],
            connective_used: false,
        })
        .collect();
    par
}

fn signed(body: Par, signature: CostSignature) -> Par {
    models::par_from_default! {
        cost_signed_terms: vec![CostSignedTerm {
            body: Some(body),
            signature: Some(signature),
        }],
        ..Par::default()
    }
}

fn stack(cells: Vec<CostSignature>) -> Par {
    models::par_from_default! {
        cost_stacks: vec![CostStack { cells, parallel_tail: vec![] }],
        ..Par::default()
    }
}

fn signatures() -> Vec<Sig> {
    vec![
        Sig::Unit,
        Sig::Ground(vec![11]),
        Sig::Quote(vec![12]),
        Sig::And(Box::new(Sig::Ground(vec![11])), Box::new(Sig::Ground(vec![12]))),
        Sig::And(
            Box::new(Sig::Ground(vec![11])),
            Box::new(Sig::And(Box::new(Sig::Ground(vec![12])), Box::new(Sig::Ground(vec![13])))),
        ),
    ]
}

fn formulas(left: SigKey, right: SigKey) -> Vec<Formula<SigKey>> {
    vec![
        Formula::True,
        Formula::All(vec![Formula::True, Formula::Sufficient { surface: left }]),
        Formula::Available { surface: left, amount: 1 },
        Formula::Required { surface: left, amount: 0 },
        Formula::Required { surface: left, amount: 1 },
        Formula::Not(Box::new(Formula::Required { surface: left, amount: 1 })),
        Formula::Required { surface: left, amount: 100 },
        Formula::Located {
            surface: left,
            body: Box::new(Formula::Sufficient { surface: left }),
        },
        Formula::Located {
            surface: left,
            body: Box::new(Formula::Available { surface: right, amount: 1 }),
        },
        Formula::Spatial(
            Box::new(Formula::Sufficient { surface: left }),
            Box::new(Formula::Sufficient { surface: right }),
        ),
        Formula::Spatial(
            Box::new(Formula::Available { surface: left, amount: 1 }),
            Box::new(Formula::Available { surface: left, amount: 1 }),
        ),
        Formula::Spend {
            grade: ResourceMultiset::singleton(left, 1),
            continuation: Box::new(Formula::Available { surface: left, amount: 1 }),
        },
        Formula::Spend {
            grade: ResourceMultiset::default(),
            continuation: Box::new(Formula::True),
        },
        Formula::linear(left),
        Formula::copyable(left),
        Formula::relevant(left),
    ]
}

fn assert_claim_parity(
    canonical: &Par,
    signature: &Sig,
    claim: &DemandBound<SigKey>,
    supply: &ResourceMultiset<SigKey>,
) -> Option<ResourceMultiset<SigKey>> {
    let wrapped = MettaSig(signature.clone());
    let native = DefaultResourceLogic.verify_demand_bound(canonical, signature, claim);
    assert_eq!(MettaResourceLogic.verify_demand_bound(canonical, &wrapped, claim), native);
    assert_eq!(
        MettaResourceLogic.is_funded_bound(canonical, &wrapped, claim, supply),
        DefaultResourceLogic.is_funded_bound(canonical, signature, claim, supply),
    );
    native
}

fn assert_observation_and_formula_parity(
    canonical: &Par,
    signature: &Sig,
    supply: &ResourceMultiset<SigKey>,
) {
    let wrapped = MettaSig(signature.clone());
    let native = DefaultResourceLogic.resource_observation(canonical, signature, supply);
    let adapted = MettaResourceLogic.resource_observation(canonical, &wrapped, supply);
    assert_eq!(adapted, native);
    if let Ok(observation) = &adapted {
        assert_eq!(&observation.available, supply);
        assert!(matches!(observation.demand, DemandKnowledge::UpperBound(_)));
    }
    for formula in formulas(signature.key(), Sig::Ground(vec![99]).key()) {
        let expected = DefaultResourceLogic.check_formula(canonical, signature, supply, &formula);
        assert_eq!(
            MettaResourceLogic.check_formula(canonical, &wrapped, supply, &formula),
            expected,
            "formula parity: {formula:?}",
        );
        if let Ok(observation) = &native {
            assert_eq!(expected, oslf::check(observation, &formula));
        }
    }
}

fn assert_program_parity(program: &Par, signature: &Sig) -> DemandBound<SigKey> {
    let native = RhoGslt
        .canonicalize_for_funding(program)
        .expect("native Par canonicalization");
    let adapted = MettaGslt
        .canonicalize_for_funding(&MettaProgram(program.clone()))
        .expect("adapter Par canonicalization");
    assert_eq!(adapted, native);
    let wrapped = MettaSig(signature.clone());
    let demand = DefaultResourceLogic.demand(&native, signature);
    assert_eq!(MettaResourceLogic.demand(&adapted, &wrapped), demand);
    let bound = DefaultResourceLogic.demand_bound(&native, signature);
    assert_eq!(MettaResourceLogic.demand_bound(&adapted, &wrapped), bound);
    let verified = DefaultResourceLogic.verify_demand_bound(&native, signature, &bound);
    let mut supplies = vec![ResourceMultiset::default()];
    if let Some(reservation) = &verified {
        supplies.push(reservation.clone());
        let mut surplus = reservation.clone();
        surplus.0.insert(Sig::Ground(vec![99]).key(), u64::MAX);
        supplies.push(surplus);
        for (&lane, &amount) in &reservation.0 {
            let mut deficient = reservation.clone();
            deficient.0.insert(lane, amount - 1);
            supplies.push(deficient);
        }
    } else {
        supplies.push(ResourceMultiset::singleton(signature.key(), u64::MAX));
    }
    for supply in &supplies {
        assert_eq!(assert_claim_parity(&native, signature, &bound, supply), verified);
        assert_observation_and_formula_parity(&native, signature, supply);
    }
    bound
}

#[test]
fn native_resource_logic_parity_reuses_the_existing_funding_laws() {
    conformance::assert_funding_laws::<RhoGslt, _>(&DefaultResourceLogic);
    conformance::assert_funding_laws::<MettaGslt, _>(&MettaResourceLogic);
    for certified_upper_bound in 0..=16 {
        for unknown in [false, true] {
            let demand = DemandEntry { certified_upper_bound, unknown };
            for supply in -2..=18 {
                assert_eq!(
                    MettaResourceLogic.is_funded(&demand, supply),
                    DefaultResourceLogic.is_funded(&demand, supply),
                );
            }
        }
    }
}

#[test]
fn native_resource_logic_parity_preserves_signature_keys_and_decompositions() {
    for signature in signatures() {
        let wrapped = MettaSig(signature.clone());
        assert_eq!(wrapped.key(), signature.key());
        let mut native = Vec::new();
        let mut adapted = Vec::new();
        signature.split_join_decompositions(&mut native);
        wrapped.split_join_decompositions(&mut adapted);
        assert_eq!(adapted, native);
    }
}

#[test]
fn native_resource_logic_parity_covers_finite_cost_carrier_grid() {
    let carriers = [
        ground(7),
        CostSignature { value: Some(SignatureValue::Unit(true)) },
        CostSignature {
            value: Some(SignatureValue::Quote(Par::default())),
        },
        CostSignature {
            value: Some(SignatureValue::Name(Par::default())),
        },
        compound_cost_signatures(&ground(7), &ground(8)).expect("native compound signature"),
    ];
    for signature in signatures() {
        for count in 0..=3 {
            assert!(matches!(
                assert_program_parity(&sends(count), &signature),
                DemandBound::FiniteUpperBound { .. }
            ));
            for carrier in &carriers {
                for depth in 1..=3 {
                    let mut program = sends(count);
                    for _ in 0..depth {
                        program = signed(program, carrier.clone());
                    }
                    assert!(matches!(
                        assert_program_parity(&program, &signature),
                        DemandBound::FiniteUpperBound { .. }
                    ));
                }
            }
        }
        for count in 1..=3 {
            for target in [
                ground(7),
                CostSignature {
                    value: Some(SignatureValue::BoundLevel(0)),
                },
            ] {
                assert!(matches!(
                    assert_program_parity(&stack(vec![target; count]), &signature),
                    DemandBound::FiniteUpperBound { .. }
                ));
            }
        }
    }
}

#[test]
fn native_resource_logic_parity_rejects_every_unprovable_reason() {
    let mut persistent_send = sends(1);
    persistent_send.sends[0].persistent = true;
    let mut persistent_receive = Par::default();
    persistent_receive.receives.push(Receive {
        persistent: true,
        body: Some(Par::default()),
        ..Receive::default()
    });
    let mut dequotation = Par::default();
    dequotation.exprs.push(Expr {
        expr_instance: Some(ExprInstance::EVarBody(EVar {
            v: Some(Var {
                var_instance: Some(VarInstance::BoundVar(0)),
            }),
        })),
    });
    let corpus = [
        (persistent_send, UnprovableDemand::UnboundedControlFlow),
        (persistent_receive, UnprovableDemand::UnboundedControlFlow),
        (dequotation, UnprovableDemand::RecursiveDequotation),
        (
            signed(
                sends(1),
                CostSignature {
                    value: Some(SignatureValue::BoundLevel(0)),
                },
            ),
            UnprovableDemand::DynamicAuthority,
        ),
        (
            signed(sends(1), CostSignature { value: None }),
            UnprovableDemand::UnsupportedSyntax,
        ),
        (stack(vec![]), UnprovableDemand::UnsupportedSyntax),
        (
            stack(vec![CostSignature { value: Some(SignatureValue::Unit(true)) }]),
            UnprovableDemand::UnsupportedSyntax,
        ),
    ];
    for signature in signatures() {
        for (program, reason) in &corpus {
            assert_eq!(
                assert_program_parity(program, &signature),
                DemandBound::Unprovable(reason.clone())
            );
            let supply = ResourceMultiset::singleton(signature.key(), u64::MAX);
            let finite_claim = DefaultResourceLogic.demand_bound(&sends(1), &signature);
            for claim in [
                DemandBound::Exact(ResourceMultiset::default()),
                finite_claim,
                DemandBound::Unprovable(reason.clone()),
            ] {
                assert_eq!(assert_claim_parity(program, &signature, &claim, &supply), None);
                assert!(!MettaResourceLogic.is_funded_bound(
                    program,
                    &MettaSig(signature.clone()),
                    &claim,
                    &supply,
                ));
            }
            assert_eq!(
                MettaResourceLogic.check_formula(
                    program,
                    &MettaSig(signature.clone()),
                    &supply,
                    &Formula::True
                ),
                Err(CheckError::Unprovable(reason.clone())),
            );
        }
    }
}

#[test]
fn native_resource_logic_parity_authenticates_evidence_kind_amount_lane_and_proof() {
    let program = sends(3);
    let signature = Sig::Ground(vec![31]);
    let claim = assert_program_parity(&program, &signature);
    let DemandBound::FiniteUpperBound { bound, proof } = claim else {
        panic!("native structural analysis produces a finite upper bound")
    };
    let supply = ResourceMultiset::singleton(signature.key(), u64::MAX);
    let mut mutations = vec![
        DemandBound::Exact(bound.clone()),
        DemandBound::Unprovable(UnprovableDemand::UnsupportedSyntax),
        DemandBound::FiniteUpperBound {
            bound: ResourceMultiset::default(),
            proof: proof.clone(),
        },
        DemandBound::FiniteUpperBound { bound: bound.clone(), proof: vec![] },
    ];
    for amount in [1, 2, 4, u64::MAX] {
        mutations.push(DemandBound::FiniteUpperBound {
            bound: ResourceMultiset::singleton(signature.key(), amount),
            proof: proof.clone(),
        });
    }
    mutations.push(DemandBound::FiniteUpperBound {
        bound: ResourceMultiset::singleton(Sig::Ground(vec![32]).key(), 3),
        proof: proof.clone(),
    });
    for index in 0..proof.len() {
        let mut altered = proof.clone();
        altered[index] ^= 1;
        mutations.push(DemandBound::FiniteUpperBound { bound: bound.clone(), proof: altered });
    }
    let mut appended = proof.clone();
    appended.push(0);
    mutations.push(DemandBound::FiniteUpperBound { bound: bound.clone(), proof: appended });
    for claim in mutations {
        assert_eq!(assert_claim_parity(&program, &signature, &claim, &supply), None);
        assert!(!MettaResourceLogic.is_funded_bound(
            &program,
            &MettaSig(signature.clone()),
            &claim,
            &supply
        ));
    }
}

#[test]
fn native_resource_logic_parity_recomputes_canonical_program_and_deploy_signature() {
    let signature = Sig::Ground(vec![41]);
    let program = sends(2);
    let claim = DefaultResourceLogic.demand_bound(&program, &signature);
    let supply = ResourceMultiset::singleton(signature.key(), u64::MAX);
    for count in [0, 1, 3, 4] {
        assert_eq!(assert_claim_parity(&sends(count), &signature, &claim, &supply), None);
    }
    assert_eq!(assert_claim_parity(&program, &Sig::Ground(vec![42]), &claim, &supply), None);

    let mut same_demand = program.clone();
    same_demand.sends[0].chan = Some(models::par_from_default! {
        exprs: vec![Expr { expr_instance: Some(ExprInstance::GInt(73)) }],
        ..Par::default()
    });
    assert_ne!(same_demand, program);
    assert_eq!(DefaultResourceLogic.demand_bound(&same_demand, &signature), claim);
    assert!(assert_claim_parity(&same_demand, &signature, &claim, &supply).is_some());
}

#[test]
fn native_resource_logic_parity_requires_each_lane_and_preserves_supply_monotonicity() {
    let signature = Sig::Ground(vec![51]);
    let left = cost_signature_to_sig(&ground(7))
        .expect("left native lane")
        .key();
    let right = cost_signature_to_sig(&ground(8))
        .expect("right native lane")
        .key();
    for left_count in 1..=3 {
        for right_count in 1..=3 {
            let mut program = signed(sends(left_count), ground(7));
            let mut other = signed(sends(right_count), ground(8));
            program
                .cost_signed_terms
                .append(&mut other.cost_signed_terms);
            let claim = assert_program_parity(&program, &signature);
            let reservation = DefaultResourceLogic
                .verify_demand_bound(&program, &signature, &claim)
                .expect("native certified reservation");
            assert_eq!(reservation.0.len(), 2);
            for left_supply in 0..=4 {
                for right_supply in 0..=4 {
                    let supply = ResourceMultiset::singleton(left, left_supply)
                        .checked_add(&ResourceMultiset::singleton(right, right_supply))
                        .expect("finite supply");
                    assert_eq!(
                        assert_claim_parity(&program, &signature, &claim, &supply),
                        Some(reservation.clone())
                    );
                    let funded = MettaResourceLogic.is_funded_bound(
                        &program,
                        &MettaSig(signature.clone()),
                        &claim,
                        &supply,
                    );
                    assert_eq!(funded, supply.dominates(&reservation));
                    let larger = supply
                        .checked_add(&ResourceMultiset::singleton(left, 1))
                        .expect("finite supply increase");
                    if funded {
                        assert!(MettaResourceLogic.is_funded_bound(
                            &program,
                            &MettaSig(signature.clone()),
                            &claim,
                            &larger
                        ));
                    }
                }
            }
        }
    }
}

#[test]
fn native_resource_logic_parity_keeps_observation_distinct_from_gross_demand() {
    let signature = Sig::Ground(vec![61]);
    let target = ground(7);
    let target_lane = cost_signature_to_sig(&target)
        .expect("native target lane")
        .key();
    let mut program = stack(vec![target.clone()]);
    let mut consumer = signed(Par::default(), target);
    program
        .cost_signed_terms
        .append(&mut consumer.cost_signed_terms);
    let claim = assert_program_parity(&program, &signature);
    let reservation = DefaultResourceLogic
        .verify_demand_bound(&program, &signature, &claim)
        .expect("gross demand remains certified");
    assert_eq!(reservation.get(&signature.key()), 1);
    assert_eq!(reservation.get(&target_lane), 1);
    let supply = ResourceMultiset::singleton(signature.key(), 1);
    let observation = MettaResourceLogic
        .resource_observation(&program, &MettaSig(signature.clone()), &supply)
        .expect("host observation accounts for the backed transfer");
    assert_eq!(observation.available, supply);
    assert_eq!(observation.demand, DemandKnowledge::UpperBound(supply.clone()));
    assert_eq!(observation.available.get(&target_lane), 0);
    assert_observation_and_formula_parity(&program, &signature, &supply);
    assert_eq!(
        MettaResourceLogic.check_formula(
            &program,
            &MettaSig(signature),
            &supply,
            &Formula::Available { surface: target_lane, amount: 1 }
        ),
        Err(CheckError::Unsatisfied),
    );
}

#[test]
fn native_resource_logic_parity_preserves_modal_uncertainty_and_surface_scopes() {
    let signature = Sig::Ground(vec![71]);
    let wrapped = MettaSig(signature.clone());
    let lane = signature.key();
    let other = Sig::Ground(vec![72]).key();
    let program = sends(1);
    let supply = ResourceMultiset::singleton(lane, 2);
    for formula in [
        Formula::Required { surface: lane, amount: 1 },
        Formula::Not(Box::new(Formula::Required { surface: lane, amount: 1 })),
        Formula::linear(lane),
        Formula::relevant(lane),
        Formula::Spend {
            grade: ResourceMultiset::singleton(lane, 1),
            continuation: Box::new(Formula::True),
        },
    ] {
        assert_eq!(
            DefaultResourceLogic.check_formula(&program, &signature, &supply, &formula),
            Err(CheckError::Indeterminate)
        );
        assert_eq!(
            MettaResourceLogic.check_formula(&program, &wrapped, &supply, &formula),
            Err(CheckError::Indeterminate)
        );
    }
    for formula in [
        Formula::Located {
            surface: lane,
            body: Box::new(Formula::Available { surface: other, amount: 1 }),
        },
        Formula::Spatial(Box::new(Formula::copyable(lane)), Box::new(Formula::copyable(lane))),
        Formula::Spend {
            grade: ResourceMultiset::default(),
            continuation: Box::new(Formula::True),
        },
    ] {
        assert_eq!(
            DefaultResourceLogic.check_formula(&program, &signature, &supply, &formula),
            Err(CheckError::Unsatisfied)
        );
        assert_eq!(
            MettaResourceLogic.check_formula(&program, &wrapped, &supply, &formula),
            Err(CheckError::Unsatisfied)
        );
    }
    let short = ResourceMultiset::default();
    let sufficient = Formula::Sufficient { surface: lane };
    assert_eq!(
        MettaResourceLogic.check_formula(&program, &wrapped, &short, &sufficient),
        Err(CheckError::Indeterminate)
    );
    assert_eq!(
        MettaResourceLogic.check_formula(&program, &wrapped, &supply, &sufficient),
        Ok(())
    );
}

#[test]
fn native_resource_logic_parity_preserves_sufficient_evidence_strength() {
    let signature = Sig::Ground(vec![81]);
    let wrapped = MettaSig(signature.clone());
    let lane = signature.key();
    let sufficient = Formula::Sufficient { surface: lane };
    let negated = Formula::Not(Box::new(sufficient.clone()));
    for count in 0..=16 {
        let program = sends(count);
        let upper = u64::try_from(count).expect("finite send count");
        for amount in 0..=18 {
            let supply = ResourceMultiset::singleton(lane, amount);
            let expected = if amount >= upper {
                Ok(())
            } else {
                Err(CheckError::Indeterminate)
            };
            let expected_negated = if amount >= upper {
                Err(CheckError::Unsatisfied)
            } else {
                Err(CheckError::Indeterminate)
            };
            for (formula, expected) in [(&sufficient, expected), (&negated, expected_negated)] {
                assert_eq!(
                    DefaultResourceLogic.check_formula(&program, &signature, &supply, formula),
                    expected
                );
                assert_eq!(
                    MettaResourceLogic.check_formula(&program, &wrapped, &supply, formula),
                    expected
                );
            }
            let exact = oslf::ResourceObservation::exact(
                supply.clone(),
                ResourceMultiset::singleton(lane, upper),
            );
            let expected_exact = if amount >= upper {
                Ok(())
            } else {
                Err(CheckError::Unsatisfied)
            };
            assert_eq!(oslf::check(&exact, &sufficient), expected_exact);
            let expected_exact_negated = if amount >= upper {
                Err(CheckError::Unsatisfied)
            } else {
                Ok(())
            };
            assert_eq!(oslf::check(&exact, &negated), expected_exact_negated);
            if amount < upper {
                let exact_zero =
                    oslf::ResourceObservation::exact(supply, ResourceMultiset::default());
                assert_eq!(oslf::check(&exact_zero, &sufficient), Ok(()));
            }
        }
    }
}
