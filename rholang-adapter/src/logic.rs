//! `MettaResourceLogic` — MeTTaIL's funding resource logic, its `OslfResourceLogic`
//! impl (proof checker for the
//! funding judgment `Σ_s ≥ Δ_s`).
//!
//! It delegates demand, certified-bound verification, located OSLF observation,
//! and funding decisions to the host's `DefaultResourceLogic`/`delta_sigma`
//! implementation. This establishes analyzer parity, not a live admission
//! call. An unknown structural demand has no finite proof and is rejected,
//! rather than being guessed with a numeric margin. See [`crate::conformance`] and
//! `formal/rocq/rho_bridge/theories/MettaFundingLawsConformance.v`.
//!
//! MeTTaIL-specific candidate ordering is implemented in [`crate::delta1`].
//! This keeps the host funding judgment pure: `demand`/`is_funded` decide
//! refutation, and Delta-one selection ranks the enabled join candidates without
//! changing the funding law.

use models::rhoapi::Par;

use rholang::rust::interpreter::accounting::authority::{DemandBound, ResourceMultiset};
use rholang::rust::interpreter::accounting::delta_sigma::{self, DemandEntry, SigKey};
use rholang::rust::interpreter::accounting::oslf::{CheckError, ResourceObservation};
use rholang::rust::interpreter::accounting::resource_logic::{
    DefaultResourceLogic, OslfResourceLogic, RhoGslt,
};

use crate::gslt::{MettaGslt, MettaSig};

/// MeTTaIL's proof checker for the funding judgment, delegating to the verified
/// `delta_sigma` analyzer (cf. f1r3node-rust's `DefaultResourceLogic`).
#[derive(Clone, Copy, Debug, Default)]
pub struct MettaResourceLogic;

impl OslfResourceLogic<MettaGslt> for MettaResourceLogic {
    #[inline]
    fn demand(&self, canonical: &Par, deploy_sig: &MettaSig) -> DemandEntry {
        delta_sigma::demand(canonical, &deploy_sig.0)
    }

    #[inline]
    fn demand_bound(&self, canonical: &Par, deploy_sig: &MettaSig) -> DemandBound<SigKey> {
        OslfResourceLogic::<RhoGslt>::demand_bound(&DefaultResourceLogic, canonical, &deploy_sig.0)
    }

    #[inline]
    fn verify_demand_bound(
        &self,
        canonical: &Par,
        deploy_sig: &MettaSig,
        bound: &DemandBound<SigKey>,
    ) -> Option<ResourceMultiset<SigKey>> {
        OslfResourceLogic::<RhoGslt>::verify_demand_bound(
            &DefaultResourceLogic,
            canonical,
            &deploy_sig.0,
            bound,
        )
    }

    #[inline]
    fn resource_observation(
        &self,
        canonical: &Par,
        deploy_sig: &MettaSig,
        authenticated_supply: &ResourceMultiset<SigKey>,
    ) -> Result<ResourceObservation<SigKey>, CheckError> {
        OslfResourceLogic::<RhoGslt>::resource_observation(
            &DefaultResourceLogic,
            canonical,
            &deploy_sig.0,
            authenticated_supply,
        )
    }

    #[inline]
    fn is_funded(&self, analysis: &DemandEntry, effective_supply_s: i64) -> bool {
        delta_sigma::is_funded(analysis, effective_supply_s)
    }
}

#[cfg(test)]
mod cost_grade_template_tests {
    use super::*;
    use models::rhoapi::{cost_signature::Value, CostSignature, CostSignedTerm};
    use rholang::rust::interpreter::accounting::authority::{
        compound_cost_signatures, cost_signature_to_sig,
    };
    use rholang::rust::interpreter::accounting::Sig;

    fn atom(tag: u8) -> CostSignature {
        CostSignature { value: Some(Value::Ground(vec![tag])) }
    }

    fn signed_empty(signature: CostSignature) -> Par {
        models::par_from_default! {
            cost_signed_terms: vec![CostSignedTerm {
                body: Some(Par::default()),
                signature: Some(signature),
            }],
            ..Par::default()
        }
    }

    #[test]
    fn finite_grade_signature_template_agrees_with_host_bound() {
        let deploy = Sig::Unit;
        let metta = MettaResourceLogic;
        let host = DefaultResourceLogic;
        let unit = Par::default();
        let unit_bound = metta.demand_bound(&unit, &MettaSig(deploy.clone()));
        assert_eq!(unit_bound, OslfResourceLogic::<RhoGslt>::demand_bound(&host, &unit, &deploy),);
        let DemandBound::FiniteUpperBound { bound, .. } = unit_bound else {
            panic!("unit grade must have a finite bound");
        };
        assert!(bound.0.is_empty(), "unit grade has no signature demand");

        let a = atom(1);
        let b = atom(2);
        let certified_generator_lane = CostSignature {
            value: Some(Value::Quote(Par::default())),
        };
        let ab = compound_cost_signatures(&a, &b).unwrap();
        let ba = compound_cost_signatures(&b, &a).unwrap();
        assert_eq!(ab, ba, "signature product must canonicalize commutatively");
        let nested_left = compound_cost_signatures(&ab, &a).unwrap();
        let nested_right = compound_cost_signatures(&a, &ba).unwrap();
        assert_eq!(nested_left, nested_right, "signature product must canonicalize associatively",);
        for signature in [certified_generator_lane, a, ab, nested_left] {
            let par = signed_empty(signature.clone());
            let metta_bound = metta.demand_bound(&par, &MettaSig(deploy.clone()));
            let host_bound = OslfResourceLogic::<RhoGslt>::demand_bound(&host, &par, &deploy);
            assert_eq!(metta_bound, host_bound);
            let DemandBound::FiniteUpperBound { bound, .. } = metta_bound else {
                panic!("fixed signed template must have a finite bound");
            };
            let lane = cost_signature_to_sig(&signature).unwrap().lane_hash();
            assert_eq!(bound.get(&lane), 1, "one unit-layer on the compound lane");
            assert_eq!(bound.0.len(), 1, "no guest-derived supply is introduced");
        }
    }
}
