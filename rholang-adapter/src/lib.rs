//! # mettail-rho-adapter — the `OslfResourceLogic<MettaGslt>` bridge
//!
//! MeTTaIL compiles GSLTs for f1r3node-rust's Rholang runtime. This crate
//! implements the host trait `OslfResourceLogic<MettaGslt>` for an
//! already-lowered Rholang `Par`. Its demand, bound verification, located OSLF
//! observation, and funding verdict delegate to the host's `delta_sigma`
//! analyzer. This is pure analysis: it does not access RSpace or execute a
//! deploy.
//!
//! The production offered-funded path does not currently call this adapter.
//! In particular, trait conformance does not project a guest `Cost(G)` grade,
//! authenticate supply, or settle a deploy. The installed grade-to-host
//! projection and a host-owned admission call must complete that boundary.
//!
//! ## Dependency direction
//! This crate depends on f1r3node-rust (`models`, `rholang`). The host
//! `rholang` and `casper` crates do not depend on this adapter. The node
//! composition root may connect the two sides without reversing that edge.
//! `formal/rocq/rho_bridge/theories/BridgeInertness.v` models the intended
//! acyclic boundary; it does not prove the current Cargo graph or a live
//! offered-funded integration.
//!
//! ## Contents
//! - [`ambiguity`] — exact-key ambiguity witness collection: scheduler order
//!   may choose execution order, not which enabled alternatives remain
//!   observable.
//! - [`delta1`] — Delta-one join-candidate selection and exact bipartite
//!   matching with separate refutation and ordering axes.
//! - [`gslt`] — `MettaGslt` (`GsltPresentation`, `CanonicalProgram = Par`),
//!   `MettaSig` (`ResourceSignature` over the host lane algebra), `MettaProgram`.
//! - [`logic`] — `MettaResourceLogic` (`OslfResourceLogic<MettaGslt>`),
//!   delegating every resource-evidence method to `DefaultResourceLogic`.
//! - [`settlement`] — Δ4 escrow/refund settlement for guarded candidates:
//!   reserve before commit, charge only on commit, refund on failure; includes
//!   `LocatedEscrowLedger` for Δ3 per-purse deterministic settlement.
//! - [`conformance`] — four funding linear-logic laws checked for
//!   `MettaResourceLogic`; mirrored by
//!   `formal/rocq/rho_bridge/theories/MettaFundingLawsConformance.v`.
//!
//! The cost axis is two-fold (vindicated by the cost-accounting papers' R-C
//! obstruction): the **refutation** axis (`is_funded`'s verdict; unprovable
//! structural demand rejects) and the **ordering** axis (demand magnitude;
//! rank-only, never inventing a funding proof).
//! The Delta-one selectors in [`delta1`] apply that split to MeTTaIL's n-ary
//! join candidates and finite matching frontiers without collapsing equal-cost
//! semantic alternatives.

#![forbid(unsafe_code)]

pub mod ambiguity;
pub mod conformance;
pub mod delta1;
pub mod gslt;
pub mod logic;
pub mod settlement;

pub use ambiguity::{
    ambiguity_observes_key, collect_enabled_ambiguity_witnesses, AmbiguityCandidate,
    AmbiguityWitnessConflict, AmbiguityWitnessSet,
};
pub use delta1::{
    delta1_selects_index, delta1_selects_left_perfect_matching_indices,
    select_delta1_min_cost_left_perfect_matchings, select_delta1_minima, DeltaOneCandidate,
    DeltaOneMatchEdge, DeltaOneMatching,
};
pub use gslt::{MettaGslt, MettaProgram, MettaSig};
pub use logic::MettaResourceLogic;
pub use settlement::{
    commit_escrow, refund_escrow, reserve_escrow, EscrowState, EscrowTicket, LedgerBlocker,
    LedgerSettlementStep, LocatedEscrowLedger, PurseId, SettlementAction, SettlementBlocker,
    SettlementStep,
};

#[cfg(test)]
mod tests {
    use super::*;
    use models::rhoapi::{
        cost_signature::Value as CostSignatureValue, CostSignature, CostSignedTerm, CostStack, Par,
    };
    use rholang::rust::interpreter::accounting::authority::{DemandBound, ResourceMultiset};
    use rholang::rust::interpreter::accounting::delta_sigma;
    use rholang::rust::interpreter::accounting::oslf::Formula;
    use rholang::rust::interpreter::accounting::resource_logic::{
        DefaultResourceLogic, GsltPresentation, OslfResourceLogic, ResourceSignature, RhoGslt,
    };
    use rholang::rust::interpreter::accounting::Sig;

    /// `MettaResourceLogic` satisfies all four funding conformance laws (the
    /// `OSLF_Funding_Logic_Sound` capstone's contract) — deliverable #2.
    #[test]
    fn metta_resource_logic_satisfies_funding_laws() {
        conformance::assert_funding_laws::<MettaGslt, _>(&MettaResourceLogic);
    }

    /// `MettaResourceLogic::demand` agrees with the free `delta_sigma::demand`
    /// over the canonicalized program. This checks analyzer parity, not
    /// production admission. `canonicalize_for_funding` uses the host path.
    #[test]
    fn metta_demand_delegates_to_delta_sigma() {
        let gslt = MettaGslt;
        let rl = MettaResourceLogic;
        let program = MettaProgram(Par::default());
        let sig = MettaSig(Sig::Ground(vec![1, 2, 3, 4]));
        let canonical = gslt
            .canonicalize_for_funding(&program)
            .expect("Rholang Par canonicalization is total");
        assert_eq!(rl.demand(&canonical, &sig), delta_sigma::demand(&canonical, &sig.0));
    }

    /// The adapter must not fall back to the trait's weaker default bound
    /// verifier. It delegates the host's actual certificate check and located
    /// observation, so the two GSLT presentations agree on the same `Par`.
    #[test]
    fn metta_bound_and_oslf_observation_match_host_checker() {
        let canonical = Par::default();
        let sig = MettaSig(Sig::Ground(vec![1, 2, 3, 4]));
        let adapter = MettaResourceLogic;
        let host = DefaultResourceLogic;
        let supply = ResourceMultiset::singleton(sig.key(), 3);
        let adapter_bound =
            OslfResourceLogic::<MettaGslt>::demand_bound(&adapter, &canonical, &sig);
        let host_bound = OslfResourceLogic::<RhoGslt>::demand_bound(&host, &canonical, &sig.0);
        assert_eq!(adapter_bound, host_bound);
        assert_eq!(
            OslfResourceLogic::<MettaGslt>::verify_demand_bound(
                &adapter,
                &canonical,
                &sig,
                &adapter_bound,
            ),
            OslfResourceLogic::<RhoGslt>::verify_demand_bound(
                &host,
                &canonical,
                &sig.0,
                &host_bound,
            ),
        );
        let forged = DemandBound::FiniteUpperBound {
            bound: ResourceMultiset::singleton(sig.key(), 999),
            proof: b"forged-cost-certificate".to_vec(),
        };
        assert_eq!(
            OslfResourceLogic::<MettaGslt>::verify_demand_bound(
                &adapter, &canonical, &sig, &forged,
            ),
            None,
            "the adapter must not accept a caller-supplied bound as proof",
        );
        assert_eq!(
            OslfResourceLogic::<MettaGslt>::resource_observation(
                &adapter, &canonical, &sig, &supply,
            ),
            OslfResourceLogic::<RhoGslt>::resource_observation(&host, &canonical, &sig.0, &supply,),
        );
        let formula = Formula::Sufficient { surface: sig.key() };
        assert_eq!(
            OslfResourceLogic::<MettaGslt>::check_formula(
                &adapter, &canonical, &sig, &supply, &formula,
            ),
            OslfResourceLogic::<RhoGslt>::check_formula(
                &host, &canonical, &sig.0, &supply, &formula,
            ),
        );
    }

    /// Rholang `Par` canonicalization is total and matches the host desugaring.
    #[test]
    fn metta_canonicalize_matches_host_desugar() {
        let gslt = MettaGslt;
        let par = Par::default();
        assert_eq!(
            gslt.canonicalize_for_funding(&MettaProgram(par.clone()))
                .expect("Rholang Par canonicalization is total"),
            delta_sigma::desugar_for_funding(&par)
        );
    }

    /// Finite structural property grid over the native signed-term and stack
    /// constructors. A guest adapter cannot silently reinterpret these cost
    /// carriers: its certificate and located judgment must be exactly the
    /// host judgment for each canonical program and authenticated supply.
    #[test]
    fn metta_signed_cost_carriers_match_host_resource_judgment() {
        let adapter = MettaResourceLogic;
        let host = DefaultResourceLogic;
        let gslt = MettaGslt;
        let signature = MettaSig(Sig::Ground(vec![1]));
        let lane = signature.key();
        let wire_ground = |tag| CostSignature {
            value: Some(CostSignatureValue::Ground(vec![tag])),
        };

        for signed_depth in 0..=3 {
            for stack_cells in 0..=3 {
                let mut par = models::par_from_default! {
                    cost_stacks: vec![CostStack {
                        cells: vec![wire_ground(8); stack_cells],
                        parallel_tail: Vec::new(),
                    }],
                    ..Par::default()
                };
                for depth in 0..signed_depth {
                    par = models::par_from_default! {
                        cost_signed_terms: vec![CostSignedTerm {
                            body: Some(par),
                            signature: Some(wire_ground(7 + depth)),
                        }],
                        ..Par::default()
                    };
                }
                let canonical = gslt
                    .canonicalize_for_funding(&MettaProgram(par.clone()))
                    .expect("native Rholang Par canonicalization is total");
                assert_eq!(canonical, delta_sigma::desugar_for_funding(&par));
                assert_eq!(
                    adapter.demand(&canonical, &signature),
                    host.demand(&canonical, &signature.0)
                );

                let adapter_bound =
                    OslfResourceLogic::<MettaGslt>::demand_bound(&adapter, &canonical, &signature);
                let host_bound =
                    OslfResourceLogic::<RhoGslt>::demand_bound(&host, &canonical, &signature.0);
                assert_eq!(adapter_bound, host_bound);
                assert_eq!(
                    OslfResourceLogic::<MettaGslt>::verify_demand_bound(
                        &adapter,
                        &canonical,
                        &signature,
                        &adapter_bound,
                    ),
                    OslfResourceLogic::<RhoGslt>::verify_demand_bound(
                        &host,
                        &canonical,
                        &signature.0,
                        &host_bound,
                    ),
                );

                for quantity in 0..=4 {
                    let supply = ResourceMultiset::singleton(lane, quantity);
                    assert_eq!(
                        OslfResourceLogic::<MettaGslt>::resource_observation(
                            &adapter, &canonical, &signature, &supply,
                        ),
                        OslfResourceLogic::<RhoGslt>::resource_observation(
                            &host,
                            &canonical,
                            &signature.0,
                            &supply,
                        ),
                    );
                }
            }
        }
    }
}
