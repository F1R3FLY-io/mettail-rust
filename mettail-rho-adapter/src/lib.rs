//! # mettail-rho-adapter — the `OslfResourceLogic<MettaGslt>` bridge
//!
//! M-RHO compiles MeTTaIL GSLTs onto f1r3node-rust's Rho machine: MeTTaIL is the
//! COMPILER, f1r3node-rust is the parallel RUNTIME. This crate is the
//! **cost/funding adapter**: it presents a MeTTaIL GSLT to f1r3node-rust's
//! resource logic by implementing the host trait `OslfResourceLogic<MettaGslt>`,
//! delegating `demand`/`is_funded` to the host's VERIFIED `delta_sigma` over a
//! canonicalized `Par`. It is **pure analysis** — no RSpace, no Tokio — so the
//! host's funding gate can consume it GENERICALLY, the way its own
//! `DenyLogic`/`ZeroDemandLogic` logics plug into
//! `admit_by_funding_with_logic<L: OslfResourceLogic<…>>`.
//!
//! ## Dependency direction (STRICTLY one-way)
//! This crate depends ONE-WAY on f1r3node-rust (`models`, `rholang`); f1r3node-rust
//! NEVER depends on mettail-rust. Enforced operationally by the host guard test
//! `mettail_rust_is_not_a_cargo_dependency`
//! (f1r3node-rust `rholang/.../accounting/resource_logic.rs:293`) and proven
//! internally consistent (acyclic + irreversible) in
//! `formal/rocq/rho_bridge/theories/BridgeInertness.v`.
//!
//! ## Contents
//! - [`delta1`] — Delta-one join-candidate selection with separate refutation
//!   and ordering axes.
//! - [`gslt`] — `MettaGslt` (`GsltPresentation`, `CanonicalProgram = Par`),
//!   `MettaSig` (`ResourceSignature` over the host lane algebra), `MettaProgram`.
//! - [`logic`] — `MettaResourceLogic` (`OslfResourceLogic<MettaGslt>`),
//!   delegating to the verified `delta_sigma::{demand,is_funded}`.
//! - [`settlement`] — Δ4 escrow/refund settlement for guarded candidates:
//!   reserve before commit, charge only on commit, refund on failure; includes
//!   `LocatedEscrowLedger` for Δ3 per-purse deterministic settlement.
//! - [`conformance`] — the four OSLF linear-logic laws (re-hosted, decision B1-a),
//!   proven green for `MettaResourceLogic`; mirrored by
//!   `formal/rocq/rho_bridge/theories/MettaOslfLawsConformance.v`.
//!
//! The cost axis is two-fold (vindicated by the cost-accounting papers' R-C
//! obstruction): the **refutation** axis (`is_funded`'s verdict; `0̄` = refuted)
//! and the **ordering** axis (`i64` demand magnitude; rank-only, never refutes).
//! The Delta-one selector in [`delta1`] applies that split to MeTTaIL's n-ary
//! join candidates without collapsing equal-cost semantic alternatives.

#![forbid(unsafe_code)]

pub mod conformance;
pub mod delta1;
pub mod gslt;
pub mod logic;
pub mod settlement;

pub use delta1::{delta1_selects_index, select_delta1_minima, DeltaOneCandidate};
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
    use models::rhoapi::Par;
    use rholang::rust::interpreter::accounting::delta_sigma;
    use rholang::rust::interpreter::accounting::resource_logic::{
        GsltPresentation, OslfResourceLogic,
    };
    use rholang::rust::interpreter::accounting::Sig;

    /// `MettaResourceLogic` satisfies all four OSLF conformance laws (the
    /// `OSLF_Funding_Logic_Sound` capstone's contract) — deliverable #2.
    #[test]
    fn metta_resource_logic_satisfies_oslf_laws() {
        conformance::assert_oslf_laws::<MettaGslt, _>(&MettaResourceLogic);
    }

    /// `MettaResourceLogic::demand` agrees with the free `delta_sigma::demand`
    /// over the canonicalized program — the adapter uses the SAME analyzer the
    /// live gate uses (no divergence), and `canonicalize_for_funding` desugars
    /// via the host path.
    #[test]
    fn metta_demand_delegates_to_delta_sigma() {
        let gslt = MettaGslt;
        let rl = MettaResourceLogic;
        let program = MettaProgram(Par::default());
        let sig = MettaSig(Sig::Ground(vec![1, 2, 3, 4]));
        let canonical = gslt.canonicalize_for_funding(&program);
        assert_eq!(rl.demand(&canonical, &sig), delta_sigma::demand(&canonical, &sig.0));
    }

    /// `canonicalize_for_funding` is total and matches the host desugaring.
    #[test]
    fn metta_canonicalize_matches_host_desugar() {
        let gslt = MettaGslt;
        let par = Par::default();
        assert_eq!(
            gslt.canonicalize_for_funding(&MettaProgram(par.clone())),
            delta_sigma::desugar_for_funding(&par)
        );
    }
}
