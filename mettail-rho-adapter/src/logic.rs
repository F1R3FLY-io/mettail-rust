//! `MettaResourceLogic` — MeTTaIL's OSLF resource logic (proof checker for the
//! funding judgment `Σ_s ≥ Δ_s`).
//!
//! It DELEGATES `demand`/`is_funded` to the already-verified pure analyzer
//! `delta_sigma::{demand,is_funded}` — the same analyzer f1r3node-rust's built-in
//! [`DefaultResourceLogic`] and the live D2 acceptance gate use — so the MeTTaIL
//! adapter and the host gate cannot diverge, and the OSLF conformance laws (see
//! [`crate::conformance`]) hold by delegation (the Rocq `OSLF_Funding_Logic_Sound`
//! capstone's image; cf. `formal/rocq/rho_bridge/theories/MettaOslfLawsConformance.v`).
//!
//! MeTTaIL-specific cost extensions (the Δ1 N-ary min-cost-matching join, the
//! two-axis refutation/ordering split) layer on in M-RHO.3 by making `demand`
//! compute more than a pure delegation; for the funding gate, full delegation is
//! the correct, sound, conformant baseline.

use models::rhoapi::Par;

use rholang::rust::interpreter::accounting::delta_sigma::{self, DemandEntry};
use rholang::rust::interpreter::accounting::resource_logic::OslfResourceLogic;

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
    fn is_funded(&self, analysis: &DemandEntry, effective_supply_s: i64, margin: i64) -> bool {
        delta_sigma::is_funded(analysis, effective_supply_s, margin)
    }
}
