//! `MettaGslt` — the MeTTaIL GSLT presentation for f1r3node-rust's funding
//! analysis (the second `GsltPresentation` instance after the host's `RhoGslt`,
//! demonstrating the trait's genericity for MeTTaIL).
//!
//! This adapter presents an already-lowered Rholang `Par` to the host's
//! `delta_sigma::desugar_for_funding` and delegates analysis to
//! [`crate::logic::MettaResourceLogic`]. It does not project arbitrary guest
//! `Cost(G)` grades, certify a cost transition, or turn a source `Par` into a
//! funding witness. Those require the checked, fingerprint-bound guest cost
//! image and a separate host projection before the existing admission gate.

use models::rhoapi::Par;

use rholang::rust::interpreter::accounting::authority::UnprovableDemand;
use rholang::rust::interpreter::accounting::delta_sigma::{self, SigKey};
use rholang::rust::interpreter::accounting::resource_logic::{
    GsltPresentation, ResourceDecomposition, ResourceSignature,
};
use rholang::rust::interpreter::accounting::Sig;

/// An already-lowered Rholang program presented for host funding analysis.
/// This wrapper is not a checked `Cost(G)` program or resource certificate.
#[derive(Clone, Debug, Default, PartialEq)]
pub struct MettaProgram(pub Par);

/// A MeTTaIL deploy signature. Wraps the host [`Sig`] so funding reuses the
/// verified `delta_sigma` lane decomposition (`split_join_decompositions`) — the
/// deploy-authority structure is the host's, MeTTaIL only re-presents it.
#[derive(Clone, Debug)]
pub struct MettaSig(pub Sig);

impl ResourceSignature for MettaSig {
    type Key = SigKey;

    #[inline]
    fn key(&self) -> Self::Key {
        // Delegate to the host `Sig`'s `ResourceSignature` impl (lane hash).
        ResourceSignature::key(&self.0)
    }

    #[inline]
    fn split_join_decompositions(&self, out: &mut Vec<ResourceDecomposition<Self::Key>>) {
        // The split/join (⊗) decompositions are the host `Sig`'s — MeTTaIL reuses
        // the verified lane algebra rather than inventing its own.
        ResourceSignature::split_join_decompositions(&self.0, out)
    }
}

/// The Rholang-target presentation of a MeTTaIL-produced `Par`.
/// Canonicalization is checked at the trait boundary; this specialization is
/// total because it only desugars an existing host `Par`.
#[derive(Clone, Copy, Debug, Default)]
pub struct MettaGslt;

impl GsltPresentation for MettaGslt {
    type Program = MettaProgram;
    type CanonicalProgram = Par;
    type Signature = MettaSig;

    #[inline]
    fn canonicalize_for_funding(&self, program: &MettaProgram) -> Result<Par, UnprovableDemand> {
        Ok(delta_sigma::desugar_for_funding(&program.0))
    }
}
