//! `MettaGslt` — the MeTTaIL GSLT presentation for f1r3node-rust's OSLF funding
//! analysis (the second `GsltPresentation` instance after the host's `RhoGslt`,
//! demonstrating the trait's genericity for MeTTaIL).
//!
//! MeTTaIL compiles a GSLT to a Rholang program; this presents that program for
//! funding by canonicalizing it to a Rholang `Par` (via the host's VERIFIED
//! `delta_sigma::desugar_for_funding`). The funding ANALYSIS proper is delegated
//! to `delta_sigma` in [`crate::logic::MettaResourceLogic`], so the MeTTaIL
//! adapter and the live f1r3node D2 acceptance gate share one analyzer and cannot
//! diverge.

use models::rhoapi::Par;

use rholang::rust::interpreter::accounting::delta_sigma::{self, SigKey};
use rholang::rust::interpreter::accounting::resource_logic::{
    GsltPresentation, ResourceDecomposition, ResourceSignature,
};
use rholang::rust::interpreter::accounting::Sig;

/// A MeTTaIL program compiled (by `mettail-rho-codegen`) to a Rholang `Par`,
/// presented for funding analysis. A distinct `Program` type from
/// `RhoGslt::Program` so the trait's genericity over GSLT presentations is
/// exercised for MeTTaIL; the funding analysis itself reuses the verified host
/// path (see the module docs).
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

/// The MeTTaIL GSLT presentation: a MeTTaIL program canonicalized to a Rholang
/// `Par` for funding via the host's verified `desugar_for_funding`.
#[derive(Clone, Copy, Debug, Default)]
pub struct MettaGslt;

impl GsltPresentation for MettaGslt {
    type Program = MettaProgram;
    type CanonicalProgram = Par;
    type Signature = MettaSig;

    #[inline]
    fn canonicalize_for_funding(&self, program: &MettaProgram) -> Par {
        delta_sigma::desugar_for_funding(&program.0)
    }
}
