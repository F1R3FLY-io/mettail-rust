//! OSLF conformance laws — the linear-resource-logic laws the Rocq
//! `OSLF_Funding_Logic_Sound` capstone proves, that EVERY `OslfResourceLogic`
//! implementation must satisfy.
//!
//! **Why these are re-hosted here (decision B1-a).** f1r3node-rust's own
//! conformance laws live in a `#[cfg(test)]` module
//! (`rholang/src/rust/interpreter/accounting/resource_logic.rs:120-209`) and are
//! private `fn`s, and its acceptance seam `admit_by_funding_with_logic<L>` is
//! fixed to `OslfResourceLogic<RhoGslt>` — so they cannot be invoked cross-crate
//! against `OslfResourceLogic<MettaGslt>`. This module is a FAITHFUL transcription
//! of those four generic laws (same assertions, same coverage grid), exposed as
//! `pub fn`s generic over `<G: GsltPresentation, R: OslfResourceLogic<G>>` so the
//! MeTTaIL adapter is checked against the identical contract. (Promoting the
//! host's laws to a `pub` conformance kit + a `G`-generic gate seam upstream is
//! B1-b, deferred to M-RHO.1 since it changes a f1r3node runtime path.)
//!
//! The Rust laws here are mirrored by the zero-admission Rocq proof
//! `formal/rocq/rho_bridge/theories/MettaOslfLawsConformance.v` (a second instance
//! of `GSLTOSLFCapstone.v`, reusing `LinearLogicResources.v`).

use rholang::rust::interpreter::accounting::delta_sigma::DemandEntry;
use rholang::rust::interpreter::accounting::resource_logic::{GsltPresentation, OslfResourceLogic};

/// A fully-resolvable demand with known lower bound `lower` (no `unknown`
/// over-approximation).
fn resolvable(lower: i64) -> DemandEntry {
    DemandEntry {
        known_lower_bound: lower,
        unknown: false,
    }
}

/// Law (sound proof-checker, both directions): funded iff `Σ ≥ Δ + margin`.
pub fn law_sound<G, R>(rl: &R)
where
    G: GsltPresentation,
    R: OslfResourceLogic<G>,
{
    for &lower in &[0i64, 1, 5, 100] {
        for &supply in &[0i64, 1, 5, 100, 101] {
            for &margin in &[0i64, 1, 10] {
                let d = resolvable(lower);
                let funded = rl.is_funded(&d, supply, margin);
                assert_eq!(
                    funded,
                    i128::from(supply) >= i128::from(lower) + i128::from(margin),
                    "funds judgment must be Σ ≥ Δ + margin (lower={lower}, supply={supply}, margin={margin})"
                );
            }
        }
    }
}

/// Law (reject underfunded): a positive demand against zero supply at zero margin
/// is rejected — the Rust mirror of `strict_reject_when_underfunded`.
pub fn law_reject_underfunded<G, R>(rl: &R)
where
    G: GsltPresentation,
    R: OslfResourceLogic<G>,
{
    assert!(!rl.is_funded(&resolvable(1), 0, 0));
    assert!(!rl.is_funded(&resolvable(7), 0, 0));
}

/// Law (no contraction / supply monotone): increasing supply never turns a funded
/// demand UNfunded — the operational image of `ll_linear_no_contraction`.
pub fn law_supply_monotone<G, R>(rl: &R)
where
    G: GsltPresentation,
    R: OslfResourceLogic<G>,
{
    for &lower in &[0i64, 3, 50] {
        for &margin in &[0i64, 2] {
            for supply in 0i64..60 {
                if rl.is_funded(&resolvable(lower), supply, margin) {
                    assert!(
                        rl.is_funded(&resolvable(lower), supply + 1, margin),
                        "is_funded must be monotone in supply (lower={lower}, supply={supply}, margin={margin})"
                    );
                }
            }
        }
    }
}

/// Law (decidable): the check always returns a verdict (a total function).
pub fn law_decidable<G, R>(rl: &R)
where
    G: GsltPresentation,
    R: OslfResourceLogic<G>,
{
    let _verdict: bool = rl.is_funded(&resolvable(3), 5, 0);
}

/// Run all four OSLF conformance laws against `rl` (for GSLT presentation `G`).
pub fn assert_oslf_laws<G, R>(rl: &R)
where
    G: GsltPresentation,
    R: OslfResourceLogic<G>,
{
    law_sound::<G, _>(rl);
    law_reject_underfunded::<G, _>(rl);
    law_supply_monotone::<G, _>(rl);
    law_decidable::<G, _>(rl);
}
