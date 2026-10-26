//! Funding conformance laws for the finite structural-demand checker. An
//! unresolved demand has no certified upper bound and must fail closed; the
//! production gate may instead use independently checked state-bound evidence.
//!
//! The host's conformance harness is private to its crate and specialized to
//! `RhoGslt`. These generic checks apply the same current finite-bound law to
//! the `MettaGslt` instance without introducing a separate funding algorithm.
//!
//! The Rust laws here are mirrored by the zero-admission Rocq proof
//! `formal/rocq/rho_bridge/theories/MettaFundingLawsConformance.v` (a second instance
//! of `GSLTOSLFCapstone.v`, reusing `LinearLogicResources.v`).

use rholang::rust::interpreter::accounting::delta_sigma::DemandEntry;
use rholang::rust::interpreter::accounting::resource_logic::{GsltPresentation, OslfResourceLogic};

/// A fully-resolvable, certified finite upper bound.
fn resolvable(bound: i64) -> DemandEntry {
    DemandEntry {
        certified_upper_bound: bound,
        unknown: false,
    }
}

/// A demand without a certified finite bound, e.g. unresolved dequotation.
fn unresolvable(bound: i64) -> DemandEntry {
    DemandEntry {
        certified_upper_bound: bound,
        unknown: true,
    }
}

/// Sound finite-bound judgment: admit iff the certified bound fits supply;
/// unprovable demand rejects for every supply.
pub fn law_sound<G, R>(rl: &R)
where
    G: GsltPresentation,
    R: OslfResourceLogic<G>,
{
    for &bound in &[0i64, 1, 5, 100] {
        for &supply in &[0i64, 1, 5, 100, 101] {
            assert_eq!(
                rl.is_funded(&resolvable(bound), supply),
                i128::from(supply) >= i128::from(bound),
                "certified bound must fit supply (bound={bound}, supply={supply})"
            );
            assert!(
                !rl.is_funded(&unresolvable(bound), supply),
                "unknown demand must reject (bound={bound}, supply={supply})"
            );
        }
    }
}

/// Law (reject underfunded): a positive demand against zero supply
/// is rejected — the Rust mirror of `strict_reject_when_underfunded`.
pub fn law_reject_underfunded<G, R>(rl: &R)
where
    G: GsltPresentation,
    R: OslfResourceLogic<G>,
{
    assert!(!rl.is_funded(&resolvable(1), 0));
    assert!(!rl.is_funded(&resolvable(7), 0));
}

/// Law (no contraction / supply monotone): increasing supply never turns a funded
/// demand UNfunded — the operational image of `ll_linear_no_contraction`.
pub fn law_supply_monotone<G, R>(rl: &R)
where
    G: GsltPresentation,
    R: OslfResourceLogic<G>,
{
    for &bound in &[0i64, 3, 50] {
        for supply in 0i64..60 {
            if rl.is_funded(&resolvable(bound), supply) {
                assert!(
                    rl.is_funded(&resolvable(bound), supply + 1),
                    "is_funded must be monotone in supply (bound={bound}, supply={supply})"
                );
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
    let _verdict: bool = rl.is_funded(&resolvable(3), 5);
}

/// Run all four funding conformance laws against `rl` (for GSLT presentation `G`).
pub fn assert_funding_laws<G, R>(rl: &R)
where
    G: GsltPresentation,
    R: OslfResourceLogic<G>,
{
    law_sound::<G, _>(rl);
    law_reject_underfunded::<G, _>(rl);
    law_supply_monotone::<G, _>(rl);
    law_decidable::<G, _>(rl);
}
