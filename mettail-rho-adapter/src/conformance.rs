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
//! MeTTaIL adapter is checked against the identical contract. Keeping the laws
//! local also avoids changing f1r3node's runtime acceptance path while preserving
//! a byte-for-byte-equivalent law suite for this bridge.
//!
//! The Rust laws here are mirrored by the zero-admission Rocq proof
//! `formal/rocq/rho_bridge/theories/MettaOslfLawsConformance.v` (a second instance
//! of `GSLTOSLFCapstone.v`, reusing `LinearLogicResources.v`).

use rholang::rust::interpreter::accounting::delta_sigma::DemandEntry;
use rholang::rust::interpreter::accounting::resource_logic::{GsltPresentation, OslfResourceLogic};

/// A fully-resolvable demand with known lower bound `lower` (no `unknown`
/// over-approximation).
fn resolvable(lower: i64) -> DemandEntry {
    DemandEntry { known_lower_bound: lower, unknown: false }
}

/// An over-approximated demand (`unknown == true`): a term with an unresolvable
/// dequotation `*x`, for which the Thm 20 safety margin applies.
fn unresolvable(lower: i64) -> DemandEntry {
    DemandEntry { known_lower_bound: lower, unknown: true }
}

/// Law (sound proof-checker, BOTH regimes): for RESOLVABLE demand the funds
/// judgment is EXACTLY Def 19 `Σ ≥ Δ` (the economic margin is INERT — it is not
/// folded into the resolvable-demand correctness gate, matching the verified Rocq
/// model `funds n d := d ≤ n`, which has no margin term); for OVER-APPROXIMATED
/// (`unknown`) demand the Thm 20 safety margin applies, `Σ ≥ Δ + margin`. This is
/// the faithful mirror of f1r3node-rust's `resource_logic::tests::law_sound`,
/// whose `is_funded` applies the margin only when `analysis.unknown` is `true`.
pub fn law_sound<G, R>(rl: &R)
where
    G: GsltPresentation,
    R: OslfResourceLogic<G>,
{
    for &lower in &[0i64, 1, 5, 100] {
        for &supply in &[0i64, 1, 5, 100, 101] {
            for &margin in &[0i64, 1, 10] {
                // Resolvable: Def 19 `Σ ≥ Δ` — margin NOT applied.
                let resolved = rl.is_funded(&resolvable(lower), supply, margin);
                assert_eq!(
                    resolved,
                    i128::from(supply) >= i128::from(lower),
                    "resolvable funds judgment must be Σ ≥ Δ (lower={lower}, supply={supply}, margin={margin})"
                );
                // Over-approximated: Thm 20 `Σ ≥ Δ + margin` — margin applied.
                let over = rl.is_funded(&unresolvable(lower), supply, margin);
                assert_eq!(
                    over,
                    i128::from(supply) >= i128::from(lower) + i128::from(margin),
                    "unknown funds judgment must be Σ ≥ Δ + margin (lower={lower}, supply={supply}, margin={margin})"
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
