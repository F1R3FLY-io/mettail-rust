//! Shared category / HOL-domain helpers for the WPDA/Dovetail codegen path.
//!
//! (The Ascent Datalog generator that previously dominated this module was
//! retired in P6; only the HOL-domain utilities remain.)

use mettail_ast::language::LanguageDef;
use std::collections::BTreeSet;

/// Compute which `(category, domain)` pairs should get auto-generated
/// higher-order-logic variants `Lam{Domain}` / `MLam{Domain}` /
/// `Apply{Domain}` / `MApply{Domain}`.
///
/// Returns the full cross-product of (category × domain) over all
/// declared language types. Every category gets HOL variants for every
/// domain.
///
/// ## Why not gate by usage?
///
/// An earlier "HOL-B" gating attempted to narrow the set by (a)
/// structural analysis of Abstraction / MultiAbstraction grammar
/// params and (b) a name scan of user-supplied `rust_code` / logic
/// blocks for `(Lam|MLam|Apply|MApply)<TypeName>` idents. This was
/// **incorrect**: downstream emitters (`prattail/src/trampoline.rs`
/// beta-reduction arms, subst/normalize codegen, etc.) emit
/// references to these variants *unconditionally* for every (cat,
/// domain) pair. Gating the enum emission against the user-side scan
/// produced dangling references to nonexistent variants — 96+ compile
/// errors across rholang/guardedrho on the merge.
///
/// The memory reduction this gating provided was a real constant
/// factor savings, but it came at the cost of correctness. If we want
/// to reduce HOL variant surface, the fix must be systemic: teach
/// every emitter to use the same gated set, or rewrite the beta/eta
/// codegen so it doesn't need per-(cat, domain) variants at all. Until
/// then, we emit the full cross-product.
pub fn compute_hol_domain_pairs(language: &LanguageDef) -> BTreeSet<(String, String)> {
    let all_types: Vec<String> = language.types.iter().map(|t| t.name.to_string()).collect();
    let mut pairs: BTreeSet<(String, String)> = BTreeSet::new();
    for cat in &all_types {
        for domain in &all_types {
            pairs.insert((cat.clone(), domain.clone()));
        }
    }
    pairs
}
