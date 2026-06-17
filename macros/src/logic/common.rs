//! Shared category / HOL-domain helpers for the WPDA/Dovetail codegen path.
//!
//! (The Ascent Datalog generator that previously dominated this module was
//! retired in P6; only the HOL-domain utilities remain.)

use mettail_ast::language::LanguageDef;
use mettail_ast::types::TypeExpr;
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
/// errors across rhocalc/guardedrho on the merge.
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

/// Extract the `(domain, codomain)` as `Ident` names from a `TypeExpr::Arrow`.
/// Returns `(None, None)` for non-arrow types. For a multi-binder
/// domain like `Name*` the inner binder name is returned.
///
/// Currently unused after HOL-B gating was reverted — kept for a
/// future re-enablement (which must also teach downstream emitters
/// to respect the gated set).
#[allow(dead_code)]
fn extract_arrow_types(ty: &TypeExpr) -> (Option<String>, Option<String>) {
    match ty {
        TypeExpr::Arrow { domain, codomain } => {
            let dom = match &**domain {
                TypeExpr::Base(id) => Some(id.to_string()),
                TypeExpr::MultiBinder(inner) => match &**inner {
                    TypeExpr::Base(id) => Some(id.to_string()),
                    _ => None,
                },
                _ => None,
            };
            let cod = match &**codomain {
                TypeExpr::Base(id) => Some(id.to_string()),
                _ => None,
            };
            (dom, cod)
        },
        _ => (None, None),
    }
}

/// Walk a TokenStream collecting identifiers matching
/// `(Lam|MLam|Apply|MApply)<Suffix>` where `Suffix` is an exact
/// language-type name. Inserts each matched `Suffix` into `out`.
///
/// Non-recursive at token level — but does recurse into groups
/// `( ... )`, `{ ... }`, `[ ... ]` because the `rust_code` body may
/// nest arbitrarily.
///
/// Currently unused after HOL-B gating was reverted — kept for a
/// future re-enablement.
#[allow(dead_code)]
fn scan_tokens_for_hol_refs(
    stream: &proc_macro2::TokenStream,
    type_names: &BTreeSet<&str>,
    out: &mut BTreeSet<String>,
) {
    use proc_macro2::TokenTree;
    for tt in stream.clone() {
        match tt {
            TokenTree::Ident(id) => {
                let name = id.to_string();
                if let Some(suffix) = name
                    .strip_prefix("MLam")
                    .or_else(|| name.strip_prefix("MApply"))
                    .or_else(|| name.strip_prefix("Lam"))
                    .or_else(|| name.strip_prefix("Apply"))
                {
                    if !suffix.is_empty() && type_names.contains(suffix) {
                        out.insert(suffix.to_string());
                    }
                }
            },
            TokenTree::Group(g) => {
                scan_tokens_for_hol_refs(&g.stream(), type_names, out);
            },
            _ => {},
        }
    }
}
