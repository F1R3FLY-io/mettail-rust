//! Stage 3 — production wiring of in-Rho set-automaton matching.
//!
//! Piece 1: [`convert_lhs_pattern`] maps a `mettail_ast` structural LHS pattern to
//! the dovetail set-automaton input (`dovetail::rules::Pattern<String>`). A
//! variable or constructor application converts structurally; a constructor over a
//! single collection literal becomes an `AcApp` (which `compile_structural` rejects,
//! routing the rule to the AC path — Stage AC); binder / substitution /
//! collection-search metasyntax have no positional set-automaton image and fail
//! closed with a typed reason (Stage 3c / off-machine), so the capability gate can
//! report per-rule WHY a rule is not matched in Rho.
//!
//! The converter is TOTAL over `mettail_ast::Pattern` (every node either converts or
//! returns a typed reject — no panics), which is the executable half of FV (ix)'s
//! total-or-reject obligation. It agrees with the existing σ-receiver LHS-var
//! classifier (`lower_lhs_vars`) on "structural" — cross-checked in the tests — so a
//! rule can never be admitted by one path and rejected by the other.

use std::collections::{HashMap, HashSet};

use dovetail::rules::Pattern as DvPattern;
use dovetail::set_automaton::{PatternId, SetAutomaton};
use mettail_ast::identity::language_definition_fingerprint;
use mettail_ast::language::LanguageDef;
use mettail_ast::pattern::{Pattern, PatternTerm};
use models::rhoapi::Par;

use crate::rho_net_automaton::{
    multi_pattern_receiver_network_par, AutomatonAcceptTarget, AutomatonUnsupported,
};
use crate::rho_net_lower::{spread_term_par, GroundTerm};

/// Why an LHS pattern has no structural set-automaton image (fail-closed to a later
/// stage rather than mis-compiling it into a wrong automaton).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PatternConvertReject {
    /// A `\x.` / `^[…].` binder (`Lambda` / `MultiLambda`) — the in-Rho binder slice
    /// (Stage 3c); the automaton has no binder image.
    Binder,
    /// A `subst` / `multisubst` (a host-computed ground σ slot) — Stage 3c.
    Subst,
    /// Collection-search metasyntax (`#map` / `#zip`, or a bare collection literal not
    /// under a constructor) — no positional / `AcApp` image; the AC path (Stage AC) or
    /// off-machine.
    CollectionSearch,
}

/// Convert a structural LHS pattern to its dovetail set-automaton input. Total over
/// `mettail_ast::Pattern`: every node either converts or returns a typed reject.
pub fn convert_lhs_pattern(p: &Pattern) -> Result<DvPattern<String>, PatternConvertReject> {
    match p {
        Pattern::Term(term) => convert_term(term),
        // A bare collection literal / search metasyntax at a matched position is not a
        // constructor-rooted structural pattern (a Collection is only structural as the
        // sole arg of a constructor — handled in `convert_term`'s Apply arm).
        Pattern::Collection { .. } | Pattern::Map { .. } | Pattern::Zip { .. } => {
            Err(PatternConvertReject::CollectionSearch)
        },
    }
}

fn convert_term(term: &PatternTerm) -> Result<DvPattern<String>, PatternConvertReject> {
    match term {
        PatternTerm::Var(id) => Ok(DvPattern::var(id.to_string())),
        PatternTerm::Apply { constructor, args } => {
            let op = constructor.to_string();
            // AC form: a constructor applied to a single collection literal (the bag).
            // Becomes an AcApp — a valid dovetail pattern that `compile_structural`
            // rejects, routing the rule to the AC path (Stage AC).
            if let [Pattern::Collection { elements, rest, .. }] = args.as_slice() {
                let fixed = elements
                    .iter()
                    .map(convert_lhs_pattern)
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(DvPattern::ac(op, fixed, rest.as_ref().map(|r| r.to_string())))
            } else {
                let converted = args
                    .iter()
                    .map(convert_lhs_pattern)
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(DvPattern::app(op, converted))
            }
        },
        PatternTerm::Lambda { .. } | PatternTerm::MultiLambda { .. } => {
            Err(PatternConvertReject::Binder)
        },
        PatternTerm::Subst { .. } | PatternTerm::MultiSubst { .. } => {
            Err(PatternConvertReject::Subst)
        },
    }
}

/// Why a rewrite is not matched in Rho (routed to a later stage / its existing path).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DeferReason {
    /// The rewrite did not lower to a base-rewrite σ-receiver (congruence / unsafe
    /// premise / AC / binder) — it has no injection site.
    NotBaseRewrite,
    /// The LHS has no structural set-automaton image (binder / subst / search).
    Convert(PatternConvertReject),
    /// The LHS compiled to an `AcApp` (the AC path — Stage AC).
    Ac,
}

/// A rewrite the in-Rho matcher does NOT serialize, and why.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DeferredRewrite {
    pub rule_label: String,
    pub reason: DeferReason,
}

/// The in-Rho matching ruleset for a language: the positional automaton over its
/// structural base-rewrite LHSs, each entry's accept channel (its σ-receiver SOURCE —
/// the coherence anchor, from [`rho_net_injection_sites`](crate::rho_net_injection_sites)),
/// the shared language fingerprint, and every rewrite NOT matched in Rho (with a reason).
pub struct InRhoMatchingRuleset {
    pub automaton: SetAutomaton<String>,
    /// `PatternId(rewrite index)` → the rule's σ-receiver source channel.
    pub accept_channels: Vec<(PatternId, String)>,
    pub language_fingerprint: String,
    pub deferred: Vec<DeferredRewrite>,
}

/// Compile a language's structural base rewrites into ONE positional set automaton,
/// routing each accept to the rule's σ-receiver source channel. TOTAL over
/// `def.rewrites`: every rewrite is either an automaton entry or in `deferred` with
/// its reason (nothing silently dropped — the executable half of FV (ix)).
///
/// A rewrite is matched in Rho iff it has a base-rewrite σ-receiver site (so it lowered
/// to a `BaseRewrite` — congruence / unsafe-premise / AC / binder rules have none) AND
/// its LHS converts structurally AND compiles AC-free. Coherence: the accept channel is
/// the SAME `rho_net_injection_sites` channel the installed σ-receiver was compiled with.
pub fn compile_in_rho_matching_ruleset(def: &LanguageDef) -> InRhoMatchingRuleset {
    let language_fingerprint = language_definition_fingerprint(def);
    let sites = crate::rho_net_injection_sites(def);
    let site_channel: HashMap<&str, &str> =
        sites.iter().map(|s| (s.rule_label.as_str(), s.channel.as_str())).collect();

    let mut pairs: Vec<(PatternId, DvPattern<String>)> = Vec::with_capacity(def.rewrites.len());
    let mut accept_channels: Vec<(PatternId, String)> = Vec::new();
    let mut deferred: Vec<DeferredRewrite> = Vec::new();

    for (index, rewrite) in def.rewrites.iter().enumerate() {
        let label = rewrite.name.to_string();
        let channel = match site_channel.get(label.as_str()) {
            Some(channel) => channel.to_string(),
            None => {
                deferred.push(DeferredRewrite { rule_label: label, reason: DeferReason::NotBaseRewrite });
                continue;
            },
        };
        match convert_lhs_pattern(&rewrite.left) {
            Ok(pattern) => {
                pairs.push((PatternId(index), pattern));
                accept_channels.push((PatternId(index), channel));
            },
            Err(reject) => {
                deferred.push(DeferredRewrite { rule_label: label, reason: DeferReason::Convert(reject) });
            },
        }
    }

    // compile_structural rejects any AcApp entry; move it to `deferred{Ac}` and recompile
    // the AC-free remainder. Converges: AcApp is the only rejection, and the empty ruleset
    // compiles.
    let automaton = loop {
        match SetAutomaton::compile_structural(pairs.clone()) {
            Ok(automaton) => break automaton,
            Err(err) => {
                let unsupported: HashSet<PatternId> =
                    err.unsupported_patterns().iter().copied().collect();
                for pid in &unsupported {
                    let label = def.rewrites[pid.0].name.to_string();
                    deferred.push(DeferredRewrite { rule_label: label, reason: DeferReason::Ac });
                }
                pairs.retain(|(pid, _)| !unsupported.contains(pid));
                accept_channels.retain(|(pid, _)| !unsupported.contains(pid));
            },
        }
    };

    InRhoMatchingRuleset { automaton, accept_channels, language_fingerprint, deferred }
}

/// Build the per-firing `call` that matches `subject` in Rho against `ruleset`: the M2a
/// receiver network composed with the spread of the subject, at a fresh `site` nonce. Run
/// as `installed_σ_receiver_program ∥ call`, the network matches the spread ON the
/// interpreter (the τ `sa:` COMMs) and on accept fires the rule's σ-receiver. The network
/// is SINGLE-SHOT (O1 symbol-once), so it rides the per-firing call, not the persistent
/// install; a fresh `site` per firing keeps redex sites disjoint.
///
/// Every channel and tag flows from `ruleset` (one fingerprint, the σ-receiver-source
/// accept channels), so the accept triad and the fingerprint stay coherent by construction.
pub fn in_rho_match_call_par(
    ruleset: &InRhoMatchingRuleset,
    subject: &GroundTerm,
    site: &str,
    out_channel: &str,
) -> Result<Par, AutomatonUnsupported> {
    let targets: Vec<AutomatonAcceptTarget> = ruleset
        .accept_channels
        .iter()
        .map(|(pattern, accept_channel)| AutomatonAcceptTarget {
            pattern: *pattern,
            accept_channel: accept_channel.clone(),
            out_channel: out_channel.to_string(),
        })
        .collect();
    let network = multi_pattern_receiver_network_par(
        &ruleset.automaton.view(),
        site,
        &targets,
        &ruleset.language_fingerprint,
    )?;
    let spread = spread_term_par(subject, &ruleset.language_fingerprint, site);
    Ok(network.append(spread))
}

/// The FV (ix) `install_admits` capability gate, executable: returns the first rule that
/// BOTH fired and is skipped-from-in-Rho-matching (the fail-closed reason), or `None` if
/// every fired rule is matchable in Rho. A language's default backend flips to in-Rho
/// matching iff this returns `None` for its report. Model: `InRhoEncoderTotalOrReject.v`
/// (`gate_admits_iff_all_fired_matchable`) — the reject exists iff some rule both `fires`
/// and is `¬in_rho` (a skipped rule is exactly `¬in_rho`).
pub fn in_rho_match_gate_reject<'a>(
    skipped: &'a [DeferredRewrite],
    fired_labels: &[&str],
) -> Option<&'a DeferredRewrite> {
    skipped.iter().find(|entry| fired_labels.contains(&entry.rule_label.as_str()))
}

/// Reconstruct the ground redex `LHS[σ]` a fired base rewrite matched — the SUBJECT the
/// in-Rho matcher re-matches ON the interpreter (the automaton still does the matching
/// work in Rho; host σ only supplies the ground subject term, not the firing). Finds the
/// rewrite named `rule_label` in `def` and instantiates its LHS with σ. Total +
/// fail-closed; a matched (non-skipped) rule's LHS is Var/Apply-only, so the error arms
/// are defensive (they never trigger past the gate).
pub fn reconstruct_redex_subject(
    def: &LanguageDef,
    rule_label: &str,
    sigma: &[(String, GroundTerm)],
) -> Result<GroundTerm, String> {
    let rewrite = def
        .rewrites
        .iter()
        .find(|rewrite| rewrite.name.to_string() == rule_label)
        .ok_or_else(|| format!("in-Rho match subject: no rewrite named {rule_label}"))?;
    let bindings: HashMap<&str, &GroundTerm> =
        sigma.iter().map(|(name, ground)| (name.as_str(), ground)).collect();
    instantiate_lhs(&rewrite.left, &bindings, rule_label)
}

fn instantiate_lhs(
    pattern: &Pattern,
    sigma: &HashMap<&str, &GroundTerm>,
    rule: &str,
) -> Result<GroundTerm, String> {
    match pattern {
        Pattern::Term(PatternTerm::Var(id)) => {
            let name = id.to_string();
            sigma
                .get(name.as_str())
                .map(|ground| (*ground).clone())
                .ok_or_else(|| {
                    format!("in-Rho match subject for {rule}: σ missing LHS variable {name}")
                })
        },
        Pattern::Term(PatternTerm::Apply { constructor, args }) => {
            if let [Pattern::Collection { .. }] = args.as_slice() {
                return Err(format!(
                    "in-Rho match subject for {rule}: AC constructor {constructor} has no positional redex image"
                ));
            }
            let children = args
                .iter()
                .map(|arg| instantiate_lhs(arg, sigma, rule))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(GroundTerm::new(constructor.to_string(), children))
        },
        // binder / subst / collection-search → skipped rules; never reached past the gate.
        _ => Err(format!(
            "in-Rho match subject for {rule}: non-structural LHS has no ground redex image"
        )),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ident(s: &str) -> syn::Ident {
        syn::parse_str(s).expect("valid identifier")
    }
    fn var(s: &str) -> Pattern {
        Pattern::Term(PatternTerm::Var(ident(s)))
    }
    fn app(constructor: &str, args: Vec<Pattern>) -> Pattern {
        Pattern::Term(PatternTerm::Apply { constructor: ident(constructor), args })
    }

    #[test]
    fn converts_a_structural_application() {
        assert_eq!(
            convert_lhs_pattern(&app("Swap", vec![var("x"), var("y")])),
            Ok(DvPattern::app(
                "Swap".to_string(),
                vec![DvPattern::var("x".to_string()), DvPattern::var("y".to_string())]
            ))
        );
    }

    #[test]
    fn converts_a_nested_application() {
        // Wrap(Pair(x, y)) — recursion propagates through the arg.
        assert_eq!(
            convert_lhs_pattern(&app("Wrap", vec![app("Pair", vec![var("x"), var("y")])])),
            Ok(DvPattern::app(
                "Wrap".to_string(),
                vec![DvPattern::app(
                    "Pair".to_string(),
                    vec![DvPattern::var("x".to_string()), DvPattern::var("y".to_string())]
                )]
            ))
        );
    }

    #[test]
    fn converts_a_bare_variable() {
        assert_eq!(convert_lhs_pattern(&var("z")), Ok(DvPattern::var("z".to_string())));
    }

    #[test]
    fn a_constructor_over_a_collection_becomes_ac() {
        // (PPar {P, Q, ...rest}) — the AC form; becomes AcApp (compile_structural rejects).
        let collection = Pattern::Collection {
            coll_type: None,
            elements: vec![var("P"), var("Q")],
            rest: Some(ident("rest")),
        };
        assert_eq!(
            convert_lhs_pattern(&app("PPar", vec![collection])),
            Ok(DvPattern::ac(
                "PPar".to_string(),
                vec![DvPattern::var("P".to_string()), DvPattern::var("Q".to_string())],
                Some("rest".to_string())
            ))
        );
    }

    #[test]
    fn binder_and_subst_and_search_fail_closed() {
        let lambda = Pattern::Term(PatternTerm::Lambda {
            binder: ident("x"),
            body: Box::new(var("y")),
        });
        assert_eq!(convert_lhs_pattern(&lambda), Err(PatternConvertReject::Binder));

        let multilambda = Pattern::Term(PatternTerm::MultiLambda {
            binders: vec![ident("x"), ident("y")],
            body: Box::new(var("z")),
        });
        assert_eq!(convert_lhs_pattern(&multilambda), Err(PatternConvertReject::Binder));

        let subst = Pattern::Term(PatternTerm::Subst {
            term: Box::new(var("t")),
            var: ident("x"),
            replacement: Box::new(var("r")),
        });
        assert_eq!(convert_lhs_pattern(&subst), Err(PatternConvertReject::Subst));

        let map = Pattern::Map {
            collection: Box::new(var("xs")),
            params: vec![ident("x")],
            body: Box::new(var("x")),
        };
        assert_eq!(convert_lhs_pattern(&map), Err(PatternConvertReject::CollectionSearch));

        let zip = Pattern::Zip {
            first: Box::new(var("a")),
            second: Box::new(var("b")),
        };
        assert_eq!(convert_lhs_pattern(&zip), Err(PatternConvertReject::CollectionSearch));
    }

    #[test]
    fn a_binder_inside_a_structural_arg_propagates_the_reject() {
        // f(\x.y) — the binder arg makes the whole conversion fail closed.
        let lambda = Pattern::Term(PatternTerm::Lambda {
            binder: ident("x"),
            body: Box::new(var("y")),
        });
        assert_eq!(
            convert_lhs_pattern(&app("f", vec![var("a"), lambda])),
            Err(PatternConvertReject::Binder)
        );
    }

    #[test]
    fn gate_rejects_a_fired_skipped_rule_and_admits_matched_ones() {
        let skipped = vec![DeferredRewrite {
            rule_label: "Cong".to_string(),
            reason: DeferReason::NotBaseRewrite,
        }];
        // A fired skipped rule → reject (fail-closed, per FV ix's install_admits).
        assert!(in_rho_match_gate_reject(&skipped, &["Cong"]).is_some());
        // A fired matched rule (not in the skip-list) → admit.
        assert!(in_rho_match_gate_reject(&skipped, &["Swap"]).is_none());
        // Nothing fired → admit.
        assert!(in_rho_match_gate_reject(&skipped, &[]).is_none());
    }

    #[test]
    fn instantiates_a_structural_lhs_with_sigma() {
        // SwapStep LHS `Swap x y` with σ = {x↦A, y↦B} reconstructs `Swap(A, B)` — the
        // ground redex the in-Rho matcher re-matches (equal to piece 3's hand-built subject).
        let lhs = app("Swap", vec![var("x"), var("y")]);
        let a = GroundTerm::new("A".to_string(), Vec::new());
        let b = GroundTerm::new("B".to_string(), Vec::new());
        let sigma: HashMap<&str, &GroundTerm> = [("x", &a), ("y", &b)].into_iter().collect();
        let subject =
            instantiate_lhs(&lhs, &sigma, "SwapStep").expect("structural LHS instantiates");
        assert_eq!(
            subject,
            GroundTerm::new(
                "Swap".to_string(),
                vec![
                    GroundTerm::new("A".to_string(), Vec::new()),
                    GroundTerm::new("B".to_string(), Vec::new()),
                ]
            )
        );
    }
}
