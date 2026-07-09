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

use std::collections::{BTreeSet, HashMap, HashSet};

use dovetail::rules::Pattern as DvPattern;
use dovetail::set_automaton::{AutomatonNode, PatternId, SetAutomaton};
use mettail_ast::identity::language_definition_fingerprint;
use mettail_ast::language::LanguageDef;
use mettail_ast::pattern::{Pattern, PatternTerm};
use models::rhoapi::Par;

use crate::rho_net_automaton::{
    multi_pattern_receiver_network_par, AutomatonAcceptTarget, AutomatonUnsupported,
};
use crate::rho_net_lower::{spread_child_location, spread_term_par, GroundTerm};

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

/// One in-Rho MATCHING dispatch record for a native process family (Stage 4 S-native): the
/// automaton entry LOCATES the native `NativeProc` head + CAPTURES its structural args in Rho, and
/// its accept routes to [`trigger_channel`](Self::trigger_channel); the match driver co-installs a
/// [`native_locate_bridge_par`](crate::native_locate_bridge_par) that binds those captures (they
/// only GATE the delivery) and forwards the trusted handler's VALUE (the firing's contractum — the
/// inherent host boundary) on [`dispatch_channel`](Self::dispatch_channel), where the installed
/// dispatch receiver emits it on `@out`. So the LOCATION is the automaton's; only the VALUE is
/// host-supplied.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativeDispatch {
    /// The Dovetail firing label (`"{Category}_{Label}"`) the report keys the native firing on.
    pub fired_rule_label: String,
    /// The native entry's accept channel — the automaton's located accept sends
    /// `trigger!(⟦arg₀⟧, …, @out)` here, and the bridge consumes it.
    pub trigger_channel: String,
    /// The installed dispatch receiver's SOURCE channel — where the bridge forwards `⟦value⟧`.
    pub dispatch_channel: String,
    /// The native process's arity `k` — the number of captured args the accept sends and the
    /// bridge binds.
    pub arity: usize,
}

/// The in-Rho matching ruleset for a language: the positional automaton over its
/// structural base-rewrite LHSs AND its native process heads (Stage 4 S-native), each entry's
/// accept channel (a base rewrite's is its σ-receiver SOURCE — the coherence anchor, from
/// [`rho_net_injection_sites`](crate::rho_net_injection_sites); a native process's is its
/// per-rule trigger channel), the shared language fingerprint, the native dispatch records the
/// match driver builds value bridges from, and every rewrite NOT matched in Rho (with a reason).
pub struct InRhoMatchingRuleset {
    pub automaton: SetAutomaton<String>,
    /// `PatternId` → the entry's accept channel (base: σ-receiver source; native: trigger channel).
    pub accept_channels: Vec<(PatternId, String)>,
    pub language_fingerprint: String,
    pub deferred: Vec<DeferredRewrite>,
    /// One record per ADMITTED native process family entry (Stage 4 S-native): the firing label,
    /// trigger + dispatch channels, and arity the match driver co-installs a value bridge from.
    pub native_dispatch: Vec<NativeDispatch>,
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
    let site_channel: HashMap<&str, &str> = sites
        .iter()
        .map(|s| (s.rule_label.as_str(), s.channel.as_str()))
        .collect();

    let mut pairs: Vec<(PatternId, DvPattern<String>)> = Vec::with_capacity(def.rewrites.len());
    let mut accept_channels: Vec<(PatternId, String)> = Vec::new();
    let mut deferred: Vec<DeferredRewrite> = Vec::new();

    for (index, rewrite) in def.rewrites.iter().enumerate() {
        let label = rewrite.name.to_string();
        let channel = match site_channel.get(label.as_str()) {
            Some(channel) => channel.to_string(),
            None => {
                deferred.push(DeferredRewrite {
                    rule_label: label,
                    reason: DeferReason::NotBaseRewrite,
                });
                continue;
            },
        };
        match convert_lhs_pattern(&rewrite.left) {
            Ok(pattern) => {
                pairs.push((PatternId(index), pattern));
                accept_channels.push((PatternId(index), channel));
            },
            Err(reject) => {
                deferred.push(DeferredRewrite {
                    rule_label: label,
                    reason: DeferReason::Convert(reject),
                });
            },
        }
    }

    // Stage 4 (S-native): ADMIT the native process families (`NativeSystemProcessRewrite` /
    // `NativeFold`). A native process `NativeProc(a₀..a_{k-1})` is a plain App-rooted node, so the
    // SAME positional automaton LOCATES it by head tag + arity once its flat pattern
    // `bare_label(x₀..x_{k-1})` is an automaton entry — the redex location moves in Rho (the
    // structural DISPATCH), while its VALUE stays the trusted host handler's payload (delivered by
    // the match driver's value bridge on the dispatch channel — the inherent boundary). Native
    // process PatternIds start AFTER the base-rewrite ones (`def.rewrites.len() + native_index`),
    // disjoint from every base `PatternId(rewrite index)`. Their accept routes to a per-rule trigger
    // channel (NOT the σ-receiver source), so the located accept hands the captures to the bridge.
    let native_base = def.rewrites.len();
    let native_entries = crate::rho_net_native_match_entries(def);
    let mut native_dispatch: Vec<NativeDispatch> = Vec::with_capacity(native_entries.len());
    for (native_index, entry) in native_entries.iter().enumerate() {
        let pid = PatternId(native_base + native_index);
        // The flat App pattern `bare_label(x₀..x_{arity-1})` over DISTINCT fresh Var leaves: the
        // automaton matches the head tag + arity and captures each arg (a Var matches any subterm),
        // exactly the base-rewrite flat entry shape (App-over-Var).
        let args: Vec<DvPattern<String>> = (0..entry.arity)
            .map(|i| DvPattern::var(format!("__mettail_native_arg_{i}")))
            .collect();
        let pattern = DvPattern::app(entry.bare_label.clone(), args);
        // The per-rule trigger channel (the located accept's target) — derived from the unique
        // dispatch channel, disjoint from every base σ-receiver / automaton `loc:`/`cap:` channel.
        let trigger = format!("{}/sa-locate", entry.dispatch_channel);
        pairs.push((pid, pattern));
        accept_channels.push((pid, trigger.clone()));
        native_dispatch.push(NativeDispatch {
            fired_rule_label: entry.fired_rule_label.clone(),
            trigger_channel: trigger,
            dispatch_channel: entry.dispatch_channel.clone(),
            arity: entry.arity,
        });
    }

    // The label of a rejected `PatternId` — a base rewrite name, or a native firing label for the
    // (non-occurring) native rejection, so the retry loop never indexes `def.rewrites` out of range.
    // Reads `native_entries` (parallel to `native_dispatch`, never mutated), so it does not conflict
    // with the defensive `native_dispatch.retain` below.
    let deferred_label = |pid: PatternId| -> String {
        if pid.0 < native_base {
            def.rewrites[pid.0].name.to_string()
        } else {
            native_entries
                .get(pid.0 - native_base)
                .map(|entry| entry.fired_rule_label.clone())
                .unwrap_or_else(|| format!("native#{}", pid.0))
        }
    };

    // compile_structural rejects any AcApp entry; move it to `deferred{Ac}` and recompile
    // the AC-free remainder. Converges: AcApp is the only rejection (a native flat App-over-Var
    // entry is never rejected), and the empty ruleset compiles.
    let automaton = loop {
        match SetAutomaton::compile_structural(pairs.clone()) {
            Ok(automaton) => break automaton,
            Err(err) => {
                let unsupported: HashSet<PatternId> =
                    err.unsupported_patterns().iter().copied().collect();
                for pid in &unsupported {
                    deferred.push(DeferredRewrite {
                        rule_label: deferred_label(*pid),
                        reason: DeferReason::Ac,
                    });
                }
                pairs.retain(|(pid, _)| !unsupported.contains(pid));
                accept_channels.retain(|(pid, _)| !unsupported.contains(pid));
                native_dispatch.retain(|entry| {
                    !unsupported.iter().any(|pid| {
                        pid.0 >= native_base
                            && native_entries
                                .get(pid.0 - native_base)
                                .is_some_and(|e| e.fired_rule_label == entry.fired_rule_label)
                    })
                });
            },
        }
    };

    InRhoMatchingRuleset {
        automaton,
        accept_channels,
        language_fingerprint,
        deferred,
        native_dispatch,
    }
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

/// The set of rule LHS ROOT constructors the in-Rho matcher's positional automaton dispatches
/// on — the compiled entries' root ops. A subject node whose head is one of these is a CANDIDATE
/// redex position the automaton attempts a match at (the plural, locate-all generalization of the
/// single-redex [`rule_lhs_root_constructor`]). Reads ONLY the compiled automaton (not the report
/// σ), so it never re-does the host match.
pub fn rule_lhs_root_constructors(ruleset: &InRhoMatchingRuleset) -> BTreeSet<String> {
    let view = ruleset.automaton.view();
    (0..view.entry_count())
        .filter_map(|entry| match view.node(view.entry_root_state(entry)) {
            AutomatonNode::App { op, .. } => Some(op.to_string()),
            AutomatonNode::Var(_) => None,
        })
        .collect()
}

/// Whether every compiled entry is FLAT — an App root over Var-leaf arguments only. This is the
/// soundness precondition for the Stage-4 locate-all multi-site install
/// ([`in_rho_match_all_sites_call_par`]): a flat entry's network reads only its own root `loc:`
/// head-tag channel and its direct-child `cap:` COLLAPSE channels, which are DISJOINT across
/// distinct positions (`loc:ρ/ℓ₁ ≠ loc:ρ/ℓ₂`, `cap:ρ/ℓ₁/op.i ≠ cap:ρ/ℓ₂/op.j`), so co-installing
/// one network per redex position over ONE spread never contends for a channel. A NESTED entry
/// would DESCEND `loc:` head tags into its arguments; a co-installed root attempt at a descent
/// position would then race for that one linear head-tag send. Such a ruleset fails closed to the
/// σ-replay driver ([`AutomatonUnsupported::NestedEntryMultiSite`]).
pub fn ruleset_all_entries_flat(ruleset: &InRhoMatchingRuleset) -> bool {
    let view = ruleset.automaton.view();
    (0..view.entry_count()).all(|entry| match view.node(view.entry_root_state(entry)) {
        AutomatonNode::App { args, .. } => args
            .iter()
            .all(|&arg| matches!(view.node(arg), AutomatonNode::Var(_))),
        AutomatonNode::Var(_) => false,
    })
}

/// Collect the per-position SITE strings of `node` at which the automaton attempts a match: every
/// position (pre-order, DFS) whose head constructor is a rule LHS root (`roots`). The site string
/// is the ν-free location path `⌜(ρ,ℓ)⌝` (root nonce ρ = `root_location`, position ℓ derived via
/// [`spread_child_location`] — the SAME derivation the spread uses for its `loc:`/`cap:` channels),
/// so the network built at each site reads the channels the ONE spread of the whole subject
/// published there. Distinct positions get distinct (disjoint-prefix) site strings.
fn collect_redex_sites(
    node: &GroundTerm,
    location: &str,
    roots: &BTreeSet<String>,
    sites: &mut Vec<String>,
) {
    if roots.contains(&node.constructor) {
        sites.push(location.to_string());
    }
    for (index, child) in node.children.iter().enumerate() {
        let child_location = spread_child_location(location, &node.constructor, index);
        collect_redex_sites(child, &child_location, roots, sites);
    }
}

/// Stage 4 (locate-all + multi-firing) — build ONE combined match call that locates EVERY redex of
/// `subject`, at ANY position and multiple simultaneously (P1 Thm 6.12 / P2 Thm 2). The whole
/// reflected subject is spread ONCE at root nonce `root_site`; for every position whose head is a
/// rule LHS root ([`rule_lhs_root_constructors`]) a positional receiver network is built at that
/// position's ν-free site path (`⌜(ρ,ℓ)⌝`), and all networks are composed with the one spread. Each
/// site's accept fires the matched rule's σ-receiver on `out_channel`, so a single isolated run
/// observes every located redex's contractum on that channel (the shared persistent σ-receiver
/// serves every site's accept — the accept send carries its σ + `@out` atomically, so distinct
/// sites never cross-talk). Returns the combined call and the number of located sites (0 = a normal
/// form: the call is the bare spread, which fires nothing).
///
/// The automaton — not the host — LOCATES + binds σ: `collect_redex_sites` only pre-filters
/// candidate positions by head op (exactly the set-automaton root-state dispatch); at each site the
/// emitted network re-does the head `Match` and the `cap:` σ capture ON the interpreter, so σ is
/// produced by the accept, never the report (M-reflect).
///
/// Contention is possible ONLY when ≥2 networks are CO-INSTALLED (a nested-App entry descends
/// `loc:` head tags, which a co-installed root attempt at that descent position could race for). So
/// this admits: a flat-only ruleset ([`ruleset_all_entries_flat`]) at ANY number of sites (disjoint
/// `loc:`/`cap:` reads); OR a nested ruleset at ≤1 site (no co-installation → no contention, exactly
/// the single-redex path). A nested ruleset with ≥2 located redexes fails closed
/// ([`AutomatonUnsupported::NestedEntryMultiSite`]) to the σ-replay driver — never a wrong match.
pub fn in_rho_match_all_sites_call_par(
    ruleset: &InRhoMatchingRuleset,
    subject: &GroundTerm,
    root_site: &str,
    out_channel: &str,
) -> Result<(Par, usize), AutomatonUnsupported> {
    let targets: Vec<AutomatonAcceptTarget> = ruleset
        .accept_channels
        .iter()
        .map(|(pattern, accept_channel)| AutomatonAcceptTarget {
            pattern: *pattern,
            accept_channel: accept_channel.clone(),
            out_channel: out_channel.to_string(),
        })
        .collect();

    let roots = rule_lhs_root_constructors(ruleset);
    let mut sites: Vec<String> = Vec::new();
    collect_redex_sites(subject, root_site, &roots, &mut sites);

    // Co-installing ≥2 per-position networks is contention-free only for a flat-only ruleset; a
    // nested ruleset admits at most one site (no co-installation). Fail closed otherwise.
    if sites.len() > 1 && !ruleset_all_entries_flat(ruleset) {
        return Err(AutomatonUnsupported::NestedEntryMultiSite);
    }

    // One positional network per located site (disjoint-prefix channels), then ONE spread of the
    // whole subject. A normal form (no located site) is the bare spread — a valid no-op.
    let mut call = Par::default();
    for site in &sites {
        let network = multi_pattern_receiver_network_par(
            &ruleset.automaton.view(),
            site,
            &targets,
            &ruleset.language_fingerprint,
        )?;
        call = call.append(network);
    }
    let spread = spread_term_par(subject, &ruleset.language_fingerprint, root_site);
    Ok((call.append(spread), sites.len()))
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
    skipped
        .iter()
        .find(|entry| fired_labels.contains(&entry.rule_label.as_str()))
}

/// The ROOT constructor of a rewrite's LHS (an `Apply`-rooted structural pattern), or a typed
/// error if the rule is absent or its LHS is not constructor-rooted.
///
/// The Stage-4 in-Rho MATCH path (M-reflect) spreads the WHOLE reflected subject term and lets
/// the automaton LOCATE the redex at the spread ROOT. That locates a redex only when the whole
/// subject IS the redex — i.e. the subject's root constructor equals the fired rule's LHS root.
/// The driver uses this to fail a NESTED redex (whose subject root is a context constructor)
/// closed to the σ-replay path, which openly uses σ to locate + inject nested redexes. This
/// reads ONLY the compiled rule set (not the report σ), so it never re-does the host match.
pub fn rule_lhs_root_constructor(def: &LanguageDef, rule_label: &str) -> Result<String, String> {
    let rewrite = def
        .rewrites
        .iter()
        .find(|rewrite| rewrite.name.to_string() == rule_label)
        .ok_or_else(|| format!("in-Rho match root check: no rewrite named {rule_label}"))?;
    match &rewrite.left {
        Pattern::Term(PatternTerm::Apply { constructor, .. }) => Ok(constructor.to_string()),
        _ => Err(format!(
            "in-Rho match root check: rewrite {rule_label} LHS is not constructor-rooted"
        )),
    }
}

/// Reconstruct the ground redex `LHS[σ]` a fired base rewrite matched — the SUBJECT the
/// in-Rho matcher re-matches ON the interpreter (the automaton still does the matching
/// work in Rho; host σ only supplies the ground subject term, not the firing). Finds the
/// rewrite named `rule_label` in `def` and instantiates its LHS with σ. Total +
/// fail-closed; a matched (non-skipped) rule's LHS is Var/Apply-only, so the error arms
/// are defensive (they never trigger past the gate).
///
/// NOTE: the Stage-4 M-reflect MATCH path no longer calls this (it reflects the whole `term`
/// structurally instead of rebuilding `LHS[σ]` from the report σ). It is retained as the
/// executable spec/oracle for the redex a firing matched (still exercised by the unit tests).
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
    let bindings: HashMap<&str, &GroundTerm> = sigma
        .iter()
        .map(|(name, ground)| (name.as_str(), ground))
        .collect();
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

    /// The flat SwapDemo ruleset (`Swap(x, y) ~> Pair(y, x)`) — a single flat App entry.
    fn swap_demo_def() -> LanguageDef {
        syn::parse_str(
            r#"
                name: SwapRulesetGen,
                types { Proc }
                terms {
                    A . |- "A" : Proc ;
                    B . |- "B" : Proc ;
                    Pair . x:Proc, y:Proc |- "pair" "(" x "," y ")" : Proc ;
                    Swap . x:Proc, y:Proc |- "swap" "(" x "," y ")" : Proc ;
                }
                equations {}
                rewrites { SwapStep . |- (Swap x y) ~> (Pair y x) ; }
            "#,
        )
        .expect("the SwapDemo ruleset fragment parses")
    }

    #[test]
    fn rule_lhs_roots_are_the_flat_entry_ops() {
        let ruleset = compile_in_rho_matching_ruleset(&swap_demo_def());
        assert_eq!(
            rule_lhs_root_constructors(&ruleset),
            ["Swap".to_string()].into_iter().collect::<BTreeSet<_>>(),
            "the only matchable rule root is Swap"
        );
        assert!(ruleset_all_entries_flat(&ruleset), "Swap(x, y) is a flat App-over-Var entry");
    }

    #[test]
    fn a_nested_pattern_entry_is_not_flat() {
        // Wrap(Swap x y) ~> Pair(y, x): the LHS has a NESTED App child, so the ruleset is not
        // flat and the locate-all multi-site install fails closed (co-install contention).
        let def: LanguageDef = syn::parse_str(
            r#"
                name: NestedRulesetGen,
                types { Proc }
                terms {
                    A . |- "A" : Proc ;
                    Pair . x:Proc, y:Proc |- "pair" "(" x "," y ")" : Proc ;
                    Swap . x:Proc, y:Proc |- "swap" "(" x "," y ")" : Proc ;
                    Wrap . x:Proc |- "wrap" "(" x ")" : Proc ;
                }
                equations {}
                rewrites { NestStep . |- (Wrap (Swap x y)) ~> (Pair y x) ; }
            "#,
        )
        .expect("the nested-pattern fragment parses");
        let ruleset = compile_in_rho_matching_ruleset(&def);
        assert!(!ruleset_all_entries_flat(&ruleset), "Wrap(Swap x y) is a nested entry");

        let swap_a_a = GroundTerm::new(
            "Swap",
            vec![GroundTerm::new("A", Vec::new()), GroundTerm::new("A", Vec::new())],
        );
        let wrap = |inner: GroundTerm| GroundTerm::new("Wrap", vec![inner]);

        // A SINGLE nested-pattern redex has no co-installation, so it still matches in Rho (the
        // pre-Stage-4 single-redex behavior is preserved — no fallback).
        let single = wrap(swap_a_a.clone());
        let (_call, n_single) =
            in_rho_match_all_sites_call_par(&ruleset, &single, "site0", "OUT")
                .expect("a single nested-pattern redex still serializes (no co-install contention)");
        assert_eq!(n_single, 1, "the single Wrap(Swap …) redex is located");

        // ≥2 co-installed nested-pattern networks could contend, so fail closed (→ σ-replay).
        let two = GroundTerm::new(
            "Pair",
            vec![wrap(swap_a_a.clone()), wrap(swap_a_a)],
        );
        assert_eq!(
            in_rho_match_all_sites_call_par(&ruleset, &two, "site0", "OUT"),
            Err(AutomatonUnsupported::NestedEntryMultiSite),
            "≥2 nested-pattern sites fail closed to the σ-replay driver"
        );
    }

    #[test]
    fn locate_all_finds_every_redex_position() {
        let ruleset = compile_in_rho_matching_ruleset(&swap_demo_def());

        // A single ROOT redex: Swap(A, B) — one site.
        let a = GroundTerm::new("A", Vec::new());
        let b = GroundTerm::new("B", Vec::new());
        let root = GroundTerm::new("Swap", vec![a.clone(), b.clone()]);
        let (_call, n_root) = in_rho_match_all_sites_call_par(&ruleset, &root, "site0", "OUT")
            .expect("a flat ruleset serializes the locate-all call");
        assert_eq!(n_root, 1, "Swap(A, B) is one root-rooted redex");

        // A single NESTED redex: Pair(Swap(A, B), B) — Pair is inert (not a rule root), so the
        // only located site is the nested Swap at position Pair.0.
        let nested = GroundTerm::new(
            "Pair",
            vec![GroundTerm::new("Swap", vec![a.clone(), b.clone()]), b.clone()],
        );
        let (_call, n_nested) = in_rho_match_all_sites_call_par(&ruleset, &nested, "site0", "OUT")
            .expect("locate-all serializes for a nested redex");
        assert_eq!(n_nested, 1, "the nested Swap at Pair.0 is located (Pair is inert)");

        // MULTIPLE redexes: Pair(Swap(A, B), Swap(B, A)) — two sites (Pair.0 and Pair.1).
        let multi = GroundTerm::new(
            "Pair",
            vec![
                GroundTerm::new("Swap", vec![a.clone(), b.clone()]),
                GroundTerm::new("Swap", vec![b.clone(), a.clone()]),
            ],
        );
        let (_call, n_multi) = in_rho_match_all_sites_call_par(&ruleset, &multi, "site0", "OUT")
            .expect("locate-all serializes for multiple redexes");
        assert_eq!(n_multi, 2, "both nested Swaps are located simultaneously");

        // A NESTED redex in a non-inert arg position: Swap(A, Swap(B, A)) — the outer Swap AND
        // the inner Swap at position Swap.1 are both redexes → two sites.
        let nested_arg = GroundTerm::new(
            "Swap",
            vec![a.clone(), GroundTerm::new("Swap", vec![b.clone(), a.clone()])],
        );
        let (_call, n_nested_arg) =
            in_rho_match_all_sites_call_par(&ruleset, &nested_arg, "site0", "OUT")
                .expect("locate-all serializes for a nested-arg redex");
        assert_eq!(n_nested_arg, 2, "the outer Swap and the inner Swap at Swap.1 are both located");

        // A normal form: Pair(A, B) — no located site (the bare spread, a no-op).
        let normal = GroundTerm::new("Pair", vec![a, b]);
        let (_call, n_normal) = in_rho_match_all_sites_call_par(&ruleset, &normal, "site0", "OUT")
            .expect("locate-all serializes a no-op for a normal form");
        assert_eq!(n_normal, 0, "Pair(A, B) has no redex");
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
