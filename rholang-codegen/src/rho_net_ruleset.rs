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
use mettail_ast::grammar::{GrammarItem, TermParam};
use mettail_ast::identity::language_definition_fingerprint;
use mettail_ast::language::LanguageDef;
use mettail_ast::pattern::{Pattern, PatternTerm};
use models::rhoapi::Par;

use crate::rho_net_automaton::{
    multi_pattern_receiver_network_par, AutomatonAcceptTarget, AutomatonUnsupported,
};
use crate::rho_net_lower::{
    ac_match_call_par, congruence_only_premises, contextual_hole_bridge_par,
    contextual_premise_hole_channel, nested_structural_ac_match_call_par, spread_child_location,
    spread_term_par, structural_ac_match_call_par, GroundTerm, RhoNetAcMatchEntry,
    RhoNetContextualMatchEntry, RhoNetNestedStructuralAcMatchEntry,
    RhoNetStructuralAcMatchEntry, LAMBDA_REFLECT_LABEL, MULTILAMBDA_REFLECT_LABEL,
};

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

/// The binder constructors of a language mapped to their RESERVED reflection tag (Stage 4
/// S-binder): a single-binder constructor (a `TermParam::Abstraction`, e.g. `Lam` from
/// `^x.body:[Term -> Term]`) → [`LAMBDA_REFLECT_LABEL`] (`^lambda`); a multi-binder
/// (`TermParam::MultiAbstraction`) → [`MULTILAMBDA_REFLECT_LABEL`] (`^multilambda`).
///
/// This is the CODEGEN-side dual of the macro `reflect_category_fn`'s
/// Binder/MultiBinder arm: the M-reflect subject reflection tags a runtime `Lam(scope)`
/// node `^lambda`, so a subst rewrite whose LHS names that binder constructor must convert
/// `Lam` to the SAME `^lambda` op for the automaton entry to MATCH the reflected subject.
/// An old-syntax binder without a `term_context` (a bare `GrammarItem::Binder`) is treated
/// as a single binder.
fn binder_reflect_tags(def: &LanguageDef) -> HashMap<String, &'static str> {
    let mut tags: HashMap<String, &'static str> = HashMap::new();
    for term in &def.terms {
        let label = term.label.to_string();
        if let Some(params) = &term.term_context {
            let mut is_single = false;
            let mut is_multi = false;
            for param in params {
                match param {
                    TermParam::Abstraction { .. } => is_single = true,
                    TermParam::MultiAbstraction { .. } => is_multi = true,
                    _ => {},
                }
            }
            if is_multi {
                tags.insert(label, MULTILAMBDA_REFLECT_LABEL);
            } else if is_single {
                tags.insert(label, LAMBDA_REFLECT_LABEL);
            }
        } else if term.items.iter().any(|item| matches!(item, GrammarItem::Binder { .. })) {
            tags.insert(label, LAMBDA_REFLECT_LABEL);
        }
    }
    tags
}

/// Convert a binder/β-substitution rewrite's LHS pattern to its dovetail set-automaton input
/// (Stage 4 S-binder), REMAPPING each binder constructor to its reserved reflection tag via
/// `binder_tags`. Unlike the base [`convert_lhs_pattern`] (which keeps `Lam` as the op and rejects
/// `\x.` / `^[…].` binder metasyntax), this maps a binder constructor `Lam` → `^lambda` (and a
/// `Lambda` / `MultiLambda` node → `^lambda` / `^multilambda` over its converted body, the binder
/// De Bruijn-implicit), so `App(Lam(fun), arg)` compiles to the nested App entry
/// `App(^lambda(fun), arg)` that MATCHES the M-reflect subject (whose `Lam` node reflects to
/// `^lambda`) and CAPTURES `(fun, arg)`. Total over `Pattern`: every node converts or returns a
/// typed reject. The base converter is left BYTE-IDENTICAL (no landed base/native/AC/contextual
/// admission changes); only the S-binder subst admission uses this binder-aware path.
fn convert_subst_lhs(
    p: &Pattern,
    binder_tags: &HashMap<String, &'static str>,
) -> Result<DvPattern<String>, PatternConvertReject> {
    match p {
        Pattern::Term(term) => convert_subst_term(term, binder_tags),
        Pattern::Collection { .. } | Pattern::Map { .. } | Pattern::Zip { .. } => {
            Err(PatternConvertReject::CollectionSearch)
        },
    }
}

fn convert_subst_term(
    term: &PatternTerm,
    binder_tags: &HashMap<String, &'static str>,
) -> Result<DvPattern<String>, PatternConvertReject> {
    match term {
        PatternTerm::Var(id) => Ok(DvPattern::var(id.to_string())),
        PatternTerm::Apply { constructor, args } => {
            // A binder constructor (`Lam`) reflects to `^lambda`; a plain constructor (`App`, `F`)
            // keeps its label — the SAME op the M-reflect subject tags the node with.
            let op = binder_tags
                .get(constructor.to_string().as_str())
                .map(|tag| (*tag).to_string())
                .unwrap_or_else(|| constructor.to_string());
            if let [Pattern::Collection { elements, rest, .. }] = args.as_slice() {
                let fixed = elements
                    .iter()
                    .map(|p| convert_subst_lhs(p, binder_tags))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(DvPattern::ac(op, fixed, rest.as_ref().map(|r| r.to_string())))
            } else {
                let converted = args
                    .iter()
                    .map(|p| convert_subst_lhs(p, binder_tags))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(DvPattern::app(op, converted))
            }
        },
        // A `\x.body` / `^[…].body` binder written in binder metasyntax reflects to
        // `^lambda` / `^multilambda` over its converted body; the binder is De Bruijn-implicit.
        PatternTerm::Lambda { body, .. } => {
            let body_pat = convert_subst_lhs(body, binder_tags)?;
            Ok(DvPattern::app(LAMBDA_REFLECT_LABEL.to_string(), vec![body_pat]))
        },
        PatternTerm::MultiLambda { body, .. } => {
            let body_pat = convert_subst_lhs(body, binder_tags)?;
            Ok(DvPattern::app(MULTILAMBDA_REFLECT_LABEL.to_string(), vec![body_pat]))
        },
        // A subst/multisubst on the LHS has no positional image (it is a host-computed σ slot).
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
    /// The BARE head label (`"PowInt"`) — the automaton entry's root op AND the tag the
    /// structurally reflected subject node carries (A-S2: the report-free match path counts
    /// LOCATED native sites by walking the reflected subject for these heads, instead of
    /// counting report firings).
    pub bare_label: String,
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
    /// One record per ADMITTED HashBag AC family entry (Stage 4 S-AC): the firing label, operand
    /// constructor, element count, and pre-built RHS the match driver
    /// ([`ac_match_call_par`](crate::ac_match_call_par)) co-installs a per-site AC receiver from —
    /// re-sourcing the operand bag from the SPREAD of the subject, not the host-σ report. Unlike a
    /// base rewrite or native process, an AC redex is NOT an automaton entry (its `AcApp` has no
    /// positional image), so it carries no `accept_channels` entry and no `PatternId`.
    pub ac_dispatch: Vec<RhoNetAcMatchEntry>,
    /// One record per ADMITTED contextual (congruence) rewrite family (Stage 4 S-contextual): the
    /// contextual rule label and its `n` join premise channels the match driver
    /// ([`contextual_match_call_par`](crate::contextual_match_call_par)) routes each hole position's
    /// IN-RHO nested firing to (via [`contextual_hole_bridge_par`](crate::contextual_hole_bridge_par)),
    /// so the installed [`contextual_join_receiver_par`](crate::contextual_join_receiver_par)
    /// reassembles ⟦K'⟧ from the automaton's firings, not the host-σ report. Like an AC redex, a
    /// contextual redex is NOT an automaton entry (its outer context `K` fires no positional root
    /// `Match` — the base automaton locates the HOLE's premise redex by nested-App descent), so it
    /// carries no `accept_channels` entry and no `PatternId`.
    pub contextual_dispatch: Vec<RhoNetContextualMatchEntry>,
    /// One record per ADMITTED STRUCTURAL non-linear AC family entry (Stage 4 S-binder SLICE 3b — the
    /// Ambient `OpenRule`): the firing label + recognized shape the match driver
    /// ([`structural_ac_match_call_par`](crate::structural_ac_match_call_par)) co-installs a per-site
    /// MATCH receiver from — re-sourcing the operand bag AND the structural reducts from the SPREAD of
    /// the subject (binding the reduct arguments FROM the bag), not the host-σ report. Like a linear
    /// AC redex, a structural-AC redex is NOT an automaton entry (its `AcApp` bag has no positional
    /// image), so it carries no `accept_channels` entry and no `PatternId`; the walk rides the SAME
    /// `^lambda`/nested descent, so a bag under a `new(x, ·)` binder is located too.
    pub structural_ac_dispatch: Vec<RhoNetStructuralAcMatchEntry>,
    /// One record per ADMITTED DEPTH-2 NESTED structural non-linear AC family entry (Stage 4 —
    /// the Ambient `InRule`/`OutRule`): the firing label + recognized nested shape the match driver
    /// ([`nested_structural_ac_match_call_par`](crate::nested_structural_ac_match_call_par))
    /// co-installs a per-site MATCH receiver from — re-sourcing the operand AND the NESTED reducts
    /// from the SPREAD of the subject (binding every σ slot from the operand and rebuilding the nested
    /// reduct in the receiver body), not the host-σ report. The DEPTH-2 generalization of
    /// [`structural_ac_dispatch`](Self::structural_ac_dispatch): like every AC redex it is NOT an
    /// automaton entry (its nested `AcApp` has no positional image), so it carries no
    /// `accept_channels` entry and no `PatternId`; the walk keys on the LHS root pattern's TOP
    /// constructor (a bag op for `InRule`, a wrapper for `OutRule`).
    pub nested_structural_ac_dispatch: Vec<RhoNetNestedStructuralAcMatchEntry>,
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

    // Stage 4 (S-AC): ADMIT the linear with-rest HashBag AC family rewrites. An AC rewrite has NO
    // base-rewrite σ-receiver site (it un-skipped to an `AcRewrite`), so it would otherwise defer
    // `NotBaseRewrite` and the gate would reject the match path. Instead the match driver
    // ([`ac_match_call_par`](crate::ac_match_call_par)) LOCATES the bag in the reflected subject and
    // co-installs a per-site AC receiver re-sourcing the operand bag from the SPREAD (not the
    // report σ). Admitting a rule here (skipping its defer) shrinks `deferred`, so the gate stops
    // rejecting it — the AC analogue of S-native's `native_dispatch`.
    let ac_dispatch = crate::rho_net_ac_match_entries(def);
    let ac_admitted: HashSet<&str> =
        ac_dispatch.iter().map(|entry| entry.fired_rule_label.as_str()).collect();

    // Stage 4 (S-contextual): ADMIT the contextual (congruence) rewrite families. A contextual
    // rewrite has NO base-rewrite σ-receiver site (it lowered to a `ContextualRewrite` join), so it
    // would otherwise defer `NotBaseRewrite` and the gate would reject the match path. Instead the
    // match driver ([`contextual_match_call_par`]) LOCATES each hole position's premise redex in the
    // reflected subject (the base automaton's nested-App descent through `K`'s spine) and routes its
    // reduced hole to the join's premise channel, where the installed
    // [`contextual_join_receiver_par`] reassembles ⟦K'⟧. Admitting a rule here (skipping its defer)
    // shrinks `deferred`, so the gate stops rejecting it — the contextual analogue of S-native's
    // `native_dispatch` / S-AC's `ac_dispatch`.
    let contextual_dispatch = crate::rho_net_contextual_match_entries(def);
    let contextual_admitted: HashSet<&str> =
        contextual_dispatch.iter().map(|entry| entry.fired_rule_label.as_str()).collect();

    // Stage 4 (S-binder SLICE 3b): ADMIT the STRUCTURAL non-linear AC family rewrites (the Ambient
    // `OpenRule`). A structural-AC rewrite has NO base-rewrite σ-receiver site (it un-skipped to a
    // `StructuralAcRewrite`), so it would otherwise defer `NotBaseRewrite` and the gate would reject
    // the match path. Instead the match driver ([`structural_ac_match_call_par`]) LOCATES the bag in
    // the reflected subject (riding the SAME `^lambda`/nested descent, so a bag under a `new(x, ·)`
    // binder is reached too) and co-installs a per-site MATCH receiver re-sourcing the operand bag +
    // structural reducts from the SPREAD (not the report σ). Admitting a rule here (skipping its
    // defer) shrinks `deferred`, so the gate stops rejecting it — the structural-AC analogue of
    // S-AC's `ac_dispatch` / S-contextual's `contextual_dispatch`.
    let structural_ac_dispatch = crate::rho_net_structural_ac_match_entries(def);
    let structural_ac_admitted: HashSet<&str> =
        structural_ac_dispatch.iter().map(|entry| entry.fired_rule_label.as_str()).collect();

    // Stage 4 (Ambient In/Out): ADMIT the DEPTH-2 NESTED structural non-linear AC family rewrites
    // (the Ambient `InRule`/`OutRule`). A nested-structural-AC rewrite has NO base-rewrite σ-receiver
    // site (it un-skipped to a `NestedStructuralAcRewrite`), so it would otherwise defer
    // `NotBaseRewrite` and the gate would reject the match path — deferring In/Out to the host-σ
    // report replay (the DUAL PATH). Instead the match driver
    // ([`nested_structural_ac_match_call_par`]) LOCATES the operand in the reflected subject (keyed on
    // the LHS root pattern's TOP constructor — a bag op `PPar` for `InRule`, a wrapper `PAmb` for
    // `OutRule`) and co-installs a per-site MATCH receiver that re-sources the operand AND rebuilds
    // the NESTED reduct in its body from the SPREAD (not the report σ). Admitting a rule here (skipping
    // its defer) shrinks `deferred`, so the gate stops rejecting it — the DEPTH-2 generalization of
    // S-binder SLICE 3b's `structural_ac_dispatch`. This is what upgrades In/Out from the REPORT path
    // to the SPREAD path, eliminating the dual runtime path.
    let nested_structural_ac_dispatch = crate::rho_net_nested_structural_ac_match_entries(def);
    let nested_structural_ac_admitted: HashSet<&str> = nested_structural_ac_dispatch
        .iter()
        .map(|entry| entry.fired_rule_label.as_str())
        .collect();

    // Stage 4 (S-binder): ADMIT the binder/β-substitution rewrites. A subst rewrite lowered to a
    // `SubstRewrite` σ-receiver (NOT a base rewrite), so `site_channel` misses it and it would
    // otherwise defer `NotBaseRewrite` (the gate would reject the match path). Its LHS
    // `App(Lam(fun), arg)` is a NESTED App over a BINDER constructor; the binder constructor
    // reflects to the reserved `^lambda`/`^multilambda` tag (`binder_reflect_tags`) — the SAME tag
    // the M-reflect subject reflection emits for a runtime `Lam(scope)` node — so
    // `convert_subst_lhs` yields the `App(^lambda(fun), arg)` automaton entry that MATCHES the
    // reflected subject + CAPTURES `(fun, arg)`. Its accept routes to the subst σ-receiver SOURCE
    // channel (exactly like a base rewrite's accept), where the installed `SubstRewrite` σ-receiver
    // forwards the fun (scope-body) slot. In the MATCH path that slot carries the RAW captured body
    // (the automaton's in-Rho capture), NOT the host-computed reduct — the capture-avoiding
    // substitution (the in-Rho subst TRS) is S-binder slice 2. This slice LOCATES + captures.
    let subst_sites = crate::rho_net_subst_injection_sites(def);
    let subst_site_channel: HashMap<&str, &str> =
        subst_sites.iter().map(|s| (s.rule_label.as_str(), s.channel.as_str())).collect();
    let binder_tags = binder_reflect_tags(def);

    let mut pairs: Vec<(PatternId, DvPattern<String>)> = Vec::with_capacity(def.rewrites.len());
    let mut accept_channels: Vec<(PatternId, String)> = Vec::new();
    let mut deferred: Vec<DeferredRewrite> = Vec::new();

    for (index, rewrite) in def.rewrites.iter().enumerate() {
        let label = rewrite.name.to_string();
        let channel = match site_channel.get(label.as_str()) {
            Some(channel) => channel.to_string(),
            None => {
                // Admitted via the AC match path (its bag is located + fired in Rho by the match
                // driver), the contextual match path (its holes are located + reassembled in Rho), the
                // structural-AC match path (its bag is located under the `^lambda`/nested descent and
                // fired in Rho), or the DEPTH-2 nested structural-AC match path (the Ambient
                // `InRule`/`OutRule`: its operand is located + its nested reduct rebuilt in Rho) — do
                // NOT defer, so the gate admits it.
                if ac_admitted.contains(label.as_str())
                    || contextual_admitted.contains(label.as_str())
                    || structural_ac_admitted.contains(label.as_str())
                    || nested_structural_ac_admitted.contains(label.as_str())
                {
                    continue;
                }
                // Stage 4 (S-binder): admit a binder/β-substitution rewrite as a `^lambda`-remapped
                // nested App automaton entry, routed to its `SubstRewrite` σ-receiver source channel
                // (the coherence anchor, exactly like a base rewrite's accept). A binder LHS with no
                // positional image (e.g. a subst/collection-search arg) fails closed via
                // `convert_subst_lhs`.
                if let Some(channel) = subst_site_channel.get(label.as_str()) {
                    match convert_subst_lhs(&rewrite.left, &binder_tags) {
                        Ok(pattern) => {
                            pairs.push((PatternId(index), pattern));
                            accept_channels.push((PatternId(index), (*channel).to_string()));
                        },
                        Err(reject) => {
                            deferred.push(DeferredRewrite {
                                rule_label: label,
                                reason: DeferReason::Convert(reject),
                            });
                        },
                    }
                    continue;
                }
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
            bare_label: entry.bare_label.clone(),
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
        ac_dispatch,
        contextual_dispatch,
        structural_ac_dispatch,
        nested_structural_ac_dispatch,
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

    // Stage 4 (S-AC): co-install the HashBag AC redexes. Each admitted AC family
    // ([`InRhoMatchingRuleset::ac_dispatch`]) has NO automaton entry (its `AcApp` has no positional
    // image), so it is located by a SEPARATE walk of the subject ([`ac_match_call_par`]) rather than
    // by `collect_redex_sites`: at every bag position whose op is admitted, a per-site AC receiver
    // reads the site-keyed `ac:` carrier the walk publishes the SUBJECT bag's soup on (not the
    // report σ) and picks k-of-n + binds `rest` in ONE atomic `consume`. AC leaves read only their
    // OWN disjoint site-keyed carrier (Red-team #4/#5), so they are ALWAYS co-installable — with
    // each other AND with the base networks (disjoint `ac:` vs `loc:`/`cap:` channels) — and never
    // trigger the nested-multi-site contention gate.
    let ac_call = ac_match_call_par(
        subject,
        &ruleset.ac_dispatch,
        root_site,
        out_channel,
        &ruleset.language_fingerprint,
    );
    call = call.append(ac_call);

    // Stage 4 (S-binder SLICE 3b): co-install the STRUCTURAL non-linear AC redexes (Ambient
    // `OpenRule`). Each admitted structural-AC family ([`InRhoMatchingRuleset::structural_ac_dispatch`])
    // has NO automaton entry (its `AcApp` bag has no positional image), so — like a linear AC redex —
    // it is located by a SEPARATE walk of the subject ([`structural_ac_match_call_par`]) rather than
    // by `collect_redex_sites`: at every admitted bag position (reached by the SAME `^lambda`/nested
    // descent, so a bag under `new(x, ·)` is located too) a per-site MATCH receiver reads the
    // site-keyed `ac:` carrier the walk publishes the SUBJECT bag's soup on (not the report σ), binds
    // the k elements + structural reducts + `rest` from the bag, and fires `{r0, …, rest}` in ONE
    // atomic `consume` under the `N ≡ N` guard. Structural-AC leaves read only their OWN disjoint
    // site-keyed carrier, so they are ALWAYS co-installable — with each other, the linear AC leaves,
    // AND the base networks (disjoint `ac:` vs `loc:`/`cap:` channels) — and never trigger the
    // nested-multi-site contention gate.
    let structural_ac_call = structural_ac_match_call_par(
        subject,
        &ruleset.structural_ac_dispatch,
        root_site,
        out_channel,
        &ruleset.language_fingerprint,
    );
    call = call.append(structural_ac_call);

    // Stage 4 (Ambient In/Out): co-install the DEPTH-2 NESTED structural non-linear AC redexes (the
    // Ambient `InRule`/`OutRule`). Each admitted nested family
    // ([`InRhoMatchingRuleset::nested_structural_ac_dispatch`]) has NO automaton entry (its nested
    // `AcApp` has no positional image), so — like every AC redex — it is located by a SEPARATE walk
    // of the subject ([`nested_structural_ac_match_call_par`]) rather than by `collect_redex_sites`:
    // at every node whose head is a nested rule's LHS root constructor (a bag op `PPar` for `InRule`,
    // a wrapper `PAmb` for `OutRule`) a per-site MATCH receiver reads the site-keyed `ac:` carrier the
    // walk publishes the SUBJECT operand on (not the report σ), binds every σ slot from the operand,
    // and — matching the DEPTH-2 nested pattern + the cross-level `M ≡ M` guard — REBUILDS the nested
    // reduct in its body, firing in ONE atomic `consume`. Nested-AC leaves read only their OWN disjoint
    // site-keyed carrier, so they are ALWAYS co-installable — with each other, the flat/linear AC
    // leaves, AND the base networks (disjoint `ac:` vs `loc:`/`cap:` channels) — and never trigger the
    // nested-multi-site contention gate. This SPREAD path replaces the In/Out REPORT path (dual-path
    // elimination); the host-σ `structural_ac_contract_call` replay survives only as the fail-closed
    // fallback (reached when the gate defers, like every other family).
    let nested_structural_ac_call = nested_structural_ac_match_call_par(
        subject,
        &ruleset.nested_structural_ac_dispatch,
        root_site,
        out_channel,
        &ruleset.language_fingerprint,
    );
    call = call.append(nested_structural_ac_call);

    let spread = spread_term_par(subject, &ruleset.language_fingerprint, root_site);
    Ok((call.append(spread), sites.len()))
}

/// Stage 4 (S-contextual) — build the in-Rho contextual-JOIN match call for `subject`: LOCATE the
/// outer context `K`'s hole positions' PREMISE redexes in Rho, route each reduced hole to the
/// installed [`contextual_join_receiver_par`](crate::contextual_join_receiver_par)'s premise channel,
/// and let the reused join reassemble ⟦K'⟧ — the reduced holes coming from the automaton's NESTED
/// FIRINGS, never the host-σ [`reconstruct_contractum`](crate::reconstruct_contractum) report replay.
///
/// The outer context spine `K` is the reflected subject with `n` distinguished hole positions
/// ℓ_0..ℓ_{n-1} (the premise subjects). Each hole position is derived from the contextual rule's LHS
/// (the `(op, index)` path to premise `i`'s source variable, folded through [`spread_child_location`]
/// — the SAME derivation `collect_redex_sites` uses). At each hole site the automaton LOCATES the
/// premise redex (its head `Match` + `cap:` capture in Rho) and fires its σ-receiver with the
/// intermediate [`contextual_premise_hole_channel`] `ph:c(ℓ_i)` as its dynamic out; the
/// [`contextual_hole_bridge_par`] then re-delivers the reduced hole `T_i` on the join's premise
/// channel `c(ℓ_i)` (the LAST hole additionally carries the dynamic out — the join's
/// `(T_{n-1}, out)` bind), where the installed join binds all `n` reduced holes and emits
/// ⟦K'⟧ = ⟦K(T_0..T_{n-1})⟧ on `@out`. The hole↔channel correspondence (premise `i`'s located firing
/// routes to premise channel `i`) is what places each reduced hole at its context position in `K'`.
///
/// The `n` hole sites are DISJOINT-PREFIX locations, so their co-installed networks read disjoint
/// `loc:`/`cap:` channels (like the locate-all multi-site install), and the `ph:` intermediates +
/// the join's `c(ℓ_i)` are all disjoint — so the single-shot bridges and the persistent join never
/// race. `n > 1` co-installed networks require a flat-only ruleset (a nested-App entry would descend
/// into a co-installed site — [`AutomatonUnsupported::NestedEntryMultiSite`]).
///
/// FAIL-CLOSED ([`AutomatonUnsupported::ContextualHoleMismatch`]) when `subject`/`ruleset` does not
/// match `K`'s hole structure: 0 or ≥2 contextual families, a premise-channel/hole-position drift,
/// or — the load-bearing check — the subject's LOCATED rule-root redexes are not EXACTLY the `n`
/// expected hole positions (a normal form, a deeper redex inside a hole, or an extra redex outside
/// the holes). Never a wrong reassembly. Reduced holes come from the automaton's IN-RHO nested
/// firings, never the host-σ [`reconstruct_contractum`](crate::reconstruct_contractum) report replay.
pub fn contextual_match_call_par(
    ruleset: &InRhoMatchingRuleset,
    subject: &GroundTerm,
    root_site: &str,
    out_channel: &str,
) -> Result<Par, AutomatonUnsupported> {
    // Exactly one contextual family (the single congruence context to close). 0 or ≥2 fail closed.
    let [entry] = ruleset.contextual_dispatch.as_slice() else {
        return Err(AutomatonUnsupported::ContextualHoleMismatch);
    };
    let n = entry.premise_channels.len();
    // A congruence has ≥1 premise, and each premise contributes one channel AND one hole position
    // (aligned index-for-index) — a drift means the entry was derived from a mismatched def.
    if n == 0 || n != entry.hole_positions.len() {
        return Err(AutomatonUnsupported::ContextualHoleMismatch);
    }

    // The `n` expected hole sites: fold `spread_child_location` over each premise's `(op, index)`
    // path from the spread root (the SAME derivation `collect_redex_sites` publishes `loc:`/`cap:`
    // at, so the network built at a hole site reads exactly what the spread published there).
    let expected_sites: Vec<String> = entry
        .hole_positions
        .iter()
        .map(|path| {
            path.iter().fold(root_site.to_string(), |site, (op, index)| {
                spread_child_location(&site, op, *index)
            })
        })
        .collect();

    // LOAD-BEARING bijection check: the subject's located rule-root redexes must be EXACTLY the `n`
    // expected hole positions (as a multiset). This rejects a normal form (0 hole redexes), a deeper
    // nested redex inside a hole, and an extra redex outside the holes — so the reused join binds
    // exactly the `n` located firings the context expects, never a wrong reassembly.
    let roots = rule_lhs_root_constructors(ruleset);
    let mut located: Vec<String> = Vec::new();
    collect_redex_sites(subject, root_site, &roots, &mut located);
    let mut located_sorted = located;
    located_sorted.sort();
    let mut expected_sorted = expected_sites.clone();
    expected_sorted.sort();
    if located_sorted != expected_sorted {
        return Err(AutomatonUnsupported::ContextualHoleMismatch);
    }

    // Co-installing ≥2 per-hole networks over ONE spread is contention-free only for a flat-only
    // ruleset (a nested-App entry would descend `loc:` head tags into a co-installed site). A single
    // hole (n = 1) has no co-installation and admits a nested entry.
    if n > 1 && !ruleset_all_entries_flat(ruleset) {
        return Err(AutomatonUnsupported::NestedEntryMultiSite);
    }

    // Build one positional network per hole site — each routing its accept to that hole's
    // intermediate `ph:c(ℓ_i)` channel — plus a per-hole bridge re-delivering the reduced hole on
    // the join's premise channel `c(ℓ_i)` in the join's bind ABI (the LAST hole carries `@out`).
    let mut call = Par::default();
    for (index, expected_site) in expected_sites.iter().enumerate() {
        let premise_channel = &entry.premise_channels[index];
        let hole_channel = contextual_premise_hole_channel(premise_channel);
        let targets: Vec<AutomatonAcceptTarget> = ruleset
            .accept_channels
            .iter()
            .map(|(pattern, accept_channel)| AutomatonAcceptTarget {
                pattern: *pattern,
                accept_channel: accept_channel.clone(),
                out_channel: hole_channel.clone(),
            })
            .collect();
        let network = multi_pattern_receiver_network_par(
            &ruleset.automaton.view(),
            expected_site,
            &targets,
            &ruleset.language_fingerprint,
        )?;
        call = call.append(network);

        let is_last = index + 1 == n;
        let bridge = contextual_hole_bridge_par(
            &hole_channel,
            premise_channel,
            if is_last { Some(out_channel) } else { None },
        );
        call = call.append(bridge);
    }

    // ONE spread of the whole subject — every hole network reads its site's channels from it.
    let spread = spread_term_par(subject, &ruleset.language_fingerprint, root_site);
    Ok(call.append(spread))
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

/// A-S2 (D-stage demotion): the STATIC capability gate — the term-INDEPENDENT strengthening of
/// [`in_rho_match_gate_reject`]. Admits a language for REPORT-FREE in-Rho matching iff every
/// FIREABLE rewrite is un-deferred, so the report-free match path
/// (`rho_net_match_invocation_to`) never needs the Dovetail report's fired-rule labels to know
/// the located redexes are all matchable in Rho.
///
/// FIREABLE means the rewrite can appear in `report.rewrite_justifications`: a
/// CONGRUENCE-ONLY rewrite (`| S ~> T |- K(S) ~> K(T)`, a rule whose NON-EMPTY premise set is
/// ALL [`mettail_ast::language::Premise::Congruence`] — [`congruence_only_premises`], the
/// A-S5.1 `any→all` hardening)
/// NEVER does — the e-graph closes contexts implicitly, so its label is never a fired-rule label
/// and the dynamic gate never consulted it. The static gate therefore EXEMPTS congruence-only
/// rewrites (enumerated from `def.rewrites[..].premises`) rather than demanding their admission;
/// demanding it would reject languages the dynamic gate admits today (e.g. every language with
/// auto-injected cast congruence rules — all singleton-congruence-premise, for which `all` ≡
/// `any`). A MIXED-premise rewrite (congruence + a freshness / guard / relation side condition)
/// is deliberately NOT exempt under the hardened predicate: its non-congruence side condition
/// makes "never fireable" unestablishable from the congruence fact alone, so it fails closed.
/// The hardening is proven outcome-neutral corpus-wide (red-team F13): the only bundled
/// multi-premise rewrite, `bicongdemo`'s `NodeCong`, carries two congruence premises and stays
/// exempt.
///
/// Soundness relative to the dynamic gate: for any complete report,
/// `fired ⊆ {fireable rewrites}`, so `static-admitted ⇒ dynamic-admitted` — the static gate is
/// STRICTLY at least as strong on fireable rules, hence a static admission can never let a
/// firing through that the dynamic gate would have rejected. Model: the FV (ix)
/// `install_admits` obligation (`InRhoEncoderTotalOrReject.v`); the report-checked ⟺ deferral
/// coupling lives in `DovetailRhoLanguageBackendWrapper.v`.
///
/// Returns `Ok(())` when admitted, `Err(deferred_fireable)` — every genuinely-deferred FIREABLE
/// rewrite with its [`DeferReason`] — when rejected (fail-closed to the lazy-report path).
pub fn in_rho_static_gate(
    ruleset: &InRhoMatchingRuleset,
    def: &LanguageDef,
) -> Result<(), Vec<DeferredRewrite>> {
    // The congruence-ONLY rewrites: never fireable (no explicit Dovetail firing), so their
    // deferral is irrelevant to the report-free match path — the e-graph congruence closure (or
    // the admitted contextual family) covers them, exactly as it does on the dynamic-gate path.
    // A-S5.1 hardening: the SHARED `congruence_only_premises` predicate (all + non-empty, the
    // same predicate the install boundary's exempt disposition tests in
    // `rho_net_lower::exempt_or_record`) replaces the previous `any(Premise::Congruence)` scan,
    // so a future mixed-premise rewrite can never ride the exemption past its side condition.
    let congruence_exempt: HashSet<String> = def
        .rewrites
        .iter()
        .filter(|rewrite| congruence_only_premises(&rewrite.premises))
        .map(|rewrite| rewrite.name.to_string())
        .collect();

    let rejects: Vec<DeferredRewrite> = ruleset
        .deferred
        .iter()
        .filter(|entry| !congruence_exempt.contains(&entry.rule_label))
        .cloned()
        .collect();

    if rejects.is_empty() {
        Ok(())
    } else {
        Err(rejects)
    }
}

/// A-S2 (D-stage demotion): count the LOCATED native-process sites of `subject` — the positions
/// whose head constructor is an ADMITTED native entry's bare head label
/// ([`NativeDispatch::bare_label`]). This replaces the report-firing count of the report-carrying
/// match path (`rho_invocation.rs`'s per-justification native scan): the automaton's positional
/// walk over the STRUCTURALLY REFLECTED subject is exactly the site set the locate-all install
/// dispatches on, so the count is derived from term + metadata alone.
///
/// A-S3 (native dispatch boundary tightening): the report-free match path now uses the per-rule
/// refinement [`located_native_site_count_for`] to ADMIT located native sites (registering the
/// rule's machine-side handler contract and co-installing one contract-call bridge per site)
/// rather than failing closed on this aggregate; the aggregate remains the total-count view
/// (`Σ` of the per-rule counts over `native_dispatch`).
pub fn located_native_site_count(ruleset: &InRhoMatchingRuleset, subject: &GroundTerm) -> usize {
    if ruleset.native_dispatch.is_empty() {
        return 0;
    }
    let native_roots: BTreeSet<String> = ruleset
        .native_dispatch
        .iter()
        .map(|dispatch| dispatch.bare_label.clone())
        .collect();
    let mut sites: Vec<String> = Vec::new();
    collect_redex_sites(subject, "site0", &native_roots, &mut sites);
    sites.len()
}

/// A-S3 (native dispatch boundary tightening): count the LOCATED sites of ONE native rule — the
/// positions of `subject` whose head constructor is `bare_label` — by the SAME positional walk as
/// [`located_native_site_count`] restricted to that single head.
///
/// The report-free match body uses the per-rule count to co-install one contract-call bridge
/// ([`native_locate_contract_bridge_par`](crate::native_locate_contract_bridge_par)) PER located
/// site of each admitted native rule: every site's accept drives its own machine-side handler
/// invocation (the bridges are identical value-free forwarders, so multiplicity is all that
/// matters — no cross-talk is possible), which is what lifts the report path's single-native-firing
/// restriction on the ADMITTED path.
pub fn located_native_site_count_for(
    ruleset: &InRhoMatchingRuleset,
    subject: &GroundTerm,
    bare_label: &str,
) -> usize {
    if !ruleset
        .native_dispatch
        .iter()
        .any(|dispatch| dispatch.bare_label == bare_label)
    {
        return 0;
    }
    let roots: BTreeSet<String> = std::iter::once(bare_label.to_string()).collect();
    let mut sites: Vec<String> = Vec::new();
    collect_redex_sites(subject, "site0", &roots, &mut sites);
    sites.len()
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

    /// The CtxDemo ruleset: a base rewrite `Flip: Swap(x,y) ~> Pair(y,x)` (reduces the hole) and a
    /// UNARY congruence `WrapCong: | S ~> T |- Wrap(S) ~> Wrap(T)` (the outer context Wrap(_)).
    fn ctx_demo_def() -> LanguageDef {
        syn::parse_str(
            r#"
                name: CtxRulesetGen,
                types { Proc }
                terms {
                    A . |- "A" : Proc ;
                    B . |- "B" : Proc ;
                    Pair . x:Proc, y:Proc |- "pair" "(" x "," y ")" : Proc ;
                    Swap . x:Proc, y:Proc |- "swap" "(" x "," y ")" : Proc ;
                    Wrap . x:Proc |- "wrap" "(" x ")" : Proc ;
                }
                equations {}
                rewrites {
                    Flip . |- (Swap x y) ~> (Pair y x) ;
                    WrapCong . | S ~> T |- (Wrap S) ~> (Wrap T) ;
                }
            "#,
        )
        .expect("the CtxDemo ruleset fragment parses")
    }

    /// The bare `GString` name of a single-expr `Par` (a `loc:`/`ph:`/premise channel), or `None`.
    fn par_gstring(par: &Par) -> Option<String> {
        use models::rhoapi::expr::ExprInstance;
        match par.exprs.first()?.expr_instance.as_ref()? {
            ExprInstance::GString(s) => Some(s.clone()),
            _ => None,
        }
    }

    #[test]
    fn compile_admits_the_contextual_family() {
        // Stage 4 S-contextual: WrapCong is ADMITTED via `contextual_dispatch` (its hole is located
        // + reassembled in Rho), so the gate no longer skips it; it is NOT an automaton entry (the
        // base automaton dispatches only on Swap, the hole's premise redex root).
        let ruleset = compile_in_rho_matching_ruleset(&ctx_demo_def());
        assert_eq!(ruleset.contextual_dispatch.len(), 1, "one contextual family");
        assert_eq!(ruleset.contextual_dispatch[0].fired_rule_label, "WrapCong");
        assert_eq!(
            ruleset.contextual_dispatch[0].premise_channels.len(),
            1,
            "WrapCong is a unary congruence (one premise channel)"
        );
        assert!(
            !ruleset.deferred.iter().any(|d| d.rule_label == "WrapCong"),
            "WrapCong is admitted (contextual), not deferred: {:?}",
            ruleset.deferred
        );
        assert_eq!(
            rule_lhs_root_constructors(&ruleset),
            ["Swap".to_string()].into_iter().collect::<BTreeSet<_>>(),
            "the base automaton dispatches only on the hole's premise root Swap (Wrap is inert)"
        );
    }

    #[test]
    fn contextual_match_call_routes_the_unary_hole_to_the_premise_channel() {
        // Wrap(Swap(A, B)): the hole redex Swap is at Wrap.0. The contextual match call co-installs
        // the hole bridge reading `ph:{premise_channel}` (where the located Swap's nested firing
        // lands) and re-delivering on the join's premise channel — the IN-RHO hole routing.
        let ruleset = compile_in_rho_matching_ruleset(&ctx_demo_def());
        let swap = GroundTerm::new(
            "Swap",
            vec![GroundTerm::new("A", Vec::new()), GroundTerm::new("B", Vec::new())],
        );
        let subject = GroundTerm::new("Wrap", vec![swap]);
        let call = contextual_match_call_par(&ruleset, &subject, "site0", "OUT")
            .expect("the unary contextual match call serializes");

        let premise = &ruleset.contextual_dispatch[0].premise_channels[0];
        let hole_channel = format!("ph:{premise}");
        let has_bridge = call.receives.iter().any(|receive| {
            receive.binds.iter().any(|bind| {
                bind.source.as_ref().and_then(par_gstring).as_deref()
                    == Some(hole_channel.as_str())
            })
        });
        assert!(
            has_bridge,
            "the contextual match call must co-install the hole bridge reading {hole_channel}"
        );
    }

    #[test]
    fn contextual_match_call_fails_closed_off_the_unary_shape() {
        let ruleset = compile_in_rho_matching_ruleset(&ctx_demo_def());
        // A normal form Wrap(Pair(A, B)): Pair is inert, so NO hole redex is located → fail closed
        // (the single-hole join has nothing to reassemble).
        let normal = GroundTerm::new(
            "Wrap",
            vec![GroundTerm::new(
                "Pair",
                vec![GroundTerm::new("A", Vec::new()), GroundTerm::new("B", Vec::new())],
            )],
        );
        assert_eq!(
            contextual_match_call_par(&ruleset, &normal, "site0", "OUT"),
            Err(AutomatonUnsupported::ContextualHoleMismatch),
            "a normal form has no located hole redex — fail closed"
        );

        // Two hole redexes Pair(Swap(A,B), Swap(B,A)) under the SAME single-hole context: the located
        // redexes (Wrap.0/Pair.0, Wrap.0/Pair.1) are NOT the expected single hole (Wrap.0) → the
        // bijection check fails closed (an extra redex inside the hole).
        let two = GroundTerm::new(
            "Wrap",
            vec![GroundTerm::new(
                "Pair",
                vec![
                    GroundTerm::new(
                        "Swap",
                        vec![GroundTerm::new("A", Vec::new()), GroundTerm::new("B", Vec::new())],
                    ),
                    GroundTerm::new(
                        "Swap",
                        vec![GroundTerm::new("B", Vec::new()), GroundTerm::new("A", Vec::new())],
                    ),
                ],
            )],
        );
        assert_eq!(
            contextual_match_call_par(&ruleset, &two, "site0", "OUT"),
            Err(AutomatonUnsupported::ContextualHoleMismatch),
            "located redexes that are not exactly the expected hole positions — fail closed"
        );
    }

    /// A 2-ARY congruence `NodeCong: | S0 ~> T0, S1 ~> T1 |- Node(S0, S1) ~> Node(T0, T1)` (plus the
    /// base `Flip` to reduce each hole) — the n-ary (n > 1) contextual shape.
    fn bicong_demo_def() -> LanguageDef {
        syn::parse_str(
            r#"
                name: BiCongRulesetGen,
                types { Proc }
                terms {
                    A . |- "A" : Proc ;
                    B . |- "B" : Proc ;
                    C . |- "C" : Proc ;
                    D . |- "D" : Proc ;
                    Pair . x:Proc, y:Proc |- "pair" "(" x "," y ")" : Proc ;
                    Swap . x:Proc, y:Proc |- "swap" "(" x "," y ")" : Proc ;
                    Node . x:Proc, y:Proc |- "node" "(" x "," y ")" : Proc ;
                }
                equations {}
                rewrites {
                    Flip . |- (Swap x y) ~> (Pair y x) ;
                    NodeCong . | S0 ~> T0, S1 ~> T1 |- (Node S0 S1) ~> (Node T0 T1) ;
                }
            "#,
        )
        .expect("the 2-ary congruence fragment parses")
    }

    #[test]
    fn contextual_match_entry_locates_the_two_hole_positions() {
        // The 2-ary NodeCong hole positions: S0 at Node.0, S1 at Node.1 — aligned with the two
        // premise channels in premise order.
        let ruleset = compile_in_rho_matching_ruleset(&bicong_demo_def());
        assert_eq!(ruleset.contextual_dispatch.len(), 1, "one contextual family (NodeCong)");
        let entry = &ruleset.contextual_dispatch[0];
        assert_eq!(entry.premise_channels.len(), 2, "two congruence premises ⇒ two channels");
        assert_eq!(
            entry.hole_positions,
            vec![vec![("Node".to_string(), 0)], vec![("Node".to_string(), 1)]],
            "S0 at Node.0, S1 at Node.1 (premise order)"
        );
    }

    #[test]
    fn contextual_match_call_routes_each_of_two_holes_to_its_own_premise_channel() {
        // Node(Swap(A, B), Swap(C, D)): two hole redexes at Node.0 and Node.1. The n-ary match call
        // co-installs a bridge per hole, each reading `ph:{premise_channel_i}` and re-delivering on
        // its OWN join premise channel — so K'(T0, T1) = Node(Pair(B,A), Pair(D,C)) reassembles with
        // each reduced hole at its context position.
        let ruleset = compile_in_rho_matching_ruleset(&bicong_demo_def());
        let swap = |a: &str, b: &str| {
            GroundTerm::new(
                "Swap",
                vec![GroundTerm::new(a, Vec::new()), GroundTerm::new(b, Vec::new())],
            )
        };
        let subject = GroundTerm::new("Node", vec![swap("A", "B"), swap("C", "D")]);
        let call = contextual_match_call_par(&ruleset, &subject, "site0", "OUT")
            .expect("the 2-ary contextual match call serializes");

        // Both intermediate hole channels are read by a co-installed bridge (distinct per hole).
        for premise in &ruleset.contextual_dispatch[0].premise_channels {
            let hole_channel = format!("ph:{premise}");
            let has_bridge = call.receives.iter().any(|receive| {
                receive.binds.iter().any(|bind| {
                    bind.source.as_ref().and_then(par_gstring).as_deref()
                        == Some(hole_channel.as_str())
                })
            });
            assert!(has_bridge, "a hole bridge must read {hole_channel}");
        }
    }

    #[test]
    fn contextual_match_call_fails_closed_when_a_hole_is_a_normal_form() {
        // Node(Swap(A, B), Pair(C, D)): only Node.0 has a redex (Pair is inert), so the located
        // redexes {Node.0} ≠ the expected holes {Node.0, Node.1} → fail closed (a hole is not a
        // redex — the join could never bind that hole).
        let ruleset = compile_in_rho_matching_ruleset(&bicong_demo_def());
        let subject = GroundTerm::new(
            "Node",
            vec![
                GroundTerm::new(
                    "Swap",
                    vec![GroundTerm::new("A", Vec::new()), GroundTerm::new("B", Vec::new())],
                ),
                GroundTerm::new(
                    "Pair",
                    vec![GroundTerm::new("C", Vec::new()), GroundTerm::new("D", Vec::new())],
                ),
            ],
        );
        assert_eq!(
            contextual_match_call_par(&ruleset, &subject, "site0", "OUT"),
            Err(AutomatonUnsupported::ContextualHoleMismatch),
            "a hole that is not a located redex fails closed"
        );
    }

    /// Sub-slice 3 (declared-join Comm): a Comm authored AS A DECLARED JOIN — a congruence rewrite
    /// with a premise, here NAMED `Comm` to make the point — `Comm: | S ~> T |- Send(S) ~> Send(T)`.
    /// The classification routes by STRUCTURE (`Premise::Congruence`), not by name, so a declared-join
    /// Comm is a `ContextualRewrite` and rides `contextual_match_call_par` IDENTICALLY to WrapCong.
    /// (No bundled language authors a Comm this way — the bundled Comms are AC-bag PROCESS rules
    /// `PPar{...} ~> PPar{...}` that ride S-AC — so this is the honest, code-grounded demonstration
    /// that the declared-join Comm case is subsumed by the contextual mechanism.)
    fn comm_join_demo_def() -> LanguageDef {
        syn::parse_str(
            r#"
                name: CommJoinRulesetGen,
                types { Proc }
                terms {
                    A . |- "A" : Proc ;
                    B . |- "B" : Proc ;
                    Pair . x:Proc, y:Proc |- "pair" "(" x "," y ")" : Proc ;
                    Swap . x:Proc, y:Proc |- "swap" "(" x "," y ")" : Proc ;
                    Send . x:Proc |- "send" "(" x ")" : Proc ;
                }
                equations {}
                rewrites {
                    Flip . |- (Swap x y) ~> (Pair y x) ;
                    Comm . | S ~> T |- (Send S) ~> (Send T) ;
                }
            "#,
        )
        .expect("the declared-join Comm fragment parses")
    }

    // ————————————————————————————————————————————————————————————————————————————————
    // A-S2: the STATIC gate (`in_rho_static_gate`) — term-independent admission for the
    // report-free match path.
    // ————————————————————————————————————————————————————————————————————————————————

    #[test]
    fn static_gate_admits_a_fully_matchable_language() {
        // SwapDemo: one flat structural rewrite, nothing deferred → the static gate admits
        // without consulting any report.
        let def = swap_demo_def();
        let ruleset = compile_in_rho_matching_ruleset(&def);
        assert!(ruleset.deferred.is_empty(), "SwapDemo defers nothing: {:?}", ruleset.deferred);
        assert_eq!(in_rho_static_gate(&ruleset, &def), Ok(()));
    }

    #[test]
    fn static_gate_exempts_congruence_premise_rules() {
        // A congruence rewrite (WrapCong: `| S ~> T |- Wrap(S) ~> Wrap(T)`) NEVER appears as a
        // fired rule in `rewrite_justifications` (the e-graph closes contexts implicitly), so the
        // static gate must EXEMPT it rather than demand its admission. The compiled CtxDemo
        // ruleset admits WrapCong contextually (deferred empty); to exercise the exemption we
        // simulate the deferral a NON-contextual compilation would produce (`deferred` is a `pub`
        // field — the same supported direct-construction surface the admission-matrix audit uses).
        let def = ctx_demo_def();
        let mut ruleset = compile_in_rho_matching_ruleset(&def);
        assert_eq!(in_rho_static_gate(&ruleset, &def), Ok(()), "CtxDemo admits as compiled");

        ruleset.deferred.push(DeferredRewrite {
            rule_label: "WrapCong".to_string(),
            reason: DeferReason::NotBaseRewrite,
        });
        assert_eq!(
            in_rho_static_gate(&ruleset, &def),
            Ok(()),
            "a deferred CONGRUENCE-premise rule is exempt — it can never fire, so its deferral \
             cannot make a located redex unmatchable"
        );
    }

    #[test]
    fn static_gate_rejects_a_genuinely_deferred_fireable_rule() {
        // `Flip` is a FIREABLE base rewrite (no congruence premise). If it were deferred, the
        // report-free path could locate a Flip redex the automaton cannot fire → the static gate
        // must reject (fail-closed to the lazy-report path), returning exactly the deferred entry.
        let def = ctx_demo_def();
        let mut ruleset = compile_in_rho_matching_ruleset(&def);
        let deferred = DeferredRewrite {
            rule_label: "Flip".to_string(),
            reason: DeferReason::NotBaseRewrite,
        };
        ruleset.deferred.push(deferred.clone());
        assert_eq!(in_rho_static_gate(&ruleset, &def), Err(vec![deferred]));
    }

    #[test]
    fn static_gate_rejects_every_defer_reason_variant() {
        // Every `DeferReason` variant on a FIREABLE rule rejects — the gate keys on
        // fireability, not on WHY the rule was deferred (any deferral means the located redex
        // could not fire in Rho). Covers: NotBaseRewrite, Ac, and all three
        // `Convert(PatternConvertReject)` sub-reasons.
        let def = ctx_demo_def();
        let reasons = [
            DeferReason::NotBaseRewrite,
            DeferReason::Ac,
            DeferReason::Convert(PatternConvertReject::Binder),
            DeferReason::Convert(PatternConvertReject::Subst),
            DeferReason::Convert(PatternConvertReject::CollectionSearch),
        ];
        for reason in reasons {
            let mut ruleset = compile_in_rho_matching_ruleset(&def);
            let deferred = DeferredRewrite {
                rule_label: "Flip".to_string(),
                reason: reason.clone(),
            };
            ruleset.deferred.push(deferred.clone());
            assert_eq!(
                in_rho_static_gate(&ruleset, &def),
                Err(vec![deferred]),
                "a fireable rule deferred with {reason:?} must reject"
            );
        }
    }

    #[test]
    fn static_gate_separates_exempt_from_fireable_deferrals() {
        // A mixed deferral list: the congruence-premise WrapCong entry is filtered out, the
        // fireable Flip entry is returned — the reject payload names exactly the genuinely
        // deferred fireable rules.
        let def = ctx_demo_def();
        let mut ruleset = compile_in_rho_matching_ruleset(&def);
        ruleset.deferred.push(DeferredRewrite {
            rule_label: "WrapCong".to_string(),
            reason: DeferReason::NotBaseRewrite,
        });
        let fireable = DeferredRewrite {
            rule_label: "Flip".to_string(),
            reason: DeferReason::Convert(PatternConvertReject::Binder),
        };
        ruleset.deferred.push(fireable.clone());
        assert_eq!(in_rho_static_gate(&ruleset, &def), Err(vec![fireable]));
    }

    /// The NativeDemo-shaped fold language (`PowInt . a:Int, b:Int |- a "^" b : Int ![…] fold`):
    /// one ADMITTED native entry (bare head `PowInt`), no base rewrites.
    fn native_demo_def() -> LanguageDef {
        syn::parse_str(
            r#"
                name: NativeRulesetGen,
                types {
                    ![i64] as Int
                }
                terms {
                    PowInt . a:Int, b:Int |- a "^" b : Int ![a.pow(b as u32)] fold;
                }
                equations {}
                rewrites {}
            "#,
        )
        .expect("the native fold fragment parses")
    }

    #[test]
    fn native_dispatch_carries_the_bare_head_label() {
        // A-S2: `NativeDispatch.bare_label` is the automaton entry's root op — what the
        // report-free path counts located sites by.
        let ruleset = compile_in_rho_matching_ruleset(&native_demo_def());
        assert_eq!(ruleset.native_dispatch.len(), 1, "one admitted native family (PowInt)");
        assert_eq!(ruleset.native_dispatch[0].bare_label, "PowInt");
        assert_eq!(ruleset.native_dispatch[0].fired_rule_label, "Int_PowInt");
        assert_eq!(ruleset.native_dispatch[0].arity, 2);
    }

    #[test]
    fn located_native_site_count_counts_native_heads_only() {
        let ruleset = compile_in_rho_matching_ruleset(&native_demo_def());
        let two = GroundTerm::new("NumLit", vec![GroundTerm::new("2", Vec::new())]);
        let three = GroundTerm::new("NumLit", vec![GroundTerm::new("3", Vec::new())]);

        // A root PowInt redex → 1 located native site.
        let root = GroundTerm::new("PowInt", vec![two.clone(), three.clone()]);
        assert_eq!(located_native_site_count(&ruleset, &root), 1);

        // A NESTED PowInt inside a PowInt → 2 located native sites (the walk is positional,
        // pre-order — the same site set the locate-all install dispatches on).
        let nested = GroundTerm::new("PowInt", vec![root.clone(), three.clone()]);
        assert_eq!(located_native_site_count(&ruleset, &nested), 2);

        // A native-free subject → 0 (the report-free path needs no host value).
        assert_eq!(located_native_site_count(&ruleset, &two), 0);

        // A ruleset with NO native families short-circuits to 0 for any subject.
        let swap_ruleset = compile_in_rho_matching_ruleset(&swap_demo_def());
        assert_eq!(located_native_site_count(&swap_ruleset, &root), 0);
    }

    /// A-S3: the per-rule refinement [`located_native_site_count_for`] agrees with the
    /// aggregate on a single-rule language (its `Σ` decomposition), counts ONLY the named
    /// rule's head, and returns 0 for a head that is not an admitted native entry — the
    /// report-free match body installs exactly this many contract-call bridges per rule.
    #[test]
    fn located_native_site_count_for_counts_one_rule_positionally() {
        let ruleset = compile_in_rho_matching_ruleset(&native_demo_def());
        let two = GroundTerm::new("NumLit", vec![GroundTerm::new("2", Vec::new())]);
        let three = GroundTerm::new("NumLit", vec![GroundTerm::new("3", Vec::new())]);
        let root = GroundTerm::new("PowInt", vec![two.clone(), three.clone()]);
        let nested = GroundTerm::new("PowInt", vec![root.clone(), three.clone()]);

        // Per-rule counts: 1 at the root redex, 2 for the nested pair — and they equal the
        // aggregate for the single-native-rule NativeDemo (the Σ decomposition).
        assert_eq!(located_native_site_count_for(&ruleset, &root, "PowInt"), 1);
        assert_eq!(located_native_site_count_for(&ruleset, &nested, "PowInt"), 2);
        assert_eq!(
            located_native_site_count_for(&ruleset, &nested, "PowInt"),
            located_native_site_count(&ruleset, &nested),
            "for a single-native-rule language the per-rule count IS the aggregate"
        );

        // A head that is NOT an admitted native entry counts 0 — even if it occurs in the
        // subject (the walk is restricted to admitted native heads, never a guess).
        assert_eq!(located_native_site_count_for(&ruleset, &nested, "NumLit"), 0);
        assert_eq!(located_native_site_count_for(&ruleset, &two, "PowInt"), 0);
    }

    #[test]
    fn a_declared_join_comm_rides_the_contextual_path() {
        // The `Comm`-named declared join is a ContextualRewrite: admitted via contextual_dispatch
        // (not deferred), and its hole is matched + reassembled in Rho exactly like WrapCong.
        let ruleset = compile_in_rho_matching_ruleset(&comm_join_demo_def());
        assert_eq!(ruleset.contextual_dispatch.len(), 1, "the declared-join Comm is a contextual family");
        assert_eq!(ruleset.contextual_dispatch[0].fired_rule_label, "Comm");
        assert!(
            !ruleset.deferred.iter().any(|d| d.rule_label == "Comm"),
            "the declared-join Comm is admitted (contextual), not deferred: {:?}",
            ruleset.deferred
        );
        // Send(Swap(A, B)): the hole redex Swap is at Send.0 — the declared-join Comm reassembles
        // Send(Pair(B, A)) via the SAME contextual match call as WrapCong.
        let subject = GroundTerm::new(
            "Send",
            vec![GroundTerm::new(
                "Swap",
                vec![GroundTerm::new("A", Vec::new()), GroundTerm::new("B", Vec::new())],
            )],
        );
        contextual_match_call_par(&ruleset, &subject, "site0", "OUT")
            .expect("the declared-join Comm rides contextual_match_call_par identically to WrapCong");
    }
}
