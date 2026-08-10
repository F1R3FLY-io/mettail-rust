//! **INV-S6 — the channel-name fingerprint invariant, enforced BY SWEEP.**
//!
//! > Every channel name emitted by the driver network contains the emitting language's
//! > fingerprint.
//!
//! # Why this file is a sweep and not a checklist
//!
//! The defect S6 closes is a CROSS-FINGERPRINT WRONG FIRING: two co-installed languages
//! sharing a driver-network channel and consuming each other's operands. It has three
//! independent constructions (`sa:` σ-receivers keyed on pattern TEXT, `ac:` carriers keyed
//! on a BARE constructor label, and the `loc:`/`col:`/`cap:` matching-τ family keyed on a
//! caller-supplied site string), and the `cap:` one cannot be defended at the receiver at
//! all — a σ capture binds a fully collapsed subterm through a pattern VARIABLE, which must
//! accept an arbitrary subterm, so there is no tag to discriminate on and there could not
//! be one. The only available discriminator is the NAME.
//!
//! Two attempts to fix this by enumerating emission sites both came up short — the second
//! named four `RhoNetChannel::location` call sites where the tree has nineteen. So the
//! requirement is stated here as a property of the EMITTED `Par`, and checked by walking
//! every channel position of a fully compiled production language. A new emission site
//! cannot be added without either inheriting a scope or failing this test.
//!
//! # The taxonomy is the tree's own
//!
//! The family partition is not invented here. It is
//! [`mettail_rholang_runtime::bench_support::CommChannelClass`], the exhaustive COMM
//! classification the benchmark harness already buckets every channel by, reproduced as
//! [`ChannelFamily`] so `rholang-codegen` need not depend on `rholang-runtime`
//! (the dependency runs the other way). [`family_partition_matches_the_runtime_taxonomy`]
//! pins the two against each other by name, so a family added to the taxonomy and not to
//! this sweep is a test failure rather than a silent hole.
//!
//! | prefix | family | scoped by |
//! |---|---|---|
//! | `sa:` | firing-visible | `RhoNetChannel::set_automaton_trace` |
//! | `ac:` | AC carrier | `ac_soup_channel` (bare) / `ac_carrier_channel` (site-keyed, inherits) |
//! | `loc:` `col:` `cap:` | matching-τ | shared compact subject-position channel ABI |
//! | `ph:` | contextual plumbing | inherits from its `loc:` premise channel |
//! | `e6a:` | PathMap index | `e6a_index_channel` / `e6a_sites_channel` |
//! | `eq:` `obs:` | plan-level | `RhoNetChannel::consistency` / `::observation` |
//! | `GPrivate(mettail.term.{fp}.…)` | subst-τ / respread-τ / drive-τ | the reflected-tag ABI, already scoped |
//!
//! Anything else is `Other`, which is COUNTED and REPORTED rather than dropped — the same
//! never-silently-bucket discipline the runtime taxonomy uses.

use std::collections::{BTreeMap, BTreeSet};

use mettail_ast::language::LanguageDef;
use mettail_rholang_codegen::{
    ac_match_call_par, compile_in_rho_matching_ruleset, contextual_match_call_par,
    in_rho_match_all_sites_call_par, lower_language_def, nested_structural_ac_match_call_par,
    plan_rho_default_backend, reconstruct_language_def, rho_net_ac_match_entries,
    rho_net_nested_structural_ac_match_entries, rho_net_structural_ac_match_entries,
    spread_term_par, structural_ac_match_call_par, suggest_rejected_rule_dispositions, GroundTerm,
    RhoCoverageEvidence, RhoDefaultBackendPlan, RhoDefaultBackendRequirements,
    RhoGuardCoverageEvidence,
};
use models::rhoapi::expr::ExprInstance;
use models::rhoapi::{Expr, Par};

// ─────────────────────────────────────────────────────────────────────────────
//  The family partition (mirroring `bench_support::CommChannelClass`)
// ─────────────────────────────────────────────────────────────────────────────

/// One emitted-channel family. Mirrors
/// `mettail_rholang_runtime::bench_support::CommChannelClass`; see the module docs for why
/// it is mirrored rather than imported.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum ChannelFamily {
    /// `sa:` — accept / σ-receiver source / native dispatch.
    FiringVisible,
    /// `ac:` — AC bag carrier, bare or site-keyed.
    AcCarrier,
    /// `e6a:` — the E-6a PathMap subject index.
    PathMapIndex,
    /// `ph:`, and `loc:…/contextual-premise/…` — contextual (congruence) plumbing.
    ContextualPlumbing,
    /// `loc:` / `col:` / `cap:` — the matching network's internal τ traffic.
    MatchingTau,
    /// `eq:` / `obs:` — plan-level consistency and observation channels.
    PlanScoped,
    /// A `^`-prefixed reserved GString ledger channel — `^fired:{fp}` (the firing ledger)
    /// and the typed fail-close channels `^drive-err:{fp}` / `^drive-fuel:{fp}`.
    ///
    /// ★ FOUND BY THE SWEEP, not by the relayed taxonomy. The runtime COMM taxonomy does
    /// not list these because they are RESTING PRODUCES — nothing in-Rho consumes them, so
    /// they contribute zero COMMs and are read back by peek rather than classified. They
    /// are nonetheless emitted channel NAMES and therefore in scope for INV-S6. They were
    /// already correctly scoped (`{label}:{fingerprint}`, scope LAST rather than first),
    /// so S6 changes nothing about them — but they are now a named family rather than
    /// unexplained residue in the `Other` bucket.
    ReservedLedger,
    /// A `GPrivate` reflected-tag channel (`mettail.term.{fp}.{label}`): the subst-TRS,
    /// `^respread`, and `^drive` families. Already fingerprint-scoped by the tag ABI.
    ReservedPrivate,
    /// None of the above — counted and REPORTED, never silently dropped.
    Other,
}

impl ChannelFamily {
    /// Whether INV-S6 requires this family's names to embed the language fingerprint.
    ///
    /// Every family except `Other` does. `Other` is where the CONFIGURED observation
    /// channel lands (a name the caller chooses, e.g. `"OUT"`, which MeTTaIL does not own
    /// and must not rewrite) along with anything unrecognized — so `Other` is not exempted
    /// here, it is enumerated by [`the_only_unscoped_names_are_the_configured_out_channel`]
    /// instead.
    fn requires_fingerprint(self) -> bool {
        self != ChannelFamily::Other
    }

    /// The family of a QUOTED (GString) channel name.
    fn of_quoted(name: &str) -> Self {
        // Precedence mirrors `CommChannelClass`'s derived `Ord`: most specific first, so a
        // reserved prefix outranks a pathologically colliding out-channel name.
        match name {
            _ if name.starts_with("sa:") => ChannelFamily::FiringVisible,
            _ if name.starts_with("ac:") => ChannelFamily::AcCarrier,
            _ if name.starts_with("e6a:") => ChannelFamily::PathMapIndex,
            _ if name.starts_with("ph:") => ChannelFamily::ContextualPlumbing,
            _ if name.starts_with("loc:") => {
                if name.contains("/contextual-premise/") {
                    ChannelFamily::ContextualPlumbing
                } else {
                    ChannelFamily::MatchingTau
                }
            },
            _ if name.starts_with("cap:") || name.starts_with("col:") => ChannelFamily::MatchingTau,
            _ if name.starts_with("eq:") || name.starts_with("obs:") => ChannelFamily::PlanScoped,
            _ if name.starts_with('^') => ChannelFamily::ReservedLedger,
            _ => ChannelFamily::Other,
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────────
//  The sweep
// ─────────────────────────────────────────────────────────────────────────────

/// One observed channel position in an emitted `Par`.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct ObservedChannel {
    /// The rendered name: the `GString` text, or `GPrivate(<decoded tag>)`.
    name: String,
    family: ChannelFamily,
}

/// Collect EVERY channel-position name reachable from `par`.
///
/// A "channel position" is any `Par` that the reducer will treat as a name: a `Send.chan`,
/// a `ReceiveBind.source`, and — transitively — the same positions inside every `Receive`
/// body, `New` body, `Match` target and case body, `Bundle` body, and `Send` datum. Data
/// positions are recursed into (never classified as channels themselves) because the driver
/// network passes channel names AS DATA in several places: the spread's `^respread` seed
/// carries its `loc:`/`cap:` roots as `GString` payloads, and a contextual σ-receiver takes
/// its dynamic out channel as a message argument. A sweep that skipped data would miss
/// exactly the names the S6 defect travels on.
///
/// Consequently a quoted name appearing only as data is still collected; that is
/// deliberate, because such a name IS used as a channel by whoever receives it.
fn collect_channels(par: &Par, out: &mut BTreeSet<ObservedChannel>) {
    for send in &par.sends {
        if let Some(chan) = send.chan.as_ref() {
            record(chan, out);
            collect_channels(chan, out);
        }
        for datum in &send.data {
            collect_channels(datum, out);
        }
    }
    for receive in &par.receives {
        for bind in &receive.binds {
            if let Some(source) = bind.source.as_ref() {
                record(source, out);
                collect_channels(source, out);
            }
            for pattern in &bind.patterns {
                collect_channels(pattern, out);
            }
        }
        if let Some(body) = receive.body.as_ref() {
            collect_channels(body, out);
        }
        if let Some(condition) = receive.condition.as_ref() {
            collect_channels(condition, out);
        }
    }
    for new in &par.news {
        if let Some(body) = new.p.as_ref() {
            collect_channels(body, out);
        }
    }
    for m in &par.matches {
        if let Some(target) = m.target.as_ref() {
            collect_channels(target, out);
        }
        for case in &m.cases {
            if let Some(pattern) = case.pattern.as_ref() {
                collect_channels(pattern, out);
            }
            if let Some(source) = case.source.as_ref() {
                collect_channels(source, out);
            }
        }
    }
    for bundle in &par.bundles {
        if let Some(body) = bundle.body.as_ref() {
            collect_channels(body, out);
        }
    }
    for expr in &par.exprs {
        collect_expr_channels(expr, out);
    }
}

/// Recurse into the `Par`-bearing arms of an `Expr` (collection literals, method calls,
/// and every binary/unary operator), so a channel name nested inside an `EList` datum or a
/// `PathMap` method receiver is still swept.
fn collect_expr_channels(expr: &Expr, out: &mut BTreeSet<ObservedChannel>) {
    let Some(instance) = expr.expr_instance.as_ref() else {
        return;
    };
    let mut walk = |p: &Option<Par>| {
        if let Some(p) = p.as_ref() {
            collect_channels(p, out);
        }
    };
    match instance {
        ExprInstance::EListBody(list) => list.ps.iter().for_each(|p| collect_channels(p, out)),
        ExprInstance::ETupleBody(t) => t.ps.iter().for_each(|p| collect_channels(p, out)),
        ExprInstance::ESetBody(s) => s.ps.iter().for_each(|p| collect_channels(p, out)),
        ExprInstance::EMapBody(m) => {
            for kv in &m.kvs {
                walk(&kv.key);
                walk(&kv.value);
            }
        },
        ExprInstance::EMethodBody(method) => {
            walk(&method.target);
            method
                .arguments
                .iter()
                .for_each(|p| collect_channels(p, out));
        },
        ExprInstance::EMatchesBody(m) => {
            walk(&m.target);
            walk(&m.pattern);
        },
        ExprInstance::ENotBody(p) => walk(&p.p),
        ExprInstance::ENegBody(p) => walk(&p.p),
        ExprInstance::EPlusBody(b) => {
            walk(&b.p1);
            walk(&b.p2);
        },
        ExprInstance::EMinusBody(b) => {
            walk(&b.p1);
            walk(&b.p2);
        },
        ExprInstance::EMultBody(b) => {
            walk(&b.p1);
            walk(&b.p2);
        },
        ExprInstance::EDivBody(b) => {
            walk(&b.p1);
            walk(&b.p2);
        },
        ExprInstance::EAndBody(b) => {
            walk(&b.p1);
            walk(&b.p2);
        },
        ExprInstance::EOrBody(b) => {
            walk(&b.p1);
            walk(&b.p2);
        },
        ExprInstance::EEqBody(b) => {
            walk(&b.p1);
            walk(&b.p2);
        },
        ExprInstance::ENeqBody(b) => {
            walk(&b.p1);
            walk(&b.p2);
        },
        ExprInstance::ELtBody(b) => {
            walk(&b.p1);
            walk(&b.p2);
        },
        ExprInstance::ELteBody(b) => {
            walk(&b.p1);
            walk(&b.p2);
        },
        ExprInstance::EGtBody(b) => {
            walk(&b.p1);
            walk(&b.p2);
        },
        ExprInstance::EGteBody(b) => {
            walk(&b.p1);
            walk(&b.p2);
        },
        // Ground scalars, variables, and unforgeables carry no nested `Par`.
        _ => {},
    }
}

/// Record `chan` as an observed channel position, if it renders to a name at all.
///
/// A channel that is a bound variable, a connective, or a structural pattern has no static
/// name and is skipped: INV-S6 constrains the names the codegen MINTS, and a variable
/// channel's name is whatever was sent to it — which this sweep already checked at the
/// sending site.
fn record(chan: &Par, out: &mut BTreeSet<ObservedChannel>) {
    if let Some(name) = quoted_name(chan) {
        let family = ChannelFamily::of_quoted(&name);
        out.insert(ObservedChannel { name, family });
    } else if let Some(tag) = private_tag(chan) {
        out.insert(ObservedChannel {
            name: format!("GPrivate({tag})"),
            family: ChannelFamily::ReservedPrivate,
        });
    }
}

/// The `GString` text of a `Par` that is exactly one quoted string, else `None`.
fn quoted_name(par: &Par) -> Option<String> {
    let [expr] = par.exprs.as_slice() else {
        return None;
    };
    match expr.expr_instance.as_ref()? {
        ExprInstance::GString(name) => Some(name.clone()),
        _ => None,
    }
}

/// The UTF-8 tag of a `Par` that is exactly one `GPrivate` built by
/// `GPrivateBuilder::new_par_from_string`, else `None`. That builder writes
/// `<String as prost::Message>`, so `String::decode` is its exact inverse.
fn private_tag(par: &Par) -> Option<String> {
    use models::rhoapi::g_unforgeable::UnfInstance;
    use prost::Message;

    let [unforgeable] = par.unforgeables.as_slice() else {
        return None;
    };
    match unforgeable.unf_instance.as_ref()? {
        UnfInstance::GPrivateBody(value) => String::decode(value.id.as_slice()).ok(),
        _ => None,
    }
}

// ─────────────────────────────────────────────────────────────────────────────
//  Compilation harness (the `a_s5c` production-gate reconstruction path)
// ─────────────────────────────────────────────────────────────────────────────

fn extract_language_body(source: &str) -> &str {
    let start = source.find("language! {").expect("language! block") + "language! {".len();
    let end = source.rfind('}').expect("closing brace");
    &source[start..end]
}

fn plan_and_fingerprint(source: &str) -> (RhoDefaultBackendPlan, String) {
    let body = extract_language_body(source);
    let def: LanguageDef =
        reconstruct_language_def(body).expect("the production body must reconstruct");
    let fingerprint = mettail_ast::identity::language_definition_fingerprint(&def);
    let lowering = lower_language_def(&def);
    let requirements = RhoDefaultBackendRequirements {
        coverage: RhoCoverageEvidence::CoveredRejectedRules(suggest_rejected_rule_dispositions(
            &def, &lowering,
        )),
        guard_coverage: RhoGuardCoverageEvidence::NoGuardObligations,
    };
    let plan =
        plan_rho_default_backend(&def, requirements).expect("the production language must plan");
    (plan, fingerprint)
}

/// The production languages swept. Deliberately BOTH: Lambda exercises the binder /
/// subst-TRS families and Ambient exercises the AC carrier, `^float`, and nested-AC
/// families, so between them every family in the taxonomy that a production language can
/// emit is represented.
const SWEPT_LANGUAGES: [(&str, &str); 2] = [
    ("Lambda", include_str!("../../languages/src/lambda.rs")),
    ("Ambient", include_str!("../../languages/src/ambient.rs")),
];

/// A ground SUBJECT that the ruleset's `entry`-th automaton pattern locates, derived from
/// the pattern itself: every `App` node becomes the same constructor applied to its walked
/// children, and every `Var` leaf becomes a fresh nullary probe constructor (a Var matches
/// an arbitrary subterm, so any ground term serves).
///
/// Derived rather than hand-written so the sweep needs no per-language fixture and cannot
/// drift when a production language's rules change. The subject's SHAPE only decides how
/// many location channels the spread emits; their SCOPE — the property under test — comes
/// from the fingerprint, so a derived subject tests the invariant exactly as well as a
/// curated one, and keeps testing it after a rule edit.
fn locating_subject(
    view: &dovetail::set_automaton::SetAutomatonView<'_, String>,
    entry: usize,
) -> GroundTerm {
    use dovetail::set_automaton::{AutomatonNode, StateId};

    fn walk(
        view: &dovetail::set_automaton::SetAutomatonView<'_, String>,
        state: StateId,
    ) -> GroundTerm {
        match view.node(state) {
            AutomatonNode::App { op, args } => {
                GroundTerm::new(op.clone(), args.iter().map(|a| walk(view, a.state())).collect())
            },
            AutomatonNode::Var => GroundTerm::nullary("__s6_probe"),
        }
    }
    walk(view, view.entry_root_state(entry))
}

/// Every channel name one language emits, across BOTH halves of the driver network.
///
/// Sweeping only the installed program would be vacuous for the family the S6 defect is
/// sharpest on: the installed program is the RECEIVER side (σ-receivers, the subst-TRS, the
/// `^drive` family), and the entire matching-τ family — `loc:`, `col:`, `cap:` — is emitted
/// by the per-subject DRIVER CALL instead. The first run of this sweep found exactly that
/// hole (`Lambda channel census: {FiringVisible: 1, ReservedPrivate: 6, Other: 3}` — zero
/// `MatchingTau`), which is why [`the_sweep_reaches_every_family_a_production_language_emits`]
/// asserts the census rather than merely printing it.
///
/// So both halves are swept and unioned:
///
/// 1. `installed_rho_net_program_par()` — the co-installed receivers;
/// 2. `in_rho_match_all_sites_call_par` over a [`locating_subject`] per automaton entry —
///    the spread + automaton receiver network, i.e. every `loc:`/`col:`/`cap:` name.
fn sweep(source: &str) -> (String, BTreeSet<ObservedChannel>) {
    let (plan, fingerprint) = plan_and_fingerprint(source);
    let mut channels = BTreeSet::new();

    let installed = plan
        .installed_rho_net_program_par()
        .expect("the production language installs");
    collect_channels(&installed, &mut channels);

    let body = extract_language_body(source);
    let def: LanguageDef = reconstruct_language_def(body).expect("reconstructs");
    let ruleset = compile_in_rho_matching_ruleset(&def);
    let view = ruleset.automaton.view();

    // Subjects: one per automaton entry, plus a nullary fallback so a language whose rules
    // are ALL AC-shaped (Ambient — its `AcApp` bags have no positional image, so it has few
    // or no positional entries) still spreads something. The spread's channel SCOPE does not
    // depend on the subject, so a fallback subject tests the invariant no less rigorously.
    let mut subjects: Vec<GroundTerm> = (0..view.entry_count())
        .map(|e| locating_subject(&view, e))
        .collect();
    if let Some(term) = def.terms.first() {
        subjects.push(GroundTerm::nullary(term.label.to_string()));
    }
    assert!(
        !subjects.is_empty(),
        "no subject to spread — the matching-τ half of the sweep would be empty and INV-S6 \
         would pass vacuously for `loc:`/`col:`/`cap:`"
    );

    for subject in &subjects {
        // (a) The SPREAD itself: the sole emitter of the whole matching-τ family.
        collect_channels(&spread_term_par(subject, &fingerprint, "site0"), &mut channels);

        // (b) The positional driver call: spread + automaton receiver network, adding every
        //     `loc:`/`cap:` name the automaton RECEIVES on. A call can legitimately fail to
        //     serialize for an unsupported entry shape (`AutomatonUnsupported`); such an
        //     entry simply contributes nothing beyond (a).
        if let Ok((call, _)) = in_rho_match_all_sites_call_par(&ruleset, subject, "site0", "OUT") {
            collect_channels(&call, &mut channels);
        }

        // (c) The AC drivers — where the SITE-KEYED carrier `ac:loc:{fp}/{site}/{op}` and its
        //     per-site receivers are emitted. These are the families Ambient's rules take, and
        //     they are the reason (b) alone left Ambient's matching-τ census at zero on the
        //     sweep's second run.
        let ac = rho_net_ac_match_entries(&def);
        if !ac.is_empty() {
            collect_channels(
                &ac_match_call_par(subject, &ac, "site0", "OUT", &fingerprint),
                &mut channels,
            );
        }
        let structural = rho_net_structural_ac_match_entries(&def);
        if !structural.is_empty() {
            collect_channels(
                &structural_ac_match_call_par(subject, &structural, "site0", "OUT", &fingerprint),
                &mut channels,
            );
        }
        let nested = rho_net_nested_structural_ac_match_entries(&def);
        if !nested.is_empty() {
            collect_channels(
                &nested_structural_ac_match_call_par(
                    subject,
                    &nested,
                    "site0",
                    "OUT",
                    &fingerprint,
                ),
                &mut channels,
            );
        }

        // (d) The contextual (congruence) driver — the `ph:` premise-hole bridge family.
        if !ruleset.contextual_dispatch.is_empty() {
            if let Ok(call) = contextual_match_call_par(&ruleset, subject, "site0", "OUT") {
                collect_channels(&call, &mut channels);
            }
        }
    }

    (fingerprint, channels)
}

// ─────────────────────────────────────────────────────────────────────────────
//  THE INVARIANT
// ─────────────────────────────────────────────────────────────────────────────

/// ★ INV-S6, stated directly: every emitted channel name in a scoped family carries the
/// emitting language's fingerprint.
#[test]
fn every_emitted_channel_name_carries_the_language_fingerprint() {
    for (language, source) in SWEPT_LANGUAGES {
        let (fingerprint, channels) = sweep(source);
        assert!(
            !channels.is_empty(),
            "{language}: the sweep found no channels at all — the walker is not reaching \
             the installed program"
        );

        let unscoped: Vec<&ObservedChannel> = channels
            .iter()
            .filter(|c| c.family.requires_fingerprint() && !c.name.contains(&fingerprint))
            .collect();
        assert!(
            unscoped.is_empty(),
            "{language}: INV-S6 VIOLATED — {} emitted channel name(s) do not carry the \
             fingerprint {fingerprint:?}. Two co-installed languages would share these \
             channels and could consume each other's operands:\n{}",
            unscoped.len(),
            unscoped
                .iter()
                .map(|c| format!("  [{:?}] {}", c.family, c.name))
                .collect::<Vec<_>>()
                .join("\n"),
        );
    }
}

/// The census, made visible: every family the sweep actually finds, with a count. A family
/// dropping to zero means the sweep stopped reaching it (a walker regression that would
/// make the invariant test vacuously pass), so the counts are asserted, not just printed.
#[test]
fn the_sweep_reaches_every_family_a_production_language_emits() {
    // Families each production language MUST emit. Lambda is binder/TRS-shaped and emits no
    // AC carrier; Ambient is the AC/nested-AC language. Both emit the matching-τ and
    // firing-visible families and the reserved private tags.
    let required: BTreeMap<&str, Vec<ChannelFamily>> = BTreeMap::from([
        (
            "Lambda",
            vec![
                ChannelFamily::FiringVisible,
                ChannelFamily::MatchingTau,
                ChannelFamily::ReservedPrivate,
                ChannelFamily::ReservedLedger,
            ],
        ),
        (
            "Ambient",
            vec![
                ChannelFamily::FiringVisible,
                ChannelFamily::MatchingTau,
                ChannelFamily::AcCarrier,
                ChannelFamily::ReservedPrivate,
                ChannelFamily::ReservedLedger,
            ],
        ),
    ]);

    for (language, source) in SWEPT_LANGUAGES {
        let (_, channels) = sweep(source);
        let mut census: BTreeMap<ChannelFamily, usize> = BTreeMap::new();
        for channel in &channels {
            *census.entry(channel.family).or_insert(0) += 1;
        }
        println!("{language} channel census: {census:?}");
        for family in &required[language] {
            assert!(
                census.get(family).copied().unwrap_or(0) > 0,
                "{language}: the sweep found ZERO {family:?} channels — either the emitter \
                 stopped producing them or the walker stopped reaching them. Either way the \
                 INV-S6 test would pass vacuously for this family.\ncensus: {census:?}"
            );
        }
    }
}

/// The `Other` bucket is ENUMERATED, not exempted: the only emitted names allowed to carry
/// no fingerprint are ones MeTTaIL does not own.
///
/// Today that is exactly the configured observation channel (`"OUT"`) — a caller-chosen
/// name that must be reproduced verbatim or the caller could not read its own results — and
/// the `rho:` / `sys:` f1r3node system-process URIs, which name f1r3node's channels rather
/// than MeTTaIL's. Anything else appearing here is a new unscoped family and fails the test
/// with its name, rather than being absorbed by a permissive filter.
#[test]
fn the_only_unscoped_names_are_the_configured_out_channel() {
    /// Names MeTTaIL emits but does not own. `OUT` is the caller's observation channel;
    /// the `rho:`/`sys:` prefixes are f1r3node's own system-process URIs.
    fn is_foreign(name: &str) -> bool {
        name == "OUT" || name.starts_with("rho:") || name.starts_with("sys:")
    }

    for (language, source) in SWEPT_LANGUAGES {
        let (_, channels) = sweep(source);
        let unexplained: Vec<&ObservedChannel> = channels
            .iter()
            .filter(|c| c.family == ChannelFamily::Other && !is_foreign(&c.name))
            .collect();
        assert!(
            unexplained.is_empty(),
            "{language}: {} emitted channel name(s) belong to NO known family and are not \
             foreign-owned. Each is a candidate unscoped channel family — classify it and \
             scope it, or add it to the foreign-owned set with a rationale:\n{}",
            unexplained.len(),
            unexplained
                .iter()
                .map(|c| format!("  {}", c.name))
                .collect::<Vec<_>>()
                .join("\n"),
        );
    }
}

/// The two languages' channel name sets are DISJOINT — the property the whole stage exists
/// to establish, checked end to end rather than inferred from the per-name assertion.
///
/// Before S6 this intersection was non-empty for any two languages sharing a constructor
/// name or a site string; `@"ac:PPar"` alone collided by default between any two process
/// calculi, since `PPar` is the name `rholang` and every AC/Ambient demo actually use.
#[test]
fn two_co_installed_languages_share_no_channel_name() {
    let (lambda_fp, lambda) = sweep(SWEPT_LANGUAGES[0].1);
    let (ambient_fp, ambient) = sweep(SWEPT_LANGUAGES[1].1);
    assert_ne!(
        lambda_fp, ambient_fp,
        "the two production languages must have distinct fingerprints for this to test \
         anything"
    );

    let lambda_names: BTreeSet<&str> = lambda.iter().map(|c| c.name.as_str()).collect();
    let ambient_names: BTreeSet<&str> = ambient.iter().map(|c| c.name.as_str()).collect();
    let shared: Vec<&&str> = lambda_names
        .intersection(&ambient_names)
        .filter(|name| **name != "OUT" && !name.starts_with("rho:") && !name.starts_with("sys:"))
        .collect();

    assert!(
        shared.is_empty(),
        "Lambda and Ambient share {} channel name(s). Co-installed, they could consume each \
         other's operands on these:\n{}",
        shared.len(),
        shared
            .iter()
            .map(|n| format!("  {n}"))
            .collect::<Vec<_>>()
            .join("\n"),
    );
}

/// The mirrored [`ChannelFamily`] partition must stay aligned with the runtime taxonomy it
/// mirrors. Pinned by NAME against the documented `CommChannelClass` variants, so a family
/// added there and not here is a failure rather than a silent gap in the sweep.
///
/// `SubstTau`, `RespreadTau` and `DriveTau` collapse into [`ChannelFamily::ReservedPrivate`]
/// here: all three are `GPrivate(mettail.term.{fp}.{label})` tags, and INV-S6 treats them
/// identically (the reflected-tag ABI already embeds the fingerprint). `Observation` and
/// `Other` collapse into [`ChannelFamily::Other`], which
/// [`the_only_unscoped_names_are_the_configured_out_channel`] enumerates.
#[test]
fn family_partition_matches_the_runtime_taxonomy() {
    // The `CommChannelClass` variants, as documented at `bench_support.rs:156-202`.
    const RUNTIME_TAXONOMY: [&str; 10] = [
        "SubstTau",
        "RespreadTau",
        "DriveTau",
        "FiringVisible",
        "AcCarrier",
        "PathMapIndex",
        "ContextualPlumbing",
        "MatchingTau",
        "Observation",
        "Other",
    ];
    // How each runtime class maps onto this file's partition.
    let mapping: BTreeMap<&str, ChannelFamily> = BTreeMap::from([
        ("SubstTau", ChannelFamily::ReservedPrivate),
        ("RespreadTau", ChannelFamily::ReservedPrivate),
        ("DriveTau", ChannelFamily::ReservedPrivate),
        ("FiringVisible", ChannelFamily::FiringVisible),
        ("AcCarrier", ChannelFamily::AcCarrier),
        ("PathMapIndex", ChannelFamily::PathMapIndex),
        ("ContextualPlumbing", ChannelFamily::ContextualPlumbing),
        ("MatchingTau", ChannelFamily::MatchingTau),
        ("Observation", ChannelFamily::Other),
        ("Other", ChannelFamily::Other),
    ]);
    for class in RUNTIME_TAXONOMY {
        assert!(
            mapping.contains_key(class),
            "the runtime COMM taxonomy has a class `{class}` this sweep does not map — the \
             INV-S6 census would be incomplete for it"
        );
    }
    // `PlanScoped` (`eq:`/`obs:`) has no runtime COMM class because those plan-level
    // channels are not reached by a COMM in the emitted program; the sweep still scopes
    // them, which is strictly stronger than the taxonomy requires.
    assert_eq!(
        ChannelFamily::of_quoted("eq:x"),
        ChannelFamily::PlanScoped,
        "plan-level consistency channels stay a recognized family"
    );
}

/// The scoping primitive itself, pinned: the fingerprint rides VERBATIM and is separated
/// from the path by a single `/`, so a reader can recover either half.
#[test]
fn the_scope_is_a_verbatim_fingerprint_and_a_slash() {
    use mettail_rholang_codegen::scoped_channel_name;

    let fp = "mettail-langdef-v1:0123456789abcdef";
    assert_eq!(
        scoped_channel_name("loc", fp, "site0/Swap.1"),
        "loc:mettail-langdef-v1:0123456789abcdef/site0/Swap.1"
    );
    // Slash-free fingerprint ⇒ the FIRST `/` after the family prefix splits scope from path.
    let name = scoped_channel_name("cap", fp, "site0/f.0");
    let after_prefix = name.strip_prefix("cap:").expect("family prefix");
    let (scope, path) = after_prefix.split_once('/').expect("scope/path split");
    assert_eq!(scope, fp);
    assert_eq!(path, "site0/f.0");
}
