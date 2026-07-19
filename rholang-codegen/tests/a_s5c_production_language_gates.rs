//! Track A — A-S5c: plan-gate + in-Rho admission pinning for the REAL
//! production `Lambda` (`languages/src/lambda.rs`) and `Ambient`
//! (`languages/src/ambient.rs`) language definitions — NOT the demo languages.
//!
//! Every test asserts what the Rho-default plan gate and the in-Rho admission
//! machinery say TODAY, so the A-S5 Lambda/Ambient flip lands against a pinned,
//! honest baseline. On ANY deviation the affected table is printed in full and
//! the test panics: a deviation means the machinery moved, and the flip design
//! must be re-checked against it — a deviation must be reported, never silently
//! adjusted.
//!
//! # Flip-readiness picture (the pinned TODAY state)
//!
//! **Lambda** — static gate ADMITS, plan gate PASSES, install FAILS CLOSED:
//! - `Beta` compiles to the ONE automaton entry `App(^lambda(fun), arg)` — a
//!   NESTED entry (root `App` over a `^lambda` child), routed to its
//!   `SubstRewrite` σ-receiver source channel.
//! - `AppCongL`/`AppCongR`/`LamCong` defer `NotBaseRewrite`: no contextual join
//!   materializes for them (`AppCongL`/`AppCongR` lower
//!   `Unsupported(DanglingRhsVariable)` — the premise target `M1`/`N1` has no σ
//!   slot and the passenger variable rides the LHS trace only; `LamCong` lowers
//!   `Unsupported(LambdaBinder)`). All three carry `Premise::Congruence`, so the
//!   static gate EXEMPTS them (`in_rho_static_gate` = `Ok(())`): the e-graph
//!   closes contexts implicitly, and a congruence label is never a fired-rule
//!   label.
//! - Per-site admission (the honest boundary the flip must lift): a single-App
//!   subject admits locate-all with exactly 1 site; every subject with ≥ 2
//!   head-`App` candidate sites fails closed
//!   `AutomatonUnsupported::NestedEntryMultiSite` (a nested entry's `loc:`
//!   descent would contend with a co-installed root attempt). The single-root
//!   drive (`in_rho_match_call_par`) admits every chain length.
//! - `plan_rho_default_backend` passes with
//!   `CoveredRejectedRules([Lam, App → RhoAstContract])` +
//!   `NoGuardObligations` (no premise induces a guard obligation —
//!   `backend.rs` `collect_premise_guard_obligations`: the
//!   `Freshness | Congruence | RelationQuery | SyntheticInjGuard` arm adds
//!   nothing). BUT `installed_rho_net_program_par()` FAILS CLOSED on the three
//!   unmaterialized congruence lowerings — plan-accepted ≠ installable.
//!
//! **Ambient** — static gate REJECTS, plan gate PASSES, install FAILS CLOSED:
//! - ALL SIX rewrites defer `NotBaseRewrite`; every dispatch family (linear AC,
//!   contextual, structural-AC, nested-structural-AC, native) is EMPTY and the
//!   automaton has ZERO entries — the in-Rho match call for any Ambient subject
//!   is a bare spread that locates 0 automaton sites and fires nothing.
//! - ROOT CAUSE (pinned by `ambient_collection_kind_is_unresolvable_today`):
//!   the production `PPar` is declared with the `::=` grammar form
//!   (`PPar . Proc ::= HashBag(Proc) sep "|" delim "{" "}"`), so its
//!   `GrammarRule::term_context` is `None`, and
//!   `resolve_constructor_collection_type` (which reads ONLY term-context
//!   `ps:HashBag(Proc)` parameters) cannot resolve the HashBag kind; the parsed
//!   rewrite patterns' `Collection::coll_type` is also `None`. Every
//!   AC-family recognizer (`collection_apply` / `resolve_bag_apply`) therefore
//!   declines, and `InRule`/`OutRule`/`OpenRule`/`ParCong` lower
//!   `Unsupported(CollectionAc)` — this is why the demo twins (`ambdemo` /
//!   `ambnewdemo` / `inoutdemo`, term-context-declared bags) admit while the
//!   REAL Ambient does not. `InRule`/`OutRule` are ALSO independently gated to
//!   binder-free languages (`def.equations.is_empty()`,
//!   `rho_net_lower.rs` nested-receiver gate) — Ambient has 6 equations.
//! - Consequently `is_nested_structural_ac_rewrite` is FALSE for the real
//!   `InRule`/`OutRule` (shape recognition never reaches the representability
//!   check), and both `rho_net_structural_ac_match_entries` (OpenRule) and
//!   `rho_net_nested_structural_ac_match_entries` (In/Out) are EMPTY.
//! - `in_rho_static_gate` = `Err([InRule, OutRule, OpenRule])` — the BLOCKING
//!   FINDING for the flip: three fireable rewrites are deferred and not
//!   congruence-exempt. `ParCong`/`NewCong`/`AmbCong` carry
//!   `Premise::Congruence` and are exempt.
//! - `plan_rho_default_backend` STILL passes (the scalar-coverage flip gate:
//!   all 7 rejected constructors covered by suggested `RhoAstContract`
//!   dispositions; freshness premises in the 6 equations induce NO guard
//!   obligations, so `NoGuardObligations` holds). Install fails closed on all
//!   six unmaterialized rewrites.
//!
//! Placement: this test lives in `rholang-codegen` (not `languages`) because
//! every gate under audit is `pub` here and the REAL definitions are reachable
//! through the SAME production reconstruction path the generated runtime uses:
//! the verbatim `language!` body (what the macro embeds as
//! `LanguageMetadata::definition_source`) is extracted from the production
//! source file via `include_str!` and fed to `reconstruct_language_def`
//! (composition + auto-injection applied — the augmentation the fingerprint is
//! computed over). `languages` depends on `rholang-codegen` via its generated
//! code, so the dependency cannot point the other way; no `[[test]]`
//! registration is needed (the crate auto-discovers integration tests).

use dovetail::set_automaton::PatternId;
use mettail_ast::language::{LanguageDef, Premise};
use mettail_ast::pattern::{Pattern, PatternTerm};
use mettail_rholang_codegen::{
    collect_guard_obligations, compile_in_rho_matching_ruleset, in_rho_match_all_sites_call_par,
    in_rho_match_call_par, in_rho_static_gate, is_nested_structural_ac_rewrite,
    lower_language_def, plan_rho_default_backend, reconstruct_language_def,
    rho_net_nested_structural_ac_match_entries, rho_net_structural_ac_match_entries,
    rho_net_subst_injection_sites, rule_lhs_root_constructors, ruleset_all_entries_flat,
    suggest_rejected_rule_dispositions, AutomatonUnsupported, DeferReason, GroundTerm,
    InRhoMatchingRuleset, RhoCoverageEvidence, RhoDefaultBackendPlan,
    RhoDefaultBackendRequirements, RhoGuardCoverageEvidence, RhoNetInstallError,
    RhoNetLoweredRule, RhoNetLoweringError, RhoRejectedRuleDisposition,
    RhoRejectedRuleDispositionKind, UnsupportedFamily, LAMBDA_REFLECT_LABEL,
};

// ─────────────────────────────────────────────────────────────────────────────
// The REAL production definitions, reconstructed the production way.
// ─────────────────────────────────────────────────────────────────────────────

/// Extract the verbatim `language! { … }` body from a production language
/// source file: everything between the macro invocation's opening `{` and the
/// LAST `}` in the file (the macro's own closing brace). This is the same body
/// text the macro captures as `LanguageMetadata::definition_source`.
fn extract_language_body(source: &str) -> &str {
    let macro_at = source
        .find("language!")
        .expect("the production language file must invoke language!");
    let open = source[macro_at..]
        .find('{')
        .map(|offset| macro_at + offset)
        .expect("the language! invocation must open a brace");
    let close = source.rfind('}').expect("the language! invocation must close its brace");
    &source[open + 1..close]
}

/// The REAL production Lambda definition, reconstructed through the SAME
/// `reconstruct_language_def` path the production installer and the generated
/// `rho_net_program()` accessor use (composition + auto-injection applied).
fn lambda_def() -> LanguageDef {
    let body = extract_language_body(include_str!("../../languages/src/lambda.rs"));
    let def = reconstruct_language_def(body).expect("the production Lambda body must reconstruct");
    mettail_ast::validation::validate_language(&def)
        .expect("the production Lambda definition must validate");
    def
}

/// The REAL production Ambient definition (same reconstruction path).
fn ambient_def() -> LanguageDef {
    let body = extract_language_body(include_str!("../../languages/src/ambient.rs"));
    let def = reconstruct_language_def(body).expect("the production Ambient body must reconstruct");
    mettail_ast::validation::validate_language(&def)
        .expect("the production Ambient definition must validate");
    def
}

fn rewrite_names(def: &LanguageDef) -> Vec<String> {
    def.rewrites.iter().map(|rewrite| rewrite.name.to_string()).collect()
}

fn term_labels(def: &LanguageDef) -> Vec<String> {
    def.terms.iter().map(|term| term.label.to_string()).collect()
}

/// The rewrites carrying a `Premise::Congruence` — the exact set
/// `in_rho_static_gate` exempts (its own enumeration, recomputed here).
fn congruence_premise_rewrites(def: &LanguageDef) -> Vec<String> {
    def.rewrites
        .iter()
        .filter(|rewrite| {
            rewrite
                .premises
                .iter()
                .any(|premise| matches!(premise, Premise::Congruence { .. }))
        })
        .map(|rewrite| rewrite.name.to_string())
        .collect()
}

// ─────────────────────────────────────────────────────────────────────────────
// The per-rewrite admission/deferral verdict table.
// ─────────────────────────────────────────────────────────────────────────────

/// Where one rewrite of the compiled `InRhoMatchingRuleset` landed. TOTAL:
/// `Unclassified` (a rewrite in NO family and NOT deferred) would be a
/// totality-violation FINDING and is asserted to never occur.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Verdict {
    /// A positional automaton entry (base or `^lambda`-remapped subst rewrite).
    AutomatonEntry,
    /// Admitted via the linear HashBag AC match family.
    AcDispatch,
    /// Admitted via the contextual (congruence-join) match family.
    ContextualDispatch,
    /// Admitted via the flat structural non-linear AC match family.
    StructuralAcDispatch,
    /// Admitted via the depth-2 nested structural non-linear AC match family.
    NestedStructuralAcDispatch,
    /// Not matched in Rho, with the typed reason.
    Deferred(DeferReason),
    /// In NO family and NOT deferred — a totality violation (never expected).
    Unclassified,
}

/// Classify every rewrite of `def` against the compiled ruleset, in rewrite
/// order. Base/subst automaton entries carry `PatternId(rewrite index)`;
/// dispatch families are keyed by fired-rule label; everything else must be in
/// `deferred` with a typed reason.
fn admission_table(def: &LanguageDef, ruleset: &InRhoMatchingRuleset) -> Vec<(String, Verdict)> {
    def.rewrites
        .iter()
        .enumerate()
        .map(|(index, rewrite)| {
            let label = rewrite.name.to_string();
            let verdict = if ruleset
                .accept_channels
                .iter()
                .any(|(pid, _)| *pid == PatternId(index))
            {
                Verdict::AutomatonEntry
            } else if ruleset.ac_dispatch.iter().any(|e| e.fired_rule_label == label) {
                Verdict::AcDispatch
            } else if ruleset
                .contextual_dispatch
                .iter()
                .any(|e| e.fired_rule_label == label)
            {
                Verdict::ContextualDispatch
            } else if ruleset
                .structural_ac_dispatch
                .iter()
                .any(|e| e.fired_rule_label == label)
            {
                Verdict::StructuralAcDispatch
            } else if ruleset
                .nested_structural_ac_dispatch
                .iter()
                .any(|e| e.fired_rule_label == label)
            {
                Verdict::NestedStructuralAcDispatch
            } else if let Some(deferred) = ruleset
                .deferred
                .iter()
                .find(|deferred| deferred.rule_label == label)
            {
                Verdict::Deferred(deferred.reason.clone())
            } else {
                Verdict::Unclassified
            };
            (label, verdict)
        })
        .collect()
}

/// Assert one language's full admission table, printing the whole actual table
/// on any deviation (never a silent partial diff).
fn assert_admission_table(language: &str, actual: &[(String, Verdict)], expected: &[(&str, Verdict)]) {
    let expected_owned: Vec<(String, Verdict)> = expected
        .iter()
        .map(|(label, verdict)| ((*label).to_string(), verdict.clone()))
        .collect();
    if actual != expected_owned.as_slice() {
        let mut report = format!("{language} ADMISSION-TABLE DEVIATION — actual table:\n");
        for (label, verdict) in actual {
            report.push_str(&format!("  {label} → {verdict:?}\n"));
        }
        report.push_str("expected table:\n");
        for (label, verdict) in &expected_owned {
            report.push_str(&format!("  {label} → {verdict:?}\n"));
        }
        panic!("{report}");
    }
    // Totality: no rewrite may be unclassified (the item-5 FINDING class).
    for (label, verdict) in actual {
        assert_ne!(
            *verdict,
            Verdict::Unclassified,
            "{language}::{label} is in NO admission family and NOT deferred — totality violation"
        );
    }
}

/// The per-rule lowered-family names of an accepted plan's `RhoNetLowered`
/// (rule-id → family), for pinning the WHY behind each deferral.
fn lowered_family_table(plan: &RhoDefaultBackendPlan) -> Vec<(String, String)> {
    plan.rho_net_lowered()
        .rules()
        .iter()
        .map(|rule| (rule.rule_id().to_string(), lowered_family_name(rule)))
        .collect()
}

fn lowered_family_name(rule: &RhoNetLoweredRule) -> String {
    use RhoNetLoweredRule as R;
    match rule {
        R::NativeFold { .. } => "NativeFold".to_string(),
        R::BaseRewrite { .. } => "BaseRewrite".to_string(),
        R::AcRewrite { .. } => "AcRewrite".to_string(),
        R::CommRewrite { .. } => "CommRewrite".to_string(),
        R::StructuralAcRewrite { .. } => "StructuralAcRewrite".to_string(),
        R::NestedStructuralAcRewrite { .. } => "NestedStructuralAcRewrite".to_string(),
        R::ContextualRewrite { .. } => "ContextualRewrite".to_string(),
        R::SubstRewrite { .. } => "SubstRewrite".to_string(),
        R::NativeSystemProcessRewrite { .. } => "NativeSystemProcessRewrite".to_string(),
        R::StructuralConstructor { .. } => "StructuralConstructor".to_string(),
        R::CongruenceClosure { .. } => "CongruenceClosure".to_string(),
        R::Comm { .. } => "Comm".to_string(),
        R::NativeSystemProcess { .. } => "NativeSystemProcess".to_string(),
        R::Unsupported { family, .. } => format!("Unsupported({family:?})"),
    }
}

fn assert_lowered_family_table(
    language: &str,
    actual: &[(String, String)],
    expected: &[(&str, &str)],
) {
    let expected_owned: Vec<(String, String)> = expected
        .iter()
        .map(|(id, family)| ((*id).to_string(), (*family).to_string()))
        .collect();
    if actual != expected_owned.as_slice() {
        let mut report = format!("{language} LOWERED-FAMILY DEVIATION — actual table:\n");
        for (id, family) in actual {
            report.push_str(&format!("  {id} → {family}\n"));
        }
        report.push_str("expected table:\n");
        for (id, family) in &expected_owned {
            report.push_str(&format!("  {id} → {family}\n"));
        }
        panic!("{report}");
    }
}

/// The production plan invocation under audit: suggested rejected-rule
/// dispositions + `NoGuardObligations` — exactly the doc-28 §7.2 production
/// requirements shape.
fn plan_with_suggested_coverage(def: &LanguageDef) -> RhoDefaultBackendPlan {
    let lowering = lower_language_def(def);
    let requirements = RhoDefaultBackendRequirements {
        coverage: RhoCoverageEvidence::CoveredRejectedRules(suggest_rejected_rule_dispositions(
            def, &lowering,
        )),
        guard_coverage: RhoGuardCoverageEvidence::NoGuardObligations,
    };
    plan_rho_default_backend(def, requirements).unwrap_or_else(|error| {
        panic!(
            "{} must pass the Rho-default plan gate with suggested coverage + \
             NoGuardObligations, got: {error:#?}",
            def.name
        )
    })
}

// ─────────────────────────────────────────────────────────────────────────────
// Shared subjects (reflected-form GroundTerms, as the M-reflect spread sees them).
// ─────────────────────────────────────────────────────────────────────────────

fn nullary(label: &str) -> GroundTerm {
    GroundTerm::new(label, Vec::new())
}

/// A λ-chain App-spine with `n ≥ 1` App nodes over the REFLECTED binder tag:
/// `App(^lambda(F), App(^lambda(F), … App(^lambda(F), A0)))` — the reflected
/// subject shape the real Beta entry `App(^lambda(fun), arg)` matches.
fn lambda_chain(n: usize) -> GroundTerm {
    let mut term = nullary("A0");
    for _ in 0..n {
        term = GroundTerm::new(
            "App",
            vec![GroundTerm::new(LAMBDA_REFLECT_LABEL, vec![nullary("F")]), term],
        );
    }
    term
}

/// The Ambient open-redex bag `{ open(n, 0) | n[0] }` as a reflected subject.
fn ambient_open_redex() -> GroundTerm {
    GroundTerm::new(
        "PPar",
        vec![
            GroundTerm::new("POpen", vec![nullary("n"), nullary("PZero")]),
            GroundTerm::new("PAmb", vec![nullary("n"), nullary("PZero")]),
        ],
    )
}

// ─────────────────────────────────────────────────────────────────────────────
// Inventory pinning: the reconstructed defs ARE the production defs.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn lambda_reconstructs_with_the_production_inventory() {
    let def = lambda_def();
    assert_eq!(def.name.to_string(), "Lambda", "the production language name");
    assert_eq!(term_labels(&def), ["Lam", "App"], "the two production constructors");
    assert_eq!(def.equations.len(), 0, "Lambda declares no equations");
    assert_eq!(
        rewrite_names(&def),
        ["Beta", "AppCongL", "AppCongR", "LamCong"],
        "the four production rewrites, in source order (auto-injection added none)"
    );
}

#[test]
fn ambient_reconstructs_with_the_production_inventory() {
    let def = ambient_def();
    assert_eq!(def.name.to_string(), "Ambient", "the production language name");
    assert_eq!(
        term_labels(&def),
        ["PZero", "PIn", "POut", "POpen", "PAmb", "PNew", "PPar"],
        "the seven production constructors"
    );
    assert_eq!(
        def.equations
            .iter()
            .map(|equation| equation.name.to_string())
            .collect::<Vec<_>>(),
        ["NewComm", "ScopeExtrusion", "InNew", "OutNew", "OpenNew", "AmbNew"],
        "the six structural-congruence equations"
    );
    assert_eq!(
        rewrite_names(&def),
        ["InRule", "OutRule", "OpenRule", "ParCong", "NewCong", "AmbCong"],
        "the six production rewrites, in source order (auto-injection added none)"
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// (2) `compile_in_rho_matching_ruleset`: the full admission/deferral tables.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn lambda_admission_table_is_beta_entry_plus_congruence_deferrals() {
    let def = lambda_def();
    let ruleset = compile_in_rho_matching_ruleset(&def);
    let actual = admission_table(&def, &ruleset);
    eprintln!("Lambda admission table: {actual:?}");
    assert_admission_table(
        "Lambda",
        &actual,
        &[
            ("Beta", Verdict::AutomatonEntry),
            ("AppCongL", Verdict::Deferred(DeferReason::NotBaseRewrite)),
            ("AppCongR", Verdict::Deferred(DeferReason::NotBaseRewrite)),
            ("LamCong", Verdict::Deferred(DeferReason::NotBaseRewrite)),
        ],
    );
}

#[test]
fn ambient_admission_table_defers_every_rewrite_not_base_rewrite() {
    let def = ambient_def();
    let ruleset = compile_in_rho_matching_ruleset(&def);
    let actual = admission_table(&def, &ruleset);
    eprintln!("Ambient admission table: {actual:?}");
    assert_admission_table(
        "Ambient",
        &actual,
        &[
            ("InRule", Verdict::Deferred(DeferReason::NotBaseRewrite)),
            ("OutRule", Verdict::Deferred(DeferReason::NotBaseRewrite)),
            ("OpenRule", Verdict::Deferred(DeferReason::NotBaseRewrite)),
            ("ParCong", Verdict::Deferred(DeferReason::NotBaseRewrite)),
            ("NewCong", Verdict::Deferred(DeferReason::NotBaseRewrite)),
            ("AmbCong", Verdict::Deferred(DeferReason::NotBaseRewrite)),
        ],
    );
}

#[test]
fn lambda_beta_is_the_single_automaton_entry_routed_to_its_subst_site() {
    let def = lambda_def();
    let ruleset = compile_in_rho_matching_ruleset(&def);
    assert_eq!(ruleset.accept_channels.len(), 1, "exactly one automaton entry (Beta)");
    let (pid, accept_channel) = &ruleset.accept_channels[0];
    assert_eq!(*pid, PatternId(0), "Beta is rewrite index 0");
    // Accept-triad coherence: the entry routes to the SAME SubstRewrite
    // σ-receiver source channel the subst injection targets.
    let subst_sites = rho_net_subst_injection_sites(&def);
    assert_eq!(subst_sites.len(), 1, "exactly one subst σ-receiver site (Beta)");
    assert_eq!(subst_sites[0].rule_label, "Beta");
    assert_eq!(
        *accept_channel, subst_sites[0].channel,
        "the Beta accept channel IS the Beta SubstRewrite σ-receiver source"
    );
}

#[test]
fn lambda_dispatch_families_are_all_empty() {
    let ruleset = compile_in_rho_matching_ruleset(&lambda_def());
    assert!(ruleset.native_dispatch.is_empty(), "no native rules in Lambda");
    assert!(ruleset.ac_dispatch.is_empty(), "no linear AC rules in Lambda");
    assert!(
        ruleset.contextual_dispatch.is_empty(),
        "NO contextual join materializes for AppCongL/AppCongR/LamCong today \
         (DanglingRhsVariable / LambdaBinder lowerings)"
    );
    assert!(ruleset.structural_ac_dispatch.is_empty(), "no structural-AC rules in Lambda");
    assert!(ruleset.nested_structural_ac_dispatch.is_empty(), "no nested-AC rules in Lambda");
}

#[test]
fn ambient_has_zero_automaton_entries_and_empty_dispatch_families() {
    let ruleset = compile_in_rho_matching_ruleset(&ambient_def());
    assert!(
        ruleset.accept_channels.is_empty(),
        "no Ambient rewrite compiles to a positional automaton entry today"
    );
    assert!(ruleset.native_dispatch.is_empty(), "no native rules in Ambient");
    assert!(
        ruleset.ac_dispatch.is_empty(),
        "no LINEAR AC admission (all Ambient AC rules are structured, and the \
         HashBag kind is unresolvable — see the collection-kind root-cause test)"
    );
    assert!(ruleset.contextual_dispatch.is_empty(), "no contextual join materializes");
    assert!(
        ruleset.structural_ac_dispatch.is_empty(),
        "OpenRule is NOT admitted on the structural-AC match path today"
    );
    assert!(
        ruleset.nested_structural_ac_dispatch.is_empty(),
        "InRule/OutRule are NOT admitted on the nested structural-AC match path today"
    );
    assert!(
        rule_lhs_root_constructors(&ruleset).is_empty(),
        "zero entries ⇒ zero dispatch root constructors"
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// The static capability gate + its congruence exemption.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn lambda_congruence_premise_rewrites_are_exactly_the_three_congs() {
    assert_eq!(
        congruence_premise_rewrites(&lambda_def()),
        ["AppCongL", "AppCongR", "LamCong"],
        "the static gate's exemption basis for Lambda"
    );
}

#[test]
fn ambient_congruence_premise_rewrites_are_exactly_the_three_congs() {
    assert_eq!(
        congruence_premise_rewrites(&ambient_def()),
        ["ParCong", "NewCong", "AmbCong"],
        "the static gate's exemption basis for Ambient"
    );
}

#[test]
fn lambda_static_gate_admits_because_every_deferral_is_congruence_exempt() {
    let def = lambda_def();
    let ruleset = compile_in_rho_matching_ruleset(&def);
    assert_eq!(
        in_rho_static_gate(&ruleset, &def),
        Ok(()),
        "Lambda's only deferrals are the three congruence-premise rewrites, \
         which the static gate exempts (never fireable)"
    );
}

#[test]
fn ambient_static_gate_rejects_on_exactly_in_out_open() {
    let def = ambient_def();
    let ruleset = compile_in_rho_matching_ruleset(&def);
    let rejects = in_rho_static_gate(&ruleset, &def)
        .expect_err("BLOCKING FINDING: the static gate must reject Ambient today");
    assert_eq!(
        rejects
            .iter()
            .map(|deferred| (deferred.rule_label.as_str(), deferred.reason.clone()))
            .collect::<Vec<_>>(),
        [
            ("InRule", DeferReason::NotBaseRewrite),
            ("OutRule", DeferReason::NotBaseRewrite),
            ("OpenRule", DeferReason::NotBaseRewrite),
        ],
        "the three FIREABLE non-exempt deferrals — the exact set the A-S5 flip \
         must admit; ParCong/NewCong/AmbCong are congruence-exempt and absent"
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// (3) Ambient specifics: structural-AC / nested-shape verdicts + root cause.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn ambient_nested_shape_predicate_is_false_for_the_real_in_and_out_rules() {
    let def = ambient_def();
    for rewrite in &def.rewrites {
        assert!(
            !is_nested_structural_ac_rewrite(&rewrite.left, &rewrite.right, &def),
            "{}: the single-source-of-truth nested-shape predicate must be FALSE \
             for every REAL Ambient rewrite today (the HashBag kind never \
             resolves, so shape recognition fails before the representability \
             check `nested_structural_ac_shape_is_match_representable` is even \
             reached)",
            rewrite.name
        );
    }
}

#[test]
fn ambient_open_rule_is_not_admitted_by_the_structural_ac_family() {
    let entries = rho_net_structural_ac_match_entries(&ambient_def());
    assert_eq!(
        entries
            .iter()
            .map(|entry| entry.fired_rule_label.as_str())
            .collect::<Vec<_>>(),
        Vec::<&str>::new(),
        "the REAL OpenRule does NOT surface a structural-AC match entry today \
         (its demo twins ambdemo/ambnewdemo do — term-context-declared bags)"
    );
}

#[test]
fn ambient_in_out_rules_are_not_admitted_by_the_nested_structural_ac_family() {
    let entries = rho_net_nested_structural_ac_match_entries(&ambient_def());
    assert_eq!(
        entries
            .iter()
            .map(|entry| entry.fired_rule_label.as_str())
            .collect::<Vec<_>>(),
        Vec::<&str>::new(),
        "the REAL InRule/OutRule do NOT surface nested structural-AC match \
         entries today (kind unresolvable; ALSO independently gated on empty \
         equations, and Ambient has six)"
    );
}

/// THE root cause: the production `PPar` declares its HashBag through the `::=`
/// grammar form, so no term-context collection parameter exists for
/// `resolve_constructor_collection_type` to read, and the parsed rewrite
/// patterns carry no inline `coll_type` either — every AC recognizer declines.
#[test]
fn ambient_collection_kind_is_unresolvable_today() {
    let def = ambient_def();
    let ppar = def
        .terms
        .iter()
        .find(|term| term.label == "PPar")
        .expect("PPar is a production constructor");
    assert!(
        ppar.term_context.is_none(),
        "PPar is `::=`-declared: no term-context params, so the collection-kind \
         resolver (term-context-only) cannot see its HashBag"
    );
    for rule_name in ["InRule", "OpenRule", "ParCong"] {
        let rewrite = def
            .rewrites
            .iter()
            .find(|rewrite| rewrite.name == rule_name)
            .expect("production rewrite present");
        let Pattern::Term(PatternTerm::Apply { constructor, args }) = &rewrite.left else {
            panic!("{rule_name}: the LHS is a constructor application");
        };
        assert_eq!(constructor.to_string(), "PPar", "{rule_name} is PPar-rooted");
        let [Pattern::Collection { coll_type, .. }] = args.as_slice() else {
            panic!("{rule_name}: the LHS is PPar over one collection literal");
        };
        assert_eq!(
            *coll_type, None,
            "{rule_name}: the parsed pattern carries NO inline collection kind, \
             so with an unresolvable constructor kind the AC recognizers decline"
        );
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// (4) Lambda specifics: the nested Beta entry's per-site admission facts.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn lambda_beta_entry_is_nested_with_app_root() {
    let ruleset = compile_in_rho_matching_ruleset(&lambda_def());
    assert!(
        !ruleset_all_entries_flat(&ruleset),
        "the Beta entry App(^lambda(fun), arg) is NESTED (a non-Var child)"
    );
    assert_eq!(
        rule_lhs_root_constructors(&ruleset)
            .into_iter()
            .collect::<Vec<_>>(),
        ["App"],
        "App is the one candidate-site head constructor"
    );
}

#[test]
fn lambda_single_app_subject_admits_locate_all_with_one_site() {
    let ruleset = compile_in_rho_matching_ruleset(&lambda_def());
    let (call, sites) = in_rho_match_all_sites_call_par(&ruleset, &lambda_chain(1), "site0", "OUT")
        .expect("a single-App subject admits the locate-all install");
    assert_eq!(sites, 1, "exactly the root redex site");
    assert!(
        call.locally_free.is_empty() && !call.connective_used,
        "the emitted locate-all call is a closed Par"
    );
}

#[test]
fn lambda_multi_app_subjects_fail_closed_nested_entry_multi_site() {
    let ruleset = compile_in_rho_matching_ruleset(&lambda_def());
    for n in 2..=4usize {
        assert_eq!(
            in_rho_match_all_sites_call_par(&ruleset, &lambda_chain(n), "site0", "OUT"),
            Err(AutomatonUnsupported::NestedEntryMultiSite),
            "an App-chain of {n} head-App candidate sites must fail closed — the \
             honest multi-site boundary the A-S5 flip must lift"
        );
    }
}

#[test]
fn lambda_single_root_drive_admits_every_chain_length() {
    let ruleset = compile_in_rho_matching_ruleset(&lambda_def());
    for n in 1..=4usize {
        let call = in_rho_match_call_par(&ruleset, &lambda_chain(n), "site0", "OUT")
            .expect("the single-root drive serializes the nested Beta entry at any n");
        assert!(
            call.locally_free.is_empty() && !call.connective_used,
            "the emitted single-root call is a closed Par (n = {n})"
        );
    }
}

#[test]
fn ambient_locate_all_is_a_no_op_spread_with_zero_automaton_sites() {
    let ruleset = compile_in_rho_matching_ruleset(&ambient_def());
    let (_, sites) =
        in_rho_match_all_sites_call_par(&ruleset, &ambient_open_redex(), "site0", "OUT")
            .expect("zero entries + zero dispatch families never trip the multi-site gate");
    assert_eq!(
        sites, 0,
        "no automaton entry ⇒ the open-redex subject locates ZERO sites: the \
         in-Rho match call is a bare spread that can fire nothing (the Ambient \
         half of the flip gap, in one number)"
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// (1) The Rho-default plan gate + the guard-obligation premise arm.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn lambda_induces_no_guard_obligations() {
    let def = lambda_def();
    // Non-vacuity: congruence premises ARE present…
    assert!(
        def.rewrites
            .iter()
            .flat_map(|rewrite| rewrite.premises.iter())
            .any(|premise| matches!(premise, Premise::Congruence { .. })),
        "Lambda carries congruence premises"
    );
    // …and the `Freshness | Congruence | RelationQuery | SyntheticInjGuard` arm
    // of `collect_premise_guard_obligations` (backend.rs) induces nothing.
    assert_eq!(collect_guard_obligations(&def), Vec::new(), "no guard obligations");
}

#[test]
fn ambient_freshness_premises_induce_no_guard_obligations() {
    let def = ambient_def();
    // Non-vacuity: freshness premises ARE present (ScopeExtrusion/InNew/…)…
    assert!(
        def.equations
            .iter()
            .flat_map(|equation| equation.premises.iter())
            .any(|premise| matches!(premise, Premise::Freshness(_))),
        "Ambient carries freshness premises in its equations"
    );
    // …and they induce NO guard obligations (the same premise arm), which is
    // exactly why `NoGuardObligations` passes below.
    assert_eq!(collect_guard_obligations(&def), Vec::new(), "no guard obligations");
}

#[test]
fn lambda_scalar_lowering_rejects_exactly_the_two_constructors() {
    let lowering = lower_language_def(&lambda_def());
    assert_eq!(lowering.rejected, ["Lam", "App"], "the scalar path rejects both constructors");
}

#[test]
fn ambient_scalar_lowering_rejects_exactly_the_seven_constructors() {
    let lowering = lower_language_def(&ambient_def());
    assert_eq!(
        lowering.rejected,
        ["PZero", "PIn", "POut", "POpen", "PAmb", "PNew", "PPar"],
        "the scalar path rejects all seven constructors"
    );
}

#[test]
fn lambda_suggested_dispositions_cover_both_rejections_as_rho_ast_contracts() {
    let def = lambda_def();
    let lowering = lower_language_def(&def);
    assert_eq!(
        suggest_rejected_rule_dispositions(&def, &lowering),
        vec![
            RhoRejectedRuleDisposition::new("Lam", RhoRejectedRuleDispositionKind::RhoAstContract),
            RhoRejectedRuleDisposition::new("App", RhoRejectedRuleDispositionKind::RhoAstContract),
        ],
        "both rejected constructors get RhoAstContract suggestions"
    );
}

#[test]
fn ambient_suggested_dispositions_cover_all_seven_rejections_as_rho_ast_contracts() {
    let def = ambient_def();
    let lowering = lower_language_def(&def);
    let expected: Vec<RhoRejectedRuleDisposition> =
        ["PZero", "PIn", "POut", "POpen", "PAmb", "PNew", "PPar"]
            .into_iter()
            .map(|label| {
                RhoRejectedRuleDisposition::new(label, RhoRejectedRuleDispositionKind::RhoAstContract)
            })
            .collect();
    assert_eq!(
        suggest_rejected_rule_dispositions(&def, &lowering),
        expected,
        "all seven rejected constructors get RhoAstContract suggestions"
    );
}

#[test]
fn lambda_passes_the_plan_gate_with_suggested_coverage_and_no_guard_obligations() {
    let plan = plan_with_suggested_coverage(&lambda_def());
    assert_eq!(plan.language_name(), "Lambda", "the accepted plan is Lambda's");
}

#[test]
fn ambient_passes_the_plan_gate_with_suggested_coverage_and_no_guard_obligations() {
    let plan = plan_with_suggested_coverage(&ambient_def());
    assert_eq!(plan.language_name(), "Ambient", "the accepted plan is Ambient's");
}

// ─────────────────────────────────────────────────────────────────────────────
// (5) The WHY per rule, and the install boundary (plan-accepted ≠ installable).
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn lambda_lowered_families_pin_the_why_per_rule() {
    let plan = plan_with_suggested_coverage(&lambda_def());
    let actual = lowered_family_table(&plan);
    eprintln!("Lambda lowered families: {actual:?}");
    assert_lowered_family_table(
        "Lambda",
        &actual,
        &[
            ("rule:term:0:Lam", "StructuralConstructor"),
            ("rule:term:1:App", "StructuralConstructor"),
            ("rule:rewrite:0:Beta", "SubstRewrite"),
            ("rule:rewrite:1:AppCongL", "Unsupported(DanglingRhsVariable)"),
            ("rule:rewrite:2:AppCongR", "Unsupported(DanglingRhsVariable)"),
            ("rule:rewrite:3:LamCong", "Unsupported(LambdaBinder)"),
        ],
    );
}

#[test]
fn ambient_lowered_families_pin_the_why_per_rule() {
    let plan = plan_with_suggested_coverage(&ambient_def());
    let actual = lowered_family_table(&plan);
    eprintln!("Ambient lowered families: {actual:?}");
    assert_lowered_family_table(
        "Ambient",
        &actual,
        &[
            ("rule:term:0:PZero", "StructuralConstructor"),
            ("rule:term:1:PIn", "StructuralConstructor"),
            ("rule:term:2:POut", "StructuralConstructor"),
            ("rule:term:3:POpen", "StructuralConstructor"),
            ("rule:term:4:PAmb", "StructuralConstructor"),
            ("rule:term:5:PNew", "StructuralConstructor"),
            ("rule:term:6:PPar", "StructuralConstructor"),
            ("rule:equation:0:NewComm", "CongruenceClosure"),
            ("rule:equation:1:ScopeExtrusion", "CongruenceClosure"),
            ("rule:equation:2:InNew", "CongruenceClosure"),
            ("rule:equation:3:OutNew", "CongruenceClosure"),
            ("rule:equation:4:OpenNew", "CongruenceClosure"),
            ("rule:equation:5:AmbNew", "CongruenceClosure"),
            ("rule:rewrite:0:InRule", "Unsupported(CollectionAc)"),
            ("rule:rewrite:1:OutRule", "Unsupported(CollectionAc)"),
            ("rule:rewrite:2:OpenRule", "Unsupported(CollectionAc)"),
            ("rule:rewrite:3:ParCong", "Unsupported(CollectionAc)"),
            ("rule:rewrite:4:NewCong", "Unsupported(LambdaBinder)"),
            ("rule:rewrite:5:AmbCong", "Unsupported(DanglingRhsVariable)"),
        ],
    );
}

#[test]
fn lambda_install_fails_closed_on_the_three_unmaterialized_congruences() {
    let plan = plan_with_suggested_coverage(&lambda_def());
    assert_eq!(
        plan.installed_rho_net_program_par(),
        Err(RhoNetInstallError::LoweringErrors(vec![
            RhoNetLoweringError::UnsupportedFamily {
                rule_id: "rule:rewrite:1:AppCongL".to_string(),
                family: UnsupportedFamily::DanglingRhsVariable,
            },
            RhoNetLoweringError::UnsupportedFamily {
                rule_id: "rule:rewrite:2:AppCongR".to_string(),
                family: UnsupportedFamily::DanglingRhsVariable,
            },
            RhoNetLoweringError::UnsupportedFamily {
                rule_id: "rule:rewrite:3:LamCong".to_string(),
                family: UnsupportedFamily::LambdaBinder,
            },
        ])),
        "FLIP-BLOCKING: Lambda's plan is accepted and its static gate admits, \
         yet the installed σ-receiver program fails closed — the congruence \
         lowerings must materialize (or be install-exempted) before A-S5"
    );
}

#[test]
fn ambient_install_fails_closed_on_all_six_unmaterialized_rewrites() {
    let plan = plan_with_suggested_coverage(&ambient_def());
    assert_eq!(
        plan.installed_rho_net_program_par(),
        Err(RhoNetInstallError::LoweringErrors(vec![
            RhoNetLoweringError::UnsupportedFamily {
                rule_id: "rule:rewrite:0:InRule".to_string(),
                family: UnsupportedFamily::CollectionAc,
            },
            RhoNetLoweringError::UnsupportedFamily {
                rule_id: "rule:rewrite:1:OutRule".to_string(),
                family: UnsupportedFamily::CollectionAc,
            },
            RhoNetLoweringError::UnsupportedFamily {
                rule_id: "rule:rewrite:2:OpenRule".to_string(),
                family: UnsupportedFamily::CollectionAc,
            },
            RhoNetLoweringError::UnsupportedFamily {
                rule_id: "rule:rewrite:3:ParCong".to_string(),
                family: UnsupportedFamily::CollectionAc,
            },
            RhoNetLoweringError::UnsupportedFamily {
                rule_id: "rule:rewrite:4:NewCong".to_string(),
                family: UnsupportedFamily::LambdaBinder,
            },
            RhoNetLoweringError::UnsupportedFamily {
                rule_id: "rule:rewrite:5:AmbCong".to_string(),
                family: UnsupportedFamily::DanglingRhsVariable,
            },
        ])),
        "FLIP-BLOCKING: Ambient's plan is accepted, yet not one rewrite \
         materializes a receiver — the whole AC family must be admitted (kind \
         resolution + nested gate) before A-S5"
    );
}
