//! ★ The DISPOSITION of a declared construct under generated runtime lowering.
//!
//! # The defect this module exists to remove
//!
//! Lowering used to answer with a pair: a `Vec<TokenStream>` of rules that were emitted,
//! and a `Vec<String>` of excuses for the ones that were not. The excuse vector was
//! dropped at four of its five consumption sites — `let (rules, _unsupported) = …` — so
//! nothing downstream could tell these three outcomes apart:
//!
//! ```text
//!   ┌──────────────────────────┬───────────────────────────────────────────────┐
//!   │ lowered HERE             │  a rule appears in the emitted vector          │
//!   │ lowered by ANOTHER lane  │  no rule, no excuse — deliberate and correct   │
//!   │ lowered NOWHERE          │  no rule, an excuse nobody reads               │
//!   └──────────────────────────┴───────────────────────────────────────────────┘
//!                                        ↑ these two are BYTE-IDENTICAL to every reader
//! ```
//!
//! The second and third rows are indistinguishable, and the second row is the *common*
//! one: 400 of a language's 461 declared rewrites take it (a congruence rewrite needs no
//! lowered rule, because e-graph congruence closure propagates the merge for it). So
//! "silence means a defect" is false 400 times over, and "silence means fine" hides every
//! real drop. A boolean cannot express the difference. A **disposition** can:
//!
//! | outcome | meaning |
//! |---|---|
//! | [`LoweringOutcome::Delivered`] | lowered by the reporting lane; carries the emitted rule label |
//! | [`LoweringOutcome::DeliveredElsewhere`] | lowered by another lane, **named** |
//! | [`LoweringOutcome::Suppressed`] | deliberately not lowered, for a **recorded** reason |
//! | [`LoweringOutcome::Declined`] | lowered NOWHERE — the reason lowering refused it |
//!
//! # Where the vocabulary comes from
//!
//! It is not invented here. `mettail_rholang_codegen::backend::RhoRejectedRuleDispositionKind`
//! already named *which lane covers a rule this lane did not lower*, for the Rho side.
//! [`mettail_runtime::LoweringLane`] adopts those four names verbatim and adds the
//! Dovetail-side lanes that had no name at all, and
//! `RhoRejectedRuleDispositionKind::lowering_lane` is the pinned bridge between them.
//!
//! # The two representations
//!
//! * [`LoweringDisposition`] — the macro-time, owned-`String` form the generators build.
//! * [`mettail_runtime::LoweringDispositionDef`] — the `'static` form emitted into each
//!   language's generated metadata, reachable at runtime through
//!   `LanguageMetadata::lowering_dispositions`.
//!
//! [`emit_disposition_defs`] is the only place that converts one into the other.
//!
//! # Byte-compatibility with the legacy diagnostic
//!
//! The generated `EGraph<String>`-path report still emits a runtime `Err(String)` listing
//! the constructs that lowered nowhere. That message is assembled by
//! [`legacy_unsupported_messages`], which reconstructs the *exact* pre-existing strings —
//! `"{noun} `{name}` {detail}"` — from the `Declined` dispositions whose
//! [`LoweringDisposition::legacy_diagnostic`] flag is set. Newly-surfaced dispositions
//! (`Suppressed` orientations, fold declinations, lane attributions) carry the flag
//! `false` and therefore do not perturb one byte of previously generated code.

use mettail_runtime::{
    LoweredConstructKind, LoweredConstructOrigin, LoweringLane, LoweringOutcomeKind,
};
use proc_macro2::TokenStream;
use quote::quote;
use syn::LitStr;

/// What happened to one declared construct.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum LoweringOutcome {
    /// Lowered by the reporting lane. `label` is the emitted rule label
    /// (`"<Lang>::rewrite::<name>"`, `"<Lang>::equation::<name>::forward"`, …).
    Delivered { label: String },
    /// Lowered by `lane`, not here. `note` says what the lane does with it.
    DeliveredElsewhere { lane: LoweringLane, note: String },
    /// Deliberately not lowered anywhere, for the recorded `reason`.
    Suppressed { reason: String },
    /// Lowered nowhere. `reason` is why lowering refused it.
    Declined { reason: String },
}

/// One construct's disposition, in the macro-time owned form.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct LoweringDisposition {
    /// Which class of construct this is.
    pub(crate) construct_kind: LoweredConstructKind,
    /// The construct's declared name (equation/rewrite name, or a fold's constructor label).
    pub(crate) construct: String,
    /// Whether the author wrote it or `mettail_ast::auto_inject` injected it.
    pub(crate) origin: LoweredConstructOrigin,
    /// What happened.
    pub(crate) outcome: LoweringOutcome,
    /// ★ Whether this disposition reproduces one of the eight pre-existing `unsupported`
    /// diagnostic strings.
    ///
    /// Only these contribute to the generated runtime `Err(…)` message, so the generated
    /// report bodies stay byte-identical while the inventory grows strictly richer. See
    /// [`legacy_unsupported_messages`].
    pub(crate) legacy_diagnostic: bool,
}

impl LoweringDisposition {
    /// A construct this lane lowered, with the label of the rule it emitted.
    pub(crate) fn delivered(
        construct_kind: LoweredConstructKind,
        construct: impl Into<String>,
        origin: LoweredConstructOrigin,
        label: impl Into<String>,
    ) -> Self {
        Self {
            construct_kind,
            construct: construct.into(),
            origin,
            outcome: LoweringOutcome::Delivered { label: label.into() },
            legacy_diagnostic: false,
        }
    }

    /// A construct another lane lowers. `note` records what that lane does, so a reader
    /// does not have to trust the lane name alone.
    pub(crate) fn delivered_elsewhere(
        construct_kind: LoweredConstructKind,
        construct: impl Into<String>,
        origin: LoweredConstructOrigin,
        lane: LoweringLane,
        note: impl Into<String>,
    ) -> Self {
        Self {
            construct_kind,
            construct: construct.into(),
            origin,
            outcome: LoweringOutcome::DeliveredElsewhere { lane, note: note.into() },
            legacy_diagnostic: false,
        }
    }

    /// A construct deliberately left unlowered, with the decision recorded.
    pub(crate) fn suppressed(
        construct_kind: LoweredConstructKind,
        construct: impl Into<String>,
        origin: LoweredConstructOrigin,
        reason: impl Into<String>,
    ) -> Self {
        Self {
            construct_kind,
            construct: construct.into(),
            origin,
            outcome: LoweringOutcome::Suppressed { reason: reason.into() },
            legacy_diagnostic: false,
        }
    }

    /// A construct lowered nowhere.
    ///
    /// `legacy_diagnostic` must be `true` exactly when `reason` is the suffix of one of the
    /// eight pre-existing `unsupported` strings, so that
    /// [`legacy_unsupported_messages`] reproduces the generated diagnostic verbatim.
    pub(crate) fn declined(
        construct_kind: LoweredConstructKind,
        construct: impl Into<String>,
        origin: LoweredConstructOrigin,
        reason: impl Into<String>,
        legacy_diagnostic: bool,
    ) -> Self {
        Self {
            construct_kind,
            construct: construct.into(),
            origin,
            outcome: LoweringOutcome::Declined { reason: reason.into() },
            legacy_diagnostic,
        }
    }

    /// Whether this construct is lowered nowhere.
    pub(crate) fn is_declined(&self) -> bool {
        matches!(self.outcome, LoweringOutcome::Declined { .. })
    }

    /// ★ Whether this is a declination of a construct the GENERATOR injected.
    ///
    /// Categorically different from accepted debt: the generator emitted a construct its
    /// own lowering cannot consume. The inventory records it as its own category so a
    /// reader — and a golden test — can separate *"we have not implemented this yet"* from
    /// *"we broke this ourselves"*.
    #[allow(dead_code)] // Consumed by the generated inventory's runtime predicate.
    pub(crate) fn is_generator_bug(&self) -> bool {
        self.is_declined() && self.origin == LoweredConstructOrigin::AutoInjected
    }

    /// The pre-existing diagnostic string this disposition reproduces, if any.
    ///
    /// `"equation `par_comm` has side conditions"`, `"rewrite `Comm` LHS: …"`, and so on —
    /// the exact `format!` output the four `unsupported.push(…)` sites used to build.
    fn legacy_message(&self) -> Option<String> {
        match (&self.outcome, self.legacy_diagnostic) {
            (LoweringOutcome::Declined { reason }, true) => Some(format!(
                "{} `{}` {}",
                self.construct_kind.noun(),
                self.construct,
                reason,
            )),
            _ => None,
        }
    }

    /// The runtime `outcome` discriminant.
    fn outcome_kind(&self) -> LoweringOutcomeKind {
        match self.outcome {
            LoweringOutcome::Delivered { .. } => LoweringOutcomeKind::Delivered,
            LoweringOutcome::DeliveredElsewhere { .. } => LoweringOutcomeKind::DeliveredElsewhere,
            LoweringOutcome::Suppressed { .. } => LoweringOutcomeKind::Suppressed,
            LoweringOutcome::Declined { .. } => LoweringOutcomeKind::Declined,
        }
    }

    /// The runtime `detail` payload.
    fn detail(&self) -> &str {
        match &self.outcome {
            LoweringOutcome::Delivered { label } => label,
            LoweringOutcome::DeliveredElsewhere { note, .. } => note,
            LoweringOutcome::Suppressed { reason } => reason,
            LoweringOutcome::Declined { reason } => reason,
        }
    }

    /// The runtime `lane` payload (present only for `DeliveredElsewhere`).
    fn lane(&self) -> Option<LoweringLane> {
        match &self.outcome {
            LoweringOutcome::DeliveredElsewhere { lane, .. } => Some(*lane),
            _ => None,
        }
    }
}

/// ★ The pre-existing `unsupported: Vec<String>` — reconstructed verbatim, in declaration
/// order, from the dispositions that carry a legacy diagnostic.
///
/// This is the compatibility hinge of the whole change. The generated `EGraph<String>`-path
/// report embeds this list in a runtime `Err(…)`; reproducing it byte-for-byte is what lets
/// a macro-wide change regenerate all 46 languages and move only the metadata file.
pub(crate) fn legacy_unsupported_messages(dispositions: &[LoweringDisposition]) -> Vec<String> {
    dispositions
        .iter()
        .filter_map(LoweringDisposition::legacy_message)
        .collect()
}

/// ★ THE ANTI-VACUITY CHECK ON THE MECHANISM ITSELF.
///
/// An inventory that silently skips a construct is worse than no inventory: it reports a clean
/// bill of health for something it never looked at. This asserts the one property that makes
/// the record trustworthy — **every declared construct appears in it at least once** — at each
/// site that produces dispositions, so a future `continue` added ahead of a disposition push
/// fails macro expansion instead of quietly shrinking the record.
///
/// `include_folds` is false for the `EGraph<String>` path, whose report generator never walks
/// the fold rules at all (they are the typed path's concern); the inventory adds their
/// dispositions separately in [`crate::gen::runtime::dovetail_report::lowering_disposition_inventory`].
///
/// ★ #141 G9 — RETURNS the refusal as `compile_error!` tokens (EMPTY when every
/// declared construct is disposed). It used to `panic!`, and its own doc-comment
/// said that "a proc macro surfaces [a panic] as a compile error naming the
/// construct" — which is FALSE on this workspace's cranelift dev backend: the
/// payload never appears and `rustc` dies with `fatal runtime error: Rust cannot
/// catch foreign exceptions` (#141 RED-0, 2026-07-29). A generator that has lost
/// track of a declared construct still must not emit a language that claims
/// otherwise; the difference is that the author now learns which construct.
#[must_use]
pub(crate) fn every_construct_disposed_or_refusal(
    language: &mettail_ast::language::LanguageDef,
    dispositions: &[LoweringDisposition],
    include_folds: bool,
    site: &str,
) -> TokenStream {
    use std::collections::HashSet;

    let recorded: HashSet<(LoweredConstructKind, &str)> = dispositions
        .iter()
        .map(|disposition| (disposition.construct_kind, disposition.construct.as_str()))
        .collect();

    let mut missing = Vec::new();
    for equation in &language.equations {
        let name = equation.name.to_string();
        if !recorded.contains(&(LoweredConstructKind::Equation, name.as_str())) {
            missing.push(format!("equation `{name}`"));
        }
    }
    for rewrite in &language.rewrites {
        let name = rewrite.name.to_string();
        if !recorded.contains(&(LoweredConstructKind::Rewrite, name.as_str())) {
            missing.push(format!("rewrite `{name}`"));
        }
    }
    if include_folds {
        for rule in &language.terms {
            if rule.eval_mode != Some(mettail_ast::types::EvalMode::Fold) {
                continue;
            }
            let name = rule.label.to_string();
            if !recorded.contains(&(LoweredConstructKind::Fold, name.as_str())) {
                missing.push(format!("fold `{name}`"));
            }
        }
    }

    // ★ #141 G9. This is the census that makes a silently-dropped construct
    // impossible — and it was itself silent: a `panic!` inside a proc macro prints
    // NOTHING under this workspace's cranelift dev backend (#141 RED-0), so a
    // dropped construct aborted `rustc` with no message. The refusal is returned as
    // tokens for the caller to splice, which is the only shape available to a
    // function whose product is a bookkeeping check rather than emitted code.
    match missing.is_empty() {
        true => TokenStream::new(),
        false => {
            let message = format!(
                "mettail internal error: language `{}` — the lowering at `{site}` produced \
                 no disposition for {} declared construct(s): {}. Every declared construct \
                 must be accounted for; a construct with no disposition is exactly the \
                 silent drop this record exists to make impossible. This is a macro bug, \
                 not a grammar bug — please report it.",
                language.name,
                missing.len(),
                missing.join(", "),
            );
            quote::quote_spanned!(language.name.span() => compile_error!(#message);)
        },
    }
}

/// Emit the `&'static [LoweringDispositionDef]` array the generated metadata returns.
///
/// This is the ONLY conversion from the macro-time form to the runtime form, so the two
/// representations cannot disagree about what a disposition is.
pub(crate) fn emit_disposition_defs(dispositions: &[LoweringDisposition]) -> TokenStream {
    let defs: Vec<TokenStream> = dispositions
        .iter()
        .map(|disposition| {
            let construct_kind = construct_kind_tokens(disposition.construct_kind);
            let construct = lit(&disposition.construct);
            let origin = origin_tokens(disposition.origin);
            let outcome = outcome_tokens(disposition.outcome_kind());
            let detail = lit(disposition.detail());
            let lane = match disposition.lane() {
                Some(lane) => {
                    let lane = lane_tokens(lane);
                    quote! { ::core::option::Option::Some(#lane) }
                },
                None => quote! { ::core::option::Option::None },
            };
            quote! {
                mettail_runtime::LoweringDispositionDef {
                    construct_kind: #construct_kind,
                    construct: #construct,
                    origin: #origin,
                    outcome: #outcome,
                    detail: #detail,
                    lane: #lane,
                }
            }
        })
        .collect();

    quote! { &[#(#defs),*] }
}

fn lit(value: &str) -> LitStr {
    LitStr::new(value, proc_macro2::Span::call_site())
}

fn construct_kind_tokens(kind: LoweredConstructKind) -> TokenStream {
    match kind {
        LoweredConstructKind::Equation => {
            quote! { mettail_runtime::LoweredConstructKind::Equation }
        },
        LoweredConstructKind::Rewrite => quote! { mettail_runtime::LoweredConstructKind::Rewrite },
        LoweredConstructKind::Fold => quote! { mettail_runtime::LoweredConstructKind::Fold },
    }
}

fn origin_tokens(origin: LoweredConstructOrigin) -> TokenStream {
    match origin {
        LoweredConstructOrigin::Declared => {
            quote! { mettail_runtime::LoweredConstructOrigin::Declared }
        },
        LoweredConstructOrigin::AutoInjected => {
            quote! { mettail_runtime::LoweredConstructOrigin::AutoInjected }
        },
    }
}

fn outcome_tokens(outcome: LoweringOutcomeKind) -> TokenStream {
    match outcome {
        LoweringOutcomeKind::Delivered => {
            quote! { mettail_runtime::LoweringOutcomeKind::Delivered }
        },
        LoweringOutcomeKind::DeliveredElsewhere => {
            quote! { mettail_runtime::LoweringOutcomeKind::DeliveredElsewhere }
        },
        LoweringOutcomeKind::Suppressed => {
            quote! { mettail_runtime::LoweringOutcomeKind::Suppressed }
        },
        LoweringOutcomeKind::Declined => quote! { mettail_runtime::LoweringOutcomeKind::Declined },
    }
}

fn lane_tokens(lane: LoweringLane) -> TokenStream {
    match lane {
        LoweringLane::EGraphCongruenceClosure => {
            quote! { mettail_runtime::LoweringLane::EGraphCongruenceClosure }
        },
        LoweringLane::TypedNativeSubstitution => {
            quote! { mettail_runtime::LoweringLane::TypedNativeSubstitution }
        },
        LoweringLane::TypedNativeComm => quote! { mettail_runtime::LoweringLane::TypedNativeComm },
        LoweringLane::TypedNativeStructuralAc => {
            quote! { mettail_runtime::LoweringLane::TypedNativeStructuralAc }
        },
        LoweringLane::TypedNativeNestedStructuralAc => {
            quote! { mettail_runtime::LoweringLane::TypedNativeNestedStructuralAc }
        },
        LoweringLane::TypedNativeFold => quote! { mettail_runtime::LoweringLane::TypedNativeFold },
        LoweringLane::HostNativeEvaluation => {
            quote! { mettail_runtime::LoweringLane::HostNativeEvaluation }
        },
        LoweringLane::BinderCongruenceFloat => {
            quote! { mettail_runtime::LoweringLane::BinderCongruenceFloat }
        },
        LoweringLane::RhoNativeSystemProcess => {
            quote! { mettail_runtime::LoweringLane::RhoNativeSystemProcess }
        },
        LoweringLane::RhoNativeHandler => {
            quote! { mettail_runtime::LoweringLane::RhoNativeHandler }
        },
        LoweringLane::RhoExternalContract => {
            quote! { mettail_runtime::LoweringLane::RhoExternalContract }
        },
        LoweringLane::RhoAstContract => quote! { mettail_runtime::LoweringLane::RhoAstContract },
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// #141 G9 RED — the completeness census REFUSES by returning tokens
// ═══════════════════════════════════════════════════════════════════════════
//
// ⚠ No cell expects a panic: each reads the `TokenStream` the census returns.
#[cfg(test)]
mod census_refusal_red {
    use super::*;
    use mettail_ast::grammar::rule_fixture;
    use mettail_ast::language::{Equation, LanguageDef};
    use mettail_ast::pattern::{Pattern, PatternTerm};
    use proc_macro2::Span;
    use syn::Ident;

    fn id(name: &str) -> Ident {
        Ident::new(name, Span::call_site())
    }

    /// A language declaring exactly one equation, named `Assoc`.
    fn language_with_one_equation() -> LanguageDef {
        let mut language = crate::gen::empty_language_for_tests();
        language.equations.push(Equation {
            name: id("Assoc"),
            type_context: Vec::new(),
            premises: Vec::new(),
            left: Pattern::Term(PatternTerm::Var(id("X"))),
            right: Pattern::Term(PatternTerm::Var(id("Y"))),
        });
        let _ = rule_fixture(id("Unused"), id("Term"));
        language
    }

    /// ★ THE MUTATION CELL. A declared equation with NO disposition refuses, and
    /// the diagnostic names the construct, the language and the lowering site.
    #[test]
    fn a_construct_with_no_disposition_refuses_and_names_it() {
        let language = language_with_one_equation();
        let rendered =
            every_construct_disposed_or_refusal(&language, &[], false, "a_test_lowering")
                .to_string();

        assert!(
            rendered.contains("compile_error"),
            "a declared construct that left the lowering with no account of itself must \
             REFUSE — a silent drop is exactly what this record exists to make \
             impossible. Got: {rendered}",
        );
        assert!(
            rendered.contains("Assoc"),
            "the diagnostic must name the CONSTRUCT that went missing. Got: {rendered}",
        );
        assert!(
            rendered.contains("TestLang"),
            "…and the LANGUAGE, since one `rustc` process expands every bundled \
             grammar. Got: {rendered}",
        );
        assert!(
            rendered.contains("a_test_lowering"),
            "…and the SITE, since four lowerings share this census and they fail for \
             different reasons. Got: {rendered}",
        );
    }

    /// ★ THE CONTROL that must NOT discriminate: the same language, with the
    /// equation's dispositions recorded, refuses NOTHING and emits no tokens.
    #[test]
    fn a_fully_disposed_language_emits_nothing_at_all() {
        let language = language_with_one_equation();
        // The census keys on the equation's NAME, so one delivered record for
        // `Assoc` is exactly what accounts for it.
        let dispositions = vec![LoweringDisposition::delivered(
            LoweredConstructKind::Equation,
            "Assoc".to_string(),
            LoweredConstructOrigin::Declared,
            "TestLang::equation::Assoc::forward".to_string(),
        )];
        let rendered =
            every_construct_disposed_or_refusal(&language, &dispositions, false, "a_test_lowering")
                .to_string();

        assert!(
            rendered.is_empty(),
            "a census that passes must emit NOTHING — anything else moves the generated \
             bytes of every language and would show up as a mover on the \
             `target/generated` manifest. Got: {rendered}",
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The legacy diagnostic is reconstructed verbatim — `"{noun} `{name}` {suffix}"` — and
    /// ONLY from dispositions that opt in. This is the property that keeps every previously
    /// generated report body byte-identical.
    #[test]
    fn legacy_messages_reproduce_the_pre_existing_strings() {
        let dispositions = vec![
            LoweringDisposition::declined(
                LoweredConstructKind::Equation,
                "par_comm",
                LoweredConstructOrigin::Declared,
                "has side conditions",
                true,
            ),
            LoweringDisposition::declined(
                LoweredConstructKind::Rewrite,
                "NormCastIntToBigIntInInt",
                LoweredConstructOrigin::AutoInjected,
                "LHS: constructor `CastInt` has no category",
                true,
            ),
            // Newly surfaced: must NOT appear in the legacy diagnostic.
            LoweringDisposition::declined(
                LoweredConstructKind::Fold,
                "shift_right",
                LoweredConstructOrigin::Declared,
                "parameter `l` is not a Simple/Base typed parameter",
                false,
            ),
            LoweringDisposition::suppressed(
                LoweredConstructKind::Equation,
                "NewComm",
                LoweredConstructOrigin::Declared,
                "user decision Q-NC",
            ),
            LoweringDisposition::delivered_elsewhere(
                LoweredConstructKind::Rewrite,
                "ParCong",
                LoweredConstructOrigin::Declared,
                LoweringLane::EGraphCongruenceClosure,
                "congruence closure propagates the merge",
            ),
        ];

        assert_eq!(
            legacy_unsupported_messages(&dispositions),
            vec![
                "equation `par_comm` has side conditions".to_string(),
                "rewrite `NormCastIntToBigIntInInt` LHS: constructor `CastInt` has no category"
                    .to_string(),
            ],
        );
    }

    /// A declination of an AUTO-INJECTED construct is a generator bug; a declination of a
    /// DECLARED one is accepted debt; a non-declination is neither.
    #[test]
    fn generator_bug_is_exactly_declined_and_auto_injected() {
        let declared_declined = LoweringDisposition::declined(
            LoweredConstructKind::Equation,
            "e",
            LoweredConstructOrigin::Declared,
            "r",
            false,
        );
        let injected_declined = LoweringDisposition::declined(
            LoweredConstructKind::Rewrite,
            "r",
            LoweredConstructOrigin::AutoInjected,
            "r",
            false,
        );
        let injected_delivered = LoweringDisposition::delivered(
            LoweredConstructKind::Rewrite,
            "r",
            LoweredConstructOrigin::AutoInjected,
            "L::rewrite::r",
        );

        assert!(!declared_declined.is_generator_bug());
        assert!(declared_declined.is_declined());
        assert!(injected_declined.is_generator_bug());
        assert!(!injected_delivered.is_generator_bug());
        assert!(!injected_delivered.is_declined());
    }
}
