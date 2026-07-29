//! ★★ Task #94 — THE GOLDEN LOWERING-DISPOSITION INVENTORY.
//!
//! # What this file is
//!
//! Every production language's **declination set**, pinned by name. A declination is a
//! declared construct — an equation orientation, a rewrite, or a `fold` — that the generated
//! runtime lowering emits **nowhere**: no rule on this lane, no delegation to another lane, no
//! recorded decision to leave it out. It is a construct the language's surface syntax still
//! advertises and its semantics no longer contains.
//!
//! # Why a pinned SET and not a count
//!
//! A count is satisfied by any set of the same size, so a count-based gate goes green while one
//! construct silently replaces another. These assertions compare the **exact sorted list** of
//! `(construct kind, name, origin)` triples, so:
//!
//! * a construct that **newly** stops being lowered turns this suite RED **naming it**;
//! * a construct that **starts** being lowered also turns it red, naming it, which is the
//!   signal to move it out of the debt table;
//! * a swap of one for another — the failure mode a count cannot see — turns it red twice.
//!
//! That is the anti-vacuity property: **it fails on additions, not on a number.**
//!
//! # ★ The debt is ACCEPTED, not hidden — and one class of it has now been PAID
//!
//! The entries below are real defects. Pinning them is not approval; it is the difference
//! between a defect that is *known, named, and bounded* and one that is invisible. When one is
//! repaired, the assertion that mentions it fails and names it, which is exactly the
//! notification a repair should produce.
//!
//! ★★ THAT NOTIFICATION FIRED. Task #101 repaired the fold gate: `TypeExpr::Collection`
//! parameters are lowered per CARRIER — an ordered `Vec(T)` through the labelled, losslessly
//! invertible `FieldSeq<T>` leaf, a whole-constructor `HashBag(T)` through the AC bag node it
//! already had — so the **fifteen** fold declinations this table used to carry are now zero.
//! They were not deleted: [`no_fold_in_the_corpus_is_refused_for_a_collection_parameter`]
//! carries the same enumeration INVERTED, pinning the exact set of fifteen `Delivered` folds,
//! so a fold that stops being lowered turns this suite red naming itself exactly as a fold that
//! newly stopped being lowered used to.
//!
//! The remaining debt is the `NormCast*` injection (`ast/src/auto_inject.rs`) and Rholang's
//! `Extrude` equation.
//!
//! # ★ The two categories are NOT the same
//!
//! | origin | meaning |
//! |---|---|
//! | `Declared` | the language author wrote the construct and the lowering has not implemented its shape — **accepted debt** |
//! | `AutoInjected` | the GENERATOR emitted a construct its own lowering cannot consume — **a generator bug** |
//!
//! All 15 auto-injected declinations are `NormCast*` rewrites synthesized over `CastBool` /
//! `CastInt` / `CastFloat` / `CastFixed` constructors the languages never declare. That is a
//! self-inflicted wound, and the inventory records it as its own category rather than filing it
//! beside honest unimplemented-feature debt.
//!
//! # ★★ The anti-vacuity control on the whole file
//!
//! [`congruence_rewrites_are_delivered_elsewhere_not_declined`] proves the mechanism does not
//! reach its small declination numbers by classifying everything as fine. Rholang declares 461
//! rewrites; **139 of its disposition entries attribute a rewrite to another lane**, and 216 of
//! Calculator's do. Had those been called declinations, this table would carry four hundred
//! false positives and be worthless.

#![cfg(all(
    feature = "ambient",
    feature = "calculator",
    feature = "json",
    feature = "lambda",
    feature = "monoid",
    feature = "pi",
    feature = "rholang",
    feature = "turing",
))]

use mettail_runtime::{
    LanguageMetadata, LoweredConstructKind, LoweredConstructOrigin, LoweringDispositionDef,
    LoweringLane, LoweringOutcomeKind,
};

/// (Task #101) The live fixture that keeps "the gate did not open too far" from being an
/// assertion about an empty set — the corpus declares no fold with a set/map parameter. See
/// clause (c) of [`no_fold_in_the_corpus_is_refused_for_a_collection_parameter`].
#[path = "definitions/map_param_refusal_demo.rs"]
mod map_param_refusal_demo;

/// The eight production languages, each with its metadata.
fn production_languages() -> Vec<(&'static str, &'static dyn LanguageMetadata)> {
    vec![
        ("Ambient", &mettail_languages::ambient::AmbientMetadata),
        ("Calculator", &mettail_languages::calculator::CalculatorMetadata),
        ("Json", &mettail_languages::json::JsonMetadata),
        ("Lambda", &mettail_languages::lambda::LambdaMetadata),
        ("Monoid", &mettail_languages::monoid::MonoidMetadata),
        ("Pi", &mettail_languages::pi::PiMetadata),
        ("Rholang", &mettail_languages::rholang::RholangMetadata),
        ("Turing", &mettail_languages::turing::TuringMetadata),
    ]
}

/// `(kind noun, construct name, origin)` for each declination, in inventory order.
fn declination_triples(metadata: &dyn LanguageMetadata) -> Vec<(&'static str, String, &'static str)> {
    metadata
        .lowering_dispositions()
        .iter()
        .filter(|disposition| disposition.is_declined())
        .map(|disposition| {
            (
                disposition.construct_kind.noun(),
                disposition.construct.to_string(),
                disposition.origin.as_str(),
            )
        })
        .collect()
}

/// A readable rendering of one language's declinations, for failure messages.
fn render_declinations(metadata: &dyn LanguageMetadata) -> String {
    metadata
        .lowering_dispositions()
        .iter()
        .filter(|disposition| disposition.is_declined())
        .map(|disposition| {
            format!(
                "\n    {:8} {:32} {:12} {}",
                disposition.construct_kind.noun(),
                disposition.construct,
                disposition.origin.as_str(),
                disposition.detail,
            )
        })
        .collect()
}

/// Assert one language's declination set exactly.
fn assert_declinations(
    language: &str,
    metadata: &dyn LanguageMetadata,
    expected: &[(&str, &str, &str)],
) {
    let actual = declination_triples(metadata);
    let expected: Vec<(&str, String, &str)> = expected
        .iter()
        .map(|(kind, name, origin)| (*kind, (*name).to_string(), *origin))
        .collect();
    assert_eq!(
        actual,
        expected,
        "★ {language}'s declination set changed. An ADDITION is a construct that newly stops \
         being lowered; a REMOVAL is a repair, and the debt table below should lose its \
         entry.{}",
        render_declinations(metadata),
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// Per-language accepted-debt tables
// ─────────────────────────────────────────────────────────────────────────────

/// Ambient declines NOTHING.
///
/// ★ Every one of its seven equation dispositions is an attribution, not a declination, and
/// that is the interesting fact. `ScopeExtrusion` / `InNew` / `OutNew` / `OpenNew` / `AmbNew`
/// each carry a `Lambda` metapattern that the structural lowering cannot lower — but the
/// generated binder-congruence normal form floats binders outward before reduction and
/// discharges them in full, so they are `DeliveredElsewhere { BinderCongruenceFloat }`.
/// `NewComm` is `Suppressed`: in-Rho binder-commutation reordering is deliberately omitted
/// (the user's Q-NC decision), because the host's alpha-canonical-key minimization is not
/// Match-expressible and redex exposure is commutation-invariant.
///
/// Calling any of those seven a declination would be a false alarm on a language that works.
#[test]
fn ambient_declines_nothing_because_its_binder_laws_are_covered() {
    let metadata = &mettail_languages::ambient::AmbientMetadata;
    assert_declinations("Ambient", metadata, &[]);

    let inventory = metadata.lowering_dispositions();
    let floated = inventory
        .iter()
        .filter(|d| d.lane == Some(LoweringLane::BinderCongruenceFloat))
        .count();
    let suppressed = inventory
        .iter()
        .filter(|d| d.outcome == LoweringOutcomeKind::Suppressed)
        .count();
    assert_eq!(
        (floated, suppressed),
        (5, 2),
        "the five float laws are attributed to the float lane and `NewComm`'s two \
         orientations are suppressed by the Q-NC decision; inventory: {inventory:?}",
    );
}

/// Pi declines nothing, for the same reason as Ambient.
#[test]
fn pi_declines_nothing_because_its_binder_laws_are_covered() {
    let metadata = &mettail_languages::pi::PiMetadata;
    assert_declinations("Pi", metadata, &[]);

    let inventory = metadata.lowering_dispositions();
    assert_eq!(
        inventory
            .iter()
            .filter(|d| d.lane == Some(LoweringLane::BinderCongruenceFloat))
            .count(),
        1,
        "`ScopeExt` is discharged by the float lane; inventory: {inventory:?}",
    );
    assert_eq!(
        inventory
            .iter()
            .filter(|d| d.outcome == LoweringOutcomeKind::Suppressed)
            .count(),
        2,
        "`NewComm`'s two orientations are suppressed by the Q-NC decision; \
         inventory: {inventory:?}",
    );
}

/// Lambda and Monoid decline nothing at all — the two production languages whose declared
/// semantics is lowered in full.
#[test]
fn lambda_and_monoid_decline_nothing() {
    assert_declinations("Lambda", &mettail_languages::lambda::LambdaMetadata, &[]);
    assert_declinations("Monoid", &mettail_languages::monoid::MonoidMetadata, &[]);

    // Monoid's two `Suppressed` entries are a NEWLY VISIBLE fact, not a defect: `UnitL`'s and
    // `UnitR`'s reverse orientations (`x ⟶ x · 1`) have a bare metavariable on the left, so
    // the reversed rule would match every e-class. That elision was previously invisible —
    // the code took the branch and recorded nothing.
    let monoid = mettail_languages::monoid::MonoidMetadata.lowering_dispositions();
    assert_eq!(
        monoid
            .iter()
            .filter(|d| d.outcome == LoweringOutcomeKind::Suppressed)
            .count(),
        2,
        "inventory: {monoid:?}",
    );
}

/// ★ Calculator: EIGHT declinations, every one of them a GENERATOR BUG.
///
/// All eight are `NormCast*` cast-canonicalization rewrites that `ast/src/auto_inject.rs`
/// synthesizes. Three name `CastBool`, one `CastFloat`, one `CastFixed` — constructors the
/// Calculator never declares, so the rewrite's own LHS cannot lower ("constructor `CastBool`
/// has no category"). The other three carry a synthetic-injection guard premise that
/// structural saturation does not model.
///
/// The generator emitted eight rewrites its own lowering cannot consume. That is categorically
/// different from an unimplemented feature, and the `AutoInjected` origin says so.
#[test]
fn calculator_declines_only_generator_injected_cast_rewrites() {
    let metadata = &mettail_languages::calculator::CalculatorMetadata;
    assert_declinations(
        "Calculator",
        metadata,
        &[
            ("rewrite", "NormCastBoolToUInt32InProc", "AutoInjected"),
            ("rewrite", "NormCastBoolToBigIntInProc", "AutoInjected"),
            ("rewrite", "NormCastBoolToBigRatInProc", "AutoInjected"),
            ("rewrite", "NormCastUInt32ToBigIntInProc", "AutoInjected"),
            ("rewrite", "NormCastUInt32ToBigRatInProc", "AutoInjected"),
            ("rewrite", "NormCastFloatToBigRatInProc", "AutoInjected"),
            ("rewrite", "NormCastBigIntToBigRatInProc", "AutoInjected"),
            ("rewrite", "NormCastFixedToBigRatInProc", "AutoInjected"),
        ],
    );
    assert_eq!(metadata.generator_bug_lowerings().len(), 8);
}

/// Json: one declination, also a generator-injected `NormCast*`.
#[test]
fn json_declines_only_a_generator_injected_cast_rewrite() {
    let metadata = &mettail_languages::json::JsonMetadata;
    assert_declinations(
        "Json",
        metadata,
        &[("rewrite", "NormCastBoolToBigRatInValue", "AutoInjected")],
    );
    assert_eq!(metadata.generator_bug_lowerings().len(), 1);
}

/// ★★ Turing declines NOTHING — and the entry it used to carry was the machine's entire
/// ability to compute.
///
/// `shift_right` advances the tape head. Its first parameter is `l:Vec(Sym)`, a
/// `TypeExpr::Collection`, and the fold gate used to drop it, so the head never moved and every
/// derivation had length at most one: the language named `Turing` could not compute more than
/// one step. Task #101 gave the ordered container a carrier with an inverse, and the fold is
/// lowered.
///
/// The zero is POSITIVELY CONTROLLED here rather than asserted bare: the same walk that finds
/// no declination must find `shift_right` `Delivered`, naming the rule it emitted. A walk that
/// inspected nothing would satisfy the first assertion and fail the second. The measured
/// consequence — two firings, the second one the head move — is
/// `languages/tests/turing.rs`'s `turing_head_moves_because_shift_right_folds`.
#[test]
fn turing_declines_nothing_because_its_head_move_is_lowered() {
    let metadata = &mettail_languages::turing::TuringMetadata;
    assert_declinations("Turing", metadata, &[]);
    assert!(
        metadata.generator_bug_lowerings().is_empty(),
        "Turing injects nothing its own lowering cannot consume",
    );

    let shift_right: Vec<&LoweringDispositionDef> = metadata
        .lowering_dispositions()
        .iter()
        .filter(|d| {
            d.construct_kind == LoweredConstructKind::Fold && d.construct == "shift_right"
        })
        .collect();
    assert_eq!(
        shift_right.len(),
        1,
        "`shift_right` must have exactly one disposition; inventory: {:?}",
        metadata.lowering_dispositions(),
    );
    assert_eq!(
        shift_right[0].outcome,
        LoweringOutcomeKind::Delivered,
        "★ the head move must be LOWERED — that is the whole of Task #101 for this language: {}",
        shift_right[0].summary(),
    );
    assert_eq!(
        shift_right[0].detail, "Turing::fold::Tape_shift_right",
        "a Delivered disposition carries the label of the rule it emitted: {}",
        shift_right[0].summary(),
    );
}

/// ★ Rholang: SEVEN declinations — one equation and six generator-injected rewrites.
///
/// ⚠ FOURTEEN ENTRIES LEFT THIS TABLE UNDER TASK #101, all of one class: the polyadic-syntax
/// desugarings — `PParInternal`'s `ps:HashBag(Proc)`, the seven `*2Plus` sends' `bs:Vec(Proc)`,
/// the five `InputBind*` receives' `args:Vec(Proc)` / `lhss:Vec(Name)`, and `PForUser`'s
/// `rows:Vec(ForRow)`. Every one had been refused for the SAME reason as Turing's head move — a
/// collection-typed parameter whose lowered derivation child had no inverse — which is why the
/// class was a class and not fourteen unrelated bugs, and why one repair retired all fourteen.
/// Their `Delivered` labels are pinned as a SET in
/// [`no_fold_in_the_corpus_is_refused_for_a_collection_parameter`], so this removal cannot be
/// mistaken for the folds quietly vanishing.
///
/// ⚠ THIRTEEN OF THOSE FOURTEEN REMAIN; `PParInternal` IS NOT ONE OF THEM (2026-07-29). The
/// `__ppar(…)` rule was deleted outright as a vestige of the pre-braced grammar — see
/// `languages/src/rholang.rs`, above the `PPar` rule — so its fold is not "quietly missing",
/// it has no rule to be the fold OF. The count above is left at fourteen because it is a
/// statement about what Task #101 measured, not about what the grammar declares today; the
/// live count is whatever [`COLLECTION_PARAMETER_FOLDS`] enumerates, and that constant is the
/// one a future reader should trust.
#[test]
fn rholang_declination_set_is_pinned() {
    let metadata = &mettail_languages::rholang::RholangMetadata;
    assert_declinations(
        "Rholang",
        metadata,
        &[
            ("equation", "Extrude", "Declared"),
            ("rewrite", "NormCastIntToBigIntInProc", "AutoInjected"),
            ("rewrite", "NormCastIntToBigRatInProc", "AutoInjected"),
            ("rewrite", "NormCastUInt32ToIntInProc", "AutoInjected"),
            ("rewrite", "NormCastUInt32ToBigIntInProc", "AutoInjected"),
            ("rewrite", "NormCastUInt32ToBigRatInProc", "AutoInjected"),
            ("rewrite", "NormCastBigIntToBigRatInProc", "AutoInjected"),
        ],
    );
    assert_eq!(metadata.generator_bug_lowerings().len(), 6);
}

// ─────────────────────────────────────────────────────────────────────────────
// Cross-language totals and class enumerations
// ─────────────────────────────────────────────────────────────────────────────

/// The whole-corpus totals, by construct class and origin.
///
/// Pinned as a table rather than a sum so a shift BETWEEN classes — a fold declination
/// becoming a rewrite declination, say — cannot hide inside an unchanged total.
#[test]
fn production_declination_totals_are_pinned() {
    let mut equations = 0usize;
    let mut rewrites = 0usize;
    let mut folds = 0usize;
    let mut declared = 0usize;
    let mut injected = 0usize;
    let mut inspected = 0usize;

    for (name, metadata) in production_languages() {
        let inventory = metadata.lowering_dispositions();
        assert!(
            !inventory.is_empty(),
            "{name} publishes an EMPTY inventory — every count below would be vacuously \
             satisfied by a language nothing looked at",
        );
        inspected += inventory.len();
        for disposition in inventory.iter().filter(|d| d.is_declined()) {
            match disposition.construct_kind {
                LoweredConstructKind::Equation => equations += 1,
                LoweredConstructKind::Rewrite => rewrites += 1,
                LoweredConstructKind::Fold => folds += 1,
            }
            match disposition.origin {
                LoweredConstructOrigin::Declared => declared += 1,
                LoweredConstructOrigin::AutoInjected => injected += 1,
            }
        }
    }

    assert_eq!(
        (equations, rewrites, folds),
        (1, 15, 0),
        "the per-class declination totals across the eight production languages. ★ The fold \
         column is ZERO since Task #101: every collection-parameter fold is lowered. Pinned as \
         a per-class table rather than a sum precisely so that a fold declination reappearing \
         under a different class cannot hide inside an unchanged total.",
    );
    assert_eq!(
        (declared, injected),
        (1, 15),
        "ONE is accepted debt (Rholang's `Extrude` equation); fifteen are generator bugs",
    );
    assert_eq!(equations + rewrites + folds, 16);
    assert!(
        inspected > 500,
        "the inventory must cover the whole corpus, not a handful of constructs \
         (inspected {inspected})",
    );
}

/// ★★ THE ANTI-VACUITY CONTROL ON THIS ENTIRE FILE.
///
/// The declination totals above are small. They are small because most constructs really are
/// lowered — a great many of them on a lane other than the structural one. A mechanism that
/// reached the same small numbers by classifying everything as fine would be indistinguishable
/// from this one on the tests above and useless in practice.
///
/// This asserts the other side of the ledger: **every congruence rewrite in the corpus is
/// attributed to the e-graph congruence closure by name**, and the attributed population is
/// large. Had those been called declinations, the tables above would carry hundreds of false
/// positives.
#[test]
fn congruence_rewrites_are_delivered_elsewhere_not_declined() {
    let mut attributed_to_congruence = 0usize;
    let mut attributed_anywhere = 0usize;

    for (name, metadata) in production_languages() {
        for disposition in metadata.lowering_dispositions() {
            if disposition.outcome != LoweringOutcomeKind::DeliveredElsewhere {
                continue;
            }
            attributed_anywhere += 1;
            let lane = disposition
                .lane
                .unwrap_or_else(|| panic!("{name}: {} names no lane", disposition.summary()));
            if lane == LoweringLane::EGraphCongruenceClosure {
                attributed_to_congruence += 1;
            }
        }
    }

    assert!(
        attributed_to_congruence >= 300,
        "the congruence lane must carry the bulk of the corpus's rewrites; counted \
         {attributed_to_congruence}",
    );
    assert!(
        attributed_anywhere > attributed_to_congruence,
        "attribution must distinguish lanes rather than answering `congruence` for \
         everything: {attributed_anywhere} attributed, {attributed_to_congruence} to \
         congruence",
    );

    // Rholang's congruence population is the concrete instance of the 400-false-positive
    // hazard: this many rewrites produce no structural rule and are nevertheless correct.
    let rholang = mettail_languages::rholang::RholangMetadata.lowering_dispositions();
    let rholang_congruence = rholang
        .iter()
        .filter(|d| d.lane == Some(LoweringLane::EGraphCongruenceClosure))
        .count();
    assert!(
        rholang_congruence >= 130,
        "Rholang attributes {rholang_congruence} rewrites to congruence closure; calling \
         them declinations would bury its six real ones",
    );
}

/// ★★ THE SIBLING ENUMERATION, INVERTED (Task #101).
///
/// This assertion used to read
/// `every_declined_fold_in_the_corpus_is_refused_for_a_collection_parameter`: every fold the
/// gate refused, across the entire corpus, refused for ONE shape — a parameter whose type is a
/// `TypeExpr::Collection`. Not one was refused for a binder abstraction, a guard slot, an
/// optional group, or an arrow type. It existed because "adding a guard ≠ enumerating siblings"
/// had been the recurring failure of the surrounding campaign: a gate written against the
/// instance's lane rather than the SHAPE lets the class recur.
///
/// The enumeration did its job. Because the fifteen refusals were one shape, one repair —
/// giving the ordered container a carrier with an inverse — retired all fifteen at once, and
/// this assertion is now the same enumeration read the other way:
///
///   (a) **the count is zero**, naming any survivor;
///   (b) ★★ **the non-vacuity control**: the EXACT SET of fifteen `(language::construct,
///       delivered-label)` pairs. A zero on its own is satisfied by a corpus nothing looked at,
///       and — worse — by a fold that stopped being *declared*. Pinning the delivered set means
///       a fold that stops being lowered, or is renamed, or loses its rule label, turns this
///       red NAMING ITSELF, exactly as a newly-refused fold used to;
///   (c) **the gate did not open too far**: the `MapParamRefusalDemo` fixture's `HashMap`
///       parameter is still `Declined`. The corpus has zero set/map fold parameters, so without
///       a live fixture that clause would be an assertion about an empty set.
#[test]
fn no_fold_in_the_corpus_is_refused_for_a_collection_parameter() {
    // ── (a) the count is ZERO, and any survivor is named ──────────────────────────────────
    let mut declined_folds: Vec<(String, String)> = Vec::new();
    for (name, metadata) in production_languages() {
        for disposition in metadata.lowering_dispositions() {
            if disposition.construct_kind != LoweredConstructKind::Fold
                || !disposition.is_declined()
            {
                continue;
            }
            declined_folds.push((
                format!("{name}::{}", disposition.construct),
                disposition.detail.to_string(),
            ));
        }
    }
    assert!(
        declined_folds.is_empty(),
        "★ a fold is refused again. The collection-parameter class had fifteen members and \
         Task #101 retired all of them; a survivor here is either a NEW shape the gate does not \
         admit or a regression in the carrier lowering: {declined_folds:#?}",
    );

    // ── (b) ★★ THE NON-VACUITY CONTROL: the fifteen, delivered, as a SET ──────────────────
    // These are the exact folds the gate used to drop — Turing's head move and Rholang's
    // fourteen polyadic desugarings — each paired with the label of the rule it now emits.
    let mut delivered_collection_folds: Vec<(String, String)> = Vec::new();
    for (name, metadata) in production_languages() {
        for disposition in metadata.lowering_dispositions() {
            if disposition.construct_kind != LoweredConstructKind::Fold
                || disposition.outcome != LoweringOutcomeKind::Delivered
            {
                continue;
            }
            let qualified = format!("{name}::{}", disposition.construct);
            if COLLECTION_PARAMETER_FOLDS.contains(&qualified.as_str()) {
                delivered_collection_folds
                    .push((qualified, disposition.detail.to_string()));
            }
        }
    }
    delivered_collection_folds.sort();

    let mut expected: Vec<(String, String)> = vec![
        ("Turing::shift_right", "Turing::fold::Tape_shift_right"),
        ("Rholang::POutput2Plus", "Rholang::fold::Proc_POutput2Plus"),
        ("Rholang::PPersistOutput2Plus", "Rholang::fold::Proc_PPersistOutput2Plus"),
        ("Rholang::POutputNil2Plus", "Rholang::fold::Proc_POutputNil2Plus"),
        ("Rholang::PPersistOutputNil2Plus", "Rholang::fold::Proc_PPersistOutputNil2Plus"),
        ("Rholang::POutputQuoted2Plus", "Rholang::fold::Proc_POutputQuoted2Plus"),
        ("Rholang::POutputShort2Plus", "Rholang::fold::Proc_POutputShort2Plus"),
        ("Rholang::PPersistOutputShort2Plus", "Rholang::fold::Proc_PPersistOutputShort2Plus"),
        ("Rholang::InputBindQuery", "Rholang::fold::InputBind_InputBindQuery"),
        ("Rholang::InputBindEmptyQuery", "Rholang::fold::InputBind_InputBindEmptyQuery"),
        ("Rholang::InputBindQuotedQuery", "Rholang::fold::InputBind_InputBindQuotedQuery"),
        ("Rholang::InputBindPolyadic", "Rholang::fold::InputBind_InputBindPolyadic"),
        (
            "Rholang::InputBindPersistentPolyadic",
            "Rholang::fold::InputBind_InputBindPersistentPolyadic",
        ),
        ("Rholang::PForUser", "Rholang::fold::Proc_PForUser"),
    ]
    .into_iter()
    .map(|(c, l)| (c.to_string(), l.to_string()))
    .collect();
    expected.sort();

    assert_eq!(
        expected.len(),
        COLLECTION_PARAMETER_FOLDS.len(),
        "the expected list and the membership set must describe the same fifteen folds",
    );
    assert_eq!(
        delivered_collection_folds, expected,
        "★★ the fifteen collection-parameter folds must ALL be Delivered, each naming the rule \
         it emitted. A missing entry means a fold stopped being lowered (or stopped being \
         declared) and the zero above went green over its absence — which is exactly the \
         failure a bare count cannot see.",
    );

    // ── (c) the gate did not open too far, on a NON-EMPTY set ─────────────────────────────
    // The corpus declares no fold with a set/map parameter, so this clause needs a live
    // fixture. `MapParamRefusalDemo::MapFold` takes a `HashMap(Proc, Proc)`, whose `Debug` does
    // not agree with `Eq` (its e-graph content key is a SORTED `Display`), so there is no
    // stored order to invert and no honest carrier for it. Its sibling `VecFold` on the same
    // language IS delivered — the positive control that keeps this from being a language
    // nothing looked at. Both, with their reasons, are asserted in
    // `languages/tests/collection_fold_carriers.rs`.
    let fixture = map_param_refusal_demo::MapParamRefusalDemoMetadata.lowering_dispositions();
    let map_fold: Vec<&LoweringDispositionDef> = fixture
        .iter()
        .filter(|d| d.construct_kind == LoweredConstructKind::Fold && d.construct == "MapFold")
        .collect();
    assert_eq!(map_fold.len(), 1, "the fixture's `MapFold` must have one disposition");
    assert!(
        map_fold[0].is_declined(),
        "★ THE GATE OPENED TOO FAR: a keyed container has no order to invert, so admitting it \
         would claim an inverse that does not exist: {}",
        map_fold[0].summary(),
    );
    assert!(
        map_fold[0].detail.contains("HashMap("),
        "the declination must NAME the refusing type: {}",
        map_fold[0].summary(),
    );
    let vec_fold: Vec<&LoweringDispositionDef> = fixture
        .iter()
        .filter(|d| d.construct_kind == LoweredConstructKind::Fold && d.construct == "VecFold")
        .collect();
    assert_eq!(vec_fold.len(), 1, "the fixture's `VecFold` control must have one disposition");
    assert_eq!(
        vec_fold[0].outcome,
        LoweringOutcomeKind::Delivered,
        "the ORDERED control on the same language must be delivered, or the refusal above is \
         indistinguishable from a walk that inspected nothing: {}",
        vec_fold[0].summary(),
    );
}

/// The fifteen folds whose declaration carries a `TypeExpr::Collection` parameter — the exact
/// class the fold gate used to refuse. Membership is a property of the GRAMMAR (each of these
/// declares a `Vec(T)` or `HashBag(T)` parameter), so the list is stable under lowering
/// changes and is what makes clause (b) of
/// [`no_fold_in_the_corpus_is_refused_for_a_collection_parameter`] a set assertion rather than
/// a count.
///
/// ⚠ THIS LIST IS THE PRODUCTION CORPUS ONLY, and says so because the earlier census did not.
/// Task #94's note here read "a whole-tree parse of all 49 `language!` bodies … found 186
/// declared folds and exactly 16 collection-parameter refusals: the 15 here plus the
/// `TypedDropDemo::Head` fixture". Measured under #101, that census was already short: repairing
/// the gate also flipped `IdentParamToy::Call` (`args:Vec(Num)`, in
/// `languages/tests/ident_param_capture.rs`) from `Declined` to `Delivered`, which the census
/// does not mention. A test-hosted grammar is not in `production_languages()`, so it cannot be
/// pinned here; the honest scope of THIS constant is the eight production languages, and the
/// count of test-hosted instances is left to the fixtures that own them
/// (`lowering_disposition_reds.rs` for `TypedDropDemo::Head`,
/// `collection_fold_carriers.rs` for `MapParamRefusalDemo`).
const COLLECTION_PARAMETER_FOLDS: &[&str] = &[
    "Turing::shift_right",
    // `Rholang::PParInternal` was here until 2026-07-29, when the `__ppar(…)` rule it named
    // was deleted as a vestige of the pre-braced `PPar` grammar. It is the only entry ever
    // removed from this list for that reason — every other removal would be a regression.
    "Rholang::POutput2Plus",
    "Rholang::PPersistOutput2Plus",
    "Rholang::POutputNil2Plus",
    "Rholang::PPersistOutputNil2Plus",
    "Rholang::POutputQuoted2Plus",
    "Rholang::POutputShort2Plus",
    "Rholang::PPersistOutputShort2Plus",
    "Rholang::InputBindQuery",
    "Rholang::InputBindEmptyQuery",
    "Rholang::InputBindQuotedQuery",
    "Rholang::InputBindPolyadic",
    "Rholang::InputBindPersistentPolyadic",
    "Rholang::PForUser",
];

/// A `DeliveredElsewhere` disposition always names a lane; no other outcome ever does.
#[test]
fn lane_is_present_exactly_for_delivered_elsewhere() {
    let mut checked = 0usize;
    for (name, metadata) in production_languages() {
        for disposition in metadata.lowering_dispositions() {
            checked += 1;
            let expected_lane = disposition.outcome == LoweringOutcomeKind::DeliveredElsewhere;
            assert_eq!(
                disposition.lane.is_some(),
                expected_lane,
                "{name}: {}",
                disposition.summary(),
            );
        }
    }
    assert!(checked > 500, "the invariant must be checked against the whole corpus");
}

/// Every `Delivered` disposition carries the label of the rule it emitted, and every
/// `Declined` one carries a non-empty reason.
///
/// A disposition with an empty `detail` is silence wearing a label — the exact thing this
/// mechanism replaced — so it is rejected here rather than being allowed to accumulate.
#[test]
fn every_disposition_carries_a_non_empty_detail() {
    let mut checked = 0usize;
    for (name, metadata) in production_languages() {
        for disposition in metadata.lowering_dispositions() {
            checked += 1;
            assert!(
                !disposition.detail.trim().is_empty(),
                "{name}: {} has an empty detail",
                disposition.qualified_construct(),
            );
            if disposition.outcome == LoweringOutcomeKind::Delivered {
                assert!(
                    disposition.detail.starts_with(name),
                    "{name}: a Delivered disposition's detail is the emitted rule label, which \
                     is language-qualified; got {:?}",
                    disposition.detail,
                );
            }
        }
    }
    assert!(checked > 500);
}

/// The defaulted trait method keeps hand-written `LanguageMetadata` impls valid.
///
/// The inventory is additive: a metadata implementation that predates it — or one written by
/// hand outside the macro — answers with the empty slice instead of failing to compile.
#[test]
fn hand_written_metadata_impls_keep_compiling_against_the_default() {
    struct HandWritten;
    impl LanguageMetadata for HandWritten {
        fn name(&self) -> &'static str {
            "HandWritten"
        }
        fn types(&self) -> &'static [mettail_runtime::TypeDef] {
            &[]
        }
        fn terms(&self) -> &'static [mettail_runtime::TermDef] {
            &[]
        }
        fn equations(&self) -> &'static [mettail_runtime::EquationDef] {
            &[]
        }
        fn rewrites(&self) -> &'static [mettail_runtime::RewriteDef] {
            &[]
        }
    }

    let empty: &[LoweringDispositionDef] = HandWritten.lowering_dispositions();
    assert!(empty.is_empty());
    assert!(HandWritten.declined_lowerings().is_empty());
    assert!(HandWritten.generator_bug_lowerings().is_empty());
}
