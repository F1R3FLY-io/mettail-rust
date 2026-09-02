//! (A4) **The token-text leaf is LABELLED, INVERTIBLE and FOLD-READABLE** — the red proofs.
//!
//! # What was actually missing, measured before the change
//!
//! It was NOT the bytes. `typed_lowering`'s `opaque_leaf_typed` emitted
//! `FieldOpaque(format!("{:?}", payload))`, and for a token-text field the payload IS the
//! `String` — so the leaf was already `FieldOpaque("\"nth\"")`, and `op_enum`'s
//! `SemanticHash::write_content` already framed those bytes into the e-graph content key.
//! `l.foo()` and `l.bar()` were ALREADY distinct e-classes.
//!
//! Two things were missing:
//!
//! 1. a **label** — `FieldOpaque` is shared with builtin scalars, `Vec` payloads, predicate
//!    slots and guest bodies, so provenance was unrecoverable; and
//! 2. an **inverse** — blocked by ONE over-broad predicate. `reconstruct`'s
//!    `is_plain_category_field` answered `bool`, so its caller could only `continue` the
//!    WHOLE variant, and a constructor with a token-text field fell through to `_ => None`.
//!    **The refusal was structural, not informational.**
//!
//! # The shape of every assertion here
//!
//! Each test names the MUTATION it must go red under and carries a CONTROL produced by the
//! same walk over the same language ([`token_text_leaf_demo`]), so "the property holds"
//! cannot be confused with "nothing ran".
//!
//! ⚠ **Everything except [`a4_parsed_ident_folds_on_the_name`] is proven at the DERIVATION
//! level, on terms this file constructs itself.** That is deliberate: the capture path
//! (task #131) is still under repair and may deliver an empty string for a while, and A's
//! value does not depend on it — A removes a structural refusal in the derivation and closes
//! two silent degradations (rho-native reflection falling closed to σ-replay, and `term_gen`
//! dropping the ident-bearing constructor). None of that needs a working capture.
//!
//! ⚠ [`a4_parsed_ident_folds_on_the_name`] is the ONE end-to-end assertion that does need a
//! captured string. It is written honestly and left to fail for the right reason until #131
//! lands; when it lands it must go green **with no edit to this file**. If it needs an edit
//! at that point, A was not actually proven.
//!
//! ⚠ `mettail_runtime::clear_var_cache()` is called by every test that parses. `cargo test`
//! shares one process across tests while `cargo nextest` forks per test, so a test that
//! relies on another having cleared the cache passes under one harness and fails under the
//! other. Every test here is self-sufficient.

#![cfg(feature = "dovetail-codegen")]
#![allow(non_local_definitions)]

use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

use mettail_runtime::{
    Language, LoweredConstructKind, LoweringDispositionDef, RuntimeDovetailRunReport,
};

#[path = "definitions/token_text_leaf_demo.rs"]
mod token_text_leaf_demo;

use token_text_leaf_demo::{Proc, TokenTextLeafDemoLanguage, TokenTextLeafDemoTerm};

// ─────────────────────────────────────────────────────────────────────────────
// Shared helpers
// ─────────────────────────────────────────────────────────────────────────────

/// Reduce `term` through the generated typed Dovetail path — the production `exec` reducer.
/// The depth/budget are the same ones `dovetail_codegen_report.rs` uses for its scalar fold.
fn reduce(term: &Proc) -> RuntimeDovetailRunReport {
    // `Proc` is the AST enum; `mettail_runtime::Term` is implemented on the generated
    // WRAPPER, which is the only `&dyn Term` the report compiler accepts.
    let wrapped = TokenTextLeafDemoTerm(term.clone());
    TokenTextLeafDemoLanguage::dovetail_report_for(&wrapped, 8, 1_024)
        .expect("the generated typed Dovetail report compiler must run")
}

/// Every `op_display` the report recorded — the op-enum `Display` projection of each e-class
/// the lowering produced. This is how a spine leaf's IDENTITY becomes observable from a test:
/// `FieldTokenText` renders `<field-token-text>("…")`, `FieldOpaque` renders
/// `<field-opaque>("…")`, and the two are exactly the label the change adds.
fn op_displays(report: &RuntimeDovetailRunReport) -> Vec<String> {
    report.terms.iter().map(|t| t.op_display.clone()).collect()
}

fn dispositions() -> Vec<LoweringDispositionDef> {
    TokenTextLeafDemoLanguage
        .metadata()
        .lowering_dispositions()
        .to_vec()
}

/// A one-line rendering of the whole inventory, so a failure is diagnosable from the log
/// rather than only reproducible by hand.
fn render(inventory: &[LoweringDispositionDef]) -> String {
    inventory
        .iter()
        .map(|d| {
            format!(
                "\n    {:8} {:10} {:18} {}",
                d.construct_kind.noun(),
                d.construct,
                d.outcome.as_str(),
                d.detail,
            )
        })
        .collect()
}

fn hash_of(t: &Proc) -> u64 {
    let mut s = DefaultHasher::new();
    t.hash(&mut s);
    s.finish()
}

// ─────────────────────────────────────────────────────────────────────────────
// A-1 — the leaf is LABELLED, and the label is per-KIND
// ─────────────────────────────────────────────────────────────────────────────

/// **A-1.** Lowering a term with an `m:Ident` field produces an e-node carrying the
/// `FieldTokenText` op — observable as its `Display` projection `<field-token-text>`.
///
/// ★ MUTATION: reverting `typed_lowering`'s token-text branch to `opaque_leaf_typed` puts the
/// leaf back under `<field-opaque>` and this goes red.
///
/// ★ CONTROL, in the SAME language and the SAME lowering walk: a `GuestBody` field
/// (`Guest`, an `Arc<FltNode>` from a `*flt(…)` capture) must STILL lower to
/// `<field-opaque>`. That is what proves the split is per-KIND rather than a blanket
/// promotion of every opaque leaf — a blanket change would claim an inverse for a payload
/// that has none.
#[test]
fn a1_token_text_lowers_to_its_own_labelled_leaf() {
    let named = Proc::Named("abc".to_string());
    let displays = op_displays(&reduce(&named));
    assert!(
        displays.iter().any(|d| d.contains("<field-token-text>")),
        "an `m:Ident` field must lower to the LABELLED `FieldTokenText` leaf; op_displays: \
         {displays:#?}",
    );
    assert!(
        !displays.iter().any(|d| d.contains("<field-opaque>")),
        "an `m:Ident` field must NOT lower to the shared, unlabelled `FieldOpaque` leaf; \
         op_displays: {displays:#?}",
    );
}

/// **A-1 CONTROL.** A `GuestBody` capture keeps the lossy `FieldOpaque` leaf.
///
/// If this ever reports `<field-token-text>`, the change stopped discriminating by KIND and
/// started claiming a lossless inverse for `Arc<FltNode>`, which does not exist.
#[test]
fn a1_control_guest_body_still_lowers_to_the_opaque_leaf() {
    let guest = Proc::Guest(std::sync::Arc::new(mettail_runtime::FltNode::new(
        "g".to_string(),
        String::new(),
        Vec::new(),
        0,
    )));
    let displays = op_displays(&reduce(&guest));
    assert!(
        displays.iter().any(|d| d.contains("<field-opaque>")),
        "a `*flt(…)` guest-body field must STILL lower to the lossy `FieldOpaque` leaf — the \
         split is per-KIND; op_displays: {displays:#?}",
    );
    assert!(
        !displays.iter().any(|d| d.contains("<field-token-text>")),
        "a guest-body payload has no lossless `Debug` inverse, so it must not be promoted to \
         the invertible leaf; op_displays: {displays:#?}",
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// A-2 — the leaf is INVERTIBLE, with a non-empty string this file constructs
// ─────────────────────────────────────────────────────────────────────────────

/// **A-2.** The round trip `add → Extractor::kth → build_token_text_d` returns the captured
/// text, with a NON-EMPTY string constructed here rather than parsed.
///
/// The inverse is a private nested fn of the generated report compiler, so it is observed
/// through the only thing that can call it: the FOLD BODY. `Named`'s body dispatches on
/// `m.as_str()`, so `Named("zero")` reduces to `Nil` and `Named("other")` does not. A fold
/// that received the wrong string — or `None`, deferring forever — cannot produce that pair
/// of outcomes.
///
/// ★ MUTATION: making `build_token_text_d` return `None` defers the fold, the root stays
/// `Named`, and the first assertion goes red.
///
/// ★ CONTROL: the same round trip for a `Proc` CHILD via `build_proc_d` — `Wrap(Nil)` folds
/// through its object reconstructor. Without it, "the text round-tripped" could not be told
/// apart from "the fold machinery ran at all".
#[test]
fn a2_token_text_round_trips_through_the_derivation() {
    let zero = reduce(&Proc::Named("zero".to_string()));
    assert!(
        zero.rule_firings.iter().any(|f| {
            f.label.as_deref() == Some("TokenTextLeafDemo::fold::Proc_Named") && f.count >= 1
        }),
        "the `Named` fold must FIRE — a deferred fold means the text never reached the body: \
         {zero:#?}",
    );
    assert!(
        zero.terms
            .iter()
            .any(|t| t.is_root && t.op_display == "TokenTextLeafDemo::Proc::Nil"),
        "`Named(\"zero\")` must reduce to `Nil`, which happens ONLY if the body received the \
         exact string \"zero\": {zero:#?}",
    );

    // The discriminating half: a DIFFERENT non-empty name must not take the "zero" branch.
    let other = reduce(&Proc::Named("other".to_string()));
    assert!(
        !other
            .terms
            .iter()
            .any(|t| t.is_root && t.op_display == "TokenTextLeafDemo::Proc::Nil"),
        "`Named(\"other\")` must NOT reduce to `Nil`; if it did, the body is dispatching on \
         something other than the captured text: {other:#?}",
    );
}

/// **A-2 CONTROL.** An object child round-trips through `build_proc_d` on the same language.
#[test]
fn a2_control_object_child_round_trips_through_its_own_reconstructor() {
    let report = reduce(&Proc::Wrap(std::sync::Arc::new(Proc::Nil)));
    assert!(
        report.rule_firings.iter().any(|f| {
            f.label.as_deref() == Some("TokenTextLeafDemo::fold::Proc_Wrap") && f.count >= 1
        }),
        "the object-only `Wrap` fold must fire, proving the fold machinery runs on this \
         language independently of any token-text change: {report:#?}",
    );
    assert!(
        report
            .terms
            .iter()
            .any(|t| t.is_root && t.op_display.contains("Proc::Named")),
        "`Wrap(Nil)` must reduce to the constructor its body names, which happens only if \
         `build_proc_d` handed the body the `Nil` child: {report:#?}",
    );
}

/// **A-2, the MIXED variant.** `Call(recv, m)` carries an `Arc<Proc>` beside a bare `String`,
/// so its reconstruction needs a PER-FIELD builder: `Arc::new(build_proc_d(child0)?)` for the
/// category child and the UNWRAPPED `build_token_text_d(child1)?` for the text.
///
/// This is the assertion that distinguishes a per-FIELD fix from a per-VARIANT one: the old
/// predicate could only refuse the whole variant the moment ANY field was a leaf.
#[test]
fn a2_mixed_variant_reconstructs_category_child_and_text_together() {
    let call = Proc::Call(std::sync::Arc::new(Proc::Nil), "nth".to_string());
    let report = reduce(&call);
    assert!(
        report.rule_firings.iter().any(|f| {
            f.label.as_deref() == Some("TokenTextLeafDemo::fold::Proc_Call") && f.count >= 1
        }),
        "the mixed `Call` fold must fire — it fires only if BOTH the `Arc<Proc>` child and \
         the bare `String` reconstructed: {report:#?}",
    );
    // ★ The strongest single assertion in this file. `Call`'s body takes its `nil-dot-nth`
    // branch ONLY when the reconstructed pair is exactly `(Nil, "nth")` — the category child
    // through `build_proc_d` (wrapped in `Arc`) and the text through `build_token_text_d`
    // (UNWRAPPED). A per-VARIANT invertibility test could not produce this at all: the old
    // predicate refused the whole variant the moment any field was a leaf.
    assert!(
        report
            .terms
            .iter()
            .any(|t| t.is_root && t.op_display.contains("Proc::Named")),
        "`Call(Nil, \"nth\")` must fold to the constructor its body names for exactly that \
         pair: {report:#?}",
    );
    let displays = op_displays(&report);
    assert!(
        displays.iter().any(|d| d.contains("<field-token-text>")),
        "the mixed variant's text field must still be the labelled leaf: {displays:#?}",
    );
}

/// Exact optional token text must distinguish `Some(text)` from indexed
/// absence and deliver both cases to the fold body without reparsing text.
#[test]
fn a2_optional_token_text_round_trips_present_and_absent() {
    for (term, expected) in [
        (Proc::MaybeNamed(Some("zero".to_string())), "optional-token-present"),
        (Proc::MaybeNamed(None), "optional-token-absent"),
    ] {
        let probe = Proc::Probe(std::sync::Arc::new(term.clone()));
        let report = reduce(&probe);
        assert!(
            report.rule_firings.iter().any(|f| {
                f.label.as_deref() == Some("TokenTextLeafDemo::fold::Proc_Probe") && f.count >= 1
            }),
            "the inverse-probe fold must fire for {term:?}: {report:#?}",
        );
        assert!(
            report.terms.iter().any(|t| t.op_display.contains(expected)),
            "the optional-token fold must preserve the present/absent case `{expected}`: \
             {report:#?}",
        );
    }
}

/// Exact optional category children use the ordinary child derivation when
/// present and the indexed absence carrier when omitted.
#[test]
fn a2_optional_category_child_round_trips_present_and_absent() {
    for (term, expected) in [
        (Proc::MaybeProc(Some(std::sync::Arc::new(Proc::Nil))), "optional-child-present"),
        (Proc::MaybeProc(None), "optional-child-absent"),
    ] {
        let probe = Proc::Probe(std::sync::Arc::new(term.clone()));
        let report = reduce(&probe);
        assert!(
            report.rule_firings.iter().any(|f| {
                f.label.as_deref() == Some("TokenTextLeafDemo::fold::Proc_Probe") && f.count >= 1
            }),
            "the inverse-probe fold must fire for {term:?}: {report:#?}",
        );
        assert!(
            report.terms.iter().any(|t| t.op_display.contains(expected)),
            "the optional-child fold must preserve the present/absent case `{expected}`: \
             {report:#?}",
        );
    }
}

/// A required category child followed by an optional category child must be
/// reconstructed in field order. In particular, absence is a deferred PDA
/// action rather than an eager value-stack mutation that can overtake `head`.
#[test]
fn a2_mixed_required_and_optional_children_preserve_field_order() {
    for (term, expected) in [
        (
            Proc::MixedMaybe(std::sync::Arc::new(Proc::Nil), None),
            "mixed-required-then-absent",
        ),
        (
            Proc::MixedMaybe(std::sync::Arc::new(Proc::Nil), Some(std::sync::Arc::new(Proc::Nil))),
            "mixed-required-then-present",
        ),
    ] {
        let probe = Proc::Probe(std::sync::Arc::new(term.clone()));
        let report = reduce(&probe);
        assert!(
            report.rule_firings.iter().any(|f| {
                f.label.as_deref() == Some("TokenTextLeafDemo::fold::Proc_Probe") && f.count >= 1
            }),
            "the inverse-probe fold must fire for {term:?}: {report:#?}",
        );
        assert!(
            report.terms.iter().any(|t| t.op_display.contains(expected)),
            "mixed required/optional reconstruction must preserve `{expected}`: {report:#?}",
        );
    }
}

/// Exact optional ordered sequences preserve the Option boundary and the
/// element order carried by the labelled sequence leaf.
#[test]
fn a2_optional_ordered_sequence_round_trips_present_and_absent() {
    for (term, expected) in [
        (Proc::MaybeMany(Some(vec![Proc::Nil])), "optional-sequence-present"),
        (Proc::MaybeMany(None), "optional-sequence-absent"),
    ] {
        let probe = Proc::Probe(std::sync::Arc::new(term.clone()));
        let report = reduce(&probe);
        assert!(
            report.rule_firings.iter().any(|f| {
                f.label.as_deref() == Some("TokenTextLeafDemo::fold::Proc_Probe") && f.count >= 1
            }),
            "the inverse-probe fold must fire for {term:?}: {report:#?}",
        );
        assert!(
            report.terms.iter().any(|t| t.op_display.contains(expected)),
            "the optional sequence inverse must preserve `{expected}`: {report:#?}",
        );
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// A-3 — the fold gate ADMITS `Ident`, and still declines what it should
// ─────────────────────────────────────────────────────────────────────────────

/// **A-3.** The lowering-disposition inventory has ZERO `Declined` entries mentioning `Ident`.
///
/// ★ MUTATION: restoring the `ty.is_ident_text()` refusal in `collect_fold_rules` puts
/// `Named` and `Call` back in the inventory as `Declined`, and this goes red.
///
/// ★ CONTROL, so it cannot pass by the gate having been disabled: `Guarded` carries a
/// `?g:Guard` slot, which is genuinely unsupported, and must STILL be `Declined` with
/// `describe_term_param`'s exact wording.
#[test]
fn a3_no_fold_is_declined_for_being_an_ident() {
    let inventory = dispositions();
    assert!(
        !inventory.is_empty(),
        "an empty inventory would make every assertion here vacuous",
    );
    let ident_declinations: Vec<&LoweringDispositionDef> = inventory
        .iter()
        .filter(|d| d.is_declined() && d.detail.contains("Ident"))
        .collect();
    assert!(
        ident_declinations.is_empty(),
        "no construct may be declined for carrying identifier text; found \
         {ident_declinations:#?}{}",
        render(&inventory),
    );

    // Positive half: the two ident-bearing folds are DELIVERED, not merely un-declined.
    for label in ["Named", "Call"] {
        let recorded: Vec<&LoweringDispositionDef> = inventory
            .iter()
            .filter(|d| d.construct_kind == LoweredConstructKind::Fold && d.construct == label)
            .collect();
        assert_eq!(
            recorded.len(),
            1,
            "fold `{label}` must have exactly one disposition{}",
            render(&inventory),
        );
        assert!(
            !recorded[0].is_declined(),
            "fold `{label}` carries an `m:Ident` param and must now be LOWERED{}",
            render(&inventory),
        );
    }
}

/// **A-3 CONTROL.** A genuinely unsupported parameter — a BINDER ABSTRACTION — still
/// declines, in `describe_term_param`'s exact wording, so A-3 cannot pass by disabling the
/// gate. (The brief names a `?g:Guard` slot; see the fixture's comment on `Bind` for the
/// pre-existing, unrelated `wpda_codegen` guard field-order defect that rules it out here.)
#[test]
fn a3_control_unsupported_param_still_declines_with_its_exact_wording() {
    let inventory = dispositions();
    let bind: Vec<&LoweringDispositionDef> = inventory
        .iter()
        .filter(|d| d.construct_kind == LoweredConstructKind::Fold && d.construct == "Bind")
        .collect();
    assert_eq!(
        bind.len(),
        1,
        "fold `Bind` must have exactly one disposition{}",
        render(&inventory),
    );
    assert!(
        bind[0].is_declined(),
        "a binder-abstraction fold param is genuinely unsupported and must STILL decline{}",
        render(&inventory),
    );
    // `describe_term_param`'s wording for a guard slot, verbatim.
    assert!(
        bind[0].detail.contains("(a binder abstraction)"),
        "the declination must name the offender in `describe_term_param`'s wording, so the \
         gate is demonstrably still reading parameter shapes{}",
        render(&inventory),
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// A-4 — end to end, including the surface
// ─────────────────────────────────────────────────────────────────────────────

/// **A-4, derivation half.** A term CONSTRUCTED here folds on its name.
///
/// This is the whole of A-4 that does not depend on the parser's capture path: build
/// `Named("zero")` and `Named("other")` directly, reduce both, and require the two outcomes
/// to differ. It is green today.
#[test]
fn a4_constructed_ident_folds_on_the_name() {
    let zero_root = reduce(&Proc::Named("zero".to_string()))
        .terms
        .iter()
        .find(|t| t.is_root)
        .map(|t| t.op_display.clone())
        .expect("the report must record a root term");
    let other_root = reduce(&Proc::Named("other".to_string()))
        .terms
        .iter()
        .find(|t| t.is_root)
        .map(|t| t.op_display.clone())
        .expect("the report must record a root term");
    assert_eq!(
        zero_root, "TokenTextLeafDemo::Proc::Nil",
        "`Named(\"zero\")` must normalize to `Nil`",
    );
    assert_ne!(
        other_root, "TokenTextLeafDemo::Proc::Nil",
        "`Named(\"other\")` must NOT normalize to `Nil` — otherwise the fold is not reading \
         the name",
    );
}

/// **A-4, surface half. ⚠ EXPECTED TO FAIL UNTIL TASK #131 LANDS, and left failing on
/// purpose.**
///
/// The parser's `m:Ident` capture currently does not deliver the matched text into the action
/// (`ConsumeIdentAndReplace` is the BINDER-scope op: it interns the name into the binder scope
/// and deliberately does not fold it onto the args stack, because for a binder "the captured
/// name lives in the binder scope, not the args stack". A method name has no scope, so the
/// name is interned and dropped). That is a defect in the CAPTURE, not in this capability:
/// A's fold would faithfully deliver whatever the capture hands it.
///
/// ⚠ DO NOT weaken, `#[ignore]`, or delete this. When #131 lands it must go green with NO
/// edit to this file; if it needs one, A was not actually proven.
#[test]
fn a4_parsed_ident_folds_on_the_name() {
    // Leg 1 — THE CAPTURE (task #131's property): the surface text reaches the AST field.
    mettail_runtime::clear_var_cache();
    let zero = Proc::parse("tag zero").expect("`tag zero` must parse");
    assert_eq!(
        zero,
        Proc::Named("zero".to_string()),
        "the `m:Ident` capture must deliver the matched text into the AST field; a \
         `Named(\"\")` here is the capture defect (task #131), not a fold defect",
    );

    // Leg 2 — THE FOLD over the parsed term. `parse` parses; folds run in the reducer, so
    // the end-to-end claim is the COMPOSITION, not a property of `parse` alone.
    let root = reduce(&zero)
        .terms
        .iter()
        .find(|t| t.is_root)
        .map(|t| t.op_display.clone())
        .expect("the report must record a root term");
    assert_eq!(
        root, "TokenTextLeafDemo::Proc::Nil",
        "a PARSED `tag zero` must normalize to `Nil` — surface → capture → derivation → fold",
    );

    mettail_runtime::clear_var_cache();
    let other = Proc::parse("tag other").expect("`tag other` must parse");
    assert_eq!(other, Proc::Named("other".to_string()), "`tag other` must keep its name");
}

// ─────────────────────────────────────────────────────────────────────────────
// A-5 — the name is DATA, and INERTNESS is unchanged
// ─────────────────────────────────────────────────────────────────────────────

/// **A-5.** Distinct names are distinct terms under `Eq`, `Hash` and `Ord`.
///
/// ★ MUTATION: routing `Ident` to `NonTerminalKind::Var` in `term_ops/subst.rs` would make
/// the field an `OrdVar`, and this file would not COMPILE — `Proc::Named(String)` type-checks
/// only against the `String` carrier. That is a sharper guard than any runtime check, because
/// `OrdVar` also carries a name and a value-level comparison could pass against the wrong
/// carrier.
#[test]
fn a5_distinct_names_are_distinct_terms_under_eq_hash_ord() {
    let foo = Proc::Named("foo".to_string());
    let bar = Proc::Named("bar".to_string());
    assert_ne!(foo, bar, "terms differing only in the ident field must not be equal");
    assert_ne!(hash_of(&foo), hash_of(&bar), "distinct names must hash apart");
    assert_ne!(foo.cmp(&bar), std::cmp::Ordering::Equal, "distinct names must order apart");
}

/// **A-5.** A binder in scope does NOT capture a method name.
///
/// `Bind` binds a `Proc` variable; the ident field of the `Named` inside its body is a
/// `String`, which no substitution can see into. Were the field an `OrdVar`, `subst`'s
/// canonicalisation of `Var::Free` under unify would rewrite it and the body would change.
///
/// ★ CONTROL: the same walk over the same binder must leave a `Named` with a DIFFERENT name
/// equally untouched — so "nothing changed" is not an artifact of the term being trivial.
#[test]
fn a5_a_binder_in_scope_does_not_capture_an_ident_field() {
    for name in ["x", "foo", "nth"] {
        let body = Proc::Named(name.to_string());
        let binder = mettail_runtime::Binder(mettail_runtime::FreeVar::fresh_named(name));
        let scope = mettail_runtime::Scope::new(binder, std::sync::Arc::new(body.clone()));
        let bound = Proc::Bind(scope);
        let normalized = bound.normalize();
        let rendered = format!("{normalized:?}");
        assert!(
            rendered.contains(name),
            "binding a variable spelled {name:?} must leave the ident field {name:?} intact \
             — an ident is DATA, not a variable; got {rendered}",
        );
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// A-8 — the ident-bearing constructor is generated
// ─────────────────────────────────────────────────────────────────────────────

/// **A-8.** Over N seeds, the ident-bearing constructor appears in random generation.
///
/// ★ MUTATION: restoring `quote! {}` for a non-lang-type argument in `term_gen/random.rs`
/// drops every ident-bearing constructor from generation and this goes red.
///
/// ★ CONTROL: a `Proc`-only constructor on the SAME language must also appear — otherwise
/// "the ident constructor is missing" is indistinguishable from "the sampler never ran".
#[test]
fn a8_ident_bearing_constructor_appears_in_random_generation() {
    const SEEDS: u64 = 256;
    let vars: Vec<String> = vec!["a".to_string()];

    let mut saw_ident_bearing = false;
    let mut saw_object_only = false;
    let mut seen_names: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();

    for seed in 0..SEEDS {
        for depth in 0..3usize {
            let term = Proc::generate_random_at_depth_with_seed(&vars, depth, 2, seed);
            collect_shapes(&term, &mut saw_ident_bearing, &mut saw_object_only, &mut seen_names);
        }
    }

    assert!(
        saw_object_only,
        "CONTROL: a `Proc`-only constructor must be generated, otherwise this test cannot \
         tell a missing ident constructor from a sampler that never ran",
    );
    assert!(
        saw_ident_bearing,
        "an ident-bearing constructor must appear in random generation over {SEEDS} seeds; \
         before A it was dropped silently because `is_lang_type(Ident)` is false",
    );
    assert!(
        seen_names.iter().all(|n| !n.is_empty()),
        "no generated identifier may be empty — the empty string is not an identifier under \
         any lexer pattern; got {seen_names:?}",
    );
}

fn collect_shapes(
    term: &Proc,
    saw_ident_bearing: &mut bool,
    saw_object_only: &mut bool,
    seen_names: &mut std::collections::BTreeSet<String>,
) {
    match term {
        Proc::Named(name) => {
            *saw_ident_bearing = true;
            seen_names.insert(name.clone());
        },
        Proc::Call(recv, name) => {
            *saw_ident_bearing = true;
            seen_names.insert(name.clone());
            collect_shapes(recv, saw_ident_bearing, saw_object_only, seen_names);
        },
        Proc::Wrap(inner) => {
            *saw_object_only = true;
            collect_shapes(inner, saw_ident_bearing, saw_object_only, seen_names);
        },
        // Everything else — `Nil`, the guest-body leaf, the binder, and the AUTO-INJECTED
        // `PVar` / `LamProc` / `MLamProc` / `ApplyProc` / `MApplyProc` variants — carries no
        // shape this test discriminates on. The catch-all is over variants the GRAMMAR did
        // not declare, so it cannot hide a subject: `Named` and `Call` are matched above by
        // name, and adding a declared constructor to the fixture without teaching this
        // collector about it would leave that constructor unobserved, not silently accepted.
        _ => {},
    }
}

/// **A-8, exhaustive peer.** The bounded-exhaustive enumerator also reaches the ident-bearing
/// constructor, over the fixed spec-derived sample set.
#[test]
fn a8_ident_bearing_constructor_appears_in_exhaustive_generation() {
    let terms = Proc::generate_terms(&["a".to_string()], 2, 2);
    let mut saw_ident_bearing = false;
    let mut saw_object_only = false;
    let mut seen_names: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();
    for term in &terms {
        collect_shapes(term, &mut saw_ident_bearing, &mut saw_object_only, &mut seen_names);
    }
    assert!(
        saw_object_only,
        "CONTROL: a `Proc`-only constructor must be enumerated, otherwise a missing ident \
         constructor is indistinguishable from an enumerator that produced nothing",
    );
    assert!(
        saw_ident_bearing,
        "an ident-bearing constructor must be enumerated; enumerated {} terms",
        terms.len(),
    );
    assert!(
        seen_names.iter().all(|n| !n.is_empty()),
        "no enumerated identifier may be empty; got {seen_names:?}",
    );
}
