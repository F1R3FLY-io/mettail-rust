//! ★★ Task #94 — THE THREE REDs for the lowering-disposition inventory.
//!
//! # What was broken
//!
//! Generated runtime lowering answered with a `Vec<TokenStream>` of rules plus a
//! `Vec<String>` of excuses, and the excuse vector was bound to `_` at four of its five
//! consumption sites. Three genuinely different outcomes therefore looked identical to every
//! downstream reader, **including every test**:
//!
//! | outcome | what the reader saw |
//! |---|---|
//! | lowered here | a rule in the emitted vector |
//! | lowered by another lane | no rule, no excuse |
//! | lowered **nowhere** | no rule, an excuse nobody read |
//!
//! The last two rows are byte-identical. That is why 36 constructs across six production
//! languages stopped being lowered without a single test noticing, and — symmetrically — why
//! the obvious fix of "treat silence as an error" was unavailable: for the bundled Rholang,
//! 400 of 461 declared rewrites are silent *and correct*.
//!
//! # The three REDs
//!
//! Each is a purpose-built grammar plus an assertion on
//! [`mettail_runtime::LanguageMetadata::lowering_dispositions`], the inventory the macro now
//! emits into every generated language's metadata.
//!
//! | RED | class | what it pins |
//! |---|---|---|
//! | **A** | D4 — recorded, then discarded by the consumer | a `Lambda`-carrying equation on the `EGraph<String>` + binder-float path is `Declined`, naming the equation **and** the refusal |
//! | **B** | D1–D3 — the typed path, which discarded its record three times | a `Lambda` equation, a freshness-premised equation, and (until Task #101 repaired it) a `Vec(T)`-parameter fold each carry a RECORD, on a language where none of the three produced any diagnostic before |
//! | **C** | ★ the anti-vacuity check on the fix | a congruence rewrite is `DeliveredElsewhere { EGraphCongruenceClosure }` and **not** `Declined` — the property that stops 400 correctly-elsewhere-handled rewrites becoming false positives |
//!
//! Every RED carries a **positive control**: a construct on the same language, produced by the
//! same walk, with the opposite disposition. Without one, an assertion that something is
//! `Declined` cannot be told apart from a walk that inspected nothing at all.

#![allow(non_local_definitions)]

use mettail_runtime::{
    LanguageMetadata, LoweredConstructKind, LoweredConstructOrigin, LoweringDispositionDef,
    LoweringLane, LoweringOutcomeKind,
};

#[path = "definitions/binder_law_demo.rs"]
mod binder_law_demo;

#[path = "definitions/typed_drop_demo.rs"]
mod typed_drop_demo;

#[path = "definitions/congruence_lane_demo.rs"]
mod congruence_lane_demo;

// ─────────────────────────────────────────────────────────────────────────────
// Shared helpers
// ─────────────────────────────────────────────────────────────────────────────

/// Every disposition recorded for `construct`, of `kind`.
fn dispositions_for<'a>(
    inventory: &'a [LoweringDispositionDef],
    kind: LoweredConstructKind,
    construct: &str,
) -> Vec<&'a LoweringDispositionDef> {
    inventory
        .iter()
        .filter(|disposition| {
            disposition.construct_kind == kind && disposition.construct == construct
        })
        .collect()
}

/// A one-line rendering of a whole inventory, for assertion messages. A failure that prints
/// only "expected Declined" is a failure the reader has to reproduce by hand; one that prints
/// the entire record is one they can diagnose from the log.
fn render(inventory: &[LoweringDispositionDef]) -> String {
    inventory
        .iter()
        .map(|disposition| {
            format!(
                "\n    {:8} {:16} {:18} {:12} {}",
                disposition.construct_kind.noun(),
                disposition.construct,
                disposition.outcome.as_str(),
                disposition.origin.as_str(),
                match disposition.lane {
                    Some(lane) => lane.as_str().to_string(),
                    None => disposition.detail.to_string(),
                },
            )
        })
        .collect()
}

/// Assert that `construct` has at least one `Declined` disposition whose reason contains
/// `reason_fragment`, and return those dispositions.
fn assert_declined_because<'a>(
    inventory: &'a [LoweringDispositionDef],
    kind: LoweredConstructKind,
    construct: &str,
    reason_fragment: &str,
) -> Vec<&'a LoweringDispositionDef> {
    let recorded = dispositions_for(inventory, kind, construct);
    assert!(
        !recorded.is_empty(),
        "the inventory has NO entry for {} `{construct}` at all — a construct with no \
         disposition is the silent drop this record exists to make impossible.{}",
        kind.noun(),
        render(inventory),
    );
    let declined: Vec<&LoweringDispositionDef> = recorded
        .iter()
        .copied()
        .filter(|d| d.is_declined())
        .collect();
    assert!(
        !declined.is_empty(),
        "{} `{construct}` is recorded but NOT as Declined; it is lowered nowhere, so anything \
         else is a false claim of coverage.{}",
        kind.noun(),
        render(inventory),
    );
    assert!(
        declined.iter().any(|d| d.detail.contains(reason_fragment)),
        "{} `{construct}` is Declined, but no recorded reason contains {reason_fragment:?} — \
         the inventory must say WHY lowering refused it, not merely that it did.{}",
        kind.noun(),
        render(inventory),
    );
    declined
}

// ─────────────────────────────────────────────────────────────────────────────
// RED A — class D4: the diagnostic that reached nothing
// ─────────────────────────────────────────────────────────────────────────────

/// ★ RED A. `BinderLawDemo::PairComm` carries a `Lambda` metapattern on both sides, so
/// `pattern_to_dovetail` refuses both orientations and the law is lowered NOWHERE.
///
/// Before the disposition mechanism, that refusal was computed into a `Vec<String>` and then
/// discarded by its consumer: this language satisfies all three conditions of
/// `should_emit_binder_congruence` (a surface single binder `Nu` over the primary category,
/// non-empty equations, no `RhoNativeJoin` obligation), so the generated report's `native_gate`
/// — the only place the `EGraph<String>` path ever embedded the declination list — is emitted as
/// an empty token stream. The generated source contained neither the refusal string nor any
/// `unsupported` array; the runtime `Err` that would have carried it is not emitted either.
/// The construct simply stopped being part of the language's semantics, silently.
#[test]
fn red_a_binder_equation_declination_is_recorded_with_its_reason() {
    let inventory = binder_law_demo::BinderLawDemoMetadata.lowering_dispositions();

    let declined = assert_declined_because(
        inventory,
        LoweredConstructKind::Equation,
        "PairComm",
        "lambda patterns require binder lowering",
    );

    // BOTH orientations are refused — the forward one on its LHS, the reverse one on the
    // pattern the reverse rule takes as ITS left-hand side. An equation half-lowered is a
    // materially different fact from one lowered nowhere, and the record distinguishes them.
    assert_eq!(
        declined.len(),
        2,
        "both orientations of `PairComm` are refused, so both must be recorded.{}",
        render(inventory),
    );
    assert!(
        declined.iter().any(|d| d.detail.starts_with("LHS:")),
        "the forward orientation's refusal must be recorded.{}",
        render(inventory),
    );
    assert!(
        declined
            .iter()
            .any(|d| d.detail.starts_with("reverse LHS:")),
        "the reverse orientation's refusal must be recorded.{}",
        render(inventory),
    );

    // The author wrote this equation; the generator did not inject it.
    for disposition in &declined {
        assert_eq!(disposition.origin, LoweredConstructOrigin::Declared);
        assert!(!disposition.is_generator_bug());
    }

    // ★ POSITIVE CONTROL ON THE ZERO. `declined_lowerings` returning exactly these two proves
    // the walk ran over the whole language and found one declination — not that it inspected
    // nothing. A grammar whose only equation is refused would otherwise be indistinguishable
    // from a grammar the inventory never looked at.
    let all_declined = binder_law_demo::BinderLawDemoMetadata.declined_lowerings();
    assert_eq!(
        all_declined.len(),
        2,
        "BinderLawDemo declines exactly its one equation, in both orientations.{}",
        render(inventory),
    );
    assert!(
        !inventory.is_empty(),
        "an empty inventory would make every assertion above vacuous",
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// RED B — classes D1–D3: the typed path, which discarded its record three times
// ─────────────────────────────────────────────────────────────────────────────

/// ★ RED B. `TypedDropDemo` takes the TYPED path (its `Id` fold has a non-native output
/// category), where all three `rule_block` consumers wrote `let (rules_expr, _unsupported)`.
/// Three constructs are lowered nowhere on that path and, before this change, produced ZERO
/// diagnostics on any lane — not a compile error, not a runtime `Err`, not a line of generated
/// source.
#[test]
fn red_b_typed_path_declinations_are_recorded_on_every_construct_class() {
    let inventory = typed_drop_demo::TypedDropDemoMetadata.lowering_dispositions();

    // (1) The `Lambda`-carrying equation: refused by the structural pattern lowering.
    assert_declined_because(
        inventory,
        LoweredConstructKind::Equation,
        "PairComm",
        "lambda patterns require binder lowering",
    );

    // (2) The freshness-premised equation: `premise_supported` admits only congruence premises,
    //     so this is refused before either orientation is attempted. Exactly ONE record, because
    //     the premise is a property of the equation rather than of an orientation.
    let fresh = assert_declined_because(
        inventory,
        LoweredConstructKind::Equation,
        "FreshSwap",
        "has side conditions",
    );
    assert_eq!(
        fresh.len(),
        1,
        "a premise refusal kills both orientations at once, so it is recorded once.{}",
        render(inventory),
    );

    // (3) ★★ THE FOLD GATE — REPAIRED (Task #101), and this entry INVERTED with it.
    //
    //     `Head`'s `xs` is a `Vec(Term)` parameter. This RED used to assert that the gate's
    //     `if !all_simple { continue }` DROPPED it, with a reason containing "is not a
    //     `Simple`/`Base` typed parameter" and naming `` `xs:Vec(Term)` ``. That refusal was
    //     accurate for the lowering of the day: a fold operand is bound by INVERTING its
    //     lowered derivation child, and a `Vec` field lowered to
    //     `FieldOpaque(format!("{:?}", …))`, which has no inverse.
    //
    //     Task #101 changed the LOWERING, exactly as that refusal said it must: an ordered
    //     collection now lowers to the labelled `FieldSeq<Term>(Vec<Term>)` leaf — the whole
    //     vector VERBATIM — with the total inverse `__mettail_dovetail_build_seq_term_d`. So
    //     `Head` binds like any other fold and is DELIVERED.
    //
    //     The RED is retired by INVERSION rather than deletion: the same construct, on the
    //     same grammar, in the same walk, now carries the opposite disposition and states the
    //     label of the rule it emitted. A regression that re-refuses it turns this red naming
    //     it.
    let head = dispositions_for(inventory, LoweredConstructKind::Fold, "Head");
    assert_eq!(head.len(), 1, "`Head` must have exactly one disposition.{}", render(inventory));
    assert_eq!(
        head[0].outcome,
        LoweringOutcomeKind::Delivered,
        "★ Task #101: a `Vec(T)` fold parameter is lowered, not declined.{}",
        render(inventory),
    );
    assert_eq!(
        head[0].detail,
        "TypedDropDemo::fold::Term_Head",
        "a Delivered disposition carries the label of the rule it emitted.{}",
        render(inventory),
    );

    // ★ POSITIVE CONTROL ON THE FOLD WALK, kept and re-purposed. `Id` is a SCALAR-free object
    // fold on the same language, found by the same traversal. It was the control on "the gate
    // declined `Head`"; it is now the control on "the walk distinguishes folds at all", since
    // both folds being Delivered could otherwise mean the walk stopped inspecting.
    let id = dispositions_for(inventory, LoweredConstructKind::Fold, "Id");
    assert_eq!(id.len(), 1, "`Id` must have exactly one disposition.{}", render(inventory));
    assert_eq!(
        id[0].outcome,
        LoweringOutcomeKind::Delivered,
        "`Id` is lowered by the typed native fold dispatcher.{}",
        render(inventory),
    );
    assert_eq!(
        id[0].detail,
        "TypedDropDemo::fold::Term_Id",
        "a Delivered disposition carries the label of the rule it emitted.{}",
        render(inventory),
    );

    // The declination set is exactly these three records and no others — an assertion on the
    // SET, so a new silent drop on this grammar turns this test red naming the construct.
    // ⚠ `fold Head` left this list under Task #101; the two equation declinations remain,
    // which is what keeps the assertion from being satisfied by an empty walk.
    let declined: Vec<String> = typed_drop_demo::TypedDropDemoMetadata
        .declined_lowerings()
        .iter()
        .map(|d| format!("{} {}", d.construct_kind.noun(), d.construct))
        .collect();
    assert_eq!(
        declined,
        vec![
            "equation PairComm".to_string(),
            "equation PairComm".to_string(),
            "equation FreshSwap".to_string(),
        ],
        "the declination set is pinned; an addition is a new silent drop.{}",
        render(inventory),
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// ★★ RED C — the anti-vacuity check on the fix itself
// ─────────────────────────────────────────────────────────────────────────────

/// ★★ RED C. A congruence rewrite must be `DeliveredElsewhere { EGraphCongruenceClosure }`,
/// **not** `Declined`.
///
/// This is the assertion that keeps the mechanism honest. A disposition record that classified
/// every rule-less outcome as a declination would pass RED A and RED B and be useless: for the
/// bundled Rholang it would report 400 false declinations alongside the 15 real ones, and the
/// golden inventory would be noise. `WrapCong` produces no lowered rule for a reason that is
/// correct — e-graph congruence closure propagates `AToB`'s child-e-class merge through
/// `Wrap(_)` with no rule firing — and the record must say which lane covers it.
#[test]
fn red_c_congruence_rewrite_is_delivered_elsewhere_not_declined() {
    let inventory = congruence_lane_demo::CongruenceLaneDemoMetadata.lowering_dispositions();

    let cong = dispositions_for(inventory, LoweredConstructKind::Rewrite, "WrapCong");
    assert_eq!(
        cong.len(),
        1,
        "`WrapCong` must have exactly one disposition.{}",
        render(inventory),
    );
    let cong = cong[0];

    assert!(
        !cong.is_declined(),
        "★ ANTI-VACUITY FAILURE: `WrapCong` is a congruence rewrite that the e-graph closure \
         covers, and calling it a declination would make 400 of Rholang's 461 rewrites false \
         positives.{}",
        render(inventory),
    );
    assert_eq!(
        cong.outcome,
        LoweringOutcomeKind::DeliveredElsewhere,
        "a congruence rewrite is lowered on another lane, not lowered nowhere.{}",
        render(inventory),
    );
    assert_eq!(
        cong.lane,
        Some(LoweringLane::EGraphCongruenceClosure),
        "the covering lane must be NAMED — `DeliveredElsewhere` with no lane would be silence \
         wearing a label.{}",
        render(inventory),
    );

    // ★ POSITIVE CONTROL. `AToB` is the kernel rewrite whose merge the closure propagates. It
    // IS lowered here, so the walk demonstrably distinguishes the two cases rather than
    // answering `DeliveredElsewhere` for everything.
    let kernel = dispositions_for(inventory, LoweredConstructKind::Rewrite, "AToB");
    assert_eq!(
        kernel.len(),
        1,
        "`AToB` must have exactly one disposition.{}",
        render(inventory)
    );
    assert_eq!(
        kernel[0].outcome,
        LoweringOutcomeKind::Delivered,
        "the kernel rewrite is lowered HERE, as a structural rule.{}",
        render(inventory),
    );
    assert_eq!(
        kernel[0].detail,
        "CongruenceLaneDemo::rewrite::AToB",
        "a Delivered disposition carries the label of the rule it emitted.{}",
        render(inventory),
    );
    assert_eq!(
        kernel[0].lane,
        None,
        "a rule lowered here has no OTHER lane.{}",
        render(inventory)
    );

    // Nothing on this grammar is declined at all, and that zero is positively controlled by the
    // two assertions above: the walk saw both rewrites and gave them different dispositions.
    assert!(
        congruence_lane_demo::CongruenceLaneDemoMetadata
            .declined_lowerings()
            .is_empty(),
        "CongruenceLaneDemo declines nothing.{}",
        render(inventory),
    );
    assert_eq!(
        inventory.len(),
        2,
        "the inventory covers both declared rewrites and nothing else.{}",
        render(inventory),
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// The mechanism's own invariants
// ─────────────────────────────────────────────────────────────────────────────

/// A `DeliveredElsewhere` disposition always names a lane, and no other outcome ever does.
///
/// This is what stops `DeliveredElsewhere` from degenerating back into silence: an unattributed
/// "covered somewhere" claim is exactly the empty `Vec<String>` this mechanism replaced.
#[test]
fn lane_is_present_exactly_for_delivered_elsewhere() {
    let inventories = [
        ("BinderLawDemo", binder_law_demo::BinderLawDemoMetadata.lowering_dispositions()),
        ("TypedDropDemo", typed_drop_demo::TypedDropDemoMetadata.lowering_dispositions()),
        (
            "CongruenceLaneDemo",
            congruence_lane_demo::CongruenceLaneDemoMetadata.lowering_dispositions(),
        ),
    ];
    let mut checked = 0usize;
    for (name, inventory) in inventories {
        for disposition in inventory {
            checked += 1;
            match disposition.outcome {
                LoweringOutcomeKind::DeliveredElsewhere => assert!(
                    disposition.lane.is_some(),
                    "{name}: {} claims another lane covers it but does not say which",
                    disposition.summary(),
                ),
                _ => assert!(
                    disposition.lane.is_none(),
                    "{name}: {} names a lane it does not delegate to",
                    disposition.summary(),
                ),
            }
        }
    }
    // Positive control on the loop: three grammars, at least one disposition each.
    assert!(checked >= 3, "the invariant must have been checked against real entries");
}
