//! **RhoCalc's `where` slot induces a semantic-predicate obligation.**
//!
//! # What this pins, and why it needed a new mechanism
//!
//! *"If it is in a `where` clause, it is a semantic predicate."* Before this change,
//! `collect_guard_obligations` induced **zero** obligations from RhoCalc's `where` surface: it
//! emitted one only for a [`TermParam::GuardBody`] — a `?name:Guard` slot — and RhoCalc's guard
//! parameter is `cond:Proc`, an ordinary [`TermParam::Simple`], which was explicitly skipped.
//!
//! Retyping the slot to `?cond:Guard` was the obvious move and it is the wrong one. The `Guard`
//! type switches the parser into the predicate sublanguage, whose runtime `BehavioralPred` is
//! `RelationQuery | Quantified | AcMatch | And | Or | Not | Implies | Top` with
//! `PredArg = Var | IntLit | StringLit`. That grammar has **no comparison operators, no
//! arithmetic, and no nesting inside arguments**, so:
//!
//! | RhoCalc `where` today | as a `BehavioralPred` |
//! |---|---|
//! | `where x == 42` | only as a flat `RelationQuery("eq", [Var x, IntLit 42])` |
//! | `where x + y < 10` | **not expressible** |
//! | `where t matches {P \| Q}` | **not expressible** |
//!
//! Retyping would therefore not make the guard a semantic predicate; it would delete most of the
//! guard language, taking the guard test suite and the settlement demos with it.
//!
//! The `guards { guard_slots { … } }` declaration says the same thing without the loss: the
//! author states that the parameter is a semantic predicate, and the backend induces exactly the
//! obligation a `?cond:Guard` slot would. The guard itself stays a full `Proc` expression, which
//! `mettail_languages::rhocalc::guard_substrate` encodes into the Dovetail/SFT substrate.
//!
//! [`TermParam::GuardBody`]: mettail_ast::grammar::TermParam::GuardBody
//! [`TermParam::Simple`]: mettail_ast::grammar::TermParam::Simple

#![cfg(feature = "rhocalc")]

use mettail_languages::rhocalc::RhoCalcLanguage;
use mettail_rholang_codegen::{
    collect_guard_obligations, RhoGuardObligation, RhoGuardObligationKind,
};
use mettail_runtime::Language;

fn rhocalc_def() -> mettail_ast::language::LanguageDef {
    let source = RhoCalcLanguage
        .metadata()
        .definition_source()
        .expect("generated RhoCalcLanguage must expose its definition_source");
    mettail_rholang_codegen::reconstruct_language_def(source)
        .expect("RhoCalcLanguage definition_source must reconstruct as a LanguageDef")
}

/// ★ THE OBLIGATIONS EXIST. Both `where` surfaces — the multi-bind `&`-join row and the
/// single-bind row — induce a `BehavioralPredicate` obligation.
#[test]
fn both_where_surfaces_induce_a_behavioral_predicate_obligation() {
    let obligations = collect_guard_obligations(&rhocalc_def());

    for expected_id in ["term:ForRowWhere:guard:cond", "term:ForRowSingleWhere:guard:cond"] {
        assert!(
            obligations.contains(&RhoGuardObligation::new(
                expected_id,
                RhoGuardObligationKind::BehavioralPredicate
            )),
            "expected obligation `{expected_id}` (BehavioralPredicate); RhoCalc's `where` slot \
             is a semantic predicate and must induce one. Got: {:?}",
            obligations
                .iter()
                .map(|o| o.id.as_str())
                .collect::<Vec<_>>()
        );
    }
}

/// The count went UP by exactly two, and the two are the `where` slots — not some third thing
/// the declaration dragged in.
#[test]
fn exactly_the_two_where_slots_were_added() {
    let obligations = collect_guard_obligations(&rhocalc_def());
    let where_slots: Vec<&str> = obligations
        .iter()
        .filter(|o| o.id.starts_with("term:") && o.id.contains(":guard:"))
        .map(|o| o.id.as_str())
        .collect();
    assert_eq!(
        where_slots,
        vec!["term:ForRowSingleWhere:guard:cond", "term:ForRowWhere:guard:cond"],
        "exactly the two declared `where` slots induce term-guard obligations"
    );
}

/// The obligation a DECLARED slot induces is indistinguishable from the one a `?name:Guard` slot
/// induces — same id shape, same kind. That is the property that makes the declaration a genuine
/// alternative surface rather than a parallel mechanism with its own semantics.
#[test]
fn a_declared_slot_and_a_typed_slot_induce_the_same_shape() {
    let rhocalc = collect_guard_obligations(&rhocalc_def());
    let declared = rhocalc
        .iter()
        .find(|o| o.id == "term:ForRowWhere:guard:cond")
        .expect("the declared slot's obligation");

    // GuardedRho's `?guard:Guard` slot, the typed surface, for comparison.
    let guarded_rho_source = mettail_languages::guardedrho::GuardedRhoLanguage
        .metadata()
        .definition_source()
        .expect("generated GuardedRhoLanguage must expose its definition_source");
    let guarded_rho_def = mettail_rholang_codegen::reconstruct_language_def(guarded_rho_source)
        .expect("GuardedRhoLanguage definition_source must reconstruct as a LanguageDef");
    let typed = collect_guard_obligations(&guarded_rho_def)
        .into_iter()
        .find(|o| o.id == "term:PGuardedInput:guard:guard")
        .expect("the typed slot's obligation");

    assert_eq!(
        declared.kind, typed.kind,
        "a declared guard slot and a `?name:Guard` slot must induce the SAME obligation kind"
    );
    assert_eq!(declared.kind, RhoGuardObligationKind::BehavioralPredicate);
    // Both ids follow `term:<Label>:guard:<param>`; only the label and param differ.
    for id in [declared.id.as_str(), typed.id.as_str()] {
        let parts: Vec<&str> = id.split(':').collect();
        assert_eq!(parts.len(), 4, "id shape is `term:<Label>:guard:<param>`: {id}");
        assert_eq!(parts[0], "term");
        assert_eq!(parts[2], "guard");
    }
}

/// ★ RECOGNITION IS BY DECLARATION, NEVER BY SPELLING. The `where` literal in the rule's syntax
/// form is not what makes the slot a guard — `ForRowNoWhere` and `ForRowSingleNoWhere` have no
/// guard parameter and induce nothing, and no rule outside the declaration does either.
#[test]
fn no_undeclared_rule_induces_a_term_guard_obligation() {
    let def = rhocalc_def();
    let declared: Vec<String> = def
        .guard_config
        .as_ref()
        .map(|config| {
            config
                .guard_slots
                .iter()
                .map(|slot| format!("term:{}:guard:{}", slot.label, slot.param))
                .collect()
        })
        .unwrap_or_default();
    assert_eq!(declared.len(), 2, "RhoCalc declares exactly two guard slots");

    for obligation in collect_guard_obligations(&def) {
        if obligation.id.starts_with("term:") {
            assert!(
                declared.contains(&obligation.id),
                "`{}` is a term-guard obligation that no `guard_slots` entry declares — \
                 recognition must be by declaration, never by the `where` spelling",
                obligation.id
            );
        }
    }
}
