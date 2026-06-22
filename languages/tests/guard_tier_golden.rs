//! Golden tier assertions for `check_guard_decidability` (OSLF substrate
//! Phase 1 `.1`).
//!
//! Each assertion is the **actual** output of
//! [`mettail_testkit::analytical::guards::check_guard_decidability`] on a
//! generated language's [`LanguageMetadata`], harvested by running the code (not
//! invented). The tuple is `(total_guards, T1, T2, T3, T4, worst_tier)`.
//!
//! ## How the tuple is determined (the guard-source inventory)
//!
//! `check_guard_decidability` tallies guards by source:
//!
//! - **Structural (T1)** — one per non-binder, non-`Guard` constructor field.
//!   Each is a data-sort *type assertion* decided by the EBA-backed sorted
//!   classifier: a registry-resident scalar sort (`Int`, `Float`, `Str`, …) is
//!   compile-time decidable, and a non-scalar category (a process category like
//!   `Proc`/`Name`, a collection container, a user ADT) falls back to the
//!   structural classifier on the `True` skeleton — also compile-time decidable.
//!   So **T1 == (number of non-binder, non-`Guard` fields)**, exactly.
//!
//! - **Behavioral (T2)** — rewrite freshness conditions (`x # P`), congruence
//!   premises (`S ~> T`), and binder-field freshness (`^x. body`). Each is a
//!   relational atom over the reduction / α-equivalence relation, runtime-
//!   decidable. So **T2 == (Σ rewrite conditions) + (number of congruence
//!   premises) + (number of binder fields)**.
//!
//! Hence **total == T1 + T2**, and **worst == T2** for any grammar that has at
//! least one congruence rewrite, freshness condition, or binder; **worst == T1**
//! only for a grammar with none of those (pure structural type assertions).
//!
//! A `?guard:Guard` slot is the guard *body carrier*, not a data-sort assertion,
//! so it is excluded from the structural tally (see `GuardedRho` below). T3/T4
//! never arise here: no grammar declares an unbounded/semi-decidable infinite
//! quantifier in a guard source — every behavioral source is a (runtime-
//! decidable) relational atom, and every structural source is (compile-time
//! decidable).
//!
//! These tuples are a **regression fence**: if the guard-typing logic, a
//! grammar's field count, or its congruence/binder structure changes, the exact
//! tuple changes and the test fails loudly — it must be re-derived from the code,
//! never relaxed.

use mettail_runtime::{Language, LanguageMetadata};
use mettail_testkit::analytical::guards::check_guard_decidability;

/// Assert the exact `(total, T1, T2, T3, T4, worst)` tuple for a language and,
/// independently, re-derive `(T1, T2)` from the raw metadata so the golden
/// numbers are *cross-checked* against the guard-source inventory in the same
/// test (T1 = structural fields; T2 = conditions + congruence premises + binder
/// fields). This makes every magic number self-justifying.
fn assert_tier_tuple(
    meta: &dyn LanguageMetadata,
    total: usize,
    t1: usize,
    t2: usize,
    t3: usize,
    t4: usize,
    worst: &str,
) {
    let r = check_guard_decidability(meta);
    assert_eq!(
        (
            r.total_guards,
            r.compile_time_decidable,
            r.runtime_decidable,
            r.semi_decidable,
            r.undecidable,
            r.worst_tier.as_str(),
        ),
        (total, t1, t2, t3, t4, worst),
        "golden tier tuple changed for `{}` — re-derive from the code, do not relax: {}",
        meta.name(),
        r.summary,
    );

    // ── Cross-check the asserted T1/T2 against the raw guard-source inventory ──
    let structural_fields = meta
        .terms()
        .iter()
        .flat_map(|t| t.fields.iter())
        .filter(|f| !f.is_binder && f.ty != "Guard" && f.ty != "Option<Guard>")
        .count();
    let binder_fields = meta
        .terms()
        .iter()
        .flat_map(|t| t.fields.iter())
        .filter(|f| f.is_binder)
        .count();
    let conditions: usize = meta.rewrites().iter().map(|rw| rw.conditions.len()).sum();
    let congruence_premises = meta
        .rewrites()
        .iter()
        .filter(|rw| rw.premise.is_some())
        .count();

    assert_eq!(
        structural_fields, t1,
        "`{}`: T1 must equal the number of non-binder, non-Guard structural fields",
        meta.name()
    );
    assert_eq!(
        conditions + congruence_premises + binder_fields,
        t2,
        "`{}`: T2 must equal (rewrite conditions) + (congruence premises) + (binder fields)",
        meta.name()
    );
    assert_eq!(t1 + t2, total, "`{}`: total must equal T1 + T2", meta.name());
}

const T2: &str = "T2 (runtime decidable)";

/// **Calculator** — the full scalar arithmetic tower (`Int`/`UInt32`/`BigInt`/
/// `BigRat`/`Fixed`/`Float`/`Bool`/`Str`) plus `Proc`/`List`/`Bag`/`Map`. No
/// binders. 236 structural fields (operator operands `a:Int`, `a:BigRat`,
/// cast inputs, injection payloads — all data-sort assertions ⇒ all T1). T2 =
/// 219 rewrite conditions + 216 congruence premises (the `…Cong . | S ~> T |- …`
/// closure over every operator) + 0 binders = 435. worst = T2 (congruences are
/// runtime-decidable side conditions on `~>`).
#[test]
fn calculator_guard_tiers() {
    let meta = mettail_languages::calculator::CalculatorLanguage.metadata();
    assert_tier_tuple(meta, 671, 236, 435, 0, 0, T2);
}

/// **RhoCalc** — process calculus over `Proc`/`Name` + the scalar tower. 2
/// binder fields (`PInputs`/`PNew` carry `^[xs].p` multi-binders ⇒ T2 freshness).
/// 105 structural fields (scalar operands, casts, channel/process payloads).
/// T2 = 102 conditions + 96 congruence premises + 2 binders = 200. worst = T2.
#[test]
fn rhocalc_guard_tiers() {
    let meta = mettail_languages::rhocalc::RhoCalcLanguage.metadata();
    assert_tier_tuple(meta, 305, 105, 200, 0, 0, T2);
}

/// **Ambient** — mobile ambients over `Proc`/`Name` (both non-scalar; no native
/// types). 1 binder field (`PNew ^x.p` ⇒ T2). 9 structural fields (the `Name`/
/// `Proc` positions of `PIn`/`POut`/`POpen`/`PAmb` — non-scalar categories that
/// fall back to the `True` skeleton ⇒ still T1). T2 = 3 conditions + 3
/// congruence premises (`ParCong`/`NewCong`/`AmbCong`) + 1 binder = 7. worst = T2.
#[test]
fn ambient_guard_tiers() {
    let meta = mettail_languages::ambient::AmbientLanguage.metadata();
    assert_tier_tuple(meta, 16, 9, 7, 0, 0, T2);
}

/// **Lambda** — untyped λ-calculus over a single `Term` sort. 1 binder field
/// (`Lam ^x.body` ⇒ T2). 2 structural fields (`App fun:Term, arg:Term` — the
/// non-scalar `Term` positions ⇒ T1). T2 = 3 conditions + 3 congruence premises
/// (`AppCongL`/`AppCongR`/`LamCong`) + 1 binder = 7. worst = T2.
#[test]
fn lambda_guard_tiers() {
    let meta = mettail_languages::lambda::LambdaLanguage.metadata();
    assert_tier_tuple(meta, 9, 2, 7, 0, 0, T2);
}

/// **GuardedRho** — guarded Rho with a `?guard:Guard` slot and a single `Int`
/// scalar. 1 binder field (`PGuardedInput ^x.p` ⇒ T2). 1 `Guard` slot, which is
/// the guard-body *carrier* and is **excluded** from the structural tally (R1
/// containment). 7 structural fields (channel `Name`s, process `Proc`s, the
/// `CastInt k:Int` operand — `Int` is a registry scalar ⇒ T1; the rest are
/// non-scalar ⇒ T1 via fallback). No rewrites ⇒ 0 conditions, 0 congruence
/// premises. T2 = 0 + 0 + 1 binder = 1. worst = T2 (the single binder).
#[test]
fn guardedrho_guard_tiers() {
    let meta = mettail_languages::guardedrho::GuardedRhoLanguage.metadata();
    assert_tier_tuple(meta, 8, 7, 1, 0, 0, T2);
}

/// **LedTest** — `Num`/`Pred`/`Expr` with `i32`/`bool` scalars. No binders. 18
/// structural fields (the `a:Num, b:Num` operands of the arithmetic/comparison
/// operators, casts, `Expr` positions ⇒ all T1). T2 = 18 conditions + 18
/// congruence premises (the `…Cong . | U ~> V |- …` closure) + 0 binders = 36.
/// worst = T2.
#[test]
fn ledtest_guard_tiers() {
    let meta = mettail_languages::ledtest::LedTestLanguage.metadata();
    assert_tier_tuple(meta, 54, 18, 36, 0, 0, T2);
}

/// **BaseMath** (composition base grammar). No binders. 4 structural fields ⇒
/// T1. T2 = 4 conditions + 4 congruence premises + 0 binders = 8. worst = T2.
#[test]
fn basemath_guard_tiers() {
    let meta = mettail_languages::basemath::BaseMathLanguage.metadata();
    assert_tier_tuple(meta, 12, 4, 8, 0, 0, T2);
}

/// **ExtMath** (composition extended grammar) — same guard shape as BaseMath at
/// this layer: 4 structural fields (T1) + 4 conditions + 4 congruence premises
/// (T2) = 12, worst = T2.
#[test]
fn extmath_guard_tiers() {
    let meta = mettail_languages::extmath::ExtMathLanguage.metadata();
    assert_tier_tuple(meta, 12, 4, 8, 0, 0, T2);
}

/// **R1 containment**: a binder field NEVER lands in the structural tally. We
/// assert this two ways for every language that has binders: (i) the structural
/// T1 count equals the non-binder/non-Guard field count *exactly* (so binders are
/// excluded — already cross-checked in `assert_tier_tuple`), and (ii) here, that
/// every binder field is instead counted at T2, by confirming the T2 total drops
/// by exactly the binder count when binders are hypothetically removed from the
/// behavioral sum. This guards against a regression that would mis-route a binder
/// into the structural (T1) bucket.
#[test]
fn binders_never_enter_structural_tally() {
    for meta in [
        mettail_languages::rhocalc::RhoCalcLanguage.metadata(),
        mettail_languages::ambient::AmbientLanguage.metadata(),
        mettail_languages::lambda::LambdaLanguage.metadata(),
        mettail_languages::guardedrho::GuardedRhoLanguage.metadata(),
    ] {
        let r = check_guard_decidability(meta);

        let binder_fields = meta
            .terms()
            .iter()
            .flat_map(|t| t.fields.iter())
            .filter(|f| f.is_binder)
            .count();
        let structural_fields = meta
            .terms()
            .iter()
            .flat_map(|t| t.fields.iter())
            .filter(|f| !f.is_binder && f.ty != "Guard" && f.ty != "Option<Guard>")
            .count();
        let conditions: usize = meta.rewrites().iter().map(|rw| rw.conditions.len()).sum();
        let congruence_premises =
            meta.rewrites().iter().filter(|rw| rw.premise.is_some()).count();

        assert!(binder_fields >= 1, "`{}` should have ≥1 binder for this check", meta.name());

        // (i) Structural T1 excludes binders entirely.
        assert_eq!(
            r.compile_time_decidable, structural_fields,
            "`{}`: a binder field leaked into the structural T1 tally",
            meta.name()
        );

        // (ii) Each binder is counted at T2 (behavioral). Removing the binder
        // contribution from the behavioral sum must exactly reproduce the
        // condition+congruence behavioral total, i.e. T2 - binders == cond + cong.
        assert_eq!(
            r.runtime_decidable - binder_fields,
            conditions + congruence_premises,
            "`{}`: binder fields are not all routed to the behavioral T2 tally",
            meta.name()
        );
    }
}
