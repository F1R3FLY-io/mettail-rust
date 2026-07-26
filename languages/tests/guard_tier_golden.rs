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

// Task #11 (extended 2026-07-26): the FIXTURE grammars whose golden tier tuples are pinned
// here are not production languages, so their definitions live in
// `languages/tests/definitions/` and are `#[path]`-included rather than named through
// `mettail_languages::<lang>`. This binary is a CONSUMER of each: it deliberately does NOT
// invoke any `<lang>_generated_tests!` wrapper, because each definition's DESIGNATED HOST
// binary is the sole invoker, so the generated suites stay single-instanced.
#[path = "definitions/led_test.rs"]
mod ledtest;
#[path = "definitions/guarded_rho.rs"]
mod guardedrho;

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

/// **RhoCalc** — process calculus over `Proc`/`Name` + the scalar tower, grown by the
/// RhoCalc→Rholang-1.4/WFST merge (pathmap + read/write zippers, set/map/bag native types,
/// for-row sugar, input-bind, byte-array). 1 binder field (the `^[xs].p` scope binder ⇒ T2
/// freshness). 227 structural fields (211 after Layer-F, +16 from the `@`-led empty/polyadic
/// send rules — see the send-rule paragraph below; scalar operands, casts, channel/process
/// payloads, and the collection/zipper/cast operands — all data-sort assertions ⇒ T1). T2 = 144
/// rewrite conditions + 138 congruence premises + 1 binder = 283. worst = T2.
///
/// ROOT-P Layer F (design-cycle-2, 2026-07-02): the six grammar-redundant persistent ForRow
/// rules (ForRowPersistentWhere/NoWhere, ForRowSinglePersistentWhere/NoWhere,
/// ForRowSingleEmptyPersistentWhere/NoWhere) were DELETED (their readings are expressible via
/// the general ForRow rules over a persistent InputBind — see ForRowPersistentRuleRedundancy.v).
/// That removed exactly 15 structural fields (4+3+3+2+1 from the Where/NoWhere heads + the empty
/// forms: cond/bs/lhs/n operands), dropping T1 226 → 211 and total 509 → 494. T2 is unchanged
/// (283) — the deleted rules carried no binder / rewrite-condition / congruence premise.
///
/// `@`-led send-rule additions (2026-07-04, merge-to-green): the empty `@`-send rules
/// (`POutputNilEmpty`/`PPersistOutputNilEmpty` [0 fields each], `POutputQuotedEmpty` [n:Name],
/// `POutputShortEmpty`/`PPersistOutputShortEmpty` [p:Proc] = 3 fields) plus the polyadic `@`-send
/// rules (`POutputNil2Plus`/`PPersistOutputNil2Plus` [a,bs = 2 each], `POutputQuoted2Plus`/
/// `POutputShort2Plus`/`PPersistOutputShort2Plus` [chan,a,bs = 3 each] = 13 fields) add exactly
/// 3 + 13 = 16 structural (data-sort) fields ⇒ T1 211 → 227, total 494 → 510. T2 is unchanged
/// (283) — none carries a binder / rewrite-condition / congruence premise; T3/T4 stay 0.
///
/// Re-derived (not invented) after the send-rule additions: the harvested
/// `check_guard_decidability` tuple is `(510, 227, 283, 0, 0, T2)`, and the in-test cross-check
/// (`assert_tier_tuple`) independently confirms 227 == structural fields and 283 == conditions +
/// congruence premises + binders against the raw metadata.
///
/// Semantic-predicate surface (2026-07-25, M-0): the `implies` connective
/// (`Implies . a:Proc, b:Proc`) adds exactly **2** structural fields ⇒ T1 227 → 229,
/// total 510 → 512. T2 is unchanged (283): `implies` declares no binder, no rewrite
/// condition and no congruence premise — it is one more propositional operator over
/// the same two `Proc` operand positions `And`/`Or` already contribute. T3/T4 stay 0,
/// so `worst` stays T2. Both numbers were HARVESTED from a failing run of this test
/// and then justified by the field count above, never the other way round.
///
/// Semantic-predicate surface (2026-07-25, M-1b): `matches`
/// (`Matches . a:Proc, p:Proc`) and the paper's spatial connective
/// (`SpatialPPar . a:Proc, b:Proc`) add **2 + 2 = 4** more structural fields ⇒
/// T1 229 → 233, total 512 → 516. T2 is again unchanged (283): both are pure
/// constructors with no binder, no rewrite condition, and no congruence premise —
/// `matches` is decided post-match (in guard position) and `PPar(φ,ψ)` is a
/// pattern former, so neither participates in the reduction relation at all.
/// T3/T4 stay 0 and `worst` stays T2.
///
/// Trie-enumeration surface (2026-07-26): `getPath` (`RZGetPath . z:Proc`),
/// `toNextLeaf` (`RZToNextLeaf . z:Proc`) and `leafCount`
/// (`RZLeafCount . z:Proc`) add **1 + 1 + 1 = 3** structural fields ⇒
/// T1 233 → 236, total 516 → 519. Each declares exactly ONE operand — the
/// receiver `z`, a data-sort assertion like every other ReadZipper method
/// (`RZGetLeaf`, `RZChildCount`, `RZDescendFirst`, `RZToNextSibling`) ⇒ T1.
/// T2 is unchanged (283): none declares a binder, a rewrite condition, or a
/// congruence premise — all three are queries over an already-reduced zipper
/// and none participates in the reduction relation. T3/T4 stay 0 and `worst`
/// stays T2.
#[test]
fn rhocalc_guard_tiers() {
    let meta = mettail_languages::rhocalc::RhoCalcLanguage.metadata();
    assert_tier_tuple(meta, 519, 236, 283, 0, 0, T2);
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
    let meta = crate::guardedrho::GuardedRhoLanguage.metadata();
    assert_tier_tuple(meta, 8, 7, 1, 0, 0, T2);
}

/// **LedTest** — `Num`/`Pred`/`Expr` with `i32`/`bool` scalars. No binders. 18
/// structural fields (the `a:Num, b:Num` operands of the arithmetic/comparison
/// operators, casts, `Expr` positions ⇒ all T1). T2 = 18 conditions + 18
/// congruence premises (the `…Cong . | U ~> V |- …` closure) + 0 binders = 36.
/// worst = T2.
#[test]
fn ledtest_guard_tiers() {
    let meta = crate::ledtest::LedTestLanguage.metadata();
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
        crate::guardedrho::GuardedRhoLanguage.metadata(),
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
