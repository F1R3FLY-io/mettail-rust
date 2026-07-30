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
#[path = "definitions/guarded_rho.rs"]
mod guardedrho;
#[path = "definitions/led_test.rs"]
mod ledtest;

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

    // ── The raw guard-source inventory, computed BEFORE the golden assert so a
    // ── mismatch can report the decomposition instead of only the totals.
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
        (
            r.total_guards,
            r.compile_time_decidable,
            r.runtime_decidable,
            r.semi_decidable,
            r.undecidable,
            r.worst_tier.as_str(),
        ),
        (total, t1, t2, t3, t4, worst),
        "golden tier tuple changed for `{}` — re-derive from the code, do not relax: {}\n\
         {}",
        meta.name(),
        r.summary,
        drift_shape(
            meta,
            (total, t1, t2),
            (r.total_guards, r.compile_time_decidable, r.runtime_decidable),
            structural_fields,
            binder_fields,
            conditions,
            congruence_premises,
        ),
    );

    assert_eq!(
        structural_fields,
        t1,
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

/// Turn a golden-tuple mismatch into a **statement about the grammar**, derived from
/// `check_guard_decidability`'s own tally rules rather than restated by hand.
///
/// `check_guard_decidability` ([`mettail_testkit::analytical::guards`]) computes
///
/// ```text
///     T1 = #{ f ∈ fields(metadata.terms()) | ¬f.is_binder ∧ f.ty ∉ {Guard, Option<Guard>} }
///     T2 = Σ_rw rw.conditions.len()  +  #{ rw | rw.premise.is_some() }  +  #{ f | f.is_binder }
/// ```
///
/// so `ΔT1` and `ΔT2` **localise** a drift to one guard source before anyone opens a diff:
/// `ΔT1 ≠ 0 ∧ ΔT2 = 0` can only be a constructor field appearing or disappearing; `ΔT1 = 0 ∧
/// ΔT2 ≠ 0` can only be a rewrite condition, a congruence premise, or a binder; a field that
/// merely *changed tier* (e.g. gained `is_binder`) shows as `ΔT1 = −k, ΔT2 = +k` with `Δtotal
/// = 0`. This is diagnostics only — it pins no new constant and so cannot itself go stale —
/// and it exists because the 2026-07-30 `PParInternal` investigation had to reconstruct
/// exactly this inference, and then the raw decomposition, by hand from a totals-only message.
/// `"1 field"` / `"2 fields"`. A diagnostic that says "exactly 1 field(s)" invites the reader
/// to wonder whether the count is really known, which is the opposite of this message's job.
fn plural(n: isize, one: &'static str, many: &'static str) -> &'static str {
    match n {
        1 => one,
        _ => many,
    }
}

fn drift_shape(
    meta: &dyn LanguageMetadata,
    expected: (usize, usize, usize),
    actual: (usize, usize, usize),
    structural_fields: usize,
    binder_fields: usize,
    conditions: usize,
    congruence_premises: usize,
) -> String {
    let d = |a: usize, e: usize| a as isize - e as isize;
    let (d_total, d_t1, d_t2) = (
        d(actual.0, expected.0),
        d(actual.1, expected.1),
        d(actual.2, expected.2),
    );

    // `{:+}` renders zero as `+0`, which reads as a change when it is the absence of one —
    // and "ΔT2 = 0" is the single most load-bearing token in this message, because it is what
    // rules out a tier shift. So sign only the non-zero deltas.
    let signed = |v: isize| if v == 0 { "0".to_string() } else { format!("{v:+}") };

    let mut s = String::with_capacity(1024);
    s.push_str("    ── implied shape of the change (derived from guards.rs's tally rules) ──\n");
    s.push_str(&format!(
        "    Δtotal = {}, ΔT1 = {}, ΔT2 = {}\n",
        signed(d_total),
        signed(d_t1),
        signed(d_t2)
    ));

    match (d_t1, d_t2) {
        (0, 0) => s.push_str(
            "    T1 and T2 both match, so only `worst`/T3/T4 moved — the guard-TYPING logic \
             changed, not the grammar.\n",
        ),
        (dt1, 0) => s.push_str(&format!(
            "    ΔT2 = 0 ⇒ no rewrite condition, congruence premise, or binder field changed.\n    \
             ΔT1 = {dt1:+} ⇒ exactly {n} non-binder, non-`Guard` constructor {field} {verb} \
             `metadata.terms()`.\n    Look for a rule ADDED TO or REMOVED FROM the declaring \
             `language!` spec — not for a field changing type.\n",
            n = dt1.abs(),
            field = plural(dt1.abs(), "field", "fields"),
            verb = if dt1 < 0 { "DISAPPEARED from" } else { "APPEARED in" },
        )),
        (0, dt2) => s.push_str(&format!(
            "    ΔT1 = 0 ⇒ no constructor field was added or removed.\n    ΔT2 = {dt2:+} ⇒ the \
             change is in the BEHAVIORAL sources: a rewrite condition, a congruence premise, \
             or a binder field. Note a congruence contributes to BOTH sums, so one added \
             congruence moves T2 by 2.\n",
        )),
        (dt1, dt2) if dt1 == -dt2 && d_total == 0 => s.push_str(&format!(
            "    Δtotal = 0 with ΔT1 = {dt1:+}, ΔT2 = {dt2:+} ⇒ {n} {field} CHANGED TIER \
             rather than appearing or disappearing — the signature of `is_binder` flipping, \
             or of a field's type becoming (or ceasing to be) `Guard`/`Option<Guard>`.\n",
            n = dt1.abs(),
            field = plural(dt1.abs(), "field", "fields"),
        )),
        (dt1, dt2) => s.push_str(&format!(
            "    ΔT1 = {dt1:+} AND ΔT2 = {dt2:+} ⇒ BOTH a structural and a behavioral source \
             moved. Do not attribute this to one commit without checking both; a single rule \
             carrying its own congruence does exactly this (+1 T1, +2 T2).\n",
        )),
    }

    s.push_str(&format!(
        "    observed inventory NOW: structural={structural_fields} binders={binder_fields} \
         conditions={conditions} premises={congruence_premises} \
         (terms={terms}, rewrites={rewrites})\n    \
         so T1 == {structural_fields} and T2 == {conditions} + {congruence_premises} + \
         {binder_fields} == {t2sum}.\n",
        terms = meta.terms().len(),
        rewrites = meta.rewrites().len(),
        t2sum = conditions + congruence_premises + binder_fields,
    ));
    s
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

/// **Rholang** — process calculus over `Proc`/`Name` + the scalar tower, grown by the
/// Rholang→Rholang-1.4/WFST merge (pathmap + read/write zippers, set/map/bag native types,
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
///
/// ★ Speculation-lookahead surface (2026-07-26, RE-DERIVED not relaxed). `a5a93a23`
/// added the `[*]` / `[n]` lookahead SURFACE
///
/// ```text
///     PLookahead    . p:Proc, n:Proc |- p "[" n "]" : Proc;
///     PLookaheadAll . p:Proc         |- p "[" "*" "]" : Proc;
/// ```
///
/// — **2 + 1 = 3** more structural fields ⇒ T1 236 → 239, total 519 → 522. T2 is
/// unchanged (283): both are PLAIN rules — no `![…]` action, no `fold`/`step` mode, no
/// binder field, no freshness condition and no congruence premise — so neither adds a
/// relational atom over the reduction relation. Every field is a `Proc` position, i.e. a
/// non-scalar category decided by the structural classifier on the `True` skeleton ⇒ T1.
/// T3/T4 stay 0 and `worst` stays T2.
///
/// ⚠ This golden was STALE for twelve commits: `a5a93a23` landed the rules and did not
/// re-derive the tuple, so the test had been failing on `(522, 239, …)` vs `(519, 236, …)`
/// since then, INDEPENDENTLY of the half-rule-family work that noticed it. The number is
/// re-derived from the two rule declarations above, not fitted to the observed output —
/// the cross-check inside `assert_tier_tuple` re-counts the structural fields from the raw
/// metadata and would reject a fitted number.
///
/// ★ `List.last()` (2026-07-28, RE-DERIVED not relaxed). Adding the FIPS-mandated `last()`
/// projection contributes **+1 T1 and +2 T2**, and the split is worth spelling out because
/// the two halves come from two different declarations:
///
/// ```text
///     LLast     . l:Proc |- l "." "last" "(" ")" : Proc ![{ … }] fold;
///     LLastCong .        | S ~> T |- (LLast S) ~> (LLast T);
/// ```
///
/// * **T1 239 → 240.** `LLast` declares exactly ONE operand, the receiver `l:Proc` — a
///   non-binder, non-`Guard` field, and a non-scalar category decided by the structural
///   classifier on the `True` skeleton, exactly like every other unary collection method
///   (`LLength`, `MKeys`, `RZGetLeaf`). The `fold` action contributes nothing: an `![…]`
///   body is not a field, and it is not a rewrite condition either — which is precisely why
///   the three trie-enumeration rules above moved T1 while leaving T2 alone.
/// * **T2 283 → 285, i.e. +2 from ONE rule.** A congruence contributes to BOTH behavioral
///   sums, because `T2 == (Σ rewrite conditions) + (congruence premises) + (binder fields)`
///   and the generated `RewriteDef` for `LLastCong` carries
///   `conditions: &["S ~> T"]` *and* `premise: Some(("S", "T"))`. It is counted once in each
///   sum. This is not special pleading for `last`: every congruence in this grammar has that
///   shape — the immediately adjacent `LConcatCongL` is byte-identical in structure — and it
///   is the same double-count that makes Calculator's T2 read "219 rewrite conditions + 216
///   congruence premises". `LLast` declares no binder and no freshness condition, so nothing
///   else moves.
/// * **total 522 → 525**, and `522 + 1 + 2 == 525 == 240 + 285` closes the arithmetic.
///   T3/T4 stay 0 (no unbounded quantifier is introduced), so `worst` stays T2.
///
/// The numbers were derived from the two declarations and then CONFIRMED against the
/// generated `metadata.rs` (`TermDef "LLast"` has one non-binder field; `RewriteDef
/// "LLastCong"` has one condition and one premise) — not read off the failure message. The
/// cross-check inside `assert_tier_tuple` independently re-counts both from raw metadata and
/// would reject a fitted number.
///
/// ★ `PParInternal` DELETED (2026-07-30, RE-DERIVED not relaxed). `8c946bff` deleted the
/// dead `__ppar(…)` rule, declared at `languages/src/rholang.rs:450` as of `8c946bff^`:
///
/// ```text
///     PParInternal . ps:HashBag(Proc)
///     |- "__ppar" "(" ps.*sep(",") ")" : Proc ![{ Proc::PPar(ps.clone()) }] fold;
/// ```
///
/// * **T1 240 → 239, total 525 → 524.** The rule declared exactly ONE field, `ps`, of type
///   `HashBag(Proc)` — non-binder and non-`Guard`, hence one structural guard while it
///   existed. `HashBag(Proc)` is a collection container, i.e. a non-scalar category decided
///   by the structural classifier on the `True` skeleton, exactly like every other
///   collection-payload field ⇒ it was T1, never T2.
/// * **T2 unchanged at 285.** The rule declared no binder, no freshness condition and no
///   congruence premise, and its `![…] fold` action is neither a field nor a rewrite
///   condition — the same reason `LLast`'s fold moved T1 while leaving T2 alone, above.
///   T3/T4 stay 0, so `worst` stays T2. Measured after the deletion: 145 rewrite conditions
///   + 139 congruence premises + 1 binder = 285.
///
/// **The deletion is CORRECT and this pin was STALE** — not the other way round, which is the
/// distinction that decides whether to fix the grammar or re-derive the number. `PParInternal`
/// was a THIRD surface for a node that has two (the braced `PPar` collection rule and the
/// infix `PParInfix`), and it was unreachable in BOTH directions: `__ppar(Nil, Nil)` did not
/// parse at any arity (`TrailingTokens` at byte 5), and `Proc::PPar` renders through the
/// braced `{ … | … }` form, never through `__ppar(…)`. A data-sort type assertion on a slot
/// no term could ever reach is a guard this grammar genuinely no longer has, so 239 is the
/// right answer and 240 was describing a rule that is gone. `8c946bff` re-derived SEVEN
/// downstream consumers (`lowering_disposition_inventory`'s `COLLECTION_PARAMETER_FOLDS`,
/// `wpda_codegen/factoring.rs`'s rule-index pins, the two `dovetail_report` narratives,
/// `test_gen/strategies.rs`, and two manual pages) and missed only this one, which then stood
/// red for 27 commits.
///
/// ⚠ The float rulings are NOT the cause, and neither is #98 — both were CHECKED AND
/// EXCLUDED, not assumed away, because the arithmetic (total −1, T1 −1, T2 flat) pins the
/// change to "exactly one non-binder, non-`Guard` field disappeared" and several plausible
/// suspects had to be eliminated:
///
/// * Over the whole `bbceb6d9`→here range the complete `(term, field, ty, is_binder)`
///   inventory of `languages/src/rholang.rs` differs by **exactly the one row above**. The
///   other ten commits that touched the spec in that range — including the `!`-marked float
///   rulings `b77e657c` / `ab885336` / `19510082`, the `#163` ruling `0d05986d`, and the
///   `#151`/`#74` unset-value change `848d36ad` — changed rewrite bodies, actions and prose,
///   and moved no constructor's field list at all.
/// * #98 (`e6172128`, the demand-gated HOL family) cannot move ANY language's tally, which is
///   a stronger statement than "rholang happens to be unaffected". The family
///   (`Lam{D}`/`MLam{D}`/`Apply{D}`/`MApply{D}`) is emitted into the AST *enums* — rholang's
///   `ast_enums.rs` carries 1520 such variants — and **no** HOL variant is ever emitted as a
///   `TermDef`. `metadata.terms()` carries declared rules plus the twelve auto-injected
///   numeric coercions only; `generate_term_defs` is byte-identical across the range; and the
///   auto-injected contribution is 12 fields on both sides of it (240 − 228 == 239 − 227).
/// ★ The three byte-named methods (2026-07-30, RE-DERIVED not relaxed). `5a9efa00` closed the
/// byte-method axis by declaring three rules, each carrying its own congruence:
///
/// ```text
///     MHexToBytes      . s:Proc |- s "." "hexToBytes"   "(" ")" : Proc ![{ … }] fold;
///     MBytesToHex      . b:Proc |- b "." "bytesToHex"   "(" ")" : Proc ![{ … }] fold;
///     MToUtf8Bytes     . s:Proc |- s "." "toUtf8Bytes"  "(" ")" : Proc ![{ … }] fold;
///     MHexToBytesCong  . | S ~> T |- (MHexToBytes  S) ~> (MHexToBytes  T);
///     MBytesToHexCong  . | S ~> T |- (MBytesToHex  S) ~> (MBytesToHex  T);
///     MToUtf8BytesCong . | S ~> T |- (MToUtf8Bytes S) ~> (MToUtf8Bytes T);
/// ```
///
/// * **T1 239 → 242.** Each method rule declares exactly ONE operand — its receiver, a
///   non-binder, non-`Guard` field of the non-scalar category `Proc`, decided by the structural
///   classifier on the `True` skeleton. Three unary receivers ⇒ +3. The `fold` actions
///   contribute nothing, for the reason already established for `LLast` and `PParInternal`
///   above: an `![…]` body is neither a field nor a rewrite condition.
/// * **T2 285 → 291, i.e. +6 from three rules.** ★ This is the `LLast` arithmetic applied three
///   times, not a new phenomenon. `T2 == (Σ rewrite conditions) + (congruence premises) +
///   (binder fields)`, and each generated congruence `RewriteDef` carries
///   `conditions: &["S ~> T"]` *and* `premise: Some(("S", "T"))` — counted once in each sum, so
///   **+2 per congruence**. Three congruences ⇒ +6. Measured after the addition: 148 rewrite
///   conditions + 142 congruence premises + 1 binder = 291, i.e. conditions 145 → 148 and
///   premises 139 → 142, each +3.
/// * **total 524 → 533**, and `524 + 3 + 6 == 533 == 242 + 291` closes the arithmetic. No binder
///   and no freshness condition is declared, so T3/T4 stay 0 and `worst` stays T2.
///
/// ★★ The `drift_shape` diagnostic added alongside the `PParInternal` re-derivation predicted
/// this shape before the cause was known, which is the whole point of it: it printed
/// `ΔT1 = +3 AND ΔT2 = +6 ⇒ BOTH a structural and a behavioral source moved. Do not attribute
/// this to one commit without checking both; a single rule carrying its own congruence does
/// exactly this (+1 T1, +2 T2).` The three-rule attribution was then confirmed against
/// `5a9efa00`'s own diff, not inferred from the failure message.
///
/// ⚠ Do NOT read "+3 methods" as "+3 to the byte-method count on every axis" — that count is
/// axis-dependent and four axes were measured. These three are the **byte-NAMED** methods
/// (axis B, 1 → 4). Separately, `length`/`nth`/`last` gained a `Bytes` receiver **in the host
/// fold lane** (axis D, 0 → 3) by *routing*, declaring no new rule, so they move neither tally.
/// Axis D had never been measured and was the one that mattered: those three are reducer
/// `method_table` keys, so the machine already answered them correctly while the fold answered
/// `error` — a live fold/machine disagreement from the moment `b"…"` became spellable.
#[test]
fn rholang_guard_tiers() {
    let meta = mettail_languages::rholang::RholangLanguage.metadata();
    assert_tier_tuple(meta, 533, 242, 291, 0, 0, T2);
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

/// **Anti-vacuity floor for [`drift_shape`].** The diagnostic only ever runs on the failure
/// path of a golden assert, so nothing in the eight passing cases would notice if it silently
/// degraded to an empty string — which is exactly the shape of vacuous guard this campaign has
/// repeatedly shipped. This drives it directly with synthetic `(expected, actual)` pairs and
/// asserts it LOCALISES each kind of drift, using a real `LanguageMetadata` for the inventory
/// half so the observed-decomposition line is exercised too.
///
/// The four cases are the exhaustive partition of `(ΔT1, ΔT2)` that `drift_shape` discriminates:
/// both zero (typing logic moved), structural only, behavioral only, and the tier-shift /
/// mixed cases.
#[test]
fn drift_shape_localises_each_kind_of_change() {
    let meta = mettail_languages::lambda::LambdaLanguage.metadata();
    // Lambda's real inventory: 2 structural, 1 binder, 3 conditions, 3 premises ⇒ (9, 2, 7).
    let shape = |expected: (usize, usize, usize), actual: (usize, usize, usize)| {
        drift_shape(meta, expected, actual, 2, 1, 3, 3)
    };

    // (i) A vanished structural field: Δtotal = −1, ΔT1 = −1, ΔT2 = 0. This is the exact
    // 2026-07-30 `PParInternal` signature, so it is asserted verbatim, singular noun and all.
    let structural_only = shape((9, 2, 7), (8, 1, 7));
    assert!(
        structural_only.contains("Δtotal = -1, ΔT1 = -1, ΔT2 = 0")
            && structural_only
                .contains("exactly 1 non-binder, non-`Guard` constructor field DISAPPEARED from")
            && structural_only.contains("REMOVED FROM"),
        "drift_shape must localise a lost field to the declaring spec's rule list, got:\n{structural_only}"
    );
    // A zero delta must read `0`, never `+0`: "ΔT2 = 0" is what rules out a tier shift, and a
    // signed zero reads as a change.
    assert!(
        !structural_only.contains("+0"),
        "drift_shape must not render a zero delta as `+0`, got:\n{structural_only}"
    );

    // (ii) An added structural field points the reader the other way, and pluralises.
    let added = shape((9, 2, 7), (11, 4, 7));
    assert!(
        added.contains("ΔT1 = +2")
            && added.contains("exactly 2 non-binder, non-`Guard` constructor fields APPEARED in"),
        "drift_shape must distinguish an ADDED field from a lost one, and pluralise, got:\n{added}"
    );

    // (iii) Behavioral-only drift must NOT send the reader hunting for a field.
    let behavioral = shape((9, 2, 7), (11, 2, 9));
    assert!(
        behavioral.contains("no constructor field was added or removed")
            && behavioral.contains("BEHAVIORAL"),
        "drift_shape must localise behavioral drift to conditions/premises/binders, got:\n{behavioral}"
    );

    // (iv) A tier shift (Δtotal == 0, ΔT1 == −ΔT2) is its own signature, not a lost field.
    let tier_shift = shape((9, 2, 7), (9, 1, 8));
    assert!(
        tier_shift.contains("CHANGED TIER") && tier_shift.contains("is_binder"),
        "drift_shape must recognise a tier shift rather than report a lost field, got:\n{tier_shift}"
    );

    // (v) Tuple-equal ⇒ the guard-TYPING logic moved, not the grammar.
    let typing_only = shape((9, 2, 7), (9, 2, 7));
    assert!(
        typing_only.contains("guard-TYPING logic changed"),
        "drift_shape must attribute a T1/T2-stable mismatch to the typing logic, got:\n{typing_only}"
    );

    // (vi) The observed decomposition is always reported — that is the line whose absence
    // forced the 2026-07-30 investigation to write a metadata dumper by hand.
    for (name, s) in [
        ("structural_only", &structural_only),
        ("added", &added),
        ("behavioral", &behavioral),
        ("tier_shift", &tier_shift),
        ("typing_only", &typing_only),
    ] {
        assert!(
            s.contains("structural=2 binders=1 conditions=3 premises=3")
                && s.contains("terms=2, rewrites=4")
                && s.contains("== 3 + 3 + 1 == 7"),
            "`{name}`: drift_shape must always report the raw decomposition, got:\n{s}"
        );
        assert!(
            s.len() > 200,
            "`{name}`: drift_shape degenerated to a near-empty message ({} bytes)",
            s.len()
        );
    }
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
        mettail_languages::rholang::RholangLanguage.metadata(),
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
        let congruence_premises = meta
            .rewrites()
            .iter()
            .filter(|rw| rw.premise.is_some())
            .count();

        assert!(binder_fields >= 1, "`{}` should have ≥1 binder for this check", meta.name());

        // (i) Structural T1 excludes binders entirely.
        assert_eq!(
            r.compile_time_decidable,
            structural_fields,
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
